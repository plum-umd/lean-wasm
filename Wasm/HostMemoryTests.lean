import Wasm.HostMemory

namespace Wasm.Tests

private instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false

private def sameHostMemory {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameHostMemory

private def checkHostMemory (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"host memory regression failed: {name}")

private def memoryPending (config : Configuration) : IO PendingHostCall := do
  match (runUntilHost 100 config).status with
  | .pending call => return call
  | _ => throw (IO.userError "expected a suspended host call")

private def memoryReply (pending : PendingHostCall) (results : List Value)
    (writes : List HostMemoryWrite) : IO Configuration := do
  match resumeHostCallWithMemory pending results writes with
  | .ok next => return next
  | .error error => throw (IO.userError s!"unexpected host memory error: {repr error}")

private def memoryReplyError (pending : PendingHostCall) (results : List Value)
    (writes : List HostMemoryWrite) : Option HostMemoryReplyError :=
  match resumeHostCallWithMemory pending results writes with
  | .ok _ => none
  | .error error => some error

private def memoryRead (pending : PendingHostCall) (index offset count : Nat) :
    IO (Array Byte) := do
  match readHostMemory pending index offset count with
  | .ok bytes => return bytes
  | .error error => throw (IO.userError s!"unexpected host memory read error: {repr error}")

#eval do
  let bufferType : FuncType := ⟨[.i32, .i32], [.i32]⟩
  let wrapperType : FuncType := ⟨[], [.i32]⟩
  -- Memory 0 in the callee is store memory 1. Index 2 aliases that same memory.
  let caller : ModuleInst :=
    { types := [bufferType, wrapperType], funcs := [⟨0⟩], mems := [⟨1⟩, ⟨2⟩, ⟨1⟩] }
  let host : FuncInst := ⟨bufferType, {}, .host 99⟩
  let nested : FuncInst := ⟨wrapperType, caller, .wasm ⟨1, [.i32],
    [.const (.i32 4), .const (.i32 3), .call 0, .drop,
      .const (.i32 4), .load .i32_8U 0 {}]⟩⟩
  let outer : MemoryInst := ⟨⟨.i32, 1, some 1⟩, Array.replicate pageSize 7⟩
  let inner : MemoryInst := ⟨⟨.i32, 1, some 1⟩, Array.replicate pageSize 0⟩
  let wide : MemoryInst := ⟨⟨.i64, 1, some 2⟩, Array.replicate pageSize 8⟩
  let store : Store :=
    { funcs := [host, nested]
      mems := [outer, inner, wide]
      globals := [⟨⟨.var, .i32⟩, .i32 123⟩] }
  let frame : Frame :=
    { module := { funcs := [⟨1⟩], mems := [⟨0⟩] }, locals := [some (.i32 55)] }
  let pending ← memoryPending ⟨store, frame, instructions [.call 0]⟩
  checkHostMemory "buffer parameters" (pending.request.arguments ≟ [.i32 4, .i32 3])
  checkHostMemory "nested calling module" (pending.request.caller.module ≟ caller)
  checkHostMemory "read callee memory" ((← memoryRead pending 0 4 3) ≟ #[0, 0, 0])
  checkHostMemory "explicit memory selection" ((← memoryRead pending 1 4 3) ≟ #[8, 8, 8])
  checkHostMemory "read alias" ((← memoryRead pending 2 4 3) ≟ #[0, 0, 0])
  let write : HostMemoryWrite := ⟨0, 4, #[42, 43, 44]⟩
  let resumed ← memoryReply pending [.i32 3] [write]
  checkHostMemory "guest load sees host write"
    ((runConfiguration 100 resumed).status ≟ .finished [.i32 42])
  checkHostMemory "caller locals restored" (resumed.frame ≟ pending.source.frame)
  checkHostMemory "host context retained"
    (resumed.code ≟ pending.context.fill (pending.resultCode [.i32 3]))
  checkHostMemory "outer memory untouched" (resumed.store.mem? ⟨0⟩ ≟ some outer)
  checkHostMemory "unrelated memory untouched" (resumed.store.mem? ⟨2⟩ ≟ some wide)
  checkHostMemory "non-memory store untouched"
    (resumed.store.withoutHostMemories ≟ pending.source.store.withoutHostMemories)
  checkHostMemory "memory shapes retained"
    (resumed.store.hostMemoryShape ≟ pending.source.store.hostMemoryShape)
  let changed := (resumed.store.mem? ⟨1⟩).getD inner
  checkHostMemory "written bytes" (changed.read 4 3 ≟ #[42, 43, 44])
  checkHostMemory "prefix unchanged" (changed.read 0 4 ≟ inner.read 0 4)
  checkHostMemory "suffix unchanged"
    (changed.read 7 (pageSize - 7) ≟ inner.read 7 (pageSize - 7))
  checkHostMemory "snapshot remains unchanged" ((← memoryRead pending 0 4 3) ≟ #[0, 0, 0])
  checkHostMemory "unknown index read"
    (readHostMemory pending 3 0 0 ≟ .error (.unknownMemory 3))
  checkHostMemory "read past end"
    (readHostMemory pending 0 (pageSize - 1) 2 ≟
      .error (.outOfBounds 0 (pageSize - 1) 2))
  checkHostMemory "zero-length read at end" ((← memoryRead pending 0 pageSize 0) ≟ #[])
  checkHostMemory "zero-length read past end"
    (readHostMemory pending 0 (pageSize + 1) 0 ≟
      .error (.outOfBounds 0 (pageSize + 1) 0))
  for large in [2 ^ 32, 2 ^ 64, 2 ^ 128] do
    checkHostMemory "non-wrapping offset"
      (readHostMemory pending 0 large 1 ≟ .error (.outOfBounds 0 large 1))
    checkHostMemory "non-wrapping length"
      (readHostMemory pending 0 1 large ≟ .error (.outOfBounds 0 1 large))
    checkHostMemory "non-wrapping write offset"
      (memoryReplyError pending [.i32 3] [⟨0, large, #[1]⟩] ≟
        some (.memory (.outOfBounds 0 large 1)))
  checkHostMemory "invalid second write is atomic"
    (memoryReplyError pending [.i32 3] [write, ⟨0, pageSize, #[1]⟩] ≟
      some (.memory (.outOfBounds 0 pageSize 1)))
  checkHostMemory "unknown memory write is atomic"
    (memoryReplyError pending [.i32 3] [write, ⟨3, 0, #[]⟩] ≟
      some (.memory (.unknownMemory 3)))
  for results in ([[], [.i64 3], [.i32 3, .i32 4], [.ref (.func ⟨999⟩)]] : List (List Value)) do
    checkHostMemory "invalid results cannot commit writes"
      (memoryReplyError pending results [write] ≟ some (.reply .invalidResults))
  checkHostMemory "all rejections retain source bytes"
    ((← memoryRead pending 0 4 3) ≟ #[0, 0, 0])
  let retried ← memoryReply pending [.i32 3] [write]
  checkHostMemory "retry after rejection" (retried ≟ resumed)
  let overlapping ← memoryReply pending [.i32 3] [write, ⟨2, 5, #[91, 92]⟩]
  checkHostMemory "later aliased write wins"
    (((overlapping.store.mem? ⟨1⟩).getD inner).read 4 4 ≟ #[42, 91, 92, 0])
  let multiple ← memoryReply pending [.i32 3] [write, ⟨1, 9, #[55]⟩]
  checkHostMemory "multiple memories"
    ((multiple.store.hostByte? ⟨1⟩ 4 ≟ some 42) &&
      (multiple.store.hostByte? ⟨2⟩ 9 ≟ some 55))
  checkHostMemory "memory64 guest load"
    ((runConfiguration 20 ⟨multiple.store, { module := caller },
      instructions [.const (.i64 9), .load .i32_8U 1 {}]⟩).status ≟ .finished [.i32 55])
  let atEnd ← memoryReply pending [.i32 0] [⟨0, pageSize, #[]⟩]
  checkHostMemory "zero-length write at end" (atEnd.store ≟ pending.source.store)
  checkHostMemory "zero-length write past end"
    (memoryReplyError pending [.i32 0] [⟨0, pageSize + 1, #[]⟩] ≟
      some (.memory (.outOfBounds 0 (pageSize + 1) 0)))
  let last ← memoryReply pending [.i32 1] [⟨0, pageSize - 1, #[9]⟩]
  checkHostMemory "last byte writable" (last.store.hostByte? ⟨1⟩ (pageSize - 1) ≟ some 9)
  let old := resumeHostCall pending (.values [.i32 3])
  match old with
  | .error _ => throw (IO.userError "old reply failed")
  | .ok unchanged =>
    checkHostMemory "old API unchanged store" (unchanged.store ≟ pending.source.store)
    checkHostMemory "empty effect compatibility"
      (resumeHostCallWithMemory pending [.i32 3] [] ≟ .ok unchanged)
  match resumeHostCall pending .trap with
  | .error _ => throw (IO.userError "old trap reply failed")
  | .ok trapped => checkHostMemory "old trap preserves store" (trapped.store ≟ store)
  let danglingFrame : Frame := { module := { mems := [⟨99⟩] } }
  let dangling ← memoryPending ⟨store, danglingFrame,
    values [.i32 0, .i32 0] ++ [AdminInstr.invoke ⟨0⟩ bufferType]⟩
  checkHostMemory "dangling memory address read"
    (readHostMemory dangling 0 0 0 ≟ .error (.missingMemory ⟨99⟩))
  checkHostMemory "dangling memory address write"
    (memoryReplyError dangling [.i32 0] [⟨0, 0, #[]⟩] ≟
      some (.memory (.missingMemory ⟨99⟩)))
  let referenceType : FuncType := ⟨[], [.ref .func]⟩
  let referenceStore : Store := { funcs := [⟨referenceType, {}, .host 100⟩] }
  match (runUntilHost 0 ⟨referenceStore, {}, [.invoke ⟨0⟩ referenceType]⟩).status with
  | .unsupportedHost call =>
    checkHostMemory "unsupported signature rejected before effects"
      (memoryReplyError call [.ref (.null .func)] [write] ≟ some (.reply .unsupportedSignature))
  | _ => throw (IO.userError "expected an unsupported reference signature")
  -- Tail-call unwinding uses the same saved context after memory effects commit.
  let tail ← memoryPending ⟨store, frame, [.frame 1 { module := caller }
    [.label 1 [] [.handler [] (values [.i32 4, .i32 3] ++
      [AdminInstr.returnInvoke ⟨0⟩ bufferType, .instr .unreachable])]]]⟩
  let tailResumed ← memoryReply tail [.i32 3] [write]
  let tailFinished := runConfiguration 100 tailResumed
  checkHostMemory "tail reply" (tailFinished.status ≟ .finished [.i32 3])
  checkHostMemory "tail write retained" (tailFinished.state.store.hostByte? ⟨1⟩ 4 ≟ some 42)

example (resumed : resumeHostCallWithMemory pending results writes = .ok next)
    (valid : ∀ memory ∈ pending.source.store.mems, memory.Valid) :
    ∀ memory ∈ next.store.mems, memory.Valid :=
  (resumeHostCallWithMemory_sound resumed).memories_valid valid

example (resumed : resumeHostCallWithMemory pending results writes = .ok next) :
    next.frame = pending.source.frame ∧
      next.code = pending.context.fill (pending.resultCode results) :=
  (resumeHostCallWithMemory_spec resumed).2

#print axioms readHostMemory_sound
#print axioms HostMemoryRead.size
#print axioms resumeHostCallWithMemory_sound
#print axioms MemoryInst.host_write_valid
#print axioms MemoryInst.host_write_inside
#print axioms MemoryInst.host_write_outside
#print axioms HostMemoryEffects.other_components
#print axioms HostMemoryEffects.shape
#print axioms HostMemoryEffects.memories_valid
#print axioms HostMemoryEffects.bytes_outside
#print axioms HostMemoryEffects.unwritten_memory
#print axioms HostMemoryEffects.arguments_typing
#print axioms resumeHostCallWithMemory_empty
#print axioms resumeHostCallWithMemory_spec
#print axioms resumeHostCallWithMemory_bytes_outside
#print axioms runUntilHost_resume_memory_sound

end Wasm.Tests
