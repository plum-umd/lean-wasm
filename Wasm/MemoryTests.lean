import Wasm.Configuration
import Wasm.CallValidation

namespace Wasm.Tests

open AdminInstr
private def checkMemory (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"memory regression failed: {name}")
private def sameMemory {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameMemory

private def executeMemory (memory : MemoryInst) (code : List Instr) : ConfigurationRunResult :=
  runConfiguration 40
    ⟨{ mems := [memory] }, { module := { mems := [⟨0⟩] } }, instructions code⟩

private def memoryTests : IO Unit := do
  let data : Array Byte := #[128, 255, 255, 255, 255, 255, 255, 255] ++
    Array.replicate (pageSize - 8) 0
  let loads : List (LoadOp × Nat) :=
    [(.i32, 4294967168), (.i64, 18446744073709551488),
      (.i32_8S, 4294967168), (.i32_8U, 128), (.i32_16S, 4294967168), (.i32_16U, 65408),
      (.i64_8S, 18446744073709551488), (.i64_8U, 128),
      (.i64_16S, 18446744073709551488), (.i64_16U, 65408),
      (.i64_32S, 18446744073709551488), (.i64_32U, 4294967168)]
  let stores : List StoreOp := [.i32, .i64, .i32_8, .i32_16, .i64_8, .i64_16, .i64_32]
  for addrType in [ValType.i32, .i64] do
    let memory : MemoryInst := ⟨⟨addrType, 1, some 2⟩, data⟩
    let address := Value.ofNat addrType
    for (op, expected) in loads do
      checkMemory s!"load {reprStr addrType} {reprStr op}"
        ((executeMemory memory [.const (address 0), .load op 0 {}]).status ≟
          .finished [Value.ofNat op.type expected])
      checkMemory s!"load end {reprStr addrType} {reprStr op}"
        ((executeMemory memory [.const (address (pageSize - op.bytes)), .load op 0 {}]).status ≟
          .finished [Value.ofNat op.type 0])
      checkMemory s!"load past end {reprStr addrType} {reprStr op}"
        ((executeMemory memory [.const (address (pageSize - op.bytes + 1)), .load op 0 {}]).status ≟
          .trapped)
    let zero : MemoryInst := { memory with bytes := Array.replicate pageSize 0 }
    for op in stores do
      let result := executeMemory zero
        [.const (address 1), .const (Value.ofNat op.type 9833440827789222417), .store op 0 {}]
      checkMemory s!"store {reprStr addrType} {reprStr op}" (result.status ≟ .finished [])
      let written := (result.state.store.mems[0]?.getD memory)
      let expected : Array Byte := #[17, 34, 51, 68, 85, 102, 119, 136]
      checkMemory "little endian and packed truncation"
        (written.read 1 op.bytes ≟ expected.extract 0 op.bytes)
      checkMemory "store preserves preceding byte" (written.bytes[0]? ≟ some 0)
      checkMemory "store preserves following byte" (written.bytes[1 + op.bytes]? ≟ some 0)
      checkMemory "store preserves size" (written.bytes.size ≟ pageSize)
      let failed := executeMemory memory
        [.const (address (pageSize - op.bytes + 1)), .const (Value.ofNat op.type 9), .store op 0 {}]
      checkMemory "store past end traps" (failed.status ≟ .trapped)
      checkMemory "trapping store is atomic" (failed.state.store.mems ≟ [memory])
    checkMemory "memory size" ((executeMemory memory [.memorySize 0]).status ≟
      .finished [address 1])
    let grown := executeMemory memory [.const (address 1), .memoryGrow 0]
    checkMemory "growth returns previous size" (grown.status ≟ .finished [address 1])
    let next := (grown.state.store.mems[0]?.getD memory)
    checkMemory "growth size" (next.bytes.size ≟ 2 * pageSize)
    checkMemory "growth updates runtime minimum" (next.type.min ≟ 2)
    checkMemory "growth retains maximum" (next.type.max ≟ some 2)
    checkMemory "growth retains bytes" (next.bytes.extract 0 pageSize ≟ data)
    checkMemory "growth zero fills" (next.bytes.extract pageSize (2 * pageSize) ≟
      Array.replicate pageSize 0)
    checkMemory "grown memory size" ((executeMemory next [.memorySize 0]).status ≟
      .finished [address 2])
    checkMemory "zero growth" ((executeMemory memory [.const (address 0), .memoryGrow 0]).status ≟
      .finished [address 1])
    let failed := executeMemory memory [.const (address 2), .memoryGrow 0]
    checkMemory "growth above maximum returns minus one" (failed.status ≟
      .finished [Value.ofInt addrType (-1)])
    checkMemory "failed growth preserves memory" (failed.state.store.mems ≟ [memory])
    checkMemory "unsigned huge growth fails" ((executeMemory memory
      [.const (Value.ofInt addrType (-1)), .memoryGrow 0]).status ≟ .finished [Value.ofInt addrType (-1)])
    checkMemory "effective address does not wrap" ((executeMemory memory
      [.const (Value.ofInt addrType (-1)), .load .i32_8U 0 { offset := 1 }]).status ≟ .trapped)

  let memory : MemoryInst := ⟨⟨.i32, 1, none⟩, data⟩
  let other : MemoryInst := ⟨⟨.i64, 1, some 1⟩, Array.replicate pageSize 0⟩
  checkMemory "offset read" ((executeMemory memory
    [.const (.i32 0), .load .i32_8U 0 { offset := 1 }]).status ≟ .finished [.i32 255])
  checkMemory "misaligned full load" ((executeMemory memory
    [.const (.i32 1), .load .i32 0 { align := 2 }]).status ≟ .finished [.i32 4294967295])
  checkMemory "alignment is not a runtime condition" ((executeMemory memory
    [.const (.i32 0), .load .i32_8U 0 { align := 20 }]).status ≟ .finished [.i32 128])
  checkMemory "wrong address width" ((executeMemory memory
    [.const (.i64 0), .load .i32 0 {}]).status ≟ .stuck)
  checkMemory "wrong stored value width" ((executeMemory memory
    [.const (.i32 0), .const (.i64 7), .store .i32 0 {}]).status ≟ .stuck)
  checkMemory "operand underflow" ((executeMemory memory [.store .i32 0 {}]).status ≟ .stuck)
  checkMemory "no skipping" ((executeMemory memory
    [.localSet 0, .memorySize 0]).status ≟ .stuck)
  checkMemory "missing memory index" ((executeMemory memory [.memorySize 1]).status ≟ .stuck)
  checkMemory "growth resource budget" ((executeMemory memory
    [.const (.i32 (BitVec.ofNat 32 growthBudgetPages)), .memoryGrow 0]).status ≟ .finished [.i32 4294967295])
  checkMemory "address-space limit" (memory.CanGrow (65536 : Nat) |> decide |> not)
  checkMemory "memory64 page limit" (other.type.pageLimit ≟ 281474976710656)
  let store : Store := { mems := [memory, other] }
  let frame : Frame := { module := { mems := [⟨1⟩, ⟨0⟩] } }
  checkMemory "module indices resolve to distinct addresses"
    (store.resolveMem? frame.module 0 ≟ some other)
  checkMemory "memory64 size through index" ((runConfiguration 10
    ⟨store, frame, instructions [.memorySize 0]⟩).status ≟ .finished [.i64 1])
  let dangling : Frame := { module := { mems := [⟨9⟩] } }
  checkMemory "missing store memory" ((runConfiguration 10
    ⟨store, dangling, instructions [.memorySize 0]⟩).status ≟ .stuck)
  let empty : MemoryInst := ⟨⟨.i32, 0, some 0⟩, #[]⟩
  checkMemory "empty memory size" ((executeMemory empty [.memorySize 0]).status ≟ .finished [.i32 0])
  checkMemory "empty memory load traps" ((executeMemory empty
    [.const (.i32 0), .load .i32_8U 0 {}]).status ≟ .trapped)
  let ft : FuncType := ⟨[], []⟩
  let owner : ModuleInst := { types := [ft], mems := [⟨0⟩] }
  let writer : FuncInst := ⟨ft, owner, .wasm ⟨0, [],
    [.const (.i32 10), .const (.i32 42), .store .i32 0 {}, .return_]⟩⟩
  let shared : Store := { funcs := [writer], mems := [memory, other] }
  let caller : Frame := { module := { funcs := [⟨0⟩], mems := [⟨1⟩, ⟨0⟩] } }
  let across := runConfiguration 30 ⟨shared, caller,
    instructions [.call 0, .const (.i32 10), .load .i32 1 {}]⟩
  checkMemory "writes shared across call" (across.status ≟ .finished [.i32 42])
  checkMemory "callee uses defining memory mapping" (across.state.store.mem? ⟨1⟩ ≟ some other)
  checkMemory "caller restored" (across.state.frame ≟ caller)
  checkMemory "function instances preserved" (across.state.store.funcs ≟ [writer])
  let block := executeMemory memory [.block (.val none)
    [.const (.i32 10), .const (.i32 42), .store .i32 0 {}], .const (.i32 10), .load .i32 0 {}]
  checkMemory "block shares memory" (block.status ≟ .finished [.i32 42])
  let trapped := executeMemory memory
    [.const (.i32 10), .const (.i32 42), .store .i32 0 {}, .unreachable]
  checkMemory "trap retains preceding write" ((trapped.state.store.mems[0]?.getD memory).read 10 4 ≟ #[42, 0, 0, 0])
  let start : Configuration := ⟨store, frame, instructions [.memorySize 0]⟩
  checkMemory "zero fuel" ((runConfiguration 0 start).status ≟ .exhausted)
  checkMemory "exact fuel terminal" ((runConfiguration 1 start).status ≟ .finished [.i64 1])
  let allocated := store.allocateMemory empty
  checkMemory "allocation address" (allocated.1 ≟ ⟨2⟩)
  checkMemory "allocation lookup" (allocated.2.mem? allocated.1 ≟ some empty)
  checkMemory "allocation preserves existing memory" (allocated.2.mem? ⟨0⟩ ≟ some memory)
  checkMemory "exported memory address"
    (({ exports := [⟨"memory", .memory ⟨0⟩⟩] } : ModuleInst).export? "memory" ≟
      some (.memory ⟨0⟩))

#eval memoryTests

example : decodeLoad .i32_8S #[128] = .i32 4294967168 := by decide
example : decodeLoad .i64_32S #[0, 0, 0, 128] = .i64 18446744071562067968 := by decide
example : ¬ MemArg.Valid { align := 1 } .i32 1 := by decide
example : ¬ MemArg.Valid { offset := 4294967296 } .i32 4 := by decide
example : MemoryInstrTyping [⟨.i64, 0, none⟩]
    (.load .i32_8S 0 {}) [.i64] [.i32] :=
  .load (memoryType := ⟨.i64, 0, none⟩) rfl (by decide)
example : RuntimeInstrTyping { mems := [⟨.i32, 0, none⟩] } []
    (.memorySize 0) [] [.i32] := .memory (.size (memoryType := ⟨.i32, 0, none⟩) rfl)

-- Resource failure is permitted even when growth by zero could succeed.
example : MemoryReduces ⟨⟨.i32, 0, none⟩, #[]⟩
    [.instr (.const (.i32 0)), .instr (.memoryGrow 0)] none (values [.i32 4294967295]) :=
  .growFail rfl

example : FuncTyping [.func ⟨[], [.i32]⟩] [] [] [⟨.i32, 0, none⟩] 0
    ⟨0, [], [.memorySize 0]⟩ ⟨[], [.i32]⟩ :=
  .wasm rfl (by decide) (.cons (.memory (.size (memoryType := ⟨.i32, 0, none⟩) rfl)) .empty)

#print axioms stepMemory_sound
#print axioms MemoryInst.write_size
#print axioms MemoryInst.grown_pages
#print axioms MemoryInst.grow?_sound
#print axioms MemoryStep.functions_preserved
#print axioms Store.allocateMemory_preserves

end Wasm.Tests
