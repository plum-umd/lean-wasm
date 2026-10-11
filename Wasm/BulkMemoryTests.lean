import Wasm.Configuration
import Wasm.DataValidation

namespace Wasm.Tests

private def checkBulk (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"bulk-memory regression failed: {name}")
private def sameBulk {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameBulk

private def bulkTests : IO Unit := do
  let bytes : Array Byte := #[1, 2, 3, 4, 5, 6, 7, 8] ++ Array.replicate (pageSize - 8) 0
  let segment : DataInst := ⟨#[255, 128, 3, 4]⟩
  for type in [ValType.i32, .i64] do
    let memory : MemoryInst := ⟨⟨type, 1, none⟩, bytes⟩
    let store : Store := { mems := [memory], datas := [segment] }
    let frame : Frame := { module := { mems := [⟨0⟩], datas := [⟨0⟩] } }
    let address := Value.ofNat type
    let execute := fun code => runConfiguration 100 ⟨store, frame, instructions code⟩
    let read := fun (result : ConfigurationRunResult) start count =>
      (result.state.store.mems[0]?.getD memory).read start count
    let fill := [.const (address 2), .const (.i32 511), .const (address 3), .memoryFill 0]
    let first := runConfiguration 1 ⟨store, frame, instructions fill⟩
    checkBulk "fill lowers without writing" (first.state.store ≟ store)
    checkBulk "fill exact lowering" (first.state.code ≟ fillCode type 0 2 (.i32 511) 3)
    checkBulk "fill truncation and neighbors"
      (read (execute fill) 0 8 ≟ #[1, 2, 255, 255, 255, 6, 7, 8])
    checkBulk "fill finishes" ((execute fill).status ≟ .finished [])
    let oneByte := [.const (address 2), .const (.i32 9), .const (address 1), .memoryFill 0]
    checkBulk "fill fuel counts byte store and zero tail"
      ((runConfiguration 2 ⟨store, frame, instructions oneByte⟩).status ≟ .exhausted)
    checkBulk "fill exact fuel"
      ((runConfiguration 3 ⟨store, frame, instructions oneByte⟩).status ≟ .finished [])
    for (dst, src, expected) in
        [(2, 0, (#[1, 2, 1, 2, 3, 4, 7, 8] : Array Byte)),
          (0, 2, #[3, 4, 5, 6, 5, 6, 7, 8]), (0, 0, #[1, 2, 3, 4, 5, 6, 7, 8])] do
      let copy := [.const (address dst), .const (address src), .const (address 4), .memoryCopy 0 0]
      let result := execute copy
      checkBulk "overlapping copy" (read result 0 8 ≟ expected)
      checkBulk "copy finishes" (result.status ≟ .finished [])
      let lowered := runConfiguration 1 ⟨store, frame, instructions copy⟩
      checkBulk "copy exact lowering" (lowered.state.code ≟ copyCode type type 0 0 dst src 4)
      checkBulk "copy lowers without writing" (lowered.state.store ≟ store)
    let init := [.const (address 2), .const (.i32 1), .const (.i32 2), .memoryInit 0 0]
    let initialized := execute init
    checkBulk "init unsigned bytes and slice" (read initialized 0 6 ≟ #[1, 2, 128, 3, 5, 6])
    checkBulk "init leaves segment reusable" (initialized.state.store.datas ≟ [segment])
    checkBulk "init finishes" (initialized.status ≟ .finished [])
    let firstInit := runConfiguration 1 ⟨store, frame, instructions init⟩
    checkBulk "init exact lowering" (firstInit.state.code ≟ initCode type 0 0 2 1 2 128)
    checkBulk "init lowers without writing" (firstInit.state.store ≟ store)
    let oneInit := instructions
      [.const (address 10), .const (.i32 0), .const (.i32 1), .memoryInit 0 0]
    checkBulk "init fuel exhaustion"
      ((runConfiguration 2 ⟨store, frame, oneInit⟩).status ≟ .exhausted)
    checkBulk "init exact fuel"
      ((runConfiguration 3 ⟨store, frame, oneInit⟩).status ≟ .finished [])
    let oneCopy := instructions
      [.const (address 10), .const (address 0), .const (address 1), .memoryCopy 0 0]
    checkBulk "copy fuel exhaustion"
      ((runConfiguration 3 ⟨store, frame, oneCopy⟩).status ≟ .exhausted)
    checkBulk "copy exact fuel"
      ((runConfiguration 4 ⟨store, frame, oneCopy⟩).status ≟ .finished [])
    for op in [Instr.memoryFill 0, .memoryCopy 0 0, .memoryInit 0 0] do
      let src := if op == .memoryFill 0 then Value.i32 9 else address 0
      let src := if op == .memoryInit 0 0 then Value.i32 0 else src
      let lenType := if op == .memoryInit 0 0 then ValType.i32 else type
      let bad := execute [.const (address (pageSize - 1)), .const src,
        .const (Value.ofNat lenType 2), op]
      checkBulk "destination bounds trap before writing" (bad.status ≟ .trapped)
      checkBulk "destination trap preserves store" (bad.state.store ≟ store)
      checkBulk "zero length at end" ((execute [.const (address pageSize), .const src,
        .const (Value.ofNat lenType 0), op]).status ≟ .finished [])
      checkBulk "zero length beyond end" ((execute [.const (address (pageSize + 1)), .const src,
        .const (Value.ofNat lenType 0), op]).status ≟ .trapped)
      checkBulk "unsigned destination" ((execute [.const (Value.ofInt type (-1)), .const src,
        .const (Value.ofNat lenType 1), op]).status ≟ .trapped)
    for (src, n) in [(pageSize, 0), (pageSize - 1, 2), (pageSize + 1, 0)] do
      let result := execute [.const (address 0), .const (address src), .const (address n),
        .memoryCopy 0 0]
      checkBulk "copy source bounds"
        (result.status ≟ (if src + n ≤ pageSize then .finished [] else .trapped))
      checkBulk "copy source bounds preserves store" (result.state.store ≟ store)
    for (src, n) in [(4, 0), (3, 2), (5, 0)] do
      let result := execute [.const (address 0), .const (Value.ofNat .i32 src),
        .const (Value.ofNat .i32 n), .memoryInit 0 0]
      checkBulk "init source bounds"
        (result.status ≟ (if src + n ≤ 4 then .finished [] else .trapped))
      checkBulk "init source bounds preserves store" (result.state.store ≟ store)
    let dropped := execute [.dataDrop 0, .dataDrop 0]
    checkBulk "drop idempotent" (dropped.status ≟ .finished [])
    checkBulk "drop retains empty instance" (dropped.state.store.datas ≟ [⟨#[]⟩])
    checkBulk "drop preserves memory" (dropped.state.store.mems ≟ [memory])
    for (src, n, status) in
        [(0, 0, RunStatus.finished []), (0, 1, .trapped), (1, 0, .trapped)] do
      checkBulk "init after drop" ((execute [.dataDrop 0, .const (address 0),
        .const (Value.ofNat .i32 src), .const (Value.ofNat .i32 n), .memoryInit 0 0]).status ≟ status)
    let active : Data := ⟨segment.bytes, .active 0 [.const (address 10)]⟩
    let activated := execute (active.initializer 0)
    checkBulk "active segment initializes" (read activated 10 4 ≟ segment.bytes)
    checkBulk "active segment drops" (activated.state.store.datas ≟ [⟨#[]⟩])
    let outOfBounds : Data := ⟨segment.bytes, .active 0 [.const (address (pageSize - 1))]⟩
    let failedActive := execute (outOfBounds.initializer 0)
    checkBulk "active initializer bounds trap" (failedActive.status ≟ .trapped)
    checkBulk "failed active initializer retains data" (failedActive.state.store ≟ store)
    checkBulk "passive initializer is empty"
      (({ active with mode := .passive }).initializer 0 ≟ [])
    checkBulk "nested block and value context" ((execute [.const (.i32 42),
      .block (.val none) fill]).status ≟ .finished [.i32 42])
    checkBulk "init i64 source is stuck" ((execute [.const (address 0), .const (.i64 0),
      .const (.i32 1), .memoryInit 0 0]).status ≟ .stuck)
    checkBulk "fill i64 byte value is stuck" ((execute [.const (address 0), .const (.i64 1),
      .const (address 1), .memoryFill 0]).status ≟ .stuck)
    checkBulk "bulk operand underflow" ((execute [.memoryFill 0]).status ≟ .stuck)
    checkBulk "missing data" ((execute [.dataDrop 1]).status ≟ .stuck)
    checkBulk "missing memory" ((execute [.const (address 0), .const (.i32 1),
      .const (address 1), .memoryFill 1]).status ≟ .stuck)
    checkBulk "no skipping instructions" ((execute [.localSet 0, .dataDrop 0]).status ≟ .stuck)
    let afterTrap := execute (fill ++ [.unreachable])
    checkBulk "trap retains earlier bulk writes" (read afterTrap 2 3 ≟ #[255, 255, 255])
    checkBulk "bulk trap propagation" ((execute [.block (.val none)
      [.const (address pageSize), .const (.i32 1), .const (address 1),
        .memoryFill 0]]).status ≟ .trapped)

  for dstType in [ValType.i32, .i64] do
    for srcType in [ValType.i32, .i64] do
      let dst : MemoryInst := ⟨⟨dstType, 1, none⟩, Array.replicate pageSize 0⟩
      let src : MemoryInst := ⟨⟨srcType, 1, none⟩, bytes⟩
      let store : Store := { mems := [src, dst] }
      let frame : Frame := { module := { mems := [⟨1⟩, ⟨0⟩] } }
      let code := instructions [.const (Value.ofNat dstType 10), .const (Value.ofNat srcType 1),
        .const (Value.ofNat (dstType.minAddress srcType) 4), .memoryCopy 0 1]
      let result := runConfiguration 100 ⟨store, frame, code⟩
      checkBulk "all copy address-width pairs" (result.status ≟ .finished [])
      checkBulk "cross memory indexed destination"
        ((result.state.store.mems[1]?.getD dst).read 10 4 ≟ #[2, 3, 4, 5])
      checkBulk "cross memory source unchanged" (result.state.store.mem? ⟨0⟩ ≟ some src)
      let wrongLength := instructions
        [.const (Value.ofNat dstType 0), .const (Value.ofNat srcType 0),
        .const (Value.ofNat (if dstType.minAddress srcType == .i32 then .i64 else .i32) 1),
        .memoryCopy 0 1]
      checkBulk "copy length width checked"
        ((runConfiguration 10 ⟨store, frame, wrongLength⟩).status ≟ .stuck)

  let memory : MemoryInst := ⟨⟨.i32, 1, none⟩, bytes⟩
  let ft : FuncType := ⟨[], []⟩
  let owner : ModuleInst := { types := [ft], mems := [⟨0⟩], datas := [⟨1⟩] }
  let function : FuncInst := ⟨ft, owner, .wasm ⟨0, [],
    [.const (.i32 10), .const (.i32 0), .const (.i32 4), .memoryInit 0 0, .dataDrop 0]⟩⟩
  let store : Store := { funcs := [function], mems := [memory], datas := [⟨#[9]⟩, segment] }
  let caller : Frame := { module := { funcs := [⟨0⟩], datas := [⟨0⟩] } }
  let result := runConfiguration 100 ⟨store, caller, instructions [.call 0]⟩
  checkBulk "callee segment mapping" (result.status ≟ .finished [])
  checkBulk "callee initialized shared memory"
    ((result.state.store.mems[0]?.getD memory).read 10 4 ≟ segment.bytes)
  checkBulk "callee drops defining segment" (result.state.store.datas ≟ [⟨#[9]⟩, ⟨#[]⟩])
  checkBulk "caller restored" (result.state.frame ≟ caller)
  let aliasFrame : Frame := { module := { mems := [⟨0⟩, ⟨0⟩], datas := [⟨1⟩, ⟨1⟩] } }
  let aliased := runConfiguration 100 ⟨store, aliasFrame, instructions
    [.const (.i32 2), .const (.i32 0), .const (.i32 4), .memoryCopy 0 1, .dataDrop 0]⟩
  checkBulk "memory aliases overlap correctly"
    ((aliased.state.store.mems[0]?.getD memory).read 0 8 ≟ #[1, 2, 1, 2, 3, 4, 7, 8])
  checkBulk "drop visible through alias" (aliased.state.store.resolveData? aliasFrame.module 1 ≟
    some ⟨#[]⟩)
  let dangling : Frame := { module := { datas := [⟨99⟩] } }
  checkBulk "dangling segment stuck"
    ((runConfiguration 10 ⟨store, dangling, instructions [.dataDrop 0]⟩).status ≟ .stuck)
  let allocated := store.allocateData segment
  checkBulk "segment allocation address" (allocated.1 ≟ ⟨2⟩)
  checkBulk "segment allocation lookup" (allocated.2.data? allocated.1 ≟ some segment)
  checkBulk "segment allocation preserves earlier addresses" (allocated.2.data? ⟨0⟩ ≟ some ⟨#[9]⟩)

#eval bulkTests

example : BulkInstrTyping [⟨.i64, 0, none⟩] 1 (.memoryFill 0) [.i64, .i32, .i64] [] :=
  .fill (memory := ⟨.i64, 0, none⟩) rfl
example : BulkInstrTyping [⟨.i64, 0, none⟩, ⟨.i32, 0, none⟩] 0
    (.memoryCopy 0 1) [.i64, .i32, .i32] [] :=
  .copy (dst := ⟨.i64, 0, none⟩) (src := ⟨.i32, 0, none⟩) rfl rfl
example : RuntimeInstrTyping { mems := [⟨.i64, 0, none⟩], dataCount := 1 } []
    (.memoryInit 0 0) [.i64, .i32, .i32] [] :=
  .bulk (.init (memory := ⟨.i64, 0, none⟩) rfl (by decide))
example : FuncTyping [.func ⟨[], []⟩] [] [] [] 1 ⟨0, [], [.dataDrop 0]⟩ ⟨[], []⟩ :=
  .wasm rfl (by decide) (.cons (.bulk (.drop (by decide))) .empty)
example : DataTyping { mems := [⟨.i32, 0, none⟩] }
    ⟨#[1, 2], .active 0 [.const (.i32 3)]⟩ := by
  apply DataTyping.active (memory := ⟨.i32, 0, none⟩) rfl
  · exact .cons (.plain (.plain (.plain .const))) .empty
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    exact .const

#print axioms stepBulkMemory_sound
#print axioms BulkStep.data_count_preserved
#print axioms Store.dropData_lookup
#print axioms Store.allocateData_preserves
#print axioms ConfigStep.data_count_preserved
#print axioms runConfiguration_sound

end Wasm.Tests
