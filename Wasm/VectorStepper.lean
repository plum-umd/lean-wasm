import Wasm.Vectors
import Wasm.FamilyScanner

namespace Wasm

/-- A vector memory instruction yields an optional write. All bounds use the full, unwrapped
sum of the address and offset, as required for memory64 as well as memory32. -/
def evalVectorMemory (store : Store) (state : Frame) (op : VectorOp) (args : List Value) :
    Option (Option (MemAddr × MemoryInst) × List AdminInstr) := do
  if !decide op.ImmediatesValid then return ← none
  if args.length != op.opcode.signature.params.length then return ← none
  let address ← state.module.memAddr? op.memory
  let memory ← store.mem? address
  let first ← args.head?
  let start ← first.address? memory.type.addrType
  let start := start + op.arg.offset
  let count := op.opcode.memoryBytes
  if start + count > memory.bytes.size then return (none, [.trap])
  let name := op.opcode.name
  let lane := op.lanes.headD 0
  if name.startsWith "v128.store" then
    let .v128 bits ← args[1]? | none
    let bytes := encodeBytes (if name.endsWith "lane" then
      vectorLane (8 * count) bits.toNat lane else bits.toNat) count
    return (some (address, memory.write start bytes), [])
  let loaded := decodeBytes (memory.read start count).toList
  let bits ← if name.endsWith "lane" then do
    let .v128 bits ← args[1]? | none
    let width := 8 * count
    pure (vectorPack width ((List.range (128 / width)).map fun i =>
      if i == lane then loaded else vectorLane width bits.toNat i))
  else if name.endsWith "splat" then
    pure (vectorPack (8 * count) (List.replicate (16 / count) loaded))
  else if name.endsWith "_s" || name.endsWith "_u" then
    let source := if name.startsWith "v128.load8" then 8
      else if name.startsWith "v128.load16" then 16 else 32
    pure (vectorPack (2 * source) ((List.range (64 / source)).map fun i =>
      let n := vectorLane source loaded i
      if name.endsWith "_s" then vectorWrap (2 * source) (vectorSigned source n) else n))
  else pure loaded
  return (none, values [.v128 (BitVec.ofNat 128 bits)])

def vectorMemoryStore (store : Store) (write : Option (MemAddr × MemoryInst)) : Store :=
  match write with
  | none => store
  | some (address, memory) => store.setMemory address memory

inductive VectorReduces : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | pure (evaluated : evalVector op args = some value) :
      VectorReduces store state (values args ++ [.instr (.vector op)]) store (values [value])
  | memory (isMemory : op.opcode.isMemory = true)
      (evaluated : evalVectorMemory store state op args = some (write, code)) :
      VectorReduces store state (values args ++ [.instr (.vector op)])
        (vectorMemoryStore store write) code

inductive VectorStep : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | redex : VectorReduces store state code next code' → VectorStep store state code next code'
  | context : VectorStep store state code next code' →
      VectorStep store state (values vs ++ code ++ tail) next (values vs ++ code' ++ tail)
  | label : VectorStep store state body next body' →
      VectorStep store state [.label n continuation body] next [.label n continuation body']
  | handler : VectorStep store state body next body' →
      VectorStep store state [.handler catches body] next [.handler catches body']
  | frame : VectorStep store inner body next body' →
      VectorStep store state [.frame n inner body] next [.frame n inner body']

abbrev CheckedVectorStep (store : Store) (state : Frame) (code : List AdminInstr) :=
  Option {next : Store × List AdminInstr // VectorStep store state code next.1 next.2}

private def checkedVectorRedex (store : Store) (state : Frame) (op : VectorOp)
    (args : List Value) : CheckedVectorStep store state (values args ++ [.instr (.vector op)]) := by
  if hm : op.opcode.isMemory = true then
    match he : evalVectorMemory store state op args with
    | none => exact none
    | some (write, code) => exact some ⟨(_, code), .redex (.memory hm he)⟩
  else
    match he : evalVector op args with
    | none => exact none
    | some value => exact some ⟨(store, values [value]), .redex (.pure he)⟩

private def vectorContext (vs : List Value) (tail : List AdminInstr)
    (checked : CheckedVectorStep store state code) :
    CheckedVectorStep store state (values vs ++ code ++ tail) :=
  checked.map fun next => ⟨(next.val.1, values vs ++ next.val.2 ++ tail),
    .context next.property⟩

private inductive VectorAtom : Store → Frame → VectorOp → List Value →
    Store → List AdminInstr → Prop where
  | pure (evaluated : evalVector op args = some value) :
      VectorAtom store state op args store (values [value])
  | memory (isMemory : op.opcode.isMemory = true)
      (evaluated : evalVectorMemory store state op args = some (write, code)) :
      VectorAtom store state op args (vectorMemoryStore store write) code

private def VectorLocal : FamilyRedex := fun store state instruction args next code =>
  match instruction with
  | .instr (.vector op) => VectorAtom store state op args next code
  | _ => False

private def vectorScanner : FamilyScanner where
  operands _ instruction := match instruction with
    | .instr (.vector op) => some op.opcode.signature.params.length
    | _ => none
  reduce store state instruction args := match instruction with
    | .instr (.vector op) => (checkedVectorRedex store state op args).map Subtype.val
    | _ => none

private theorem FamilyStep.vectors (reduced : FamilyStep VectorLocal store state code next code') :
    VectorStep store state code next code' := by
  induction reduced with
  | @redex _ instruction args _ _ h =>
    cases instruction <;> simp only [VectorLocal] at h
    all_goals try contradiction
    rename_i instr
    cases instr <;> simp only [VectorLocal] at h
    all_goals try contradiction
    cases h with
    | pure evaluated => exact .redex (.pure evaluated)
    | memory memory evaluated => exact .redex (.memory memory evaluated)
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

private theorem vectorScanner_sound (found : vectorScanner.scan store state code stack = some next) :
    VectorStep store state (values stack ++ code) next.1 next.2 := by
  apply FamilyStep.vectors
  apply vectorScanner.scan_sound (redex := VectorLocal) ?_ found
  intro store state instruction args next found
  cases instruction <;> simp only [vectorScanner] at found
  all_goals try contradiction
  rename_i instr
  cases instr <;> simp only [vectorScanner] at found
  all_goals try contradiction
  obtain ⟨checked, found, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  simp only [checkedVectorRedex] at found
  split at found
  · split at found <;> simp_all
    simp only [VectorLocal]
    rw [← found]
    exact .memory (by assumption) (by assumption)
  · split at found <;> simp_all
    simp only [VectorLocal]
    rw [← found]
    exact .pure (by assumption)

private def scanVectors (store : Store) (state : Frame) (code : List AdminInstr)
    (stack : List Value) : CheckedVectorStep store state (values stack ++ code) :=
  match found : vectorScanner.scan store state code stack with
  | none => none
  | some next => some ⟨next, vectorScanner_sound found⟩

def stepVectors (store : Store) (state : Frame) (code : List AdminInstr) :
    Option (Store × List AdminInstr) := (scanVectors store state code []).map Subtype.val

theorem stepVectors_sound (h : stepVectors store state code = some next) :
    VectorStep store state code next.1 next.2 := by
  unfold stepVectors at h
  cases hs : scanVectors store state code [] with
  | none => simp [hs] at h
  | some result => simp [hs] at h; subst next; simpa [values] using result.property

private theorem VectorStep.family (reduced : VectorStep store state code next code') :
    FamilyStep VectorLocal store state code next code' := by
  induction reduced with
  | redex h =>
    cases h with
    | pure evaluated => exact .redex (.pure evaluated)
    | memory memory evaluated => exact .redex (.memory memory evaluated)
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

private theorem evalVectorMemory_arity
    (found : evalVectorMemory store state op args = some output) :
    args.length = op.opcode.signature.params.length := by
  by_cases same : args.length = op.opcode.signature.params.length
  · exact same
  · simp [evalVectorMemory, same] at found

/-- The SIMD scanner finds any permitted integer, bitwise, or memory successor. -/
theorem stepVectors_complete (reduced : VectorStep store state code next code') :
    (stepVectors store state code).isSome = true := by
  have success : (vectorScanner.step store state code).isSome = true := by
    apply vectorScanner.step_complete (redex := VectorLocal) ?_ reduced.family
    intro state instruction args next code reduced
    cases instruction <;> simp only [VectorLocal] at reduced
    all_goals try contradiction
    rename_i instr
    cases instr <;> simp only [VectorLocal] at reduced
    all_goals try contradiction
    refine ⟨by simp [AdminInstr.ScannerAtom], ?_⟩
    cases reduced with
    | pure evaluated =>
      obtain ⟨arity, memory⟩ := evalVector_arity evaluated
      simp only [vectorScanner, arity, Option.isSome_map, checkedVectorRedex, memory]
      repeat first | simp_all | split
    | memory memory evaluated =>
      have arity := evalVectorMemory_arity evaluated
      simp only [vectorScanner, arity, Option.isSome_map, checkedVectorRedex, memory]
      repeat first | simp_all | split
  simp only [stepVectors, scanVectors, FamilyScanner.step] at *
  split <;> simp_all

#print axioms stepVectors_complete

theorem VectorStep.resources_preserved (h : VectorStep store state code next code') :
    next.funcs = store.funcs ∧ next.globals = store.globals ∧
      next.mems.length = store.mems.length ∧ next.datas = store.datas ∧
      next.tables = store.tables ∧ next.elems = store.elems := by
  induction h with
  | redex reduced =>
    cases reduced with
    | pure => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | @memory _ _ _ _ write _ _ =>
      cases write <;> simp [vectorMemoryStore, Store.setMemory]
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

end Wasm
