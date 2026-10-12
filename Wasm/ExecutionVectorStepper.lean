import Wasm.ExecutionRuntime

namespace Wasm.Execution


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

private def scanVectors (store : Store) (state : Frame) (code : List AdminInstr)
    (stack : List Value) : CheckedVectorStep store state (values stack ++ code) := by
  match code with
  | .instr (.const value) :: tail =>
    simpa [values, List.map_append, List.append_assoc] using
      scanVectors store state tail (stack ++ [value])
  | .instr instr :: tail =>
    match instr with
    | .vector op =>
      let count := op.opcode.signature.params.length
      if h : count ≤ stack.length then
        let below := stack.take (stack.length - count)
        let args := stack.drop (stack.length - count)
        have split : stack = below ++ args := (List.take_append_drop _ _).symm
        simpa [split, values, List.map_append, List.append_assoc] using
          vectorContext below tail (checkedVectorRedex store state op args)
      else exact none
    | _ => exact none
  | .label n continuation body :: tail =>
    let inner : CheckedVectorStep store state [.label n continuation body] :=
      (scanVectors store state body []).map fun next =>
        ⟨(next.val.1, [.label n continuation next.val.2]), .label next.property⟩
    simpa [values] using vectorContext stack tail inner
  | .handler catches body :: tail =>
    let inner : CheckedVectorStep store state [.handler catches body] :=
      (scanVectors store state body []).map fun next =>
        ⟨(next.val.1, [.handler catches next.val.2]), .handler next.property⟩
    simpa [values] using vectorContext stack tail inner
  | .frame n inner body :: tail =>
    let checked : CheckedVectorStep store state [.frame n inner body] :=
      (scanVectors store inner body []).map fun next =>
        ⟨(next.val.1, [.frame n inner next.val.2]), .frame next.property⟩
    simpa [values] using vectorContext stack tail checked
  | _ => exact none
termination_by sizeOf code

def stepVectors (store : Store) (state : Frame) (code : List AdminInstr) :
    Option (Store × List AdminInstr) := (scanVectors store state code []).map Subtype.val

theorem stepVectors_sound (h : stepVectors store state code = some next) :
    VectorStep store state code next.1 next.2 := by
  unfold stepVectors at h
  cases hs : scanVectors store state code [] with
  | none => simp [hs] at h
  | some result => simp [hs] at h; subst next; simpa [values] using result.property

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

end Wasm.Execution
