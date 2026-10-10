import Wasm.Runtime

namespace Wasm

/-! Global instances use store addresses resolved through the active module.
Mutability and value types are validation premises, not dynamic trap conditions.
https://webassembly.github.io/spec/core/exec/instructions.html#variable-instructions
-/
def ModuleInst.globalAddr? (module : ModuleInst) (index : Nat) : Option GlobalAddr :=
  module.globals[index]?

def Store.global? (store : Store) (address : GlobalAddr) : Option GlobalInst :=
  store.globals[address.index]?

def Store.resolveGlobal? (store : Store) (module : ModuleInst) (index : Nat) : Option GlobalInst :=
  (module.globalAddr? index).bind store.global?

def Store.allocateGlobal (store : Store) (global : GlobalInst) : GlobalAddr × Store :=
  (⟨store.globals.length⟩, { store with globals := store.globals ++ [global] })

theorem Store.allocateGlobal_lookup (store : Store) (global : GlobalInst) :
    (store.allocateGlobal global).2.global? (store.allocateGlobal global).1 = some global := by
  simp [Store.allocateGlobal, Store.global?]

theorem Store.allocateGlobal_preserves (store : Store) (global : GlobalInst) (address : GlobalAddr)
    (h : address.index < store.globals.length) :
    (store.allocateGlobal global).2.global? address = store.global? address := by
  simp [Store.allocateGlobal, Store.global?, List.getElem?_append, h]

def Store.setGlobal (store : Store) (address : GlobalAddr) (global : GlobalInst) : Store :=
  { store with globals := store.globals.set address.index global }

theorem Store.setGlobal_types (store : Store) (address : GlobalAddr)
    (global : GlobalInst) (value : Value) (hg : store.global? address = some global) :
    (store.setGlobal address { global with value }).globals.map GlobalInst.type =
      store.globals.map GlobalInst.type := by
  apply List.ext_getElem?
  intro i
  by_cases h : address.index = i
  · subst i
    obtain ⟨bound, he⟩ := List.getElem?_eq_some_iff.mp hg
    simp [Store.setGlobal, bound, he]
  · simp [Store.setGlobal, List.getElem?_map, List.getElem?_set_ne h]

inductive GlobalStep : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | get (ha : state.module.globalAddr? x = some address)
      (hg : store.global? address = some global) :
      GlobalStep store state [.instr (.globalGet x)] store (values [global.value])
  | set (ha : state.module.globalAddr? x = some address)
      (hg : store.global? address = some global) (hv : Typed store v global.type.valType) :
      GlobalStep store state [.instr (.const v), .instr (.globalSet x)]
        (store.setGlobal address { global with value := v }) []
  | context : GlobalStep store state es store' es' →
      GlobalStep store state (values vs ++ es ++ tail) store' (values vs ++ es' ++ tail)
  | label : GlobalStep store state body store' body' →
      GlobalStep store state [.label n continuation body] store' [.label n continuation body']
  | frame : GlobalStep store inner body store' body' →
      GlobalStep store state [.frame n inner body] store' [.frame n inner body']

abbrev CheckedGlobalStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : Store × List AdminInstr // GlobalStep store state es next.1 next.2 }

private def globalContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedGlobalStep store state es) :
    CheckedGlobalStep store state (values vs ++ es ++ tail) :=
  s.map fun next => ⟨(next.val.1, values vs ++ next.val.2 ++ tail), .context next.property⟩

def checkedGlobalStep (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedGlobalStep store state es := by
  match es with
  | .instr (.globalGet x) :: tail =>
    match ha : state.module.globalAddr? x with
    | none => exact none
    | some address =>
      match hg : store.global? address with
      | none => exact none
      | some global =>
        simpa [values] using globalContext [] tail
          (some ⟨(store, values [global.value]), GlobalStep.get ha hg⟩)
  | .instr (.const v) :: .instr (.globalSet x) :: tail =>
    match ha : state.module.globalAddr? x with
    | none => exact none
    | some address =>
      match hg : store.global? address with
      | none => exact none
      | some global =>
        match checkValue store v global.type.valType with
        | none => exact none
        | some proof =>
          simpa [values] using globalContext [] tail
            (some ⟨(store.setGlobal address { global with value := v }, []),
              GlobalStep.set ha hg proof.down⟩)
  | .instr (.const v) :: tail =>
    simpa [values] using globalContext [v] [] (checkedGlobalStep store state tail)
  | .label n continuation body :: tail =>
    let inner : CheckedGlobalStep store state [.label n continuation body] :=
      (checkedGlobalStep store state body).map fun next =>
        ⟨(next.val.1, [.label n continuation next.val.2]), .label next.property⟩
    simpa [values] using globalContext [] tail inner
  | .frame n frame body :: tail =>
    let inner : CheckedGlobalStep store state [.frame n frame body] :=
      (checkedGlobalStep store frame body).map fun next =>
        ⟨(next.val.1, [.frame n frame next.val.2]), .frame next.property⟩
    simpa [values] using globalContext [] tail inner
  | _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

def stepGlobals (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (Store × List AdminInstr) :=
  (checkedGlobalStep store state es).map Subtype.val

theorem stepGlobals_sound (h : stepGlobals store state es = some next) :
    GlobalStep store state es next.1 next.2 := by
  unfold stepGlobals at h
  cases hs : checkedGlobalStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

theorem GlobalStep.functions_preserved (h : GlobalStep store state es store' es') :
    store'.funcs = store.funcs := by
  induction h with
  | get | set => rfl
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem GlobalStep.length_preserved (h : GlobalStep store state es store' es') :
    store'.globals.length = store.globals.length := by
  induction h with
  | get => rfl
  | set => simp [Store.setGlobal]
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem GlobalStep.types_preserved (h : GlobalStep store state es store' es') :
    store'.globals.map GlobalInst.type = store.globals.map GlobalInst.type := by
  induction h with
  | get => rfl
  | set _ hg _ => exact Store.setGlobal_types _ _ _ _ hg
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem GlobalInst.valid_set {store : Store} {global : GlobalInst} {value : Value}
    {address : GlobalAddr} (h : Typed store value global.type.valType) :
    ({ global with value } : GlobalInst).Valid
      (store.setGlobal address { global with value }) :=
  h.store_funcs rfl

end Wasm
