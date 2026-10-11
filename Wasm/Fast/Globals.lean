import Wasm.Fast.Runtime

namespace Wasm.Fast

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
  | handler : GlobalStep store state body store' body' →
      GlobalStep store state [.handler catches body] store' [.handler catches body']
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
  | .handler catches body :: tail =>
    let inner : CheckedGlobalStep store state [.handler catches body] :=
      (checkedGlobalStep store state body).map fun next =>
        ⟨(next.val.1, [.handler catches next.val.2]), .handler next.property⟩
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
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem GlobalStep.length_preserved (h : GlobalStep store state es store' es') :
    store'.globals.length = store.globals.length := by
  induction h with
  | get => rfl
  | set => simp [Store.setGlobal]
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

end Wasm.Fast
