import Wasm.Runtime

namespace Wasm

/-! Local-variable reductions and their label/activation evaluation contexts.
https://webassembly.github.io/spec/core/exec/instructions.html#variable-instructions
-/
inductive LocalStep : Frame → List AdminInstr → Frame → List AdminInstr → Prop where
  | get (h : state.locals[x]? = some (some v)) :
      LocalStep state [.instr (.localGet x)] state (values [v])
  | set (h : x < state.locals.length) :
      LocalStep state [ .instr (.const v), .instr (.localSet x)]
        { state with locals := state.locals.set x (some v) } []
  | tee : LocalStep state [.instr (.const v), .instr (.localTee x)] state
      [.instr (.const v), .instr (.const v), .instr (.localSet x)]
  | context : LocalStep state es state' es' →
      LocalStep state (values vs ++ es ++ tail) state' (values vs ++ es' ++ tail)
  | label : LocalStep state body state' body' →
      LocalStep state [.label n continuation body] state' [.label n continuation body']
  | handler : LocalStep state body state' body' →
      LocalStep state [.handler catches body] state' [.handler catches body']
  | frame : LocalStep inner body inner' body' →
      LocalStep state [.frame n inner body] state [.frame n inner' body']

abbrev CheckedLocalStep (state : Frame) (es : List AdminInstr) :=
  Option { next : Frame × List AdminInstr // LocalStep state es next.1 next.2 }

private def localContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedLocalStep state es) :
    CheckedLocalStep state (values vs ++ es ++ tail) :=
  s.map fun next => ⟨(next.val.1, values vs ++ next.val.2 ++ tail), .context next.property⟩

/-- Find a local redex at the active evaluation position, without skipping instructions. -/
def checkedLocalStep (state : Frame) (es : List AdminInstr) : CheckedLocalStep state es := by
  match es with
  | .instr (.localGet x) :: tail =>
    match h : state.locals[x]? with
    | some (some v) =>
      simpa [values] using localContext [] tail
        (some ⟨(state, values [v]), LocalStep.get h⟩)
    | _ => exact none
  | .instr (.const v) :: .instr (.localSet x) :: tail =>
    if h : x < state.locals.length then
      simpa [values] using localContext [] tail
        (some ⟨({ state with locals := state.locals.set x (some v) }, []), LocalStep.set h⟩)
    else exact none
  | .instr (.const v) :: .instr (.localTee x) :: tail =>
    simpa [values] using localContext [] tail
      (some ⟨(state, [.instr (.const v), .instr (.const v), .instr (.localSet x)]),
        LocalStep.tee⟩)
  | .instr (.const v) :: tail =>
    simpa [values] using localContext [v] [] (checkedLocalStep state tail)
  | .label n continuation body :: tail =>
    let inner : CheckedLocalStep state [.label n continuation body] :=
      (checkedLocalStep state body).map fun next =>
      ⟨(next.val.1, [.label n continuation next.val.2]), LocalStep.label next.property⟩
    simpa [values] using localContext [] tail inner
  | .handler catches body :: tail =>
    let inner : CheckedLocalStep state [.handler catches body] :=
      (checkedLocalStep state body).map fun next =>
      ⟨(next.val.1, [.handler catches next.val.2]), LocalStep.handler next.property⟩
    simpa [values] using localContext [] tail inner
  | .frame n frame body :: tail =>
    let inner : CheckedLocalStep state [.frame n frame body] :=
      (checkedLocalStep frame body).map fun next =>
      ⟨(state, [.frame n next.val.1 next.val.2]), LocalStep.frame next.property⟩
    simpa [values] using localContext [] tail inner
  | _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

def stepLocals (state : Frame) (es : List AdminInstr) : Option (Frame × List AdminInstr) :=
  (checkedLocalStep state es).map Subtype.val

theorem stepLocals_sound (h : stepLocals state es = some next) :
    LocalStep state es next.1 next.2 := by
  unfold stepLocals at h
  cases hs : checkedLocalStep state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

theorem LocalStep.module_preserved (h : LocalStep state es state' es') :
    state'.module = state.module := by
  induction h with
  | get | set | tee | frame => rfl
  | context _ ih | label _ ih | handler _ ih => exact ih

theorem LocalStep.length_preserved (h : LocalStep state es state' es') :
    state'.locals.length = state.locals.length := by
  induction h with
  | get | tee | frame => rfl
  | set => simp
  | context _ ih | label _ ih | handler _ ih => exact ih

end Wasm
