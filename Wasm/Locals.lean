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

/-- Find a local redex at the active evaluation position, without skipping instructions. -/
def checkedLocalStep (state : Frame) (es : List AdminInstr) : CheckedLocalStep state es := by
  match es with
  | .instr (.localGet x) :: tail =>
    match h : state.locals[x]? with
    | some (some v) => exact some ⟨(state, .instr (.const v) :: tail), by
        simpa [values] using LocalStep.context (vs := []) (tail := tail) (LocalStep.get h)⟩
    | _ => exact none
  | .instr (.const v) :: .instr (.localSet x) :: tail =>
    if h : x < state.locals.length then
      exact some ⟨({state with locals := state.locals.set x (some v)}, tail), by
        simpa [values] using LocalStep.context (vs := []) (tail := tail) (LocalStep.set h)⟩
    else exact none
  | .instr (.const v) :: .instr (.localTee x) :: tail =>
    exact some ⟨(state, .instr (.const v) :: .instr (.const v) :: .instr (.localSet x) :: tail), by
      simpa [values] using LocalStep.context (vs := []) (tail := tail) (LocalStep.tee (v := v))⟩
  | .instr (.const v) :: tail =>
    exact (checkedLocalStep state tail).map fun next =>
      ⟨(next.val.1, .instr (.const v) :: next.val.2), by
        simpa [values] using LocalStep.context (vs := [v]) (tail := []) next.property⟩
  | .label n continuation body :: tail =>
    exact (checkedLocalStep state body).map fun next =>
      ⟨(next.val.1, .label n continuation next.val.2 :: tail), by
        simpa [values] using LocalStep.context (vs := []) (tail := tail)
          (LocalStep.label next.property)⟩
  | .handler catches body :: tail =>
    exact (checkedLocalStep state body).map fun next =>
      ⟨(next.val.1, .handler catches next.val.2 :: tail), by
        simpa [values] using LocalStep.context (vs := []) (tail := tail)
          (LocalStep.handler next.property)⟩
  | .frame n inner body :: tail =>
    exact (checkedLocalStep inner body).map fun next =>
      ⟨(state, .frame n next.val.1 next.val.2 :: tail), by
        simpa [values] using LocalStep.context (vs := []) (tail := tail)
          (LocalStep.frame next.property)⟩
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

private theorem stepLocals_eq (state : Frame) (code : List AdminInstr) :
    stepLocals state code = match code with
    | .instr (.localGet x) :: tail =>
      match state.locals[x]? with
      | some (some v) => some (state, .instr (.const v) :: tail)
      | _ => none
    | .instr (.const v) :: .instr (.localSet x) :: tail =>
      if x < state.locals.length then
        some ({state with locals := state.locals.set x (some v)}, tail) else none
    | .instr (.const v) :: .instr (.localTee x) :: tail =>
      some (state, .instr (.const v) :: .instr (.const v) :: .instr (.localSet x) :: tail)
    | .instr (.const v) :: tail =>
      (stepLocals state tail).map fun next => (next.1, .instr (.const v) :: next.2)
    | .label n continuation body :: tail =>
      (stepLocals state body).map fun next => (next.1, .label n continuation next.2 :: tail)
    | .handler catches body :: tail =>
      (stepLocals state body).map fun next => (next.1, .handler catches next.2 :: tail)
    | .frame n inner body :: tail =>
      (stepLocals inner body).map fun next => (state, .frame n next.1 next.2 :: tail)
    | _ => none := by
  cases code with
  | nil => simp [stepLocals, checkedLocalStep]
  | cons head tail =>
    cases head with
    | instr op =>
      cases op <;> simp only [stepLocals, checkedLocalStep, Option.map_map, Function.comp_def]
      all_goals try rfl
      · cases tail with
        | nil => simp only [checkedLocalStep, Option.map_map, Function.comp_def] <;> rfl
        | cons second rest =>
          cases second with
          | instr op =>
            cases op <;> simp only [checkedLocalStep, Option.map_map, Function.comp_def]
            all_goals try rfl
            split <;> simp_all
          | _ => simp only [checkedLocalStep, Option.map_map, Function.comp_def] <;> rfl
      · split <;> simp_all
    | _ => simp only [stepLocals, checkedLocalStep, Option.map_map, Function.comp_def] <;> rfl

private theorem local_success_tail
    (success : stepLocals state code = some next) (tail : List AdminInstr) :
    stepLocals state (code ++ tail) = some (next.1, next.2 ++ tail) := by
  induction code generalizing state next with
  | nil => rw [stepLocals_eq] at success; contradiction
  | cons head code ih =>
    rw [stepLocals_eq] at success ⊢
    cases head with
    | instr op =>
      cases op <;> simp only [List.cons_append] at success ⊢
      all_goals try contradiction
      · rename_i value
        cases code with
        | nil => simp only [stepLocals_eq, Option.map_none] at success; contradiction
        | cons second rest =>
          cases second with
          | instr op =>
            cases op <;> simp only [List.cons_append] at success ⊢
            all_goals first
              | obtain ⟨inner, found, same⟩ := Option.map_eq_some_iff.mp success
                subst next
                have lifted := congrArg
                  (Option.map (fun pair => (pair.1, .instr (.const value) :: pair.2))) (ih found)
                simpa only [List.cons_append, Option.map_some] using lifted
              | split at success
                · simp only [Option.some.injEq] at success
                  cases success; simp_all
                · contradiction
              | cases success; rfl
          | _ =>
            simp only [List.cons_append] at success ⊢
            obtain ⟨inner, found, same⟩ := Option.map_eq_some_iff.mp success
            subst next
            have lifted := congrArg
              (Option.map (fun pair => (pair.1, .instr (.const value) :: pair.2))) (ih found)
            simpa only [List.cons_append, Option.map_some] using lifted
      · split at success <;> try simp only [Option.some.injEq] at success
        all_goals try contradiction
        cases success; rfl
    | label _ _ _ | handler _ _ | frame _ _ _ =>
      simp only [List.cons_append] at success ⊢
      obtain ⟨inner, found, same⟩ := Option.map_eq_some_iff.mp success
      cases same
      simp [found]
    | _ => contradiction

private theorem local_success_const (success : stepLocals state code = some next) (v : Value) :
    stepLocals state (.instr (.const v) :: code) =
      some (next.1, .instr (.const v) :: next.2) := by
  cases code with
  | nil => rw [stepLocals_eq] at success; contradiction
  | cons head tail =>
    rw [stepLocals_eq]
    cases head with
    | instr op =>
      cases op <;> simp only
      all_goals first
        | rw [success]; rfl
        | rw [stepLocals_eq] at success; contradiction
    | _ => simp only; rw [success]; rfl

private theorem local_success_prefix (success : stepLocals state code = some next)
    (vs : List Value) :
    stepLocals state (values vs ++ code) = some (next.1, values vs ++ next.2) := by
  induction vs with
  | nil => simpa [values] using success
  | cons v vs ih => simpa [values] using local_success_const ih v

/-- Every local reduction, including evaluation contexts, is recognized by the local executor. -/
theorem stepLocals_complete (h : LocalStep state code state' code') :
    stepLocals state code = some (state', code') := by
  induction h with
  | get lookup => simp [stepLocals_eq, lookup, values]
  | set bound => simp [stepLocals_eq, bound]
  | tee => simp [stepLocals_eq]
  | context _ ih =>
    simpa [List.append_assoc] using local_success_prefix (local_success_tail ih _) _
  | label _ ih | handler _ ih | frame _ ih =>
    rw [stepLocals_eq]
    simp only [ih, Option.map_some]

/-- Soundness and completeness characterize all successful local steps. -/
theorem stepLocals_iff : stepLocals state code = some (state', code') ↔
    LocalStep state code state' code' := ⟨stepLocals_sound, stepLocals_complete⟩

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
