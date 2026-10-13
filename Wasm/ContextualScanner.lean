import Wasm.FamilyScanner

/-! Scanning with administrative exits that take priority over nested reductions. -/
namespace Wasm

abbrev ContextualRedex := Store → Frame → List AdminInstr → Store → List AdminInstr → Prop

inductive ContextualStep (redex : ContextualRedex) :
    Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | redex : redex store state code next code' → ContextualStep redex store state code next code'
  | context : ContextualStep redex store state code next code' →
      ContextualStep redex store state (values vs ++ code ++ tail) next (values vs ++ code' ++ tail)
  | label : ContextualStep redex store state body next body' →
      ContextualStep redex store state [.label n continuation body] next [.label n continuation body']
  | handler : ContextualStep redex store state body next body' →
      ContextualStep redex store state [.handler catches body] next [.handler catches body']
  | frame : ContextualStep redex store inner body next body' →
      ContextualStep redex store state [.frame n inner body] next [.frame n inner body']

structure ContextualScanner where
  leaf : Store → Frame → AdminInstr → List Value → List AdminInstr →
    Option (Store × List AdminInstr)
  boundary : Store → Frame → AdminInstr → Option (Store × List AdminInstr)

def ContextualScanner.scan (scanner : ContextualScanner) (store : Store) (state : Frame)
    (code : List AdminInstr) (stack : List Value) : Option (Store × List AdminInstr) :=
  match code with
  | .instr (.const value) :: tail => scanner.scan store state tail (stack ++ [value])
  | .label n continuation body :: tail =>
    match scanner.boundary store state (.label n continuation body) with
    | some next => some (next.1, values stack ++ next.2 ++ tail)
    | none => (scanner.scan store state body []).map fun next =>
        (next.1, values stack ++ [.label n continuation next.2] ++ tail)
  | .handler catches body :: tail =>
    match scanner.boundary store state (.handler catches body) with
    | some next => some (next.1, values stack ++ next.2 ++ tail)
    | none => (scanner.scan store state body []).map fun next =>
        (next.1, values stack ++ [.handler catches next.2] ++ tail)
  | .frame n inner body :: tail =>
    match scanner.boundary store state (.frame n inner body) with
    | some next => some (next.1, values stack ++ next.2 ++ tail)
    | none => (scanner.scan store inner body []).map fun next =>
        (next.1, values stack ++ [.frame n inner next.2] ++ tail)
  | op :: tail => scanner.leaf store state op stack tail
  | [] => none
termination_by sizeOf code

def ContextualScanner.step (scanner : ContextualScanner) (store : Store) (state : Frame)
    (code : List AdminInstr) := scanner.scan store state code []

theorem ContextualScanner.scan_values (scanner : ContextualScanner) (vs : List Value) :
    scanner.scan store state (values vs ++ code) stack =
      scanner.scan store state code (stack ++ vs) := by
  induction vs generalizing stack with
  | nil => simp [values]
  | cons value vs ih =>
    simp only [values, List.map_cons, List.cons_append, scan]
    simpa only [List.append_assoc, List.singleton_append] using ih (stack := stack ++ [value])

theorem ContextualScanner.scan_sound {scanner : ContextualScanner} {redex : ContextualRedex}
    (leafSound : ∀ store state op stack tail next,
      scanner.leaf store state op stack tail = some next →
      ContextualStep redex store state (values stack ++ op :: tail) next.1 next.2)
    (boundarySound : ∀ store state op next, scanner.boundary store state op = some next →
      ContextualStep redex store state [op] next.1 next.2)
    (success : scanner.scan store state code stack = some next) :
    ContextualStep redex store state (values stack ++ code) next.1 next.2 := by
  cases code with
  | nil => simp [scan] at success
  | cons op tail =>
    cases op with
    | instr instr =>
      cases instr with
      | const value =>
        simp only [scan] at success
        have inner := ContextualScanner.scan_sound leafSound boundarySound success
        simpa [values, List.map_append, List.append_assoc] using inner
      | _ => simp only [scan] at success; exact leafSound _ _ _ _ _ _ success
    | label n continuation body | handler catches body | frame n inner body =>
      simp only [scan] at success
      split at success
      · simp only [Option.some.injEq] at success
        cases success
        simpa only [List.append_assoc, List.singleton_append] using
          ContextualStep.context (vs := stack) (tail := tail) (boundarySound _ _ _ _ (by assumption))
      · obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp success
        cases same
        have inner := ContextualScanner.scan_sound leafSound boundarySound found
        simp only [values, List.map_nil, List.nil_append] at inner
        first
          | simpa only [List.append_assoc, List.singleton_append] using
              ContextualStep.context (vs := stack) (tail := tail) (.label inner)
          | simpa only [List.append_assoc, List.singleton_append] using
              ContextualStep.context (vs := stack) (tail := tail) (.handler inner)
          | simpa only [List.append_assoc, List.singleton_append] using
              ContextualStep.context (vs := stack) (tail := tail) (.frame inner)
    | _ => simp only [scan] at success; exact leafSound _ _ _ _ _ _ success
termination_by sizeOf code

/-- A successful boundary exit or a successful inner scan provides progress. -/
theorem ContextualScanner.scan_complete {scanner : ContextualScanner} {redex : ContextualRedex}
    {domain : Frame → AdminInstr → Prop}
    (localComplete : ∀ state code next code', redex store state code next code' →
      CodeScopedValid domain state code → ∀ stack tail,
        (scanner.scan store state (code ++ tail) stack).isSome = true)
    (reduced : ContextualStep redex store state code next code')
    (valid : CodeScopedValid domain state code) (stack : List Value) (tail : List AdminInstr) :
    (scanner.scan store state (code ++ tail) stack).isSome = true := by
  induction reduced generalizing stack tail with
  | redex h => exact localComplete _ _ _ _ h valid stack tail
  | @context state code next code' vs suffix reduced ih =>
    simp only [codeScopedValid_append] at valid
    simpa only [List.append_assoc, scan_values] using ih valid.1.2 (stack ++ vs) (suffix ++ tail)
  | label reduced ih | handler reduced ih | frame reduced ih =>
    simp only [codeScopedValid_singleton, AdminInstr.ScopedValid] at valid
    simp only [List.singleton_append, scan]
    split
    · rfl
    · simp only [Option.isSome_map]
      simpa only [List.append_nil] using ih valid [] []

theorem AdminInstr.scopedValid_true (instruction : AdminInstr) (state : Frame) :
    instruction.ScopedValid (fun _ _ => True) state := by
  cases instruction with
  | label n continuation body | handler catches body | frame n inner body =>
    simp only [ScopedValid]
    intro op member
    exact op.scopedValid_true _
  | _ => simp only [ScopedValid]
termination_by sizeOf instruction

theorem codeScopedValid_true (state : Frame) (code : List AdminInstr) :
    CodeScopedValid (fun _ _ => True) state code := by
  intro instruction _
  exact instruction.scopedValid_true state

theorem ContextualScanner.step_complete {scanner : ContextualScanner} {redex : ContextualRedex}
    {domain : Frame → AdminInstr → Prop}
    (localComplete : ∀ state code next code', redex store state code next code' →
      CodeScopedValid domain state code → ∀ stack tail,
        (scanner.scan store state (code ++ tail) stack).isSome = true)
    (reduced : ContextualStep redex store state code next code')
    (valid : CodeScopedValid domain state code) : (scanner.step store state code).isSome = true := by
  simpa [step] using scanner.scan_complete localComplete reduced valid [] []

#print axioms ContextualScanner.scan_sound
#print axioms ContextualScanner.scan_complete
end Wasm
