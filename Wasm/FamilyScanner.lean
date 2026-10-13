import Wasm.Runtime

/-! Shared value-prefix scanning for instruction families with fixed operand arity. -/
namespace Wasm

abbrev FamilyRedex := Store → Frame → AdminInstr → List Value → Store → List AdminInstr → Prop

/-- Closure of a local instruction-family relation under administrative evaluation contexts. -/
inductive FamilyStep (redex : FamilyRedex) :
    Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | redex : redex store state op args next code' →
      FamilyStep redex store state (values args ++ [op]) next code'
  | context : FamilyStep redex store state code next code' →
      FamilyStep redex store state (values vs ++ code ++ tail) next (values vs ++ code' ++ tail)
  | label : FamilyStep redex store state body next body' →
      FamilyStep redex store state [.label n continuation body] next [.label n continuation body']
  | handler : FamilyStep redex store state body next body' →
      FamilyStep redex store state [.handler catches body] next [.handler catches body']
  | frame : FamilyStep redex store inner body next body' →
      FamilyStep redex store state [.frame n inner body] next [.frame n inner body']

/-- Local recognition and arity; neither field assumes that an executable check succeeds. -/
structure FamilyScanner where
  operands : Frame → AdminInstr → Option Nat
  reduce : Store → Frame → AdminInstr → List Value → Option (Store × List AdminInstr)

/-- Constant prefixes are accumulated; operand selection cannot cross a frame or label boundary. -/
def FamilyScanner.scan (scanner : FamilyScanner) (store : Store) (state : Frame)
    (code : List AdminInstr) (stack : List Value) : Option (Store × List AdminInstr) :=
  match code with
  | .instr (.const value) :: tail => scanner.scan store state tail (stack ++ [value])
  | .label n continuation body :: tail =>
    (scanner.scan store state body []).map fun next =>
      (next.1, values stack ++ [.label n continuation next.2] ++ tail)
  | .handler catches body :: tail =>
    (scanner.scan store state body []).map fun next =>
      (next.1, values stack ++ [.handler catches next.2] ++ tail)
  | .frame n inner body :: tail =>
    (scanner.scan store inner body []).map fun next =>
      (next.1, values stack ++ [.frame n inner next.2] ++ tail)
  | op :: tail => do
    let count ← scanner.operands state op
    if count ≤ stack.length then
      let below := stack.take (stack.length - count)
      let args := stack.drop (stack.length - count)
      (scanner.reduce store state op args).map fun next =>
        (next.1, values below ++ next.2 ++ tail)
    else none
  | [] => none
termination_by sizeOf code

def FamilyScanner.step (scanner : FamilyScanner) (store : Store) (state : Frame)
    (code : List AdminInstr) : Option (Store × List AdminInstr) :=
  scanner.scan store state code []

private theorem scan_values (scanner : FamilyScanner) (vs : List Value) :
    scanner.scan store state (values vs ++ code) stack =
      scanner.scan store state code (stack ++ vs) := by
  induction vs generalizing stack with
  | nil => simp [values]
  | cons v vs ih =>
    simp only [values, List.map_cons, List.cons_append, FamilyScanner.scan]
    simpa only [List.append_assoc, List.singleton_append] using ih (stack := stack ++ [v])

private theorem operand_sound {redex : FamilyRedex} {scanner : FamilyScanner}
    (localSound : ∀ store state op args next, scanner.reduce store state op args = some next →
      redex store state op args next.1 next.2)
    (success : (do
      let count ← scanner.operands state op
      if count ≤ stack.length then
        (scanner.reduce store state op (stack.drop (stack.length - count))).map fun next =>
          (next.1, values (stack.take (stack.length - count)) ++ next.2 ++ tail)
      else none) = some next) :
    FamilyStep redex store state (values stack ++ op :: tail) next.1 next.2 := by
  simp only [Option.bind_eq_bind, Option.bind] at success
  split at success <;> try contradiction
  dsimp only at success
  split at success <;> try contradiction
  obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp success
  cases same
  rename_i count lookup bound
  have matched := FamilyStep.context (vs := stack.take (stack.length - count))
    (tail := tail) (.redex (localSound _ _ _ _ _ found))
  have splitStack := congrArg values (List.take_append_drop (stack.length - count) stack)
  simp only [values, List.map_append] at splitStack
  simpa only [values, ← splitStack, List.append_assoc, List.singleton_append] using matched

/-- The scanner returns only certified family reductions. -/
theorem FamilyScanner.scan_sound {scanner : FamilyScanner} {redex : FamilyRedex}
    (localSound : ∀ store state op args next, scanner.reduce store state op args = some next →
      redex store state op args next.1 next.2)
    (success : scanner.scan store state code stack = some next) :
    FamilyStep redex store state (values stack ++ code) next.1 next.2 := by
  cases code with
  | nil => simp [scan] at success
  | cons op tail =>
    cases op with
    | instr instr =>
      cases instr with
      | const value =>
        simp only [scan] at success
        have inner := FamilyScanner.scan_sound localSound success
        simpa [values, List.map_append, List.append_assoc] using inner
      | _ => simp only [scan] at success; exact operand_sound localSound success
    | label n continuation body =>
      simp only [scan] at success
      obtain ⟨inner, found, same⟩ := Option.map_eq_some_iff.mp success
      cases same
      simpa only [List.append_assoc, List.singleton_append] using
        FamilyStep.context (vs := stack) (tail := tail) (.label (n := n) (continuation := continuation) (by
        simpa [values] using FamilyScanner.scan_sound localSound found))
    | handler catches body =>
      simp only [scan] at success
      obtain ⟨inner, found, same⟩ := Option.map_eq_some_iff.mp success
      cases same
      simpa only [List.append_assoc, List.singleton_append] using
        FamilyStep.context (vs := stack) (tail := tail) (.handler (catches := catches) (by
        simpa [values] using FamilyScanner.scan_sound localSound found))
    | frame n inner body =>
      simp only [scan] at success
      obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp success
      cases same
      simpa only [List.append_assoc, List.singleton_append] using
        FamilyStep.context (vs := stack) (tail := tail) (.frame (state := state) (n := n) (by
        simpa [values] using FamilyScanner.scan_sound localSound found))
    | _ => simp only [scan] at success; exact operand_sound localSound success
termination_by sizeOf code

/-- These administrative instructions are local redex heads rather than scanner contexts. -/
def AdminInstr.ScannerAtom : AdminInstr → Prop
  | .instr (.const _) | .label _ _ _ | .handler _ _ | .frame _ _ _ => False
  | _ => True

private theorem scan_atom (scanner : FamilyScanner) (atom : op.ScannerAtom) :
    scanner.scan store state (op :: tail) stack = (do
      let count ← scanner.operands state op
      if count ≤ stack.length then
        (scanner.reduce store state op (stack.drop (stack.length - count))).map fun next =>
          (next.1, values (stack.take (stack.length - count)) ++ next.2 ++ tail)
      else none) := by
  cases op with
  | instr instr =>
    cases instr <;> simp only [AdminInstr.ScannerAtom] at atom
    all_goals try contradiction
    all_goals simp only [FamilyScanner.scan]
  | _ => simp_all only [AdminInstr.ScannerAtom, FamilyScanner.scan]

/-- A complete local operand list is passed unchanged to its family checker. -/
theorem FamilyScanner.step_atom_isSome {scanner : FamilyScanner}
    (atom : op.ScannerAtom) (arity : scanner.operands state op = some args.length) :
    (scanner.step store state (values args ++ [op])).isSome =
      (scanner.reduce store state op args).isSome := by
  simp only [step, scan_values, List.nil_append]
  rw [scan_atom scanner atom]
  simp [arity]

/-- Local progress and correct arity lift to progress in every scanner context. -/
theorem FamilyScanner.scan_complete {scanner : FamilyScanner} {redex : FamilyRedex}
    (localComplete : ∀ state op args next code,
      redex store state op args next code → op.ScannerAtom ∧
        scanner.operands state op = some args.length ∧
        (scanner.reduce store state op args).isSome = true)
    (reduced : FamilyStep redex store state code next code') (stack : List Value)
    (tail : List AdminInstr) : (scanner.scan store state (code ++ tail) stack).isSome = true := by
  induction reduced generalizing stack tail with
  | @redex state op args next code' reduced =>
    obtain ⟨atom, arity, success⟩ := localComplete _ _ _ _ _ reduced
    rw [List.append_assoc, List.singleton_append, scan_values, scan_atom scanner atom]
    simp only [arity]
    simp [success]
  | @context state code next code' vs suffix reduced ih =>
    simpa only [List.append_assoc, scan_values] using ih (stack ++ vs) (suffix ++ tail)
  | label reduced ih | handler reduced ih | frame reduced ih =>
    simp only [List.singleton_append, scan, Option.isSome_map]
    simpa only [List.append_nil] using ih [] []

/-- Progress completeness of a family scanner, with no assumption on the selected successor. -/
theorem FamilyScanner.step_complete {scanner : FamilyScanner} {redex : FamilyRedex}
    (localComplete : ∀ state op args next code,
      redex store state op args next code → op.ScannerAtom ∧
        scanner.operands state op = some args.length ∧
        (scanner.reduce store state op args).isSome = true)
    (reduced : FamilyStep redex store state code next code') :
    (scanner.step store state code).isSome = true := by
  simpa [step] using scanner.scan_complete localComplete reduced [] []

/-- A state predicate holds for every administrative frame nested in an instruction. -/
def AdminInstr.FramesValid (domain : Frame → Prop) : AdminInstr → Prop
  | .frame _ inner body => domain inner ∧ ∀ instruction ∈ body, instruction.FramesValid domain
  | .label _ _ body | .handler _ body | .tailActivation body =>
      ∀ instruction ∈ body, instruction.FramesValid domain
  | _ => True
termination_by instruction => sizeOf instruction

def CodeFramesValid (domain : Frame → Prop) (code : List AdminInstr) : Prop :=
  ∀ instruction ∈ code, instruction.FramesValid domain

@[simp] theorem codeFramesValid_append : CodeFramesValid domain (left ++ right) ↔
    CodeFramesValid domain left ∧ CodeFramesValid domain right := by
  simp [CodeFramesValid, List.mem_append, or_imp, forall_and]

@[simp] theorem codeFramesValid_values : CodeFramesValid domain (values vs) := by
  simp [CodeFramesValid, values, AdminInstr.FramesValid]

@[simp] theorem codeFramesValid_singleton : CodeFramesValid domain [instruction] ↔
    instruction.FramesValid domain := by
  simp [CodeFramesValid]

/-- The same scanner proof applies when local recognition requires valid frame declarations. -/
theorem FamilyScanner.scan_complete_on {scanner : FamilyScanner} {redex : FamilyRedex}
    {domain : Frame → Prop}
    (localComplete : ∀ state op args next code, domain state →
      redex store state op args next code → op.ScannerAtom ∧
        scanner.operands state op = some args.length ∧
        (scanner.reduce store state op args).isSome = true)
    (reduced : FamilyStep redex store state code next code') (valid : domain state)
    (frames : CodeFramesValid domain code) (stack : List Value) (tail : List AdminInstr) :
    (scanner.scan store state (code ++ tail) stack).isSome = true := by
  induction reduced generalizing stack tail with
  | @redex state op args next code' reduced =>
    obtain ⟨atom, arity, success⟩ := localComplete _ _ _ _ _ valid reduced
    rw [List.append_assoc, List.singleton_append, scan_values, scan_atom scanner atom]
    simp [arity, success]
  | @context state code next code' vs suffix reduced ih =>
    simp only [codeFramesValid_append, codeFramesValid_values, true_and] at frames
    simpa only [List.append_assoc, scan_values] using
      ih valid frames.1 (stack ++ vs) (suffix ++ tail)
  | label reduced ih | handler reduced ih =>
    simp only [codeFramesValid_singleton, AdminInstr.FramesValid] at frames
    simp only [List.singleton_append, scan, Option.isSome_map]
    simpa only [List.append_nil] using ih valid frames [] []
  | frame reduced ih =>
    simp only [codeFramesValid_singleton, AdminInstr.FramesValid] at frames
    simp only [List.singleton_append, scan, Option.isSome_map]
    simpa only [List.append_nil] using ih frames.1 frames.2 [] []

theorem FamilyScanner.step_complete_on {scanner : FamilyScanner} {redex : FamilyRedex}
    {domain : Frame → Prop}
    (localComplete : ∀ state op args next code, domain state →
      redex store state op args next code → op.ScannerAtom ∧
        scanner.operands state op = some args.length ∧
        (scanner.reduce store state op args).isSome = true)
    (reduced : FamilyStep redex store state code next code') (valid : domain state)
    (frames : CodeFramesValid domain code) : (scanner.step store state code).isSome = true := by
  simpa [step] using scanner.scan_complete_on localComplete reduced valid frames [] []

/-- An instruction predicate interpreted in the module of each enclosing frame. -/
def AdminInstr.ScopedValid (domain : Frame → AdminInstr → Prop) (state : Frame) : AdminInstr → Prop
  | .frame _ inner body => ∀ instruction ∈ body, instruction.ScopedValid domain inner
  | .label _ _ body | .handler _ body => ∀ instruction ∈ body, instruction.ScopedValid domain state
  | instruction => domain state instruction
termination_by instruction => sizeOf instruction

def CodeScopedValid (domain : Frame → AdminInstr → Prop) (state : Frame)
    (code : List AdminInstr) : Prop := ∀ instruction ∈ code, instruction.ScopedValid domain state

@[simp] theorem codeScopedValid_append : CodeScopedValid domain state (left ++ right) ↔
    CodeScopedValid domain state left ∧ CodeScopedValid domain state right := by
  simp [CodeScopedValid, List.mem_append, or_imp, forall_and]

@[simp] theorem codeScopedValid_singleton : CodeScopedValid domain state [instruction] ↔
    instruction.ScopedValid domain state := by simp [CodeScopedValid]

theorem AdminInstr.ScannerAtom.scopedValid_eq {instruction : AdminInstr} {state : Frame}
    {domain : Frame → AdminInstr → Prop} (atom : instruction.ScannerAtom) :
    instruction.ScopedValid domain state = domain state instruction := by
  cases instruction <;> simp_all [AdminInstr.ScannerAtom, AdminInstr.ScopedValid]

theorem FamilyScanner.scan_complete_scoped {scanner : FamilyScanner} {redex : FamilyRedex}
    {domain : Frame → AdminInstr → Prop}
    (localComplete : ∀ state op args next code, domain state op →
      redex store state op args next code → op.ScannerAtom ∧
        scanner.operands state op = some args.length ∧
        (scanner.reduce store state op args).isSome = true)
    (atoms : ∀ state op args next code, redex store state op args next code → op.ScannerAtom)
    (reduced : FamilyStep redex store state code next code')
    (valid : CodeScopedValid domain state code) (stack : List Value) (tail : List AdminInstr) :
    (scanner.scan store state (code ++ tail) stack).isSome = true := by
  induction reduced generalizing stack tail with
  | @redex state op args next code' reduced =>
    have atom := atoms _ _ _ _ _ reduced
    have ready := valid op (by simp)
    rw [atom.scopedValid_eq] at ready
    obtain ⟨_, arity, success⟩ := localComplete _ _ _ _ _ ready reduced
    rw [List.append_assoc, List.singleton_append, scan_values, scan_atom scanner atom]
    simp [arity, success]
  | @context state code next code' vs suffix reduced ih =>
    simp only [codeScopedValid_append] at valid
    simpa only [List.append_assoc, scan_values] using ih valid.1.2 (stack ++ vs) (suffix ++ tail)
  | label reduced ih | handler reduced ih | frame reduced ih =>
    simp only [codeScopedValid_singleton, AdminInstr.ScopedValid] at valid
    simp only [List.singleton_append, scan, Option.isSome_map]
    simpa only [List.append_nil] using ih valid [] []

theorem FamilyScanner.step_complete_scoped {scanner : FamilyScanner} {redex : FamilyRedex}
    {domain : Frame → AdminInstr → Prop}
    (localComplete : ∀ state op args next code, domain state op →
      redex store state op args next code → op.ScannerAtom ∧
        scanner.operands state op = some args.length ∧
        (scanner.reduce store state op args).isSome = true)
    (atoms : ∀ state op args next code, redex store state op args next code → op.ScannerAtom)
    (reduced : FamilyStep redex store state code next code')
    (valid : CodeScopedValid domain state code) : (scanner.step store state code).isSome = true := by
  simpa [step] using scanner.scan_complete_scoped localComplete atoms reduced valid [] []

#print axioms FamilyScanner.scan_sound
#print axioms FamilyScanner.scan_complete

end Wasm
