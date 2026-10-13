import Wasm.FamilyScanner

/-! Operand scanning for progress and resource-limit probes at the same evaluation position. -/
namespace Wasm

def scanOperands (operands : Frame → AdminInstr → Option Nat)
    (probe : Store → Frame → AdminInstr → List Value → Option α)
    (store : Store) (state : Frame) (code : List AdminInstr) (stack : List Value) : Option α :=
  match code with
  | .instr (.const value) :: tail => scanOperands operands probe store state tail (stack ++ [value])
  | .label _ _ body :: _ | .handler _ body :: _ => scanOperands operands probe store state body []
  | .frame _ inner body :: _ => scanOperands operands probe store inner body []
  | op :: _ => do
    let count ← operands state op
    if count ≤ stack.length then probe store state op (stack.drop (stack.length - count)) else none
  | [] => none
termination_by sizeOf code

def hasOperands (operands : Frame → AdminInstr → Option Nat)
    (probe : Store → Frame → AdminInstr → List Value → Bool)
    (store : Store) (state : Frame) (code : List AdminInstr) (stack : List Value) : Bool :=
  match code with
  | .instr (.const value) :: tail => hasOperands operands probe store state tail (stack ++ [value])
  | .label _ _ body :: _ | .handler _ body :: _ => hasOperands operands probe store state body []
  | .frame _ inner body :: _ => hasOperands operands probe store inner body []
  | op :: _ => match operands state op with
    | some count => if count ≤ stack.length then probe store state op (stack.drop (stack.length - count)) else false
    | none => false
  | [] => false
termination_by sizeOf code

private theorem operand_probe_isSome (counts : Option Nat) (stack : List Value)
    (probe : Nat → Option α) :
    (counts.bind fun count => if count ≤ stack.length then probe count else none).isSome =
      (match counts with
        | some count => if count ≤ stack.length then (probe count).isSome else false
        | none => false) := by
  cases counts with
  | none => rfl
  | some count =>
    by_cases bound : count ≤ stack.length <;> simp [Option.bind, bound]

private theorem operand_probe_or (counts : Option Nat) (stack : List Value)
    (left right : Nat → Bool) :
    (match counts with
      | some count => if count ≤ stack.length then left count || right count else false
      | none => false) =
    ((match counts with
      | some count => if count ≤ stack.length then left count else false
      | none => false) ||
     (match counts with
      | some count => if count ≤ stack.length then right count else false
      | none => false)) := by
  cases counts with
  | none => rfl
  | some count =>
    by_cases bound : count ≤ stack.length <;> simp [bound]

theorem scanOperands_isSome :
    (scanOperands operands probe store state code stack).isSome =
      hasOperands operands (fun store state op args => (probe store state op args).isSome)
        store state code stack := by
  cases code with
  | nil => simp [scanOperands, hasOperands]
  | cons op tail =>
    cases op with
    | instr instr =>
      cases instr with
      | const value =>
        simp only [scanOperands, hasOperands]
        exact scanOperands_isSome
      | _ =>
        simp only [scanOperands, hasOperands]
        exact operand_probe_isSome _ _ _
    | label n continuation body | handler catches body | frame n inner body =>
      simp only [scanOperands, hasOperands]
      exact scanOperands_isSome
    | _ =>
      simp only [scanOperands, hasOperands]
      exact operand_probe_isSome _ _ _
termination_by sizeOf code

theorem FamilyScanner.scan_isSome_eq_hasOperands (scanner : FamilyScanner) :
    (scanner.scan store state code stack).isSome =
      hasOperands scanner.operands (fun store state op args =>
        (scanner.reduce store state op args).isSome) store state code stack := by
  cases code with
  | nil => simp [scan, hasOperands]
  | cons op tail =>
    cases op with
    | instr instr =>
      cases instr with
      | const value =>
        simp only [scan, hasOperands]
        exact scanner.scan_isSome_eq_hasOperands
      | _ =>
        simp only [scan, hasOperands]
        dsimp only [Bind.bind, Option.bind]
        repeat first | simp_all [Option.isSome_map] | split
        all_goals grind
    | label n continuation body | handler catches body | frame n inner body =>
      simp only [scan, hasOperands, Option.isSome_map]
      exact scanner.scan_isSome_eq_hasOperands
    | _ =>
      simp only [scan, hasOperands]
      dsimp only [Bind.bind, Option.bind]
      repeat first | simp_all [Option.isSome_map] | split
      all_goals grind
termination_by sizeOf code

theorem hasOperands_or :
    hasOperands operands (fun store state op args =>
      left store state op args || right store state op args) store state code stack =
      (hasOperands operands left store state code stack ||
        hasOperands operands right store state code stack) := by
  cases code with
  | nil => simp [hasOperands]
  | cons op tail =>
    cases op with
    | instr instr =>
      cases instr with
      | const value =>
        simp only [hasOperands]
        exact hasOperands_or
      | _ =>
        simp only [hasOperands]
        exact operand_probe_or _ _ _ _
    | label n continuation body | handler catches body | frame n inner body =>
      simp only [hasOperands]
      exact hasOperands_or
    | _ =>
      simp only [hasOperands]
      exact operand_probe_or _ _ _ _
termination_by sizeOf code

#print axioms FamilyScanner.scan_isSome_eq_hasOperands
#print axioms hasOperands_or
end Wasm
