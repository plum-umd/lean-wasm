import Wasm.Validation
import Wasm.Reduction

/-!
First type-safety lemmas for the store-independent integer arithmetic redexes.
These establish local progress and result typing, not configuration type safety.
The premises are the integer instruction typing side condition and canonical
operand types. No executable-stepper success is assumed in the progress proofs.
-/

namespace Wasm.TypeSafety

theorem evalBinOp_total (ht : t.IsInteger) (ha : a.type = t) (hb : b.type = t) :
    ∃ result, evalBinOp t op a b = some result := by
  cases t <;> cases a <;> cases b <;>
    simp_all [ValType.IsInteger, Value.type, evalBinOp]

theorem evalEqz_total (ht : t.IsInteger) (ha : a.type = t) :
    ∃ result, evalEqz t a = some result := by
  cases t <;> cases a <;> simp_all [ValType.IsInteger, Value.type, evalEqz]

theorem evalBinOp_type (h : evalBinOp t op a b = some result) : result.type = t := by
  cases t <;> cases a <;> cases b <;> simp_all [evalBinOp, Value.type] <;>
    subst result <;> rfl

theorem evalEqz_type (h : evalEqz t a = some result) : result.type = .i32 := by
  cases t <;> cases a <;> simp_all [evalEqz, Value.type] <;> subst result <;> rfl

/-- A well-typed arithmetic redex can reduce to a value of its declared result type. -/
theorem binop_progress (ht : t.IsInteger) (ha : a.type = t) (hb : b.type = t) :
    ∃ result, Reduces [.instr (.const a), .instr (.const b), .instr (.binop t op)]
      (values [result]) ∧ result.type = t := by
  obtain ⟨result, h⟩ := evalBinOp_total (op := op) ht ha hb
  exact ⟨result, .binop h, evalBinOp_type h⟩

/-- Every arithmetic reduction preserves the declared result type. -/
theorem binop_preservation
    (h : Reduces [.instr (.const a), .instr (.const b), .instr (.binop t op)] code) :
    ∃ result, code = values [result] ∧ result.type = t := by
  cases h with
  | binop h => exact ⟨_, rfl, evalBinOp_type h⟩

theorem eqz_progress (ht : t.IsInteger) (ha : a.type = t) :
    ∃ result, Reduces [.instr (.const a), .instr (.eqz t)] (values [result]) ∧
      result.type = .i32 := by
  obtain ⟨result, h⟩ := evalEqz_total ht ha
  exact ⟨result, .eqz h, evalEqz_type h⟩

theorem eqz_preservation (h : Reduces [.instr (.const a), .instr (.eqz t)] code) :
    ∃ result, code = values [result] ∧ result.type = .i32 := by
  cases h with
  | eqz h => exact ⟨_, rfl, evalEqz_type h⟩

end Wasm.TypeSafety
