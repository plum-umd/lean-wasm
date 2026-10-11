import Wasm.TypeSafety.Arithmetic
import Wasm.IntegerReduction

namespace Wasm.TypeSafety

/-- Undefined integer arithmetic has a typed trap result, rather than a missing step. -/
def NumericResultTyped (result : NumericResult) (type : ValType) : Prop :=
  match result with
  | .value value => value.type = type
  | .trap => True

theorem evalUnary_total (ht : t.IsInteger) (ha : a.type = t) :
    ∃ result, evalUnary t op a = some result := by
  cases t <;> cases a <;> simp_all [ValType.IsInteger, Value.type, evalUnary]

theorem evalBinary_total (ht : t.IsInteger) (ha : a.type = t) (hb : b.type = t) :
    ∃ result, evalBinary t op a b = some result := by
  cases t <;> cases a <;> cases b <;>
    simp_all [ValType.IsInteger, Value.type, evalBinary]

theorem evalRel_total (ht : t.IsInteger) (ha : a.type = t) (hb : b.type = t) :
    ∃ result, evalRel t op a b = some result := by
  cases t <;> cases a <;> cases b <;>
    simp_all [ValType.IsInteger, Value.type, evalRel]

theorem evalConversion_total (ha : a.type = op.inputType) :
    ∃ result, evalConversion op a = some result := by
  cases op <;> cases a <;>
    simp_all [IntConversion.inputType, Value.type, evalConversion]

theorem evalBinary_type (h : evalBinary t op a b = some result) :
    NumericResultTyped result t := by
  cases t <;> cases a <;> cases b <;> simp only [evalBinary] at h <;> try contradiction
  all_goals
    rename_i x y
    cases he : evalIntBinary op x y <;> simp only [he] at h <;> cases h <;> trivial

theorem unary_progress (ht : t.IsInteger) (ha : a.type = t) :
    ∃ result, IntegerReduces [.instr (.const a), .instr (.intUnary t op)]
      (values [result]) ∧ result.type = t := by
  obtain ⟨result, h⟩ := evalUnary_total (op := op) ht ha
  exact ⟨result, .unary h, Wasm.evalUnary_type h⟩

theorem binary_progress (ht : t.IsInteger) (ha : a.type = t) (hb : b.type = t) :
    ∃ result : NumericResult, IntegerReduces [.instr (.const a), .instr (.const b),
      .instr (.intBinary t op)] result.code ∧ NumericResultTyped result t := by
  obtain ⟨result, h⟩ := evalBinary_total (op := op) ht ha hb
  exact ⟨result, .binary h, evalBinary_type h⟩

theorem rel_progress (ht : t.IsInteger) (ha : a.type = t) (hb : b.type = t) :
    ∃ result, IntegerReduces [.instr (.const a), .instr (.const b),
      .instr (.intRel t op)] (values [result]) ∧ result.type = .i32 := by
  obtain ⟨result, h⟩ := evalRel_total (op := op) ht ha hb
  exact ⟨result, .rel h, Wasm.evalRel_type h⟩

theorem conversion_progress (ha : a.type = op.inputType) :
    ∃ result, IntegerReduces [.instr (.const a), .instr (.intConvert op)]
      (values [result]) ∧ result.type = op.outputType := by
  obtain ⟨result, h⟩ := evalConversion_total ha
  exact ⟨result, .conversion h, Wasm.evalConversion_type h⟩

theorem unary_preservation
    (h : IntegerReduces [.instr (.const a), .instr (.intUnary t op)] code) :
    ∃ result, code = values [result] ∧ result.type = t := by
  cases h with
  | unary h => exact ⟨_, rfl, Wasm.evalUnary_type h⟩

theorem binary_preservation
    (h : IntegerReduces [.instr (.const a), .instr (.const b),
      .instr (.intBinary t op)] code) :
    ∃ result : NumericResult, code = result.code ∧ NumericResultTyped result t := by
  cases h with
  | binary h => exact ⟨_, rfl, evalBinary_type h⟩

theorem rel_preservation
    (h : IntegerReduces [.instr (.const a), .instr (.const b), .instr (.intRel t op)] code) :
    ∃ result, code = values [result] ∧ result.type = .i32 := by
  cases h with
  | rel h => exact ⟨_, rfl, Wasm.evalRel_type h⟩

theorem conversion_preservation
    (h : IntegerReduces [.instr (.const a), .instr (.intConvert op)] code) :
    ∃ result, code = values [result] ∧ result.type = op.outputType := by
  cases h with
  | conversion h => exact ⟨_, rfl, Wasm.evalConversion_type h⟩

end Wasm.TypeSafety
