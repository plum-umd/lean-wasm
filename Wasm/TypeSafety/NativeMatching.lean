import Wasm.TypeSafety.NativeTyping

namespace Wasm.TypeSafety

/-- A concrete numeric value cannot acquire bottom or a different type through matching. -/
theorem Types.ValMatches.numeric_left
    (matching : Wasm.Types.ValMatches context (Wasm.Types.embedVal t) actual)
    (number : t.IsNumber) : actual = Wasm.Types.embedVal t := by
  cases t <;> simp only [ValType.IsNumber] at number <;> try contradiction
  all_goals
    generalize ht : Wasm.Types.embedVal _ = a at matching
    cases matching <;> simp_all [Wasm.Types.embedVal, Wasm.Types.RefType.val]

/-- Matching into a numeric type admits exactly that type or the validator's bottom. -/
theorem Types.ValMatches.numeric_right
    (matching : Wasm.Types.ValMatches context actual (Wasm.Types.embedVal t))
    (number : t.IsNumber) : actual = .bot ∨ actual = Wasm.Types.embedVal t := by
  cases t <;> simp only [ValType.IsNumber] at number <;> try contradiction
  all_goals
    generalize ht : Wasm.Types.embedVal _ = b at matching
    cases matching <;> simp_all [Wasm.Types.embedVal, Wasm.Types.RefType.val]

theorem Types.ResultMatches.numeric_left {ts : List ValType}
    (matching : Wasm.Types.ResultMatches context (ts.map Wasm.Types.embedVal) actual)
    (number : ∀ t ∈ ts, t.IsNumber) : actual = ts.map Wasm.Types.embedVal := by
  induction ts generalizing actual with
  | nil => cases matching; rfl
  | cons t ts ih =>
    cases matching with
    | cons head tail =>
      rw [Types.ValMatches.numeric_left head (number t (by simp)),
        ih tail (fun t ht => number t (by simp [ht]))]
      rfl

/-- Numeric matching chains collapse without assumptions about reference-type scoping. -/
theorem Types.ResultMatches.numeric_chain {ts : List ValType}
    (first : Wasm.Types.ResultMatches context (ts.map Wasm.Types.embedVal) middle)
    (second : Wasm.Types.ResultMatches context middle output)
    (number : ∀ t ∈ ts, t.IsNumber) : output = ts.map Wasm.Types.embedVal := by
  have equal := Types.ResultMatches.numeric_left first number
  rw [equal] at second
  exact Types.ResultMatches.numeric_left second number

theorem numeric_value_not_bottom {v : Value} (number : v.type.IsNumber)
    (matching : Wasm.Types.ValMatches context (Wasm.Types.embedVal v.type) .bot) : False := by
  have equal := Types.ValMatches.numeric_left matching number
  cases v <;> simp_all [Value.type, ValType.IsNumber, Wasm.Types.embedVal]

end Wasm.TypeSafety
