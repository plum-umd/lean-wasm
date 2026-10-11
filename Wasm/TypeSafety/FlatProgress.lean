import Wasm.TypeSafety.FlatPreservation

namespace Wasm.TypeSafety

/-- Integer operations and parametric instructions; constants are opaque values. -/
def ScalarInstruction : Instr → Prop
  | .const _ => True
  | .nop | .unreachable | .drop | .select _ | .binop _ _ | .eqz _ | .intUnary _ _
    | .intBinary _ _ | .intRel _ _ | .intConvert _ => True
  | _ => False

def ScalarCode (code : List AdminInstr) : Prop :=
  ∀ i ∈ code, match i with
    | .instr source => ScalarInstruction source
    | .trap => True
    | _ => False

def FlatTerminal (code : List AdminInstr) : Prop :=
  (∃ vs, code = values vs) ∨ code = [.trap]

private theorem map_one (h : vs.map Value.type = [t]) :
    ∃ v, vs = [v] ∧ v.type = t := by
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at h
  obtain ⟨v, rest, rfl, ht, rfl⟩ := h
  exact ⟨v, rfl, ht⟩

private theorem map_two (h : vs.map Value.type = [t, u]) :
    ∃ a b, vs = [a, b] ∧ a.type = t ∧ b.type = u := by
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at h
  obtain ⟨a, tail, rfl, ha, b, rest, rfl, hb, rfl⟩ := h
  exact ⟨a, b, rfl, ha, hb⟩

private theorem map_three (h : vs.map Value.type = [t, u, w]) :
    ∃ a b c, vs = [a, b, c] ∧ a.type = t ∧ b.type = u ∧ c.type = w := by
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at h
  obtain ⟨a, tail, rfl, ha, b, rest, rfl, hb, c, last, rfl, hc, rfl⟩ := h
  exact ⟨a, b, c, rfl, ha, hb, hc⟩

/-- Progress uses typing and canonical operand forms, never executable-stepper success. -/
theorem scalar_instruction_progress (typed : InstrTyping i input output)
    (supported : ScalarInstruction i) (notConstant : ∀ v, i ≠ .const v)
    (operands : vs.map Value.type = input) :
    ∃ next, ExecStep types (values vs ++ [.instr i]) next := by
  induction typed generalizing vs with
  | const => exact False.elim (notConstant _ rfl)
  | nop =>
    exact ⟨values vs, by
      simpa using ExecStep.context (vs := vs) (tail := []) (.primitive .nop)⟩
  | unreachable =>
    exact ⟨values vs ++ [.trap], by
      simpa using ExecStep.context (vs := vs) (tail := []) (.primitive .unreachable)⟩
  | drop =>
    obtain ⟨v, rfl, _⟩ := map_one operands
    exact ⟨[], .primitive .drop⟩
  | select | selectTyped =>
    obtain ⟨a, b, c, rfl, _, _, hc⟩ := map_three operands
    cases c <;> simp only [Value.type] at hc <;> try contradiction
    rename_i bits
    by_cases hz : bits = 0
    · subst bits; exact ⟨values [b], .primitive .selectZero⟩
    · exact ⟨values [a], .primitive (.selectNonzero hz)⟩
  | binop ht =>
    obtain ⟨a, b, rfl, ha, hb⟩ := map_two operands
    obtain ⟨result, he⟩ := evalBinOp_total ht ha hb
    exact ⟨values [result], .primitive (.binop he)⟩
  | eqz ht =>
    obtain ⟨a, rfl, ha⟩ := map_one operands
    obtain ⟨result, he⟩ := evalEqz_total ht ha
    exact ⟨values [result], .primitive (.eqz he)⟩
  | intUnary ht =>
    obtain ⟨a, rfl, ha⟩ := map_one operands
    obtain ⟨result, he⟩ := evalUnary_total ht ha
    exact ⟨values [result], .integer (.unary he)⟩
  | intBinary ht =>
    obtain ⟨a, b, rfl, ha, hb⟩ := map_two operands
    obtain ⟨result, he⟩ := evalBinary_total ht ha hb
    exact ⟨result.code, .integer (.binary he)⟩
  | intRel ht =>
    obtain ⟨a, b, rfl, ha, hb⟩ := map_two operands
    obtain ⟨result, he⟩ := evalRel_total ht ha hb
    exact ⟨values [result], .integer (.rel he)⟩
  | intConvert =>
    obtain ⟨a, rfl, ha⟩ := map_one operands
    obtain ⟨result, he⟩ := evalConversion_total ha
    exact ⟨values [result], .integer (.conversion he)⟩
  | floatUnary | floatBinary | floatRel | floatConvert => exact False.elim supported
  | weaken _ ih =>
    obtain ⟨stack, args, rfl, _, hargs⟩ := List.map_eq_append_iff.mp operands
    obtain ⟨next, step⟩ := ih supported notConstant hargs
    exact ⟨values stack ++ next, by
      simpa [values, List.map_append, List.append_assoc] using
        ExecStep.context (vs := stack) (tail := []) step⟩

theorem FlatTyping.progress_with_values (typed : FlatTyping code (vs.map Value.type) output)
    (supported : ScalarCode code) :
    FlatTerminal (values vs ++ code) ∨ ∃ next, ExecStep types (values vs ++ code) next := by
  induction code generalizing vs with
  | nil => exact .inl (.inl ⟨vs, by simp⟩)
  | cons i rest ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | trap =>
        by_cases terminal : values vs ++ [.trap] ++ rest = [.trap]
        · exact .inl (.inr (by simpa using terminal))
        · exact .inr ⟨[.trap], by simpa using ExecStep.trap terminal⟩
      | @source sourceInstr _ _ hi =>
        have hs : ScalarInstruction sourceInstr := supported (.instr sourceInstr) (by simp)
        have hr : ScalarCode rest := fun i hm => supported i (by simp [hm])
        by_cases constant : ∃ v, sourceInstr = .const v
        · obtain ⟨v, he⟩ := constant
          subst sourceInstr
          obtain ⟨shape, _⟩ := const_shape hi
          have ht : FlatTyping rest ((vs ++ [v]).map Value.type) output := by
            simpa [List.map_append, ← shape] using tail
          simpa [values, List.map_append, List.append_assoc] using ih ht hr
        · have hn : ∀ v, sourceInstr ≠ Instr.const v := by
            intro v he; exact constant ⟨v, he⟩
          obtain ⟨next, step⟩ := scalar_instruction_progress hi hs hn rfl
          exact .inr ⟨next ++ rest, by
            simpa using ExecStep.context (vs := []) (tail := rest) step⟩

theorem FlatTyping.progress (typed : FlatTyping code [] output) (supported : ScalarCode code) :
    FlatTerminal code ∨ ∃ next, ExecStep types code next := by
  simpa [values] using FlatTyping.progress_with_values (vs := []) typed supported

end Wasm.TypeSafety
