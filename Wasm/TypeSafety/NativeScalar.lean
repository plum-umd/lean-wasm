import Wasm.TypeSafety.NativeValues

namespace Wasm.TypeSafety

theorem InstrTyping.scalar_numbers (typed : InstrTyping i input output)
    (supported : ScalarInstruction i) (live : i ≠ .unreachable)
    (number : ∀ t ∈ input, t.IsNumber) : ∀ t ∈ output, t.IsNumber := by
  induction typed with
  | const hn => simpa using hn
  | nop | drop => simp
  | unreachable => exact False.elim (live rfl)
  | select hn => simpa using hn
  | selectTyped =>
    rename_i t
    simpa using number t (by simp)
  | binop | intUnary | intBinary =>
    rename_i t op ht
    cases t <;> simp_all [ValType.IsInteger, ValType.IsNumber]
  | eqz | intRel => simp [ValType.IsNumber]
  | intConvert =>
    rename_i op
    cases op <;> simp [IntConversion.outputType, ValType.IsNumber]
  | floatUnary | floatBinary | floatRel | floatConvert => contradiction
  | @weaken i input output below h ih =>
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact number t (by simp [ht])
    · exact ih supported live (fun t ht => number t (by simp [ht])) t ht

/-- Live scalar effects have ordinary numeric stack types at both endpoints. -/
theorem NativeSourceTyping.scalar_effect {ts : List ValType}
    (typed : NativeSourceTyping store context labels i input output)
    (supported : ScalarInstruction i) (live : i ≠ .unreachable)
    (number : ∀ t ∈ ts, t.IsNumber) (inputTypes : input = ts.map Wasm.Types.embedVal) :
    ∃ result, InstrTyping i ts result ∧ output = result.map Wasm.Types.embedVal := by
  induction typed generalizing ts with
  | exact h =>
    have equal := (List.map_inj_right Wasm.Types.embedVal_injective).mp inputTypes
    subst ts
    exact ⟨_, h.of_scalar supported, rfl⟩
  | drop =>
    have shape := inputTypes.symm
    simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
    obtain ⟨t, rest, rfl, _, rfl⟩ := shape
    exact ⟨[], .drop, rfl⟩
  | select ht =>
    have shape := inputTypes.symm
    simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
    obtain ⟨a, rest, rfl, ha, b, rest, rfl, hb, c, rest, rfl, hc, rfl⟩ := shape
    have hab : a = b := Wasm.Types.embedVal_injective (ha.trans hb.symm)
    have hci : c = .i32 := Wasm.Types.embedVal_injective hc
    subst b; subst c
    exact ⟨[a], .select (number a (by simp)), by simpa using ha.symm⟩
  | unreachable => exact False.elim (live rfl)
  | weaken h ih =>
    obtain ⟨stack, args, he, hp, ha⟩ := List.map_eq_append_iff.mp inputTypes.symm
    subst ts
    obtain ⟨result, typed, shape⟩ := ih supported live
      (fun t ht => number t (by simp [ht])) ha.symm
    exact ⟨stack ++ result, .weaken typed, by simp [shape, ← hp]⟩
  | @subtype i input output input' output' h hin hout ih =>
    have numeric : ∀ t ∈ input', NativeNumber t := by
      rw [inputTypes]
      intro t ht
      obtain ⟨actual, ha, rfl⟩ := List.mem_map.mp ht
      exact (NativeNumber.embed _).mpr (number actual ha)
    have equal := native_results_match_numeric hin numeric
    obtain ⟨result, typed, shape⟩ := ih supported live number (equal.trans inputTypes)
    have hn := InstrTyping.scalar_numbers typed supported live number
    rw [shape] at hout
    exact ⟨result, typed, Types.ResultMatches.numeric_left hout hn⟩
  | _ => simp [ScalarInstruction] at supported

/-- Live numeric operands remove bottom polymorphism from a scalar instruction's input. -/
theorem NativeSourceTyping.scalar_input {ts : List ValType}
    (typed : NativeSourceTyping store context labels i input output)
    (supported : ScalarInstruction i) (live : i ≠ .unreachable)
    (number : ∀ t ∈ ts, t.IsNumber) (inputTypes : input = ts.map Wasm.Types.embedVal) :
    ∃ result, InstrTyping i ts result := by
  obtain ⟨result, ordinary, _⟩ := typed.scalar_effect supported live number inputTypes
  exact ⟨result, ordinary⟩

/-- Scalar progress for native administrative typing includes bottom-aware source derivations. -/
theorem NativeCoreInstrTyping.scalar_progress
    (typed : NativeCoreInstrTyping store context labels (.instr i)
      ((vs.map Value.type).map Wasm.Types.embedVal) output)
    (number : ∀ v ∈ vs, v.type.IsNumber) (supported : ScalarInstruction i)
    (notConstant : ∀ v, i ≠ .const v) :
    ∃ next, ExecStep types (values vs ++ [.instr i]) next := by
  by_cases unreachable : i = .unreachable
  · subst i
    exact ⟨values vs ++ [.trap], by
      simpa using ExecStep.context (vs := vs) (tail := []) (.primitive .unreachable)⟩
  · obtain ⟨result, oldTyped⟩ := NativeSourceTyping.scalar_input typed.source_effect supported
      unreachable (by simpa using number) rfl
    exact scalar_instruction_progress oldTyped supported notConstant rfl

end Wasm.TypeSafety
