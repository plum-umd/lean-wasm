import Wasm.TypeSafety.NativeSourceInversion

namespace Wasm.TypeSafety

def NativeNumber : Wasm.Types.ValType → Prop
  | .i32 | .i64 | .f32 | .f64 | .v128 => True
  | _ => False

@[simp] theorem NativeNumber.embed (t : ValType) :
    NativeNumber (Wasm.Types.embedVal t) ↔ t.IsNumber := by
  cases t <;> rfl

theorem native_value_matches_numeric
    (matching : Wasm.Types.ValMatches context input output) (number : NativeNumber input) :
    output = input := by
  cases matching <;> simp_all [NativeNumber, Wasm.Types.RefType.val]

theorem native_results_match_numeric
    (matching : Wasm.Types.ResultMatches context input output)
    (number : ∀ t ∈ input, NativeNumber t) : output = input := by
  induction matching with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.cons.injEq]
    exact ⟨native_value_matches_numeric head (number _ (by simp)),
      ih (fun t ht => number t (by simp [ht]))⟩

theorem StackMatches.numeric (matching : StackMatches context input output)
    (number : ∀ t ∈ input, NativeNumber t) : output = input := by
  induction matching with
  | refl => rfl
  | step head tail ih =>
    have equal := native_results_match_numeric head number
    subst_vars
    exact ih number

theorem NativeSourceTyping.const_shape
    (typed : NativeSourceTyping store context labels (.const v) input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    output = input ++ [Wasm.Types.embedVal v.type] ∧ v.type.IsNumber := by
  generalize hi : Instr.const v = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨shape, hn⟩ := h.const_shape
    exact ⟨by simp [shape], hn⟩
  | weaken _ ih =>
    obtain ⟨shape, hn⟩ := ih (fun t ht => number t (by simp [ht])) hi
    exact ⟨by simp [shape, List.append_assoc], hn⟩
  | @subtype i input output input' output' _ hin hout ih =>
    have equal := native_results_match_numeric hin number
    subst_vars
    obtain ⟨shape, hn⟩ := ih number rfl
    have outputNumber : ∀ t ∈ output, NativeNumber t := by
      rw [shape]
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact number t ht
      · have ht : t = Wasm.Types.embedVal v.type := by simpa using ht
        subst t
        exact (NativeNumber.embed _).mpr hn
    exact ⟨(native_results_match_numeric hout outputNumber).trans shape, hn⟩
  | _ => cases hi

theorem NativeCoreInstrTyping.const_shape
    (typed : NativeCoreInstrTyping store context labels (.instr (.const v)) input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    output = input ++ [Wasm.Types.embedVal v.type] ∧ v.type.IsNumber :=
  NativeSourceTyping.const_shape typed.source_effect number

theorem NativeCoreTyping.const_cons_iff (number : ∀ t ∈ input, NativeNumber t) :
    NativeCoreTyping store context labels (.instr (.const v) :: rest) input output ↔
      v.type.IsNumber ∧ NativeCoreTyping store context labels rest
        (input ++ [Wasm.Types.embedVal v.type]) output := by
  constructor
  · intro typed
    obtain ⟨middle, head, tail⟩ := NativeCoreTyping.cons_iff.mp typed
    obtain ⟨shape, hn⟩ := head.const_shape number
    exact ⟨hn, shape ▸ tail⟩
  · rintro ⟨hn, tail⟩
    have head : NativeCoreInstrTyping store context labels (.instr (.const v))
        [] [Wasm.Types.embedVal v.type] :=
      .source (.legacy (.plain (.plain (.plain (.const hn))))) (.scalar (by trivial))
    exact .cons (by simpa using head.weaken (stackBelow := input)) tail

/-- Peeling numeric constants recovers their concrete operand types despite source subtyping. -/
theorem NativeCoreTyping.after_values
    (typed : NativeCoreTyping store context labels (values vs ++ tail) input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    (∀ v ∈ vs, v.type.IsNumber) ∧ NativeCoreTyping store context labels tail
      (input ++ (vs.map Value.type).map Wasm.Types.embedVal) output := by
  induction vs generalizing input with
  | nil => exact ⟨by simp, by simpa [values] using typed⟩
  | cons v vs ih =>
    change NativeCoreTyping store context labels (.instr (.const v) :: (values vs ++ tail))
      input output at typed
    obtain ⟨hn, typed⟩ := (NativeCoreTyping.const_cons_iff number).mp typed
    have numbers : ∀ t ∈ input ++ [Wasm.Types.embedVal v.type], NativeNumber t := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact number t ht
      · have ht : t = Wasm.Types.embedVal v.type := by simpa using ht
        subst t
        exact (NativeNumber.embed _).mpr hn
    obtain ⟨hvs, tailTyped⟩ := ih typed numbers
    exact ⟨by simpa using And.intro hn hvs, by simpa [List.append_assoc] using tailTyped⟩

theorem NativeCoreTyping.terminal_values
    (typed : NativeCoreTyping store context labels (values vs) [] output) :
    (∀ v ∈ vs, v.type.IsNumber) ∧ output = (vs.map Value.type).map Wasm.Types.embedVal := by
  obtain ⟨hn, tail⟩ := NativeCoreTyping.after_values (tail := [])
    (by simpa using typed) (by simp)
  refine ⟨hn, StackMatches.numeric tail.empty_matches ?_⟩
  intro t ht
  obtain ⟨v, htype, rfl⟩ := List.mem_map.mp ht
  obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp htype
  exact (NativeNumber.embed _).mpr (hn value hvalue)

theorem native_numbers_map {ts : List ValType} (number : ∀ t ∈ ts, t.IsNumber) :
    ∀ t ∈ ts.map Wasm.Types.embedVal, NativeNumber t := by
  intro t ht
  obtain ⟨actual, ha, rfl⟩ := List.mem_map.mp ht
  exact (NativeNumber.embed _).mpr (number actual ha)

theorem NativeCoreTyping.values_typed (number : ∀ v ∈ vs, v.type.IsNumber) :
    NativeCoreTyping store context labels (values vs) input
      (input ++ (vs.map Value.type).map Wasm.Types.embedVal) := by
  induction vs generalizing input with
  | nil =>
    simpa [values] using (NativeCoreTyping.nil (store := store) (context := context)
      (labels := labels) (ts := input))
  | cons v vs ih =>
    have head : NativeCoreInstrTyping store context labels (.instr (.const v))
        [] [Wasm.Types.embedVal v.type] :=
      .source (.legacy (.plain (.plain (.plain (.const (number v (by simp)))))))
        (.scalar (by trivial))
    have tail := ih (input := input ++ [Wasm.Types.embedVal v.type])
      (fun v hv => number v (by simp [hv]))
    simpa [values, List.append_assoc] using
      NativeCoreTyping.cons (by simpa using head.weaken (stackBelow := input)) tail

end Wasm.TypeSafety
