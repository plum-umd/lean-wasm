import Wasm.TypeSafety.NativeControl
import Wasm.TypeSafety.NativeLocals
import Wasm.TypeSafety.NativePreservation

namespace Wasm.TypeSafety

theorem native_numbers_unembed {input : List Wasm.Types.ValType}
    (number : ∀ t ∈ input, NativeNumber t) :
    ∃ ts : List ValType, input = ts.map Wasm.Types.embedVal ∧ ∀ t ∈ ts, t.IsNumber := by
  induction input with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons t rest ih =>
    obtain ⟨ts, hr, hn⟩ := ih (fun t ht => number t (by simp [ht]))
    have ht := number t (by simp)
    cases t with
    | i32 =>
      exact ⟨.i32 :: ts, by simp [hr, Wasm.Types.embedVal],
        by simpa only [List.forall_mem_cons] using And.intro True.intro hn⟩
    | i64 =>
      exact ⟨.i64 :: ts, by simp [hr, Wasm.Types.embedVal],
        by simpa only [List.forall_mem_cons] using And.intro True.intro hn⟩
    | f32 =>
      exact ⟨.f32 :: ts, by simp [hr, Wasm.Types.embedVal],
        by simpa only [List.forall_mem_cons] using And.intro True.intro hn⟩
    | f64 =>
      exact ⟨.f64 :: ts, by simp [hr, Wasm.Types.embedVal],
        by simpa only [List.forall_mem_cons] using And.intro True.intro hn⟩
    | v128 =>
      exact ⟨.v128 :: ts, by simp [hr, Wasm.Types.embedVal],
        by simpa only [List.forall_mem_cons] using And.intro True.intro hn⟩
    | ref | bot => exact False.elim ht

theorem ExecStep.preserves_native (step : ExecStep types code next)
    (typed : NativeCoreTyping store context labels code input output)
    (typeContext : context.types = types) (number : ∀ t ∈ input, NativeNumber t) :
    NativeCoreTyping store context labels next input output := by
  induction step generalizing context labels input output with
  | primitive h =>
    obtain ⟨ts, hi, hn⟩ := native_numbers_unembed number
    subst input
    exact Reduces.preserves_native_scalar h typed hn
  | integer h =>
    obtain ⟨ts, hi, hn⟩ := native_numbers_unembed number
    subst input
    exact IntegerReduces.preserves_native_scalar h typed hn
  | activation h => exact FrameReduces.preserves_native h typed number
  | control h =>
    rw [← typeContext] at h
    exact ControlReduces.preserves_native h typed number
  | context _ ih =>
    obtain ⟨hn, body⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using typed) number
    obtain ⟨middle, redex, tail⟩ := body.split
    have redex := ih redex typeContext
      (native_numbers_append number (native_value_numbers hn))
    simpa only [List.append_assoc] using
      (NativeCoreTyping.values_typed hn).append (redex.append tail)
  | label _ ih =>
    obtain ⟨branch, results, hn, hb, hc, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).label_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    have hb := ih hb typeContext (by simp)
    apply NativeCoreTyping.single_iff.mpr
    rw [hn, hi]
    simpa using (NativeCoreInstrTyping.weaken (.label hb hc)).output_matches ho
  | frame _ ih =>
    obtain ⟨inner, results, hn, hf, hr, hb, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).frame_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    have hb := ih hb hf.1.1 (by simp)
    apply NativeCoreTyping.single_iff.mpr
    rw [hn, hi]
    simpa using (NativeCoreInstrTyping.weaken (.frame hf hr hb)).output_matches ho
  | localFrame h =>
    obtain ⟨inner, results, hn, hf, hr, hb, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).frame_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    obtain ⟨hf, hb⟩ := LocalStep.preserves_native h hf hb (by simp)
    apply NativeCoreTyping.single_iff.mpr
    rw [hn, hi]
    simpa using (NativeCoreInstrTyping.weaken (.frame hf hr hb)).output_matches ho
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | trap _ => exact .cons .trap .nil

theorem ExecSteps.preserves_native (steps : ExecSteps types code next)
    (typed : NativeCoreTyping store context labels code input output)
    (typeContext : context.types = types) (number : ∀ t ∈ input, NativeNumber t) :
    NativeCoreTyping store context labels next input output := by
  induction steps with
  | refl => exact typed
  | cons step _ ih => exact ih (ExecStep.preserves_native step typed typeContext number)

end Wasm.TypeSafety
