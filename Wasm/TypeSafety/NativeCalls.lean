import Wasm.TypeSafety.NativeLocals
import Wasm.TypeSafety.NativeStore

namespace Wasm.TypeSafety

theorem CallStep.preserves_native (step : CallStep store state code next)
    (storeTyped : NativeCoreStoreTyped store) (frameTyped : CoreFrameTyped store state context)
    (typed : NativeCoreTyping store context labels code input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    NativeCoreTyping store context labels next input output := by
  induction step generalizing context labels input output with
  | call addressLookup functionLookup =>
    obtain ⟨ft, ht, effect⟩ := (NativeCoreTyping.single_iff.mp typed).source_effect.call_effect
    obtain ⟨address, function, ha, hf, htype⟩ := frameTyped.1.2.2 _ _ ht
    have he := Option.some.inj (addressLookup.symm.trans ha)
    subst address
    have he := Option.some.inj (functionLookup.symm.trans hf)
    subst function
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    rw [hi, ← htype]
    apply NativeCoreTyping.single_iff.mpr
    apply NativeCoreInstrTyping.output_matches (.weaken (.invoke hf))
    simpa [htype] using ho
  | invoke functionLookup signature invocation =>
    obtain ⟨hn, hop⟩ := typed.after_values number
    obtain ⟨function, hf, ht, effect⟩ := (NativeCoreTyping.single_iff.mp hop).invoke_effect
    have he := Option.some.inj (functionLookup.symm.trans hf)
    subst function
    have hfunction := storeTyped _ _ hf
    have hargs := ArgsTyped.integer_types (Invokes.args_typed invocation)
      hfunction.params_integer
    obtain ⟨lower, hi, ho⟩ := effect.numeric
      (native_numbers_append number (native_value_numbers hn))
    rw [hargs] at hi
    have hbelow := List.append_cancel_right hi
    apply NativeCoreTyping.single_iff.mpr
    have activationTyped := (Invokes.native_core_typed
      (callerContext := context) (labels := labels) hfunction invocation).weaken
      (stackBelow := input)
    apply NativeCoreInstrTyping.output_matches (by simpa using activationTyped)
    simpa [← hbelow] using ho
  | context _ ih =>
    obtain ⟨hn, body⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using typed) number
    obtain ⟨middle, redex, tail⟩ := body.split
    have redex := ih frameTyped redex
      (native_numbers_append number (native_value_numbers hn))
    simpa only [List.append_assoc] using
      (NativeCoreTyping.values_typed hn).append (redex.append tail)
  | label _ ih =>
    obtain ⟨branch, results, hn, hb, hc, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).label_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    have hb := ih frameTyped hb (by simp)
    apply NativeCoreTyping.single_iff.mpr
    rw [hn, hi]
    simpa using (NativeCoreInstrTyping.weaken (.label hb hc)).output_matches ho
  | frame _ ih =>
    obtain ⟨inner, results, hn, hf, hr, hb, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).frame_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    have hb := ih hf hb (by simp)
    apply NativeCoreTyping.single_iff.mpr
    rw [hn, hi]
    simpa using (NativeCoreInstrTyping.weaken (.frame hf hr hb)).output_matches ho
  | handler | tailHandler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | tailLabel =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    have hp := hb.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead] at hp
  | tailFrame =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    have hp := hb.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead] at hp
  | _ =>
    have hp := typed.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead, ScalarInstruction] at hp

end Wasm.TypeSafety
