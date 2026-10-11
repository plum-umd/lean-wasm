import Wasm.TypeSafety.NativeEffects

namespace Wasm.TypeSafety

theorem LocalStep.preserves_native (step : LocalStep frame code nextFrame next)
    (frameTyped : CoreFrameTyped store frame context)
    (typed : NativeCoreTyping store context labels code input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    CoreFrameTyped store nextFrame context ∧
      NativeCoreTyping store context labels next input output := by
  induction step generalizing context labels input output with
  | @get x value state lookup =>
    obtain ⟨t, ht, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).source_effect.localGet_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    obtain ⟨v, hv, he, hint⟩ := frameTyped.get ht
    have eqValue := Option.some.inj (lookup.symm.trans hv)
    cases eqValue
    refine ⟨frameTyped, ?_⟩
    have hn : ∀ w ∈ [value], w.type.IsNumber := by
      intro w hw; simp only [List.mem_singleton] at hw; subst w
      rw [he]; cases t <;> simp_all [ValType.IsInteger, ValType.IsNumber]
    have result := NativeCoreTyping.values_typed (store := store) (context := context)
      (labels := labels) (input := input) hn
    apply result.output_matches
    simpa [hi, he] using ho
  | set bound =>
    obtain ⟨hn, hop⟩ := (NativeCoreTyping.const_cons_iff number).mp typed
    obtain ⟨t, ht, effect⟩ := (NativeCoreTyping.single_iff.mp hop).source_effect.localSet_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric
      (native_numbers_append number (by simpa using (NativeNumber.embed _).mpr hn))
    have hl := congrArg List.length hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    obtain ⟨hbelow, he⟩ := List.append_inj hi (by omega)
    have he := Wasm.Types.embedVal_injective (List.singleton_inj.mp he)
    refine ⟨frameTyped.set ht he, ?_⟩
    apply NativeCoreTyping.output_matches .nil
    simpa [hbelow] using ho
  | tee =>
    obtain ⟨hn, hop⟩ := (NativeCoreTyping.const_cons_iff number).mp typed
    obtain ⟨t, ht, effect⟩ := (NativeCoreTyping.single_iff.mp hop).source_effect.localTee_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric
      (native_numbers_append number (by simpa using (NativeNumber.embed _).mpr hn))
    have hl := congrArg List.length hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    obtain ⟨hbelow, he⟩ := List.append_inj hi (by omega)
    have he := Wasm.Types.embedVal_injective (List.singleton_inj.mp he)
    refine ⟨frameTyped, ?_⟩
    apply NativeCoreTyping.output_matches (output := input ++ [Wasm.Types.embedVal t])
    · apply (NativeCoreTyping.const_cons_iff number).mpr
      refine ⟨hn, ?_⟩
      apply (NativeCoreTyping.const_cons_iff
        (native_numbers_append number (by simpa using (NativeNumber.embed _).mpr hn))).mpr
      refine ⟨hn, NativeCoreTyping.single_iff.mpr ?_⟩
      have hs := NativeSourceTyping.toNativeCoreInstrTyping
        (NativeSourceTyping.exact (CoreInstrTyping.localSet (store := store) (labels := labels) ht))
      simpa [he, List.append_assoc] using
        hs.weaken (stackBelow := input ++ [Wasm.Types.embedVal t])
    · simpa [hbelow] using ho
  | context _ ih =>
    obtain ⟨hn, body⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using typed) number
    obtain ⟨middle, redex, tail⟩ := body.split
    obtain ⟨hf, redex⟩ := ih frameTyped redex
      (native_numbers_append number (native_value_numbers hn))
    exact ⟨hf, by simpa only [List.append_assoc] using
      (NativeCoreTyping.values_typed hn).append (redex.append tail)⟩
  | label _ ih =>
    obtain ⟨branch, results, hn, hb, hc, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).label_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    obtain ⟨hf, hb⟩ := ih frameTyped hb (by simp)
    refine ⟨hf, NativeCoreTyping.single_iff.mpr ?_⟩
    rw [hn, hi]
    simpa using (NativeCoreInstrTyping.weaken (.label hb hc)).output_matches ho
  | frame _ ih =>
    obtain ⟨inner, results, hn, hf, hr, hb, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).frame_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    obtain ⟨hf, hb⟩ := ih hf hb (by simp)
    refine ⟨frameTyped, NativeCoreTyping.single_iff.mpr ?_⟩
    rw [hn, hi]
    simpa using (NativeCoreInstrTyping.weaken (.frame hf hr hb)).output_matches ho
  | handler =>
    have h := (NativeCoreTyping.single_iff.mp typed).head
    exact False.elim h

end Wasm.TypeSafety
