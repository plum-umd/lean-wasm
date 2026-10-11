import Wasm.TypeSafety.NativeEffects

namespace Wasm.TypeSafety

theorem ControlReduces.preserves_native (step : ControlReduces context.types code next)
    (typed : NativeCoreTyping store context labels code input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    NativeCoreTyping store context labels next input output := by
  cases step with
  | @block ft args bt body ht ha =>
    obtain ⟨hn, hop⟩ := typed.after_values number
    obtain ⟨actual, hactual, hb, effect⟩ :=
      (NativeCoreTyping.single_iff.mp hop).source_effect.block_effect
    have he : actual = ft := Option.some.inj (hactual.symm.trans ht)
    subst actual
    obtain ⟨lower, hi, ho⟩ := effect.numeric
      (native_numbers_append number (native_value_numbers hn))
    have hl := congrArg List.length hi
    simp only [List.length_append, List.length_map] at hl
    obtain ⟨hbelow, hargs⟩ := List.append_inj hi (by omega)
    have hv := NativeCoreTyping.values_typed (store := store) (context := context)
      (labels := ft.results :: labels) (input := []) hn
    simp only [List.nil_append, hargs] at hv
    have bodyTyped := hv.append hb
    apply NativeCoreTyping.single_iff.mpr
    apply NativeCoreInstrTyping.output_matches
      (output := input ++ ft.results.map Wasm.Types.embedVal)
    · simpa using (NativeCoreInstrTyping.label (continuation := []) bodyTyped .nil).weaken
        (stackBelow := input)
    · simpa [← hbelow] using ho
  | @loop ft args bt body ht ha =>
    obtain ⟨hn, hop⟩ := typed.after_values number
    obtain ⟨actual, hactual, hb, effect⟩ :=
      (NativeCoreTyping.single_iff.mp hop).source_effect.loop_effect
    have he : actual = ft := Option.some.inj (hactual.symm.trans ht)
    subst actual
    obtain ⟨lower, hi, ho⟩ := effect.numeric
      (native_numbers_append number (native_value_numbers hn))
    have hl := congrArg List.length hi
    simp only [List.length_append, List.length_map] at hl
    obtain ⟨hbelow, hargs⟩ := List.append_inj hi (by omega)
    have hv := NativeCoreTyping.values_typed (store := store) (context := context)
      (labels := ft.params :: labels) (input := []) hn
    simp only [List.nil_append, hargs] at hv
    have continuation : NativeCoreTyping store context labels
        (instructions [.loop bt body]) (ft.params.map Wasm.Types.embedVal)
          (ft.results.map Wasm.Types.embedVal) := .cons (.loop ht hb) .nil
    apply NativeCoreTyping.single_iff.mpr
    apply NativeCoreInstrTyping.output_matches
      (output := input ++ ft.results.map Wasm.Types.embedVal)
    · simpa using (NativeCoreInstrTyping.label (hv.append hb) continuation).weaken
        (stackBelow := input)
    · simpa [← hbelow] using ho
  | ifZero =>
    obtain ⟨hn, hop⟩ := (NativeCoreTyping.const_cons_iff number).mp typed
    obtain ⟨ft, ht, hy, hn, effect⟩ :=
      (NativeCoreTyping.single_iff.mp hop).source_effect.if_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric
      (native_numbers_append number (by simp [NativeNumber, Value.type, Wasm.Types.embedVal]))
    have hi : input = lower ++ ft.params.map Wasm.Types.embedVal := by
      apply List.append_cancel_right (bs := [Wasm.Types.ValType.i32])
      simpa [Value.type, Wasm.Types.embedVal, List.append_assoc] using hi
    rw [hi]
    exact NativeCoreTyping.single_iff.mpr
      ((NativeCoreInstrTyping.weaken (.block ht hn)).output_matches ho)
  | ifNonzero _ =>
    obtain ⟨hn, hop⟩ := (NativeCoreTyping.const_cons_iff number).mp typed
    obtain ⟨ft, ht, hy, hn, effect⟩ :=
      (NativeCoreTyping.single_iff.mp hop).source_effect.if_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric
      (native_numbers_append number (by simp [NativeNumber, Value.type, Wasm.Types.embedVal]))
    have hi : input = lower ++ ft.params.map Wasm.Types.embedVal := by
      apply List.append_cancel_right (bs := [Wasm.Types.ValType.i32])
      simpa [Value.type, Wasm.Types.embedVal, List.append_assoc] using hi
    rw [hi]
    exact NativeCoreTyping.single_iff.mpr
      ((NativeCoreInstrTyping.weaken (.block ht hy)).output_matches ho)
  | brIfZero =>
    obtain ⟨hn, hop⟩ := (NativeCoreTyping.const_cons_iff number).mp typed
    obtain ⟨ts, ht, effect⟩ := (NativeCoreTyping.single_iff.mp hop).source_effect.brIf_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric
      (native_numbers_append number (by simp [NativeNumber, Value.type, Wasm.Types.embedVal]))
    have hi : input = lower ++ ts.map Wasm.Types.embedVal := by
      apply List.append_cancel_right (bs := [Wasm.Types.ValType.i32])
      simpa [Value.type, Wasm.Types.embedVal, List.append_assoc] using hi
    exact NativeCoreTyping.output_matches .nil (by simpa [← hi] using ho)
  | brIfNonzero _ =>
    obtain ⟨hn, hop⟩ := (NativeCoreTyping.const_cons_iff number).mp typed
    obtain ⟨ts, ht, effect⟩ := (NativeCoreTyping.single_iff.mp hop).source_effect.brIf_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric
      (native_numbers_append number (by simp [NativeNumber, Value.type, Wasm.Types.embedVal]))
    have hi : input = lower ++ ts.map Wasm.Types.embedVal := by
      apply List.append_cancel_right (bs := [Wasm.Types.ValType.i32])
      simpa [Value.type, Wasm.Types.embedVal, List.append_assoc] using hi
    rw [hi]
    exact NativeCoreTyping.single_iff.mpr (.source (.br ht) .br)
  | brTableHit hit =>
    obtain ⟨hn, hop⟩ := (NativeCoreTyping.const_cons_iff number).mp typed
    obtain ⟨ts, lower, ht, hi⟩ :=
      (NativeCoreTyping.single_iff.mp hop).source_effect.brTable_target
        (native_numbers_append number (by simp [NativeNumber, Value.type, Wasm.Types.embedVal]))
        (List.mem_cons_of_mem _ (List.mem_of_getElem? hit))
    have hi : input = lower ++ ts.map Wasm.Types.embedVal := by
      apply List.append_cancel_right (bs := [Wasm.Types.ValType.i32])
      simpa [Value.type, Wasm.Types.embedVal] using hi
    rw [hi]
    exact NativeCoreTyping.single_iff.mpr (.source (.br ht) .br)
  | @brTableDefault c targets fallback bound =>
    obtain ⟨hn, hop⟩ := (NativeCoreTyping.const_cons_iff number).mp typed
    obtain ⟨ts, lower, ht, hi⟩ :=
      (NativeCoreTyping.single_iff.mp hop).source_effect.brTable_target
        (native_numbers_append number (by simp [NativeNumber, Value.type, Wasm.Types.embedVal]))
        (x := fallback) (by simp)
    have hi : input = lower ++ ts.map Wasm.Types.embedVal := by
      apply List.append_cancel_right (bs := [Wasm.Types.ValType.i32])
      simpa [Value.type, Wasm.Types.embedVal] using hi
    rw [hi]
    exact NativeCoreTyping.single_iff.mpr (.source (.br ht) .br)
  | labelDone =>
    obtain ⟨branch, results, _, hb, hc, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).label_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    obtain ⟨hn, hv⟩ := hb.terminal_values
    apply (NativeCoreTyping.values_typed hn).output_matches
    simpa [← hi, hv] using ho
  | labelTrap => exact .cons .trap .nil
  | returnLabel =>
    obtain ⟨branch, results, _, hb, hc, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).label_effect
    obtain ⟨hn, body⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using hb) (by simp)
    obtain ⟨middle, head, tail⟩ := NativeCoreTyping.cons_iff.mp body
    obtain ⟨returns, lower, hr, hi⟩ := head.return_shape
      (by simpa using native_value_numbers hn)
    simp only [List.nil_append] at hi
    refine (NativeCoreTyping.values_typed hn).append (NativeCoreTyping.single_iff.mpr ?_)
    have result : NativeCoreInstrTyping store context labels (.instr .return_)
        ((input ++ lower) ++ returns.map Wasm.Types.embedVal) output :=
      .source (.return_ hr) .return_
    simpa [← hi, List.append_assoc] using result
  | brSucc =>
    obtain ⟨branch, results, _, hb, hc, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).label_effect
    obtain ⟨hn, body⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using hb) (by simp)
    obtain ⟨middle, head, tail⟩ := NativeCoreTyping.cons_iff.mp body
    obtain ⟨ts, lower, ht, hi⟩ := head.br_shape
      (by simpa using native_value_numbers hn)
    simp only [List.nil_append] at hi
    simp only [List.getElem?_cons_succ] at ht
    refine (NativeCoreTyping.values_typed hn).append (NativeCoreTyping.single_iff.mpr ?_)
    have result : NativeCoreInstrTyping store context labels (.instr (.br _))
        ((input ++ lower) ++ ts.map Wasm.Types.embedVal) output := .source (.br ht) .br
    simpa [← hi, List.append_assoc] using result
  | @brZero n continuation discarded results tail hn =>
    obtain ⟨branch, outputTypes, harity, hb, hc, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).label_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    obtain ⟨hd, body⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using hb) (by simp)
    obtain ⟨hr, body⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using body) (native_value_numbers hd)
    obtain ⟨middle, head, tailTyped⟩ := NativeCoreTyping.cons_iff.mp body
    obtain ⟨ts, below, ht, shape⟩ := head.br_shape
      (by simpa using native_numbers_append (native_value_numbers hd) (native_value_numbers hr))
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
    subst ts
    have hl := congrArg List.length shape
    simp only [List.length_append, List.length_map] at hl
    obtain ⟨_, hresults⟩ := List.append_inj shape (by simp only [List.length_map]; omega)
    have continuationTyped := hc.weaken (stackBelow := input)
    rw [← hresults] at continuationTyped
    apply ((NativeCoreTyping.values_typed hr).append continuationTyped).output_matches
    simpa [← hi] using ho

theorem FrameReduces.preserves_native (step : FrameReduces code next)
    (typed : NativeCoreTyping store context labels code input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    NativeCoreTyping store context labels next input output := by
  cases step with
  | done _ =>
    obtain ⟨inner, results, _, hf, hr, hb, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).frame_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    obtain ⟨hn, hv⟩ := hb.terminal_values
    apply (NativeCoreTyping.values_typed hn).output_matches
    simpa [← hi, hv] using ho
  | trap => exact .cons .trap .nil
  | @return_ n state discarded results tail hn =>
    obtain ⟨inner, outputTypes, harity, hf, hr, hb, effect⟩ :=
      (NativeCoreTyping.single_iff.mp typed).frame_effect
    obtain ⟨lower, hi, ho⟩ := effect.numeric number
    simp only [List.append_nil] at hi
    obtain ⟨hd, body⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using hb) (by simp)
    obtain ⟨hnum, body⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using body) (native_value_numbers hd)
    obtain ⟨middle, head, tailTyped⟩ := NativeCoreTyping.cons_iff.mp body
    obtain ⟨returnTypes, below, ht, shape⟩ := head.return_shape
      (by simpa using native_numbers_append (native_value_numbers hd) (native_value_numbers hnum))
    have he : returnTypes = outputTypes := Option.some.inj (ht.symm.trans hr)
    subst returnTypes
    have hl := congrArg List.length shape
    simp only [List.length_append, List.length_map] at hl
    obtain ⟨_, hresults⟩ := List.append_inj shape (by simp only [List.length_map]; omega)
    apply (NativeCoreTyping.values_typed hnum).output_matches
    simpa [← hi, ← hresults] using ho

end Wasm.TypeSafety
