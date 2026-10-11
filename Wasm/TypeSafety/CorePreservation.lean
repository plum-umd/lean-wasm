import Wasm.TypeSafety.CoreTyping

namespace Wasm.TypeSafety

private theorem reduces_scalar (h : Reduces code next) : ScalarCode code ∧ ScalarCode next := by
  cases h <;> simp [ScalarCode, ScalarInstruction]

private theorem integers_scalar (h : IntegerReduces code next) :
    ScalarCode code ∧ ScalarCode next := by
  cases h with
  | binary =>
    rename_i result _
    cases result <;> simp [NumericResult.code, ScalarCode, values, ScalarInstruction]
  | _ => simp [ScalarCode, values, ScalarInstruction]

theorem Reduces.preserves_core (step : Reduces code next)
    (typed : CoreTyping store context labels code input output) :
    CoreTyping store context labels next input output := by
  obtain ⟨before, after⟩ := reduces_scalar step
  exact (Reduces.preserves_flat step (typed.toFlatTyping before)).toCoreTyping after

theorem IntegerReduces.preserves_core (step : IntegerReduces code next)
    (typed : CoreTyping store context labels code input output) :
    CoreTyping store context labels next input output := by
  obtain ⟨before, after⟩ := integers_scalar step
  exact (IntegerReduces.preserves_flat step (typed.toFlatTyping before)).toCoreTyping after

private theorem value_results (typed : CoreTyping store context labels (values vs) [] output) :
    vs.map Value.type = output := by
  have h := CoreTyping.after_values (tail := []) (by simpa using typed)
  simpa using h

/-- Preservation of every structured-control redex, including branch and return unwinding. -/
theorem ControlReduces.preserves_core (step : ControlReduces context.types code next)
    (typed : CoreTyping store context labels code input output) :
    CoreTyping store context labels next input output := by
  cases step with
  | @block ft args bt body ht ha =>
    have hop := (CoreTyping.single_iff.mp typed.after_values).block_shape
    obtain ⟨actual, below, hactual, hi, ho, hb⟩ := hop
    have he : actual = ft := Option.some.inj (hactual.symm.trans ht)
    subst actual
    have hl := congrArg List.length hi
    simp only [List.length_append, List.length_map] at hl
    obtain ⟨hbelow, hargs⟩ := List.append_inj hi (by omega)
    have hn := typed.values_number
    rw [ho, ← hbelow]
    apply CoreTyping.single_iff.mpr
    have bodyTyped : CoreTyping store context (ft.results :: labels)
        (values args ++ instructions body) [] ft.results := by
      have hv := CoreTyping.values_typed (store := store) (context := context)
        (labels := ft.results :: labels) (input := []) hn
      simp only [List.nil_append, hargs] at hv
      exact hv.append hb
    simpa using CoreInstrTyping.weaken (stackBelow := input)
      (.label (continuation := []) bodyTyped .nil)
  | @loop ft args bt body ht ha =>
    have hop := (CoreTyping.single_iff.mp typed.after_values).loop_shape
    obtain ⟨actual, below, hactual, hi, ho, hb⟩ := hop
    have he : actual = ft := Option.some.inj (hactual.symm.trans ht)
    subst actual
    have hl := congrArg List.length hi
    simp only [List.length_append, List.length_map] at hl
    obtain ⟨hbelow, hargs⟩ := List.append_inj hi (by omega)
    have hn := typed.values_number
    rw [ho, ← hbelow]
    apply CoreTyping.single_iff.mpr
    have bodyTyped : CoreTyping store context (ft.params :: labels)
        (values args ++ instructions body) [] ft.results := by
      have hv := CoreTyping.values_typed (store := store) (context := context)
        (labels := ft.params :: labels) (input := []) hn
      simp only [List.nil_append, hargs] at hv
      exact hv.append hb
    have continuation : CoreTyping store context labels
        (instructions [.loop bt body]) ft.params ft.results := .cons (.loop ht hb) .nil
    simpa using CoreInstrTyping.weaken (stackBelow := input) (.label bodyTyped continuation)
  | ifZero =>
    simp only [CoreTyping.const_cons_iff, CoreTyping.single_iff] at typed
    obtain ⟨_, h⟩ := typed
    obtain ⟨ft, below, ht, hi, ho, _, hn⟩ := h.if_shape
    have hi : input = below ++ ft.params := by
      apply List.append_cancel_right (bs := [ValType.i32])
      simpa [Value.type, ← List.append_assoc] using hi
    rw [hi, ho]
    exact CoreTyping.single_iff.mpr (.weaken (.block ht hn))
  | ifNonzero _ =>
    simp only [CoreTyping.const_cons_iff, CoreTyping.single_iff] at typed
    obtain ⟨_, h⟩ := typed
    obtain ⟨ft, below, ht, hi, ho, hy, _⟩ := h.if_shape
    have hi : input = below ++ ft.params := by
      apply List.append_cancel_right (bs := [ValType.i32])
      simpa [Value.type, ← List.append_assoc] using hi
    rw [hi, ho]
    exact CoreTyping.single_iff.mpr (.weaken (.block ht hy))
  | brIfZero =>
    simp only [CoreTyping.const_cons_iff, CoreTyping.single_iff] at typed
    obtain ⟨_, h⟩ := typed
    obtain ⟨ts, below, _, hi, ho⟩ := h.brIf_shape
    have hi : input = below ++ ts := by
      apply List.append_cancel_right (bs := [ValType.i32])
      simpa [Value.type, ← List.append_assoc] using hi
    rw [hi, ho]; exact .nil
  | brIfNonzero _ =>
    simp only [CoreTyping.const_cons_iff, CoreTyping.single_iff] at typed
    obtain ⟨_, h⟩ := typed
    obtain ⟨ts, below, ht, hi, ho⟩ := h.brIf_shape
    have hi : input = below ++ ts := by
      apply List.append_cancel_right (bs := [ValType.i32])
      simpa [Value.type, ← List.append_assoc] using hi
    rw [hi]
    exact CoreTyping.single_iff.mpr (.br ht)
  | brTableHit hit =>
    simp only [CoreTyping.const_cons_iff, CoreTyping.single_iff] at typed
    obtain ⟨_, h⟩ := typed
    obtain ⟨ts, below, _, targets, hi⟩ := h.brTable_shape
    have hi : input = below ++ ts := by
      apply List.append_cancel_right (bs := [ValType.i32])
      simpa [Value.type] using hi
    have ht := targets _ (List.mem_of_getElem? hit)
    rw [hi]; exact CoreTyping.single_iff.mpr (.br ht)
  | brTableDefault _ =>
    simp only [CoreTyping.const_cons_iff, CoreTyping.single_iff] at typed
    obtain ⟨_, h⟩ := typed
    obtain ⟨ts, below, ht, _, hi⟩ := h.brTable_shape
    have hi : input = below ++ ts := by
      apply List.append_cancel_right (bs := [ValType.i32])
      simpa [Value.type] using hi
    rw [hi]; exact CoreTyping.single_iff.mpr (.br ht)
  | labelDone =>
    obtain ⟨branch, results, _, ho, hb, _⟩ :=
      (CoreTyping.single_iff.mp typed).label_shape
    have hv := value_results hb
    rw [ho, ← hv]
    exact CoreTyping.values_typed
      (CoreTyping.values_number (tail := []) (by simpa using hb))
  | labelTrap => exact .cons .trap .nil
  | returnLabel =>
    obtain ⟨branch, results, _, ho, hb, _⟩ :=
      (CoreTyping.single_iff.mp typed).label_shape
    simp only [List.append_assoc] at hb
    have hn := hb.values_number
    cases hb.after_values with
    | cons head tail =>
      obtain ⟨returns, below, hr, hi⟩ := head.return_shape
      simp only [List.nil_append] at hi
      refine (CoreTyping.values_typed (input := input) hn).append ?_
      apply CoreTyping.single_iff.mpr
      have hreturn : CoreInstrTyping store context labels (.instr .return_)
          ((input ++ below) ++ returns) output := .return_ hr
      simpa [hi, List.append_assoc] using hreturn
  | brSucc =>
    obtain ⟨branch, results, _, ho, hb, _⟩ :=
      (CoreTyping.single_iff.mp typed).label_shape
    simp only [List.append_assoc] at hb
    have hn := hb.values_number
    cases hb.after_values with
    | cons head tail =>
      obtain ⟨ts, below, ht, hi⟩ := head.br_shape
      simp only [List.nil_append] at hi
      simp only [List.getElem?_cons_succ] at ht
      refine (CoreTyping.values_typed (input := input) hn).append ?_
      apply CoreTyping.single_iff.mpr
      have hbr : CoreInstrTyping store context labels (.instr (.br _))
          ((input ++ below) ++ ts) output := .br ht
      simpa [hi, List.append_assoc] using hbr
  | @brZero n continuation discarded results tail hn =>
    obtain ⟨branch, outputTypes, harity, ho, hb, hc⟩ :=
      (CoreTyping.single_iff.mp typed).label_shape
    simp only [List.append_assoc] at hb
    have hvalues := hb.after_values.after_values
    cases hvalues with
    | cons head tailTyped =>
      obtain ⟨ts, below, ht, hi⟩ := head.br_shape
      simp only [List.nil_append] at hi
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
      subst ts
      have hl := congrArg List.length hi
      simp only [List.length_append, List.length_map] at hl
      have hlen : (discarded.map Value.type).length = below.length := by
        simp only [List.length_map]; omega
      obtain ⟨_, hresults⟩ := List.append_inj (by simpa using hi) hlen
      have hnum := (hb.after_values).values_number
      rw [ho]
      have hv := CoreTyping.values_typed (store := store) (context := context)
        (labels := labels) (input := input) hnum
      have hcontinuation := hc.weaken (stackBelow := input)
      rw [← hresults] at hcontinuation
      exact hv.append hcontinuation

/-- Completing an activation preserves result types, including explicit return. -/
theorem FrameReduces.preserves_core (step : FrameReduces code next)
    (typed : CoreTyping store context labels code input output) :
    CoreTyping store context labels next input output := by
  cases step with
  | done _ =>
    obtain ⟨innerContext, results, _, ho, _, _, hb⟩ :=
      (CoreTyping.single_iff.mp typed).frame_shape
    have hv := value_results hb
    rw [ho, ← hv]
    exact CoreTyping.values_typed
      (CoreTyping.values_number (tail := []) (by simpa using hb))
  | trap => exact .cons .trap .nil
  | @return_ n state discarded results tail hn =>
    obtain ⟨innerContext, outputTypes, harity, ho, _, hr, hb⟩ :=
      (CoreTyping.single_iff.mp typed).frame_shape
    simp only [List.append_assoc] at hb
    cases hb.after_values.after_values with
    | cons head tailTyped =>
      obtain ⟨returnTypes, below, ht, hi⟩ := head.return_shape
      have he : returnTypes = outputTypes := Option.some.inj (ht.symm.trans hr)
      subst returnTypes
      simp only [List.nil_append] at hi
      have hl := congrArg List.length hi
      simp only [List.length_append, List.length_map] at hl
      have hlen : (discarded.map Value.type).length = below.length := by
        simp only [List.length_map]; omega
      obtain ⟨_, hresults⟩ := List.append_inj hi hlen
      rw [ho, ← hresults]
      exact CoreTyping.values_typed hb.after_values.values_number

end Wasm.TypeSafety
