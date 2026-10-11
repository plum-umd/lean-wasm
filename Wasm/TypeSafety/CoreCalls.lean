import Wasm.TypeSafety.CoreStore

namespace Wasm.TypeSafety

/-- Direct calls preserve typing; the defining module determines the activation context. -/
theorem CallStep.preserves_core (step : CallStep store state code next)
    (storeTyped : CoreStoreTyped store) (frameTyped : CoreFrameTyped store state context)
    (typed : CoreTyping store context labels code input output) :
    CoreTyping store context labels next input output := by
  induction step generalizing context labels input output with
  | call addressLookup functionLookup =>
    obtain ⟨ft, below, ht, hi, ho⟩ := (CoreTyping.single_iff.mp typed).call_shape
    obtain ⟨address, function, ha, hf, htype⟩ := frameTyped.1.2.2 _ _ ht
    have he := Option.some.inj (addressLookup.symm.trans ha)
    subst address
    have he := Option.some.inj (functionLookup.symm.trans hf)
    subst function
    rw [hi, ho, ← htype]
    exact CoreTyping.single_iff.mpr (.weaken (.invoke hf))
  | invoke functionLookup signature invocation =>
    obtain ⟨function, below, hf, ht, hi, ho⟩ :=
      (CoreTyping.single_iff.mp typed.after_values).invoke_shape
    have he := Option.some.inj (functionLookup.symm.trans hf)
    subst function
    have hfunction := storeTyped _ _ hf
    have hargs := ArgsTyped.integer_types (Invokes.args_typed invocation)
      hfunction.params_integer
    rw [hargs] at hi
    have hbelow := List.append_cancel_right hi
    rw [ho, ← hbelow]
    apply CoreTyping.single_iff.mpr
    simpa using CoreInstrTyping.weaken (stackBelow := input)
      (Invokes.core_typed hfunction invocation)
  | context _ ih =>
    obtain ⟨middle, left, right⟩ := typed.split
    obtain ⟨last, valuesTyped, body⟩ := left.split
    exact (valuesTyped.append (ih frameTyped body)).append right
  | label _ ih =>
    obtain ⟨branch, results, hn, ho, hb, hc⟩ :=
      (CoreTyping.single_iff.mp typed).label_shape
    have hb := ih frameTyped hb
    rw [hn, ho]
    apply CoreTyping.single_iff.mpr
    simpa using CoreInstrTyping.weaken (stackBelow := input) (.label hb hc)
  | frame _ ih =>
    obtain ⟨innerContext, results, hn, ho, hf, hr, hb⟩ :=
      (CoreTyping.single_iff.mp typed).frame_shape
    have hb := ih hf hb
    rw [hn, ho]
    apply CoreTyping.single_iff.mpr
    simpa using CoreInstrTyping.weaken (stackBelow := input) (.frame hf hr hb)
  | handler | tailHandler =>
    exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | tailLabel =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    have hp := hb.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead] at hp
  | tailFrame =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    have hp := hb.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead] at hp
  | _ =>
    have hp := typed.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead, ScalarInstruction] at hp

end Wasm.TypeSafety
