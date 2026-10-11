import Wasm.TypeSafety.CoreLocals

namespace Wasm.TypeSafety

/-- Pure execution preserves administrative typing, even across activation contexts. -/
theorem ExecStep.preserves_core (step : ExecStep types code next)
    (typed : CoreTyping store context labels code input output)
    (typeContext : context.types = types) :
    CoreTyping store context labels next input output := by
  induction step generalizing context labels input output with
  | primitive h => exact Reduces.preserves_core h typed
  | integer h => exact IntegerReduces.preserves_core h typed
  | activation h => exact FrameReduces.preserves_core h typed
  | control h =>
    rw [← typeContext] at h
    exact ControlReduces.preserves_core h typed
  | context _ ih =>
    obtain ⟨middle, left, right⟩ := typed.split
    obtain ⟨last, valuesTyped, body⟩ := left.split
    exact (valuesTyped.append (ih body typeContext)).append right
  | label _ ih =>
    obtain ⟨branch, results, hn, ho, hb, hc⟩ :=
      (CoreTyping.single_iff.mp typed).label_shape
    have hb := ih hb typeContext
    rw [hn, ho]
    apply CoreTyping.single_iff.mpr
    simpa using CoreInstrTyping.weaken (stackBelow := input) (.label hb hc)
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | frame _ ih =>
    obtain ⟨innerContext, results, hn, ho, hf, hr, hb⟩ :=
      (CoreTyping.single_iff.mp typed).frame_shape
    have hb := ih hb hf.1.1
    rw [hn, ho]
    apply CoreTyping.single_iff.mpr
    simpa using CoreInstrTyping.weaken (stackBelow := input) (.frame hf hr hb)
  | localFrame h =>
    obtain ⟨innerContext, results, hn, ho, hf, hr, hb⟩ :=
      (CoreTyping.single_iff.mp typed).frame_shape
    obtain ⟨hf, hb⟩ := LocalStep.preserves_core h hf hb
    rw [hn, ho]
    apply CoreTyping.single_iff.mpr
    simpa using CoreInstrTyping.weaken (stackBelow := input) (.frame hf hr hb)
  | trap _ => exact .cons .trap .nil

theorem ExecSteps.preserves_core (steps : ExecSteps types code next)
    (typed : CoreTyping store context labels code input output)
    (typeContext : context.types = types) :
    CoreTyping store context labels next input output := by
  induction steps with
  | refl => exact typed
  | cons step _ ih => exact ih (ExecStep.preserves_core step typed typeContext)

end Wasm.TypeSafety
