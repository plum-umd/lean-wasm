import Wasm.TypeSafety.CoreCalls

namespace Wasm.TypeSafety

private theorem GlobalStep.not_core (step : GlobalStep store state code storeNext next)
    (typed : CoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    exact ih hb
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | _ =>
    have hp := typed.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead, ScalarInstruction] at hp

private theorem ExceptionStep.not_core (step : ExceptionStep store state code storeNext next)
    (typed : CoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    exact ih hb
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | labelThrow =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    have hp := hb.heads
    simp [CoreHead] at hp
  | frameThrow =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    have hp := hb.heads
    simp [CoreHead] at hp
  | _ =>
    have hp := typed.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead, ScalarInstruction] at hp

private theorem VectorStep.not_core (step : VectorStep store state code storeNext next)
    (typed : CoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    exact ih hb
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem StructStep.not_core (step : StructStep store state code storeNext next)
    (typed : CoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    exact ih hb
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem ArrayStep.not_core (step : ArrayStep store state code storeNext next)
    (typed : CoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    exact ih hb
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | _ =>
    have hp := typed.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead, ScalarInstruction] at hp

private theorem ReferenceStep.not_core (step : ReferenceStep store state code next)
    (typed : CoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    exact ih hb
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem TableStep.not_core (step : TableStep store state code storeNext next)
    (typed : CoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    exact ih hb
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem BulkStep.not_core (step : BulkStep store state code storeNext next)
    (typed : CoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    exact ih hb
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem MemoryStep.not_core (step : MemoryStep store state code storeNext next)
    (typed : CoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, _, hb, _⟩ := (CoreTyping.single_iff.mp typed).label_shape
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, _, hb⟩ := (CoreTyping.single_iff.mp typed).frame_shape
    exact ih hb
  | handler => exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | access _ _ _ h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

/-- Integer-core configurations carry independent store, frame, and expression invariants. -/
def CoreConfigurationTyped (config : Configuration) (output : List ValType) : Prop :=
  CoreStoreTyped config.store ∧ ∃ context,
    CoreFrameTyped config.store config.frame context ∧ context.returns = none ∧
    CoreTyping config.store context [] config.code [] output

/-- Every rule in the full configuration relation preserves the integer-core invariant. -/
theorem ConfigStep.preserves_core (step : ConfigStep config next)
    (typed : CoreConfigurationTyped config output) :
    CoreConfigurationTyped next output ∧ next.store = config.store := by
  obtain ⟨hs, context, hf, hr, hc⟩ := typed
  cases step with
  | pure h =>
    exact ⟨⟨hs, context, hf, hr, ExecStep.preserves_core h hc hf.1.1⟩, rfl⟩
  | locals h =>
    obtain ⟨hf, hc⟩ := LocalStep.preserves_core h hf hc
    exact ⟨⟨hs, context, hf, hr, hc⟩, rfl⟩
  | call h =>
    exact ⟨⟨hs, context, hf, hr, CallStep.preserves_core h hs hf hc⟩, rfl⟩
  | globals h => exact False.elim (GlobalStep.not_core h hc)
  | exceptions h => exact False.elim (ExceptionStep.not_core h hc)
  | vectors h => exact False.elim (VectorStep.not_core h hc)
  | structures h => exact False.elim (StructStep.not_core h hc)
  | arrays h => exact False.elim (ArrayStep.not_core h hc)
  | references h => exact False.elim (ReferenceStep.not_core h hc)
  | tables h => exact False.elim (TableStep.not_core h hc)
  | bulk h => exact False.elim (BulkStep.not_core h hc)
  | memory h => exact False.elim (MemoryStep.not_core h hc)

theorem ConfigSteps.preserves_core (steps : ConfigSteps config next)
    (typed : CoreConfigurationTyped config output) :
    CoreConfigurationTyped next output ∧ next.store = config.store := by
  induction steps with
  | refl => exact ⟨typed, rfl⟩
  | cons step _ ih =>
    obtain ⟨ht, hs⟩ := ConfigStep.preserves_core step typed
    obtain ⟨ht, hs'⟩ := ih ht
    exact ⟨ht, hs'.trans hs⟩

end Wasm.TypeSafety
