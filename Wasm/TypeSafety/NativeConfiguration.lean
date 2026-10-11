import Wasm.TypeSafety.NativeCalls
import Wasm.TypeSafety.NativeExecution

namespace Wasm.TypeSafety

private theorem GlobalStep.not_native (step : GlobalStep store state code storeNext next)
    (typed : NativeCoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    exact ih hb
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | _ =>
    have hp := typed.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead, ScalarInstruction] at hp

private theorem ExceptionStep.not_native (step : ExceptionStep store state code storeNext next)
    (typed : NativeCoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    exact ih hb
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | labelThrow =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    have hp := hb.heads
    simp [CoreHead] at hp
  | frameThrow =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    have hp := hb.heads
    simp [CoreHead] at hp
  | _ =>
    have hp := typed.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead, ScalarInstruction] at hp

private theorem VectorStep.not_native (step : VectorStep store state code storeNext next)
    (typed : NativeCoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    exact ih hb
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem StructStep.not_native (step : StructStep store state code storeNext next)
    (typed : NativeCoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    exact ih hb
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem ArrayStep.not_native (step : ArrayStep store state code storeNext next)
    (typed : NativeCoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    exact ih hb
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | _ =>
    have hp := typed.heads
    (repeat rw [List.forall_mem_append] at hp) <;> simp [CoreHead, ScalarInstruction] at hp

private theorem ReferenceStep.not_native (step : ReferenceStep store state code next)
    (typed : NativeCoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    exact ih hb
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem TableStep.not_native (step : TableStep store state code storeNext next)
    (typed : NativeCoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    exact ih hb
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem BulkStep.not_native (step : BulkStep store state code storeNext next)
    (typed : NativeCoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    exact ih hb
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | redex h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

private theorem MemoryStep.not_native (step : MemoryStep store state code storeNext next)
    (typed : NativeCoreTyping store context labels code input output) : False := by
  induction step generalizing context labels input output with
  | context _ ih =>
    obtain ⟨middle, left, _⟩ := typed.split
    obtain ⟨last, _, body⟩ := left.split
    exact ih body
  | label _ ih =>
    obtain ⟨_, _, _, hb, _⟩ := (NativeCoreTyping.single_iff.mp typed).label_body
    exact ih hb
  | frame _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := (NativeCoreTyping.single_iff.mp typed).frame_body
    exact ih hb
  | handler => exact False.elim (NativeCoreTyping.single_iff.mp typed).head
  | access _ _ _ h =>
    have hp := typed.heads
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [CoreHead, ScalarInstruction] at hp

theorem ConfigStep.preserves_native (step : ConfigStep config next)
    (typed : NativeCoreConfigurationTyped config output) :
    NativeCoreConfigurationTyped next output ∧ next.store = config.store := by
  obtain ⟨hs, context, hf, hr, hc⟩ := typed
  cases step with
  | pure h =>
    exact ⟨⟨hs, context, hf, hr, ExecStep.preserves_native h hc hf.1.1 (by simp)⟩, rfl⟩
  | locals h =>
    obtain ⟨hf, hc⟩ := LocalStep.preserves_native h hf hc (by simp)
    exact ⟨⟨hs, context, hf, hr, hc⟩, rfl⟩
  | call h =>
    exact ⟨⟨hs, context, hf, hr, CallStep.preserves_native h hs hf hc (by simp)⟩, rfl⟩
  | globals h => exact False.elim (GlobalStep.not_native h hc)
  | exceptions h => exact False.elim (ExceptionStep.not_native h hc)
  | vectors h => exact False.elim (VectorStep.not_native h hc)
  | structures h => exact False.elim (StructStep.not_native h hc)
  | arrays h => exact False.elim (ArrayStep.not_native h hc)
  | references h => exact False.elim (ReferenceStep.not_native h hc)
  | tables h => exact False.elim (TableStep.not_native h hc)
  | bulk h => exact False.elim (BulkStep.not_native h hc)
  | memory h => exact False.elim (MemoryStep.not_native h hc)

theorem ConfigSteps.preserves_native (steps : ConfigSteps config next)
    (typed : NativeCoreConfigurationTyped config output) :
    NativeCoreConfigurationTyped next output ∧ next.store = config.store := by
  induction steps with
  | refl => exact ⟨typed, rfl⟩
  | cons step _ ih =>
    obtain ⟨ht, hs⟩ := ConfigStep.preserves_native step typed
    obtain ⟨ht, hs'⟩ := ih ht
    exact ⟨ht, hs'.trans hs⟩

end Wasm.TypeSafety
