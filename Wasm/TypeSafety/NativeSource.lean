import Wasm.TypeSafety.NativeTyping

namespace Wasm.TypeSafety

/-- Both function-body typing paths retain their stack matching evidence. -/
theorem RuntimeSeqTyping.toNativeCoreTyping
    (typed : RuntimeSeqTyping context labels code input output)
    (supported : ∀ i ∈ code, CoreSource i) :
    NativeCoreTyping store context labels (instructions code)
      (input.map Types.embedVal) (output.map Types.embedVal) := by
  revert supported
  apply RuntimeSeqTyping.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun labels code input output _ => (∀ i ∈ code, CoreSource i) →
      NativeCoreTyping store context labels (instructions code)
        (input.map Types.embedVal) (output.map Types.embedVal))
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun labels code input output _ => (∀ i ∈ code, CoreSource i) →
      NativeCoreTyping store context labels (instructions code) input output)
    (t := typed)
  all_goals try (intros; trivial)
  · intro labels code input output h hs
    exact (FunctionSeqTyping.toCoreTyping h hs).toNativeCoreTyping
  · intro labels ts hs; exact .nil
  · intro labels i input middle rest output head tail ihhead ihtail hs
    exact .cons (.source (.legacy head) (hs i (by simp)))
      (ihtail (fun i hi => hs i (by simp [hi])))
  · intro labels code input output below h ih hs
    simpa only [List.map_append] using (ih hs).weaken
  · intro labels code input output input' output' h hin hout ih hs
    exact .subtype (ih hs) hin hout
  · intro labels ts hs; exact .nil
  · intro labels i input middle rest output head tail ihhead ihtail hs
    exact .cons (.source head (hs i (by simp)))
      (ihtail (fun i hi => hs i (by simp [hi])))
  · intro labels code input output below h ih hs; exact (ih hs).weaken
  · intro labels code input output input' output' h hin hout ih hs
    exact .subtype (ih hs) hin hout

/-- The bottom-aware path embeds without projecting or choosing a value type for bottom. -/
theorem ValidationSeqTyping.toNativeCoreTyping
    (typed : ValidationSeqTyping context labels code input output)
    (supported : ∀ i ∈ code, CoreSource i) :
    NativeCoreTyping store context labels (instructions code) input output := by
  revert supported
  apply ValidationSeqTyping.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun labels code input output _ => (∀ i ∈ code, CoreSource i) →
      NativeCoreTyping store context labels (instructions code)
        (input.map Types.embedVal) (output.map Types.embedVal))
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun labels code input output _ => (∀ i ∈ code, CoreSource i) →
      NativeCoreTyping store context labels (instructions code) input output)
    (t := typed)
  all_goals try (intros; trivial)
  · intro labels code input output h hs
    exact (FunctionSeqTyping.toCoreTyping h hs).toNativeCoreTyping
  · intro labels ts hs; exact .nil
  · intro labels i input middle rest output head tail ihhead ihtail hs
    exact .cons (.source (.legacy head) (hs i (by simp)))
      (ihtail (fun i hi => hs i (by simp [hi])))
  · intro labels code input output below h ih hs
    simpa only [List.map_append] using (ih hs).weaken
  · intro labels code input output input' output' h hin hout ih hs
    exact .subtype (ih hs) hin hout
  · intro labels ts hs; exact .nil
  · intro labels i input middle rest output head tail ihhead ihtail hs
    exact .cons (.source head (hs i (by simp)))
      (ihtail (fun i hi => hs i (by simp [hi])))
  · intro labels code input output below h ih hs; exact (ih hs).weaken
  · intro labels code input output input' output' h hin hout ih hs
    exact .subtype (ih hs) hin hout

theorem RuntimeInstrTyping.toNativeCoreInstrTyping
    (typed : RuntimeInstrTyping context labels i input output) (supported : CoreSource i) :
    NativeCoreInstrTyping store context labels (.instr i)
      (input.map Types.embedVal) (output.map Types.embedVal) :=
  .source (.legacy typed) supported

theorem ValidationInstrTyping.toNativeCoreInstrTyping
    (typed : ValidationInstrTyping context labels i input output) (supported : CoreSource i) :
    NativeCoreInstrTyping store context labels (.instr i) input output :=
  .source typed supported

end Wasm.TypeSafety
