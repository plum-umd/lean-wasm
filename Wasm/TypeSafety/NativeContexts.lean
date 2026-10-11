import Wasm.TypeSafety.NativeMatching

namespace Wasm.TypeSafety

/-- Explicit matching chains avoid assuming transitivity for unscoped reference types. -/
inductive StackMatches (context : Wasm.Types.Context) :
    List Wasm.Types.ValType → List Wasm.Types.ValType → Prop where
  | refl : StackMatches context ts ts
  | step : Wasm.Types.ResultMatches context input middle →
      StackMatches context middle output → StackMatches context input output

theorem native_matches_refl (context : Wasm.Types.Context) (ts : List Wasm.Types.ValType) :
    Wasm.Types.ResultMatches context ts ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih =>
    refine .cons ?_ ih
    cases t with
    | i32 => exact .i32
    | i64 => exact .i64
    | f32 => exact .f32
    | f64 => exact .f64
    | v128 => exact .v128
    | ref nullable heap => exact .ref (Wasm.Types.RefMatches.refl context ⟨nullable, heap⟩)
    | bot => exact .bot

theorem native_matches_append
    (left : Wasm.Types.ResultMatches context a b)
    (right : Wasm.Types.ResultMatches context c d) :
    Wasm.Types.ResultMatches context (a ++ c) (b ++ d) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

theorem StackMatches.trans (left : StackMatches context input middle)
    (right : StackMatches context middle output) : StackMatches context input output := by
  induction left with
  | refl => exact right
  | step head tail ih => exact .step head (ih right)

theorem StackMatches.weaken {stackBelow : List Wasm.Types.ValType}
    (h : StackMatches context input output) :
    StackMatches context (stackBelow ++ input) (stackBelow ++ output) := by
  induction h with
  | refl => exact .refl
  | step head tail ih =>
    exact .step (native_matches_append (native_matches_refl context stackBelow) head) ih

theorem NativeCoreTyping.empty_matches
    (typed : NativeCoreTyping store context labels [] input output) :
    StackMatches ⟨context.definedTypes, []⟩ input output := by
  generalize hc : ([] : List AdminInstr) = code at typed
  revert hc
  apply NativeCoreTyping.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun context labels code input output _ => [] = code →
      StackMatches ⟨context.definedTypes, []⟩ input output) (t := typed)
  all_goals try (intros; trivial)
  · intro context labels ts hc; exact .refl
  · intro context labels i input middle rest output head tail ihhead ihtail hc; cases hc
  · intro context labels code input output below h ih hc; exact (ih hc).weaken
  · intro context labels code input output input' output' h hin hout ih hc
    exact .step hin ((ih hc).trans (.step hout .refl))

theorem NativeCoreTyping.input_matches
    (typed : NativeCoreTyping store context labels code input output)
    (matching : StackMatches ⟨context.definedTypes, []⟩ input' input) :
    NativeCoreTyping store context labels code input' output := by
  induction matching with
  | refl => exact typed
  | step head tail ih => exact .subtype (ih typed) head (native_matches_refl _ _)

theorem NativeCoreInstrTyping.output_matches
    (typed : NativeCoreInstrTyping store context labels i input output)
    (matching : StackMatches ⟨context.definedTypes, []⟩ output output') :
    NativeCoreInstrTyping store context labels i input output' := by
  induction matching with
  | refl => exact typed
  | step head tail ih =>
    exact ih (.subtype typed (native_matches_refl _ _) head)

theorem NativeCoreTyping.output_matches
    (typed : NativeCoreTyping store context labels code input output)
    (matching : StackMatches ⟨context.definedTypes, []⟩ output output') :
    NativeCoreTyping store context labels code input output' := by
  induction matching with
  | refl => exact typed
  | step head tail ih => exact ih (.subtype typed (native_matches_refl _ _) head)

theorem NativeCoreInstrTyping.input_matches
    (typed : NativeCoreInstrTyping store context labels i input output)
    (matching : StackMatches ⟨context.definedTypes, []⟩ input' input) :
    NativeCoreInstrTyping store context labels i input' output := by
  induction matching with
  | refl => exact typed
  | step head tail ih => exact .subtype (ih typed) head (native_matches_refl _ _)

/-- Subtyping and weakening can be pushed into the head and tail of a nonempty sequence. -/
theorem NativeCoreTyping.cons_iff :
    NativeCoreTyping store context labels (i :: rest) input output ↔
      ∃ middle, NativeCoreInstrTyping store context labels i input middle ∧
        NativeCoreTyping store context labels rest middle output := by
  constructor
  · intro typed
    generalize hc : i :: rest = code at typed
    revert hc
    apply NativeCoreTyping.rec
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun context labels code input output _ => i :: rest = code →
        ∃ middle, NativeCoreInstrTyping store context labels i input middle ∧
          NativeCoreTyping store context labels rest middle output) (t := typed)
    all_goals try (intros; trivial)
    · intro context labels ts hc; cases hc
    · intro context labels i' input middle rest' output head tail ihhead ihtail hc
      cases hc; exact ⟨_, head, tail⟩
    · intro context labels code input output below h ih hc
      obtain ⟨middle, head, tail⟩ := ih hc
      exact ⟨_, .weaken head, .weaken tail⟩
    · intro context labels code input output input' output' h hin hout ih hc
      obtain ⟨middle, head, tail⟩ := ih hc
      exact ⟨middle, .subtype head hin (native_matches_refl _ _),
        .subtype tail (native_matches_refl _ _) hout⟩
  · rintro ⟨middle, head, tail⟩; exact .cons head tail

theorem NativeCoreTyping.single_iff :
    NativeCoreTyping store context labels [i] input output ↔
      NativeCoreInstrTyping store context labels i input output := by
  constructor
  · intro typed
    obtain ⟨middle, head, tail⟩ := NativeCoreTyping.cons_iff.mp typed
    exact head.output_matches tail.empty_matches
  · intro typed; exact .cons typed .nil

theorem NativeCoreTyping.append
    (left : NativeCoreTyping store context labels a input middle)
    (right : NativeCoreTyping store context labels b middle output) :
    NativeCoreTyping store context labels (a ++ b) input output := by
  induction a generalizing input with
  | nil => exact right.input_matches left.empty_matches
  | cons i a ih =>
    obtain ⟨inner, head, tail⟩ := NativeCoreTyping.cons_iff.mp left
    exact .cons head (ih tail)

theorem NativeCoreTyping.split
    (typed : NativeCoreTyping store context labels (a ++ b) input output) :
    ∃ middle, NativeCoreTyping store context labels a input middle ∧
      NativeCoreTyping store context labels b middle output := by
  induction a generalizing input with
  | nil => exact ⟨input, .nil, typed⟩
  | cons i a ih =>
    obtain ⟨inner, head, tail⟩ := NativeCoreTyping.cons_iff.mp typed
    obtain ⟨middle, left, right⟩ := ih tail
    exact ⟨middle, .cons head left, right⟩

end Wasm.TypeSafety
