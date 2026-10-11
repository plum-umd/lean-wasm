import Wasm.TypeSafety.FlatTyping

namespace Wasm.TypeSafety

private theorem select_output (h : InstrTyping (.select types)
    (stackBelow ++ [a, b, .i32]) output) :
    output = stackBelow ++ [a] ∧ output = stackBelow ++ [b] := by
  obtain ⟨other, t, hi, ho⟩ := select_shape h
  have hl := congrArg List.length hi
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  obtain ⟨hpre, hargs⟩ := List.append_inj hi (by omega)
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨ha, hb⟩ := hargs
  subst a; subst b
  exact ⟨hpre ▸ ho, hpre ▸ ho⟩

theorem Reduces.preserves_flat (step : Reduces code next)
    (typed : FlatTyping code input output) : FlatTyping next input output := by
  cases step with
  | nop =>
    have h := (fixed_output (stackBelow := input) (args := [])
      (by simpa using typed) (ft := ⟨[], []⟩) rfl rfl).2
    simp only [List.append_nil] at h
    exact h ▸ FlatTyping.nil
  | unreachable => exact FlatTyping.trapped
  | drop =>
    simp only [FlatTyping.const_cons_iff, FlatTyping.single_iff] at typed
    obtain ⟨_, hop⟩ := typed
    obtain ⟨t, hi⟩ := drop_shape hop
    have hl := congrArg List.length hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    have he := (List.append_inj hi (by omega)).1
    exact he ▸ FlatTyping.nil
  | selectZero =>
    simp only [FlatTyping.const_cons_iff, FlatTyping.single_iff] at typed
    obtain ⟨_, hnb, _, hop⟩ := typed
    have ho := (select_output (by simpa [Value.type, List.append_assoc] using hop)).2
    rw [ho]
    exact typed_value hnb
  | selectNonzero _ =>
    simp only [FlatTyping.const_cons_iff, FlatTyping.single_iff] at typed
    obtain ⟨hna, _, _, hop⟩ := typed
    have ho := (select_output (by simpa [Value.type, List.append_assoc] using hop)).1
    rw [ho]
    exact typed_value hna
  | @binop t op a b result he =>
    simp only [FlatTyping.const_cons_iff, FlatTyping.single_iff] at typed
    obtain ⟨hna, _, hop⟩ := typed
    obtain ⟨ha, ho⟩ := fixed_output (stackBelow := input) (args := [a.type, b.type])
      (ft := ⟨[t, t], [t]⟩)
      (by simpa [List.append_assoc] using hop) rfl rfl
    have ha : _ = _ := (List.cons.inj ha).1
    rw [ho, ← evalBinOp_type he]
    exact typed_value (by rw [evalBinOp_type he, ← ha]; exact hna)
  | eqz he =>
    simp only [FlatTyping.const_cons_iff, FlatTyping.single_iff] at typed
    obtain ⟨_, hop⟩ := typed
    have ho := (fixed_output (ft := ⟨[_], [.i32]⟩) hop rfl rfl).2
    rw [ho, ← evalEqz_type he]
    exact typed_value (by rw [evalEqz_type he]; trivial)

theorem IntegerReduces.preserves_flat (step : IntegerReduces code next)
    (typed : FlatTyping code input output) : FlatTyping next input output := by
  cases step with
  | unary he =>
    simp only [FlatTyping.const_cons_iff, FlatTyping.single_iff] at typed
    obtain ⟨hna, hop⟩ := typed
    obtain ⟨ha, ho⟩ := fixed_output (ft := ⟨[_], [_]⟩) hop rfl rfl
    have ha := List.singleton_inj.mp ha
    rw [ho, ← Wasm.evalUnary_type he]
    exact typed_value (by rw [Wasm.evalUnary_type he, ← ha]; exact hna)
  | @binary t op a b result he =>
    simp only [FlatTyping.const_cons_iff, FlatTyping.single_iff] at typed
    obtain ⟨hna, _, hop⟩ := typed
    obtain ⟨ha, ho⟩ := fixed_output (stackBelow := input) (args := [a.type, b.type])
      (ft := ⟨[t, t], [t]⟩)
      (by simpa [List.append_assoc] using hop) rfl rfl
    have ha := (List.cons.inj ha).1
    have hr := evalBinary_type he
    cases result with
    | trap => exact FlatTyping.trapped
    | value v =>
      change v.type = _ at hr
      rw [ho, ← hr]
      exact typed_value (by rw [hr, ← ha]; exact hna)
  | @rel t op a b result he =>
    simp only [FlatTyping.const_cons_iff, FlatTyping.single_iff] at typed
    obtain ⟨_, _, hop⟩ := typed
    have ho := (fixed_output (stackBelow := input) (args := [a.type, b.type])
      (ft := ⟨[t, t], [.i32]⟩)
      (by simpa [List.append_assoc] using hop) rfl rfl).2
    rw [ho, ← Wasm.evalRel_type he]
    exact typed_value (by rw [Wasm.evalRel_type he]; trivial)
  | @conversion op a result he =>
    simp only [FlatTyping.const_cons_iff, FlatTyping.single_iff] at typed
    obtain ⟨_, hop⟩ := typed
    have ho := (fixed_output (ft := ⟨[_], [_]⟩) hop rfl rfl).2
    rw [ho, ← Wasm.evalConversion_type he]
    exact typed_value (by rw [Wasm.evalConversion_type he]; cases op <;> trivial)

theorem Step.preserves_flat (step : Step code next) (typed : FlatTyping code input output) :
    FlatTyping next input output := by
  cases step with
  | context h =>
    obtain ⟨middle, left, right⟩ := typed.split
    obtain ⟨last, redex, tail⟩ := left.split
    exact (redex.append (Reduces.preserves_flat h tail)).append right
  | trap _ => exact FlatTyping.trapped

theorem Steps.preserves_flat (steps : Steps code next) (typed : FlatTyping code input output) :
    FlatTyping next input output := by
  induction steps with
  | refl => exact typed
  | cons step _ ih => exact ih (Step.preserves_flat step typed)

end Wasm.TypeSafety
