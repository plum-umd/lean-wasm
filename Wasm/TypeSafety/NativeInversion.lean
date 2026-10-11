import Wasm.TypeSafety.NativeValues

namespace Wasm.TypeSafety

theorem NativeSourceTyping.br_shape
    (typed : NativeSourceTyping store context labels (.br x) input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    ∃ ts below, labels[x]? = some ts ∧ input = below ++ ts.map Wasm.Types.embedVal := by
  generalize hi : Instr.br x = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨ts, below, ht, shape⟩ := h.br_shape
    exact ⟨ts, below.map Wasm.Types.embedVal, ht, by simp [shape]⟩
  | br ht => cases hi; exact ⟨_, _, ht, rfl⟩
  | @weaken i input output below _ ih =>
    obtain ⟨ts, lower, ht, shape⟩ := ih (fun t ht => number t (by simp [ht])) hi
    exact ⟨ts, below ++ lower, ht, by simp [shape, List.append_assoc]⟩
  | subtype _ hin hout ih =>
    have equal := native_results_match_numeric hin number
    rw [← equal] at number ⊢
    exact ih number hi
  | _ => cases hi

theorem NativeSourceTyping.return_shape
    (typed : NativeSourceTyping store context labels .return_ input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    ∃ results below, context.returns = some results ∧
      input = below ++ results.map Wasm.Types.embedVal := by
  generalize hi : Instr.return_ = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨results, below, ht, shape⟩ := h.return_shape
    exact ⟨results, below.map Wasm.Types.embedVal, ht, by simp [shape]⟩
  | return_ ht => cases hi; exact ⟨_, _, ht, rfl⟩
  | @weaken i input output below _ ih =>
    obtain ⟨results, lower, ht, shape⟩ := ih (fun t ht => number t (by simp [ht])) hi
    exact ⟨results, below ++ lower, ht, by simp [shape, List.append_assoc]⟩
  | subtype _ hin hout ih =>
    have equal := native_results_match_numeric hin number
    rw [← equal] at number ⊢
    exact ih number hi
  | _ => cases hi

theorem NativeCoreInstrTyping.br_shape
    (typed : NativeCoreInstrTyping store context labels (.instr (.br x)) input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    ∃ ts below, labels[x]? = some ts ∧ input = below ++ ts.map Wasm.Types.embedVal :=
  typed.source_effect.br_shape number

theorem NativeCoreInstrTyping.return_shape
    (typed : NativeCoreInstrTyping store context labels (.instr .return_) input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    ∃ results below, context.returns = some results ∧
      input = below ++ results.map Wasm.Types.embedVal :=
  typed.source_effect.return_shape number

theorem NativeCoreInstrTyping.label_body
    (typed : NativeCoreInstrTyping store context labels (.label n continuation body) input output) :
    ∃ (branch results : List ValType), n = branch.length ∧
      NativeCoreTyping store context (branch :: labels) body [] (results.map Wasm.Types.embedVal) ∧
      NativeCoreTyping store context labels (instructions continuation)
        (branch.map Wasm.Types.embedVal) (results.map Wasm.Types.embedVal) := by
  generalize hi : AdminInstr.label n continuation body = admin at typed
  induction typed using NativeCoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | label hb hc ihb ihc => cases hi; exact ⟨_, _, rfl, hb, hc⟩
  | weaken _ ih => exact ih hi
  | subtype _ hin hout ih => exact ih hi
  | _ => first | trivial | cases hi

theorem NativeCoreInstrTyping.frame_body
    (typed : NativeCoreInstrTyping store context labels (.frame n state body) input output) :
    ∃ (innerContext : FunctionContext) (results : List ValType),
      n = results.length ∧ CoreFrameTyped store state innerContext ∧
      innerContext.returns = some results ∧
      NativeCoreTyping store innerContext [] body [] (results.map Wasm.Types.embedVal) := by
  generalize hi : AdminInstr.frame n state body = admin at typed
  induction typed using NativeCoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | frame hf hr hb ih => cases hi; exact ⟨_, _, rfl, hf, hr, hb⟩
  | weaken _ ih => exact ih hi
  | subtype _ hin hout ih => exact ih hi
  | _ => first | trivial | cases hi

theorem NativeCoreInstrTyping.invoke_input
    (typed : NativeCoreInstrTyping store context labels (.invoke address type) input output) :
    ∃ function below, store.func? address = some function ∧ type = function.type ∧
      StackMatches ⟨context.definedTypes, []⟩ input
        (below ++ function.type.params.map Wasm.Types.embedVal) := by
  generalize hi : AdminInstr.invoke address type = admin at typed
  induction typed using NativeCoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | invoke hf => cases hi; exact ⟨_, [], hf, rfl, .refl⟩
  | @weaken context labels i input output below _ ih =>
    obtain ⟨function, lower, hf, ht, hm⟩ := ih hi
    exact ⟨function, below ++ lower, hf, ht, by
      simpa only [List.append_assoc] using hm.weaken (stackBelow := below)⟩
  | subtype _ hin hout ih =>
    obtain ⟨function, lower, hf, ht, hm⟩ := ih hi
    exact ⟨function, lower, hf, ht, .step hin hm⟩
  | _ => first | trivial | cases hi

theorem CoreSource.head (supported : CoreSource i) : CoreHead (.instr i) := by
  cases supported with
  | scalar hs => cases i <;> first | trivial | exact hs
  | _ => trivial

theorem NativeCoreInstrTyping.head
    (typed : NativeCoreInstrTyping store context labels i input output) : CoreHead i := by
  induction typed using NativeCoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | source h hs => exact hs.head
  | weaken _ ih => exact ih
  | subtype _ hin hout ih => exact ih
  | _ => trivial

end Wasm.TypeSafety
