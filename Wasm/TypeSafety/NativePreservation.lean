import Wasm.TypeSafety.NativeScalar

namespace Wasm.TypeSafety

def LiveScalarCode (code : List AdminInstr) : Prop :=
  ∀ admin ∈ code, ∃ i, admin = .instr i ∧ ScalarInstruction i ∧ i ≠ .unreachable

/-- Reachable scalar redexes recover the original arithmetic typing derivations. -/
theorem NativeCoreTyping.live_scalar {ts : List ValType}
    (typed : NativeCoreTyping store context labels code (ts.map Wasm.Types.embedVal) output)
    (supported : LiveScalarCode code) (number : ∀ t ∈ ts, t.IsNumber) :
    ∃ result, FlatTyping code ts result ∧ output = result.map Wasm.Types.embedVal := by
  induction code generalizing ts with
  | nil =>
    exact ⟨ts, .nil, StackMatches.numeric typed.empty_matches (native_numbers_map number)⟩
  | cons admin rest ih =>
    obtain ⟨i, rfl, hi, live⟩ := supported admin (by simp)
    obtain ⟨middle, head, tail⟩ := NativeCoreTyping.cons_iff.mp typed
    obtain ⟨next, ordinary, shape⟩ :=
      head.source_effect.scalar_effect hi live number rfl
    rw [shape] at tail
    obtain ⟨result, tailTyped, outputTypes⟩ := ih tail
      (fun admin ha => supported admin (by simp [ha]))
      (InstrTyping.scalar_numbers ordinary hi live number)
    exact ⟨result, .cons (.source ordinary) tailTyped, outputTypes⟩

private theorem Reduces.live_or_unreachable (step : Reduces code next) :
    code = [.instr .unreachable] ∨ LiveScalarCode code := by
  cases step <;> simp [LiveScalarCode, ScalarInstruction]

private theorem Reduces.result_scalar (step : Reduces code next) : ScalarCode next := by
  cases step <;> simp [ScalarCode, ScalarInstruction]

private theorem IntegerReduces.live (step : IntegerReduces code next) : LiveScalarCode code := by
  cases step <;> simp [LiveScalarCode, ScalarInstruction]

private theorem IntegerReduces.result_scalar (step : IntegerReduces code next) :
    ScalarCode next := by
  cases step with
  | binary =>
    rename_i result _
    cases result <;> simp [NumericResult.code, ScalarCode, values, ScalarInstruction]
  | _ => simp [ScalarCode, values, ScalarInstruction]

theorem Reduces.preserves_native_scalar {ts : List ValType} (step : Reduces code next)
    (typed : NativeCoreTyping store context labels code (ts.map Wasm.Types.embedVal) output)
    (number : ∀ t ∈ ts, t.IsNumber) :
    NativeCoreTyping store context labels next (ts.map Wasm.Types.embedVal) output := by
  rcases Reduces.live_or_unreachable step with unreachable | live
  · rw [unreachable] at step
    cases step
    exact .cons .trap .nil
  · obtain ⟨result, ordinary, shape⟩ := typed.live_scalar live number
    rw [shape]
    exact ((Reduces.preserves_flat step ordinary).toCoreTyping
      (Reduces.result_scalar step)).toNativeCoreTyping

theorem IntegerReduces.preserves_native_scalar {ts : List ValType}
    (step : IntegerReduces code next)
    (typed : NativeCoreTyping store context labels code (ts.map Wasm.Types.embedVal) output)
    (number : ∀ t ∈ ts, t.IsNumber) :
    NativeCoreTyping store context labels next (ts.map Wasm.Types.embedVal) output := by
  obtain ⟨result, ordinary, shape⟩ := typed.live_scalar (IntegerReduces.live step) number
  rw [shape]
  exact ((IntegerReduces.preserves_flat step ordinary).toCoreTyping
    (IntegerReduces.result_scalar step)).toNativeCoreTyping

private theorem ControlReduces.not_scalar (step : ControlReduces types code next) :
    ¬ ScalarCode code := by
  cases step <;> simp only [ScalarCode, List.forall_mem_append, List.forall_mem_singleton,
    List.forall_mem_cons, ScalarInstruction] <;> simp

private theorem FrameReduces.not_scalar (step : FrameReduces code next) : ¬ ScalarCode code := by
  cases step <;> simp [ScalarCode]

/-- All existing execution rules preserve native typing in the scalar fragment. -/
theorem ExecStep.preserves_native_scalar {ts : List ValType}
    (step : ExecStep types code next)
    (typed : NativeCoreTyping store context labels code (ts.map Wasm.Types.embedVal) output)
    (supported : ScalarCode code) (number : ∀ t ∈ ts, t.IsNumber) :
    NativeCoreTyping store context labels next (ts.map Wasm.Types.embedVal) output ∧
      ScalarCode next := by
  induction step generalizing ts output with
  | primitive h =>
    exact ⟨Reduces.preserves_native_scalar h typed number, Reduces.result_scalar h⟩
  | integer h =>
    exact ⟨IntegerReduces.preserves_native_scalar h typed number, IntegerReduces.result_scalar h⟩
  | activation h => exact False.elim (FrameReduces.not_scalar h supported)
  | control h => exact False.elim (ControlReduces.not_scalar h supported)
  | @context types code next vs tail step ih =>
    simp only [ScalarCode.append_iff] at supported
    obtain ⟨hn, inner⟩ := NativeCoreTyping.after_values (tail := code ++ tail)
      (by simpa only [List.append_assoc] using typed) (native_numbers_map number)
    obtain ⟨middle, redexTyped, tailTyped⟩ := inner.split
    have hnTypes : ∀ t ∈ ts ++ vs.map Value.type, t.IsNumber := by
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact number t ht
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
        exact hn v hv
    have redexTyped : NativeCoreTyping store context labels code
        ((ts ++ vs.map Value.type).map Wasm.Types.embedVal) middle := by
      simpa using redexTyped
    obtain ⟨newTyped, newScalar⟩ := ih redexTyped supported.1.2 hnTypes
    have newTyped : NativeCoreTyping store context labels next
        (ts.map Wasm.Types.embedVal ++ (vs.map Value.type).map Wasm.Types.embedVal) middle := by
      simpa using newTyped
    exact ⟨by simpa only [List.append_assoc] using
        (NativeCoreTyping.values_typed hn).append (newTyped.append tailTyped),
      by simp [supported.1.1, supported.2, newScalar]⟩
  | label | handler | frame | localFrame => simp [ScalarCode] at supported
  | trap _ => exact ⟨.cons .trap .nil, by simp [ScalarCode]⟩

end Wasm.TypeSafety
