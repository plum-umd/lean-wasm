import Wasm.TypeSafety.NativePreservation
import Wasm.TypeSafety.NativeStore
import Wasm.TypeSafety.NativeInversion

namespace Wasm.TypeSafety

/-- Native scalar typing gives progress with an explicit concrete operand prefix. -/
theorem NativeCoreTyping.scalar_progress_with_values
    (typed : NativeCoreTyping store context labels code
      ((vs.map Value.type).map Wasm.Types.embedVal) output)
    (supported : ScalarCode code) (number : ∀ v ∈ vs, v.type.IsNumber) :
    FlatTerminal (values vs ++ code) ∨ ∃ next, ExecStep types (values vs ++ code) next := by
  induction code generalizing vs with
  | nil => exact .inl (.inl ⟨vs, by simp⟩)
  | cons admin rest ih =>
    obtain ⟨middle, head, tail⟩ := NativeCoreTyping.cons_iff.mp typed
    have hs := supported admin (by simp)
    have hr : ScalarCode rest := fun i hi => supported i (by simp [hi])
    cases admin with
    | instr i =>
      cases i with
      | const v =>
        obtain ⟨shape, hn⟩ := head.const_shape (native_numbers_map (by simpa using number))
        have tail : NativeCoreTyping store context labels rest
            (((vs ++ [v]).map Value.type).map Wasm.Types.embedVal) output := by
          simpa [shape] using tail
        have nextNumber : ∀ w ∈ vs ++ [v], w.type.IsNumber := by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact number w hw
          · have hw : w = v := by simpa using hw
            subst w; exact hn
        simpa [values, List.append_assoc] using ih tail hr nextNumber
      | _ =>
        obtain ⟨next, step⟩ := NativeCoreInstrTyping.scalar_progress head number hs
          (by intro v h; cases h)
        exact .inr ⟨next ++ rest, by
          simpa [List.append_assoc] using ExecStep.context (vs := []) (tail := rest) step⟩
    | trap =>
      by_cases terminal : values vs ++ [.trap] ++ rest = [.trap]
      · exact .inl (.inr (by simpa [List.append_assoc] using terminal))
      · exact .inr ⟨[.trap], by
          simpa [List.append_assoc] using ExecStep.trap (types := types) terminal⟩
    | _ => exact False.elim hs

theorem NativeCoreTyping.scalar_progress
    (typed : NativeCoreTyping store context labels code [] output) (supported : ScalarCode code) :
    FlatTerminal code ∨ ∃ next, ExecStep types code next := by
  simpa [values] using NativeCoreTyping.scalar_progress_with_values
    (vs := []) typed supported (by simp)

theorem CoreEscape.prepend_values (escape : CoreEscape code) :
    CoreEscape (values stack ++ code) := by
  cases escape with
  | branch =>
    simpa [values, List.append_assoc] using CoreEscape.branch (vs := stack ++ _) (x := _)
  | return_ =>
    simpa [values, List.append_assoc] using CoreEscape.return_ (vs := stack ++ _)

private theorem split_native_i32 {vs : List Value} {below : List Wasm.Types.ValType}
    (types : (vs.map Value.type).map Wasm.Types.embedVal = below ++ [.i32]) :
    ∃ stack bits, vs = stack ++ [.i32 bits] := by
  have mapped : vs.map (Wasm.Types.embedVal ∘ Value.type) = below ++ [.i32] := by
    simpa only [List.map_map] using types
  obtain ⟨stack, last, he, _, hl⟩ := List.map_eq_append_iff.mp mapped
  have hl : (last.map Value.type).map Wasm.Types.embedVal = [Wasm.Types.embedVal .i32] := by
    simpa only [List.map_map] using hl
  have lastType : last.map Value.type = [ValType.i32] :=
    (List.map_inj_right Wasm.Types.embedVal_injective).mp hl
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at lastType
  obtain ⟨v, rest, rfl, hv, rfl⟩ := lastType
  cases v <;> simp only [Value.type] at hv <;> try contradiction
  exact ⟨stack, _, he⟩

private theorem scalar_source_step
    (typed : NativeSourceTyping store context labels i input output)
    (number : ∀ v ∈ vs, v.type.IsNumber) (supported : ScalarInstruction i)
    (notConstant : ∀ v, i ≠ .const v)
    (inputTypes : input = (vs.map Value.type).map Wasm.Types.embedVal) :
    CoreCanStep store state (values vs ++ [.instr i]) := by
  have typed := typed.toNativeCoreInstrTyping
  rw [inputTypes] at typed
  obtain ⟨next, step⟩ := NativeCoreInstrTyping.scalar_progress typed number supported notConstant
  exact ⟨_, .pure step⟩

/-- All source instructions in the native core reduce or expose a branch/return escape. -/
theorem NativeSourceTyping.source_progress
    (typed : NativeSourceTyping store context labels i input output)
    (frameTyped : CoreFrameTyped store state context) (notConstant : ∀ v, i ≠ .const v)
    (number : ∀ v ∈ vs, v.type.IsNumber)
    (inputTypes : input = (vs.map Value.type).map Wasm.Types.embedVal) :
    CoreEscape (values vs ++ [.instr i]) ∨ CoreCanStep store state (values vs ++ [.instr i]) := by
  induction typed generalizing vs with
  | exact h =>
    have equal := (List.map_inj_right Wasm.Types.embedVal_injective).mp inputTypes
    rw [equal] at h
    exact CoreInstrTyping.source_progress h frameTyped notConstant
  | drop => exact .inr (scalar_source_step (context := context) (labels := labels)
      .drop number (by trivial) notConstant inputTypes)
  | select ht =>
    exact .inr (scalar_source_step (context := context) (labels := labels)
      (.select ht) number (by trivial) notConstant inputTypes)
  | unreachable => exact .inr (scalar_source_step (context := context) (labels := labels)
      (NativeSourceTyping.unreachable (output := []))
      number (by trivial) notConstant inputTypes)
  | br => exact .inl (by simpa using CoreEscape.branch (vs := vs) (tail := []))
  | return_ => exact .inl (by simpa using CoreEscape.return_ (vs := vs) (tail := []))
  | @brTable fallback targets arguments input output ht =>
    obtain ⟨stack, bits, he⟩ := split_native_i32 (vs := vs) (below := input ++ arguments)
      (by simpa only [List.append_assoc] using inputTypes.symm)
    subst vs
    right
    have step : CoreCanStep store state
        [.instr (.const (.i32 bits)), .instr (.brTable targets fallback)] := by
      cases hit : targets[bits.toNat]? with
      | some x => exact CoreCanStep.control frameTyped.1.1 (.brTableHit hit)
      | none =>
        exact CoreCanStep.control frameTyped.1.1
          (.brTableDefault (List.getElem?_eq_none_iff.mp hit))
    simpa [values, List.append_assoc] using CoreCanStep.context (vs := stack) (tail := []) step
  | @block ft body bt ht hb =>
    have arity : vs.length = ft.params.length := by
      have len := congrArg List.length inputTypes
      simpa using len.symm
    exact .inr (CoreCanStep.control frameTyped.1.1 (.block ht arity))
  | @loop ft body bt ht hb =>
    have arity : vs.length = ft.params.length := by
      have len := congrArg List.length inputTypes
      simpa using len.symm
    exact .inr (CoreCanStep.control frameTyped.1.1 (.loop ht arity))
  | @if_ ft yes no bt ht hy hn =>
    obtain ⟨stack, bits, he⟩ := split_native_i32 (by simpa using inputTypes.symm)
    subst vs
    right
    have step : CoreCanStep store state
        [.instr (.const (.i32 bits)), .instr (.if_ bt yes no)] := by
      by_cases hz : bits = 0
      · subst bits; exact CoreCanStep.control frameTyped.1.1 .ifZero
      · exact CoreCanStep.control frameTyped.1.1 (.ifNonzero hz)
    simpa [values, List.append_assoc] using CoreCanStep.context (vs := stack) (tail := []) step
  | @weaken i input output stackBelow h ih =>
    have mapped : vs.map (Wasm.Types.embedVal ∘ Value.type) = stackBelow ++ input := by
      simpa only [List.map_map] using inputTypes.symm
    obtain ⟨stack, args, he, _, ha⟩ := List.map_eq_append_iff.mp mapped
    subst vs
    have hn : ∀ v ∈ args, v.type.IsNumber := fun v hv => number v (by simp [hv])
    rcases ih notConstant hn (by simpa only [List.map_map] using ha.symm) with escape | step
    · exact .inl (by simpa [values, List.append_assoc] using escape.prepend_values (stack := stack))
    · exact .inr (by simpa [values, List.append_assoc] using
        CoreCanStep.context (vs := stack) (tail := []) step)
  | subtype h hin hout ih =>
    have equal := native_results_match_numeric hin
      (by rw [inputTypes]; exact native_numbers_map (by simpa using number))
    exact ih notConstant number (equal.trans inputTypes)

theorem NativeCoreInstrTyping.source_progress
    (typed : NativeCoreInstrTyping store context labels (.instr i)
      ((vs.map Value.type).map Wasm.Types.embedVal) output)
    (frameTyped : CoreFrameTyped store state context) (notConstant : ∀ v, i ≠ .const v)
    (number : ∀ v ∈ vs, v.type.IsNumber) :
    CoreEscape (values vs ++ [.instr i]) ∨ CoreCanStep store state (values vs ++ [.instr i]) :=
  NativeSourceTyping.source_progress typed.source_effect frameTyped notConstant number rfl

theorem NativeCoreInstrTyping.invoke_progress
    (typed : NativeCoreInstrTyping store context labels (.invoke address type)
      ((vs.map Value.type).map Wasm.Types.embedVal) output)
    (storeTyped : NativeCoreStoreTyped store) (number : ∀ v ∈ vs, v.type.IsNumber) :
    CoreCanStep store state (values vs ++ [.invoke address type]) := by
  obtain ⟨function, below, hf, ht, matching⟩ := typed.invoke_input
  have shape := (StackMatches.numeric matching (native_numbers_map (by simpa using number))).symm
  have mapped : vs.map (Wasm.Types.embedVal ∘ Value.type) =
      below ++ function.type.params.map Wasm.Types.embedVal := by
    simpa only [List.map_map] using shape
  obtain ⟨stack, args, he, _, ha⟩ := List.map_eq_append_iff.mp mapped
  have argTypes : args.map Value.type = function.type.params :=
    (List.map_inj_right Wasm.Types.embedVal_injective).mp (by
      simpa only [List.map_map] using ha)
  obtain ⟨activation, invoke⟩ := NativeCoreFunctionTyped.invokable (storeTyped _ _ hf) argTypes
  have step : CoreCanStep store state (values args ++ [.invoke address function.type]) :=
    ⟨_, .call (.invoke hf rfl invoke)⟩
  subst vs
  rw [ht]
  simpa [values, List.append_assoc] using CoreCanStep.context (vs := stack) (tail := []) step

theorem CoreEscape.native_label_step {branch : List ValType} (escape : CoreEscape body)
    (typed : NativeCoreTyping store context (branch :: labels) body [] output)
    (typeContext : context.types = state.module.types) :
    CoreCanStep store state [.label branch.length continuation body] := by
  cases escape with
  | return_ => exact CoreCanStep.control typeContext .returnLabel
  | @branch vs tail x =>
    cases x with
    | succ x => exact CoreCanStep.control typeContext .brSucc
    | zero =>
      obtain ⟨hn, tailTyped⟩ := NativeCoreTyping.after_values (tail := [.instr (.br 0)] ++ tail)
        (by simpa only [List.append_assoc] using typed) (by simp)
      obtain ⟨middle, head, _⟩ := NativeCoreTyping.cons_iff.mp tailTyped
      obtain ⟨ts, below, ht, hi⟩ := head.br_shape
        (native_numbers_map (by simpa using hn))
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
      subst ts
      have mapped : vs.map (Wasm.Types.embedVal ∘ Value.type) =
          below ++ branch.map Wasm.Types.embedVal := by
        simpa only [List.nil_append, List.map_map] using hi
      obtain ⟨discarded, returned, he, _, hr⟩ := List.map_eq_append_iff.mp mapped
      have hlen : returned.length = branch.length := by
        have := congrArg List.length hr
        simpa using this
      subst vs
      apply CoreCanStep.control typeContext
      simpa [values, List.append_assoc] using
        (ControlReduces.brZero (types := context.types) (continuation := continuation)
          (discarded := discarded) (tail := tail) hlen)

theorem CoreEscape.native_frame_step (escape : CoreEscape body)
    (typed : NativeCoreTyping store context [] body [] output)
    (returns : context.returns = some results) :
    CoreCanStep store outer [.frame results.length state body] := by
  cases escape with
  | branch =>
    obtain ⟨hn, tailTyped⟩ := NativeCoreTyping.after_values
      (by simpa only [List.append_assoc] using typed) (by simp)
    obtain ⟨middle, head, _⟩ := NativeCoreTyping.cons_iff.mp tailTyped
    obtain ⟨_, _, ht, _⟩ := head.br_shape (native_numbers_map (by simpa using hn))
    simp at ht
  | @return_ vs tail =>
    obtain ⟨hn, tailTyped⟩ := NativeCoreTyping.after_values (tail := [.instr .return_] ++ tail)
      (by simpa only [List.append_assoc] using typed) (by simp)
    obtain ⟨middle, head, _⟩ := NativeCoreTyping.cons_iff.mp tailTyped
    obtain ⟨returnTypes, below, ht, hi⟩ := head.return_shape
      (native_numbers_map (by simpa using hn))
    have he : returnTypes = results := Option.some.inj (ht.symm.trans returns)
    subst returnTypes
    have mapped : vs.map (Wasm.Types.embedVal ∘ Value.type) =
        below ++ results.map Wasm.Types.embedVal := by
      simpa only [List.nil_append, List.map_map] using hi
    obtain ⟨discarded, returned, he, _, hr⟩ := List.map_eq_append_iff.mp mapped
    have hlen : returned.length = results.length := by
      have := congrArg List.length hr
      simpa using this
    subst vs
    apply CoreCanStep.activation
    simpa [values, List.append_assoc] using
      (FrameReduces.return_ (state := state) (discarded := discarded) (tail := tail) hlen)

private theorem native_label_progress {branch : List ValType}
    (progress : FlatTerminal body ∨ CoreEscape body ∨ CoreCanStep store state body)
    (typed : NativeCoreTyping store context (branch :: labels) body [] output)
    (typeContext : context.types = state.module.types) :
    CoreCanStep store state [.label branch.length continuation body] := by
  rcases progress with terminal | escape | step
  · rcases terminal with ⟨vs, rfl⟩ | rfl
    · exact CoreCanStep.control typeContext .labelDone
    · exact CoreCanStep.control typeContext .labelTrap
  · exact escape.native_label_step typed typeContext
  · obtain ⟨⟨nextStore, nextState, next⟩, step⟩ := step
    exact ⟨_, ConfigStep.in_core_label step⟩

private theorem native_frame_progress
    (progress : FlatTerminal body ∨ CoreEscape body ∨ CoreCanStep store state body)
    (typed : NativeCoreTyping store context [] body [] (results.map Wasm.Types.embedVal))
    (returns : context.returns = some results) :
    CoreCanStep store outer [.frame results.length state body] := by
  rcases progress with terminal | escape | step
  · rcases terminal with ⟨vs, rfl⟩ | rfl
    · have hlen : vs.length = results.length := by
        have := congrArg List.length typed.terminal_values.2
        simpa using this.symm
      exact CoreCanStep.activation (.done hlen)
    · exact CoreCanStep.activation .trap
  · exact escape.native_frame_step typed returns
  · obtain ⟨⟨nextStore, nextState, next⟩, step⟩ := step
    exact ⟨_, ConfigStep.in_core_frame step⟩

/-- Progress for the whole native administrative core, including recursive activations. -/
theorem NativeCoreTyping.progress_with_values
    (typed : NativeCoreTyping store context labels code
      ((vs.map Value.type).map Wasm.Types.embedVal) output)
    (storeTyped : NativeCoreStoreTyped store) (frameTyped : CoreFrameTyped store state context)
    (number : ∀ v ∈ vs, v.type.IsNumber) :
    FlatTerminal (values vs ++ code) ∨ CoreEscape (values vs ++ code) ∨
      CoreCanStep store state (values vs ++ code) := by
  cases code with
  | nil => exact .inl (.inl ⟨vs, by simp⟩)
  | cons i rest =>
    obtain ⟨middle, head, tail⟩ := NativeCoreTyping.cons_iff.mp typed
    cases i with
    | instr source =>
      by_cases constant : ∃ v, source = .const v
      · obtain ⟨v, rfl⟩ := constant
        obtain ⟨shape, hn⟩ := head.const_shape (native_numbers_map (by simpa using number))
        have tail : NativeCoreTyping store context labels rest
            (((vs ++ [v]).map Value.type).map Wasm.Types.embedVal) output := by
          simpa [shape] using tail
        have nextNumber : ∀ w ∈ vs ++ [v], w.type.IsNumber := by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact number w hw
          · have hw : w = v := by simpa using hw
            subst w; exact hn
        simpa [values, List.append_assoc] using
          NativeCoreTyping.progress_with_values tail storeTyped frameTyped nextNumber
      · have hn : ∀ v, source ≠ Instr.const v := fun v h => constant ⟨v, h⟩
        rcases head.source_progress frameTyped hn number with escape | step
        · exact .inr (.inl (by simpa using escape.append (rest := rest)))
        · exact .inr (.inr (by simpa using CoreCanStep.context (vs := []) (tail := rest) step))
    | trap =>
      by_cases terminal : values vs ++ [.trap] ++ rest = [.trap]
      · exact .inl (.inr (by simpa using terminal))
      · exact .inr (.inr ⟨_, by simpa using ConfigStep.pure (ExecStep.trap terminal)⟩)
    | label n continuation body =>
      obtain ⟨branch, results, hn, hb, _⟩ := head.label_body
      have hp := NativeCoreTyping.progress_with_values (vs := []) hb storeTyped frameTyped (by simp)
      have step := native_label_progress (by simpa [values] using hp) hb frameTyped.1.1
        (continuation := continuation)
      rw [hn]
      exact .inr (.inr (by simpa using CoreCanStep.context (vs := vs) (tail := rest) step))
    | frame n inner body =>
      obtain ⟨innerContext, results, hn, hf, hr, hb⟩ := head.frame_body
      have hp := NativeCoreTyping.progress_with_values (vs := []) hb storeTyped hf (by simp)
      have step := native_frame_progress (outer := state) (by simpa [values] using hp) hb hr
      rw [hn]
      exact .inr (.inr (by simpa using CoreCanStep.context (vs := vs) (tail := rest) step))
    | invoke address type =>
      have step := head.invoke_progress (state := state) storeTyped number
      exact .inr (.inr (by simpa using CoreCanStep.context (vs := []) (tail := rest) step))
    | _ => have hp := head.head; exact False.elim hp
termination_by sizeOf code
decreasing_by all_goals simp_all only; simp_wf; omega

theorem native_core_configuration_progress (typed : NativeCoreConfigurationTyped config output) :
    FlatTerminal config.code ∨ ∃ next, ConfigStep config next := by
  rcases config with ⟨store, state, code⟩
  obtain ⟨hs, context, hf, hr, hc⟩ := typed
  have hp := NativeCoreTyping.progress_with_values (vs := []) hc hs hf (by simp)
  simp only [values, List.map_nil, List.nil_append] at hp
  rcases hp with terminal | escape | step
  · exact .inl terminal
  · cases escape with
    | branch =>
      obtain ⟨hn, tailTyped⟩ := NativeCoreTyping.after_values
        (by simpa only [List.append_assoc] using hc) (by simp)
      obtain ⟨middle, head, _⟩ := NativeCoreTyping.cons_iff.mp tailTyped
      obtain ⟨_, _, ht, _⟩ := head.br_shape (native_numbers_map (by simpa using hn))
      simp at ht
    | return_ =>
      obtain ⟨hn, tailTyped⟩ := NativeCoreTyping.after_values
        (by simpa only [List.append_assoc] using hc) (by simp)
      obtain ⟨middle, head, _⟩ := NativeCoreTyping.cons_iff.mp tailTyped
      obtain ⟨_, _, ht, _⟩ := head.return_shape (native_numbers_map (by simpa using hn))
      rw [hr] at ht
      contradiction
  · exact .inr step

theorem ExecSteps.preserves_native_scalar {ts : List ValType}
    (steps : ExecSteps types code next)
    (typed : NativeCoreTyping store context labels code (ts.map Wasm.Types.embedVal) output)
    (supported : ScalarCode code) (number : ∀ t ∈ ts, t.IsNumber) :
    NativeCoreTyping store context labels next (ts.map Wasm.Types.embedVal) output ∧
      ScalarCode next := by
  induction steps with
  | refl => exact ⟨typed, supported⟩
  | cons step rest ih =>
    obtain ⟨nextTyped, nextScalar⟩ := ExecStep.preserves_native_scalar step typed supported number
    exact ih nextTyped nextScalar

/-- Scalar executions from either native source path remain typed and cannot get stuck. -/
theorem native_scalar_execution_safety
    (typed : NativeCoreTyping store context labels code [] output) (supported : ScalarCode code)
    (steps : ExecSteps types code next) :
    NativeCoreTyping store context labels next [] output ∧
      (FlatTerminal next ∨ ∃ final, ExecStep types next final) := by
  obtain ⟨nextTyped, nextScalar⟩ := ExecSteps.preserves_native_scalar (ts := [])
    steps typed supported (by simp)
  exact ⟨nextTyped, NativeCoreTyping.scalar_progress nextTyped nextScalar⟩

end Wasm.TypeSafety
