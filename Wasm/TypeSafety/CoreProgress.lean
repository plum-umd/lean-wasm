import Wasm.TypeSafety.CoreContexts

namespace Wasm.TypeSafety

/-- Branches and returns wait for their enclosing label or activation to unwind them. -/
inductive CoreEscape : List AdminInstr → Prop where
  | branch : CoreEscape (values vs ++ [.instr (.br x)] ++ tail)
  | return_ : CoreEscape (values vs ++ [.instr .return_] ++ tail)

def CoreCanStep (store : Store) (state : Frame) (code : List AdminInstr) : Prop :=
  ∃ next, ConfigStep ⟨store, state, code⟩ next

theorem CoreCanStep.context (h : CoreCanStep store state code) :
    CoreCanStep store state (values vs ++ code ++ tail) := by
  obtain ⟨⟨nextStore, nextState, next⟩, step⟩ := h
  exact ⟨_, ConfigStep.in_core_context step⟩

theorem CoreCanStep.control {context : FunctionContext}
    (typeContext : context.types = state.module.types)
    (h : ControlReduces context.types code next) : CoreCanStep store state code := by
  rw [typeContext] at h
  exact ⟨_, .pure (.control h)⟩

theorem CoreCanStep.activation (h : FrameReduces code next) : CoreCanStep store state code :=
  ⟨_, .pure (.activation h)⟩

private theorem split_last (h : vs.map Value.type = ts ++ [t]) :
    ∃ stack v, vs = stack ++ [v] ∧ v.type = t := by
  obtain ⟨stack, args, rfl, _, ha⟩ := List.map_eq_append_iff.mp h
  simp only [List.map_eq_cons_iff, List.map_eq_nil_iff] at ha
  obtain ⟨v, rest, rfl, ht, rfl⟩ := ha
  exact ⟨stack, v, rfl, ht⟩

private theorem split_i32 (h : vs.map Value.type = ts ++ [.i32]) :
    ∃ stack bits, vs = stack ++ [.i32 bits] := by
  obtain ⟨stack, v, rfl, ht⟩ := split_last h
  cases v <;> simp only [Value.type] at ht <;> try contradiction
  exact ⟨stack, _, rfl⟩

/-- A waiting escape always has a reduction at the next enclosing label. -/
theorem CoreEscape.label_step {branch : List ValType} (escape : CoreEscape body)
    (typed : CoreTyping store context (branch :: labels) body [] results)
    (typeContext : context.types = state.module.types) :
    CoreCanStep store state [.label branch.length continuation body] := by
  cases escape with
  | return_ => exact CoreCanStep.control typeContext .returnLabel
  | @branch vs tail x =>
    cases x with
    | succ x => exact CoreCanStep.control typeContext .brSucc
    | zero =>
      simp only [List.append_assoc] at typed
      cases typed.after_values with
      | cons head _ =>
        obtain ⟨ts, below, ht, hi⟩ := head.br_shape
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
        subst ts
        simp only [List.nil_append] at hi
        obtain ⟨discarded, returned, he, _, hr⟩ := List.map_eq_append_iff.mp hi
        have hlen : returned.length = branch.length := by
          have := congrArg List.length hr
          simpa using this
        subst vs
        apply CoreCanStep.control typeContext
        simpa [values, List.map_append, List.append_assoc] using
          (ControlReduces.brZero (types := context.types) (continuation := continuation)
            (discarded := discarded) (tail := tail) hlen)

/-- A closed activation catches return escapes and cannot expose a free branch. -/
theorem CoreEscape.frame_step (escape : CoreEscape body)
    (typed : CoreTyping store context [] body [] results)
    (returns : context.returns = some results) :
    CoreCanStep store outer [.frame results.length state body] := by
  cases escape with
  | branch =>
    simp only [List.append_assoc] at typed
    cases typed.after_values with
    | cons head _ =>
      obtain ⟨_, _, ht, _⟩ := head.br_shape
      simp at ht
  | @return_ vs tail =>
    simp only [List.append_assoc] at typed
    cases typed.after_values with
    | cons head _ =>
      obtain ⟨returnTypes, below, ht, hi⟩ := head.return_shape
      have he : returnTypes = results := Option.some.inj (ht.symm.trans returns)
      subst returnTypes
      simp only [List.nil_append] at hi
      obtain ⟨discarded, returned, he, _, hr⟩ := List.map_eq_append_iff.mp hi
      have hlen : returned.length = results.length := by
        have := congrArg List.length hr
        simpa using this
      subst vs
      apply CoreCanStep.activation
      simpa [values, List.map_append, List.append_assoc] using
        (FrameReduces.return_ (state := state) (discarded := discarded) (tail := tail) hlen)

theorem CoreTyping.terminal_values (typed : CoreTyping store context labels (values vs) [] output) :
    vs.map Value.type = output := by
  have h := CoreTyping.after_values (tail := []) (by simpa using typed)
  simpa using h

private theorem label_progress {branch : List ValType}
    (progress : FlatTerminal body ∨ CoreEscape body ∨ CoreCanStep store state body)
    (typed : CoreTyping store context (branch :: labels) body [] results)
    (typeContext : context.types = state.module.types) :
    CoreCanStep store state [.label branch.length continuation body] := by
  rcases progress with terminal | escape | step
  · rcases terminal with ⟨vs, rfl⟩ | rfl
    · exact CoreCanStep.control typeContext .labelDone
    · exact CoreCanStep.control typeContext .labelTrap
  · exact escape.label_step typed typeContext
  · obtain ⟨⟨nextStore, nextState, next⟩, step⟩ := step
    exact ⟨_, ConfigStep.in_core_label step⟩

private theorem frame_progress
    (progress : FlatTerminal body ∨ CoreEscape body ∨ CoreCanStep store state body)
    (typed : CoreTyping store context [] body [] results)
    (returns : context.returns = some results) :
    CoreCanStep store outer [.frame results.length state body] := by
  rcases progress with terminal | escape | step
  · rcases terminal with ⟨vs, rfl⟩ | rfl
    · have hlen : vs.length = results.length := by
        have := congrArg List.length typed.terminal_values
        simpa using this
      exact CoreCanStep.activation (.done hlen)
    · exact CoreCanStep.activation .trap
  · exact escape.frame_step typed returns
  · obtain ⟨⟨nextStore, nextState, next⟩, step⟩ := step
    exact ⟨_, ConfigStep.in_core_frame step⟩

/-- Source instructions either reduce or wait for a surrounding label/activation. -/
theorem CoreInstrTyping.source_progress
    (typed : CoreInstrTyping store context labels (.instr i) (vs.map Value.type) output)
    (frameTyped : CoreFrameTyped store state context)
    (notConstant : ∀ v, i ≠ .const v) :
    CoreEscape (values vs ++ [.instr i]) ∨ CoreCanStep store state (values vs ++ [.instr i]) := by
  by_cases scalar : ScalarInstruction i
  · obtain ⟨next, step⟩ := scalar_instruction_progress
      (types := state.module.types) (typed.of_scalar scalar) scalar notConstant rfl
    exact .inr ⟨_, .pure step⟩
  · cases i with
    | block bt body =>
      obtain ⟨ft, below, ht, hi, _, _⟩ := typed.block_shape
      obtain ⟨stack, args, he, _, ha⟩ := List.map_eq_append_iff.mp hi
      have hlen : args.length = ft.params.length := by
        have := congrArg List.length ha; simpa using this
      subst vs
      apply Or.inr
      have h := CoreCanStep.control (store := store) frameTyped.1.1
        (ControlReduces.block (body := body) ht hlen)
      simpa [values, List.map_append, List.append_assoc] using
        CoreCanStep.context (vs := stack) (tail := []) h
    | loop bt body =>
      obtain ⟨ft, below, ht, hi, _, _⟩ := typed.loop_shape
      obtain ⟨stack, args, he, _, ha⟩ := List.map_eq_append_iff.mp hi
      have hlen : args.length = ft.params.length := by
        have := congrArg List.length ha; simpa using this
      subst vs
      apply Or.inr
      have h := CoreCanStep.control (store := store) frameTyped.1.1
        (ControlReduces.loop (body := body) ht hlen)
      simpa [values, List.map_append, List.append_assoc] using
        CoreCanStep.context (vs := stack) (tail := []) h
    | if_ bt yes no =>
      obtain ⟨ft, below, _, hi, _, _, _⟩ := typed.if_shape
      obtain ⟨stack, bits, he⟩ := split_i32 (vs := vs) (ts := below ++ ft.params)
        (by simpa [List.append_assoc] using hi)
      subst vs
      apply Or.inr
      have h : CoreCanStep store state
          [.instr (.const (.i32 bits)), .instr (.if_ bt yes no)] := by
        by_cases hz : bits = 0
        · subst bits; exact CoreCanStep.control frameTyped.1.1 .ifZero
        · exact CoreCanStep.control frameTyped.1.1 (.ifNonzero hz)
      simpa [values, List.map_append, List.append_assoc] using
        CoreCanStep.context (vs := stack) (tail := []) h
    | br x => exact .inl (by simpa using CoreEscape.branch (vs := vs) (x := x) (tail := []))
    | return_ => exact .inl (by simpa using CoreEscape.return_ (vs := vs) (tail := []))
    | brIf x =>
      obtain ⟨ts, below, _, hi, _⟩ := typed.brIf_shape
      obtain ⟨stack, bits, he⟩ := split_i32 (vs := vs) (ts := below ++ ts)
        (by simpa [List.append_assoc] using hi)
      subst vs
      apply Or.inr
      have h : CoreCanStep store state [.instr (.const (.i32 bits)), .instr (.brIf x)] := by
        by_cases hz : bits = 0
        · subst bits; exact CoreCanStep.control frameTyped.1.1 .brIfZero
        · exact CoreCanStep.control frameTyped.1.1 (.brIfNonzero hz)
      simpa [values, List.map_append, List.append_assoc] using
        CoreCanStep.context (vs := stack) (tail := []) h
    | brTable targets fallback =>
      obtain ⟨ts, below, _, _, hi⟩ := typed.brTable_shape
      obtain ⟨stack, bits, he⟩ := split_i32 hi
      subst vs
      apply Or.inr
      have h : CoreCanStep store state
          [.instr (.const (.i32 bits)), .instr (.brTable targets fallback)] := by
        cases hit : targets[bits.toNat]? with
        | some x => exact CoreCanStep.control frameTyped.1.1 (.brTableHit hit)
        | none =>
          exact CoreCanStep.control frameTyped.1.1
            (.brTableDefault (List.getElem?_eq_none_iff.mp hit))
      simpa [values, List.map_append, List.append_assoc] using
        CoreCanStep.context (vs := stack) (tail := []) h
    | localGet x =>
      obtain ⟨t, _, ht, _, _⟩ := typed.localGet_shape
      obtain ⟨v, lookup, _, _⟩ := frameTyped.get ht
      exact .inr ⟨_, by
        simpa using ConfigStep.locals (LocalStep.context (vs := vs) (tail := []) (.get lookup))⟩
    | localSet x =>
      obtain ⟨t, below, ht, hi, _⟩ := typed.localSet_shape
      obtain ⟨stack, v, he, _⟩ := split_last hi
      obtain ⟨old, lookup, _, _⟩ := frameTyped.get ht
      have bound : x < state.locals.length := by
        by_cases h : x < state.locals.length
        · exact h
        · have hn : state.locals[x]? = none :=
            List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt h)
          rw [lookup] at hn
          contradiction
      subst vs
      exact .inr ⟨_, by
        simpa [values, List.map_append, List.append_assoc] using
          ConfigStep.locals (LocalStep.context (vs := stack) (tail := [])
            (LocalStep.set (v := v) bound))⟩
    | localTee x =>
      obtain ⟨t, below, _, hi, _⟩ := typed.localTee_shape
      obtain ⟨stack, v, he, _⟩ := split_last hi
      subst vs
      exact .inr ⟨_, by
        simpa [values, List.map_append, List.append_assoc] using
          ConfigStep.locals (LocalStep.context (vs := stack) (tail := [])
            (LocalStep.tee (state := state) (v := v) (x := x)))⟩
    | call x =>
      obtain ⟨ft, _, ht, _, _⟩ := typed.call_shape
      obtain ⟨address, function, ha, hf, _⟩ := frameTyped.1.2.2 _ _ ht
      exact .inr ⟨_, by
        simpa using ConfigStep.call (CallStep.context (vs := vs) (tail := []) (.call ha hf))⟩
    | _ => have hp := typed.head; simp_all [CoreHead, ScalarInstruction]

theorem CoreInstrTyping.invoke_progress
    (typed : CoreInstrTyping store context labels (.invoke address type)
      (vs.map Value.type) output) (storeTyped : CoreStoreTyped store) :
    CoreCanStep store state (values vs ++ [.invoke address type]) := by
  obtain ⟨function, below, hf, ht, hi, _⟩ := typed.invoke_shape
  obtain ⟨stack, args, he, _, ha⟩ := List.map_eq_append_iff.mp hi
  obtain ⟨activation, invoke⟩ := CoreFunctionTyped.invokable (storeTyped _ _ hf) ha
  have step : CoreCanStep store state (values args ++ [.invoke address function.type]) :=
    ⟨_, .call (.invoke hf rfl invoke)⟩
  subst vs
  rw [ht]
  simpa [values, List.map_append, List.append_assoc] using
    CoreCanStep.context (vs := stack) (tail := []) step

theorem CoreEscape.append (escape : CoreEscape code) : CoreEscape (code ++ rest) := by
  cases escape with
  | @branch vs tail x =>
    simpa [List.append_assoc] using CoreEscape.branch (vs := vs) (x := x) (tail := tail ++ rest)
  | @return_ vs tail =>
    simpa [List.append_assoc] using CoreEscape.return_ (vs := vs) (tail := tail ++ rest)

/-- Progress with an explicit operand prefix and pending branch/return outcomes. -/
theorem CoreTyping.progress_with_values
    (typed : CoreTyping store context labels code (vs.map Value.type) output)
    (storeTyped : CoreStoreTyped store) (frameTyped : CoreFrameTyped store state context) :
    FlatTerminal (values vs ++ code) ∨ CoreEscape (values vs ++ code) ∨
      CoreCanStep store state (values vs ++ code) := by
  cases code with
  | nil => exact .inl (.inl ⟨vs, by simp⟩)
  | cons i rest =>
    obtain ⟨middle, head, tail⟩ := CoreTyping.cons_iff.mp typed
    cases i with
    | instr source =>
      by_cases constant : ∃ v, source = .const v
      · obtain ⟨v, rfl⟩ := constant
        have shape := head.const_shape
        have ht : CoreTyping store context labels rest ((vs ++ [v]).map Value.type) output := by
          simpa [List.map_append, ← shape.1] using tail
        simpa [values, List.map_append, List.append_assoc] using
          CoreTyping.progress_with_values ht storeTyped frameTyped
      · have hn : ∀ v, source ≠ Instr.const v := fun v h => constant ⟨v, h⟩
        rcases head.source_progress frameTyped hn with escape | step
        · exact .inr (.inl (by simpa using escape.append (rest := rest)))
        · exact .inr (.inr (by simpa using CoreCanStep.context (vs := []) (tail := rest) step))
    | trap =>
      by_cases terminal : values vs ++ [.trap] ++ rest = [.trap]
      · exact .inl (.inr (by simpa using terminal))
      · exact .inr (.inr ⟨_, by simpa using ConfigStep.pure (ExecStep.trap terminal)⟩)
    | label n continuation body =>
      obtain ⟨branch, results, hn, _, hb, _⟩ := head.label_shape
      have hp := CoreTyping.progress_with_values (vs := []) hb storeTyped frameTyped
      have step := label_progress (by simpa [values] using hp) hb frameTyped.1.1
        (continuation := continuation)
      rw [hn]
      exact .inr (.inr (by simpa using CoreCanStep.context (vs := vs) (tail := rest) step))
    | frame n inner body =>
      obtain ⟨innerContext, results, hn, _, hf, hr, hb⟩ := head.frame_shape
      have hp := CoreTyping.progress_with_values (vs := []) hb storeTyped hf
      have step := frame_progress (outer := state) (by simpa [values] using hp) hb hr
      rw [hn]
      exact .inr (.inr (by simpa using CoreCanStep.context (vs := vs) (tail := rest) step))
    | invoke address type =>
      have step := head.invoke_progress (state := state) storeTyped
      exact .inr (.inr (by simpa using CoreCanStep.context (vs := []) (tail := rest) step))
    | _ => have hp := head.head; exact False.elim hp
termination_by sizeOf code
decreasing_by all_goals simp_all only; simp_wf; omega

/-- Closed core configurations are terminal or have a step in the full semantic relation. -/
theorem core_configuration_progress (typed : CoreConfigurationTyped config output) :
    FlatTerminal config.code ∨ ∃ next, ConfigStep config next := by
  rcases config with ⟨store, state, code⟩
  obtain ⟨hs, context, hf, hr, hc⟩ := typed
  have hp := CoreTyping.progress_with_values (vs := []) hc hs hf
  simp only [values, List.map_nil, List.nil_append] at hp
  rcases hp with terminal | escape | step
  · exact .inl terminal
  · cases escape with
    | branch =>
      simp only [List.append_assoc] at hc
      cases hc.after_values with
      | cons head _ =>
        obtain ⟨_, _, ht, _⟩ := head.br_shape
        simp at ht
    | return_ =>
      simp only [List.append_assoc] at hc
      cases hc.after_values with
      | cons head _ =>
        obtain ⟨_, _, ht, _⟩ := head.return_shape
        rw [hr] at ht
        contradiction
  · exact .inr step

end Wasm.TypeSafety
