import Wasm.TypeSafety.FlatProgress
import Wasm.Configuration

namespace Wasm.TypeSafety

private def PureInstruction : Instr → Prop
  | .const _ | .nop | .unreachable | .drop | .select _ | .binop _ _ | .eqz _
    | .intUnary _ _ | .intBinary _ _ | .intRel _ _ | .intConvert _
    | .floatUnary _ _ | .floatBinary _ _ | .floatRel _ _ | .floatConvert _ => True
  | _ => False

private def PureAdmin : AdminInstr → Prop
  | .instr i => PureInstruction i
  | .trap => True
  | _ => False

private theorem InstrTyping.pure (h : InstrTyping i input output) : PureInstruction i := by
  induction h <;> simp_all [PureInstruction]

private theorem FlatTyping.pure (h : FlatTyping code input output) :
    ∀ i ∈ code, PureAdmin i := by
  induction h with
  | nil => simp
  | cons head _ ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · cases head with
      | source h => exact InstrTyping.pure h
      | trap => trivial
    · exact ih i hi

private theorem ControlReduces.not_pure (h : ControlReduces types code next) :
    ¬ (∀ i ∈ code, PureAdmin i) := by
  cases h <;>
    simp only [List.forall_mem_append, List.forall_mem_singleton, List.forall_mem_cons,
      PureAdmin, PureInstruction] <;> simp

private theorem FrameReduces.not_pure (h : FrameReduces code next) :
    ¬ (∀ i ∈ code, PureAdmin i) := by
  cases h <;> simp [PureAdmin]

/-- Preservation covers every existing execution rule, not a replacement flat-step relation. -/
theorem ExecStep.preserves_flat (step : ExecStep types code next)
    (typed : FlatTyping code input output) : FlatTyping next input output := by
  induction step generalizing input output with
  | primitive h => exact Reduces.preserves_flat h typed
  | integer h => exact IntegerReduces.preserves_flat h typed
  | activation h => exact False.elim (FrameReduces.not_pure h (FlatTyping.pure typed))
  | control h => exact False.elim (ControlReduces.not_pure h (FlatTyping.pure typed))
  | context _ ih =>
    obtain ⟨middle, left, right⟩ := typed.split
    obtain ⟨last, valuesTyped, body⟩ := left.split
    exact (valuesTyped.append (ih body)).append right
  | label | handler | frame | localFrame =>
    have hp := FlatTyping.pure typed
    simp [PureAdmin] at hp
  | trap _ => exact FlatTyping.trapped

theorem ExecSteps.preserves_flat (steps : ExecSteps types code next)
    (typed : FlatTyping code input output) : FlatTyping next input output := by
  induction steps with
  | refl => exact typed
  | cons step _ ih => exact ih (ExecStep.preserves_flat step typed)

theorem FlatTyping.after_values (typed : FlatTyping (values vs ++ tail) input output) :
    FlatTyping tail (input ++ vs.map Value.type) output := by
  induction vs generalizing input with
  | nil => simpa [values] using typed
  | cons v vs ih =>
    simp only [values, List.map_cons, List.cons_append, FlatTyping.const_cons_iff] at typed
    simpa [List.append_assoc] using ih typed.2

theorem FlatTyping.terminal_values (typed : FlatTyping (values vs) [] output) :
    vs.map Value.type = output := by
  have h := FlatTyping.after_values (tail := []) (by simpa using typed)
  simpa using h

private theorem LocalStep.not_pure (step : LocalStep frame code frame' next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem CallStep.not_pure (step : CallStep store frame code next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem GlobalStep.not_pure (step : GlobalStep store frame code store' next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem ExceptionStep.not_pure (step : ExceptionStep store frame code store' next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem VectorStep.not_pure (step : VectorStep store frame code store' next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | redex h =>
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [PureAdmin, PureInstruction] at hp
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem StructStep.not_pure (step : StructStep store frame code store' next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | redex h =>
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [PureAdmin, PureInstruction] at hp
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem ArrayStep.not_pure (step : ArrayStep store frame code store' next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | redex h =>
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [PureAdmin, PureInstruction] at hp
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem ReferenceStep.not_pure (step : ReferenceStep store frame code next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | redex h =>
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [PureAdmin, PureInstruction] at hp
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem TableStep.not_pure (step : TableStep store frame code store' next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | redex h =>
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [PureAdmin, PureInstruction] at hp
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem BulkStep.not_pure (step : BulkStep store frame code store' next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | redex h =>
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [PureAdmin, PureInstruction] at hp
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

private theorem MemoryStep.not_pure (step : MemoryStep store frame code store' next)
    (hp : ∀ i ∈ code, PureAdmin i) : False := by
  induction step with
  | context _ ih => exact ih (fun i hi => hp i (by simp [hi]))
  | access _ _ _ h =>
    cases h <;> (repeat rw [List.forall_mem_append] at hp) <;>
      simp [PureAdmin, PureInstruction] at hp
  | _ =>
    (repeat rw [List.forall_mem_append] at hp) <;> simp [PureAdmin, PureInstruction] at hp

/-- The flat fragment can only take pure steps; arbitrary ambient stores remain unchanged. -/
theorem ConfigStep.flat_inversion (step : ConfigStep config next)
    (typed : FlatTyping config.code input output) :
    next.store = config.store ∧ next.frame = config.frame ∧
      ExecStep config.frame.module.types config.code next.code := by
  have hp := FlatTyping.pure typed
  cases step with
  | pure h => exact ⟨rfl, rfl, h⟩
  | locals h => exact False.elim (LocalStep.not_pure h hp)
  | call h => exact False.elim (CallStep.not_pure h hp)
  | globals h => exact False.elim (GlobalStep.not_pure h hp)
  | exceptions h => exact False.elim (ExceptionStep.not_pure h hp)
  | vectors h => exact False.elim (VectorStep.not_pure h hp)
  | structures h => exact False.elim (StructStep.not_pure h hp)
  | arrays h => exact False.elim (ArrayStep.not_pure h hp)
  | references h => exact False.elim (ReferenceStep.not_pure h hp)
  | tables h => exact False.elim (TableStep.not_pure h hp)
  | bulk h => exact False.elim (BulkStep.not_pure h hp)
  | memory h => exact False.elim (MemoryStep.not_pure h hp)

theorem ConfigStep.preserves_flat (step : ConfigStep config next)
    (typed : FlatTyping config.code input output) :
    FlatTyping next.code input output ∧ next.store = config.store ∧
      next.frame = config.frame := by
  obtain ⟨store, frame, pure⟩ := ConfigStep.flat_inversion step typed
  exact ⟨ExecStep.preserves_flat pure typed, store, frame⟩

theorem flat_configuration_progress (typed : FlatTyping config.code [] output)
    (supported : ScalarCode config.code) :
    FlatTerminal config.code ∨ ∃ next, ConfigStep config next := by
  rcases FlatTyping.progress (types := config.frame.module.types) typed supported with
      terminal | step
  · exact .inl terminal
  · obtain ⟨code, h⟩ := step
    exact .inr ⟨{ config with code }, .pure h⟩

@[simp] theorem ScalarCode.append_iff : ScalarCode (a ++ b) ↔ ScalarCode a ∧ ScalarCode b := by
  simp only [ScalarCode, List.forall_mem_append]

@[simp] theorem ScalarCode.values (vs : List Value) : ScalarCode (Wasm.values vs) := by
  simp [ScalarCode, Wasm.values, ScalarInstruction]

private theorem Reduces.preserves_scalar (step : Reduces code next) : ScalarCode next := by
  cases step <;> simp [ScalarCode, ScalarInstruction]

private theorem IntegerReduces.preserves_scalar (step : IntegerReduces code next) :
    ScalarCode next := by
  cases step with
  | binary =>
    rename_i result _
    cases result <;> simp [NumericResult.code, ScalarCode, values, ScalarInstruction]
  | _ => simp [ScalarCode, values, ScalarInstruction]

theorem ExecStep.preserves_scalar (step : ExecStep types code next)
    (typed : FlatTyping code input output) (supported : ScalarCode code) : ScalarCode next := by
  induction step generalizing input output with
  | primitive h => exact Reduces.preserves_scalar h
  | integer h => exact IntegerReduces.preserves_scalar h
  | activation h => exact False.elim (FrameReduces.not_pure h (FlatTyping.pure typed))
  | control h => exact False.elim (ControlReduces.not_pure h (FlatTyping.pure typed))
  | context _ ih =>
    obtain ⟨middle, left, right⟩ := typed.split
    obtain ⟨last, valuesTyped, body⟩ := left.split
    simp only [ScalarCode.append_iff] at supported ⊢
    exact ⟨⟨supported.1.1, ih body supported.1.2⟩, supported.2⟩
  | label | handler | frame | localFrame =>
    have hp := FlatTyping.pure typed
    simp [PureAdmin] at hp
  | trap _ => simp [ScalarCode]

theorem ConfigSteps.preserves_flat (steps : ConfigSteps config next)
    (typed : FlatTyping config.code input output) (supported : ScalarCode config.code) :
    FlatTyping next.code input output ∧ ScalarCode next.code ∧
      next.store = config.store ∧ next.frame = config.frame := by
  induction steps with
  | refl => exact ⟨typed, supported, rfl, rfl⟩
  | cons step _ ih =>
    obtain ⟨store, frame, pure⟩ := ConfigStep.flat_inversion step typed
    obtain ⟨ht, hs, hstore, hframe⟩ := ih (ExecStep.preserves_flat pure typed)
      (ExecStep.preserves_scalar pure typed supported)
    exact ⟨ht, hs, hstore.trans store, hframe.trans frame⟩

/-- Every reachable configuration is terminal or has a semantic step. -/
theorem flat_configuration_safety (typed : FlatTyping config.code [] output)
    (supported : ScalarCode config.code) (steps : ConfigSteps config next) :
    FlatTyping next.code [] output ∧
      (FlatTerminal next.code ∨ ∃ final, ConfigStep next final) := by
  obtain ⟨ht, hs, _, _⟩ := ConfigSteps.preserves_flat steps typed supported
  exact ⟨ht, flat_configuration_progress ht hs⟩

/-- Successful executions produce exactly the declared result types. -/
theorem flat_configuration_results (typed : FlatTyping config.code [] output)
    (supported : ScalarCode config.code) (steps : ConfigSteps config next)
    (finished : next.code = values vs) : vs.map Value.type = output := by
  obtain ⟨ht, _, _, _⟩ := ConfigSteps.preserves_flat steps typed supported
  rw [finished] at ht
  exact FlatTyping.terminal_values ht

/-- The certified runner inherits semantic safety at every fuel budget. -/
theorem runConfiguration_flat_safe (typed : FlatTyping config.code [] output)
    (supported : ScalarCode config.code) (fuel : Nat) :
    FlatTyping (runConfiguration fuel config).state.code [] output ∧
      (FlatTerminal (runConfiguration fuel config).state.code ∨
        ∃ next, ConfigStep (runConfiguration fuel config).state next) :=
  flat_configuration_safety typed supported runConfiguration_sound

end Wasm.TypeSafety
