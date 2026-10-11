import Wasm.Fast.MachineExecution

namespace Wasm.Fast

-- These configuration APIs are boundaries around the sole execution machine.
def stepConfiguration (c : Configuration) : Option Configuration :=
  (Machine.step (Machine.ofConfiguration c)).map Machine.toConfiguration

theorem stepConfiguration_sound (h : stepConfiguration c = some next) :
    ConfigStep c next := by
  unfold stepConfiguration at h
  cases hs : Machine.step (Machine.ofConfiguration c) with
  | none => simp [hs] at h
  | some result =>
    simp [hs] at h
    subst next
    simpa using Machine.step_sound hs

structure ConfigurationRunResult where
  state : Configuration
  status : RunStatus
  deriving BEq, Repr

/-- Fuel bounds semantic steps, including direct-call lowering and activation entry. -/
def runConfiguration (fuel : Nat) (c : Configuration) : ConfigurationRunResult :=
  let result := Machine.run fuel (Machine.ofConfiguration c)
  ⟨result.state.toConfiguration, result.status⟩

theorem runConfiguration_sound : ConfigSteps c (runConfiguration fuel c).state := by
  simpa [runConfiguration] using
    (Machine.run_sound (fuel := fuel) (m := Machine.ofConfiguration c))

/-- Each successful fast step is one step of the existing specification. -/
theorem stepConfiguration_spec (h : stepConfiguration c = some next) :
    Wasm.ConfigStep c.toSpec next.toSpec := (stepConfiguration_sound h).toSpec

/-- Execution follows the unchanged specification; the array heap is decoded only in proofs. -/
theorem runConfiguration_spec :
    Wasm.ConfigSteps c.toSpec (runConfiguration fuel c).state.toSpec :=
  (runConfiguration_sound).toSpec

theorem runConfiguration_status_spec :
    Machine.StatusSpec (runConfiguration fuel c).status (runConfiguration fuel c).state.toSpec :=
  Machine.run_status_spec

end Wasm.Fast
