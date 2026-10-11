import Wasm.Fast.Executor

namespace Wasm

-- Compatibility boundaries use the specification store; the runner converts only once.
def stepConfiguration (config : Configuration) : Option Configuration :=
  (Fast.stepConfiguration (Fast.Configuration.ofSpec config)).map Fast.Configuration.toSpec

theorem stepConfiguration_sound (h : stepConfiguration config = some next) :
    ConfigStep config next := by
  unfold stepConfiguration at h
  cases hs : Fast.stepConfiguration (Fast.Configuration.ofSpec config) with
  | none => simp [hs] at h
  | some result =>
    simp [hs] at h
    subst next
    simpa using Fast.stepConfiguration_spec hs

structure ConfigurationRunResult where
  state : Configuration
  status : RunStatus
  deriving BEq, Repr

/-- Fuel bounds semantic steps, including direct-call lowering and activation entry. -/
def runConfiguration (fuel : Nat) (config : Configuration) : ConfigurationRunResult :=
  let result := Fast.runConfiguration fuel (Fast.Configuration.ofSpec config)
  ⟨result.state.toSpec, result.status⟩

theorem runConfiguration_sound : ConfigSteps config (runConfiguration fuel config).state := by
  simpa [runConfiguration] using
    (Fast.runConfiguration_spec (fuel := fuel) (c := Fast.Configuration.ofSpec config))

theorem runConfiguration_finished
    (h : (runConfiguration fuel config).status = .finished vs) :
    (runConfiguration fuel config).state.code = values vs := by
  have hs := Fast.runConfiguration_status_spec (fuel := fuel)
    (c := Fast.Configuration.ofSpec config)
  change (Fast.runConfiguration fuel (Fast.Configuration.ofSpec config)).status = .finished vs at h
  rw [h] at hs
  exact hs

theorem runConfiguration_trapped (h : (runConfiguration fuel config).status = .trapped) :
    (runConfiguration fuel config).state.code = [.trap] := by
  have hs := Fast.runConfiguration_status_spec (fuel := fuel)
    (c := Fast.Configuration.ofSpec config)
  change (Fast.runConfiguration fuel (Fast.Configuration.ofSpec config)).status = .trapped at h
  rw [h] at hs
  exact hs

end Wasm
