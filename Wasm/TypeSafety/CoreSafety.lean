import Wasm.TypeSafety.CoreProgress

namespace Wasm.TypeSafety

/-- Every reachable core configuration remains typed and cannot become stuck. -/
theorem core_configuration_safety (typed : CoreConfigurationTyped config output)
    (steps : ConfigSteps config next) :
    CoreConfigurationTyped next output ∧
      (FlatTerminal next.code ∨ ∃ final, ConfigStep next final) := by
  obtain ⟨ht, _⟩ := ConfigSteps.preserves_core steps typed
  exact ⟨ht, core_configuration_progress ht⟩

theorem core_configuration_results (typed : CoreConfigurationTyped config output)
    (steps : ConfigSteps config next) (finished : next.code = values vs) :
    vs.map Value.type = output := by
  obtain ⟨⟨_, context, _, _, codeTyped⟩, _⟩ := ConfigSteps.preserves_core steps typed
  rw [finished] at codeTyped
  exact codeTyped.terminal_values

theorem runConfiguration_core_safe (typed : CoreConfigurationTyped config output) (fuel : Nat) :
    CoreConfigurationTyped (runConfiguration fuel config).state output ∧
      (FlatTerminal (runConfiguration fuel config).state.code ∨
        ∃ next, ConfigStep (runConfiguration fuel config).state next) :=
  core_configuration_safety typed runConfiguration_sound

end Wasm.TypeSafety
