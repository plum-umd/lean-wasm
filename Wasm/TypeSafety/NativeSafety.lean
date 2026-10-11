import Wasm.TypeSafety.NativeConfiguration
import Wasm.TypeSafety.NativeProgress
import Wasm.TypeSafety.NativeValidation

namespace Wasm.TypeSafety

/-- Every reachable native core configuration remains typed and cannot become stuck. -/
theorem native_core_configuration_safety (typed : NativeCoreConfigurationTyped config output)
    (steps : ConfigSteps config next) :
    NativeCoreConfigurationTyped next output ∧
      (FlatTerminal next.code ∨ ∃ final, ConfigStep next final) := by
  obtain ⟨ht, _⟩ := ConfigSteps.preserves_native steps typed
  exact ⟨ht, native_core_configuration_progress ht⟩

theorem native_core_configuration_results (typed : NativeCoreConfigurationTyped config output)
    (steps : ConfigSteps config next) (finished : next.code = values vs) :
    vs.map Value.type = output := by
  obtain ⟨⟨_, context, _, _, codeTyped⟩, _⟩ := ConfigSteps.preserves_native steps typed
  rw [finished] at codeTyped
  exact (List.map_inj_right Wasm.Types.embedVal_injective).mp
    codeTyped.terminal_values.2.symm

theorem runConfiguration_native_core_safe
    (typed : NativeCoreConfigurationTyped config output) (fuel : Nat) :
    NativeCoreConfigurationTyped (runConfiguration fuel config).state output ∧
      (FlatTerminal (runConfiguration fuel config).state.code ∨
        ∃ next, ConfigStep (runConfiguration fuel config).state next) :=
  native_core_configuration_safety typed runConfiguration_sound

theorem checkSourceCode_native_safety
    (checked : Validation.checkSourceCode context source [] output [] = true)
    (supported : ∀ i ∈ source, CoreSource i) (storeTyped : NativeCoreStoreTyped config.store)
    (frameTyped : CoreFrameTyped config.store config.frame context)
    (returns : context.returns = none) (code : config.code = instructions source)
    (steps : ConfigSteps config next) :
    NativeCoreConfigurationTyped next output ∧
      (FlatTerminal next.code ∨ ∃ final, ConfigStep next final) :=
  native_core_configuration_safety
    (checkSourceCode_native_configuration checked supported storeTyped frameTyped returns code)
    steps

end Wasm.TypeSafety
