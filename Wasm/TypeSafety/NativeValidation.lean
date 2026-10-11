import Wasm.TypeSafety.NativeStore
import Wasm.ExecutableValidationSoundness

namespace Wasm.TypeSafety

/-- Successful executable source checking supplies bottom-aware administrative typing. -/
theorem checkSourceCode_native
    (checked : Validation.checkSourceCode context code input output labels = true)
    (supported : ∀ i ∈ code, CoreSource i) :
    NativeCoreTyping store context labels (instructions code)
      (input.map Types.embedVal) (output.map Types.embedVal) :=
  RuntimeSeqTyping.toNativeCoreTyping (Validation.checkSourceCode_sound checked) supported

theorem checkBottomCode_native
    (checked : Validation.checkBottomCode context code input output labels = true)
    (supported : ∀ i ∈ code, CoreSource i) :
    NativeCoreTyping store context labels (instructions code)
      (input.map Types.embedVal) (output.map Types.embedVal) :=
  ValidationSeqTyping.toNativeCoreTyping (Validation.checkBottomCode_sound checked) supported

theorem checkSourceCode_native_configuration
    (checked : Validation.checkSourceCode context source [] output [] = true)
    (supported : ∀ i ∈ source, CoreSource i) (storeTyped : NativeCoreStoreTyped config.store)
    (frameTyped : CoreFrameTyped config.store config.frame context)
    (returns : context.returns = none) (code : config.code = instructions source) :
    NativeCoreConfigurationTyped config output :=
  RuntimeSeqTyping.native_configuration (Validation.checkSourceCode_sound checked)
    supported storeTyped frameTyped returns code

end Wasm.TypeSafety
