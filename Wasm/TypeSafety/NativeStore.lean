import Wasm.TypeSafety.NativeSource

namespace Wasm.TypeSafety

/-- The integer frame/store restrictions with bottom-aware function-body typing. -/
def NativeCoreFunctionTyped (store : Store) (function : FuncInst) : Prop :=
  match function.code with
  | .wasm code => ∃ context,
      CoreModuleTyped store function.module context ∧
      context.locals = function.type.params ++ code.locals ∧
      context.returns = some function.type.results ∧
      function.module.types.func? code.typeIdx = some function.type ∧
      (∀ t ∈ context.locals, t.IsInteger) ∧
      (∀ t ∈ function.type.results, t.IsInteger) ∧
      NativeCoreTyping store context [function.type.results]
        (instructions code.body) [] (function.type.results.map Types.embedVal)
  | _ => False

def NativeCoreStoreTyped (store : Store) : Prop :=
  ∀ address function, store.func? address = some function → NativeCoreFunctionTyped store function

def NativeCoreConfigurationTyped (config : Configuration) (output : List ValType) : Prop :=
  NativeCoreStoreTyped config.store ∧ ∃ context,
    CoreFrameTyped config.store config.frame context ∧ context.returns = none ∧
    NativeCoreTyping config.store context [] config.code [] (output.map Types.embedVal)

/-- Either existing function-typing constructor supplies the native function invariant. -/
theorem FuncTyping.native_body
    (typed : FuncTyping types funcs globals mems dataCount function ft
      (tables := tables) (elems := elems) (declaredRefs := declaredRefs)
      (definedTypes := definedTypes) (funcTypeIndices := funcTypeIndices)
      (elemTypes := elemTypes) (tags := tags))
    (supported : ∀ i ∈ function.body, CoreSource i) :
    ∃ context : FunctionContext, context.types = types ∧ context.funcs = funcs ∧
      context.locals = ft.params ++ function.locals ∧ context.returns = some ft.results ∧
      types.func? function.typeIdx = some ft ∧
      NativeCoreTyping store context [ft.results]
        (instructions function.body) [] (ft.results.map Types.embedVal) := by
  let context : FunctionContext :=
    { types, locals := ft.params ++ function.locals, funcs, returns := some ft.results,
      globals, mems, dataCount, tables, elems, declaredRefs, definedTypes,
      funcTypeIndices, elemTypes, tags }
  refine ⟨context, rfl, rfl, rfl, rfl, ?_⟩
  cases typed with
  | wasm signature _ body =>
    exact ⟨signature, RuntimeSeqTyping.toNativeCoreTyping body supported⟩
  | wasmValidation signature _ body =>
    exact ⟨signature, ValidationSeqTyping.toNativeCoreTyping body supported⟩

theorem FuncTyping.toNativeCoreFunctionTyped
    (typed : FuncTyping module.types funcs globals mems dataCount function ft
      (tables := tables) (elems := elems) (declaredRefs := declaredRefs)
      (definedTypes := definedTypes) (funcTypeIndices := funcTypeIndices)
      (elemTypes := elemTypes) (tags := tags))
    (moduleTyped : CoreModuleTyped store module { types := module.types, funcs })
    (localsInteger : ∀ t ∈ ft.params ++ function.locals, t.IsInteger)
    (resultsInteger : ∀ t ∈ ft.results, t.IsInteger)
    (supported : ∀ i ∈ function.body, CoreSource i) :
    NativeCoreFunctionTyped store ⟨ft, module, .wasm function⟩ := by
  obtain ⟨context, ht, hf, hl, hr, signature, body⟩ := FuncTyping.native_body typed supported
  refine ⟨context, ?_, hl, hr, signature, ?_, resultsInteger, body⟩
  · rcases moduleTyped with ⟨hm, hn, lookup⟩
    exact ⟨ht, by simpa [hf] using hn, by simpa [hf] using lookup⟩
  · simpa [hl] using localsInteger

theorem CoreFunctionTyped.toNativeCoreFunctionTyped
    (h : CoreFunctionTyped store function) : NativeCoreFunctionTyped store function := by
  cases function with
  | mk type module code =>
    cases code with
    | wasm code =>
      obtain ⟨context, hm, hl, hr, ht, hi, ho, hb⟩ := h
      exact ⟨context, hm, hl, hr, ht, hi, ho, hb.toNativeCoreTyping⟩
    | host | hostTyped => contradiction

theorem CoreStoreTyped.toNativeCoreStoreTyped (h : CoreStoreTyped store) :
    NativeCoreStoreTyped store :=
  fun address function lookup => (h address function lookup).toNativeCoreFunctionTyped

theorem CoreConfigurationTyped.toNativeCoreConfigurationTyped
    (h : CoreConfigurationTyped config output) : NativeCoreConfigurationTyped config output := by
  obtain ⟨storeTyped, context, frameTyped, returns, codeTyped⟩ := h
  exact ⟨storeTyped.toNativeCoreStoreTyped, context, frameTyped, returns,
    codeTyped.toNativeCoreTyping⟩

/-- Source typing establishes the native initial expression invariant. -/
theorem RuntimeSeqTyping.native_configuration
    (sourceTyped : RuntimeSeqTyping context [] source [] output)
    (supported : ∀ i ∈ source, CoreSource i) (storeTyped : NativeCoreStoreTyped config.store)
    (frameTyped : CoreFrameTyped config.store config.frame context)
    (returns : context.returns = none) (code : config.code = instructions source) :
    NativeCoreConfigurationTyped config output := by
  refine ⟨storeTyped, context, frameTyped, returns, ?_⟩
  rw [code]
  exact RuntimeSeqTyping.toNativeCoreTyping sourceTyped supported

theorem ValidationSeqTyping.native_configuration
    (sourceTyped : ValidationSeqTyping context [] source [] (output.map Types.embedVal))
    (supported : ∀ i ∈ source, CoreSource i) (storeTyped : NativeCoreStoreTyped config.store)
    (frameTyped : CoreFrameTyped config.store config.frame context)
    (returns : context.returns = none) (code : config.code = instructions source) :
    NativeCoreConfigurationTyped config output := by
  refine ⟨storeTyped, context, frameTyped, returns, ?_⟩
  rw [code]
  exact ValidationSeqTyping.toNativeCoreTyping sourceTyped supported

theorem NativeCoreFunctionTyped.params_integer (h : NativeCoreFunctionTyped store function) :
    ∀ t ∈ function.type.params, t.IsInteger := by
  cases function with
  | mk type module code =>
    cases code with
    | wasm code =>
      obtain ⟨context, _, hl, _, _, hi, _, _⟩ := h
      intro t ht
      apply hi
      rw [hl]; simp [ht]
    | host | hostTyped => contradiction

/-- A source-typed function installs a typed activation under its own defining module. -/
theorem Invokes.native_core_typed (functionTyped : NativeCoreFunctionTyped store function)
    (invoke : Invokes store function args activation) :
    NativeCoreInstrTyping store callerContext labels activation []
      (function.type.results.map Types.embedVal) := by
  have hp := functionTyped.params_integer
  cases invoke with
  | @wasm type args module code signature argTypes =>
    obtain ⟨context, hm, hl, hr, _, hi, _, hb⟩ := functionTyped
    have ha := ArgsTyped.integer_types argTypes hp
    have hf := CoreFrameTyped.initialize hm hl hi ha
    apply NativeCoreInstrTyping.frame hf hr
    exact .cons (.label (branch := type.results) hb .nil) .nil

theorem NativeCoreFunctionTyped.invokable (h : NativeCoreFunctionTyped store function)
    (types : args.map Value.type = function.type.params) :
    ∃ activation, Invokes store function args activation := by
  have hp := h.params_integer
  cases function with
  | mk type module code =>
    cases code with
    | wasm code =>
      obtain ⟨_, _, _, _, signature, _, _, _⟩ := h
      exact ⟨_, .wasm signature (ArgsTyped.of_integer_types types hp)⟩
    | host | hostTyped => contradiction

end Wasm.TypeSafety
