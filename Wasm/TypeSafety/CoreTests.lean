import Wasm.TypeSafety.CoreSource
import Wasm.TypeSafety.NativeSafety

namespace Wasm.Tests.CoreSafety

open Wasm.TypeSafety

private def recursiveType : FuncType := ⟨[], [.i32]⟩
private def recursiveModule : ModuleInst :=
  { types := [.func recursiveType], funcs := [⟨0⟩] }
private def recursiveContext : FunctionContext :=
  { types := recursiveModule.types, funcs := [recursiveType], returns := some [.i32] }
private def recursiveFunction : FuncInst :=
  ⟨recursiveType, recursiveModule, .wasm ⟨0, [], [.call 0]⟩⟩
private def recursiveStore : Store := { funcs := [recursiveFunction] }

private theorem recursive_module_typed :
    CoreModuleTyped recursiveStore recursiveModule recursiveContext := by
  refine ⟨rfl, rfl, ?_⟩
  intro x ft ht
  cases x with
  | zero =>
    simp [recursiveContext] at ht
    subst ft
    exact ⟨⟨0⟩, recursiveFunction, rfl, rfl, rfl⟩
  | succ x => simp [recursiveContext] at ht

private theorem recursive_function_typed : CoreFunctionTyped recursiveStore recursiveFunction := by
  refine ⟨recursiveContext, recursive_module_typed, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [recursiveContext]
  · simp [recursiveFunction, recursiveType, ValType.IsInteger]
  · exact .cons (.call (ft := recursiveType) rfl) .nil

private theorem recursive_store_typed : CoreStoreTyped recursiveStore := by
  intro ⟨index⟩ function lookup
  cases index with
  | zero =>
    simp [Store.func?, recursiveStore] at lookup
    subst function
    exact recursive_function_typed
  | succ index => simp [Store.func?, recursiveStore] at lookup

private def recursiveConfig : Configuration :=
  ⟨recursiveStore, { module := recursiveModule }, [.instr (.call 0)]⟩

private theorem recursive_config_typed : CoreConfigurationTyped recursiveConfig [.i32] := by
  refine ⟨recursive_store_typed, { recursiveContext with returns := none }, ?_, rfl, ?_⟩
  · exact ⟨recursive_module_typed, rfl, by simp [recursiveContext]⟩
  · exact .cons (.call (ft := recursiveType) rfl) .nil

-- Recursion needs no termination premise or bounded call-depth hypothesis.
example (steps : ConfigSteps recursiveConfig next) :
    NativeCoreConfigurationTyped next [.i32] ∧
      (FlatTerminal next.code ∨ ∃ final, ConfigStep next final) :=
  native_core_configuration_safety recursive_config_typed.toNativeCoreConfigurationTyped steps

example (fuel : Nat) :
    CoreConfigurationTyped (runConfiguration fuel recursiveConfig).state [.i32] ∧
      (FlatTerminal (runConfiguration fuel recursiveConfig).state.code ∨
        ∃ next, ConfigStep (runConfiguration fuel recursiveConfig).state next) :=
  runConfiguration_core_safe recursive_config_typed fuel

private def pairContext : FunctionContext := { types := [.func ⟨[], [.i32, .i64]⟩] }

-- A branch keeps two results while discarding a lower stack value.
example : CoreTyping {} pairContext []
    (instructions [.block (.typeIdx 0)
      [.const (.i32 99), .const (.i32 7), .const (.i64 9), .br 0]]) [] [.i32, .i64] := by
  apply CoreTyping.single_iff.mpr
  apply CoreInstrTyping.block (ft := ⟨[], [.i32, .i64]⟩) rfl
  refine .cons (.plain (.const (by trivial)) (by trivial)) ?_
  refine .cons (.weaken (stackBelow := [.i32])
    (.plain (.const (by trivial)) (by trivial))) ?_
  refine .cons (.weaken (stackBelow := [.i32, .i32])
    (.plain (.const (by trivial)) (by trivial))) ?_
  exact .cons (.br (input := [.i32]) rfl) .nil

example (typed : CoreConfigurationTyped config results) (steps : ConfigSteps config next) :
    CoreConfigurationTyped next results ∧
      (FlatTerminal next.code ∨ ∃ final, ConfigStep next final) :=
  core_configuration_safety typed steps

#print axioms Wasm.TypeSafety.ConfigStep.preserves_core
#print axioms Wasm.TypeSafety.core_configuration_progress
#print axioms Wasm.TypeSafety.core_configuration_safety
#print axioms Wasm.TypeSafety.core_configuration_results
#print axioms Wasm.TypeSafety.runConfiguration_core_safe
#print axioms Wasm.TypeSafety.FunctionSeqTyping.toCoreTyping
#print axioms Wasm.TypeSafety.FunctionSeqTyping.configuration_safety
#print axioms recursive_config_typed

end Wasm.Tests.CoreSafety
