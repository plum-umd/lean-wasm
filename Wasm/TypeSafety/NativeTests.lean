import Wasm.TypeSafety.NativeValidation
import Wasm.TypeSafety.NativeMatching
import Wasm.TypeSafety.NativeProgress
import Wasm.TypeSafety.NativeSafety

namespace Wasm.Tests.NativeSafety

open Wasm.TypeSafety

private theorem select_typed_shape
    (h : InstrTyping (.select (some [t])) input output) :
    ∃ stackBelow, input = stackBelow ++ [t, t, .i32] ∧ output = stackBelow ++ [t] := by
  generalize hi : Instr.select (some [t]) = i at h
  induction h with
  | selectTyped => cases hi; exact ⟨[], rfl, rfl⟩
  | @weaken i input output stackBelow _ ih =>
    obtain ⟨below, ha, ho⟩ := ih hi
    exact ⟨stackBelow ++ below, by simp [ha, List.append_assoc],
      by simp [ho, List.append_assoc]⟩
  | _ => cases hi

-- Both select annotations are in dead code; nullability widens between them.
private def deadReferenceSelect : List Instr :=
  [.unreachable, .select (some [.refNonNull .func]), .const (.i32 1),
    .select (some [.ref .func]), .drop]

private theorem deadReferenceSelect_supported : ∀ i ∈ deadReferenceSelect, CoreSource i := by
  intro i hi
  apply CoreSource.scalar
  simp only [deadReferenceSelect, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h <;> subst i <;> trivial

private theorem deadReferenceSelect_checked :
    Validation.checkSourceCode {} deadReferenceSelect [] [] [] = true := by decide +kernel

private theorem deadReferenceSelect_native :
    NativeCoreTyping {} {} [] (instructions deadReferenceSelect) [] [] :=
  RuntimeSeqTyping.toNativeCoreTyping
    (Validation.checkSourceCode_sound deadReferenceSelect_checked) deadReferenceSelect_supported

private def sourceFunction : Func := ⟨0, [], deadReferenceSelect⟩

private def sourceModule : ModuleInst := { types := [.func ⟨[], []⟩], funcs := [⟨0⟩] }

private def sourceInstance : FuncInst := ⟨⟨[], []⟩, sourceModule, .wasm sourceFunction⟩

private def sourceStore : Store := { funcs := [sourceInstance] }

private theorem sourceFunction_typed :
    FuncTyping sourceModule.types [⟨[], []⟩] [] [] 0 sourceFunction ⟨[], []⟩ := by
  apply FuncTyping.wasm rfl
  · decide +kernel
  · apply Validation.checkSourceCode_sound
    decide +kernel

private theorem sourceStore_native : NativeCoreStoreTyped sourceStore := by
  intro ⟨address⟩ function lookup
  have only : address = 0 := by
    cases address with
    | zero => rfl
    | succ address => simp [sourceStore, Store.func?] at lookup
  subst address
  have functionEq : function = sourceInstance := by
    simpa [sourceStore, Store.func?] using lookup.symm
  subst function
  apply FuncTyping.toNativeCoreFunctionTyped sourceFunction_typed
  · refine ⟨rfl, rfl, ?_⟩
    intro x ft hx
    have only : x = 0 := by
      cases x with
      | zero => rfl
      | succ x => simp at hx
    subst x
    have type : ft = ⟨[], []⟩ := by simpa using hx.symm
    subst ft
    exact ⟨⟨0⟩, sourceInstance, rfl, rfl, rfl⟩
  · simp [sourceFunction]
  · simp
  · exact deadReferenceSelect_supported

-- The old exact-stack invariant cannot express this valid, closed, core function body.
private theorem deadReferenceSelect_not_exact :
    ¬ CoreTyping store context [] (instructions deadReferenceSelect) [] [] := by
  intro typed
  change CoreTyping store context []
    [.instr .unreachable, .instr (.select (some [.refNonNull .func])), .instr (.const (.i32 1)),
      .instr (.select (some [.ref .func])), .instr .drop] [] [] at typed
  obtain ⟨_, _, tail⟩ := CoreTyping.cons_iff.mp typed
  obtain ⟨middle, first, tail⟩ := CoreTyping.cons_iff.mp tail
  obtain ⟨_, tail⟩ := CoreTyping.const_cons_iff.mp tail
  obtain ⟨_, second, _⟩ := CoreTyping.cons_iff.mp tail
  obtain ⟨below, _, hfirst⟩ := select_typed_shape (first.of_scalar (by trivial))
  obtain ⟨below', hsecond, _⟩ := select_typed_shape (second.of_scalar (by trivial))
  have last : middle = below' ++ [.ref .func, .ref .func] :=
    List.append_cancel_right (by simpa [List.append_assoc] using hsecond)
  rw [hfirst] at last
  have incompatible := congrArg List.getLast? last
  simp at incompatible

-- Bottom remains bottom rather than being arbitrarily projected to i32 or i64.
example : NativeCoreTyping store context []
    (instructions [.unreachable, .const (.i32 1), .select none, .drop]) [] [] := by
  refine .cons (.source (.unreachable (output := [.bot, .bot])) (.scalar (by trivial))) ?_
  refine .cons (.weaken (stackBelow := [.bot, .bot])
    (.source (.legacy (.plain (.plain (.plain (.const (by trivial))))))
      (.scalar (by trivial)))) ?_
  exact .cons (.source (.select (t := .bot) (Or.inl rfl)) (.scalar (by trivial)))
    (.cons (.source (.drop (t := .bot)) (.scalar (by trivial))) .nil)

-- A branch table may consume bottom arguments and target matching labels.
example : NativeCoreTyping store context [[.i32]]
    (instructions [.unreachable, .brTable [0] 0]) [] [.i32] := by
  refine .cons (.source (.unreachable (output := [.bot, .i32])) (.scalar (by trivial))) ?_
  refine .cons (.source (.brTableMatches (arguments := [.bot]) (input := []) ?_) .brTable) .nil
  intro x hx
  have : x = 0 := by simpa using hx
  subst x
  exact ⟨[.i32], rfl, .cons .bot .nil⟩

example (typed : ValidationSeqTyping context labels code input output)
    (supported : ∀ i ∈ code, CoreSource i) :
    NativeCoreTyping store context labels (instructions code) input output :=
  ValidationSeqTyping.toNativeCoreTyping typed supported

example (typed : CoreConfigurationTyped config results) :
    NativeCoreConfigurationTyped config results := typed.toNativeCoreConfigurationTyped

-- The validator-to-function bridge is usable by a real store and invocation.
example : ∃ activation, Invokes sourceStore sourceInstance [] activation ∧
    NativeCoreInstrTyping sourceStore {} [] activation [] [] := by
  have typed := sourceStore_native ⟨0⟩ sourceInstance rfl
  obtain ⟨activation, invoke⟩ := NativeCoreFunctionTyped.invokable typed (args := []) rfl
  exact ⟨activation, invoke, Invokes.native_core_typed typed invoke⟩

private def sourceCaller : Configuration :=
  ⟨sourceStore, { module := sourceModule }, [.instr (.call 0)]⟩

private theorem sourceCaller_native : NativeCoreConfigurationTyped sourceCaller [] := by
  refine ⟨sourceStore_native, { types := sourceModule.types, funcs := [⟨[], []⟩] }, ?_, rfl, ?_⟩
  · refine ⟨⟨rfl, rfl, ?_⟩, rfl, by simp⟩
    intro x ft lookup
    cases x with
    | zero =>
      simp at lookup
      subst ft
      exact ⟨⟨0⟩, sourceInstance, rfl, rfl, rfl⟩
    | succ x => simp at lookup
  · exact .cons (.source (.legacy (.call (ft := ⟨[], []⟩) rfl)) .call) .nil

-- Progress uses the source-typed store containing the body that fails exact administrative typing.
example : FlatTerminal sourceCaller.code ∨ ∃ next, ConfigStep sourceCaller next :=
  native_core_configuration_progress sourceCaller_native

example (invoke : Invokes sourceStore sourceInstance [] activation) :
    FlatTerminal [activation] ∨
      ∃ next, ConfigStep ⟨sourceStore, sourceCaller.frame, [activation]⟩ next := by
  obtain ⟨storeTyped, context, frameTyped, returns, _⟩ := sourceCaller_native
  apply native_core_configuration_progress
    (config := ⟨sourceStore, sourceCaller.frame, [activation]⟩) (output := [])
  refine ⟨storeTyped, context, frameTyped, returns, .cons ?_ .nil⟩
  exact Invokes.native_core_typed (sourceStore_native ⟨0⟩ sourceInstance rfl) invoke

example (typed : NativeCoreConfigurationTyped config results) :
    FlatTerminal config.code ∨ ∃ next, ConfigStep config next :=
  native_core_configuration_progress typed

-- Every pure execution trace of the unreachable/subtyping regression remains safe.
example (steps : ExecSteps types (instructions deadReferenceSelect) next) :
    NativeCoreTyping {} {} [] next [] [] ∧
      (FlatTerminal next ∨ ∃ final, ExecStep types next final) := by
  apply native_scalar_execution_safety deadReferenceSelect_native (steps := steps)
  simp [deadReferenceSelect, instructions, ScalarCode, ScalarInstruction]

example (steps : ExecSteps types code next)
    (typed : NativeCoreTyping store context labels code [] output)
    (supported : ScalarCode code) :
    NativeCoreTyping store context labels next [] output ∧
      (FlatTerminal next ∨ ∃ final, ExecStep types next final) :=
  native_scalar_execution_safety typed supported steps

-- Full configuration safety follows the actual call, invocation, label, and frame reductions.
example (steps : ConfigSteps sourceCaller next) :
    NativeCoreConfigurationTyped next [] ∧
      (FlatTerminal next.code ∨ ∃ final, ConfigStep next final) :=
  native_core_configuration_safety sourceCaller_native steps

example (fuel : Nat) :
    NativeCoreConfigurationTyped (runConfiguration fuel sourceCaller).state [] ∧
      (FlatTerminal (runConfiguration fuel sourceCaller).state.code ∨
        ∃ next, ConfigStep (runConfiguration fuel sourceCaller).state next) :=
  runConfiguration_native_core_safe sourceCaller_native fuel

example (typed : NativeCoreConfigurationTyped config results)
    (steps : ConfigSteps config next) (finished : next.code = values vs) :
    vs.map Value.type = results :=
  native_core_configuration_results typed steps finished

#print axioms Wasm.TypeSafety.ControlReduces.preserves_native
#print axioms Wasm.TypeSafety.FrameReduces.preserves_native
#print axioms Wasm.TypeSafety.LocalStep.preserves_native
#print axioms Wasm.TypeSafety.CallStep.preserves_native
#print axioms Wasm.TypeSafety.ExecStep.preserves_native
#print axioms Wasm.TypeSafety.ConfigStep.preserves_native
#print axioms Wasm.TypeSafety.ConfigSteps.preserves_native
#print axioms Wasm.TypeSafety.native_core_configuration_safety
#print axioms Wasm.TypeSafety.native_core_configuration_results
#print axioms Wasm.TypeSafety.runConfiguration_native_core_safe
#print axioms Wasm.TypeSafety.checkSourceCode_native_safety
#print axioms Wasm.TypeSafety.CoreTyping.toNativeCoreTyping
#print axioms Wasm.TypeSafety.RuntimeSeqTyping.toNativeCoreTyping
#print axioms Wasm.TypeSafety.ValidationSeqTyping.toNativeCoreTyping
#print axioms Wasm.TypeSafety.Invokes.native_core_typed
#print axioms Wasm.TypeSafety.FuncTyping.toNativeCoreFunctionTyped
#print axioms Wasm.TypeSafety.checkSourceCode_native_configuration
#print axioms Wasm.TypeSafety.Types.ResultMatches.numeric_chain
#print axioms deadReferenceSelect_native
#print axioms deadReferenceSelect_not_exact
#print axioms sourceStore_native
#print axioms Wasm.TypeSafety.NativeCoreTyping.cons_iff
#print axioms Wasm.TypeSafety.NativeCoreTyping.terminal_values
#print axioms Wasm.TypeSafety.ExecStep.preserves_native_scalar
#print axioms Wasm.TypeSafety.native_core_configuration_progress
#print axioms Wasm.TypeSafety.native_scalar_execution_safety

end Wasm.Tests.NativeSafety
