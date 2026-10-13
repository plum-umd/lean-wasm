import Wasm.RuntimeInvariantPreservation
import Wasm.RuntimeExpectedTypesInvariant

/-! Preservation of arbitrary declaration properties of frame modules. -/
namespace Wasm

/-- Every module carried by a nested administrative frame has coherent type projections. -/
def AdminInstr.ModulesSatisfy (property : ModuleInst → Prop) : AdminInstr → Prop
  | .frame _ inner body => property inner.module ∧
      ∀ instruction ∈ body, instruction.ModulesSatisfy property
  | .label _ _ body | .handler _ body | .tailActivation body =>
      ∀ instruction ∈ body, instruction.ModulesSatisfy property
  | _ => True
termination_by instruction => sizeOf instruction

def CodeModulesSatisfy (property : ModuleInst → Prop) (code : List AdminInstr) : Prop :=
  ∀ instruction ∈ code, instruction.ModulesSatisfy property

@[simp] theorem codeModulesSatisfy_append :
    CodeModulesSatisfy property (left ++ right) ↔
      CodeModulesSatisfy property left ∧ CodeModulesSatisfy property right := by
  simp [CodeModulesSatisfy, List.mem_append, or_imp, forall_and]

@[simp] theorem codeModulesSatisfy_values : CodeModulesSatisfy property (values vs) := by
  simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy]

@[simp] theorem codeModulesSatisfy_instructions : CodeModulesSatisfy property (instructions code) := by
  simp [CodeModulesSatisfy, instructions, AdminInstr.ModulesSatisfy]

@[simp] theorem codeModulesSatisfy_singleton :
    CodeModulesSatisfy property [instruction] ↔ instruction.ModulesSatisfy property := by
  simp [CodeModulesSatisfy]

@[simp] theorem codeModulesSatisfy_nil : CodeModulesSatisfy property [] := by
  simp [CodeModulesSatisfy]

@[simp] theorem codeModulesSatisfy_cons : CodeModulesSatisfy property (instruction :: code) ↔
    instruction.ModulesSatisfy property ∧ CodeModulesSatisfy property code := by
  simp [CodeModulesSatisfy]

/-- Local writes change values but preserve every module carried by a frame. -/
theorem LocalStep.modulesSatisfy_preserved (step : LocalStep state code state' code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | get | set | tee => simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy, or_imp, forall_and]
  | context _ ih => simp_all
  | label _ ih | handler _ ih => simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]
  | frame step ih =>
    simp only [codeModulesSatisfy_singleton, AdminInstr.ModulesSatisfy] at modules ⊢
    exact ⟨step.module_preserved ▸ modules.1, ih modules.2⟩

theorem GlobalStep.modulesSatisfy_preserved (step : GlobalStep store state code next code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | get | set => simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]

theorem MemoryStep.modulesSatisfy_preserved (step : MemoryStep store state code next code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | access ha hm hi reduced =>
    cases reduced <;> simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]

theorem BulkStep.modulesSatisfy_preserved (step : BulkStep store state code next code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | redex reduced =>
    cases reduced <;> simp [fillCode, copyCode, initCode,
      CodeModulesSatisfy, instructions, AdminInstr.ModulesSatisfy, or_imp, forall_and]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]

theorem TableStep.modulesSatisfy_preserved (step : TableStep store state code next code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | redex reduced =>
    cases reduced <;> simp [tableFillCode, tableCopyCode, tableInitCode,
      CodeModulesSatisfy, values, instructions, AdminInstr.ModulesSatisfy, or_imp, forall_and]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]

theorem StructStep.modulesSatisfy_preserved (step : StructStep store state code next code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | redex reduced =>
    cases reduced <;> simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]

theorem ArrayStep.modulesSatisfy_preserved (step : ArrayStep store state code next code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | redex reduced =>
    cases reduced <;> simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]

private theorem catch_modules_satisfy (caught : CatchOutcome state address exception catches code) :
    CodeModulesSatisfy property code := by
  induction caught with
  | miss _ _ _ ih => exact ih
  | _ => simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy, or_imp, forall_and]

theorem ExceptionStep.modulesSatisfy_preserved (step : ExceptionStep store state code next code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]
  | caught he caught => exact catch_modules_satisfy caught
  | _ => simp [CodeModulesSatisfy, values, instructions, AdminInstr.ModulesSatisfy, or_imp, forall_and]


/-- Stored function modules remain available when an invocation creates a frame. -/
def Store.FunctionModulesSatisfy (store : Store) (property : ModuleInst → Prop) : Prop :=
  ∀ function ∈ store.funcs, property function.module

private theorem activation_modules_satisfy (invoked : Invokes store function args activation)
    (moduleValid : property function.module) : activation.ModulesSatisfy property := by
  cases invoked
  simpa [AdminInstr.ModulesSatisfy, Frame.initialize, CodeModulesSatisfy] using
    And.intro moduleValid (codeModulesSatisfy_instructions (code := _))

theorem CallStep.modulesSatisfy_preserved (step : CallStep store state code code')
    (functions : store.FunctionModulesSatisfy property) (modules : CodeModulesSatisfy property code) :
    CodeModulesSatisfy property code' := by
  induction step with
  | invoke hf ht invoked | refInvoke hf ht invoked | typedInvoke hf ht he invoked =>
    exact (codeModulesSatisfy_singleton.mpr
      (activation_modules_satisfy invoked (functions _ (List.mem_of_getElem? hf))))
  | returnInvoke hf ht invoked | returnRefInvoke hf ht invoked
  | returnTypedInvoke hf ht he invoked =>
    simpa [AdminInstr.ModulesSatisfy] using (codeModulesSatisfy_singleton.mpr
      (activation_modules_satisfy invoked (functions _ (List.mem_of_getElem? hf))))
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih =>
    simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]
  | tailLabel | tailHandler | tailFrame =>
    simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy, values, List.mem_append,
      or_imp, forall_and]
  | _ => simp [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]

theorem ExecStep.modulesSatisfy_preserved (step : ExecStep types code code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | primitive reduced =>
    cases reduced <;> simp [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]
  | integer reduced =>
    cases reduced <;> simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy]
    rename_i result evaluated
    cases result <;> simp [NumericResult.code, values,
      AdminInstr.ModulesSatisfy]
  | activation reduced =>
    cases reduced <;> simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy]
  | control reduced =>
    cases reduced <;> simp [CodeModulesSatisfy, values, instructions, AdminInstr.ModulesSatisfy, or_imp, forall_and]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih =>
    simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]
  | localFrame step =>
    simp only [codeModulesSatisfy_singleton, AdminInstr.ModulesSatisfy] at modules ⊢
    exact ⟨step.module_preserved ▸ modules.1, step.modulesSatisfy_preserved modules.2⟩
  | trap => simp [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]

private theorem gc_reference_modules_satisfy (evaluated : evalGCReference op args = some code) :
    CodeModulesSatisfy property code := by
  unfold evalGCReference at evaluated
  split at evaluated <;> try simp only [Option.some.injEq] at evaluated
  all_goals try contradiction
  all_goals cases evaluated; simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy]

theorem ReferenceStep.modulesSatisfy_preserved (step : ReferenceStep store state code code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | redex reduced =>
    cases reduced with
    | gc evaluated => exact gc_reference_modules_satisfy evaluated
    | brCastYes | brCastNo =>
      split <;> simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy, or_imp, forall_and]
    | _ => simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih =>
    simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]

set_option maxHeartbeats 2000000 in
private theorem vector_memory_modules_satisfy
    (evaluated : evalVectorMemory store state op args = some (write, code)) :
    CodeModulesSatisfy property code := by
  unfold evalVectorMemory at evaluated
  repeat first
    | contradiction
    | (simp only [pure, Option.some.injEq, Prod.mk.injEq] at evaluated
       rcases evaluated with ⟨_, rfl⟩
       simp [CodeModulesSatisfy, values, AdminInstr.ModulesSatisfy])
    | simp only [Option.pure_def, Option.bind_eq_bind, Option.bind] at evaluated
    | split at evaluated

theorem VectorStep.modulesSatisfy_preserved (step : VectorStep store state code next code')
    (modules : CodeModulesSatisfy property code) : CodeModulesSatisfy property code' := by
  induction step with
  | redex reduced =>
    cases reduced with
    | pure => exact codeModulesSatisfy_values
    | memory isMemory evaluated => exact vector_memory_modules_satisfy evaluated
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih =>
    simp_all [CodeModulesSatisfy, AdminInstr.ModulesSatisfy]


private theorem ready_frames (instruction : AdminInstr)
    (valid : instruction.ModulesSatisfy (fun module =>
      module.RuntimeTypesCoherent ∧ module.RuntimeExpectedTypesValid)) :
    instruction.FramesValid Frame.RuntimeTypesReady := by
  cases instruction
  all_goals simp only [AdminInstr.ModulesSatisfy, AdminInstr.FramesValid] at valid ⊢
  case frame n inner body =>
    exact ⟨valid.1, fun instruction member => ready_frames instruction (valid.2 instruction member)⟩
  case label n continuation body | handler catches body | tailActivation body =>
    exact fun instruction member => ready_frames instruction (valid instruction member)
  all_goals trivial
termination_by sizeOf instruction

/-- Expected declaration value types remain valid across all instruction families. -/
structure Configuration.RuntimeModulesReady (config : Configuration) : Prop where
  active : config.frame.RuntimeTypesReady
  functions : config.store.FunctionModulesSatisfy (fun module =>
    module.RuntimeTypesCoherent ∧ module.RuntimeExpectedTypesValid)
  frames : CodeModulesSatisfy (fun module =>
    module.RuntimeTypesCoherent ∧ module.RuntimeExpectedTypesValid) config.code

/-- The preserved module invariant supplies the state predicate used by GC scanners. -/
theorem Configuration.RuntimeModulesReady.frames_valid {config : Configuration} (valid : config.RuntimeModulesReady) :
    CodeFramesValid Frame.RuntimeTypesReady config.code := by
  intro instruction member
  exact ready_frames instruction (valid.frames instruction member)

theorem ConfigStep.runtimeModulesReady_preserved (step : ConfigStep config next)
    (valid : config.RuntimeModulesReady) : next.RuntimeModulesReady := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Frame.RuntimeTypesReady, step.module_preserved] using valid.active
  · simpa only [Store.FunctionModulesSatisfy, step.functions_preserved] using valid.functions
  · cases step with
    | call h => exact h.modulesSatisfy_preserved valid.functions valid.frames
    | pure h => exact h.modulesSatisfy_preserved valid.frames
    | locals h => exact h.modulesSatisfy_preserved valid.frames
    | globals h => exact h.modulesSatisfy_preserved valid.frames
    | memory h => exact h.modulesSatisfy_preserved valid.frames
    | bulk h => exact h.modulesSatisfy_preserved valid.frames
    | tables h => exact h.modulesSatisfy_preserved valid.frames
    | references h => exact h.modulesSatisfy_preserved valid.frames
    | vectors h => exact h.modulesSatisfy_preserved valid.frames
    | exceptions h => exact h.modulesSatisfy_preserved valid.frames
    | arrays h => exact h.modulesSatisfy_preserved valid.frames
    | structures h => exact h.modulesSatisfy_preserved valid.frames

theorem ConfigSteps.runtimeModulesReady_preserved (steps : ConfigSteps config final)
    (valid : config.RuntimeModulesReady) : final.RuntimeModulesReady := by
  induction steps with
  | refl => exact valid
  | cons step rest ih => exact ih (step.runtimeModulesReady_preserved valid)

#print axioms ConfigSteps.runtimeModulesReady_preserved
end Wasm
