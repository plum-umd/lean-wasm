import Wasm.Configuration
import Wasm.RuntimeTypeInvariant

/-! Preservation of runtime type identities and module declarations during execution. -/
namespace Wasm

/-- Coherent modules also validate identities obtained through the runtime projection. -/
theorem ModuleInst.RuntimeTypesCoherent.defined_valid {module : ModuleInst}
    {index : Nat} {type : Types.DefinedType} (coherent : module.RuntimeTypesCoherent)
    (found : module.definedTypes[index]? = some type) : type.RuntimeValid := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  cases static : module.types[index]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp static
    have length := coherent.length
    omega
  | some source => exact (coherent.lookup static found).1

/-- Every module carried by a nested administrative frame has coherent type projections. -/
def AdminInstr.ModulesCoherent : AdminInstr → Prop
  | .frame _ inner body => inner.module.RuntimeTypesCoherent ∧
      ∀ instruction ∈ body, instruction.ModulesCoherent
  | .label _ _ body | .handler _ body | .tailActivation body =>
      ∀ instruction ∈ body, instruction.ModulesCoherent
  | _ => True
termination_by instruction => sizeOf instruction

def CodeModulesCoherent (code : List AdminInstr) : Prop :=
  ∀ instruction ∈ code, instruction.ModulesCoherent

@[simp] theorem codeModulesCoherent_append :
    CodeModulesCoherent (left ++ right) ↔
      CodeModulesCoherent left ∧ CodeModulesCoherent right := by
  simp [CodeModulesCoherent, List.mem_append, or_imp, forall_and]

@[simp] theorem codeModulesCoherent_values : CodeModulesCoherent (values vs) := by
  simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent]

@[simp] theorem codeModulesCoherent_instructions : CodeModulesCoherent (instructions code) := by
  simp [CodeModulesCoherent, instructions, AdminInstr.ModulesCoherent]

@[simp] theorem codeModulesCoherent_singleton :
    CodeModulesCoherent [instruction] ↔ instruction.ModulesCoherent := by
  simp [CodeModulesCoherent]

private theorem member_modify {P : α → Prop} {xs : List α} {f : α → α}
    (valid : ∀ x ∈ xs, P x) (preserve : ∀ x, P x → P (f x)) :
    ∀ x ∈ xs.modify index f, P x := by
  induction xs generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.modify_zero_cons, List.mem_cons]
      intro x member
      rcases member with rfl | member
      · exact preserve head (valid head (by simp))
      · exact valid x (by simp [member])
    | succ index =>
      simp only [List.modify_succ_cons, List.mem_cons]
      intro x member
      rcases member with rfl | member
      · exact valid x (by simp)
      · exact ih (fun x member => valid x (by simp [member])) x member

/-- Changes outside the four type-bearing store components preserve their validity. -/
theorem Store.RuntimeTypesValid.transfer {store next : Store} (valid : store.RuntimeTypesValid)
    (functions : next.funcs = store.funcs) (structures : next.structs = store.structs)
    (arrays : next.arrays = store.arrays) (tags : next.tags = store.tags) :
    next.RuntimeTypesValid := by
  constructor
  · simpa [functions] using valid.functions
  · simpa [structures] using valid.structures
  · simpa [arrays] using valid.arrays
  · simpa [tags] using valid.tags

private theorem allocate_struct_valid {store : Store} {object : StructInst} (valid : store.RuntimeTypesValid)
    (objectValid : object.RuntimeTypeValid) :
    ({store with structs := store.structs ++ [object]} : Store).RuntimeTypesValid := by
  constructor
  · exact valid.functions
  · intro object member
    rcases List.mem_append.mp member with member | member
    · exact valid.structures object member
    · rcases List.mem_singleton.mp member with rfl
      exact objectValid
  · exact valid.arrays
  · exact valid.tags

private theorem allocate_array_valid {store : Store} {object : ArrayInst} (valid : store.RuntimeTypesValid)
    (objectValid : object.RuntimeTypeValid) :
    ({store with arrays := store.arrays ++ [object]} : Store).RuntimeTypesValid := by
  constructor
  · exact valid.functions
  · exact valid.structures
  · intro object member
    rcases List.mem_append.mp member with member | member
    · exact valid.arrays object member
    · rcases List.mem_singleton.mp member with rfl
      exact objectValid
  · exact valid.tags

private theorem write_struct_valid {store : Store} {address : StructAddr}
    {object replacement : StructInst} (valid : store.RuntimeTypesValid)
    (lookup : store.struct? address = some object) (same : replacement.type = object.type) :
    (store.writeStruct address replacement).RuntimeTypesValid := by
  constructor
  · exact valid.functions
  · apply member_modify valid.structures
    intro previous previousValid
    simpa only [StructInst.RuntimeTypeValid, same] using
      valid.structures object (List.mem_of_getElem? lookup)
  · exact valid.arrays
  · exact valid.tags

private theorem write_array_valid {store : Store} {address : ArrayAddr}
    {object replacement : ArrayInst} (valid : store.RuntimeTypesValid)
    (lookup : store.array? address = some object) (same : replacement.type = object.type) :
    (store.writeArray address replacement).RuntimeTypesValid := by
  constructor
  · exact valid.functions
  · exact valid.structures
  · apply member_modify valid.arrays
    intro previous previousValid
    simpa only [ArrayInst.RuntimeTypeValid, same] using
      valid.arrays object (List.mem_of_getElem? lookup)
  · exact valid.tags

/-- Structure allocation validates the declared type; field updates preserve its identity. -/
theorem StructStep.runtimeTypes_preserved
    (step : StructStep store state code next code') (valid : store.RuntimeTypesValid)
    (moduleValid : state.module.RuntimeTypesCoherent) (modules : CodeModulesCoherent code) :
    next.RuntimeTypesValid := by
  induction step with
  | redex reduced =>
    cases reduced with
    | new ht hf | newDefault ht hf =>
      exact allocate_struct_valid valid ⟨moduleValid.defined_valid ht, ⟨_, hf⟩⟩
    | getNull | get | setNull => exact valid
    | set ht hf hs hm ho hr hb hv ha hp => exact write_struct_valid valid ho rfl
  | context _ ih => exact ih moduleValid ((codeModulesCoherent_append.mp
      (codeModulesCoherent_append.mp modules).1).2)
  | label _ ih | handler _ ih =>
    exact ih moduleValid (by simpa [AdminInstr.ModulesCoherent] using modules)
  | frame _ ih =>
    have inner := codeModulesCoherent_singleton.mp modules
    simp only [AdminInstr.ModulesCoherent] at inner
    exact ih inner.1 inner.2

/-- Array allocation and all array writes preserve valid runtime type identities. -/
theorem ArrayStep.runtimeTypes_preserved
    (step : ArrayStep store state code next code') (valid : store.RuntimeTypesValid)
    (moduleValid : state.module.RuntimeTypesCoherent) (modules : CodeModulesCoherent code) :
    next.RuntimeTypesValid := by
  induction step with
  | redex reduced =>
    cases reduced with
    | new ht hf | newDefault ht hf | newFixed ht hf | newData ht hf | newElem ht hf =>
      exact allocate_array_valid valid ⟨moduleValid.defined_valid ht, ⟨_, hf⟩⟩
    | set access | fill access | initData access | initElem access =>
      cases access with
      | mk type ht hf ho hr => exact write_array_valid valid ho rfl
    | copy destination source =>
      cases destination with
      | mk type ht hf ho hr => exact write_array_valid valid ho rfl
    | _ => exact valid
  | context _ ih => exact ih moduleValid ((codeModulesCoherent_append.mp
      (codeModulesCoherent_append.mp modules).1).2)
  | label _ ih | handler _ ih =>
    exact ih moduleValid (by simpa [AdminInstr.ModulesCoherent] using modules)
  | frame _ ih =>
    have inner := codeModulesCoherent_singleton.mp modules
    simp only [AdminInstr.ModulesCoherent] at inner
    exact ih inner.1 inner.2

theorem GlobalStep.runtimeTypes_preserved (step : GlobalStep store state code next code')
    (valid : store.RuntimeTypesValid) : next.RuntimeTypesValid := by
  induction step with
  | get | set => exact valid.transfer rfl rfl rfl rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => first | exact ih valid | exact ih

theorem MemoryStep.runtimeTypes_preserved (step : MemoryStep store state code next code')
    (valid : store.RuntimeTypesValid) : next.RuntimeTypesValid := by
  induction step with
  | access ha hm hi reduced => cases reduced <;> exact valid.transfer rfl rfl rfl rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => first | exact ih valid | exact ih

theorem BulkStep.runtimeTypes_preserved (step : BulkStep store state code next code')
    (valid : store.RuntimeTypesValid) : next.RuntimeTypesValid := by
  induction step with
  | redex reduced => cases reduced <;> exact valid.transfer rfl rfl rfl rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => first | exact ih valid | exact ih

theorem TableStep.runtimeTypes_preserved (step : TableStep store state code next code')
    (valid : store.RuntimeTypesValid) : next.RuntimeTypesValid := by
  induction step with
  | redex reduced => cases reduced <;> exact valid.transfer rfl rfl rfl rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => first | exact ih valid | exact ih

private theorem vectorMemoryStore_types (valid : store.RuntimeTypesValid)
    (write : Option (MemAddr × MemoryInst)) : (vectorMemoryStore store write).RuntimeTypesValid := by
  cases write <;> exact valid.transfer rfl rfl rfl rfl

theorem VectorStep.runtimeTypes_preserved (step : VectorStep store state code next code')
    (valid : store.RuntimeTypesValid) : next.RuntimeTypesValid := by
  induction step with
  | redex reduced =>
    cases reduced with
    | pure => exact valid
    | memory => exact vectorMemoryStore_types valid _
  | context _ ih | label _ ih | handler _ ih | frame _ ih => first | exact ih valid | exact ih

theorem ExceptionStep.runtimeTypes_preserved (step : ExceptionStep store state code next code')
    (valid : store.RuntimeTypesValid) : next.RuntimeTypesValid := by
  induction step with
  | context _ ih | label _ ih | handler _ ih | frame _ ih => first | exact ih valid | exact ih
  | _ => exact valid.transfer rfl rfl rfl rfl

/-- Every instruction family preserves the store's type-facing invariant. -/
theorem ConfigStep.runtimeTypes_preserved (step : ConfigStep config next)
    (valid : config.store.RuntimeTypesValid)
    (moduleValid : config.frame.module.RuntimeTypesCoherent)
    (modules : CodeModulesCoherent config.code) : next.store.RuntimeTypesValid := by
  cases step with
  | pure | locals | call | references => exact valid
  | globals h => exact h.runtimeTypes_preserved valid
  | memory h => exact h.runtimeTypes_preserved valid
  | bulk h => exact h.runtimeTypes_preserved valid
  | tables h => exact h.runtimeTypes_preserved valid
  | vectors h => exact h.runtimeTypes_preserved valid
  | exceptions h => exact h.runtimeTypes_preserved valid
  | arrays h => exact h.runtimeTypes_preserved valid moduleValid modules
  | structures h => exact h.runtimeTypes_preserved valid moduleValid modules

@[simp] theorem codeModulesCoherent_nil : CodeModulesCoherent [] := by
  simp [CodeModulesCoherent]

@[simp] theorem codeModulesCoherent_cons : CodeModulesCoherent (instruction :: code) ↔
    instruction.ModulesCoherent ∧ CodeModulesCoherent code := by
  simp [CodeModulesCoherent]

/-- Local writes change values but preserve every module carried by a frame. -/
theorem LocalStep.modules_preserved (step : LocalStep state code state' code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | get | set | tee => simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent, or_imp, forall_and]
  | context _ ih => simp_all
  | label _ ih | handler _ ih => simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]
  | frame step ih =>
    simp only [codeModulesCoherent_singleton, AdminInstr.ModulesCoherent] at modules ⊢
    exact ⟨step.module_preserved ▸ modules.1, ih modules.2⟩

theorem GlobalStep.modules_preserved (step : GlobalStep store state code next code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | get | set => simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]

theorem MemoryStep.modules_preserved (step : MemoryStep store state code next code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | access ha hm hi reduced =>
    cases reduced <;> simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]

theorem BulkStep.modules_preserved (step : BulkStep store state code next code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | redex reduced =>
    cases reduced <;> simp [fillCode, copyCode, initCode,
      CodeModulesCoherent, instructions, AdminInstr.ModulesCoherent, or_imp, forall_and]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]

theorem TableStep.modules_preserved (step : TableStep store state code next code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | redex reduced =>
    cases reduced <;> simp [tableFillCode, tableCopyCode, tableInitCode,
      CodeModulesCoherent, values, instructions, AdminInstr.ModulesCoherent, or_imp, forall_and]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]

theorem StructStep.modules_preserved (step : StructStep store state code next code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | redex reduced =>
    cases reduced <;> simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]

theorem ArrayStep.modules_preserved (step : ArrayStep store state code next code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | redex reduced =>
    cases reduced <;> simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]

private theorem catch_modules (caught : CatchOutcome state address exception catches code) :
    CodeModulesCoherent code := by
  induction caught with
  | miss _ _ _ ih => exact ih
  | _ => simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent, or_imp, forall_and]

theorem ExceptionStep.modules_preserved (step : ExceptionStep store state code next code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih => simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]
  | caught he caught => exact catch_modules caught
  | _ => simp [CodeModulesCoherent, values, instructions, AdminInstr.ModulesCoherent, or_imp, forall_and]


/-- Stored function modules remain available when an invocation creates a frame. -/
def Store.FunctionModulesCoherent (store : Store) : Prop :=
  ∀ function ∈ store.funcs, function.module.RuntimeTypesCoherent

private theorem activation_modules (invoked : Invokes store function args activation)
    (moduleValid : function.module.RuntimeTypesCoherent) : activation.ModulesCoherent := by
  cases invoked
  simpa [AdminInstr.ModulesCoherent, Frame.initialize, CodeModulesCoherent] using
    And.intro moduleValid (codeModulesCoherent_instructions (code := _))

theorem CallStep.modules_preserved (step : CallStep store state code code')
    (functions : store.FunctionModulesCoherent) (modules : CodeModulesCoherent code) :
    CodeModulesCoherent code' := by
  induction step with
  | invoke hf ht invoked | refInvoke hf ht invoked | typedInvoke hf ht he invoked =>
    exact (codeModulesCoherent_singleton.mpr
      (activation_modules invoked (functions _ (List.mem_of_getElem? hf))))
  | returnInvoke hf ht invoked | returnRefInvoke hf ht invoked
  | returnTypedInvoke hf ht he invoked =>
    simpa [AdminInstr.ModulesCoherent] using (codeModulesCoherent_singleton.mpr
      (activation_modules invoked (functions _ (List.mem_of_getElem? hf))))
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih =>
    simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]
  | tailLabel | tailHandler | tailFrame =>
    simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent, values, List.mem_append,
      or_imp, forall_and]
  | _ => simp [CodeModulesCoherent, AdminInstr.ModulesCoherent]

theorem ExecStep.modules_preserved (step : ExecStep types code code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | primitive reduced =>
    cases reduced <;> simp [CodeModulesCoherent, AdminInstr.ModulesCoherent]
  | integer reduced =>
    cases reduced <;> simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent]
    rename_i result evaluated
    cases result <;> simp [NumericResult.code, values,
      AdminInstr.ModulesCoherent]
  | activation reduced =>
    cases reduced <;> simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent]
  | control reduced =>
    cases reduced <;> simp [CodeModulesCoherent, values, instructions, AdminInstr.ModulesCoherent, or_imp, forall_and]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih =>
    simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]
  | localFrame step =>
    simp only [codeModulesCoherent_singleton, AdminInstr.ModulesCoherent] at modules ⊢
    exact ⟨step.module_preserved ▸ modules.1, step.modules_preserved modules.2⟩
  | trap => simp [CodeModulesCoherent, AdminInstr.ModulesCoherent]

private theorem gc_reference_modules (evaluated : evalGCReference op args = some code) :
    CodeModulesCoherent code := by
  unfold evalGCReference at evaluated
  split at evaluated <;> try simp only [Option.some.injEq] at evaluated
  all_goals try contradiction
  all_goals cases evaluated; simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent]

theorem ReferenceStep.modules_preserved (step : ReferenceStep store state code code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | redex reduced =>
    cases reduced with
    | gc evaluated => exact gc_reference_modules evaluated
    | brCastYes | brCastNo =>
      split <;> simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent, or_imp, forall_and]
    | _ => simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent]
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih =>
    simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]

set_option maxHeartbeats 2000000 in
private theorem vector_memory_modules
    (evaluated : evalVectorMemory store state op args = some (write, code)) :
    CodeModulesCoherent code := by
  unfold evalVectorMemory at evaluated
  repeat first
    | contradiction
    | (simp only [pure, Option.some.injEq, Prod.mk.injEq] at evaluated
       rcases evaluated with ⟨_, rfl⟩
       simp [CodeModulesCoherent, values, AdminInstr.ModulesCoherent])
    | simp only [Option.pure_def, Option.bind_eq_bind, Option.bind] at evaluated
    | split at evaluated

theorem VectorStep.modules_preserved (step : VectorStep store state code next code')
    (modules : CodeModulesCoherent code) : CodeModulesCoherent code' := by
  induction step with
  | redex reduced =>
    cases reduced with
    | pure => exact codeModulesCoherent_values
    | memory isMemory evaluated => exact vector_memory_modules evaluated
  | context _ ih => simp_all
  | label _ ih | handler _ ih | frame _ ih =>
    simp_all [CodeModulesCoherent, AdminInstr.ModulesCoherent]

/-- The declaration invariant used by preservation is stated entirely declaratively. -/
structure Configuration.RuntimeDeclarationsValid (config : Configuration) : Prop where
  store : config.store.RuntimeTypesValid
  functions : config.store.FunctionModulesCoherent
  module : config.frame.module.RuntimeTypesCoherent
  frames : CodeModulesCoherent config.code

/-- Every semantic successor preserves valid runtime identities and coherent frame modules. -/
theorem ConfigStep.runtimeDeclarations_preserved (step : ConfigStep config next)
    (valid : config.RuntimeDeclarationsValid) : next.RuntimeDeclarationsValid := by
  refine ⟨step.runtimeTypes_preserved valid.store valid.module valid.frames, ?_,
    step.module_preserved ▸ valid.module, ?_⟩
  · simpa only [Store.FunctionModulesCoherent, step.functions_preserved] using valid.functions
  · cases step with
    | pure h => exact h.modules_preserved valid.frames
    | locals h => exact h.modules_preserved valid.frames
    | call h => exact h.modules_preserved valid.functions valid.frames
    | globals h => exact h.modules_preserved valid.frames
    | memory h => exact h.modules_preserved valid.frames
    | bulk h => exact h.modules_preserved valid.frames
    | tables h => exact h.modules_preserved valid.frames
    | references h => exact h.modules_preserved valid.frames
    | vectors h => exact h.modules_preserved valid.frames
    | exceptions h => exact h.modules_preserved valid.frames
    | arrays h => exact h.modules_preserved valid.frames
    | structures h => exact h.modules_preserved valid.frames

/-- Declaration validity is preserved by arbitrary finite executions. -/
theorem ConfigSteps.runtimeDeclarations_preserved (steps : ConfigSteps config final)
    (valid : config.RuntimeDeclarationsValid) : final.RuntimeDeclarationsValid := by
  induction steps with
  | refl => exact valid
  | cons step rest ih => exact ih (step.runtimeDeclarations_preserved valid)

#print axioms ConfigStep.runtimeDeclarations_preserved
#print axioms ConfigSteps.runtimeDeclarations_preserved

#print axioms ConfigStep.runtimeTypes_preserved

end Wasm
