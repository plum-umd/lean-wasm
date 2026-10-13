import Wasm.RuntimeModulePreservation
import Wasm.RuntimeCallCompleteness

/-! Preservation of the declarative expected types used by family completeness. -/
namespace Wasm

private theorem setTable_types {store : Store} {address : TableAddr} {table replacement : TableInst}
    (found : store.table? address = some table)
    (sameType : replacement.type.refType = table.type.refType) :
    (store.setTable address replacement).tables.map (fun table => table.type.refType) =
      store.tables.map (fun table => table.type.refType) := by
  apply List.ext_getElem?
  intro index
  by_cases same : address.index = index
  · subst index
    obtain ⟨bound, entry⟩ := List.getElem?_eq_some_iff.mp found
    simp [Store.setTable, bound, entry, sameType]
  · simp [Store.setTable, List.getElem?_map, List.getElem?_set_ne same]

theorem TableStep.refTypes_preserved (step : TableStep store state code next code') :
    next.tables.map (fun table => table.type.refType) = store.tables.map (fun table => table.type.refType) := by
  induction step with
  | redex reduced =>
    cases reduced with
    | set ha ht hi hv hb => exact setTable_types ht rfl
    | grow ha ht hn hv hg => exact setTable_types ht rfl
    | _ => rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem ConfigStep.table_ref_types_preserved (step : ConfigStep config next) :
    next.store.tables.map (fun table => table.type.refType) = config.store.tables.map (fun table => table.type.refType) := by
  cases step with
  | vectors h => rw [h.resources_preserved.2.2.2.2.1]
  | arrays h => rw [h.resources_preserved.2.2.2.2.1]
  | structures h => rw [h.resources_preserved.2.2.2.2.1]
  | exceptions h => rw [h.resources_preserved.2.2.2.2.1]
  | pure | locals | call | references => rfl
  | globals h =>
    induction h <;> simp_all [Store.setGlobal]
  | memory h =>
    induction h with
    | access ha hm hi reduced =>
      cases reduced <;> simp [Store.applyMemory, Store.setMemory]
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | bulk h =>
    induction h with
    | redex reduced => cases reduced <;> simp [Store.dropData]
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | tables h => exact h.refTypes_preserved

theorem ConfigStep.globalTypesValid_preserved (step : ConfigStep config next)
    (valid : config.store.GlobalTypesValid) : next.store.GlobalTypesValid := by
  intro global member
  have typeMember : global.type ∈ next.store.globals.map GlobalInst.type :=
    List.mem_map.mpr ⟨global, member, rfl⟩
  rw [step.global_types_preserved] at typeMember
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp typeMember
  simpa only [same] using valid old oldMember

theorem ConfigStep.tableTypesValid_preserved (step : ConfigStep config next)
    (valid : config.store.TableTypesValid) : next.store.TableTypesValid := by
  intro table member
  have typeMember : table.type.refType ∈ next.store.tables.map (fun table => table.type.refType) :=
    List.mem_map.mpr ⟨table, member, rfl⟩
  rw [step.table_ref_types_preserved] at typeMember
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp typeMember
  simpa only [same] using valid old oldMember

theorem ConfigStep.tags_preserved (step : ConfigStep config next) :
    next.store.tags = config.store.tags := by
  cases step with
  | pure | locals | call | references => rfl
  | exceptions h => induction h <;> simp_all
  | structures h =>
    induction h with
    | redex h => cases h <;> simp [Store.writeStruct]
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | arrays h =>
    induction h with
    | redex h => cases h <;> simp [Store.writeArray]
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | vectors h =>
    induction h with
    | redex h =>
      cases h with
      | pure => rfl
      | memory => simp [vectorMemoryStore, Store.setMemory]; split <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | globals h => induction h <;> simp_all [Store.setGlobal]
  | memory h =>
    induction h with
    | access _ _ _ h => cases h <;> simp [Store.applyMemory, Store.setMemory]
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | bulk h =>
    induction h with
    | redex h => cases h <;> simp [Store.dropData]
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | tables h =>
    induction h with
    | redex h => cases h <;> simp [Store.setTable, Store.dropElem]
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem ConfigStep.tagParametersValid_preserved (step : ConfigStep config next)
    (valid : config.store.TagParametersValid) : next.store.TagParametersValid := by
  simpa only [Store.TagParametersValid, step.tags_preserved] using valid

theorem ConfigStep.functionParametersValid_preserved (step : ConfigStep config next)
    (valid : config.store.FunctionParametersValid) : next.store.FunctionParametersValid := by
  simpa only [Store.FunctionParametersValid, step.functions_preserved] using valid

/-- Runtime identities, expected global/table types, and all active or invocable frame modules. -/
structure Configuration.RuntimeCompletenessInvariant (config : Configuration) : Prop where
  declarations : config.RuntimeDeclarationsValid
  modules : config.RuntimeModulesReady
  globals : config.store.GlobalTypesValid
  tables : config.store.TableTypesValid
  tags : config.store.TagParametersValid
  parameters : config.store.FunctionParametersValid

theorem ConfigStep.runtimeCompletenessInvariant_preserved (step : ConfigStep config next)
    (valid : config.RuntimeCompletenessInvariant) : next.RuntimeCompletenessInvariant :=
  ⟨step.runtimeDeclarations_preserved valid.declarations,
    step.runtimeModulesReady_preserved valid.modules,
    step.globalTypesValid_preserved valid.globals, step.tableTypesValid_preserved valid.tables,
    step.tagParametersValid_preserved valid.tags,
    step.functionParametersValid_preserved valid.parameters⟩

theorem ConfigSteps.runtimeCompletenessInvariant_preserved (steps : ConfigSteps config final)
    (valid : config.RuntimeCompletenessInvariant) : final.RuntimeCompletenessInvariant := by
  induction steps with
  | refl => exact valid
  | cons step rest ih => exact ih (step.runtimeCompletenessInvariant_preserved valid)

#print axioms ConfigSteps.runtimeCompletenessInvariant_preserved
end Wasm
