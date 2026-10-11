import Wasm.VectorStepper
import Wasm.Runtime
import Wasm.Stepper
import Wasm.Calls
import Wasm.Globals
import Wasm.MemoryStepper
import Wasm.BulkMemoryStepper
import Wasm.References
import Wasm.TableStepper
import Wasm.Arrays
import Wasm.Structures
import Wasm.Exceptions

namespace Wasm

/-- Configuration reductions share the store and evaluate in the current frame. -/
inductive ConfigStep : Configuration → Configuration → Prop where
  | vectors (h : VectorStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | arrays (h : ArrayStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | structures (h : StructStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | exceptions (h : ExceptionStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | pure (h : ExecStep frame.module.types code code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store, frame, code'⟩
  | locals (h : LocalStep frame code frame' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store, frame', code'⟩
  | call (h : CallStep store frame code code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store, frame, code'⟩
  | globals (h : GlobalStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | memory (h : MemoryStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | references (h : ReferenceStep store frame code code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store, frame, code'⟩
  | tables (h : TableStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩
  | bulk (h : BulkStep store frame code store' code') :
      ConfigStep ⟨store, frame, code⟩ ⟨store', frame, code'⟩

def stepCoreConfiguration (config : Configuration) : Option Configuration :=
  match stepLocals config.frame config.code with
  | some next => some { config with frame := next.1, code := next.2 }
  | none =>
    match stepCalls config.store config.frame config.code with
    | some code => some { config with code }
    | none =>
      match stepGlobals config.store config.frame config.code with
      | some next => some { config with store := next.1, code := next.2 }
      | none =>
        match stepMemory config.store config.frame config.code with
        | some next => some { config with store := next.1, code := next.2 }
        | none =>
          match stepBulkMemory config.store config.frame config.code with
          | some next => some { config with store := next.1, code := next.2 }
          | none => (step config.frame.module.types config.code).map fun code => { config with code }

theorem stepCoreConfiguration_sound (h : stepCoreConfiguration config = some next) :
    ConfigStep config next := by
  unfold stepCoreConfiguration at h
  cases hl : stepLocals config.frame config.code with
  | some result =>
    simp [hl] at h
    subst next
    exact .locals (stepLocals_sound hl)
  | none =>
    simp only [hl] at h
    cases hc : stepCalls config.store config.frame config.code with
    | some code =>
      simp [hc] at h
      subst next
      exact .call (stepCalls_sound hc)
    | none =>
      simp only [hc] at h
      cases hg : stepGlobals config.store config.frame config.code with
      | some result =>
        simp [hg] at h
        subst next
        exact .globals (stepGlobals_sound hg)
      | none =>
        simp only [hg] at h
        cases hm : stepMemory config.store config.frame config.code with
        | some result =>
          simp [hm] at h
          subst next
          exact .memory (stepMemory_sound hm)
        | none =>
          simp only [hm] at h
          cases hb : stepBulkMemory config.store config.frame config.code with
          | some result =>
            simp [hb] at h
            subst next
            exact .bulk (stepBulkMemory_sound hb)
          | none =>
            simp only [hb] at h
            cases hs : step config.frame.module.types config.code with
            | none => simp [hs] at h
            | some code =>
              simp [hs] at h
              subst next
              exact .pure (step_sound hs)

private def stepWithoutStructures (config : Configuration) : Option Configuration :=
  match stepReferences config.store config.frame config.code with
  | some code => some { config with code }
  | none => match stepTables config.store config.frame config.code with
    | some next => some { config with store := next.1, code := next.2 }
    | none => stepCoreConfiguration config

private theorem stepWithoutStructures_sound (h : stepWithoutStructures config = some next) :
    ConfigStep config next := by
  unfold stepWithoutStructures at h
  cases hr : stepReferences config.store config.frame config.code with
  | some code =>
    simp [hr] at h
    subst next
    exact .references (stepReferences_sound hr)
  | none =>
    simp only [hr] at h
    cases ht : stepTables config.store config.frame config.code with
    | some result =>
      simp [ht] at h
      subst next
      exact .tables (stepTables_sound ht)
    | none =>
      simp only [ht] at h
      exact stepCoreConfiguration_sound h

private def stepWithStructures (config : Configuration) : Option Configuration :=
  match stepStructs config.store config.frame config.code with
  | some next => some {config with store := next.1, code := next.2}
  | none => stepWithoutStructures config

private theorem stepWithStructures_sound
    (h : stepWithStructures config = some next) : ConfigStep config next := by
  unfold stepWithStructures at h
  cases hs : stepStructs config.store config.frame config.code with
  | none => simp only [hs] at h; exact stepWithoutStructures_sound h
  | some result =>
    simp [hs] at h
    subst next
    exact .structures (stepStructs_sound hs)

private def stepOrdinaryConfiguration (config : Configuration) : Option Configuration :=
  match stepArrays config.store config.frame config.code with
  | some next => some {config with store := next.1, code := next.2}
  | none => stepWithStructures config

private theorem stepOrdinaryConfiguration_sound
    (h : stepOrdinaryConfiguration config = some next) : ConfigStep config next := by
  unfold stepOrdinaryConfiguration at h
  cases hs : stepArrays config.store config.frame config.code with
  | none => simp only [hs] at h; exact stepWithStructures_sound h
  | some result =>
    simp [hs] at h
    subst next
    exact .arrays (stepArrays_sound hs)

private def stepWithVectors (config : Configuration) : Option Configuration :=
  match stepVectors config.store config.frame config.code with
  | some next => some {config with store := next.1, code := next.2}
  | none => stepOrdinaryConfiguration config

private theorem stepWithVectors_sound (h : stepWithVectors config = some next) :
    ConfigStep config next := by
  unfold stepWithVectors at h
  cases hs : stepVectors config.store config.frame config.code with
  | none => simp only [hs] at h; exact stepOrdinaryConfiguration_sound h
  | some result =>
    simp [hs] at h
    subst next
    exact .vectors (stepVectors_sound hs)

def stepConfiguration (config : Configuration) : Option Configuration :=
  match stepExceptions config.store config.frame config.code with
  | some next => some {config with store := next.1, code := next.2}
  | none => stepWithVectors config

theorem stepConfiguration_sound (h : stepConfiguration config = some next) :
    ConfigStep config next := by
  unfold stepConfiguration at h
  cases he : stepExceptions config.store config.frame config.code with
  | none => simp only [he] at h; exact stepWithVectors_sound h
  | some result =>
    simp [he] at h
    subst next
    exact .exceptions (stepExceptions_sound he)

inductive ConfigSteps : Configuration → Configuration → Prop where
  | refl : ConfigSteps config config
  | cons : ConfigStep config middle → ConfigSteps middle final → ConfigSteps config final

private def checkedConfigRun : (fuel : Nat) → (config : Configuration) →
    { final : Configuration // ConfigSteps config final }
  | 0, config => ⟨config, .refl⟩
  | fuel + 1, config =>
    match hs : stepConfiguration config with
    | none => ⟨config, .refl⟩
    | some next =>
      let result := checkedConfigRun fuel next
      ⟨result.val, .cons (stepConfiguration_sound hs) result.property⟩

structure ConfigurationRunResult where
  state : Configuration
  status : RunStatus
  deriving BEq, Repr

/-- Fuel bounds semantic steps, including direct-call lowering and activation entry. -/
def runConfiguration (fuel : Nat) (config : Configuration) : ConfigurationRunResult :=
  let final := (checkedConfigRun fuel config).val
  let status := match stepConfiguration final with
    | some _ => RunStatus.exhausted
    | none => match stepOutcome final.frame.module.types final.code with
      | .finished vs => .finished vs
      | .trapped => .trapped
      | .exception address => .exception address
      | .stuck => .stuck
      | .next _ => .exhausted
  ⟨final, status⟩

theorem runConfiguration_sound : ConfigSteps config (runConfiguration fuel config).state :=
  (checkedConfigRun fuel config).property

theorem ConfigStep.functions_preserved (h : ConfigStep config next) :
    next.store.funcs = config.store.funcs := by
  cases h with
  | vectors h => rw [h.resources_preserved.1]
  | arrays h => rw [h.resources_preserved.1]
  | structures h => rw [h.resources_preserved.1]
  | exceptions h => rw [h.resources_preserved.1]
  | pure | locals | call | references => rfl
  | globals h => exact h.functions_preserved
  | memory h => exact h.functions_preserved
  | bulk h => exact h.functions_preserved
  | tables h => exact h.functions_preserved

theorem ConfigStep.module_preserved (h : ConfigStep config next) :
    next.frame.module = config.frame.module := by
  cases h with
  | pure | call | globals | memory | bulk | references | tables | exceptions | structures | arrays | vectors => rfl
  | locals h => exact h.module_preserved

theorem ConfigSteps.functions_preserved (h : ConfigSteps config final) :
    final.store.funcs = config.store.funcs := by
  induction h with
  | refl => rfl
  | cons h _ ih => exact ih.trans h.functions_preserved

theorem ConfigStep.global_count_preserved (h : ConfigStep config next) :
    next.store.globals.length = config.store.globals.length := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.1]
  | arrays h => rw [h.resources_preserved.2.1]
  | structures h => rw [h.resources_preserved.2.1]
  | exceptions h => rw [h.resources_preserved.2.1]
  | pure | locals | call | references => rfl
  | globals h => exact h.length_preserved
  | memory h => rw [h.globals_preserved]
  | bulk h => rw [h.globals_preserved]
  | tables h => rw [h.globals_preserved]

theorem ConfigStep.global_types_preserved (h : ConfigStep config next) :
    next.store.globals.map GlobalInst.type = config.store.globals.map GlobalInst.type := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.1]
  | arrays h => rw [h.resources_preserved.2.1]
  | structures h => rw [h.resources_preserved.2.1]
  | exceptions h => rw [h.resources_preserved.2.1]
  | pure | locals | call | references => rfl
  | globals h => exact h.types_preserved
  | memory h => rw [h.globals_preserved]
  | bulk h => rw [h.globals_preserved]
  | tables h => rw [h.globals_preserved]

theorem ConfigStep.memory_count_preserved (h : ConfigStep config next) :
    next.store.mems.length = config.store.mems.length := by
  cases h with
  | vectors h => exact h.resources_preserved.2.2.1
  | arrays h => rw [h.resources_preserved.2.2.1]
  | structures h => rw [h.resources_preserved.2.2.1]
  | exceptions h => rw [h.resources_preserved.2.2.1]
  | pure | locals | call | references => rfl
  | globals h =>
    induction h with
    | get | set => rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | memory h => exact h.count_preserved
  | bulk h => rw [h.memories_preserved]
  | tables h => rw [h.memories_preserved]

theorem ConfigStep.data_count_preserved (h : ConfigStep config next) :
    next.store.datas.length = config.store.datas.length := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.2.2.1]
  | arrays h => rw [h.resources_preserved.2.2.2.1]
  | structures h => rw [h.resources_preserved.2.2.2.1]
  | exceptions h => rw [h.resources_preserved.2.2.2.1]
  | pure | locals | call | references => rfl
  | globals h =>
    induction h with
    | get | set => rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | memory h =>
    induction h with
    | access _ _ _ hr => cases hr <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | bulk h => exact h.data_count_preserved
  | tables h => exact h.data_count_preserved

theorem ConfigStep.table_count_preserved (h : ConfigStep config next) :
    next.store.tables.length = config.store.tables.length := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.2.2.2.1]
  | arrays h => rw [h.resources_preserved.2.2.2.2.1]
  | structures h => rw [h.resources_preserved.2.2.2.2.1]
  | exceptions h => rw [h.resources_preserved.2.2.2.2.1]
  | pure | locals | call | references => rfl
  | globals h =>
    induction h with
    | get | set => rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | memory h =>
    induction h with
    | access _ _ _ hr => cases hr <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | bulk h =>
    induction h with
    | redex h => cases h <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | tables h => exact h.table_count_preserved

theorem ConfigStep.elem_count_preserved (h : ConfigStep config next) :
    next.store.elems.length = config.store.elems.length := by
  cases h with
  | vectors h => rw [h.resources_preserved.2.2.2.2.2]
  | arrays h => rw [h.resources_preserved.2.2.2.2.2]
  | structures h => rw [h.resources_preserved.2.2.2.2.2]
  | exceptions h => rw [h.resources_preserved.2.2.2.2.2]
  | pure | locals | call | references => rfl
  | globals h =>
    induction h with
    | get | set => rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | memory h =>
    induction h with
    | access _ _ _ hr => cases hr <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | bulk h =>
    induction h with
    | redex h => cases h <;> rfl
    | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | tables h => exact h.elem_count_preserved

theorem runConfiguration_finished
    (h : (runConfiguration fuel config).status = .finished vs) :
    (runConfiguration fuel config).state.code = values vs := by
  simp only [runConfiguration] at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
      exact stepOutcome_finished (by assumption)
    · cases h
    · cases h
    · cases h
    · cases h

theorem runConfiguration_trapped (h : (runConfiguration fuel config).status = .trapped) :
    (runConfiguration fuel config).state.code = [.trap] := by
  simp only [runConfiguration] at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · exact stepOutcome_trapped (by assumption)
    · cases h
    · cases h
    · cases h

end Wasm
