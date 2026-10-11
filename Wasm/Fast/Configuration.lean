import Wasm.Fast.VectorStepper
import Wasm.Fast.Runtime
import Wasm.Stepper
import Wasm.Fast.Calls
import Wasm.Fast.Globals
import Wasm.Fast.MemoryStepper
import Wasm.Fast.BulkMemoryStepper
import Wasm.Fast.References
import Wasm.Fast.TableStepper
import Wasm.Fast.Arrays
import Wasm.Fast.Structures
import Wasm.Fast.Exceptions

namespace Wasm.Fast

structure Configuration where
  store : Store
  frame : Frame
  code : List AdminInstr
  deriving BEq, Repr

def Configuration.toSpec (c : Configuration) : Wasm.Configuration :=
  ⟨c.store.toSpec, c.frame, c.code⟩

def Configuration.ofSpec (c : Wasm.Configuration) : Configuration :=
  ⟨Store.ofSpec c.store, c.frame, c.code⟩

@[simp] theorem Configuration.toSpec_ofSpec (c : Wasm.Configuration) :
    (Configuration.ofSpec c).toSpec = c := by
  cases c; simp [Configuration.ofSpec, Configuration.toSpec]


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
          | none => (step config.frame.module.types config.code).map fun code =>
            { config with code }

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
  match planStructs config.store config.frame config.code with
  | some next => some {config with store := next.1.apply config.store, code := next.2}
  | none => stepWithoutStructures config

private theorem stepWithStructures_sound
    (h : stepWithStructures config = some next) : ConfigStep config next := by
  unfold stepWithStructures at h
  cases hs : planStructs config.store config.frame config.code with
  | none => simp only [hs] at h; exact stepWithoutStructures_sound h
  | some result =>
    simp [hs] at h
    subst next
    exact .structures (planStructs_sound hs)

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

/-- Delay heap mutation until the runner has released its fallback configuration. -/
private inductive RunChange where
  | ready (next : Configuration)
  | structures (change : StructChange) (code : List AdminInstr)

private def RunChange.apply (change : RunChange) (config : Configuration) : Configuration :=
  match change with
  | .ready next => next
  | .structures change code => {config with store := change.apply config.store, code}

private def planRunStep (config : Configuration) : Option RunChange :=
  match stepExceptions config.store config.frame config.code with
  | some next => some (.ready {config with store := next.1, code := next.2})
  | none => match stepVectors config.store config.frame config.code with
    | some next => some (.ready {config with store := next.1, code := next.2})
    | none => match stepArrays config.store config.frame config.code with
      | some next => some (.ready {config with store := next.1, code := next.2})
      | none => match planStructs config.store config.frame config.code with
        | some next => some (.structures next.1 next.2)
        | none => (stepWithoutStructures config).map RunChange.ready

private theorem planRunStep_agrees (config : Configuration) :
    (planRunStep config).map (fun change => change.apply config) =
      stepConfiguration config := by
  cases he : stepExceptions config.store config.frame config.code <;>
    cases hv : stepVectors config.store config.frame config.code <;>
    cases ha : stepArrays config.store config.frame config.code <;>
    cases hs : planStructs config.store config.frame config.code <;>
    simp [planRunStep, stepConfiguration, stepWithVectors, stepOrdinaryConfiguration,
      stepWithStructures, RunChange.apply, he, hv, ha, hs, Option.map_map, Function.comp_def]

private theorem planRunStep_sound (h : planRunStep config = some change) :
    ConfigStep config (change.apply config) := by
  apply stepConfiguration_sound
  rw [← planRunStep_agrees, h]
  rfl

private def checkedConfigRun : (fuel : Nat) → (config : Configuration) →
    { final : Configuration // ConfigSteps config final }
  | 0, config => ⟨config, .refl⟩
  | fuel + 1, config =>
    match hs : planRunStep config with
    | none => ⟨config, .refl⟩
    | some change =>
      let result := checkedConfigRun fuel (change.apply config)
      ⟨result.val, .cons (planRunStep_sound hs) result.property⟩

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

end Wasm.Fast
