import Wasm.Configuration
import Wasm.RuntimeExecutionInvariant
import Wasm.AbstractMatchingCompleteness
import Wasm.DeclaredMatchingCompleteness
import Wasm.RuntimeMatchingCompleteness

/-!
Execution progress completeness asks for some permitted successor, rather than every successor.
Implementation limits are separate outcomes and do not add reduction rules to `ConfigStep`.
The full theorem needs an independently stated runtime domain. Eleven ordinary families now have
scanner completeness proofs; locals, memory, and bulk memory require no type validity hypotheses.
-/

namespace Wasm

/-- On the given domain, a semantic successor implies a successful executor step. -/
def ProgressCompleteOn (domain : Configuration → Prop) : Prop :=
  ∀ config, domain config → (∃ next, ConfigStep config next) →
    ∃ chosen, stepConfiguration config = some chosen

/-- Resource-aware progress permits an explicit implementation limit when semantics can step. -/
def ResourceProgressCompleteOn (domain : Configuration → Prop) : Prop :=
  ∀ config, domain config → (∃ next, ConfigStep config next) →
    (∃ chosen, stepConfigurationOutcome config = .next chosen) ∨
      (∃ limit, stepConfigurationOutcome config = .stopped (.resourceLimit limit))

theorem ProgressCompleteOn.resource (complete : ProgressCompleteOn domain) :
    ResourceProgressCompleteOn domain := by
  intro config valid reducible
  obtain ⟨chosen, success⟩ := complete config valid reducible
  exact .inl ⟨chosen, by simp [stepConfigurationOutcome, success]⟩

/-- The configuration has a local-variable reduction at its active evaluation position. -/
def LocalReducible (config : Configuration) : Prop :=
  ∃ frame' code', LocalStep config.frame config.code frame' code'

/-- This family is progress-complete even when another family wins the executor's priority. -/
theorem locals_progress_complete : ProgressCompleteOn LocalReducible := by
  intro config localStep _
  obtain ⟨frame', code', reduced⟩ := localStep
  exact stepConfiguration_complete_locals reduced

theorem locals_resource_progress_complete : ResourceProgressCompleteOn LocalReducible :=
  locals_progress_complete.resource

/-- A semantically reducible family among those with completed scanner proofs. -/
inductive SupportedFamilyStep (config : Configuration) : Prop where
  | pure : ExecStep config.frame.module.types config.code code' → SupportedFamilyStep config
  | locals : LocalStep config.frame config.code frame' code' → SupportedFamilyStep config
  | globals : GlobalStep config.store config.frame config.code next code' → SupportedFamilyStep config
  | memory : MemoryStep config.store config.frame config.code next code' → SupportedFamilyStep config
  | bulk : BulkStep config.store config.frame config.code next code' → SupportedFamilyStep config
  | tables : TableStep config.store config.frame config.code next code' → SupportedFamilyStep config
  | references : ReferenceStep config.store config.frame config.code code' → SupportedFamilyStep config
  | vectors : VectorStep config.store config.frame config.code next code' → SupportedFamilyStep config
  | calls : CallStep config.store config.frame config.code code' → SupportedFamilyStep config
  | exceptions : ExceptionStep config.store config.frame config.code next code' → SupportedFamilyStep config
  | structures : StructStep config.store config.frame config.code next code' → SupportedFamilyStep config

/-- Declarative hypotheses for the completed families, including nested frames. -/
structure Configuration.SupportedFamilyDomain (config : Configuration) : Prop where
  store : config.store.RuntimeTypesValid
  globals : config.store.GlobalTypesValid
  tables : config.store.TableTypesValid
  tags : config.store.TagParametersValid
  parameters : config.store.FunctionParametersValid
  calls : CodeScopedValid CallExpectedTypesValid config.frame config.code
  active : config.frame.RuntimeTypesReady
  frames : CodeFramesValid Frame.RuntimeTypesReady config.code
  references : CodeScopedValid ReferenceExpectedTypesValid config.frame config.code

theorem Configuration.SupportedFamilyDomain.of_invariant {config : Configuration}
    (valid : config.RuntimeCompletenessInvariant)
    (references : CodeScopedValid ReferenceExpectedTypesValid config.frame config.code)
    (calls : CodeScopedValid CallExpectedTypesValid config.frame config.code) :
    config.SupportedFamilyDomain :=
  ⟨valid.declarations.store, valid.globals, valid.tables, valid.tags, valid.parameters, calls,
    valid.modules.active, valid.modules.frames_valid, references⟩

/-- Family priority cannot hide progress established by any of the completed scanners. -/
theorem stepConfiguration_complete_supported (valid : config.SupportedFamilyDomain)
    (reduced : SupportedFamilyStep config) : ∃ next, stepConfiguration config = some next := by
  cases result : stepConfiguration config with
  | some next => exact ⟨next, rfl⟩
  | none =>
    obtain ⟨exceptions, vectors, arrays, structures, references, tables, locals, calls,
      globals, memory, bulk, pure⟩ := stepConfiguration_none_iff.mp result
    cases reduced with
    | pure h =>
      have success := step_complete h
      simp [pure] at success
    | locals h => rw [stepLocals_complete h] at locals; contradiction
    | globals h => rw [stepGlobals_complete h valid.store valid.globals] at globals; contradiction
    | memory h => have success := stepMemory_complete h; simp [memory] at success
    | bulk h => have success := stepBulkMemory_complete h; simp [bulk] at success
    | tables h => have success := stepTables_complete h valid.store valid.tables; simp [tables] at success
    | references h =>
      have success := stepReferences_complete h valid.store valid.references
      simp [references] at success
    | vectors h =>
      have success := stepVectors_complete h
      simp [vectors] at success
    | calls h =>
      have success := stepCalls_complete h valid.store valid.parameters valid.calls
      simp [calls] at success
    | exceptions h =>
      have success := stepExceptions_complete h valid.store valid.tags
      simp [exceptions] at success
    | structures h =>
      have success := stepStructs_complete h valid.store valid.active valid.frames
      simp [structures] at success

theorem supported_progress_complete : ProgressCompleteOn (fun config =>
    config.SupportedFamilyDomain ∧ SupportedFamilyStep config) := by
  intro config valid _
  exact stepConfiguration_complete_supported valid.1 valid.2

theorem supported_resource_progress_complete : ResourceProgressCompleteOn (fun config =>
    config.SupportedFamilyDomain ∧ SupportedFamilyStep config) := supported_progress_complete.resource

/-- Completed ordinary families, together with resource-aware array execution. -/
inductive ResourceSupportedFamilyStep (config : Configuration) : Prop where
  | ordinary : SupportedFamilyStep config → ResourceSupportedFamilyStep config
  | arrays : ArrayStep config.store config.frame config.code next code' →
      ResourceSupportedFamilyStep config

theorem stepConfiguration_resource_complete_supported (valid : config.SupportedFamilyDomain)
    (reduced : ResourceSupportedFamilyStep config) :
    (∃ chosen, stepConfigurationOutcome config = .next chosen) ∨
      (∃ limit, stepConfigurationOutcome config = .stopped (.resourceLimit limit)) := by
  cases reduced with
  | ordinary reduced =>
    obtain ⟨chosen, success⟩ := stepConfiguration_complete_supported valid reduced
    exact .inl ⟨chosen, by simp [stepConfigurationOutcome, success]⟩
  | arrays reduced =>
    cases result : stepConfiguration config with
    | some chosen => exact .inl ⟨chosen, by simp [stepConfigurationOutcome, result]⟩
    | none =>
      obtain ⟨exceptions, vectors, arrays, rest⟩ := stepConfiguration_none_iff.mp result
      obtain success | limit := stepArrays_complete_or_limit reduced valid.store valid.active valid.frames
      · simp [arrays] at success
      · cases found : arrayResourceLimit? config.store config.frame config.code with
        | none => simp [found] at limit
        | some limit => exact .inr ⟨limit, by simp [stepConfigurationOutcome, result, found]⟩

theorem resource_supported_progress_complete : ResourceProgressCompleteOn (fun config =>
    config.SupportedFamilyDomain ∧ ResourceSupportedFamilyStep config) := by
  intro config valid _
  exact stepConfiguration_resource_complete_supported valid.1 valid.2

/-- All semantic instruction families are covered by ordinary or resource-aware progress. -/
theorem ConfigStep.resourceSupported (reduced : ConfigStep config next) :
    ResourceSupportedFamilyStep config := by
  cases reduced with
  | pure h => exact .ordinary (.pure h)
  | locals h => exact .ordinary (.locals h)
  | call h => exact .ordinary (.calls h)
  | globals h => exact .ordinary (.globals h)
  | memory h => exact .ordinary (.memory h)
  | bulk h => exact .ordinary (.bulk h)
  | references h => exact .ordinary (.references h)
  | tables h => exact .ordinary (.tables h)
  | structures h => exact .ordinary (.structures h)
  | vectors h => exact .ordinary (.vectors h)
  | exceptions h => exact .ordinary (.exceptions h)
  | arrays h => exact .arrays h

/-- Every semantic successor is found, or execution reports an explicit allocation limit. -/
theorem stepConfiguration_resource_complete (valid : config.SupportedFamilyDomain)
    (reduced : ConfigStep config next) :
    (∃ chosen, stepConfigurationOutcome config = .next chosen) ∨
      (∃ limit, stepConfigurationOutcome config = .stopped (.resourceLimit limit)) :=
  stepConfiguration_resource_complete_supported valid reduced.resourceSupported

/-- Resource-aware progress completeness for the entire certified configuration semantics. -/
theorem resource_progress_complete : ResourceProgressCompleteOn Configuration.SupportedFamilyDomain := by
  intro config valid ⟨next, reduced⟩
  exact stepConfiguration_resource_complete valid reduced

/-- Failure without an allocation-limit outcome implies semantic irreducibility on the domain. -/
theorem stepConfiguration_none_irreducible (valid : config.SupportedFamilyDomain)
    (stopped : stepConfiguration config = none)
    (resources : arrayResourceLimit? config.store config.frame config.code = none) :
    ¬ ∃ next, ConfigStep config next := by
  intro ⟨next, reduced⟩
  obtain ⟨chosen, found⟩ | ⟨limit, found⟩ := stepConfiguration_resource_complete valid reduced
  all_goals cases outcome : stepOutcome config.frame.module.types config.code <;>
    simp [stepConfigurationOutcome, stopped, resources, outcome] at found

/-- Semantic irreducibility exactly characterizes failure when allocation is not limiting. -/
theorem stepConfiguration_none_iff_irreducible (valid : config.SupportedFamilyDomain)
    (resources : arrayResourceLimit? config.store config.frame config.code = none) :
    stepConfiguration config = none ↔ ¬ ∃ next, ConfigStep config next := by
  constructor
  · intro stopped
    exact stepConfiguration_none_irreducible valid stopped resources
  · intro irreducible
    cases found : stepConfiguration config with
    | none => rfl
    | some next => exact False.elim (irreducible ⟨next, stepConfiguration_sound found⟩)

/-- A stopped classification other than a resource limit has no semantic successor on the domain. -/
theorem stepConfigurationOutcome_stopped_complete (valid : config.SupportedFamilyDomain)
    (stopped : stepConfigurationOutcome config = .stopped status)
    (terminal : ∀ limit, status ≠ .resourceLimit limit) :
    ¬ ∃ next, ConfigStep config next := by
  intro ⟨next, reduced⟩
  obtain ⟨chosen, found⟩ | ⟨limit, found⟩ := stepConfiguration_resource_complete valid reduced
  · simp [stopped] at found
  · have same : status = .resourceLimit limit := by simpa [stopped] using found
    exact terminal limit same

/-- A reported stuck state has no semantic successor on the declarative runtime domain. -/
theorem stepConfigurationOutcome_stuck_complete (valid : config.SupportedFamilyDomain)
    (stuck : stepConfigurationOutcome config = .stopped .stuck) :
    ¬ ∃ next, ConfigStep config next := by
  apply stepConfigurationOutcome_stopped_complete valid stuck
  intro limit impossible
  cases impossible

#print axioms step_complete
#print axioms step_none_iff
#print axioms resource_progress_complete
#print axioms stepConfiguration_none_irreducible
#print axioms stepConfiguration_none_iff_irreducible
#print axioms stepConfigurationOutcome_stopped_complete
#print axioms stepConfigurationOutcome_stuck_complete

#print axioms stepConfiguration_resource_complete_supported

#print axioms stepConfiguration_complete_supported

#print axioms stepLocals_complete
#print axioms stepLocals_iff
#print axioms stepConfiguration_none_iff
#print axioms stepConfiguration_complete_locals
#print axioms locals_progress_complete
#print axioms locals_resource_progress_complete

end Wasm
