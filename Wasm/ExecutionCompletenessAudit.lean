import Wasm.Configuration
import Wasm.RuntimeExecutionInvariant

/-!
# Execution progress-completeness audit

The intended property is
`(∃ next, ConfigStep config next) → ∃ chosen, stepConfiguration config = some chosen`.
Together with `stepConfiguration_sound`, this rules out an executor that is stuck whenever
the semantics can step. It does not require the executor to reproduce every semantic successor,
termination, or progress of every well-typed program. The audit reflects the validity
and resource-outcome repairs.

## Checked obstructions and repairs

* `malformedRuntime_counterexample`: a function declares a struct supertype. Declarative
  matching follows that declaration, but executable matching follows the function hierarchy.
  A direct call's argument is semantically typed and its executable argument check fails.
  This remaining witness requires a runtime validity invariant for a completeness theorem.
* `malformedFunction_invalid`: the formerly scoped intermediate is not `HeapValid`.
  `HeapMatches.trans` now requires validity, following the official Wasm 3.0 rule.
  The old `.nofunc`-to-`.any` derivation through this intermediate is no longer admissible.
* `arrayBudget_counterexample`: allocation of 1,048,577 i32 elements has an `ArrayReduces.new`
  derivation, but exceeds `arrayAllocationBudget`. The legacy Option step API returns `none`;
  `stepConfigurationOutcome` and both runners now report an explicit resource-limit outcome.
  The semantic successor is symbolic; checking this witness need not allocate that array.

These witnesses do not refute `stepConfiguration_sound`: returned steps remain certified.
Resource limits are implementation outcomes, not new WebAssembly traps or semantic steps.

## Inventory of all twelve ConfigStep families

Seven families now have complete scanner proofs. The other entries identify outstanding
obligations; single-step resource-aware completeness is now proved on the declared domain.

* pure / `step`: `step_complete` proves progress for every `ExecStep`, including all
  contexts, blocks/loops, conditional and table branches, label exits/unwinding, trap
  propagation, frame completion/return, and local-frame priority. No type-validity premise
  is needed. `step_none_iff` characterizes semantic irreducibility for this family.
* locals / `stepLocals`: `stepLocals_complete` now proves exact completeness for every
  local reduction, including all evaluation contexts. `stepConfiguration_complete_locals`
  proves configuration progress despite family priority; no matching search is used.
* call / `stepCalls`: `stepCalls_complete` covers direct/indirect/reference and tail calls,
  activation, tail unwinding, and all contexts. Valid nominal function subtyping preserves
  requested/callee operand arity; valid expected function parameters discharge argument checks.
  Written invocation heap targets are valid in each enclosing frame.
* globals / `stepGlobals`: `stepGlobals_complete` proves exact completeness through all
  contexts under valid stored runtime identities and expected global types.
* memory / `stepMemory`: `stepMemory_complete` proves progress through all contexts without
  type assumptions. Growth may choose success or `growFail`, including at the embedder budget.
* bulk / `stepBulkMemory`: `stepBulkMemory_complete` covers fill/copy/init/drop, zero-length
  operations, bounds traps, and all contexts without type assumptions.
* references / `stepReferences`: `stepReferences_complete` covers GC reference operations,
  null operations, casts/tests, reference branches, and all contexts. It requires valid stored
  types and valid written cast/test targets in the module of each enclosing frame. Positive
  typing yields a found search result; negative cases use their existing rejection premise.
* tables / `stepTables`: `stepTables_complete` covers reads, writes, size/growth, fill/copy/init,
  drop, null/bounds checks, and all contexts under valid stored and expected table types.
  Growth can choose a permitted failure output.
* arrays / `stepArrays`: `stepArrays_complete_or_limit` covers allocation/default/fixed
  allocation, reads/writes, fill/copy, data/element operations, null/bounds traps, mutability,
  packing, and all contexts. Proof-bearing storage matching is complete on valid expected
  types. Allocation beyond the budget yields the explicit resource-limit alternative.
* structures / `stepStructs`: `stepStructs_complete` covers allocation/default allocation,
  reads/writes, null traps, and all contexts. Static/runtime module coherence proves field-count
  agreement; valid expected field types discharge value/argument matching.
* vectors / `stepVectors`: `stepVectors_complete` proves successful evaluation implies
  signature operand arity and reconciles pure versus memory dispatch. Kernel-checked finite
  opcode normalization leaves executable SIMD equations unchanged. Native floating arithmetic
  is outside the certified relation.
* exceptions / `stepExceptions`: `stepExceptions_complete` covers throw/throw-ref/null,
  try-table, ordered catch selection, discard/unwinding, handler exits, and all contexts.
  Valid expected tag parameters discharge throw argument checking.

## Shared proof obligations and prerequisites

All families close over value prefixes and instruction suffixes, labels, handlers, and frames
directly or through `ExecStep`. Prove that scanning constants locates a semantic redex without
skipping a non-value instruction, preserves the prefix/suffix, and never borrows operands across
a label/handler/frame boundary. Frame recursion must use the inner frame's module and type map.
Administrative exits can take priority over an inner derivation: any permitted output suffices.
At configuration level, the priority chain may select another family; completeness only needs
one successful family and soundness already justifies that selected result.

`Configuration.RuntimeCompletenessInvariant` now connects valid runtime declarations, coherent
active/nested/invocable modules, expected composite value types, and expected global/table
types. `ConfigSteps.runtimeCompletenessInvariant_preserved` preserves this invariant for all
twelve families and arbitrary finite executions. It is a type-facing invariant, not a proof
of whole object-content or instruction typing. Written reference target validity remains a
separate, frame-scoped code condition, as does written invocation target validity.
Expected function and tag parameters are also preserved by the runtime invariant.
`HeapValid` and its proof-bearing bounded checker now validate rolled declarations, including
parent ordering, finality, and composite compatibility. Matching transitivity requires this
validity certificate for intermediate heaps.

Runtime heap/value/argument matching completeness now holds at the unchanged size-derived
budgets on valid runtime types. The completed family proofs use these theorems directly.
An assumption that `checkArgs` or `checkValue` succeeds would leave the central obligation open.
For allocation, state progress completeness with either an explicit resource outcome or a
resource-admissibility hypothesis. Type validity alone does not imply an allocation bound.

`stepConfiguration_complete_supported` composes eleven ordinary family proofs across the
executor priority chain. Array progress permits an explicit allocation limit.
`resource_progress_complete` proves single-step resource-aware progress for all twelve families
on `Configuration.SupportedFamilyDomain`, with no family-selection premise.
`stepConfiguration_none_iff_irreducible` characterizes ordinary failure when the allocation-limit
probe reports none. `stepConfigurationOutcome_stopped_complete` rules out semantic successors
for every stopped classification other than a resource limit on the domain.
Runner fuel is separate from single-step completeness. Domain establishment for validated
programs, whole-content/instruction typing, and preservation of written instruction targets
remain separate obligations. Native floating arithmetic and hosts are outside `ConfigStep`.
-/

namespace Wasm.ExecutionCompletenessAudit

private def structParent : Types.DefinedType := ⟨[.struct_ true [] []], 0⟩

private def malformedFunction : Types.DefinedType :=
  ⟨[.func true [structParent.heap] [] []], 0⟩

private theorem structParent_valid : Types.HeapValid {} structParent.heap := by
  apply Types.checkHeapValid_sound (fuel := 8)
  decide +kernel

/-- Scope permits the malformed function-to-struct declaration used by the witnesses. -/
theorem malformedFunction_closed : malformedFunction.closed := by
  refine ⟨12, ?_⟩
  simp [malformedFunction, structParent, Types.DefinedType.heap, Types.HeapType.scopedFuel,
    Types.SubType.scopedFuel]

private theorem malformedFunction_matches_any :
    Types.HeapMatches {} malformedFunction.heap .any := by
  apply Types.HeapMatches.trans (middle := structParent.heap)
  · exact structParent_valid
  · exact .defined (.super rfl (by
      simp [malformedFunction, structParent, Types.DefinedType.heap, Types.SubType.supers,
        Types.SubType.mapHeap, Types.HeapType.substRecs]) .refl)
  · exact .definedComp rfl
      (.trans (.abstract (by simp)) .structEq .eqAny)

theorem malformedFunction_invalid : ¬ Types.HeapValid {} malformedFunction.heap := by
  intro h
  cases h with
  | abstract h => simp [malformedFunction, Types.DefinedType.heap] at h
  | defined groupValid bound =>
    cases groupValid with
    | mk entries =>
      have sub := entries (Types.SubType.func true [structParent.heap] [] [], 0)
        (by simp [malformedFunction])
      cases sub with
      | mk count vals supers =>
        have parent := supers structParent.heap (by simp [Types.SubType.supers])
        cases parent with
        | mk valid prior unfolded nonfinal matched =>
          simp [structParent, Types.DefinedType.heap, Types.HeapType.unrollIn?,
            Types.DefinedType.unroll?] at unfolded
          cases unfolded
          contradiction

/-- Scope alone no longer certifies an intermediate heap type. -/
theorem malformedFunction_validation_rejected :
    (Types.checkHeapValid 16 {} malformedFunction.heap).isSome = false := by
  decide +kernel

private def signature : FuncType := ⟨[.ref .any], []⟩

private def callee : FuncInst :=
  ⟨signature, {types := [signature]}, .wasm ⟨0, [], []⟩⟩

private def argumentFunction : FuncInst :=
  ⟨⟨[], []⟩, {}, .hostTyped 0 malformedFunction⟩

/-- A malformed type is stored in the argument function's runtime type. -/
def malformedRuntime : Configuration :=
  ⟨{funcs := [argumentFunction, callee]}, {},
    values [.ref (.func ⟨0⟩)] ++ [.invoke ⟨1⟩ signature]⟩

/-- The independently stated store invariant excludes the malformed runtime witness. -/
theorem malformedRuntime_types_invalid : ¬ malformedRuntime.store.RuntimeTypesValid := by
  intro valid
  have bad := (valid.functions argumentFunction (by simp [malformedRuntime])).1.2
  apply malformedFunction_invalid
  simpa [argumentFunction, FuncInst.runtimeType] using bad

theorem malformedRuntime_reducible : ∃ next, ConfigStep malformedRuntime next := by
  refine ⟨{malformedRuntime with code := [.frame 0
    (Frame.initialize callee.module [.ref (.func ⟨0⟩)] []) [.label 0 [] []]]},
    .call (.invoke rfl rfl (.wasm rfl (.cons ?_ .nil)))⟩
  exact ⟨.refNonNull malformedFunction.heap, rfl,
    .ref (a := ⟨false, malformedFunction.heap⟩) (b := ⟨true, .any⟩)
      ⟨fun _ => rfl, malformedFunction_matches_any⟩⟩

theorem malformedRuntime_stuck : stepConfiguration malformedRuntime = none := by
  decide +kernel

theorem malformedRuntime_counterexample :
    (∃ next, ConfigStep malformedRuntime next) ∧ stepConfiguration malformedRuntime = none :=
  ⟨malformedRuntime_reducible, malformedRuntime_stuck⟩

/-- Its store and instruction types do not contain the malformed intermediate declaration. -/
def malformedIntermediate : Configuration :=
  ⟨{funcs := [callee]}, {}, values [.ref (.null .func)] ++ [.invoke ⟨0⟩ signature]⟩

theorem malformedIntermediate_stuck : stepConfiguration malformedIntermediate = none := by
  decide +kernel

private def arrayType : Types.DefinedType :=
  ⟨[.array true [] (.mk (.val .i32) true)], 0⟩

/-- A scalar allocation exceeding the executor's element budget by one. -/
def arrayBudget : Configuration :=
  ⟨{}, {module := {types := [.array (.mk (.val .i32) true)], definedTypes := [arrayType]}},
    values [.i32 0, .i32 1048577] ++ [.instr (.arrayOp (.new_ 0 false))]⟩

theorem arrayBudget_reducible : ∃ next, ConfigStep arrayBudget next := by
  refine ⟨⟨{arrays := [⟨arrayType, Array.replicate 1048577 (.i32 0)⟩]}, arrayBudget.frame,
    values [.ref (.array ⟨0⟩)]⟩, .arrays (.redex (.new rfl rfl rfl ?_ rfl))⟩
  exact ⟨.i32, rfl, .i32⟩

theorem arrayBudget_stuck : stepConfiguration arrayBudget = none := by decide +kernel

theorem arrayBudget_counterexample :
    (∃ next, ConfigStep arrayBudget next) ∧ stepConfiguration arrayBudget = none :=
  ⟨arrayBudget_reducible, arrayBudget_stuck⟩

theorem arrayBudget_resource_limit :
    stepConfigurationOutcome arrayBudget =
      .stopped (.resourceLimit (.arrayElements 1048577 1048576)) := by
  have limit : arrayResourceLimit? arrayBudget.store arrayBudget.frame arrayBudget.code =
      some (.arrayElements 1048577 1048576) := by decide +kernel
  simp [stepConfigurationOutcome, arrayBudget_stuck, limit]

theorem arrayBudget_run_resource_limit :
    (runConfiguration 1 arrayBudget).status =
      .resourceLimit (.arrayElements 1048577 1048576) := by
  decide +kernel

/-- The current executor is not progress-complete for the unrestricted relation. -/
theorem not_unrestricted_progress_complete :
    ¬ (∀ config, (∃ next, ConfigStep config next) →
      ∃ chosen, stepConfiguration config = some chosen) := by
  intro complete
  obtain ⟨chosen, success⟩ := complete malformedRuntime malformedRuntime_reducible
  rw [malformedRuntime_stuck] at success
  contradiction

#print axioms malformedFunction_closed
#print axioms malformedFunction_invalid
#print axioms malformedFunction_validation_rejected
#print axioms malformedRuntime_types_invalid
#print axioms malformedRuntime_counterexample
#print axioms arrayBudget_counterexample
#print axioms arrayBudget_resource_limit
#print axioms arrayBudget_run_resource_limit
#print axioms stepConfigurationOutcome_sound
#print axioms not_unrestricted_progress_complete

end Wasm.ExecutionCompletenessAudit
