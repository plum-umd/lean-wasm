# Type-safety proof development

Work on this branch targets progress and preservation for the declarative Wasm
semantics. Passing the conformance suite and proving executable-stepper soundness
do not establish either property.

## Mechanized guide

The initial guide is [WasmCert-Isabelle at revision
d9b4659](https://github.com/WasmCert/WasmCert-Isabelle/tree/d9b4659c8b38879a5fc7e0213950751a61091908).
Its [Wasm_Soundness.thy](https://github.com/WasmCert/WasmCert-Isabelle/blob/d9b4659c8b38879a5fc7e0213950751a61091908/WebAssembly/Wasm_Soundness.thy)
derives preservation from separate store-preservation and expression-typing
preservation lemmas. Progress proceeds from numeric redexes through evaluation
contexts and labels to expressions and configurations; the supporting proofs
are in `Wasm_Properties.thy`. We use the proof organization as a guide, rather
than assuming that its definitions or feature coverage coincide with ours.

The official [Wasm 3.0 type-soundness statements](https://webassembly.github.io/spec/core/appendix/properties.html)
are the target: preservation includes store extension, and terminal states
include values, traps, and uncaught exceptions.

## Completed: flat integer configuration safety

The first milestone is complete. The proofs use the existing `Reduces`,
`IntegerReduces`, `ExecStep`, and `ConfigStep` relations without changing them.

- `Arithmetic.lean` and `Integers.lean`: totality and result-type preservation for
  every integer numeric instruction, including undefined-operation traps.
- `FlatTyping.lean`: declarative administrative typing, polymorphic traps,
  stack weakening, composition, decomposition, canonical stack effects, and
  the existing `SeqTyping` source bridge.
- `FlatPreservation.lean`: parametric and integer redex preservation, lifted
  through flat evaluation contexts.
- `FlatProgress.lean`: semantic progress from typing and canonical operand forms.
- `FlatSafety.lean`: preservation for **all** possible existing `ConfigStep`
  transitions from a flat typed configuration; multi-step safety and result types.

The main theorems are `ConfigStep.preserves_flat`,
`flat_configuration_progress`, `flat_configuration_safety`, and
`flat_configuration_results`, in namespace `Wasm.TypeSafety`.
`ScalarCode` admits integer operations, constants, `nop`, `unreachable`, `drop`,
and `select`. Constants may include other numeric types as opaque values;
floating-point operations are excluded from progress. `FlatTyping` separately
requires the existing instruction typing derivation. Arbitrary ambient frames
and stores are permitted because these instructions do not access them.

Multi-step safety assumes only initial typing, fragment membership, and an
existing `ConfigSteps` derivation. It proves typing of every reachable state
and that the state is terminal or can step. Successful terminal values have
exactly the declared result types. Termination is not claimed.

`Wasm/TypeSafetyTests.lean` checks theorem use with arbitrary operands and
configurations and prints axiom dependencies. The proofs contain no `sorry`
or custom axioms; dependencies are Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`. The `runConfiguration_flat_safe` corollary applies this
result to the certified runner at any fuel budget.

## Completed: control, locals, calls, and return

Milestones 2–4 now have kernel-checked runtime theorems:

- `CoreTyping.lean`: administrative typing for labels, activations, direct
  invocation, control, locals, and return; composition, weakening, and inversion.
- `CorePreservation.lean`: every control and activation redex preserves typing,
  including branches that discard values and explicit return unwinding.
- `CoreLocals.lean`: initialized integer local invariants and preservation of
  get/set/tee through evaluation contexts and nested activations.
- `CoreStore.lean`: independent module/function/store invariants, integer runtime
  matching, argument typing, frame initialization, and typed invocation.
- `CoreCalls.lean` and `CoreExecution.lean`: call and execution preservation through
  labels and activations, using each function's defining module.
- `CoreConfiguration.lean`: preservation for **every** rule of the existing
  `ConfigStep` relation, and its reflexive transitive closure.
- `CoreProgress.lean`: progress from typing and store/frame invariants. Intermediate
  expressions can expose a pending branch or return; labels and activations
  discharge them, and closed configurations cannot expose free escapes.
- `CoreSafety.lean`: multi-step safety, successful result types, and the certified
  runner corollary for arbitrary fuel.

The main theorems are `ConfigStep.preserves_core`,
`core_configuration_progress`, `core_configuration_safety`,
`core_configuration_results`, and `runConfiguration_core_safe`.
Their initial hypothesis is `CoreConfigurationTyped`, which packages independent
store, module, initialized-local, and expression typing. The root context has no
return target; activation contexts have their own result types. No step or
invocation success premise defines these invariants. Stores remain unchanged in
this core, so preservation proves store equality rather than allocation extension.

`CoreTests.lean` constructs a self-recursive, well-typed store and demonstrates
safety without termination or call-depth bounds. It also checks a branch that
returns two values while discarding a lower value, and prints axiom dependencies.
The quantified activation and call proofs permit distinct defining modules and
arbitrary parameter/result arities.

`CoreSource.lean` embeds the existing `ControlInstrTyping`/`ControlSeqTyping` and
`FunctionInstrTyping`/`FunctionSeqTyping` judgments, with a separate syntactic
`CoreSource` restriction. `FunctionSeqTyping.configuration_safety` connects
source proofs directly to executions of the original code.

## Source bridges: native typing and a proved obstruction

Both function-body paths now embed in `NativeCoreTyping`, retaining bottom
stack types, subtyping, and branch-table matching:

- `NativeTyping.lean`: administrative typing over `Types.ValType`, with labels,
  activations, invocations, weakening, and subtyping. Every old `CoreTyping`
  derivation embeds through `CoreTyping.toNativeCoreTyping`.
- `NativeSource.lean`: `RuntimeSeqTyping.toNativeCoreTyping` and
  `ValidationSeqTyping.toNativeCoreTyping`, plus their instruction counterparts.
  The mutually recursive legacy/validation paths are handled without erasing
  bottom or imposing restrictions on intermediate stack types.
- `NativeStore.lean`: native function/store/configuration invariants;
  `FuncTyping.toNativeCoreFunctionTyped` handles both existing function-typing
  constructors. `Invokes.native_core_typed` proves that invocation installs a
  typed activation using the defining module and initialized integer locals.
- `NativeValidation.lean`: successful executable source or bottom checking
  yields native administrative typing. `checkSourceCode_native_configuration`
  supplies the initial native invariant given independently typed store/frame
  invariants and the source fragment restriction.
- `NativeMatching.lean`: numeric matching inversion, numeric matching chains,
  and exclusion of bottom as the type of a concrete numeric value.

The originally proposed bridge into **exact** `CoreTyping` is false, even for
a closed function with integer-only locals and parameters/results. The
kernel-checked `deadReferenceSelect_not_exact` regression proves this for:

```wat
unreachable
select (result (ref func))
i32.const 1
select (result (ref null func))
drop
```

Executable validation succeeds. Both selects are unreachable, but their
annotations require nullability widening between the two stack effects. Exact
typing cannot express that widening. `deadReferenceSelect_native` proves the
native embedding, and `sourceStore_native` checks the function bridge in an
actual store. Additional examples cover bottom operands and matching branch
tables. These are typing-invariant regressions, not semantic safety failures.

## Completed: native progress, preservation, and multi-step safety

`native_core_configuration_progress` now proves progress for the whole
`NativeCoreConfigurationTyped` invariant. Every such configuration is terminal
or has a step in the existing **full** `ConfigStep` relation. The proof includes
recursive invocations, nested labels and frames, and bottom/subtyping evidence
in unreachable code. It requires neither stepper success nor a fuel or
call-depth bound.

- `NativeContexts.lean`: explicit matching chains, sequence decomposition,
  composition, singleton inversion, and input/output coercions. Matching chains
  avoid assuming transitivity for arbitrary unscoped reference types.
- `NativeSourceInversion.lean`: eliminate both mutually recursive source
  typing paths into primitive effects and typed structured bodies.
- `NativeValues.lean`: numeric constant effects, concrete operand-prefix
  inversion, and exact terminal result types despite source subtyping.
- `NativeInversion.lean`: branch/return arguments, typed label and frame bodies,
  and invocation inputs.
- `NativeScalar.lean`: live numeric operands recover ordinary scalar effects;
  bottom cannot denote a concrete operand. Scalar source progress reuses the
  existing numeric totality proofs.
- `NativeProgress.lean`: source-head progress, invocation, escape unwinding,
  structural administrative progress, and closed-configuration progress.

`NativePreservation.lean` proves preservation for parametric and integer
redexes, and for every existing `ExecStep` from a scalar expression. Unreachable
and trap effects retain arbitrary result stacks. Live redexes reuse the earlier
arithmetic preservation proofs. Evaluation contexts use native sequence
composition and concrete operand inversion.

`native_scalar_execution_safety` combines preservation and progress for
arbitrary existing `ExecSteps` traces in the scalar fragment. The regression
with unreachable typed reference selects is covered, although it cannot have
the old exact typing derivation. Other examples apply full native progress to
the source-typed store, its caller, and a fresh activation.

Full preservation and configuration safety are now proved:

- `NativeEffects.lean`: instruction effects retain explicit input/output matching
  chains through weakening and subtyping, including label/frame result effects.
- `NativeControl.lean`: structured control and activation completion, including
  multi-value branches, discarded lower values, loop continuations, and returns.
- `NativeLocals.lean`: local reductions preserve both expression typing and
  initialized local invariants through nested labels and frames.
- `NativeCalls.lean`: direct calls and invocation install independently typed
  callee bodies, including recursive functions, without a call-depth bound.
- `NativeExecution.lean`: every existing `ExecStep` preserves native typing
  with a numeric ambient input stack; closed configurations start with `[]`.
- `NativeConfiguration.lean`: every rule of the full existing `ConfigStep`
  relation preserves `NativeCoreConfigurationTyped`; unsupported instruction
  families are excluded by inversion. The store remains equal for this core.
- `NativeSafety.lean`: arbitrary `ConfigSteps` traces remain typed and cannot
  become stuck. Successful value results have exactly the declared types.
  `runConfiguration_native_core_safe` applies to every fuel value, and
  `checkSourceCode_native_safety` connects successful source validation to safety
  given independently typed stores and initialized frames.

The native-only unreachable/reference-subtyping regression is covered through
full configuration traces containing calls and activations, as well as pure
scalar traces. The older exact-core theorems remain unchanged.

All added bridges and counterexample proofs use only Lean's standard axioms;
the existing judgments, reductions, and exact-core theorem statements remain
unchanged.

The core excludes floating-point operations, SIMD operations, references, tail
calls, memory, globals, tables, GC, exceptions, and host functions. Numeric
constants can be carried as opaque values; function parameters, results, and
initialized locals are restricted to integers by the runtime invariants.
No existing judgments or reductions were changed, and no concrete semantic
counterexample was found during these milestones.

## Issues to resolve before a full theorem

- Runtime type matching uses bounded search. Valid inputs must not become stuck
  merely because the search is inconclusive; discharge sufficient-budget lemmas
  or revise the semantics/search interface with an explicit justification.
- Allocation budgets are embedder policy. A full progress theorem must account
  for the specified failure behavior rather than treating budget exhaustion as
  absence of a semantic step.
- Native floating-point and host execution are outside the current certified
  backend. A fragment theorem needs an explicit restriction; full Wasm safety
  needs corresponding semantics and assumptions.

Keep the existing judgments and reductions intact. Report concrete
specification mismatches before proposing changes. No `sorry`, custom axioms, or circular
definitions of well-typedness in terms of being able to step.
