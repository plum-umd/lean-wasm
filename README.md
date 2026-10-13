# lean-wasm

A WebAssembly 3.0 implementation in Lean 4, organized around the specification's syntax,
validation judgments, runtime structures, and small-step reduction rules. It includes an
executable validator, certified execution APIs, and a `.wast` conformance runner.

**All 257 top-level scripts in the pinned WebAssembly testsuite pass:** 65,202 commands,
zero failures, and zero unsupported commands. This is complete coverage of that corpus;
full formal conformance remains a separate proof goal.

## Build and run

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake build
sh tests/setup-testsuite.sh
lake exe wast .cache/testsuite/i32.wast .cache/testsuite/i64.wast
```

The toolchain is pinned to **Lean 4.27.0**, with no external package dependencies.
The default build checks proofs, runs Lean regression examples, and builds the `wast` executable.

Run the complete conformance regression:

```sh
sh tests/check-wast.sh --full
```

[GitHub Actions](.github/workflows/ci.yml) runs the full Lean build and this suite on every
push and pull request, and can also be started manually. Each job fetches a fresh upstream
checkout at the recorded revision.

An existing, clean checkout at the recorded revision can also be used:

```sh
sh tests/check-wast.sh --full --testsuite /path/to/testsuite
```

`sh tests/setup-testsuite.sh /path/to/testsuite` fetches into an alternative directory.
Setup is only needed once; subsequent runs can use the checkout offline. To update the suite,
change `tests/testsuite/revision` and review the inventory and expected counts against a fresh
checkout. The harness rejects a different revision or local checkout modifications.

Run individual scripts with explicit resource limits:

```sh
lake exe wast --fuel 4000000 --call-depth 256 .cache/testsuite/memory_copy64.wast
```

The CLI defaults to 10,000 semantic steps per module/action and 1,024 active function frames.
The harness supplies per-script limits, including higher fuel for tail-call stress tests.
Call-stack and allocation exhaustion can satisfy `assert_exhaustion`; fuel exhaustion is a failure.
Allocation budgets are embedder resource policy, separate from static validation.
Exit codes are **0** for complete success, **1** for failures, and **2** for unsupported coverage.

## Implemented features

- Scalar integer and floating-point instructions, conversions, and bit-preserving values.
- Structured control, multi-value blocks, locals, globals, direct/indirect/reference calls,
  tail calls, and exceptions/tags.
- Memory32/64, multiple memories, bulk memory, and active/passive data segments.
- Table32/64, bulk table operations, and element segments.
- Typed heap references, recursive composite types, subtyping, GC structs, arrays, and i31 values.
- `v128`, standard SIMD, and relaxed SIMD using a deterministic result profile.
- Module validation, import matching, allocation, initialization, start functions, and linking.
- Text and binary modules, quoted modules, `.wast` actions/assertions, registrations,
  module definitions/instances, and the `spectest` host environment.

The setup script fetches an upstream Git checkout into `.cache/testsuite/`, which is ignored
by Git. The revision is recorded in [tests/testsuite/revision](tests/testsuite/revision):
[`b464a4cd100d98175ae6e3890db89a2e6c8302f7`](https://github.com/WebAssembly/testsuite/tree/b464a4cd100d98175ae6e3890db89a2e6c8302f7).
The pinned top-level scripts comprise 191 non-SIMD, 59 standard SIMD, and 7 relaxed SIMD scripts.
[Coverage details](tests/testsuite/README.md), the [inventory](tests/testsuite/inventory.tsv),
and [measured counts](tests/testsuite/expected-broader.txt) record the regression baseline.
Unsupported assertions never count as passes. Assertion diagnostic strings are not compared.

Proposal, legacy, and custom subdirectory suites are outside this inventory. Shared
memories/atomics and host environments beyond `spectest` remain unsupported.

## Proof status

Successful executable validation yields a kernel-checked declarative typing derivation through
`Wasm.Validation.validate_sound`. Type matching and recursive type validation also have separate
success-soundness proofs.

The certified configuration stepper and runner prove that returned states follow the Lean
reduction relation (`stepConfiguration_sound`, `runConfiguration_sound`). Instantiation has
soundness proofs, and instruction families establish additional typing and resource invariants.
Integer/bitwise SIMD and vector memory execution are included in certified stepping.

The `.wast` runner uses a separate native backend for floating-point arithmetic and `spectest`
host calls. Their execution correctness is unproved; scalar and vector floating instruction
validation is included in the validator soundness proof. Relaxed SIMD selects one allowed
result profile rather than enumerating every permitted result.

The implementation manually transcribes the upstream rules. Correspondence to an imported
specification, parser/decoder correctness, validator rejection correctness/completeness,
progress of all validated programs, full typing preservation, and IEEE/native execution proofs
remain future work. There are no `sorry` proofs or custom correctness axioms; Lean tests print proof
axiom dependencies.

[The execution completeness audit](Wasm/ExecutionCompletenessAudit.lean) covers all twelve
configuration-step families. Matching transitivity now requires runtime heap validity,
including valid rolled recursive declarations, following the Wasm 3.0 specification.
The former malformed-intermediate witness cannot supply this premise. Malformed stored types
still demonstrate why a completeness theorem needs a runtime well-formedness invariant.

`stepConfigurationOutcome` distinguishes certified steps from terminal, stuck, and resource
outcomes. Array allocation beyond the element budget reports
`RunStatus.resourceLimit (.arrayElements requested maximum)` in both certified and native
runners, preserving the residual configuration. The legacy `stepConfiguration` API retains
its `Option` result for existing step proofs. A completeness theorem must account for resource
outcomes or assume sufficient resources. Memory and table growth already permit failure steps.

[Execution completeness](Wasm/ExecutionCompleteness.lean) now proves resource-aware single-step
progress for all twelve `ConfigStep` families on the explicit `SupportedFamilyDomain`.
Every semantic successor yields a certified executor step or an explicit allocation-limit
outcome. The eleven ordinary families have progress completeness through value prefixes,
instruction suffixes, labels, handlers, and frames. `step_complete` covers the full pure/control
scanner, including block/loop entry, branch selection/unwinding, returns, activation exits,
traps, and local-frame priority, without type-validity hypotheses.
Array progress additionally permits allocation limits; memory/table growth can choose permitted
failure steps. `stepConfiguration_none_iff_irreducible` characterizes failed execution when no
allocation limit is reported. `stepConfigurationOutcome_stopped_complete` proves that a stopped
classification other than a resource limit has no semantic successor on the domain.

[Runtime type invariants](Wasm/RuntimeTypeInvariant.lean) now state the type-facing store domain
and agreement between static module projections and runtime type identities without relying on
executable checks or fuel. Stored functions, structures, arrays, and tags must carry closed,
valid types of the appropriate kind. Reference lookup, semantic value typing, and argument typing
then yield valid actual types. The audit proves that this domain excludes the malformed-store
counterexample.

[Matching completeness](Wasm/MatchingCompleteness.lean) shows how heap-search
completeness lifts to value matching (including nullability) and
result-list matching at the same fuel. Numeric matching needs no heap-search fuel. Heap, value,
and result-list identity succeed with any positive fuel, including recursive types and arbitrarily
long signatures. [Abstract heap paths](Wasm/AbstractMatchingCompleteness.lean) now normalize
arbitrary compositions within the abstract hierarchy and succeed with at least two units of fuel.
[Declared supertype paths](Wasm/DeclaredMatchingCompleteness.lean) of length `n` succeed with
`n + 1` units of fuel, provided the source and target close successfully at each edge. General
[matching normalization](Wasm/MatchingNormalization.lean) now removes nested transitivity
from every heap derivation, producing equivalent primitive-edge paths with valid junctions.
[Closing normalization](Wasm/ClosingNormalization.lean) proves that closing fixes closed runtime
types, and [nominal-parent normalization](Wasm/NominalParentNormalization.lean) proves that valid
runtime definitions have defined parents after unrolling. A direct defined match between closed,
valid runtime types therefore reduces to identity or a nominal parent followed by a normalized
path. [Nominal search normalization](Wasm/NominalSearchNormalization.lean) now proves that
**every** declarative match between defined types with a closed, valid source reduces to a
searchable declared-supertype chain. The finite parent-tree certificate is derived from declarative
validity, with recursive parents handled in index order. Consequently, sufficient search fuel
exists for these matches. General declarative matches starting at abstract upper types also
normalize to the abstract hierarchy and succeed with two units of fuel.
[Heap matching completeness](Wasm/HeapMatchingCompleteness.lean) now covers **all** declarative
matches between valid runtime heaps, including mixed nominal-to-abstract matches and
hierarchy-bottom sources, at the **unchanged fixed `matchingBudget`**. A weighted parent-tree
certificate bounds nominal chains, and hierarchy normalization handles the other cases.
[Runtime matching completeness](Wasm/RuntimeMatchingCompleteness.lean) lifts this result to
runtime value types, stored values, and argument lists under declarative store and expected-type
validity. These theorems assume neither successful executable checks nor a separate fuel bound.
[Runtime invariant preservation](Wasm/RuntimeExecutionInvariant.lean) now covers every
`ConfigStep` family and arbitrary finite `ConfigSteps`. It preserves stored runtime type
identities, static/runtime module coherence, valid expected value types in active, nested, and
invocable modules, and valid expected global/table, function-parameter, and tag-parameter types. Expected composite value types are an
explicit declarative strengthening in [RuntimeExpectedTypesInvariant](Wasm/RuntimeExpectedTypesInvariant.lean),
not assumptions that executable checks succeed. Reference scanner completeness separately
requires valid written cast/test targets in the module of each enclosing frame. Calls likewise
require valid written reference/defined invocation targets in their enclosing frames.
[Nominal function shapes](Wasm/RuntimeNominalShape.lean) prove that valid function subtyping
preserves parameter/result arity, which reconciles requested and actual callee signatures.

Single-step resource-aware completeness is proved on the declared runtime domain.
Whole object-content/instruction typing
and preservation of written instruction targets are also outside the invariant proved here.

## Code organization

| Area | Entry points |
| --- | --- |
| Syntax and runtime | [Syntax](Wasm/Syntax.lean), [Runtime](Wasm/Runtime.lean), [Module](Wasm/Module.lean) |
| Types and validation | [TypeSyntax](Wasm/TypeSyntax.lean), [ExecutableValidation](Wasm/ExecutableValidation.lean), [Soundness](Wasm/ExecutableValidationSoundness.lean) |
| Certified execution | [Configuration](Wasm/Configuration.lean), [Instantiation](Wasm/Instantiation.lean), instruction-specific steppers |
| SIMD | [Vectors](Wasm/Vectors.lean), [VectorStepper](Wasm/VectorStepper.lean), [VectorValidation](Wasm/VectorValidation.lean) |
| Native arithmetic and hosts | [NativeExecution](Wasm/NativeExecution.lean), [NativeFloat](Wasm/NativeFloat.lean), [NativeVector](Wasm/NativeVector.lean), [Spectest](Wasm/Spectest.lean) |
| Parsing and scripts | [Text/Module](Wasm/Text/Module.lean), [Binary/Decode](Wasm/Binary/Decode.lean), [Text/Script](Wasm/Text/Script.lean), [CLI](WastMain.lean) |

Import `Wasm` to use the library. `WasmTests.lean` collects the Lean regressions; `tests/`
contains focused `.wast` fixtures and upstream coverage metadata. Upstream fixtures are fetched
separately rather than stored in this repository.

## Specification

The target is [WebAssembly Core 3.0](https://webassembly.github.io/spec/core/), using the online
specification dated **2026-10-09** as the initial reference. The specification itself is not
pinned to an immutable revision; the testsuite is. Specification changes require explicit review.

Useful references: [syntax](https://webassembly.github.io/spec/core/syntax/instructions.html),
[validation](https://webassembly.github.io/spec/core/valid/instructions.html),
[runtime](https://webassembly.github.io/spec/core/exec/runtime.html), and
[execution](https://webassembly.github.io/spec/core/exec/instructions.html).
