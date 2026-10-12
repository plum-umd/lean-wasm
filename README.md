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
Call-stack exhaustion can satisfy `assert_exhaustion`; running out of fuel is a failure.
Allocation budgets are embedder resource policy, separate from static validation.
Exit codes are **0** for complete success, **1** for failures, and **2** for unsupported coverage.

## Execution machine

The certified APIs and the `wast` CLI use one explicit execution machine with an
`Array StructInst` heap. Its runtime store is related to the specification store through
a boundary conversion, and each certified transition follows the reduction rules.
Instruction evaluators are certified building blocks, and the declarative reduction
relations provide the correctness specification.

Execute a specification configuration with:

```lean
import Wasm.Configuration

def execute (fuel : Nat) (input : Wasm.Configuration) : Wasm.Configuration :=
  (Wasm.runConfiguration fuel input).state
```

That API converts the store once at entry, runs the machine, and reconstructs the result
once at exit. `Wasm.stepConfiguration` similarly wraps a single machine step. Repeatedly
calling the specification single-step API converts at each call; retain a machine for
sustained execution or resumption:

```lean
import Wasm.Execution

def start (input : Wasm.Configuration) : Wasm.Execution.Machine :=
  Wasm.Execution.Machine.ofConfiguration (Wasm.Execution.Configuration.ofSpec input)

def resume (fuel : Nat) (machine : Wasm.Execution.Machine) : Wasm.Execution.Machine.RunResult :=
  Wasm.Execution.Machine.run fuel machine
```

`Wasm.Execution.runConfiguration` retains the array heap in its returned configuration.
`Wasm.Execution.Machine.toSpec` reconstructs the specification configuration when needed;
decoding never occurs inside the execution loop.
Other store components, struct fields and GC array instances retain their list representations.

The machine holds current instructions, a top-first operand stack, the current frame
(locals and module), and suspended labels, handlers and calls. It dispatches to one certified
instruction family, supplying only the operand packet. Boundary events reconstruct the
immediate context and unwind one specification step at a time. Struct updates are deferred
until the old input can be released, allowing array `push` without retaining an old snapshot.
An embedder retaining an earlier heap snapshot can still cause array copying.

`Wasm.Native.run` and `Wasm.Native.runMachine` use hooks on the same `Machine.execute` fuel
loop for native floating-point arithmetic, SIMD extensions, spectest output and call-depth
limits. Ordinary instructions do not traverse suspended contexts for call-depth checks;
only possible function activations count suspended calls. `Native.runMachine` supports
resumption without converting the heap or reconstructing nested code. Native extensions
have unproved execution correctness.

The public `stepConfiguration_sound`, `runConfiguration_sound`, `runConfiguration_finished`
and `runConfiguration_trapped` theorems connect the API to the reduction rules. Each successful
semantic transition corresponds to one `ConfigStep`, complete runs follow
`ConfigSteps`, and reported finished/trapped/exception/exhausted results have their stated
semantic meaning. Administrative moves preserve reconstruction exactly and terminate by a
strictly decreasing code-size measure, erased at runtime. They consume no fuel. Heap lookup,
allocation, mutation and reference typing have correspondence proofs. General
completeness and absence-of-step correctness remain future proof goals.
All correctness proofs use only Lean's standard axioms, with no `sorry` or new axioms.

The default build checks instruction-family fixtures, multi-value branches, calls and tail
calls through handlers, exception references, heap boundaries, API conversions, fuel
composition and resumption. Native tests additionally check output ordering and that status
probing/resumption does not print speculatively or repeat output. The conformance harness
includes a mixed machine integration script combining heap operations, floats, exceptions,
mutable globals and direct/reference/tail host calls.

Measure compiled machine execution with:

```sh
python3 tests/benchmark-fast.py
# A shorter run:
python3 tests/benchmark-fast.py --sizes 1000 16000 --depths 0 256 --repeat 3
```

The harness measures certified and native policies on the same engine. It records fresh-process
samples, medians, spread, hardware/toolchain/source metadata, and input/output conversion costs
in `.cache/benchmarks/`. Workloads cover allocation, reads, linked structures, control loops,
blocks, calls, tail-call chains, handlers and exception unwinding. These synthetic workloads
require no external application checkout and do not predict application speedups.

[Recorded machine measurements](benchmarks/unified-executor/summary.md) include 644 samples
under certified and native policies. On an Apple M1, 16,000 allocations took median execution
times of 60.4 ms and 61.4 ms respectively. At depth 256, 1,000 loop iterations under suspended
calls took 4.6 ms and 4.7 ms. The results report conversion costs separately and include the
source revision and measurement conditions.

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

The `.wast` runner uses native extensions on the same execution machine for floating-point
arithmetic and `spectest` host calls. Their execution correctness is unproved; scalar and vector floating instruction
validation is included in the validator soundness proof. Relaxed SIMD selects one allowed
result profile rather than enumerating every permitted result.

The implementation manually transcribes the upstream rules. Correspondence to an imported
specification, parser/decoder correctness, validator rejection correctness/completeness,
absence-of-step completeness, preservation/progress, and IEEE/native execution proofs remain
future work. There are no `sorry` proofs or custom correctness axioms; Lean tests print proof
axiom dependencies.

## Code organization

| Area | Entry points |
| --- | --- |
| Syntax and runtime | [Syntax](Wasm/Syntax.lean), [Runtime](Wasm/Runtime.lean), [Module](Wasm/Module.lean) |
| Types and validation | [TypeSyntax](Wasm/TypeSyntax.lean), [ExecutableValidation](Wasm/ExecutableValidation.lean), [Soundness](Wasm/ExecutableValidationSoundness.lean) |
| Certified execution | [Configuration API](Wasm/Configuration.lean), [Machine](Wasm/MachineExecution.lean), [Execution store](Wasm/Store.lean), [Semantics](Wasm/ConfigurationSemantics.lean), [Instantiation](Wasm/Instantiation.lean) |
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
