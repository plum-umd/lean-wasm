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

## Array-backed certified executor

`import Wasm.Fast` exposes a separate executor with `Array StructInst` storage. The
specification store and reduction rules remain the correctness specification. All instruction
families supported by the original certified `runConfiguration` have fast counterparts,
including mutable structs; other store components retain their existing representations.

```lean
import Wasm.Fast

def executeFast (fuel : Nat) (input : Wasm.Configuration) : Wasm.Configuration :=
  let result := Wasm.Fast.runConfiguration fuel (Wasm.Fast.Configuration.ofSpec input)
  result.state.toSpec
```

Convert once at entry and once at exit. When resuming after fuel exhaustion, retain the
`Wasm.Fast.Configuration` and pass it directly to the next run. Conversion traverses the
struct heap and should not be performed between instructions.

`Wasm.Fast.Store.Rel` relates stores by equality after decoding: the fast array's `toList`
equals the specification list, and every other component agrees. Allocation, lookup, mutation,
and runtime reference typing have kernel-checked correspondence lemmas.
`Wasm.Fast.stepConfiguration_spec` maps each successful fast transition to one original
`Wasm.ConfigStep`; `Wasm.Fast.runConfiguration_spec` maps execution to `Wasm.ConfigSteps`.
These proofs use only Lean's standard axioms, with no `sorry` or new axioms. The stronger
claim that both executors always return exactly the same optional step and run status is
covered by differential regression tests, rather than a general equality theorem.

Allocation uses array `push` and lookup uses array indexing. Struct scanning returns a planned
update, applied after dispatch and the fuel runner choose that step, so retaining the input
during fallback does not force an array copy on every allocation. A checked equality connects
the runner's deferred step plan to the fast single-step dispatcher. Lean arrays can still copy when a caller retains
an earlier heap snapshot. Struct fields and the GC array-instance heap remain lists.
The heap-only executor retains nested administrative instruction traversal. The explicit
stack executor below removes that traversal from ordinary instruction dispatch. The `wast` CLI continues to use its
existing backend, whose broader coverage exceeds the certified configuration executor.

The default build runs differential tests over complete configurations and statuses, several
fuel limits, resumed execution, heap boundaries, and instruction-family fixtures. Measure
compiled execution with:

```sh
python3 tests/benchmark-fast.py
# A shorter run:
python3 tests/benchmark-fast.py --sizes 1000 4000 --repeat 3
```

The harness alternates backends, discards warm-up samples, and records individual timings,
medians, spread, machine/toolchain metadata, and boundary-conversion costs in
`.cache/benchmarks/`. Workloads cover primitive allocation and lookup, complete allocation
loops, allocation plus reads, linked structures with function calls and casts, fixed heaps
with early/middle/late reads, and a control-only baseline. Code size stays constant as heap
size grows. Timers use IO evaluation barriers to prevent pure computation from moving across
timer reads. These synthetic workloads require no external application checkout.

Primitive heap cases time operations on prepared stores and report zero conversion costs.
Their “end-to-end” column is therefore the operation ratio. Complete executor cases measure
both configuration conversions separately and include them in the end-to-end ratio.

[Recorded measurements](benchmarks/array-heap/summary.md) on an Apple M1 use seven samples
per case, five sizes from 1,000 to 16,000, and all eleven workloads. At 16,000 structs:

| Complete workload | Original ms | Fast ms | Speedup including conversions |
| --- | ---: | ---: | ---: |
| Allocation | 2,839.9 | 114.7 | 24.73× |
| Allocation and reads | 3,925.7 | 125.8 | 31.18× |
| Linked structures, calls and casts | 7,659.2 | 446.9 | 17.13× |
| Late-address reads | 847.3 | 112.3 | 7.53× |
| Control only | 130.2 | 129.3 | 1.01× |

Early-address executor reads are about 1% slower. The fast allocation loop scales from 7.2 ms
at 1,000 structs to 114.7 ms at 16,000, consistent with linear growth over these sizes.
These are synthetic executor measurements; they establish heap scaling and do not predict
an application's speedup. The recorded directory includes raw samples, metadata and source
hashes. Validation passed `lake build` (including fast differential tests) and all 257 scripts /
65,202 commands of the unchanged backend's pinned conformance suite.

## Explicit execution stack

`Wasm.Fast.Machine` keeps the current code, a top-first operand stack, the current frame
(locals and module), and suspended labels, handlers, and calls. It retains the array heap.
Entering administrative contexts and moving constants onto the stack preserve the decoded
configuration exactly. Opcode dispatch selects one certified instruction family and supplies
only its operand packet. Returns, branches, tail calls, traps, and exceptions inspect the
immediate suspended context and unwind one specification step at a time.

```lean
import Wasm.Fast

def executeMachine (fuel : Nat) (input : Wasm.Configuration) : Wasm.Configuration :=
  let machine := Wasm.Fast.Machine.ofConfiguration (Wasm.Fast.Configuration.ofSpec input)
  (Wasm.Fast.Machine.run fuel machine).state.toSpec
```

Retain the returned machine when resuming. `Machine.toConfiguration` reconstructs the nested
fast configuration; `Machine.toSpec` additionally converts the heap. Reconstruction is used
at boundaries and in erased proofs, never in the execution loop. Boundary events reconstruct
one context only. The loop preserves deferred struct updates so allocation can consume the
array without retaining an old snapshot.

`Machine.normalize_same` proves the administrative moves preserve reconstruction; their
strictly decreasing code-size measure proves termination and is erased at runtime.
`Machine.step_spec` proves each successful semantic transition is one original `ConfigStep`.
`Machine.run_spec` proves the complete reduction sequence, and `Machine.run_status_spec`
proves finished values, traps, uncaught exceptions, and that exhausted runs can take another
specification step. Administrative moves consume no fuel. These results use only standard
Lean axioms. A general reverse simulation or no-new-stuck theorem remains unproved; tests
compare optional steps, complete configurations, statuses, fuel boundaries and resumption.
The instruction-family fixtures include multi-value branches, calls through handlers,
tail calls, mutable structures, reference exceptions, memory, tables, globals, arrays and SIMD.

Measure all three implementations with:

```sh
python3 tests/benchmark-stack.py --hardware 'Apple M1'
```

The harness measures heap workloads at 1,000, 4,000 and 16,000 iterations, and blocks,
calls, tail calls, handlers and exception unwinding at depths 0, 4, 16, 64 and 256.
Depth cases hold the leaf loop at 1,000 iterations. Each backend runs in a fresh process;
order rotates and reverses, with one warm-up and seven recorded repetitions per case.
Input/output conversion costs are separate. Results, raw samples, source hashes and metadata
are recorded in [benchmarks/explicit-stack](benchmarks/explicit-stack/summary.md).

The recorded Apple M1 run contains 966 samples. At 16,000 allocations the machine takes
57.2 ms versus 115.9 ms for the heap-only executor: a further 2.02× gain, or 50.25× over the
original including conversions. The control loop improves another 2.24×. At depth 256,
1,000 iterations under blocks take 3.8 ms versus 444.9 ms with the heap-only executor;
handlers take 3.8 ms versus 914.9 ms, and suspended calls take 4.1 ms versus 5,400.3 ms.
Machine time stays nearly flat over the measured depths. Tail-call chains remain bounded
in active depth and improve 2.88× at chain length 256. These synthetic depth cases isolate
context traversal and should not be treated as application speedup predictions.

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
absence-of-step completeness, preservation/progress, and IEEE/native execution proofs remain
future work. There are no `sorry` proofs or custom correctness axioms; Lean tests print proof
axiom dependencies.

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
