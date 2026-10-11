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

Progress, preservation, and multi-step safety are proved for an integer core with structured
control, locals, direct calls, and return against the existing configuration reduction relation.
Validator/function-body typing embeds in bottom-aware administrative typing, with progress,
preservation, multi-step safety, and exact terminal result types proved for that invariant. See
[TYPE-SAFETY.md](TYPE-SAFETY.md) for the precise invariants and scope.

The `.wast` runner uses a separate native backend for floating-point arithmetic and `spectest`
host calls. Their execution correctness is unproved; scalar and vector floating instruction
validation is included in the validator soundness proof. Relaxed SIMD selects one allowed
result profile rather than enumerating every permitted result.

The implementation manually transcribes the upstream rules. Correspondence to an imported
specification, parser/decoder correctness, validator rejection correctness/completeness,
absence-of-step completeness, full-language preservation/progress, and IEEE/native execution
proofs remain future work. There are no `sorry` proofs or custom correctness axioms; Lean tests print proof
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
