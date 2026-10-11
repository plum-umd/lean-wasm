# lean-wasm

A Lean 4 implementation of WebAssembly, built around the formal specification's
syntax, validation judgments, administrative instructions, and small-step reduction.
The current implementation covers integers, parametric and structured control instructions,
functions and tail calls, exceptions/tags, globals, linear memory, typed references,
GC structs and arrays, SIMD and relaxed SIMD, tables, data/element segments, and module
instantiation. The pinned top-level WebAssembly test corpus is covered; proof completeness
and proposal-specific suites remain separate work.

## Reference

Target: **WebAssembly Core 3.0**, with the online specification dated **2026-10-09**
as the initial reference. The links below are live; the specification is not yet
vendored or pinned to an immutable upstream commit. Specification changes must be
reviewed explicitly rather than silently changing the target.

- [Abstract instructions](https://webassembly.github.io/spec/core/syntax/instructions.html)
- [Validation](https://webassembly.github.io/spec/core/valid/instructions.html)
- [Runtime structures](https://webassembly.github.io/spec/core/exec/runtime.html)
- [Reduction conventions](https://webassembly.github.io/spec/core/exec/conventions.html)
- [Instruction execution](https://webassembly.github.io/spec/core/exec/instructions.html)
- [Numeric operations](https://webassembly.github.io/spec/core/exec/numerics.html)

## Build

Install Lean through elan, then run:

```sh
lake build
```

The toolchain is pinned to Lean 4.27.0. There are no external package dependencies.
The default build includes kernel-checked proofs and examples, plus executable stepper
regressions evaluated during the build. A failed regression fails the build.

## Implemented foundation

| Module | Contents |
| --- | --- |
| `Wasm/Syntax.lean` | Numeric/vector/reference values, recursive instructions, block types, runtime traps, labels, module instances and frames |
| `Wasm/Locals.lean` | Local reductions, contextual evaluator, soundness and frame invariants |
| `Wasm/LocalValidation.lean` | Stack typing for locals and structured control |
| `Wasm/LocalInitialization.lean` | Definite initialization effects for nonnullable locals |
| `Wasm/TypeChecking.lean` | Proof-producing matching search and distinct exhaustion status |
| `Wasm/TypeClosure.lean` | Close source type indices before linking |
| `Wasm/TypeMatchingAlgorithm.lean` | Ordinary subtype matching and separate success soundness |
| `Wasm/TypeValidationAlgorithm.lean` | Recursive function type section checking and success soundness |
| `Wasm/Binary/Reader.lean` | Bounded byte, LEB128, name and section decoding |
| `Wasm/Binary/Decode.lean` | Direct scalar, SIMD, typed-reference, and GC binary module decoding |
| `Wasm/TypedRuntimeTests.lean` | Typed execution and a kernel-checked typed module |
| `Wasm/LocalTests.lean` | Local access, update, tee lowering, block sharing and activation isolation |
| `Wasm/Memory.lean` | Memory instances, little-endian codecs, bounds/growth rules and store invariants |
| `Wasm/MemoryStepper.lean` | Sound scalar integer memory stepping with resource-bounded growth |
| `Wasm/MemoryValidation.lean` | Memory instruction typing, address widths, alignment and offset bounds |
| `Wasm/MemoryTests.lean` | All integer load/store forms, both address widths, traps, growth and imports |
| `Wasm/Data.lean` | Active/passive segments, separate data addresses, allocation and initializer lowering |
| `Wasm/DataValidation.lean` | Segment typing and constant-expression restrictions |
| `Wasm/BulkMemory.lean` | Byte-by-byte bulk reduction rules and store invariants |
| `Wasm/BulkMemoryStepper.lean` | Certified contextual bulk memory stepping |
| `Wasm/BulkMemoryValidation.lean` | Fill/copy/init/drop typing, including mixed address widths |
| `Wasm/BulkMemoryTests.lean` | Overlap, bounds, fuel, data lifecycle, aliases and callee mappings |
| `Wasm/Module.lean` | Source modules, imports/exports/globals, contexts and declarative module validation |
| `Wasm/ConstantExpression.lean` | Certified constant evaluation and agreement with configuration reduction |
| `Wasm/Instantiation.lean` | Import matching, allocation, initialization/start execution and soundness |
| `Wasm/InstantiationTests.lean` | Closures, imports, global dependencies, allocation, traps and resumption |
| `Wasm/References.lean` | References, function addresses, null tests and administrative function casts |
| `Wasm/Tables.lean` | Independent scalar/bulk table rules, limits and store invariants |
| `Wasm/TableStepper.lean` | Certified contextual table stepping and resource-bounded growth |
| `Wasm/TableValidation.lean` | Reference/table/indirect-call typing and function-reference declarations |
| `Wasm/Elements.lean` | Table definitions, active/passive/declarative elements and initializer typing |
| `Wasm/TableTests.lean` | Both index widths, overlap, bounds, growth, references and indirect-call traps |
| `Wasm/ElementInstantiationTests.lean` | Proved-valid reference module, shared imports, segment lifecycle and resumption |
| `Wasm/Globals.lean` | Global lookup/allocation, independent reduction, sound stepping and store invariants |
| `Wasm/GlobalValidation.lean` | Global typing and immutable-write rejection proof |
| `Wasm/GlobalTests.lean` | Store updates, aliases, imports, calls, traps and allocation |
| `Wasm/Calls.lean` | Direct/indirect-call lowering, reference invocation and nested call contexts |
| `Wasm/CallValidation.lean` | Call/return typing, explicit function context and function-body judgment |
| `Wasm/CallTests.lean` | Argument/result order, early returns, imports and recursive calls |
| `Wasm/Runtime.lean` | Store instances, exports and frame initialization |
| `Wasm/FrameReduction.lean` | Activation completion, explicit return and trap propagation |
| `Wasm/Configuration.lean` | Sound configuration stepping and execution with shared store |
| `Wasm/RuntimeTests.lean` | Runtime resolution, allocation, initialization and nested activations |
| `Wasm/Numerics.lean` | Modular add/sub/mul, eqz, arithmetic agreement theorem |
| `Wasm/Integers.lean` | Bit counting, division/remainder, bit operations, comparisons, conversions |
| `Wasm/IntegerReduction.lean` | Integer reduction including arithmetic traps, equivalent local evaluator |
| `Wasm/Validation.lean` | Declarative instruction and sequence typing, stack weakening |
| `Wasm/Reduction.lean` | Local reductions, executable local evaluator, flat contexts, multi-step closure |
| `Wasm/Control.lean` | Structured-control reduction, nested label contexts, extended multi-step closure |
| `Wasm/ControlValidation.lean` | Block/loop/if and branch typing in an explicit label context |
| `Wasm/ControlChoice.lean` | Executable if/br_if/br_table lowering, proved sound |
| `Wasm/Stepper.lean` | Whole-sequence stepping and fuel-bounded execution, both proved sound |
| `Wasm/ControlTests.lean` | Multi-value control, nested branches, loop continuations, traps and typing |
| `Wasm/StepperTests.lean` | Executable coverage of every supported instruction and control rule |
| `Wasm/IntegerTests.lean` | Both integer widths, signedness, traps, shift masking and conversions |
| `WasmTests.lean` | Overflow, subtraction order, selection, stuckness, context and typing examples |

Covered instructions: `i32.const`, `i64.const`, `f32.const`, `f64.const`, `nop`, `unreachable`, `drop`,
untyped and single-type `select`, all scalar integer-only numeric instructions, and
`block`, `loop`, `if`, `br`, `br_if`, `br_table`, `local.get`, `local.set`, `local.tee`,
`global.get`, `global.set`, `call`, `return`, all scalar integer loads/stores,
`memory.size`, `memory.grow`, `memory.fill`, `memory.copy`, `memory.init`, `data.drop`,
`ref.null`, `ref.func`, `ref.is_null`, `table.get`, `table.set`, `table.size`,
`table.grow`, `table.fill`, `table.copy`, `table.init`, `elem.drop`, `call_indirect`, `call_ref`, `ref.as_non_null`, `br_on_null`, and `br_on_non_null`.
The value types are i32, i64, f32, f64, and nullable/nonnullable function/external references.
Concrete references retain recursive function type identity. Untyped `select`
requires numeric values; typed `select`, locals, globals and function signatures
also support these reference types.

### Integer numeric coverage

For both i32 and i64, execution and validation cover:

- `const`, `clz`, `ctz`, `popcnt`, `eqz`;
- `add`, `sub`, `mul`, `div_s`, `div_u`, `rem_s`, `rem_u`;
- `and`, `or`, `xor`, `shl`, `shr_s`, `shr_u`, `rotl`, `rotr`;
- `eq`, `ne`, `lt_s`, `lt_u`, `gt_s`, `gt_u`, `le_s`, `le_u`, `ge_s`, `ge_u`.

Conversions cover `i32.wrap_i64`, `i64.extend_i32_s`, `i64.extend_i32_u`,
`i32.extend8_s`, `i32.extend16_s`, `i64.extend8_s`, `i64.extend16_s`, and
`i64.extend32_s`. Together these are 68 scalar integer-only numeric instructions
from the reference grammar. Integer loads/stores are covered separately below.
Floating-point operations and conversions execute through the separate native backend
described in the frontend section; their execution correctness is not yet proved.

Signed division truncates toward zero. Division/remainder by zero trap, and signed
minimum divided by -1 traps; signed minimum remainder -1 is zero. Signed remainder
uses the dividend's sign. All shift/rotate counts are reduced modulo operand width.
Comparisons produce i32 booleans even for i64 operands. Sign extensions truncate to
the specified low bit width before interpreting the sign.

The original `binop`/`IntBinOp` API retains add/sub/mul and its modular arithmetic
theorem. Additional families use `intUnary`, `intBinary`, `intRel`, and `intConvert`.
`evalBinary` returns `none` for a type mismatch and `some NumericResult.trap` for an
undefined numeric operation, keeping malformed execution distinct from a Wasm trap.

Instruction sequences use the specification's order: the **rightmost value is the
top of the operand stack**. `Reduces` spells out the local inference rules independently
of the executable `reduce` function. `Step` closes these rules under a value prefix
and instruction suffix and propagates traps through those flat contexts. The flat relation omits store and
frame components; `Configuration` supplies them for the extended runtime.
`ExecStep` extends this with `IntegerReduces`, `ControlReduces`, and evaluation inside
administrative labels and activation frames.
The original `Step` and `Steps` embed into the extended relations by proved theorems.

`reduce` evaluates one exact local redex, not a whole program. `none` means no local
rule applies; it does not mean a trap. Operand underflow and numeric type mismatches
have no reduction rule. As in the specification, execution of `select` assumes prior
validation; its type annotation is checked by the typing judgment, not by reduction.
There is no executable validation algorithm yet.

Structured control follows the administrative-label presentation in the specification:
blocks branch with their result arity, loops branch with their parameter arity, and a
loop continuation re-enters the source loop. Normal loop completion simply exits the
label; it never executes the continuation. `br 0` retains the top target-arity values
and discards other operands and the remaining body. Crossing a label with `br (l+1)`
keeps all operands and emits `br l`; the target label later selects the branch values.
Traps propagate out through labels.

`BlockType` supports empty/single-result inline types and type indices, including
multiple parameters and results through a `TypeContext`. This context is a list of
expanded function signatures. `FunctionContext.definedTypes` carries recursive identities
for subtype matching, and function validation separately checks initialization effects. Label
contexts list the innermost target first. Source indices use `Nat`; binary index
bounds will belong to decoding and validation.

`reduceControlChoice` executes one exact `if`, `br_if`, or `br_table` redex and is
proved sound for `ControlReduces`. `step` executes the entire supported fragment,
including block/loop entry, normal label completion, nested evaluation, branch
unwinding, and trap propagation. Instructions and administrative instructions
have nested recursive bodies; they derive executable
`BEq` rather than the previous automatically derived `DecidableEq` (which Lean 4.27
does not support for these nested types).

## Execution

```lean
import Wasm

open Wasm

#eval run 10 [] (instructions
  [.const (.i32 9), .const (.i32 4), .binop .i32 .sub])
-- state: [i32.const 5], status: finished [i32 5]
```

- `step types code` returns `some next` for one semantic step or `none` when it
  cannot step. Leading constants are scanned without spending semantic steps.
- `stepOutcome types code` distinguishes a next step, a finished value stack, the
  terminal runtime trap, and a stuck instruction sequence.
- `run fuel types code` performs at most `fuel` semantic steps and returns both the
  residual `state` and its `status`: finished values, trapped, stuck, or exhausted.
  An exhausted run can resume with `run moreFuel types result.state`. Even at zero
  fuel, finished, trapped, and stuck states are classified without reporting exhaustion.

The implementation scans for the first non-value instruction and evaluates inside
the active label body; values outside a label cannot supply operands inside it.
Every internal successor carries an `ExecStep` proof, erased during compilation.
The public API exposes ordinary instruction lists. Loops are bounded by runner fuel;
the mathematical semantics itself remains independent of fuel.

The relation permits different intermediate trap-propagation paths. The stepper
chooses one: collapse a flat trap context, then propagate through enclosing labels
in subsequent steps. It does not enumerate every successor allowed by `ExecStep`.
Stuck states indicate that the stepper cannot proceed; this is not an executable
module-validation API, and semantic assertions assumed by validation remain assumed.

## Proof boundary

- `evalIntBinOp_spec`: bit-vector execution agrees with natural-number modular arithmetic.
- `reduce_sound` and `reduce_complete`: executable local reduction is equivalent to `Reduces`.
- `reduces_deterministic`: local reduction has a unique result.
- `reduceControlChoice_sound`: executable control selection obeys the new reduction rules.
- `reduceInteger_sound`, `reduceInteger_complete`, `integerReduces_deterministic`:
  the additional integer evaluator agrees with its deterministic reduction rules.
- `divS_undefined_iff`, `remS_defined_iff`, `divS_spec`, `remS_spec`: signed division
  and remainder use the stated trap conditions and truncation-toward-zero primitives.
- `evalUnary_type`, `evalRel_type`, `evalConversion_type`: successful results have
  the expected output types.
- `Step.toExecStep`, `Steps.toExecSteps`, `SeqTyping.toControlSeqTyping`: the existing
  fragment embeds in the extended semantics and validation.
- `ExecSteps.trans`, `ExecSteps.inLabel`, `ExecSteps.inContext`: multi-step composition
  and closure under nested label and flat evaluation contexts.
- `step_sound`: each returned successor is an `ExecStep`.
- `run_sound`: each returned residual state is reachable by `ExecSteps`.
- `stepOutcome_finished`, `stepOutcome_trapped`, `run_finished`, `run_trapped`:
  finished and trapped statuses agree with the actual residual instruction sequence.

These are proofs about the definitions in this repository. Correspondence to the
upstream specification is currently a manual rule-by-rule transcription, not a
mechanized theorem against an imported specification. A proof that `step = none`
implies absence of any `ExecStep`, validation preservation, and progress remain future
work. Exact equivalence to all possible one-step successors is not claimed because
the relation permits alternate trap-propagation paths. There are no `sorry` proofs or
custom axioms; the tests print the proof dependencies for inspection.

## Next increments

1. Pin an immutable upstream specification revision and maintain rule-level coverage.
2. Prove absence-of-step completeness, validation preservation, and progress for the fragment.
3. Prove parser/decoder correctness and executable validator rejection correctness/completeness.
4. Formalize IEEE arithmetic and the native float/host execution boundary.
5. Add proposal-specific suites, including shared memories and threads/atomics, tied to their rules.

## Function runtime foundation

`ModuleInst` maps module-local function indices to `FuncAddr` store addresses.
`FuncInst` retains its defining module; address indirection supports imports and
recursive function references without recursive Lean records. Module/store records
currently project function, global, memory, data, table and element fields. Host functions have symbolic handles
and no invocation behavior. Module instantiation is implemented for this projection;
an executable validation algorithm remains future work. Validation judgments cover
function bodies and complete source modules.

`Frame.initialize` places parameters first. Integer and nullable reference locals receive
defaults; nonnullable reference locals have empty optional slots. `FuncInst.activation?`
checks arguments against the shared store and the signature reference, then constructs
a frame with a result-arity label. Successful checks carry `Invokes` derivations;
completeness is conditional on successful argument search.
The stepper executes existing instructions within activations using the defining
module’s types, isolates their operand stacks, and handles normal completion and
traps. Branches cannot cross an activation boundary.

Allocation lookup/preservation and frame initialization length/types are proved.
`stepConfiguration_sound` lifts instruction stepping to configurations while
allowing local updates to the current frame and global updates to the shared store.
The existing stepper
and runner soundness proofs include the new frame rules.

## Local instructions

`localGet`, `localSet`, and `localTee` use module-local local indices. `local.get`
requires a present, initialized slot; `local.set` consumes the top operand and
updates an existing slot. `local.tee` duplicates the operand and emits `local.set`,
matching the specification’s two-step reduction. Runtime writes assume validation
for value types, rather than turning malformed type mismatches into Wasm traps.
Missing slots and operand underflow are stuck; `tee` itself lowers even if its
subsequent `set` will be stuck. Uninitialized reads are also stuck.

`stepLocals frame code` returns a changed frame and instruction sequence, and
`stepConfiguration` combines local and existing instruction stepping. `step` and
`run` support locals inside administrative activations; bare local instructions
need a frame through `stepLocals` or `stepConfiguration`. Labels share their
frame’s locals; nested activations isolate them. `LocalStep` independently states
the rules, and `stepLocals_sound` certifies the evaluator. Local steps preserve
module identity and local-slot count.

`FunctionInstrTyping` and `FunctionSeqTyping` extend the existing declarative
judgments with an explicit local-type context, including inside blocks, loops,
and conditionals. `FuncTyping` also requires `Func.Initialized`: parameters and
defaultable locals start set, `local.set/tee` initialize a slot, and `local.get` requires
a set slot. Initialization effects inside blocks, loops and conditionals do not escape
into the enclosing validation context, following Wasm 3.0 instruction types.

## Direct calls and return

`Instr.call` resolves its index in the current frame’s module, then uses the shared
store. One step emits `AdminInstr.invoke address type`; a second step consumes the
callee’s arguments and creates its activation. This administrative token projects
the Wasm 3.0 intermediate pair `ref.func address; call_ref type`, retaining both
its address and closed signature. Nullable reference values and `call_indirect` are
implemented below. Source `call_ref`, GC heap types, and tail calls are implemented below.
Certified host invocation remains future work. The direct-call token continues to combine
the intermediate reference construction and invocation.

Arguments move to parameter locals in source order; declared locals start
at zero, null, or an unset slot according to defaultability. Each callee resolves
subsequent calls and block types in its defining
module. Caller operands and continuation remain outside its activation, and callee
local writes are discarded when it exits. Address indirection supports both self
and mutual recursion. Invalid function indices, missing addresses, bad argument
counts/types, and unsupported host invocations become stuck rather than traps.

`Instr.return_` first unwinds one enclosing label, retaining its operands and
discarding that label’s continuation and remaining body. At the nearest activation,
it retains the top result-arity values and discards other operands and remaining
instructions. Return outside an activation or with insufficient results is stuck.
The store-free `step`/`run` APIs support return inside frames; direct calls require
`stepConfiguration`/`runConfiguration`, which have access to the store.

`runConfiguration fuel config` returns the residual configuration and a status:
finished values, trapped, stuck, or exhausted. Each semantic step spends one fuel
unit, including call lowering, invocation, and each return-unwinding step. Resume
with `runConfiguration moreFuel result.state`. Zero fuel still classifies terminal
states. `runConfiguration_sound` proves reachability by `ConfigSteps`; finished
and trapped statuses agree with the residual code, and configuration execution
preserves the function store.

`FunctionContext` adds module-local function signatures and an optional return
type. `RuntimeInstrTyping`/`RuntimeSeqTyping` type calls and stack-polymorphic return
through blocks, loops, and conditionals. `none` forbids return in expressions;
`some []` permits return in void functions. `FuncTyping` checks the signature
reference and body with parameter/local types, an empty initial operand stack,
an implicit result label, and the function’s return type. These are declarative
judgments; execution does not invoke a validator or establish type safety.

```lean
import Wasm
open Wasm

#eval do
  let ft : FuncType := ⟨[.i32], [.i32]⟩
  let module : ModuleInst := { types := [ft], funcs := [⟨0⟩] }
  let function : FuncInst := ⟨ft, module, .wasm ⟨0, [], [.localGet 0, .return_]⟩⟩
  let config : Configuration := ⟨{ funcs := [function] }, { module },
    instructions [.const (.i32 7), .call 0]⟩
  pure (runConfiguration 20 config).status
-- finished [i32 7]
```

## Globals

`GlobalType` records mutability and value type. `GlobalInst` holds that type and
its current value; `GlobalInst.Valid` states their agreement. `ModuleInst.globals`
maps module-local global indices to `GlobalAddr` addresses in `Store.globals`.
Function and global addresses use distinct types and separate index spaces.
Global exports and referential checks are included in the runtime projection.

`globalGet` reads the addressed instance. `globalSet` consumes the top operand
and updates its value in the shared store, preserving the instance’s type and
mutability. `stepGlobals` implements `GlobalStep`, with a soundness proof;
`stepConfiguration` and `runConfiguration` integrate it with existing execution.
Labels share the current module’s mappings. Callees resolve globals in their
defining module, while imported aliases can share the same store instance.
Writes survive return and traps, including traps raised later in the callee.
The store-free `step`/`run` APIs cannot execute global instructions.

`GlobalInstrTyping` permits reads of either mutability and writes only to mutable
globals, using the declared value type. `RuntimeInstrTyping` includes these rules
inside structured control, and `FuncTyping types funcs globals mems dataCount` supplies the
function’s global-type context. `immutable_set_rejected` proves immutable writes
have no global typing derivation, including after stack weakening.

As in the specification, reduction assumes prior validation for mutability and
operand types. The evaluator does not dynamically trap or reject an immutable
write or a type mismatch. Such malformed programs must be rejected before
execution; an executable whole-module validator remains future work. Missing
module indices/store addresses and operand underflow are stuck.

Configuration soundness and runner reachability remain proved. Whole-store
preservation no longer holds: `ConfigStep.functions_preserved` and
`ConfigSteps.functions_preserved` replace the previous `store_preserved` theorems.
Global steps preserve function instances, global count, and global type metadata.
Append-only global allocation preserves existing addresses, and function
allocation preserves globals. Source global declarations and constant initializers
are supported by module validation and instantiation below.

```lean
import Wasm
open Wasm

#eval do
  let counter : GlobalInst := ⟨⟨.var, .i32⟩, .i32 0⟩
  let config : Configuration :=
    ⟨{ globals := [counter] }, { module := { globals := [⟨0⟩] } },
      instructions [.const (.i32 9), .globalSet 0, .globalGet 0]⟩
  pure (runConfiguration 10 config).status
-- finished [i32 9]
```

## Linear memory

`MemoryType` describes memory32 or memory64 address width, minimum pages, and an
optional maximum. `MemoryInst` stores its type and an `Array (BitVec 8)` byte
sequence; one page is 65,536 bytes. `MemoryInst.Valid` requires a whole number of
pages, valid limits, and a runtime minimum equal to current page count. Growth
updates this minimum as in `growmem`. Memory32 permits at most 2^16 pages and
memory64 at most 2^48. Runtime construction assumes validity; `ModuleTyping` checks
declared memory limits and instantiation allocates zero-filled memory instances.

`ModuleInst.mems` maps module-local memory indices to distinct `MemAddr` store
addresses. Imported aliases share an instance in `Store.mems`. Memory exports,
referential checks, allocation and lookup are included. Each callee uses its
defining module’s memory mappings, and writes persist across return and traps.

The scalar integer memory fragment covers:

- `i32.load`, `i64.load`;
- `i32.load8_s/u`, `i32.load16_s/u`;
- `i64.load8_s/u`, `i64.load16_s/u`, `i64.load32_s/u`;
- `i32.store`, `i32.store8`, `i32.store16`;
- `i64.store`, `i64.store8`, `i64.store16`, `i64.store32`;
- `memory.size`, `memory.grow`.

`LoadOp`/`StoreOp` enumerate valid widths. Loads decode little-endian bytes and
sign- or zero-extend packed values. Stores write the low access-width bits in
little-endian order. Operand order is address followed by stored value. Every
instruction carries a memory index, so multi-memory and both address widths work
independently of the loaded/stored integer width.

Effective addresses use unsigned address values plus immediate offsets in `Nat`,
without address-width wrapping. An access traps when its exclusive end exceeds
memory size. A trapping store leaves all bytes unchanged. Misaligned accesses
are permitted: alignment is a validation hint, not a dynamic condition.
`MemArg.Valid` checks alignment against access width and offsets against address
width; `MemoryInstrTyping` supplies the memory’s address type. These rules are
included in `RuntimeInstrTyping`, structured control and `FuncTyping`.
Missing memory indices/addresses, operand underflow, and wrong operand widths
are stuck, distinct from out-of-bounds traps.

`memory.size` returns pages in the memory’s address type. Successful growth
returns the previous page count, preserves old bytes, and appends zero bytes.
Failed growth returns an all-ones value (-1) and leaves memory unchanged.
`MemoryReduces.growFail` allows failure unconditionally for a correctly typed
operand, reflecting the specification’s resource-dependent nondeterminism.
The evaluator chooses success when declared/address-space limits and its fixed
`growthBudgetPages` budget of 1024 pages (64 MiB per memory) permit it; otherwise
it chooses failure. `MemoryInst.grow?` accepts an explicit budget for direct helper
use. This budget is an executable embedder policy, not a Wasm semantic limit.

`MemoryReduces` and `MemoryStep` state the rules independently of the certified
`stepMemory` evaluator. Configuration stepping and the fuel-bounded runner use
these rules, retaining their soundness and reachability proofs. Memory steps
preserve function/global instances and memory-instance count. Byte extraction
length, bounded-write size, growth byte/page counts, successful-growth legality,
and allocation lookup/preservation are proved. A mechanized correspondence to
upstream byte encoding and full validation preservation/progress remain future
work.

Float loads/stores preserve raw IEEE bits. SIMD memory instructions support both address widths;
shared memories and atomic instructions remain unsupported.
The store-free `step`/`run`
APIs cannot execute memory instructions; use `stepConfiguration`/`runConfiguration`.

```lean
import Wasm
open Wasm

#eval do
  let memory : MemoryInst := ⟨⟨.i32, 1, some 2⟩, Array.replicate pageSize 0⟩
  let config : Configuration :=
    ⟨{ mems := [memory] }, { module := { mems := [⟨0⟩] } },
      instructions [.const (.i32 3), .const (.i32 42), .store .i32 0 {},
        .const (.i32 3), .load .i32 0 {}]⟩
  pure (runConfiguration 10 config).status
-- finished [i32 42]
```

## Bulk memory and data segments

`memory.fill`, `memory.copy`, `memory.init`, and `data.drop` follow the
[Wasm 3.0 reduction rules](https://webassembly.github.io/spec/core/exec/instructions.html#memory-instructions).
`BulkReduces` states the primitive rules independently of the executable evaluator;
`BulkStep` extends them through value prefixes, labels, and activations.
`stepBulkMemory_sound` certifies each result. Configuration stepping and execution
include these reductions in their existing soundness proofs.

Fill takes a destination address, an i32 byte value, and an address-typed length.
The subsequent `i32.store8` truncates the byte value. Copy takes destination and
source addresses in their respective memory types; its length is i64 only when
both memories use i64 addresses, and i32 otherwise. Init takes a destination
address in the memory's type, an i32 segment offset, and an i32 length.
`BulkInstrTyping` supplies these rules. `FunctionContext.dataCount` represents
the static data index space, whose entries all have the singleton `ok` type.

Each operation checks the entire destination and source range before writing,
including for zero length. A zero-length range at the end is valid; one beyond
the end traps. Fill and init lower to one byte store and a recursive operation.
Copy lowers to a byte load/store and a recursive operation, proceeding forward
when the destination offset is at most the source offset and backward otherwise.
This preserves overlapping copies, including when distinct module indices alias
the same memory. Fuel counts these actual reduction steps: a one-byte fill/init
takes three steps, and a one-byte copy takes four.

`Data` contains bytes and a passive or active mode. `DataInst` retains only bytes
at runtime. `ModuleInst.datas` maps segment indices to `DataAddr` addresses in
`Store.datas`; segments are internal entities, not imports or exports.
`Store.allocateData` allocates an instance with stable existing addresses.
`data.drop` empties its bytes while retaining the address and instance. Repeated
drops succeed. Init can reuse a segment until it is dropped; afterward only
zero-length reads at offset zero are valid.

`Data.initializer` implements the specification's
[rundata helper](https://webassembly.github.io/spec/core/exec/modules.html#aux-rundata)
for an already allocated segment. Passive segments produce no instructions;
active segments evaluate their offset expression, initialize memory from the
whole segment, then drop it. `DataTyping` requires an existing target memory, a
correctly typed offset expression, and constant instructions: integer constants,
integer add/sub/mul, or reads of immutable globals. Module allocation, instantiation,
and start-function execution are described below. Binary decoding remains future work.
Constructing runtime instances directly still assumes a valid module.

Bulk steps preserve function/global/memory instances and the data-instance count.
Scalar stores then update memory through the existing memory reduction rules.
Allocation lookup/preservation, dropped-instance lookup, and configuration data
count preservation are proved. Tests cover both memory widths, all four copy
width combinations, both overlap directions, aliases, bounds, exact lowering
and fuel, active/passive segments, repeated drops, and callee-specific mappings.

```lean
import Wasm
open Wasm

#eval do
  let memory : MemoryInst := ⟨⟨.i32, 1, none⟩, Array.replicate pageSize 0⟩
  let data : Data := ⟨#[65, 66, 67], .active 0 [.const (.i32 10)]⟩
  let (address, store) := ({ mems := [memory] } : Store).allocateData ⟨data.bytes⟩
  let frame : Frame := { module := { mems := [⟨0⟩], datas := [address] } }
  let result := runConfiguration 20 ⟨store, frame, instructions (data.initializer 0)⟩
  pure (result.status, result.state.store.resolveData? frame.module 0)
-- (finished [], some { bytes := #[] })
```

## Module instantiation

`Module` represents the supported source fragment: function types, ordered imports,
function/global/memory/table definitions, data and element segments, an optional start function, and
exports. Source indices (`ExternIdx`) are distinct from runtime addresses.
Function imports reference a type index; global, memory and table imports declare their
types. Import module/name strings are retained, while the embedder supplies an
ordered list of resolved `ExternAddr` values. Name-based linking is a separate layer.

`ModuleTyping` is the declarative validation judgment for a complete module.
It constructs all static index spaces, checks memory/table limits, types function bodies
and data/element segments using the existing judgments, validates exports and their unique
names, and requires a start signature of `[] → []`. Global initializers must be
typed constant expressions; each sees imported and earlier defined globals only.
`ValidatedModule` pairs a module with a proof of this judgment. Instantiation takes
this proof as input, rather than claiming that a validation algorithm exists.
Proofs are erased during execution. The incoming store is assumed well-formed.

`instantiate fuel store validatedModule addresses` follows the
[Wasm 3.0 instantiation rules](https://webassembly.github.io/spec/core/exec/modules.html#exec-instantiation):

1. Check the exact import count, kinds, addresses, and declared types.
2. Evaluate global initializers in order, making earlier globals available.
3. Evaluate table initializers and element contents, then allocate definitions and exports.
4. Execute element initialization/drop code, then active data initializers, then the start function.

The complete function address map is available to all constant expressions before
closures are allocated, so `ref.func` may refer to a defined function.

Function imports follow defined-type identity and declared supertype edges. Legacy
signatures embed as singleton final groups. Mutable global imports require invariant
value types; immutable globals allow subtyping. Memory imports require the
same address width, an actual minimum at least the required minimum, and, when a
maximum is required, an actual maximum no larger than it. Table imports additionally
require invariant heap types and nullability, and use the same limit matching rules. Imported entities retain
their existing addresses and defining closures; definitions are appended after
imports in each module index space, regardless of interleaved import kinds.

Global initialization uses certified `ConstEval` evaluation, which accepts integer
constants, immutable global reads, integer add/sub/mul, `ref.null` and `ref.func`.
`ConstEval.toConfigSteps`
proves agreement with the ordinary small-step semantics. The reference's
`evalglobal` helper allocates temporary globals; `allocmodule` then allocates final
globals from the evaluated values. This implementation preserves both sets in the
store and maps the final module to the second set, matching the current formal
store layout. Only the temporary frame sees the first set.

Defined memories start with `min * pageSize` zero bytes. Defined functions close
over the complete final module, including all function, global, memory, data, table, element and
export mappings. Computing addresses before constructing closures supports forward
calls and recursion without recursively defined Lean values. Allocation preserves
lookup at all existing addresses; subsequent initialization may write imported
memory, tables or mutable globals through the shared store.

`checkedPrepareInstantiation` is the lower-level allocation API. It returns a
proof-carrying configuration satisfying `ModulePrepared`, or an `InstantiationError`
for import mismatch, the allocation resource budget, or defensive initializer/
allocation checks. It assumes a validated source module; the public `instantiate`
API enforces this through `ValidatedModule`. The optional allocation budget defaults
to `growthBudgetPages` (1024 pages per defined memory), an embedder policy rather
than a Wasm limit. Defined tables additionally use `tableGrowthBudget` (65,536 elements).
These allocation budgets do not restrict imported memories or tables.

The result contains the complete `ConfigurationRunResult`: store, frame, residual
code, and status. `InstantiationResult.module?` returns the module instance only
when execution finishes with an empty operand stack. Traps preserve allocation,
prior writes, and prior segment drops. A failed active segment prevents later
initializers and the start function from executing. Exhaustion returns a resumable
configuration; `resumeInstantiation` continues it without reallocating or repeating
initializers. Constant evaluation and allocation are finite preparation work; fuel
bounds the subsequent element/data/start reduction steps.

`instantiate_sound` proves that the resulting configuration is reachable by the
independent preparation rules followed by certified configuration reductions.
`instantiate_finished` additionally certifies the empty final code on success.
Allocation preservation and resume reachability are proved. The regressions include
a proved-valid module combining imported memory/globals, dependent global initializers,
an active and a passive segment, exports, and a start function that observes initialized
memory. They also cover mixed imports, repeat instantiation, forward/recursive calls,
allocation budgets, traps, and fuel exhaustion.

The source projection includes GC heap types, tags and exceptions. Host imports can
be linked, but the certified runner stops at host invocation; this status does not publish
a completed module. The native runner additionally executes `spectest` host functions. Full validation preservation/progress, and a mechanized upstream
correspondence remain future work.

```lean
import Wasm
open Wasm

def initializeModule (module : Module) (valid : module.Valid)
    (store : Store) (imports : List ExternAddr) :
    Except InstantiationError InstantiationResult :=
  instantiate 1000 store ⟨module, valid⟩ imports
```


## References, tables and element segments

This extension represents **nullable and nonnullable function/external references**,
including concrete recursive function types and their declared subtypes. `RefValue.func` contains a
store address, while `Instr.refFunc` contains a module-local function index.
`RefValue.extern` has an opaque external identifier; no host invocation behavior is
implied. `ref.null`, `ref.func` and `ref.is_null` have independent reduction rules
and certified contextual stepping in `References.lean`. Reference types are
excluded from integer instruction typing and integer address types.

`TableType` records its i32/i64 index type, minimum, optional maximum and reference
heap type and nullability. `TableInst` holds a reference array, while `ModuleInst.tables` maps table
indices to store addresses. Tables may alias through imports or repeated addresses.
`table.get/set` check bounds; `table.size` and `table.grow` return values in the
table's index width. Growth consumes a reference followed by a delta, fills the
new slots with that reference and updates the runtime minimum. Failure returns
-1 in the same width and preserves the store. The independent rules allow the
specification's nondeterministic growth failure, while the evaluator chooses
success within the semantic limits and `tableGrowthBudget`, and failure otherwise.

`table.fill/copy/init` check complete source/destination ranges before any write,
including zero-length operations. They lower to individual `table.get/set` steps
rather than replacing an array in one step. Copy proceeds forward or backward
according to the indices, preserving overlapping source values. Copy length is
i64 only when both tables use i64; otherwise it is i32. `table.init` uses the
destination table's index width and i32 source/length operands. Fuel therefore
bounds individual reductions, and execution can resume within a bulk operation.

Element instances retain their heap type and nullability after `elem.drop` empties their
contents. Source elements contain constant reference expressions and an active,
passive or declarative mode. Active elements run offset/`table.init`/`elem.drop`
code; passive elements remain available; declarative elements are dropped without
writing a table. Table definitions have a constant initializer, defaulting to the
null reference of their heap type; nonnullable tables require an explicit initializer.
Validation restricts table initializers to imported
globals; element expressions can read all immutable globals. Function-reference
declarations are collected from global/table/element expressions and function
exports, and `ref.func` typing requires both a valid index and a declaration.

`call_indirect table typeIdx` follows the
[Wasm 3.0 control reduction](https://webassembly.github.io/spec/core/exec/instructions.html#control-instructions):

1. Lower to `table.get table; ref.cast (ref null typeIdx); call_ref typeIdx`.
2. Fetch the reference, trapping on bounds failure.
3. Cast to the expected defined function type, trapping on a type mismatch and accepting null.
4. Invoke the reference, trapping on null, or create the callee's activation.

`AdminInstr.castDefined` and `invokeDefined` retain the expected recursive type for
modules with explicit type groups. Casts accept declared subtypes and nullable null;
invocation uses store-dependent argument typing and traps on null. Legacy modules
use `castFunc` and `invokeRef` with singleton final signatures. Bounds, type and null
failures remain separate semantic steps. Calls execute in the callee's defining module.
These operations remain administrative; source `ref.cast` and `call_ref` are future work.

`stepReferences_sound`, `stepTables_sound` and `stepConfiguration_sound` prove
agreement with these independent reduction judgments. Table reductions preserve
function/global/memory instances and store address counts. Reference constant
evaluation agrees with ordinary configuration reduction; `RefsEvaluated` certifies
initializer count and store-dependent reference typing. Allocation preserves old
table/element lookups.
The build runs regressions for scalar and bulk operations, both index widths,
external references, indirect-call stages and traps, shared imports, reference
initializers, segment lifecycle, repeated instantiation and resumption.

The `Wasm.Types` namespace now supplies the function/external heap-type foundation:
`func`/`nofunc`, `extern`/`noextern`, nullable and nonnullable references, concrete
function types, recursive groups, finality and declared supertypes. Rolling,
unrolling and closing follow the
[Wasm type conventions](https://webassembly.github.io/spec/core/valid/conventions.html).
Recursive-group identity includes the complete rolled group and projection index.
Recursive substitution stops at nested group binders; module-index substitution
descends under them.

`HeapMatches`, `DefinedMatches`, `RefMatches`, `ValMatches` and `FuncMatches`
are declarative matching judgments. Function signatures use contravariant parameters
and covariant results. Defined types follow declared supertype edges; structural
signature matching alone does not create an edge. As in the specification, matching
is intended for valid contexts. `SubType.Valid` and `TypeSectionValid` express source
validation, including earlier, non-final parents and at most one declared supertype.
`resolve?` computes closed groups but does not certify those validation conditions.
Scope checks take explicit fuel; declarative scope validity requires a successful
check at some fuel, so exhaustion cannot accept an unchecked type.

`ValType.ref heap` and `ValType.refNonNull heap` embed into this foundation with a
proved round trip. `RefKind` is now the function/external heap-type universe, retaining
`.func` and `.extern` as convenient abstract types. `Value.type? store` determines a
function reference's concrete nonnullable type from its allocated function instance;
null values use `nofunc` or `noextern`. `Value.type` remains the erased integer-layer
helper and is not used to check runtime reference assignments or call arguments.

`Module.typeGroups` contains source recursive groups, while `Module.types` contains
corresponding expanded source signatures. Module validation checks their agreement,
recursive group validity, heap-index scope and definite local initialization.
Instantiation closes type indices in signatures, locals, imports, globals, tables and
elements before linking. `ModuleInst.definedTypes` retains the closed identities;
`FuncInst.runtimeType` preserves the defining group across module boundaries. Untyped
legacy signatures become singleton final groups. Typed host references use
`FuncCode.hostTyped`; certified host invocation remains unsupported.

`searchHeap` and `searchValue` distinguish a derivation, algorithmic rejection and
inconclusive search. Runtime search uses a budget derived from the represented type
sizes. Successful checks carry proofs of the declarative matching/typing judgments.
Exhaustion and unknown function addresses cannot produce a cast-failure trap;
inconclusive stepping is stuck. `checkValue` and `checkArgs` expose successful proofs
for argument checks, global/table writes and initializers. Search completeness and
correctness of rejection against the full declarative matching relation are not yet
proved; cast-failure rules currently use algorithmic rejection as their premise.

`TypedRuntimeTests` checks subtype arguments and indirect calls, unrelated types with
the same signature, nullability, dangling references, typed host identity, mutable
import invariance and immutable global covariance. A kernel-checked source module
instantiates nonnullable globals/tables and an active nonnullable element segment
using forward function references, then executes an indirect call through a declared
parent type. Source `call_ref`, `ref.as_non_null`, `br_on_null`, and
`br_on_non_null` use certified reductions. GC reference casts/tests use certified runtime type matching.

These proofs establish soundness against the Lean judgments. They do not establish
full Wasm 3.0 type safety or a mechanized correspondence with the upstream specification.

## Text scripts and conformance tests

The first `.wast` frontend is implemented in `Wasm/Text/`: a byte-preserving
S-expression reader, an integer/float/reference module elaborator, and a script runner.
It handles nested block comments, line comments, UTF-8 strings, hexadecimal byte
escapes, Unicode scalar escapes, and decimal/hexadecimal integer literals with
signs and digit separators. Integer literals are range checked before conversion
to bit patterns.

The module fragment includes numeric and nullable/nonnullable function/external reference signatures,
named and numeric
function/local indices, inline and standalone function exports, flat and folded
numeric instructions, locals, direct calls, and structured control. Blocks, loops,
and conditionals accept inline parameter/result annotations; signatures needing
multiple results or parameters receive implicit type indices. Both flat
`block`/`loop`/`if`–`else`–`end` syntax and folded syntax are supported, along with
named/numeric branch depths, label shadowing, closing labels, and `br_table`.
Numeric `(type $name (func ...))` declarations and named/numeric `(type ...)`
uses are supported on functions, blocks, loops, conditionals, and indirect calls, including
forward references to declarations. A type use alone inherits its parameters and
results; inline annotations must match the full referenced signature exactly.
Parameter names in type declarations are documentation only; names in a function's
inline annotations bind its locals. Inferred signatures reuse the earliest matching
canonical type or append a new type after all explicit declarations. Mixed composite
recursive groups, explicit final/nonfinal subtypes, and named/numeric heap type
indices are supported. Inline signatures compare closed type identities. GC
composite types and `v128` are supported.
Tables support named/numeric indices, inline and standalone exports, i32/i64
address widths, and nullable/nonnullable abstract or concrete function/external
reference types (including `(ref null ...)` and `(ref ...)` spellings). The inline `(table funcref (elem ...))` abbreviation creates a fixed-size
table and an active element segment. Standalone active, passive, and declarative
element segments accept function indices, `ref.func`, nullable function/external references,
and immutable-global reference expressions. Tables accept explicit reference initializers;
active element offsets accept integer constant expressions, including immutable globals
and extended integer arithmetic. Elements may
refer to functions or tables declared later in the module.
Flat/folded `call_indirect` accepts an optional table index (default 0) and a type
use, including inferred numeric signatures. Calls check the table index width,
arguments, and function-table kind during validation. The runtime checks element
bounds, null entries, and target signatures when executing the call.
Function parameters, results, locals, block signatures, and typed `select` accept
nullable function/external references, including `(ref null func)` and `(ref null extern)`.
`ref.null`, `ref.func`, and `ref.is_null` work in flat and folded syntax. Function
references require a valid index and an outside-body declaration (for example an
export or element segment); a start declaration alone does not declare a reference.
`table.get`, `table.set`, `table.size`, and `table.grow` accept optional named/numeric
table indices, including i64 tables. Growth takes a reference initializer followed by an address-width
size, returns the old size on success or -1 on failure, and preserves the table on failure.
`table.fill`, `table.copy`, `table.init`, and `elem.drop` work in flat and folded
syntax with named/numeric table and element indices. Omitted table indices default
to zero; `table.copy` takes either two table indices or none, while `table.init`
requires its element index. Named element indices include implicit segments generated
by inline table abbreviations. Copy lengths use the smaller table address width;
initialization uses the destination address width with i32 segment offsets and lengths.
Bounds are checked before bulk writes, including zero-length operations. Copies
support overlap, and dropped segments behave as empty segments. Untyped `select`
accepts integer and float operands.
Scripts support anonymous and named modules, `register`, `invoke`,
integer/float/reference `assert_return`, invocation/module `assert_trap`, `assert_unlinkable`,
and `assert_invalid` for elaborated modules in the validator fragment.
Function/table/global/memory imports accept explicit and inline syntax, including inline
re-exports. Imports precede definitions and occupy the first indices in their
respective function/table/global/memory spaces. Registered names are separate from module IDs;
re-registering a name affects future imports while existing instances keep their
addresses. Imports use the shared store and the existing instantiator's runtime
type/limit matching, including a memory/table's current size after growth.
`assert_unlinkable` first validates the source and then checks missing providers,
missing exports, external kinds, and compatible types/limits. Unsupported
dependencies remain unsupported and do not pass a linking assertion.
Globals accept i32/i64/f32/f64 and nullable/nonnullable function/external references, immutable or
`(mut ...)`, named/numeric indices, inline/repeated exports, and imports.
Functions use flat/folded `global.get` and `global.set`; writes require a mutable
global with a matching value type. Script `get` actions read exported globals
from the current or named module. Imported mutable globals share store addresses.
Global initializers are checked incrementally: only imported/previous immutable
globals are readable, along with numeric constants, reference constants, and
i32/i64 `add`/`sub`/`mul` constant expressions. Forward/self references, mutable
reads, nonconstant instructions, and incorrect initializer stacks are rejected.
Function references in global initializers also declare their targets.

Memories accept i32/i64 address widths, named/numeric indices, limits, imports,
and inline/repeated exports. Inline `(memory (data ...))` declarations create
fixed-size memories and implicit active segments; their segments occupy data indices
in declaration order. All integer/float loads/stores, including packed signed/unsigned
loads, work in flat/folded syntax. Memory indices default to zero, offsets to zero,
and alignments to the natural access width. Textual `align=` uses byte powers of two;
validation checks natural alignment bounds and address-width offset limits.
`memory.size`, `memory.grow`, `memory.fill`, `memory.copy`, `memory.init`, and
`data.drop` use the existing runtime semantics, including memory64 and mixed-width
copies. Data segments accept concatenated byte strings, names, passive mode, and
active memory/offset expressions. Active offsets support integer constants,
immutable globals, and integer `add`/`sub`/`mul` constant expressions.
Module trap assertions retain store writes made before initialization traps,
including writes to imported memory, while preserving the current module selection.

Scalar floats have raw `BitVec 32`/`BitVec 64` values, so constants, locals/globals,
loads/stores, and reinterpretations preserve signed zero and NaN payloads.
Decimal/hexadecimal constants are parsed as exact rationals and rounded once;
`inf`, `nan`, and explicit `nan:0x...` payloads are accepted. Script expected results
also support `nan:canonical` and `nan:arithmetic` patterns.
All scalar f32/f64 unary/binary/comparison instructions, integer conversions,
trapping/saturating truncations, promotion/demotion, and reinterpretations execute.
Native `Float32`/`Float` operations supply arithmetic; bit-level handling implements
sign changes, signed-zero min/max, and exact conversion boundaries. Arithmetic
chooses canonical NaNs; sign operations preserve the original payload.

**Proof boundary:** the CLI uses `Wasm.Native.run` and `Wasm.Native.instantiate`
from `Wasm/NativeExecution.lean`. They have no execution soundness theorem.
`Wasm.Native.instantiate` requires `ValidatedModule` and uses certified allocation
preparation, then runs initialization with the native backend. The original
`stepConfiguration`, `runConfiguration`, and `instantiate` APIs and their soundness
theorems still describe the certified reductions; they stop at float arithmetic
and conversion instructions and host invocation. `Wasm/FloatTests.lean` and
`Wasm/SpectestTests.lean` explicitly test this boundary.
Float instruction typing and successful executable validation remain kernel proved;
IEEE arithmetic, literal rounding, and native execution correctness are deferred.
No float correctness assumptions or custom axioms were added.

Script arguments accept `ref.null func`, `ref.null extern`, and `ref.extern N`.
Result assertions compare external identities, and support the
`(ref.null)`, `(ref.func)`, and `(ref.extern)` reference result patterns. Annotated null
results match any null; the `ref.extern` wildcard matches any reference. Result
counts must match exactly. Simple module start declarations are also elaborated.
Trap assertions check the trap outcome; diagnostic strings are not compared because
our runtime currently records no trap reason. Each file starts with a fresh store.
An invalid or unsupported module clears the current instance so later commands cannot silently
invoke an earlier module; named earlier instances remain selectable.

```sh
lake exe wast tests/smoke.wast tests/control.wast tests/types.wast tests/indirect.wast
lake exe wast tests/references.wast tests/table-growth.wast tests/bulk-tables.wast tests/linking.wast
lake exe wast tests/globals.wast tests/memory.wast tests/floats.wast tests/spectest.wast
lake exe wast tests/frontend-gaps.wast
lake exe wast tests/testsuite/i32.wast tests/testsuite/i64.wast
sh tests/check-wast.sh
```

The script runner predefines `spectest` using the
[reference interpreter's host definitions](https://github.com/WebAssembly/spec/blob/main/interpreter/host/spectest.ml):
immutable numeric globals (666 or 666.6), a zeroed memory (1–2 pages), null function tables
(10–20 entries, including `table64`), and all seven print functions. Imports share the same
resources within a script; each new script gets a fresh host store. Explicit registration
can replace the `spectest` binding. Ordinary import type/limit matching remains in force.
Host calls execute only in the native backend, including direct, re-exported, and indirect
calls and start functions. `Report.output` records printed values in execution order;
the CLI displays that trace before the script summary. Output is buffered until the script
finishes. Host execution correctness is deferred alongside native float execution; the
certified runner still stops at host invocation. Unknown host handles remain stuck.
`tests/spectest.wast` covers these behaviors and mismatched imports.

The pinned scripts now exercise integer/float numerics, control flow, calls and locals,
imports/exports/linking, globals, scalar and bulk memory, memory64, references and
scalar/bulk tables, quoted/binary decoding, tail calls, exceptions, GC references,
structs and arrays, mixed recursive composite type validation, standard SIMD, and relaxed SIMD.
Across all 257 unmodified pinned top-level scripts, **65,202 commands pass, 0 fail, and 0 remain
unsupported**; all 257 scripts pass completely. Detailed counts, the fixture revision,
and the license are in
[`tests/testsuite/README.md`](tests/testsuite/README.md). Counts include module commands;
an unsupported module makes its dependent actions unavailable.
`tests/check-wast.sh --full` checks the complete inventory and exact command counts.
`tests/testsuite/inventory.tsv` separates pending scripts from the passing baseline as future
coverage is added; all current entries are complete.
These checks establish regression coverage for the selected fragment, not full Wasm 3.0 conformance.

Module definitions are validated without allocation or start execution and leave
the current instance selected. Explicit instances allocate fresh defined resources
and resolve imports using the registrations in force at instantiation time.
Definitions and instances have separate named environments. The focused
`tests/module-definitions.wast` checks repeated starts, independent globals,
memories and tables, shared imports, and trapping initialization effects.

Quoted text concatenates byte strings before parsing, and is decoded when its
command runs. Module commands and invalid/malformed assertions use the same
source decoder. Malformed assertions check decoding only; a validation error does
not satisfy them. Unsupported features stay unsupported. Folded expressions
require folded operands, and inline signatures require an available referenced type.
`tests/quoted-modules.wast` and `Wasm/TextTests.lean` include positive quoted modules
and cases where malformed assertions must fail.

Binary modules decode directly into the same source `Module` used by text validation,
linking, and instantiation. `Wasm/Binary/Reader.lean` checks bounded signed/unsigned LEB128,
UTF-8 names, and nested byte boundaries. `Wasm/Binary/Decode.lean` handles section ordering,
function/code and data counts, mixed recursive types, scalar instructions, references,
tail calls, exceptions, structs and arrays,
memargs, bulk operations, and all supported module sections. Custom sections are skipped
within their boundaries. Errors carry byte offsets; recognized excluded features report
unsupported coverage. Decoder correctness is deferred.

`Wasm/TypeMatchingAlgorithm.lean` and `Wasm/TypeValidationAlgorithm.lean` contain ordinary
boolean checks for heap/value/result matching and recursive composite type sections.
Their separate success-soundness theorems justify subtyping, scope, type closure,
nonfinal supertype requirements, and parameter contravariance/result covariance.
Typed references work through functions, locals, globals, tables, element segments,
imports, indirect calls, and `call_ref`. Nonnullable locals require definite initialization.
`tests/typed-references.wast` covers source and binary reference operations and typed imports;
`Wasm/TypeAlgorithmTests.lean` includes kernel-reduced successes and subtype rejections.

The CLI prints failures by command ordinal and groups unsupported reasons.
Exit codes are 0 for complete success, 1 for failures or unreadable/malformed
scripts, and 2 for incomplete coverage. Execution defaults to 10,000 semantic steps
per module/action; `--fuel STEPS` raises the budget for long scripts. The pinned
regression uses 4,000,000 steps for generated whole-page memory scans and a
64-frame call-depth limit, raised to 256 for `call`, `call_indirect`, and `call_ref`,
whose valid assertions recurse as far as 200 calls. Native execution defaults to 1,024 active function
frames; `--call-depth FRAMES` changes this independent resource limit.
`assert_exhaustion` requires call-stack resource exhaustion. Running out of fuel
is a failure, never a trap or successful exhaustion assertion. Modules exceeding the runtime's
allocation budget report unsupported coverage; their static validation is independent
of that embedder policy.

Modules are now checked by the ordinary executable function
`Wasm.Validation.validate : Module → Except Error Unit`. The implementation is in
`Wasm/ExecutableValidation.lean`; its separate soundness proof is in
`Wasm/ExecutableValidationSoundness.lean`:

```lean
theorem validate_sound (h : validate module = .ok ()) : module.Valid
```

The checker validates operand types and counts, exact function result stacks,
local and direct/indirect-call indices, initialization, export indices and unique
names, and start signatures. Memory checks include defined/imported limits,
load/store memargs, operand/address types, bulk memory/data indices, and constant
active data offsets. It also checks table limits and constant initializers,
element function indices, active target tables, and offset types. Reference and
scalar/bulk table instructions check operand heap kinds, table address widths, and
`ref.func` declarations, including in unreachable code. The numeric/reference fragment includes nested blocks, loops,
conditionals, and all three branch forms. Each structured body is checked in a
fresh operand frame with its own parameters and results. Branch targets use block
results or loop parameters; `br_table` checks operand subtyping against every target. This
prevents an inner instruction from consuming operands below its frame boundary.

Code after `unreachable`, `return`, `br`, or `br_table` is checked with a polymorphic
stack prefix. Known operand types, extra results, and indices are still checked.
Validation-only stack types include `Types.ValType.bot`. Untyped `select` accepts
numeric or bottom operands and preserves bottom when both operands are unknown,
so the valid `select.wast` reference consumer now succeeds. The rich typing judgments
embed the legacy judgments and permit subtype-compatible stacks without introducing
bottom numeric source/runtime values. The structural recursion budget is computed
from the instruction tree and is distinct
from execution fuel. An upfront feature scan ensures unsupported features are not
classified as invalid just because an earlier supported instruction also fails
validation.

The runner uses `validate_sound` to construct a `ValidatedModule` for
`Native.instantiate`. All successful validations
are backed by a kernel-checked soundness theorem. `assert_invalid` passes when
an elaborated supported module is rejected by the validator and fails when it
is accepted. Elaboration errors do not count as validation rejection. Validation
assertions preserve the current instance and store. Assertion diagnostic strings
are not compared. **Rejection correctness and completeness are not yet proved**;
negative assertions are algorithmic regressions, not proofs of invalidity.

Shared memories/atomics and host modules other than `spectest` remain unsupported.
Proposal, legacy, and custom subdirectory suites are outside this pinned top-level regression.
No unsupported assertion is counted as a pass. Parser/decoder correctness,
rejection correctness/completeness, full Wasm type safety, and native float/host
execution soundness remain future proof work.


## Tail calls, exceptions, and GC

Direct, indirect, and reference tail calls use certified reductions that replace the
caller activation. Exception handling supports tags, `throw`, `throw_ref`, `try_table`,
and its four catch forms. Tag imports preserve identity, and uncaught exceptions have
a distinct execution outcome used by `assert_exception`.

Type contexts contain function, struct, and array composites. Recursive closure,
subtyping, packed storage, field mutability, and function variance are checked by the
ordinary validator with separate success-soundness theorems. Function-only uses
explicitly project a function signature and reject other composite kinds.

GC reference operations currently include `ref.i31`, `i31.get_s`, `i31.get_u`, `ref.eq`,
`any.convert_extern`, and `extern.convert_any`. Conversions preserve nullability and
reference identity. The permitted operations also run in certified constant evaluation.
`ref.test` and `ref.cast` have certified matching and trap reductions.
`br_on_cast` and `br_on_cast_fail` refine branch and fallthrough reference types,
including their distinct nullability, and have certified conditional branch reductions.
Null typing uses the correct bottom for function, external, exception, and GC hierarchies.
`tests/gc-references.wast` covers this fragment; the upstream `ref_null.wast` passes fully.
Struct and array address spaces and instances are modeled. Allocation helpers preserve
existing addresses, and references obtain their closed types from the store. Packed field
storage implements truncation and signed/unsigned reads, with kernel-checked examples.
Struct allocation, defaults, reads, and mutation are supported. Array allocation,
fixed/data/element constructors, reads, mutation, length, fill, copy, and data/element
initialization have certified reductions. Copy snapshots its source, including overlapping
ranges; segment operations respect dropped segments and zero-length bounds.
Allocating constant expressions thread the store through globals, table initializers,
and element expressions. Functions are allocated first so stored `ref.func` values
refer to the final function addresses. The GC allocation budget is 1,048,576 array
elements; exceeding it can leave execution stuck rather than establish a Wasm trap.
The upstream struct, array, reference, recursive type, tail-call, and exception scripts
in the manifest pass completely. `tests/structures.wast` also checks aliases across
globals and tables, packed fields, allocation identity, and forward function references.

The GC rules and executable checks are in `Wasm/StructValidation.lean`,
`Wasm/ArrayValidation.lean`, `Wasm/Structures.lean`, and `Wasm/Arrays.lean`.
`tests/gc-cast-branches.wast` exercises binary cast branches and static rejection,
and Lean tests execute the certified reference runner and inspect soundness axioms.

## SIMD and relaxed SIMD

`v128` is a 128-bit value throughout source types, runtime matching, function signatures,
locals, globals, constant expressions, and struct/array fields. Lane zero occupies the least
significant bits. `VectorOpcode` records the complete SIMD opcode set; `VectorOp` carries
shuffle/lane immediates, a memory index, and a memory argument. Text and binary decoding
recognize vector constants, including the `0xfd` opcode space. Unknown instruction names
are malformed rather than accepted as valid-but-unsupported instructions.

`Vectors.lean` defines integer and bitwise execution equations using arbitrary precision
intermediates. They cover wrapping and saturating arithmetic, masked shifts, signed/unsigned
comparisons, population counts, masks, shuffle/swizzle, narrowing/widening, pairwise addition,
extended multiplication, dot products, Q15 rounding/saturation, and floating bitwise abs/neg.
`VectorStepper.lean` adds vector memory operations: full loads/stores, extending and splat
loads, zero loads, and lane loads/stores. Address sums do not wrap before bounds checks.
The certified configuration stepper includes vector reductions under labels, handlers, and
activation frames. `stepVectors_sound` and resource preservation are kernel checked.

`VectorValidation.lean` defines declarative stack effects and immediate/memory constraints.
The ordinary executable checker has a separate success-soundness theorem and participates
in `validate_sound`; malformed lane literals and invalid lane bounds remain distinct checks.
`NativeVector.lean` shares the scalar native floating arithmetic and conversion backend.
Vector NaN expectations inspect individual lanes, and script expectations support `either`.
Native floating arithmetic remains outside certified execution soundness.

Relaxed SIMD chooses the specification's deterministic profile: swizzle zeros out-of-range
indices, truncations saturate, lane selection uses bit selection, Q15 uses ordinary saturating
rounding, and multiply-add uses separate multiplication and addition. Min/max use the ordinary
Wasm operations; dot products use signed lane arithmetic. Result alternatives are checked
without claiming that this profile enumerates every allowed relaxed result.

The regression includes all 59 standard SIMD and 7 relaxed SIMD scripts. `VectorTests.lean`
checks arithmetic overflow, signed shifts, Q15 saturation, narrowing, dot product overflow,
and invalid immediates/alignment. `tests/vectors.wast` checks vectors across calls, globals,
GC storage, memory64 overflow traps, and lane access at the last memory byte.
