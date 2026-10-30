# Resumable host calls

Import `Wasm.Host` (also exported by `Wasm`) for a pure embedding API over the
certified configuration runner. Host functions are symbolic `.host identifier`
or `.hostTyped identifier type` instances in the store. The library never calls
native callbacks or performs host IO.

`runUntilHost fuel config` runs ordinary Wasm execution and returns a state plus:

- `.pending call`: a recognized host invocation with scalar parameters/results.
- `.unsupportedHost call`: a recognized host invocation whose signature includes
  references or vectors.
- `.ordinary status`: the existing `.finished`, `.trapped`, `.exception`,
  `.exhausted`, or `.stuck` outcome.

Completion is distinct from unsupported/stuck execution. An unknown function
address, malformed invocation, or inconclusive runtime matching check remains
stuck. A host identifier needs no library registration: it becomes a request for
the embedder to dispatch, including identifiers the embedder does not recognize.

## Observation and replies

`call.request` contains the resolved function address, symbolic identifier,
signature, arguments in parameter order, calling frame, tail-call flag, and call
form. `call.source` retains the entire configuration, including the store.
`call.context` saves the operand prefixes, continuations, labels, handlers, and
suspended frames. Its proof field certifies that the invocation occupies exactly
that context in the source configuration.

`observeHostCall config` inspects an already lowered invocation without taking
ordinary steps. Source `call` instructions first need ordinary execution fuel
for lowering. Observation performs no effects and consumes no fuel. Repeated
observation is safe. A pending value can be retained while other computations
run, then resumed later.

Use `resumeHostCall call (.values results)` to validate arity and value types
before replacing the invocation with results. It returns
`Except HostReplyError Configuration`. Wrong arity, wrong types, and reference
values supplied for scalar results return `.invalidResults`; a non-scalar
signature returns `.unsupportedSignature`. Rejection cannot modify or consume
the immutable pending computation. Successful tail replies use the existing
tail-activation machinery to discard the caller's activation and continuations.

For example, after `config` reaches an imported `(i64) -> i64` function:

```lean
let result := Wasm.runUntilHost 100 config
match result.status with
| .pending call =>
  -- Dispatch using call.request.identifier and call.request.arguments.
  match Wasm.resumeHostCall call (.values [.i64 42]) with
  | .ok resumed =>
    let continued := Wasm.runUntilHost 100 resumed
    -- Inspect continued.status, retaining continued.state if fuel runs out.
    ...
  | .error error => ...
| .unsupportedHost call => ...
| .ordinary status => ...
```

The executable regressions in `Wasm/HostTests.lean` include a nested function
that receives `42` from its import and returns `43`, with its locals and the
surrounding operand stack preserved.

## Checked guest-memory access and write replies

Import `Wasm.HostMemory` (also exported by `Wasm`) for checked byte reads and
transactional byte-write replies. These operations use existing linear memories
in the current runtime model, which does not model shared memories.

`readHostMemory call memoryIndex offset count` reads from the saved snapshot and
returns `Except HostMemoryError (Array Byte)`. `memoryIndex` is explicitly
relative to `call.request.caller.module`, including when a nested function uses a
different memory mapping from the outer frame. Imported memories and aliases
resolve through that mapping to their store addresses. The API never assumes
that the memory is module index 0 or store address 0.

Offsets and lengths are mathematical `Nat` values. The check requires
`offset + count ≤ memory.bytes.size`, without machine-integer wraparound or
narrowing to the memory's address width. This works for both memory32 and
memory64. A zero-length range at the end is valid; one past the end is invalid.
When decoding guest pointers from scalar arguments, preserve their unsigned
value (for example, `Value.unsigned`) rather than performing wrapping arithmetic
in the embedder first.

To return scalar results and memory effects together, supply a list of
`HostMemoryWrite` records to `resumeHostCallWithMemory`:

```lean
let write : Wasm.HostMemoryWrite :=
  { memoryIndex := 0, offset := 4, bytes := #[42, 43, 44] }
match Wasm.resumeHostCallWithMemory call [.i32 3] [write] with
| .ok resumed =>
  let continued := Wasm.runUntilHost 100 resumed
  ...
| .error error => ...
```

Each record names a caller-relative memory index, byte offset, and byte array.
Writes are staged in a private immutable store in list order. Later writes win
where ranges overlap, including when different module indices alias one store
memory. All writes must pass bounds and lookup checks. Result arity/types are
checked against the staged store, and only a completely successful reply
returns a changed configuration. Errors never return partially applied writes;
the original pending call and its memory snapshot remain reusable.

Read errors distinguish `.unknownMemory index` (no such caller memory),
`.missingMemory address` (the mapping points outside the store), and
`.outOfBounds index offset count`. Write replies wrap those as
`HostMemoryReplyError.memory`; signature/result failures use
`HostMemoryReplyError.reply` with the existing `HostReplyError` cases. Memory
checks precede result checks, so an invalid memory effect is reported first.
Unsupported signatures are rejected before processing effects.

The implementation cannot grow or allocate memories, change their types or
lengths, or modify any other store component. It preserves the saved execution
context and the existing tail-call behavior. Memory reads perform no effects
and do not consume execution fuel; applying host effects does not consume
ordinary-step fuel either. This interface supports successful scalar returns
with writes. To report a host trap, use the existing `.trap` reply, which retains
the original store. Write-and-trap replies and host-thrown guest exceptions are
not currently offered.

`Wasm/HostMemoryTests.lean` exercises an imported buffer-filling function inside
a nested Wasm function: the host writes bytes and the resumed guest reads them
through ordinary Wasm loads. Tests also cover multiple memories, aliases,
overlapping writes, tail calls, invalid ranges/results, large offsets/lengths,
and retries after rejection.

## Embedder responsibilities and limits

The current boundary supports `i32`, `i64`, `f32`, and `f64` parameters/results,
including empty and multi-value signatures. Direct, reference, indirect, and
all corresponding tail-call paths are supported, in both structural and nominal
administrative forms. Reference call matching uses the existing bounded runtime
checker; an inconclusive check does not manufacture a host request. Floating
values are transported as bits; this API does not add floating-point arithmetic
to the certified evaluator.

`resumeHostCall` leaves the **entire store unchanged**. The embedder can inspect
`call.source.store` and use `call.request.caller.module` to resolve the calling
instance's memories and resources. `resumeHostCallWithMemory` permits the checked
byte writes described above. Reference-valued replies, allocation, general store
mutation, and host-thrown guest exceptions remain future extensions. Neither
interface accepts arbitrary replacement stores.

A host-side error or unrecognized identifier is an embedder decision: retain the
request while reporting/retrying externally, terminate the embedding computation,
or explicitly reply `.trap`. That reply becomes a Wasm trap, propagating through
the saved contexts; it is not a catchable guest exception. An asynchronous wait
is represented by retaining the pending call, not by fuel exhaustion or a trap.

Pending calls are immutable, reusable values. The API gives no linear-use
guarantee: the embedder must prevent accidental duplicate servicing and must
decide whether replay is meaningful for its external effects. Resumption always
uses the saved store snapshot. Concurrent computations that need shared mutable
resources require a separately specified synchronization/store-update policy.

Fuel counts bounded ordinary semantic execution, including call lowering and
tail unwinding after a reply. On `.ordinary .exhausted`, continue with the
returned `state` rather than restarting the initial configuration. Fuel does
not bound elapsed time, host work, or total allocation. Host observation and
reply insertion do not spend ordinary-step fuel.

## Checked correspondence

`HostSite` independently specifies a resolved invocation with typed arguments
in an evaluation context. `HostSite.decompose` proves exact reconstruction of
the saved code. `observeHostCall_sound` proves successful detection corresponds
to that relation. `HostBoundaryStep` defines explicit returned-value and trap
transitions, with scalar-signature and result-typing premises.
`resumeHostCall_sound` proves executable resumption implements those rules, and
`resumeHostCall_store_preserved` proves it retains the store.

`runUntilHost_sound` preserves the existing `ConfigSteps` guarantee for all
ordinary execution before suspension. `runUntilHost_pending_source` identifies
the saved request's source with the returned state. `HostExecutionSteps` permits
mixed ordinary and explicit host-reply traces; embedders can impose their own
relation on the observable requests/replies to model permitted host behavior.
`runUntilHost_resume_sound` combines ordinary execution and a successful reply
into one such mixed trace.
These results establish correspondence to the explicit boundary semantics;
they do not certify external IO effects or assert full Wasm type safety.

`HostMemoryAccess`, `HostMemoryRead`, and `HostMemoryEffects` independently
specify accessible ranges, read contents, and ordered memory writes.
`HostMemoryBoundaryStep` treats those writes as host-function effects, separate
from `ConfigStep`. `readHostMemory_sound` and `resumeHostCallWithMemory_sound`
prove correspondence to those relations. Successful writes preserve memory
types and sizes (`HostMemoryEffects.shape`), `MemoryInst.Valid` assuming it held
initially (`memories_valid`), and every non-memory store component
(`other_components`). Existing runtime value/argument typing is also preserved.
`bytes_outside` proves all bytes outside the selected ranges remain unchanged,
including across aliasing and multiple writes; `unwritten_memory` retains whole
memories that no write selects.

`resumeHostCallWithMemory_spec` identifies the effects and the exact saved frame
and continuation used by successful resumption.
`resumeHostCallWithMemory_bytes_outside` exposes the byte-preservation guarantee
directly for executable replies. `runUntilHost_resume_memory_sound` connects a
runner suspension and an effectful reply through `HostMemoryExecutionSteps`.
The old boundary and its store-preservation proofs remain unchanged;
`resumeHostCallWithMemory_empty` proves that an empty write list behaves like
the original scalar-reply operation (with errors wrapped in the new error type).

Existing `Invokes`, `ConfigStep`, `stepConfiguration`, and `runConfiguration`
are unchanged. Existing callers retain their previous behavior, including
ordinary `.stuck` results at host invocations when using the old runner.
