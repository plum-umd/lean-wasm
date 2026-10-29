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

## Embedder responsibilities and limits

The current boundary supports `i32`, `i64`, `f32`, and `f64` parameters/results,
including empty and multi-value signatures. Direct, reference, indirect, and
all corresponding tail-call paths are supported, in both structural and nominal
administrative forms. Reference call matching uses the existing bounded runtime
checker; an inconclusive check does not manufacture a host request. Floating
values are transported as bits; this API does not add floating-point arithmetic
to the certified evaluator.

Host replies leave the **entire store unchanged**. The embedder can inspect
`call.source.store` and use `call.request.caller.module` to resolve the calling
instance's memories and resources. Store mutation, reference-valued replies,
allocation, and host-thrown guest exceptions are future extensions. There is no
resulting-store argument and no certification of arbitrary external store edits.

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

Existing `Invokes`, `ConfigStep`, `stepConfiguration`, and `runConfiguration`
are unchanged. Existing callers retain their previous behavior, including
ordinary `.stuck` results at host invocations when using the old runner.
