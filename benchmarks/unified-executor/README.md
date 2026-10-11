# Unified execution machine measurements

Run command:

```sh
python3 tests/benchmark-fast.py --output benchmarks/unified-executor --hardware 'Apple M1'
```

Both certified and native policies use the same explicit machine and `Machine.execute` fuel
loop. Native hooks add unproved floating-point/SIMD/host operations and activation-depth checks.
These workloads need no native operations: the policy comparison measures integration overhead,
not two independent executor implementations.

See [summary.md](summary.md), [samples.csv](samples.csv), and [metadata.json](metadata.json).
Seven repetitions, two policies, 46 cases give 644 retained samples, plus one discarded warm-up
per policy/case. Each sample runs in a fresh process; policy order alternates. Setup and
correctness checks are outside timing. Input and output representation conversions are measured
separately. No build or conformance run runs concurrently with recorded samples. Source hashes
identify the working tree on top of the pushed explicit-stack milestone `349e4c8`.

The original list-heap runner, intermediate heap-only runner, native nested-code scanner and
native fuel loop have been removed. Public configuration APIs convert at boundaries and retain
their existing certified soundness/finished/trapped theorem statements. Stateful embedders can
retain a `Fast.Machine` across runs, including through `Native.runMachine`. Runtime code uses
no full configuration reconstruction inside the loop, and releases the input before committing
a deferred struct update.

Validation passed:

```sh
lake build
sh tests/check-wast.sh --full --testsuite /Users/dvanhorn/git/lean-wasm/.cache/testsuite
```

The complete pinned conformance suite passed all 257 scripts and 65,202 commands, with zero
failures and zero unsupported commands, on the unified machine. The harness also passed the
mixed machine integration fixture: nine commands combining heap references, mutable globals,
native arithmetic, exception payloads, ordinary calls, reference calls, tail calls and host
output. Lean regressions check API boundaries, fuel composition, resumption, instruction-family
fixtures, and native output ordering/no speculative or repeated output. Correctness proofs
use only standard Lean axioms. General completeness is unproved, as for the original executor;
native execution extensions retain their previous unproved status.

All workloads are synthetic. Historical old/new comparisons remain in
[../explicit-stack](../explicit-stack/README.md) and [../array-heap](../array-heap/README.md),
and their original harnesses are reproducible from the recorded Git revisions. Current code
contains only the machine implementation.

After the complete conformance run, the certified hot path was simplified to avoid an extra
per-step extension wrapper. `Machine.execute_succ` proves exactly the same step recurrence
for every hook policy; this equivalence uses only standard Lean axioms. The final build and
focused host/float/control/exhaustion/mixed integration scripts passed after that change.
The recorded timings use the final implementation.

At 16,000 iterations, certified/native medians are 60.4/61.4 ms for allocation,
73.4/74.0 ms for allocation plus reads, 253.6/253.9 ms for linked structures, and
63.3/63.9 ms for control. At depth 256 with 1,000 iterations, blocks take 4.1/4.1 ms,
handlers 4.2/4.2 ms and suspended calls 4.6/4.7 ms. Allocation scales approximately
linearly over the measured sizes, and loop time remains nearly flat over context depth.
The shared loop has modest overhead relative to the historical certified-only machine;
these are separate recorded runs, rather than a simultaneous old/new comparison.
