# Recorded explicit stack measurements

Historical comparison, measured before executor unification. The legacy runners and
comparison harness are preserved in Git at `349e4c8`, rather than in the current implementation.
Reproduce the command below from that revision in a separate checkout.

Run command:

```sh
python3 tests/benchmark-stack.py --hardware 'Apple M1'
```

See [summary.md](summary.md), [samples.csv](samples.csv), and [metadata.json](metadata.json).
Seven repetitions, three backends, 46 cases: 966 retained samples. Each backend/case has one
discarded warm-up. Order rotates and reverses, and each sample uses a fresh process. No build
or conformance run runs concurrently with timing. Results and heap/exception counts are checked
outside the timed region. Setup, parsing, validation and instantiation are excluded; both
boundary conversions are measured separately and included in the total speedup column.

The heap-only backend is `Wasm.Fast.runConfiguration`; the machine backend is
`Wasm.Fast.Machine.run`. Heap cases vary iteration count while keeping code size fixed.
Depth cases keep the leaf loop at 1,000 iterations, varying enclosing blocks, calls, handlers
or a tail-call chain. Calls include entry and return overhead, and function instances retain
list storage. The unwind case traverses empty handlers with an uncaught exception after the
loop; it measures sustained work under handlers as well as unwinding. Tail calls keep active
call depth bounded while the forwarding chain length grows.

The machine stores operands and suspended contexts separately and dispatches to one certified
instruction family. Context entry and value movement preserve the reconstructed configuration
exactly. These administrative moves terminate by a strictly decreasing measure of focused
code size. Semantic steps correspond to one original reduction step and consume one fuel
unit. Complete runs and reported terminal results also have kernel-checked correspondence.
A general reverse simulation/no-new-stuck theorem remains open; differential regression tests
check exact optional steps, configurations, statuses, fuel boundaries and resumed execution.

Validation: `lake build` passed, including the machine regression tests and standard-axiom
checks. The dispatch matrix compares first steps and five-step runs across operands and three
context shapes; complete fixtures additionally exercise all certified instruction families,
multi-value branches, calls, tail calls and exception references. Generated C was inspected:
full reconstruction and the termination measure are absent from the execution loop, and the
old focused machine is released before a deferred struct change is committed. The run loop
is compiled as a tail loop.

The existing `wast` CLI still uses its original backend. Its complete pinned conformance run
passed during the preceding heap phase (257 scripts / 65,202 commands); these measurements
and differential tests exercise the separate certified executors. All workloads are synthetic
and require no external application checkout. Source hashes identify the measured working tree
on top of the recorded heap-phase commit.

One result line in `MachineDispatch.lean` was wrapped to 100 columns after the measured
executable was built. Metadata retains its original and delivered hashes and the generated C
hash, so this formatting adjustment is explicit rather than changing the measured source hash.
Rebuilding after that line wrap produced identical generated C.
