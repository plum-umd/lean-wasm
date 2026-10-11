# Recorded array heap measurements

Run command:

```sh
python3 tests/benchmark-fast.py --output benchmarks/array-heap --hardware 'Apple M1'
```

See [summary.md](summary.md), [samples.csv](samples.csv), and [metadata.json](metadata.json).
The summary's timing paragraph was clarified after generation to distinguish prepared-store
primitive operations from complete executor cases. The measured source hashes are unchanged.

Seven samples per backend, eleven workloads, five sizes: 770 retained samples. Each backend
and case also has one discarded warm-up. No conformance run or build ran during these samples.
All runs verified results outside the timed region. Setup excludes parsing, validation,
instantiation, workload construction, and primitive-store preparation. Complete executor cases
measure input and output representation conversions separately. These are synthetic workloads.

The allocation implementation defers mutation through dispatch and the fuel runner, allowing
Lean to consume the old configuration before `Array.push`. The fast allocation loop grows
approximately linearly over the measured sizes. The control baseline remains essentially
unchanged, while early-address reads are about 1% slower. Speedup depends on heap use and size.

Validation:

```sh
lake build
sh tests/check-wast.sh --full --testsuite /Users/dvanhorn/git/lean-wasm/.cache/testsuite
```

Both passed. The conformance suite covers the existing `wast` backend (257 scripts / 65,202
commands); fast executor coverage comes from the default-build differential tests and the
kernel-checked reduction correspondence, rather than routing the conformance CLI through fast.
