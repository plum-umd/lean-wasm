# Upstream conformance scripts

Unmodified files from https://github.com/WebAssembly/testsuite at revision
`b464a4cd100d98175ae6e3890db89a2e6c8302f7`.
The upstream Apache 2.0 license is included in `LICENSE`.

Run from the project directory:

```sh
lake exe wast tests/testsuite/i32.wast tests/testsuite/i64.wast
lake exe wast --fuel 4000000 tests/testsuite/memory_fill.wast tests/testsuite/memory_copy.wast
sh tests/check-wast.sh
```

Current command counts (including module commands):

| Script | Passed | Failed | Unsupported |
| --- | ---: | ---: | ---: |
| i32.wast | 458 | 0 | 2 |
| i64.wast | 414 | 0 | 2 |
| ref_null.wast | 0 | 0 | 34 |
| ref_func.wast | 17 | 0 | 0 |
| ref_is_null.wast | 2 | 0 | 20 |
| table_get.wast | 16 | 0 | 0 |
| table_set.wast | 26 | 0 | 0 |
| table_size.wast | 39 | 0 | 0 |
| table_grow.wast | 58 | 0 | 0 |
| table_fill.wast | 45 | 0 | 0 |
| table_copy.wast | 1728 | 0 | 0 |
| table_init.wast | 790 | 0 | 2 |
| global.wast | 117 | 0 | 7 |
| memory.wast | 86 | 0 | 4 |
| memory_size.wast | 42 | 0 | 0 |
| memory_grow.wast | 51 | 0 | 0 |
| memory_fill.wast | 100 | 0 | 0 |
| memory_copy.wast | 4450 | 0 | 0 |
| memory_init.wast | 250 | 0 | 0 |
| f32.wast | 2512 | 0 | 2 |
| f64.wast | 2512 | 0 | 2 |
| conversions.wast | 619 | 0 | 0 |
| float_misc.wast | 471 | 0 | 0 |
| float_literals.wast | 99 | 0 | 80 |
| f32_bitwise.wast | 364 | 0 | 0 |
| f64_bitwise.wast | 364 | 0 | 0 |
| f32_cmp.wast | 2407 | 0 | 0 |
| f64_cmp.wast | 2407 | 0 | 0 |
| block.wast | 208 | 0 | 15 |
| br.wast | 97 | 0 | 0 |
| br_if.wast | 118 | 0 | 1 |
| br_table.wast | 24 | 0 | 162 |
| call.wast | 89 | 0 | 2 |
| call_indirect.wast | 159 | 0 | 13 |
| local_get.wast | 36 | 0 | 0 |
| local_set.wast | 53 | 0 | 0 |
| local_tee.wast | 97 | 0 | 1 |
| loop.wast | 106 | 0 | 15 |
| if.wast | 217 | 0 | 24 |
| return.wast | 84 | 0 | 0 |
| select.wast | 153 | 1 | 3 |
| nop.wast | 88 | 0 | 0 |
| unreachable.wast | 64 | 0 | 0 |
| const.wast | 702 | 0 | 76 |
| func.wast | 151 | 0 | 24 |
| forward.wast | 5 | 0 | 0 |
| fac.wast | 7 | 0 | 1 |
| int_exprs.wast | 108 | 0 | 0 |
| float_exprs.wast | 927 | 0 | 0 |
| float_memory.wast | 90 | 0 | 0 |
| address.wast | 259 | 0 | 1 |
| align.wast | 112 | 0 | 53 |
| load.wast | 84 | 0 | 13 |
| store.wast | 61 | 0 | 7 |
| memory_trap.wast | 182 | 0 | 0 |
| imports.wast | 143 | 0 | 75 |
| exports.wast | 96 | 0 | 1 |
| data.wast | 63 | 0 | 5 |
| elem.wast | 119 | 0 | 35 |
| start.wast | 19 | 0 | 1 |
| type.wast | 1 | 0 | 2 |
| linking.wast | 120 | 0 | 43 |
| endianness.wast | 69 | 0 | 0 |
| func_ptrs.wast | 36 | 0 | 0 |
| address64.wast | 242 | 0 | 0 |
| align64.wast | 111 | 0 | 46 |
| call_indirect64.wast | 2 | 0 | 0 |
| endianness64.wast | 69 | 0 | 0 |
| float_memory64.wast | 90 | 0 | 0 |
| load64.wast | 85 | 0 | 13 |
| memory_trap64.wast | 172 | 0 | 0 |
| memory64-imports.wast | 78 | 0 | 0 |
| **Total** | **26240** | **1** | **787** |

The original 28-script group exits 2 for incomplete coverage. The broader 44-script
audit exits 1 because `select.wast` has one real validation failure. Unsupported
assertions never count as passes. Successful validation has a kernel-checked soundness theorem. Supported
`assert_invalid` commands exercise algorithmic rejection, whose correctness
and completeness are not yet proved. Unsupported syntax and features remain
separate from rejection.

All pinned scalar float bitwise/comparison/conversion/miscellaneous scripts pass.
`f32.wast` and `f64.wast` each have two unsupported malformed assertions.
`float_literals.wast` has 78 malformed assertions and one binary module with its
dependent action unsupported. Decimal/hex constants and NaN payloads are supported.
The focused `../floats.wast` tests signed zero, NaN preservation, memory, shared
imports, nested calls/control, initialization, and typing failures.

Float validation success remains kernel proved. The CLI now uses the native float
backend, whose execution correctness and IEEE arithmetic are deliberately unproved.
The certified execution APIs remain available and stop at float numeric operators;
no custom float axioms or correctness assumptions were introduced.

`table_get`, `table_set`, `table_size`, `table_grow`, `table_fill`, and `table_copy`
are fully covered. `table_init` has a typed/nonnullable reference table module and
its dependent action unsupported. There is no separate `elem_drop.wast` at this
pinned revision; `table_init.wast` exercises it. Other reference gaps involve
GC/typed/exception heaps. `ref_func.wast` is fully covered.

`global.wast` now only needs malformed assertions. Unsupported modules block their dependent actions. Shared globals are
covered separately by `../globals.wast` and `../floats.wast`. The predefined `spectest`
host unlocks 64 commands; `../spectest.wast` checks its globals, shared resources,
print trace, indirect calls, initialization, and mismatched imports. Host calls use the
unproved native backend; certified execution remains unchanged.

Memory size/grow/fill/copy/init scripts are fully covered. `memory.wast` has three
malformed assertions and one script-level `module definition` unsupported.
The focused `../memory.wast` additionally covers memory64 and mixed-width copies.
Large generated whole-page fill/copy loops need `--fuel 4000000`; exhaustion at the
default 10000-step budget is a failure. Allocation-budget limits are reported as
unsupported rather than validation errors.

The broader audit adds 44 unmodified scripts for control flow, calls and locals,
function signatures, scalar expressions, imports/exports/linking, data/elements,
start functions, loads/stores/alignment, and memory64. Nineteen of these pass completely.
Other scripts combine implemented functionality with malformed assertions, exhaustion
assertions, module definition/instance syntax, tags, typed references, or GC heaps.
`br_table.wast` illustrates the distinction: a typed-reference table declaration blocks
161 dependent commands, although ordinary branch-table execution is implemented.

The expansion fixed numeric type-index validation, repeated typed-select result
annotations, explicit nullable table initializers, externref element segments,
immutable-global element expressions, and extended element offsets. Table initializers
are checked with imported globals only; element initialization uses the completed global
context. All successful module validation remains kernel proved. The memory growth and
allocation policy now permits 1024 pages (64 MiB) per memory so call-expression scripts
can grow by 306 pages; this changes embedder resource policy, not Wasm's semantic limits.
`../frontend-gaps.wast` covers the frontend fixes and rejected initializer/type cases.

Known failure: `select.wast`, command 132, is a valid module:

```wat
(module
  (func (drop (ref.is_null (select (unreachable) (i32.const 1))))))
```

After `unreachable`, both select values have the bottom type. Untyped select must preserve
that bottom result so `ref.is_null` can consume it. Our current declarative instruction
rule and executable checker restrict untyped select results to concrete numeric types,
so validation rejects this module. This is a completeness gap; `validate_sound` does not
claim completeness. The failure is retained as failed, not relabeled unsupported.

`expected-broader.txt` records the measured counts. `../check-wast.sh` verifies those
counts and CLI exit codes, including this known failure; a successful regression check
means the recorded baseline agrees, not that every upstream assertion passed.
