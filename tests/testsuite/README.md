# Upstream conformance scripts

Unmodified files from https://github.com/WebAssembly/testsuite at revision
`b464a4cd100d98175ae6e3890db89a2e6c8302f7`.
The upstream Apache 2.0 license is included in `LICENSE`.

Run from the project directory:

```sh
lake exe wast tests/testsuite/i32.wast tests/testsuite/i64.wast
lake exe wast --fuel 4000000 tests/testsuite/memory_fill.wast tests/testsuite/memory_copy.wast
lake exe wast --fuel 4000000 --call-depth 256 tests/testsuite/call_ref.wast
sh tests/check-wast.sh --full
```

The regression covers **all 257 top-level scripts**: **65,202 passed commands,
0 failed, 0 unsupported**. This includes 191 non-SIMD scripts, 59 standard SIMD scripts,
and 7 relaxed SIMD scripts. Every vendored fixture is byte-identical to the pinned archive.
Proposal, legacy, and custom subdirectory suites are outside this inventory.

`inventory.tsv` records every script, its family, and complete/pending status. Passing scripts
are promoted into `expected-broader.txt` with measured counts; pending scripts do not weaken
that baseline. `../check-wast.sh --full` also runs pending entries and distinguishes failures
(exit 1) from incomplete coverage (exit 2). All current entries are complete. Both harness
modes check exact counts, the inventory, and exit codes. Unsupported assertions never count
as passes.

Execution fuel is 4,000,000 steps for generated memory scans. Original scripts retain their
recorded call-depth limits; newly covered scripts use 256. The CLI defaults to 10,000 steps
and 1,024 frames. Call-stack exhaustion satisfies `assert_exhaustion`; fuel exhaustion cannot.
These are independent embedder resource limits.

| Script | Passed | Failed | Unsupported |
| --- | ---: | ---: | ---: |
| address.wast | 260 | 0 | 0 |
| address0.wast | 92 | 0 | 0 |
| address1.wast | 127 | 0 | 0 |
| address64.wast | 242 | 0 | 0 |
| align.wast | 165 | 0 | 0 |
| align0.wast | 5 | 0 | 0 |
| align64.wast | 157 | 0 | 0 |
| annotations.wast | 74 | 0 | 0 |
| array.wast | 54 | 0 | 0 |
| array_copy.wast | 35 | 0 | 0 |
| array_fill.wast | 30 | 0 | 0 |
| array_init_data.wast | 46 | 0 | 0 |
| array_init_elem.wast | 36 | 0 | 0 |
| array_new_data.wast | 28 | 0 | 0 |
| array_new_elem.wast | 24 | 0 | 0 |
| binary-gc.wast | 1 | 0 | 0 |
| binary-leb128.wast | 91 | 0 | 0 |
| binary.wast | 127 | 0 | 0 |
| binary0.wast | 7 | 0 | 0 |
| binary_leb128_64.wast | 2 | 0 | 0 |
| block.wast | 223 | 0 | 0 |
| br.wast | 97 | 0 | 0 |
| br_if.wast | 119 | 0 | 0 |
| br_on_cast.wast | 37 | 0 | 0 |
| br_on_cast_fail.wast | 37 | 0 | 0 |
| br_on_non_null.wast | 12 | 0 | 0 |
| br_on_null.wast | 10 | 0 | 0 |
| br_table.wast | 186 | 0 | 0 |
| bulk.wast | 117 | 0 | 0 |
| bulk64.wast | 70 | 0 | 0 |
| call.wast | 91 | 0 | 0 |
| call_indirect.wast | 172 | 0 | 0 |
| call_indirect64.wast | 2 | 0 | 0 |
| call_ref.wast | 35 | 0 | 0 |
| comments.wast | 8 | 0 | 0 |
| const.wast | 778 | 0 | 0 |
| conversions.wast | 619 | 0 | 0 |
| custom.wast | 11 | 0 | 0 |
| data.wast | 68 | 0 | 0 |
| data0.wast | 7 | 0 | 0 |
| data1.wast | 14 | 0 | 0 |
| data_drop0.wast | 11 | 0 | 0 |
| elem.wast | 154 | 0 | 0 |
| endianness.wast | 69 | 0 | 0 |
| endianness64.wast | 69 | 0 | 0 |
| exports.wast | 97 | 0 | 0 |
| exports0.wast | 8 | 0 | 0 |
| extern.wast | 18 | 0 | 0 |
| f32.wast | 2514 | 0 | 0 |
| f32_bitwise.wast | 364 | 0 | 0 |
| f32_cmp.wast | 2407 | 0 | 0 |
| f64.wast | 2514 | 0 | 0 |
| f64_bitwise.wast | 364 | 0 | 0 |
| f64_cmp.wast | 2407 | 0 | 0 |
| fac.wast | 8 | 0 | 0 |
| float_exprs.wast | 927 | 0 | 0 |
| float_exprs0.wast | 14 | 0 | 0 |
| float_exprs1.wast | 3 | 0 | 0 |
| float_literals.wast | 179 | 0 | 0 |
| float_memory.wast | 90 | 0 | 0 |
| float_memory0.wast | 30 | 0 | 0 |
| float_memory64.wast | 90 | 0 | 0 |
| float_misc.wast | 471 | 0 | 0 |
| forward.wast | 5 | 0 | 0 |
| func.wast | 175 | 0 | 0 |
| func_ptrs.wast | 36 | 0 | 0 |
| global.wast | 124 | 0 | 0 |
| i16x8_relaxed_q15mulr_s.wast | 3 | 0 | 0 |
| i31.wast | 73 | 0 | 0 |
| i32.wast | 460 | 0 | 0 |
| i32x4_relaxed_trunc.wast | 1 | 0 | 0 |
| i64.wast | 416 | 0 | 0 |
| i8x16_relaxed_swizzle.wast | 6 | 0 | 0 |
| id.wast | 7 | 0 | 0 |
| if.wast | 241 | 0 | 0 |
| imports.wast | 218 | 0 | 0 |
| imports0.wast | 8 | 0 | 0 |
| imports1.wast | 5 | 0 | 0 |
| imports2.wast | 20 | 0 | 0 |
| imports3.wast | 10 | 0 | 0 |
| imports4.wast | 16 | 0 | 0 |
| inline-module.wast | 1 | 0 | 0 |
| instance.wast | 23 | 0 | 0 |
| int_exprs.wast | 108 | 0 | 0 |
| int_literals.wast | 51 | 0 | 0 |
| labels.wast | 29 | 0 | 0 |
| left-to-right.wast | 96 | 0 | 0 |
| linking.wast | 163 | 0 | 0 |
| linking0.wast | 6 | 0 | 0 |
| linking1.wast | 14 | 0 | 0 |
| linking2.wast | 11 | 0 | 0 |
| linking3.wast | 14 | 0 | 0 |
| load.wast | 97 | 0 | 0 |
| load0.wast | 3 | 0 | 0 |
| load1.wast | 18 | 0 | 0 |
| load2.wast | 38 | 0 | 0 |
| load64.wast | 98 | 0 | 0 |
| local_get.wast | 36 | 0 | 0 |
| local_init.wast | 10 | 0 | 0 |
| local_set.wast | 53 | 0 | 0 |
| local_tee.wast | 98 | 0 | 0 |
| loop.wast | 121 | 0 | 0 |
| memory-multi.wast | 6 | 0 | 0 |
| memory.wast | 90 | 0 | 0 |
| memory64-imports.wast | 78 | 0 | 0 |
| memory64.wast | 69 | 0 | 0 |
| memory_copy.wast | 4450 | 0 | 0 |
| memory_copy0.wast | 29 | 0 | 0 |
| memory_copy1.wast | 14 | 0 | 0 |
| memory_copy64.wast | 4450 | 0 | 0 |
| memory_fill.wast | 100 | 0 | 0 |
| memory_fill0.wast | 16 | 0 | 0 |
| memory_fill64.wast | 100 | 0 | 0 |
| memory_grow.wast | 51 | 0 | 0 |
| memory_grow64.wast | 49 | 0 | 0 |
| memory_init.wast | 250 | 0 | 0 |
| memory_init0.wast | 13 | 0 | 0 |
| memory_init64.wast | 250 | 0 | 0 |
| memory_redundancy.wast | 8 | 0 | 0 |
| memory_redundancy64.wast | 8 | 0 | 0 |
| memory_size.wast | 42 | 0 | 0 |
| memory_size0.wast | 8 | 0 | 0 |
| memory_size1.wast | 15 | 0 | 0 |
| memory_size2.wast | 21 | 0 | 0 |
| memory_size3.wast | 2 | 0 | 0 |
| memory_size_import.wast | 7 | 0 | 0 |
| memory_trap.wast | 182 | 0 | 0 |
| memory_trap0.wast | 14 | 0 | 0 |
| memory_trap1.wast | 168 | 0 | 0 |
| memory_trap64.wast | 172 | 0 | 0 |
| names.wast | 486 | 0 | 0 |
| nop.wast | 88 | 0 | 0 |
| obsolete-keywords.wast | 11 | 0 | 0 |
| ref.wast | 13 | 0 | 0 |
| ref_as_non_null.wast | 7 | 0 | 0 |
| ref_cast.wast | 45 | 0 | 0 |
| ref_eq.wast | 89 | 0 | 0 |
| ref_func.wast | 17 | 0 | 0 |
| ref_is_null.wast | 22 | 0 | 0 |
| ref_null.wast | 34 | 0 | 0 |
| ref_test.wast | 71 | 0 | 0 |
| relaxed_dot_product.wast | 11 | 0 | 0 |
| relaxed_laneselect.wast | 12 | 0 | 0 |
| relaxed_madd_nmadd.wast | 19 | 0 | 0 |
| relaxed_min_max.wast | 25 | 0 | 0 |
| return.wast | 84 | 0 | 0 |
| return_call.wast | 51 | 0 | 0 |
| return_call_indirect.wast | 83 | 0 | 0 |
| return_call_ref.wast | 53 | 0 | 0 |
| select.wast | 157 | 0 | 0 |
| simd_address.wast | 49 | 0 | 0 |
| simd_align.wast | 100 | 0 | 0 |
| simd_bit_shift.wast | 252 | 0 | 0 |
| simd_bitwise.wast | 169 | 0 | 0 |
| simd_boolean.wast | 277 | 0 | 0 |
| simd_const.wast | 758 | 0 | 0 |
| simd_conversions.wast | 282 | 0 | 0 |
| simd_f32x4.wast | 790 | 0 | 0 |
| simd_f32x4_arith.wast | 1822 | 0 | 0 |
| simd_f32x4_cmp.wast | 2607 | 0 | 0 |
| simd_f32x4_pmin_pmax.wast | 3887 | 0 | 0 |
| simd_f32x4_rounding.wast | 201 | 0 | 0 |
| simd_f64x2.wast | 803 | 0 | 0 |
| simd_f64x2_arith.wast | 1825 | 0 | 0 |
| simd_f64x2_cmp.wast | 2685 | 0 | 0 |
| simd_f64x2_pmin_pmax.wast | 3887 | 0 | 0 |
| simd_f64x2_rounding.wast | 201 | 0 | 0 |
| simd_i16x8_arith.wast | 194 | 0 | 0 |
| simd_i16x8_arith2.wast | 172 | 0 | 0 |
| simd_i16x8_cmp.wast | 465 | 0 | 0 |
| simd_i16x8_extadd_pairwise_i8x16.wast | 21 | 0 | 0 |
| simd_i16x8_extmul_i8x16.wast | 117 | 0 | 0 |
| simd_i16x8_q15mulr_sat_s.wast | 30 | 0 | 0 |
| simd_i16x8_sat_arith.wast | 222 | 0 | 0 |
| simd_i32x4_arith.wast | 194 | 0 | 0 |
| simd_i32x4_arith2.wast | 149 | 0 | 0 |
| simd_i32x4_cmp.wast | 475 | 0 | 0 |
| simd_i32x4_dot_i16x8.wast | 32 | 0 | 0 |
| simd_i32x4_extadd_pairwise_i16x8.wast | 21 | 0 | 0 |
| simd_i32x4_extmul_i16x8.wast | 117 | 0 | 0 |
| simd_i32x4_trunc_sat_f32x4.wast | 107 | 0 | 0 |
| simd_i32x4_trunc_sat_f64x2.wast | 107 | 0 | 0 |
| simd_i64x2_arith.wast | 200 | 0 | 0 |
| simd_i64x2_arith2.wast | 25 | 0 | 0 |
| simd_i64x2_cmp.wast | 113 | 0 | 0 |
| simd_i64x2_extmul_i32x4.wast | 117 | 0 | 0 |
| simd_i8x16_arith.wast | 131 | 0 | 0 |
| simd_i8x16_arith2.wast | 211 | 0 | 0 |
| simd_i8x16_cmp.wast | 445 | 0 | 0 |
| simd_i8x16_sat_arith.wast | 214 | 0 | 0 |
| simd_int_to_int_extend.wast | 253 | 0 | 0 |
| simd_lane.wast | 475 | 0 | 0 |
| simd_linking.wast | 3 | 0 | 0 |
| simd_load.wast | 39 | 0 | 0 |
| simd_load16_lane.wast | 36 | 0 | 0 |
| simd_load32_lane.wast | 24 | 0 | 0 |
| simd_load64_lane.wast | 16 | 0 | 0 |
| simd_load8_lane.wast | 52 | 0 | 0 |
| simd_load_extend.wast | 104 | 0 | 0 |
| simd_load_splat.wast | 126 | 0 | 0 |
| simd_load_zero.wast | 39 | 0 | 0 |
| simd_memory-multi.wast | 1 | 0 | 0 |
| simd_select.wast | 7 | 0 | 0 |
| simd_splat.wast | 185 | 0 | 0 |
| simd_store.wast | 28 | 0 | 0 |
| simd_store16_lane.wast | 36 | 0 | 0 |
| simd_store32_lane.wast | 24 | 0 | 0 |
| simd_store64_lane.wast | 16 | 0 | 0 |
| simd_store8_lane.wast | 52 | 0 | 0 |
| skip-stack-guard-page.wast | 11 | 0 | 0 |
| stack.wast | 7 | 0 | 0 |
| start.wast | 20 | 0 | 0 |
| start0.wast | 9 | 0 | 0 |
| store.wast | 68 | 0 | 0 |
| store0.wast | 5 | 0 | 0 |
| store1.wast | 13 | 0 | 0 |
| store2.wast | 25 | 0 | 0 |
| struct.wast | 30 | 0 | 0 |
| switch.wast | 28 | 0 | 0 |
| table-sub.wast | 3 | 0 | 0 |
| table.wast | 46 | 0 | 0 |
| table64.wast | 14 | 0 | 0 |
| table_copy.wast | 1728 | 0 | 0 |
| table_copy64.wast | 1728 | 0 | 0 |
| table_copy_mixed.wast | 4 | 0 | 0 |
| table_fill.wast | 45 | 0 | 0 |
| table_fill64.wast | 80 | 0 | 0 |
| table_get.wast | 16 | 0 | 0 |
| table_get64.wast | 11 | 0 | 0 |
| table_grow.wast | 58 | 0 | 0 |
| table_grow64.wast | 22 | 0 | 0 |
| table_init.wast | 792 | 0 | 0 |
| table_init64.wast | 888 | 0 | 0 |
| table_set.wast | 26 | 0 | 0 |
| table_set64.wast | 19 | 0 | 0 |
| table_size.wast | 39 | 0 | 0 |
| table_size64.wast | 37 | 0 | 0 |
| tag.wast | 10 | 0 | 0 |
| throw.wast | 13 | 0 | 0 |
| throw_ref.wast | 15 | 0 | 0 |
| token.wast | 61 | 0 | 0 |
| traps.wast | 36 | 0 | 0 |
| traps0.wast | 15 | 0 | 0 |
| try_table.wast | 67 | 0 | 0 |
| type-canon.wast | 2 | 0 | 0 |
| type-equivalence.wast | 32 | 0 | 0 |
| type-rec.wast | 27 | 0 | 0 |
| type-subtyping.wast | 131 | 0 | 0 |
| type.wast | 3 | 0 | 0 |
| unreachable.wast | 64 | 0 | 0 |
| unreached-invalid.wast | 121 | 0 | 0 |
| unreached-valid.wast | 13 | 0 | 0 |
| unwind.wast | 50 | 0 | 0 |
| utf8-custom-section-id.wast | 176 | 0 | 0 |
| utf8-import-field.wast | 176 | 0 | 0 |
| utf8-import-module.wast | 176 | 0 | 0 |
| utf8-invalid-encoding.wast | 176 | 0 | 0 |
| **Total** | **65202** | **0** | **0** |

Tail calls, tags, exception references, and all four `try_table` catch forms are supported.
Tail-call scripts use a 50,000,000-step allowance for million-iteration cases and a
call-depth limit of 8. Other scripts retain their existing resource limits.

The old bottom-type failure in `select.wast` is fixed. Validation-only bottom
survives unreachable untyped selection and can be consumed by a reference instruction.
All pinned integer scripts, scalar float scripts, control/call/local scripts,
scalar/bulk table operations, globals, memory32/64 scripts, linking, data/elements,
quoted malformed assertions, binary/LEB128 scripts, and SIMD are fully covered. Mixed function/struct/array recursive groups, subtypes,
`call_ref`, `ref.as_non_null`, `br_on_null`, and `br_on_non_null` are supported.
GC references, casts and cast branches, structs, arrays, bulk array operations,
and allocating constant expressions are covered by the added pinned scripts.

Focused fixtures in `../` cover bottom typing, quoted and binary modules, independent
module definitions/instances, repeated starts, generative/shared resources, typed imports,
reference traps/branches, nonnullable local initialization, and depth versus fuel exhaustion.
`instance.wast` now passes completely, including generative and shared tag identities.
Upstream fixtures remain unmodified.

Successful executable validation has a separate kernel-checked soundness theorem.
The plain boolean heap/type algorithms also have separate success-soundness proofs.
`assert_invalid` checks algorithmic rejection; rejection correctness/completeness
and parser/binary decoder correctness are not yet proved. Native float arithmetic
and `spectest` host calls remain outside certified execution soundness. No custom
correctness axioms were added. Diagnostic assertion strings are not compared because
traps currently carry no reason. These counts do not claim full Wasm 3.0 conformance.


The text reader supports nested comments, comments adjacent to tokens, the specification's
four whitespace characters, quoted identifiers, and annotations. SIMD parsing supports
vector lane constants and memory/lane immediates, including multiple memories. SIMD integer
and bitwise execution and vector memory stepping have kernel-checked success soundness;
vector floating arithmetic shares the existing native proof boundary. Relaxed SIMD uses
the deterministic profile, with `either` and per-lane NaN script expectations.
