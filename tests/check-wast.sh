#!/bin/sh
# End-to-end regression against the pinned, unmodified upstream scripts.
set -eu
lake build wast
smoke=$(.lake/build/bin/wast tests/smoke.wast)
printf '%s\n' "$smoke" | rg -q '^tests/smoke.wast: 4 passed, 0 failed, 0 unsupported$'
control=$(.lake/build/bin/wast tests/control.wast)
printf '%s\n' "$control" | rg -q '^tests/control.wast: 22 passed, 0 failed, 0 unsupported$'
types=$(.lake/build/bin/wast tests/types.wast)
printf '%s\n' "$types" | rg -q '^tests/types.wast: 13 passed, 0 failed, 0 unsupported$'
indirect=$(.lake/build/bin/wast tests/indirect.wast)
printf '%s\n' "$indirect" | rg -q '^tests/indirect.wast: 30 passed, 0 failed, 0 unsupported$'
references=$(.lake/build/bin/wast tests/references.wast)
printf '%s\n' "$references" | rg -q '^tests/references.wast: 47 passed, 0 failed, 0 unsupported$'
growth=$(.lake/build/bin/wast tests/table-growth.wast)
printf '%s\n' "$growth" | rg -q '^tests/table-growth.wast: 32 passed, 0 failed, 0 unsupported$'
bulk=$(.lake/build/bin/wast tests/bulk-tables.wast)
printf '%s\n' "$bulk" | rg -q '^tests/bulk-tables.wast: 103 passed, 0 failed, 0 unsupported$'
linking=$(.lake/build/bin/wast tests/linking.wast)
printf '%s\n' "$linking" | rg -q '^tests/linking.wast: 49 passed, 0 failed, 0 unsupported$'
globals=$(.lake/build/bin/wast tests/globals.wast)
printf '%s\n' "$globals" | rg -q '^tests/globals.wast: 66 passed, 0 failed, 0 unsupported$'
memory=$(.lake/build/bin/wast tests/memory.wast)
printf '%s\n' "$memory" | rg -q '^tests/memory.wast: 83 passed, 0 failed, 0 unsupported$'
floats=$(.lake/build/bin/wast tests/floats.wast)
printf '%s\n' "$floats" | rg -q '^tests/floats.wast: 34 passed, 0 failed, 0 unsupported$'
frontend=$(.lake/build/bin/wast tests/frontend-gaps.wast)
printf '%s\n' "$frontend" | rg -q '^tests/frontend-gaps.wast: 18 passed, 0 failed, 0 unsupported$'
spectest=$(.lake/build/bin/wast tests/spectest.wast)
printf '%s\n' "$spectest" | rg -q '^tests/spectest.wast: 23 passed, 0 failed, 0 unsupported$'
# Start, direct re-export, nested calls, and indirect host calls print in order.
expected_prints='42 : i32
17 : i32
-1 : i32
2 : i64
3.000000 : f32
4.000000 : f64
5 : i32
6.000000 : f32
7.000000 : f64
8.000000 : f64
99 : i32'
actual_prints=$(printf '%s\n' "$spectest" | rg ' : (i32|i64|f32|f64)$')
[ "$actual_prints" = "$expected_prints" ]
status=0
output=$(.lake/build/bin/wast --fuel 4000000 tests/testsuite/i32.wast tests/testsuite/i64.wast \
  tests/testsuite/ref_null.wast tests/testsuite/ref_func.wast tests/testsuite/ref_is_null.wast \
  tests/testsuite/table_get.wast tests/testsuite/table_set.wast tests/testsuite/table_size.wast \
  tests/testsuite/table_grow.wast tests/testsuite/table_fill.wast \
  tests/testsuite/table_copy.wast tests/testsuite/table_init.wast tests/testsuite/global.wast \
  tests/testsuite/memory.wast tests/testsuite/memory_size.wast tests/testsuite/memory_grow.wast \
  tests/testsuite/memory_fill.wast tests/testsuite/memory_copy.wast tests/testsuite/memory_init.wast \
  tests/testsuite/f32.wast tests/testsuite/f64.wast tests/testsuite/conversions.wast \
  tests/testsuite/float_misc.wast tests/testsuite/float_literals.wast \
  tests/testsuite/f32_bitwise.wast tests/testsuite/f64_bitwise.wast \
  tests/testsuite/f32_cmp.wast tests/testsuite/f64_cmp.wast) || status=$?
[ "$status" -eq 2 ] || { echo "expected incomplete-coverage exit 2, got $status"; exit 1; }
printf '%s\n' "$output"
printf '%s\n' "$output" | rg -q '^tests/testsuite/i32.wast: 458 passed, 0 failed, 2 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/i64.wast: 414 passed, 0 failed, 2 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/ref_null.wast: 0 passed, 0 failed, 34 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/ref_func.wast: 17 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/ref_is_null.wast: 2 passed, 0 failed, 20 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/table_get.wast: 16 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/table_set.wast: 26 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/table_size.wast: 39 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/table_grow.wast: 58 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/table_fill.wast: 45 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/table_copy.wast: 1728 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/table_init.wast: 790 passed, 0 failed, 2 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/global.wast: 117 passed, 0 failed, 7 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/memory.wast: 86 passed, 0 failed, 4 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/memory_size.wast: 42 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/memory_grow.wast: 51 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/memory_fill.wast: 100 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/memory_copy.wast: 4450 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/memory_init.wast: 250 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/f32.wast: 2512 passed, 0 failed, 2 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/f64.wast: 2512 passed, 0 failed, 2 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/conversions.wast: 619 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/float_misc.wast: 471 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/float_literals.wast: 99 passed, 0 failed, 80 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/f32_bitwise.wast: 364 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/f64_bitwise.wast: 364 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/f32_cmp.wast: 2407 passed, 0 failed, 0 unsupported$'
printf '%s\n' "$output" | rg -q '^tests/testsuite/f64_cmp.wast: 2407 passed, 0 failed, 0 unsupported$'

# The broader audit includes the documented bottom-type select validation failure.
# Match its actual failure count; never relabel it as unsupported or passed.
while IFS=' ' read -r file passed failed unsupported; do
  case "$file" in ''|'#'*) continue ;; esac
  status=0
  output=$(.lake/build/bin/wast --fuel 4000000 "tests/testsuite/$file") || status=$?
  expected_status=0
  if [ "$failed" -gt 0 ]; then expected_status=1
  elif [ "$unsupported" -gt 0 ]; then expected_status=2
  fi
  [ "$status" -eq "$expected_status" ] || {
    printf '%s\n' "$output"
    echo "unexpected exit $status for $file (expected $expected_status)"
    exit 1
  }
  printf '%s\n' "$output"
  printf '%s\n' "$output" | rg -F -x \
    "tests/testsuite/$file: $passed passed, $failed failed, $unsupported unsupported"
done < tests/testsuite/expected-broader.txt
