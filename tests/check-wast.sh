#!/bin/sh
# End-to-end regression against the pinned, unmodified upstream scripts.
set -eu
caller_dir=$(pwd)
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_dir"
mode=regression
testsuite_dir="$project_dir/.cache/testsuite"
while [ "$#" -gt 0 ]; do
  case "$1" in
    --full) mode=--full; shift ;;
    --testsuite)
      [ "$#" -ge 2 ] || { echo "--testsuite requires a directory" >&2; exit 1; }
      testsuite_dir=$2
      shift 2 ;;
    *) echo "usage: sh tests/check-wast.sh [--full] [--testsuite DIRECTORY]" >&2; exit 1 ;;
  esac
done
case "$testsuite_dir" in /*) ;; *) testsuite_dir="$caller_dir/$testsuite_dir" ;; esac
[ -d "$testsuite_dir" ] || {
  echo "testsuite missing; run: sh tests/setup-testsuite.sh" >&2
  exit 1
}
revision=$(cat tests/testsuite/revision)
[ "$(git -C "$testsuite_dir" rev-parse HEAD)" = "$revision" ] || {
  echo "testsuite revision differs from tests/testsuite/revision" >&2
  exit 1
}
[ -z "$(git -C "$testsuite_dir" status --porcelain)" ] || {
  echo "testsuite checkout has local changes" >&2
  exit 1
}
# Only top-level scripts belong to this inventory; upstream also has proposal subdirectories.
expected_files=$(awk '!/^#/ && NF {print $1}' tests/testsuite/expected-broader.txt | sort)
actual_files=$(for fixture in "$testsuite_dir"/*.wast; do
  [ -f "$fixture" ] || continue
  basename "$fixture"
done | sort)
inventory_files=$(awk '!/^#/ && NF {print $1}' tests/testsuite/inventory.tsv | sort)
[ "$actual_files" = "$inventory_files" ] || {
  echo "upstream top-level scripts differ from the recorded inventory" >&2
  exit 1
}
completed_files=$(awk '!/^#/ && $3 == "complete" {print $1}' tests/testsuite/inventory.tsv | sort)
[ "$expected_files" = "$completed_files" ] || {
  echo "passing regression manifest differs from completed inventory" >&2
  exit 1
}
lake build wast
vectors=$(.lake/build/bin/wast tests/vectors.wast)
printf '%s\n' "$vectors" | rg -q '^tests/vectors.wast: 8 passed, 0 failed, 0 unsupported$'
cast_branches=$(.lake/build/bin/wast tests/gc-cast-branches.wast)
printf '%s\n' "$cast_branches" | rg -q '^tests/gc-cast-branches.wast: 10 passed, 0 failed, 0 unsupported$'
structures=$(.lake/build/bin/wast tests/structures.wast)
printf '%s\n' "$structures" | rg -q '^tests/structures.wast: 19 passed, 0 failed, 0 unsupported$'
gc_references=$(.lake/build/bin/wast tests/gc-references.wast)
printf '%s\n' "$gc_references" | rg -q '^tests/gc-references.wast: 23 passed, 0 failed, 0 unsupported$'
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
binary=$(.lake/build/bin/wast tests/binary-modules.wast)
printf '%s\n' "$binary" | rg -q '^tests/binary-modules.wast: 6 passed, 0 failed, 0 unsupported$'
bottom=$(.lake/build/bin/wast tests/bottom.wast)
printf '%s\n' "$bottom" | rg -q '^tests/bottom.wast: 5 passed, 0 failed, 0 unsupported$'
definitions=$(.lake/build/bin/wast tests/module-definitions.wast)
printf '%s\n' "$definitions" | rg -q '^tests/module-definitions.wast: 40 passed, 0 failed, 0 unsupported$'
quoted=$(.lake/build/bin/wast tests/quoted-modules.wast)
printf '%s\n' "$quoted" | rg -q '^tests/quoted-modules.wast: 10 passed, 0 failed, 0 unsupported$'
exhaustion=$(.lake/build/bin/wast --call-depth 16 --fuel 10000 tests/exhaustion.wast)
printf '%s\n' "$exhaustion" | rg -q '^tests/exhaustion.wast: 6 passed, 0 failed, 0 unsupported$'
typed=$(.lake/build/bin/wast tests/typed-references.wast)
printf '%s\n' "$typed" | rg -q '^tests/typed-references.wast: 34 passed, 0 failed, 0 unsupported$'
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
while IFS=' ' read -r file passed failed unsupported call_depth script_fuel; do
  case "$file" in ''|'#'*) continue ;; esac
  [ "$failed" -eq 0 ] || { echo "failure baseline forbidden for $file"; exit 1; }
  [ "$unsupported" -eq 0 ] || { echo "unsupported baseline forbidden for $file"; exit 1; }
  status=0
  output=$(.lake/build/bin/wast --fuel "${script_fuel:-4000000}" --call-depth "$call_depth" \
    "$testsuite_dir/$file") || status=$?
  expected_status=0
  [ "$status" -eq "$expected_status" ] || {
    printf '%s\n' "$output"
    echo "unexpected exit $status for $file (expected $expected_status)"
    exit 1
  }
  printf '%s\n' "$output"
  printf '%s\n' "$output" | rg -q -F -x \
    "$testsuite_dir/$file: $passed passed, 0 failed, $unsupported unsupported"
done < tests/testsuite/expected-broader.txt

if [ "$mode" = --full ]; then
  full_status=0
  while read -r file family coverage; do
    case "$file" in ''|'#'*) continue ;; esac
    [ "$coverage" != complete ] || continue
    status=0
    .lake/build/bin/wast --fuel 4000000 --call-depth 256 "$testsuite_dir/$file" || status=$?
    case "$status" in
      0) ;;
      2) [ "$full_status" -ne 0 ] || full_status=2 ;;
      *) full_status=1 ;;
    esac
  done < tests/testsuite/inventory.tsv
  exit "$full_status"
fi
