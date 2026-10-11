#!/bin/sh
# Fetch an isolated upstream checkout at the recorded conformance revision.
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
revision=$(cat "$project_dir/tests/testsuite/revision")
testsuite_dir=${1:-"$project_dir/.cache/testsuite"}
[ "$#" -le 1 ] || { echo "usage: sh tests/setup-testsuite.sh [DIRECTORY]" >&2; exit 1; }

if [ -e "$testsuite_dir" ]; then
  [ -e "$testsuite_dir/.git" ] || {
    echo "refusing to replace existing non-checkout: $testsuite_dir" >&2
    exit 1
  }
else
  git init -q "$testsuite_dir"
  git -C "$testsuite_dir" remote add origin https://github.com/WebAssembly/testsuite.git
fi

if current=$(git -C "$testsuite_dir" rev-parse --verify HEAD 2>/dev/null); then
  [ "$current" = "$revision" ] || {
    echo "checkout is at $current; expected $revision. Choose a fresh directory." >&2
    exit 1
  }
else
  git -C "$testsuite_dir" fetch --depth 1 origin "$revision"
  git -C "$testsuite_dir" checkout --detach "$revision"
fi
[ -z "$(git -C "$testsuite_dir" status --porcelain)" ] || {
  echo "testsuite checkout has local changes: $testsuite_dir" >&2
  exit 1
}
testsuite_dir=$(CDPATH= cd -- "$testsuite_dir" && pwd)
printf '%s\n' "$testsuite_dir"
