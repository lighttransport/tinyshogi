#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
BIN=${1:?usage: $0 arm64-binary [args...]}
CLAIR_ROOT=${CLAIR_ROOT:-/home/syoyo/work/clair/main}
QLAIR=${QLAIR:-$CLAIR_ROOT/build/qlair}

[[ -x "$QLAIR" ]] || { echo "SKIP: QLAIR not found at $QLAIR" >&2; exit 77; }
output=$("$QLAIR" --native --stats "$BIN" -- "${@:2}" 2>&1) || {
  printf '%s\n' "$output"
  exit 1
}
printf '%s\n' "$output"
if grep -qE 'Execution failed|=== ERROR:|Maximum instruction count reached|Unknown Instructions:[[:space:]]+[1-9]' <<< "$output"; then
  exit 1
fi
