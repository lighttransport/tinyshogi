#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
BIN=${1:?usage: $0 arm64-binary [args...]}
CLAIR_ROOT=${CLAIR_ROOT:-/home/syoyo/work/clair/main}
QLAIR=${QLAIR:-$CLAIR_ROOT/build/qlair}
REPORT=${QLAIR_PROFILE_REPORT:-}
MAX_INSTR=${QLAIR_MAX_INSTR:-10M}

[[ -x "$QLAIR" ]] || { echo "SKIP: QLAIR not found at $QLAIR" >&2; exit 77; }
args=(--profile --stats)
if [[ -n "$MAX_INSTR" ]]; then
  args+=(--max-instr "$MAX_INSTR")
fi
if [[ -n "${QLAIR_PROFILE_FUNCTION:-}" ]]; then
  args+=(--profile-function "$QLAIR_PROFILE_FUNCTION")
fi
if [[ -n "${QLAIR_PROFILE_CONFIG:-}" ]]; then
  args+=(--profile-config "$QLAIR_PROFILE_CONFIG")
fi
if [[ -n "$REPORT" ]]; then
  args+=(--profile-report "$REPORT" --profile-format "${QLAIR_PROFILE_FORMAT:-json}")
fi
output=$(QLAIR_SIM_OOO="${QLAIR_SIM_OOO:-2}" "$QLAIR" "${args[@]}" "$BIN" -- "${@:2}" 2>&1) || {
  printf '%s\n' "$output"
  exit 1
}
printf '%s\n' "$output"
if grep -qE 'Execution failed|=== ERROR:|Maximum instruction count reached|Unknown Instructions:[[:space:]]+[1-9]' <<< "$output"; then
  exit 1
fi
