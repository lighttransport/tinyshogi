#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
BUILD_DIR=${BUILD_DIR:-$ROOT/build-regression}

meson setup "$BUILD_DIR" --reconfigure >/dev/null 2>&1 || meson setup "$BUILD_DIR"
meson compile -C "$BUILD_DIR"
meson test -C "$BUILD_DIR" --print-errorlogs

if [[ "${RUN_FUZZ:-0}" == 1 ]]; then
    make -C "$ROOT/fuzz" all
    FUZZ_DIR=$(mktemp -d)
    trap 'rm -rf "$FUZZ_DIR"' EXIT
    cp "$ROOT"/fuzz/corpus/*.sfen "$FUZZ_DIR"/
    LSAN_OPTIONS=${LSAN_OPTIONS:-detect_leaks=0} \
      ASAN_OPTIONS=${ASAN_OPTIONS:-detect_leaks=0} \
      "$ROOT/fuzz/shogi-fuzz" -max_total_time="${FUZZ_SECONDS:-30}" "$FUZZ_DIR"
fi

echo "regression checks passed"
