#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
CC=${CC:-cc}
mkdir -p "$ROOT_DIR/build"
"$CC" -std=c11 -Wall -Wextra -Wpedantic -O2 -fPIC -shared \
  -I"$ROOT_DIR/src" "$ROOT_DIR/examples/yaneuraou_eval_adapter.c" \
  "$ROOT_DIR/src/shogi.c" \
  -o "$ROOT_DIR/build/yaneuraou-eval-adapter.so" -pthread
echo "$ROOT_DIR/build/yaneuraou-eval-adapter.so"
