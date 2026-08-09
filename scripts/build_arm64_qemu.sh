#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
OUT=${OUT_DIR:-"$ROOT/build-arm64"}
CC=${AARCH64_CC:-aarch64-linux-gnu-gcc}
QEMU=${QEMU_AARCH64:-qemu-aarch64-static}
SYSROOT=${AARCH64_SYSROOT:-/usr/aarch64-linux-gnu}
QEMU_LD_PREFIX=${QEMU_LD_PREFIX:-$SYSROOT}
ARCH=${ARM64_ARCH:-${1:-neon}}

read -r -a CC_CMD <<< "$CC"
command -v "${CC_CMD[0]}" >/dev/null || { echo "SKIP: set AARCH64_CC to an AArch64 GCC/Clang driver" >&2; exit 77; }
command -v "$QEMU" >/dev/null || { echo "SKIP: qemu-aarch64-static unavailable" >&2; exit 77; }
[[ -d "$SYSROOT" ]] || { echo "SKIP: AARCH64_SYSROOT missing: $SYSROOT" >&2; exit 77; }
mkdir -p "$OUT"

NO_VECTOR_FLAGS=(-fno-vectorize -fno-slp-vectorize)
if [[ "${CC_CMD[0]}" == *gcc* ]]; then
  NO_VECTOR_FLAGS=(-fno-tree-vectorize -fno-tree-slp-vectorize)
fi

if [[ "$ARCH" == "sve" ]]; then
  CFLAGS="-O3 -std=c11 -march=armv8.2-a+sve -msve-vector-bits=512"
  CPU="max,sve=on,sve512=on"
else
  CFLAGS="-O3 -std=c11 -march=armv8-a+simd"
  CPU="max"
fi
COMMON=("$ROOT/src/shogi.c" "$ROOT/src/simd.c" "$ROOT/src/nnue.c")
NNUE_ASM=()
if [[ "$ARCH" == "sve" ]]; then
  NNUE_ASM=("$ROOT/src/a64fx_nnue_4way.S" "$ROOT/src/a64fx_nnue_add_rows_4exact.S" \
            "$ROOT/src/a64fx_nnue_add_rows_4row.S" \
            "$ROOT/src/a64fx_nnue_add_rows.S" \
            "$ROOT/src/a64fx_nnue_add_rows_2way.S" "$ROOT/src/a64fx_nnue_add_rows_4way.S" \
            "$ROOT/src/a64fx_nnue_add_one.S" "$ROOT/src/a64fx_nnue_sdot.S" \
            "$ROOT/src/a64fx_sdot_gemm.S" "$ROOT/src/a64fx_sdot_6x4.S" \
            "$ROOT/src/a64fx_sdot_64x6.S" \
            "$ROOT/src/a64fx_sdot_6x4_i16.S" \
            "$ROOT/src/a64fx_sdot_i16_dot.S" "$ROOT/src/a64fx_sdot_i16_4.S" \
            "$ROOT/src/a64fx_sdot_i16_batch8.S" \
            "$ROOT/src/a64fx_sdot_i16_8.S" "$ROOT/src/a64fx_sdot_i8_8.S")
fi

"${CC_CMD[@]}" $CFLAGS "$ROOT/tests/test_simd.c" "$ROOT/src/simd.c" "${NNUE_ASM[@]}" -o "$OUT/test-simd"
"${CC_CMD[@]}" $CFLAGS "$ROOT/tests/test_int.c" "$ROOT/src/int_math.c" "$ROOT/src/int_model.c" "$ROOT/src/simd.c" "${NNUE_ASM[@]}" -lm -o "$OUT/test-int"
"${CC_CMD[@]}" $CFLAGS "$ROOT/tests/test_nnue.c" "${COMMON[@]}" "${NNUE_ASM[@]}" -lm -o "$OUT/test-nnue"
if [[ "$ARCH" == "sve" ]]; then
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/a64fx_nnue_eval_bench.c" "${COMMON[@]}" "${NNUE_ASM[@]}" \
    -lm -o "$OUT/a64fx-nnue-eval"
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/a64fx_nnue_add_rows_bench.c" "$ROOT/src/simd.c" \
    "${NNUE_ASM[@]}" -o "$OUT/a64fx-nnue-rows"
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/a64fx_nnue_dot_check.c" "$ROOT/src/simd.c" \
    "${NNUE_ASM[@]}" -o "$OUT/a64fx-nnue-dot-check"
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/nnue_batch_bench.c" "${COMMON[@]}" \
    "${NNUE_ASM[@]}" -lm -o "$OUT/a64fx-nnue-batch"
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/a64fx_nnue_add_rows_4way_bench.c" \
    "$ROOT/src/a64fx_nnue_add_rows_4way.S" \
    -o "$OUT/a64fx-nnue-rows-4way"
fi
"${CC_CMD[@]}" $CFLAGS "$ROOT/tests/test_search.c" "$ROOT/src/search.c" "$ROOT/src/eval.c" "$ROOT/src/thread_posix.c" "$ROOT/src/shogi.c" -pthread -ldl -lm -o "$OUT/test-search"

if [[ "$ARCH" == "sve" ]]; then
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/a64fx_sdot_gemm_bench.c" \
    "$ROOT/src/a64fx_sdot_gemm.S" -o "$OUT/a64fx-sdot-gemm"
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/a64fx_sgemm_bench.c" \
    "$ROOT/src/a64fx_sgemm.S" -o "$OUT/a64fx-sgemm"
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/a64fx_sdot_i16_bench.c" \
    "$ROOT/src/a64fx_sdot_gemm.S" -o "$OUT/a64fx-sdot-i16"
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/a64fx_sdot_6x4_bench.c" \
    "$ROOT/src/a64fx_sdot_6x4.S" -o "$OUT/a64fx-sdot-6x4"
  "${CC_CMD[@]}" $CFLAGS "${NO_VECTOR_FLAGS[@]}" \
    "$ROOT/bench/a64fx_sdot_6x4_i16_bench.c" \
    "$ROOT/src/a64fx_sdot_6x4_i16.S" -o "$OUT/a64fx-sdot-6x4-i16"
fi

run() { "$QEMU" -cpu "$CPU" -L "$QEMU_LD_PREFIX" "$@"; }
run "$OUT/test-simd"
run "$OUT/test-int"
run "$OUT/test-nnue"
if [[ "$ARCH" == "sve" ]]; then
  run "$OUT/a64fx-nnue-eval" 10
  run "$OUT/a64fx-nnue-rows" 10
  run "$OUT/a64fx-nnue-dot-check"
  run "$OUT/a64fx-nnue-rows-4way" 10
fi
run "$OUT/test-search"
if [[ "$ARCH" == "sve" ]]; then
  run "$OUT/a64fx-sdot-gemm" 256 10
  run "$OUT/a64fx-sgemm" 256 10
  run "$OUT/a64fx-sdot-i16" 256
  run "$OUT/a64fx-sdot-6x4" 256 10
  run "$OUT/a64fx-sdot-6x4-i16" 256 10
fi
echo "PASS: ARM64 $ARCH QEMU tests"
