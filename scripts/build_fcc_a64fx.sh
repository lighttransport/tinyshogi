#!/usr/bin/env bash
set -euo pipefail

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
OUT=${OUT_DIR:-"$ROOT/build-fcc-a64fx"}
FCC=${FCC:-/opt/FJSVxtclanga/tcsds-1.2.43/bin/fcc}
mkdir -p "$OUT/obj"

[[ -x "$FCC" ]] || { echo "FCC not found: $FCC" >&2; exit 1; }

classic=(-O3 -Kfast -std=c11 -I"$ROOT/src")
clang=(-Nclang -O3 -std=c11 -I"$ROOT/src")
sve=(-O3 -Kfast -KSVE -std=c11 -I"$ROOT/src")

# FCC's classic frontend provides the A64FX SVE intrinsics, while its Clang
# frontend provides C11 atomics.  Objects from both frontends are ABI-compatible.
"$FCC" "${clang[@]}" -DTINYSHOGI_A64FX_UCT=1 -c "$ROOT/src/search.c" -o "$OUT/obj/search.o"
"$FCC" "${sve[@]}" -c "$ROOT/src/a64fx_uct.c" -o "$OUT/obj/a64fx_uct.o"
"$FCC" "${sve[@]}" "$ROOT/tests/test_a64fx_uct.c" "$OUT/obj/a64fx_uct.o" \
  -lm -o "$OUT/test-a64fx-uct"
for source in main shogi nnue eval thread_posix int_math int_model; do
  extra=()
  [[ "$source" == main ]] && extra=(-DTINYSHOGI_A64FX_NUMA=1)
  "$FCC" "${classic[@]}" "${extra[@]}" -c "$ROOT/src/$source.c" -o "$OUT/obj/$source.o"
done
"$FCC" "${sve[@]}" -c "$ROOT/src/simd.c" -o "$OUT/obj/simd.o"

assembly=(
  a64fx_nnue_4way a64fx_nnue_add_rows_4exact a64fx_nnue_add_rows_4row
  a64fx_nnue_add_rows a64fx_nnue_add_rows_2way a64fx_nnue_add_rows_4way
  a64fx_nnue_add_one a64fx_nnue_sdot a64fx_sdot_gemm a64fx_sdot_6x4 a64fx_sdot_64x6 a64fx_sdot_6x4_i16
  a64fx_sdot_i16_dot a64fx_sdot_i16_4 a64fx_sdot_i16_8 a64fx_sdot_i16_batch8 a64fx_sdot_i8_8
)
for source in "${assembly[@]}"; do
  "$FCC" -c "$ROOT/src/$source.S" -o "$OUT/obj/$source.o"
done

engine_objects=(
  "$OUT/obj/main.o" "$OUT/obj/search.o" "$OUT/obj/shogi.o"
  "$OUT/obj/nnue.o" "$OUT/obj/simd.o" "$OUT/obj/eval.o"
  "$OUT/obj/thread_posix.o" "$OUT/obj/a64fx_uct.o"
)
for source in "${assembly[@]}"; do engine_objects+=("$OUT/obj/$source.o"); done
"$FCC" "${engine_objects[@]}" -pthread -ldl -lm -o "$OUT/tinyshogi"

"$FCC" "${classic[@]}" -c "$ROOT/tests/test_rules.c" -o "$OUT/obj/test_rules.o"
"$FCC" "$OUT/obj/test_rules.o" "$OUT/obj/shogi.o" -lm -o "$OUT/test-rules"
"$FCC" "${classic[@]}" -c "$ROOT/tests/test_search.c" -o "$OUT/obj/test_search.o"
"$FCC" "$OUT/obj/test_search.o" "$OUT/obj/search.o" "$OUT/obj/shogi.o" \
  "$OUT/obj/eval.o" "$OUT/obj/thread_posix.o" "$OUT/obj/a64fx_uct.o" \
  -pthread -ldl -lm -o "$OUT/test-search"

"$FCC" "${classic[@]}" -c "$ROOT/bench/nnue_state_bench.c" \
  -o "$OUT/obj/nnue_state_bench.o"
nnue_objects=(
  "$OUT/obj/nnue_state_bench.o" "$OUT/obj/shogi.o" "$OUT/obj/nnue.o"
  "$OUT/obj/simd.o"
)
for source in "${assembly[@]}"; do nnue_objects+=("$OUT/obj/$source.o"); done
"$FCC" "${nnue_objects[@]}" -lm -o "$OUT/nnue-state-bench"

"$FCC" "${sve[@]}" -c "$ROOT/tests/test_simd.c" -o "$OUT/obj/test_simd.o"
simd_test_objects=("$OUT/obj/test_simd.o" "$OUT/obj/simd.o")
for source in "${assembly[@]}"; do simd_test_objects+=("$OUT/obj/$source.o"); done
"$FCC" "${simd_test_objects[@]}" -o "$OUT/test-simd"

"$FCC" "${classic[@]}" -c "$ROOT/tests/test_nnue.c" -o "$OUT/obj/test_nnue.o"
"$FCC" "$OUT/obj/test_nnue.o" "$OUT/obj/shogi.o" "$OUT/obj/nnue.o" \
  "$OUT/obj/simd.o" "${simd_test_objects[@]:2}" -lm -o "$OUT/test-nnue"

"$FCC" "${classic[@]}" -c "$ROOT/tests/test_int_batch.c" \
  -o "$OUT/obj/test_int_batch.o"
"$FCC" "$OUT/obj/test_int_batch.o" "$OUT/obj/int_math.o" \
  "$OUT/obj/int_model.o" "$OUT/obj/simd.o" "${simd_test_objects[@]:2}" \
  -lm -o "$OUT/test-int-batch"

"$FCC" "${sve[@]}" -c "$ROOT/bench/a64fx_nnue_dot_check.c" \
  -o "$OUT/obj/a64fx_nnue_dot_check.o"
"$FCC" "$OUT/obj/a64fx_nnue_dot_check.o" "$OUT/obj/simd.o" \
  "${simd_test_objects[@]:2}" -o "$OUT/nnue-dot-bench"

"$FCC" "${classic[@]}" -c "$ROOT/bench/nnue_batch_bench.c" \
  -o "$OUT/obj/nnue_batch_bench.o"
"$FCC" "$OUT/obj/nnue_batch_bench.o" "$OUT/obj/shogi.o" \
  "$OUT/obj/nnue.o" "$OUT/obj/simd.o" "${simd_test_objects[@]:2}" \
  -lm -o "$OUT/nnue-batch-bench"

"$FCC" "${classic[@]}" -c "$ROOT/bench/nnue3_batch_bench.c" \
  -o "$OUT/obj/nnue3_batch_bench.o"
"$FCC" "$OUT/obj/nnue3_batch_bench.o" "$OUT/obj/shogi.o" "$OUT/obj/nnue.o" \
  "$OUT/obj/simd.o" "${simd_test_objects[@]:2}" -lm -o "$OUT/nnue3-batch-bench"

"$FCC" "${classic[@]}" "$ROOT/bench/a64fx_sdot_gemm_bench.c" \
  "$ROOT/src/a64fx_sdot_gemm.S" -o "$OUT/sdot-i8-gemm-bench"
"$FCC" "${classic[@]}" "$ROOT/bench/a64fx_sdot_i16_bench.c" \
  "$ROOT/src/a64fx_sdot_gemm.S" -o "$OUT/sdot-i16-gemm-bench"
"$FCC" "${classic[@]}" "$ROOT/bench/a64fx_sdot_6x4_i16_bench.c" \
  "$ROOT/src/a64fx_sdot_6x4_i16.S" -o "$OUT/sdot-i16-6x4-bench"
"$FCC" "${classic[@]}" "$ROOT/bench/a64fx_sdot_5x4_i16_bench.c" \
  "$ROOT/src/a64fx_sdot_6x4_i16.S" -o "$OUT/sdot-i16-5x4-bench"

"$FCC" "${classic[@]}" -c "$ROOT/bench/int_model_batch_bench.c" \
  -o "$OUT/obj/int_model_batch_bench.o"
"$FCC" "$OUT/obj/int_model_batch_bench.o" "$OUT/obj/int_math.o" \
  "$OUT/obj/int_model.o" "$OUT/obj/simd.o" "${simd_test_objects[@]:2}" \
  -lm -o "$OUT/int-model-batch-bench"

"$OUT/tinyshogi" --selftest
"$OUT/test-rules"
"$OUT/test-search"
"$OUT/test-simd"
"$OUT/test-nnue"
"$OUT/test-int-batch"
"$OUT/test-a64fx-uct"
"$OUT/sdot-i8-gemm-bench" 256 10000
"$OUT/sdot-i16-gemm-bench" 256 10000
"$OUT/sdot-i16-6x4-bench" 256 10000
"$OUT/sdot-i16-5x4-bench" 256 100000
"$OUT/nnue-batch-bench" 256 100000
echo "PASS: FCC A64FX build in $OUT"
