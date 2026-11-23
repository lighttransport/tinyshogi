#!/bin/sh
# Policy: only Lean's three standard axioms; no sorry, native_decide, bv_decide.
set -e
cd "$(dirname "$0")/.."
if grep -rnE --include=*.lean '\bsorry\b|native_decide|bv_decide|^\s*axiom ' Shogi MiniC CDiff.lean; then
  echo "axiomcheck: forbidden construct" >&2; exit 1
fi
out=$(lake env lean tools/AxiomCheck.lean)
echo "$out"
echo "$out" | grep -oE '\[[^]]*\]' | tr -d '[] ' | tr ',' '\n' | grep -v '^$' \
  | grep -vxE 'propext|Classical.choice|Quot.sound' && { echo "axiomcheck: non-standard axiom" >&2; exit 1; }
echo "axiomcheck: ok"
