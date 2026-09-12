#!/usr/bin/env bash
set -euo pipefail

# Download and build the upstream Linux YaneuraOu NNUE engine.
# Override variables without editing this file, for example:
#   YANEURAOU_REF=v9.60 YANEURAOU_TARGET_CPU=SSE42 ./scripts/download_yaneuraou.sh

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PROJECT_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)

REPO_URL=${YANEURAOU_REPO_URL:-https://github.com/yaneurao/YaneuraOu.git}
REF=${YANEURAOU_REF:-master}
SOURCE_DIR=${YANEURAOU_SOURCE_DIR:-$PROJECT_ROOT/third_party/YaneuraOu}
OUTPUT_DIR=${YANEURAOU_OUTPUT_DIR:-$PROJECT_ROOT/build/yaneuraou}
EDITION=${YANEURAOU_EDITION:-YANEURAOU_ENGINE_NNUE}
TARGET_CPU=${YANEURAOU_TARGET_CPU:-AVX2}
COMPILER=${YANEURAOU_COMPILER:-clang++}
JOBS=${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || printf '1')}
CLEAN_BUILD=${YANEURAOU_CLEAN_BUILD:-1}

if [ -n "${YANEURAOU_OUTPUT_NAME:-}" ]; then
    OUTPUT_NAME=$YANEURAOU_OUTPUT_NAME
elif [ "$EDITION" = "YANEURAOU_ENGINE_MATERIAL" ]; then
    OUTPUT_NAME=YaneuraOu-material
else
    OUTPUT_NAME=YaneuraOu
fi

die() {
    echo "download_yaneuraou: $*" >&2
    exit 1
}

command -v git >/dev/null 2>&1 || die "git is required"
command -v make >/dev/null 2>&1 || die "make is required"
command -v "$COMPILER" >/dev/null 2>&1 || die "$COMPILER is required"

case "$JOBS" in
    ''|*[!0-9]*) die "JOBS must be a positive integer" ;;
esac
[ "$JOBS" -gt 0 ] || die "JOBS must be positive"

if [ -e "$SOURCE_DIR" ] && [ ! -d "$SOURCE_DIR/.git" ]; then
    die "source directory exists but is not a git checkout: $SOURCE_DIR"
fi

if [ ! -e "$SOURCE_DIR" ]; then
    mkdir -p "$(dirname -- "$SOURCE_DIR")"
    echo "Cloning YaneuraOu ($REF) into $SOURCE_DIR"
    git init "$SOURCE_DIR"
    git -C "$SOURCE_DIR" remote add origin "$REPO_URL"
    git -C "$SOURCE_DIR" fetch --depth 1 origin "$REF"
    git -C "$SOURCE_DIR" checkout --detach FETCH_HEAD
else
    echo "Using existing YaneuraOu checkout: $SOURCE_DIR"
    # Never silently build a different revision from the requested pin.
    EXPECTED=$(git -C "$SOURCE_DIR" rev-parse --verify "$REF^{commit}" 2>/dev/null || true)
    ACTUAL=$(git -C "$SOURCE_DIR" rev-parse HEAD)
    [ -n "$EXPECTED" ] && [ "$ACTUAL" = "$EXPECTED" ] || die "checkout does not match requested ref $REF"
fi

[ -f "$SOURCE_DIR/source/Makefile" ] || die "YaneuraOu source/Makefile not found"
mkdir -p "$OUTPUT_DIR"

if [ "$CLEAN_BUILD" = 1 ]; then
    # The upstream Makefile does not encode edition/compiler flags in object
    # dependencies; clean so switching NNUE/MATERIAL cannot reuse stale code.
    make -C "$SOURCE_DIR/source" clean
fi

# YaneuraOu's source Makefile defines NNUE editions and TARGET_CPU choices.
# Keep the output outside the checkout so rerunning this script is harmless.
make -C "$SOURCE_DIR/source" normal \
    -j"$JOBS" \
    YANEURAOU_EDITION="$EDITION" \
    TARGET_CPU="$TARGET_CPU" \
    COMPILER="$COMPILER" \
    TARGET="$OUTPUT_DIR/$OUTPUT_NAME"

echo "Built: $OUTPUT_DIR/$OUTPUT_NAME"
