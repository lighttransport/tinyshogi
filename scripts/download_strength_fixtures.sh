#!/usr/bin/env bash
set -euo pipefail

# External test data only. No third-party engine source or weights are shipped
# with tinyshogi. Preserve the weights archive's accompanying license locally.
ROOT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
FIXTURES="$ROOT_DIR/runs/strength/fixtures"
mkdir -p "$FIXTURES" "$ROOT_DIR/eval/hao"

download() {
    local url=$1 destination=$2 digest=$3 temporary
    if [[ ! -e "$destination" ]]; then
        temporary=$(mktemp "$FIXTURES/download.XXXXXX")
        if ! curl --fail --location --silent --show-error "$url" -o "$temporary"; then
            rm -- "$temporary"
            return 1
        fi
        if ! printf '%s  %s\n' "$digest" "$temporary" | sha256sum --check --status; then
            rm -- "$temporary"
            echo "Checksum mismatch: $url" >&2
            return 1
        fi
        mv -n -- "$temporary" "$destination"
    fi
    printf '%s  %s\n' "$digest" "$destination" | sha256sum --check
}

download \
    https://github.com/nodchip/tanuki-/releases/download/tanuki-.halfkp_256x2-32-32.2023-05-08/tanuki-.halfkp_256x2-32-32.2023-05-08.7z \
    "$FIXTURES/hao.7z" \
    f16dc66c529857bf08fce8cee4f1e53a6993297644100267a6ccccd62e43dbba
download \
    https://github.com/user-attachments/files/21482992/start_sfens_ply24.txt \
    "$FIXTURES/start_sfens_ply24.txt" \
    f93098ab6c0cf5eab5f55aaffd48da4421934e08d4c2fcfba68f7b60853ac0a2
download \
    https://github.com/user-attachments/files/21482993/start_sfens_ply32.txt \
    "$FIXTURES/start_sfens_ply32.txt" \
    b54a3f87b14b1b2c5815767d23a47ea7e78a20286f2d78e36bdc44a431db7252
7z x -aos "-o$ROOT_DIR/eval/hao" "$FIXTURES/hao.7z" eval/nn.bin gpl-3.0.txt
printf '%s  %s\n' \
    1141d275bceec911156801f27303dc9ff5beb24f4f59144cc069306c59e80782 \
    "$ROOT_DIR/eval/hao/eval/nn.bin" | sha256sum --check
