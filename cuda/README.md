# Optional CUDA workflow

The CPU engine and self-play exporter do not require CUDA. The optional CUDA
stage uses CUEW-style runtime loading: CUDA Driver API symbols are resolved by
`dlopen`, and the probe links only against `libdl`. Therefore this directory
does not require CUDA headers, `nvcc`, or `-lcuda` on the data-generation host.

## Build on the training machine

Obtain CUEW 2.x under `third_party/cuew` or point `CUEW_DIR` at an existing
copy:

```sh
make -C cuda CUEW_DIR=/path/to/cuew
cuda/build/tinyshogi-cuda-probe
```

Exit status 77 means that the host has no usable NVIDIA driver/device. This is
expected on the current development machine and is not a build failure.

The intended training flow is:

```sh
./build/tinyshogi --selfplay --games 1000 --simulations 256 \
  --threads 8 --seed 7 --output selfplay.jsonl
python3 tools/prepare_selfplay.py selfplay.jsonl selfplay.validated.jsonl
python3 tools/prepare_selfplay.py selfplay.jsonl selfplay.validated.jsonl \
  --binary selfplay.tsf
make -C cuda CUEW_DIR=/path/to/cuew
cuda/build/tinyshogi-cuda-probe
make -C cuda CUEW_DIR=/path/to/cuew feature-encode
cuda/build/tinyshogi-feature-encode selfplay.tsf selfplay.tfe
make -C cuda CUEW_DIR=/path/to/cuew train-linear
cuda/build/tinyshogi-train-linear selfplay.tsf selfplay.tfe model.tsm 10
```

`TSF1` is a compact host-side record format containing 81 encoded board cells,
14 hand counts, side-to-move, outcome, and sparse policy visits. The
`tinyshogi-feature-encode` tool compiles a small raw CUDA kernel through NVRTC,
loads it through the CUDA Driver API, and writes `TFE1` float planes: 28 piece
planes, one empty-square plane, and one side-to-move plane. No CUDA-specific
code is linked into the normal tinyshogi binary.

The trainer is a deliberately small 64-unit ReLU policy/value SGD baseline. It
writes `TSM2` weights and exists to validate the complete CUDA data/model loop;
it is not expected to produce a strong shogi model. Replace it with a batched
residual network after the GPU handoff is working.
