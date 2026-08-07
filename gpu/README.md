# TinyShogi NNUE GPU training

The GPU trainer uses the same sparse HalfKP feature IDs, `NDF1` dataset, and
`NNUE1` model format as the CPU trainer. The kernel is shared between CUDA and
HIP/ROCm builds.

Prepare data and build a CUDA trainer:

```sh
python3 tools/prepare_nnue.py selfplay.jsonl -o selfplay.ndf1 --shuffle
make -C gpu cuda
gpu/build/tinyshogi-train-nnue-cuda selfplay.ndf1 model.nnue 5 0.01
```

For ROCm:

```sh
make -C gpu rocm HIP_CXX=hipcc
gpu/build/tinyshogi-train-nnue-hip selfplay.ndf1 model.nnue 5 0.01
```

The first implementation trains one side-to-move value head with sparse
feature updates. It keeps the full feature table and current dataset batch in
device memory; the 256-unit model is well within a 16 GB card. Atomic updates
are intentionally simple and make this a correctness/reference trainer before
adding minibatch reduction or mixed precision.

CUDA 13 no longer ships code-generation support for pre-Ampere GPUs. A GTX
1050 (compute capability 6.1) therefore needs a CUDA 12.x toolkit, even when
the installed NVIDIA driver is new enough. The trainer checks this condition
and refuses to emit a checkpoint when the toolkit cannot execute the target
architecture. For example:

```sh
make -C gpu cuda CUDA_CXX=/usr/local/cuda-12.9/bin/nvcc
LD_LIBRARY_PATH=/usr/local/cuda-12.9/lib64 \
  gpu/build/tinyshogi-train-nnue-cuda selfplay.ndf1 model.nnue 100 0.01
```
