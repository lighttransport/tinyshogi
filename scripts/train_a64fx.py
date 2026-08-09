#!/usr/bin/env python3
"""Run value-NNUE self-play and synchronous training inside a PJM allocation."""

import argparse
import os
from pathlib import Path
import shlex
import subprocess
import time


def run(command, *, env, dry_run=False):
    print("+", " ".join(shlex.quote(item) for item in command), flush=True)
    if not dry_run:
        subprocess.run(command, check=True, env=env)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--engine", default="build-fcc-a64fx/tinyshogi")
    parser.add_argument("--trainer", default="build-fcc-a64fx/train-nnue-mpi")
    parser.add_argument("--model")
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--nodes", type=int, default=int(os.getenv("PJM_NODE", "1")))
    parser.add_argument("--games", type=int, default=1200)
    parser.add_argument("--simulations", type=int, default=100000)
    parser.add_argument("--max-plies", type=int, default=512)
    parser.add_argument("--threads", type=int, default=48)
    parser.add_argument("--leaf-batch", type=int, default=12)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--epochs", type=int, default=5)
    parser.add_argument("--global-batch", type=int, default=2304)
    parser.add_argument("--learning-rate", type=float, default=0.03)
    parser.add_argument("--momentum", type=float, default=0.9)
    parser.add_argument("--optimizer", choices=("momentum", "nesterov", "muon"),
                        default="momentum")
    parser.add_argument("--muon-learning-rate", type=float, default=0.02)
    parser.add_argument("--archive-data", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    if args.nodes < 1 or args.games < args.nodes:
        parser.error("nodes must be positive and games must be at least nodes")
    allocation = int(os.getenv("PJM_NODE", str(args.nodes)))
    if args.nodes > allocation:
        parser.error(f"requested {args.nodes} nodes, allocation has {allocation}")

    root = Path.cwd()
    engine = Path(args.engine).resolve()
    trainer = Path(args.trainer).resolve()
    model = Path(args.model).resolve() if args.model else None
    for path in (engine, trainer, model):
        if path is not None and not path.is_file():
            parser.error(f"missing file: {path}")

    output = Path(args.output_dir).resolve()
    output.mkdir(parents=True, exist_ok=True)
    job = os.getenv("PJM_JOBID", str(os.getpid()))
    local = f"/local/tinyshogi-train-{job}"
    log_prefix = str(output / "mpi")
    env = os.environ.copy()
    env.setdefault("OPAL_PREFIX", "/opt/FJSVxtclanga/tcsds-1.2.43")
    env.update({
        "OMP_NUM_THREADS": str(args.threads),
        "OMP_PROC_BIND": "close",
        "OMP_PLACES": "cores",
    })
    mpi = ["mpiexec", "-n", str(args.nodes), "-of-proc", log_prefix]

    stage_script = """
set -eu
mkdir -p "$1"
cp "$2" "$1/tinyshogi"
cp "$3" "$1/train_nnue_mpi"
if [ "$4" != - ]; then cp "$4" "$1/input.nnue"; fi
"""
    run(mpi + ["bash", "-c", stage_script, "stage", local, str(engine),
               str(trainer), str(model) if model else "-"], env=env,
        dry_run=args.dry_run)

    selfplay_script = """
set -eu
r=${PMIX_RANK:-${OMPI_COMM_WORLD_RANK:-0}}
nodes=$1; games=$2; base=$((games / nodes)); rem=$((games % nodes))
n=$base; if [ "$r" -lt "$rem" ]; then n=$((n + 1)); fi
before=$((r * base)); if [ "$r" -lt "$rem" ]; then before=$((before + r)); else before=$((before + rem)); fi
dir=$3
model_args=""
if [ -f "$dir/input.nnue" ]; then model_args="--eval-model $dir/input.nnue"; fi
exec "$dir/tinyshogi" --selfplay --games "$n" --game-offset "$before" \
  --simulations "$4" --max-plies "$5" --threads "$6" --leaf-batch "$7" \
  --seed "$8" --output-format ndf1 --output "$dir/train.ndf1" $model_args
"""
    started = time.monotonic()
    run(mpi + ["bash", "-c", selfplay_script, "selfplay", str(args.nodes),
               str(args.games), local, str(args.simulations), str(args.max_plies),
               str(args.threads), str(args.leaf_batch), str(args.seed)], env=env,
        dry_run=args.dry_run)
    selfplay_seconds = time.monotonic() - started

    candidate = output / "candidate.nnue"
    run(mpi + [f"{local}/train_nnue_mpi", "--data", f"{local}/train.ndf1",
               "--output", str(candidate), "--epochs", str(args.epochs),
               "--global-batch", str(args.global_batch), "--learning-rate",
               str(args.learning_rate), "--momentum", str(args.momentum),
               "--optimizer", args.optimizer, "--muon-learning-rate",
               str(args.muon_learning_rate),
               "--seed", str(args.seed)], env=env, dry_run=args.dry_run)

    if args.archive_data:
        archive = output / "data"
        archive.mkdir(exist_ok=True)
        copy_script = """
set -eu
r=${PMIX_RANK:-${OMPI_COMM_WORLD_RANK:-0}}
cp "$1/train.ndf1" "$2/rank-$r.ndf1.partial"
mv "$2/rank-$r.ndf1.partial" "$2/rank-$r.ndf1"
"""
        run(mpi + ["bash", "-c", copy_script, "archive", local, str(archive)],
            env=env, dry_run=args.dry_run)

    if not args.dry_run:
        (output / "summary.txt").write_text(
            f"nodes={args.nodes}\ngames={args.games}\nsimulations={args.simulations}\n"
            f"selfplay_seconds={selfplay_seconds:.6f}\n"
            f"selfplay_games_per_second={args.games / selfplay_seconds:.6f}\n"
        )
    print(f"candidate={candidate}", flush=True)


if __name__ == "__main__":
    main()
