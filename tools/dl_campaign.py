#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Native self-play/training supervisor. Python handles files, never tensors.

Each device phase receives a prepaid wall-time lease enforced by GNU timeout,
including if this supervisor dies. An interrupted lease is charged in full.
No opponent code, models, or games are downloaded or used for training.
"""
import argparse
from collections import deque
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import struct
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "third_party/gemm/nn/build/gn_tool"
SELFPLAY = ROOT / "build/dl/dl-selfplay"
GPU_TEST = ROOT / "third_party/gemm/nn/build/test_gpu"
HEADER = b"GNR1" + struct.pack("<III", 9, 80, 139) + bytes(56) + bytes([1]*22 + [2, 3])
FEATURE_BYTES = 56 * 11 + 22 * 4


def sha256(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def preflight_commands(backend, folder, micro, smoke):
    """Qualify the actual ROCm training batch, not just small inference shapes."""
    if backend == "cpu":
        return [("preflight", [TOOL.parent / "test_gn", folder / "preflight.safetensors"])]
    checks = [("preflight", [GPU_TEST, backend, folder / "preflight-gpu.safetensors", "wide"]),
              ("preflight-fp32", [GPU_TEST, backend.split("-")[0] + "-fp32",
                                   folder / "preflight-fp32.safetensors", "wide"])]
    if backend.startswith("hip") and not smoke:
        checks.append(("preflight-full", [GPU_TEST, backend, folder / "preflight-full.safetensors",
                                          "full", str(micro)]))
    return checks


def atomic_json(path, value):
    path = Path(path)
    partial = path.with_name(path.name + ".partial")
    with partial.open("w") as stream:
        json.dump(value, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(partial, path)


def checkpoint_info(path):
    """Read our two bounded metadata tensors without loading model weights."""
    with Path(path).open("rb") as stream:
        prefix = stream.read(8)
        if len(prefix) != 8:
            raise ValueError("truncated checkpoint")
        length, = struct.unpack("<Q", prefix)
        if length > 2**20:
            raise ValueError("oversized checkpoint header")
        header = json.loads(stream.read(length))
        values = []
        for key, count in (("__config", 12), ("__state", 2)):
            tensor = header[key]
            begin, end = tensor["data_offsets"]
            if tensor["dtype"] != "U64" or tensor["shape"] != [count] or end-begin != count*8 or begin < 0:
                raise ValueError("invalid checkpoint metadata")
            stream.seek(8+length+begin)
            values.append(struct.unpack("<"+"Q"*count, stream.read(count*8)))
    cfg, state = values
    if cfg[:4] != (1, 9, 80, 139):
        raise ValueError("not a tinyshogi DL-v1 checkpoint")
    return dict(format="tinyshogi-dl-v1", layout="NHWC", channels=cfg[4], blocks=cfg[5],
                attention_every=cfg[6], head_dim=cfg[7], value_channels=cfg[8],
                value_hidden=cfg[9], seed=cfg[10], step=state[0], rng=state[1])


def record_index(path):
    """Bounded-memory structural validation; native trainer validates tensors."""
    size = Path(path).stat().st_size
    with Path(path).open("rb") as stream:
        if stream.read(len(HEADER)) != HEADER:
            raise ValueError(f"unsupported replay schema: {path}")
        while stream.tell() < size:
            begin = stream.tell()
            raw = stream.read(28)
            if len(raw) != 28:
                raise ValueError("truncated replay record")
            game, generation, ply, count, label = struct.unpack("<QQIII", raw)
            if not 1 <= count <= 600 or label > 2 or ply >= 512:
                raise ValueError("invalid replay record")
            length = 28 + FEATURE_BYTES + 8*count
            if begin+length > size:
                raise ValueError("truncated replay payload")
            stream.seek(FEATURE_BYTES, 1)
            pairs = list(struct.iter_unpack("<II", stream.read(count*8)))
            if (len({a for a, _ in pairs}) != count or any(a >= 81*139 for a, _ in pairs)
                    or not sum(n for _, n in pairs)):
                raise ValueError("invalid sparse policy")
            yield begin, length, game, generation, ply


def pack_window(shards, destination, limit):
    """Retain a recent bounded position window; split remains game-disjoint."""
    entries = deque(maxlen=limit)
    for path in shards:
        for begin, length, game, _, _ in record_index(path):
            entries.append((path, begin, length, game))
    destination = Path(destination)
    partial = destination.with_name(destination.name + ".partial")
    source, current = None, None
    try:
        with partial.open("wb") as out:
            out.write(HEADER)
            for path, begin, length, _ in entries:
                if path != current:
                    if source:
                        source.close()
                    source, current = Path(path).open("rb"), path
                source.seek(begin)
                raw = source.read(length)
                if len(raw) != length:
                    raise ValueError("replay changed while packing")
                out.write(raw)
            out.flush()
            os.fsync(out.fileno())
        os.replace(partial, destination)
    finally:
        if source:
            source.close()
    train = sum(game % 20 != 0 for _, _, _, game in entries)
    return dict(positions=len(entries), training=train, validation=len(entries)-train,
                sha256=sha256(destination))


class Campaign:
    def __init__(self, folder, config):
        self.folder = Path(folder)
        self.folder.mkdir(parents=True, exist_ok=True)
        self.lock = (self.folder / "lock").open("a")
        fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        self.path = self.folder / "state.json"
        if self.path.exists():
            self.state = json.loads(self.path.read_text())
            if self.state["config"] != config:
                raise ValueError("resume configuration/binary changed; use a new campaign directory")
            lease = self.state.get("lease")
            if lease and time.time() < lease["expires_unix"]:
                raise ValueError("previous lease may still be running; retry after its recorded expiry")
            self.state["lease"] = None  # full reservation was already charged
            if self.state["model"] and sha256(self.state["model"]) != self.state["model_sha256"]:
                raise ValueError("modified campaign checkpoint")
            # A crash may have published a new window before committing the
            # associated shard list. Reconstruct only from committed shards.
            if self.state["shards"]:
                for shard in self.state["shards"]:
                    manifest = json.loads(Path(shard+".json").read_text())
                    if sha256(shard) != manifest["sha256"]:
                        raise ValueError("modified campaign replay shard")
                self.state["replay"] = pack_window(self.state["shards"], self.folder / "window.gnr",
                                                    config["window"])
        else:
            self.state = dict(version=1, config=config, spent_seconds=0, lease=None, sequence=0,
                              generation=1, model=None, shards=[], positions=0, credit=0, seed=1,
                              preflight=False)
        self.save()

    def save(self):
        atomic_json(self.path, self.state)

    def phase(self, command, maximum, label):
        remaining = self.state["config"]["hours"]*3600 - self.state["spent_seconds"]
        lease = min(maximum, remaining)
        if lease < 3:
            return None
        self.state["sequence"] += 1
        self.state["spent_seconds"] += lease
        self.state["lease"] = dict(command=list(map(str, command)), seconds=lease,
                                   expires_unix=time.time()+lease+2, label=label)
        self.save()  # debit before launching; a crash cannot erase usage
        log = self.folder / f"phase-{self.state['sequence']:06d}-{label}.log"
        start = time.monotonic()
        # External watchdog survives a supervisor crash. One second of the lease
        # is reserved for graceful checkpoint/finished-game publication.
        with log.open("w") as output:
            result = subprocess.run(["timeout", "--signal=TERM", "--kill-after=1s",
                                     f"{lease-1:.3f}s", *map(str, command)],
                                    stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
        elapsed = time.monotonic()-start
        self.state["spent_seconds"] -= max(0, lease-elapsed)
        self.state["lease"] = None
        self.save()
        print(json.dumps(dict(phase=label, returncode=result.returncode,
                              charged_hours=self.state["spent_seconds"]/3600, log=str(log))), flush=True)
        if result.returncode not in (0, 124, 137, -9):
            raise RuntimeError(f"{label} failed; inspect {log}")
        return result.returncode


def parse_args(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--run-dir", type=Path, required=True)
    p.add_argument("--backend", choices=("cpu", "cuda", "hip", "hip-blaslt"), required=True)
    p.add_argument("--smoke", action="store_true", help="small CPU plumbing run, not a strength experiment")
    p.add_argument("--hours", type=float, default=336)
    p.add_argument("--phase-seconds", type=float, default=3600)
    p.add_argument("--generations", type=int, default=0, help="0: continue until time budget")
    return p.parse_args(argv)


def main(argv=None):
    args = parse_args(argv)
    if (not math.isfinite(args.hours) or not 0 < args.hours <= 336 or
            not math.isfinite(args.phase_seconds) or args.phase_seconds < 3 or args.generations < 0):
        raise ValueError("invalid time/generation limits")
    if args.backend == "cpu" and not args.smoke:
        raise ValueError("CPU campaigns require --smoke; the 336-hour experiment requires a GPU")
    if not shutil.which("timeout"):
        raise ValueError("GNU timeout is required for independent budget enforcement")
    config = dict(backend=args.backend, hours=args.hours, phase_seconds=args.phase_seconds,
                  smoke=args.smoke, channels=8 if args.smoke else 256, blocks=2 if args.smoke else 20,
                  games=2 if args.smoke else 64, nodes=8 if args.smoke else 400,
                  threads=2 if args.smoke else 1, parallel=2 if args.smoke else 8,
                  max_plies=8 if args.smoke else 512,
                  batch=4 if args.smoke else 256, micro=2 if args.smoke else 16,
                  start=1 if args.smoke else 50000, window=1000 if args.smoke else 1000000,
                  tool_sha256=sha256(TOOL), selfplay_sha256=sha256(SELFPLAY),
                  gpu_test_sha256=sha256(GPU_TEST), supervisor_sha256=sha256(__file__))
    c = Campaign(args.run_dir.resolve(), config)
    s = c.state
    if not s["preflight"]:
        for name, command in preflight_commands(args.backend, c.folder, config["micro"], args.smoke):
            if c.phase(command, args.phase_seconds, name) != 0:
                raise RuntimeError(f"{name} incomplete; no training is permitted")
        s["preflight"] = True
        c.save()
    if not s["model"]:
        model = c.folder / "initial.safetensors"
        subprocess.run([str(TOOL), "init", str(model), str(config["channels"]), str(config["blocks"])], check=True)
        s["model"] = str(model)
        s["model_sha256"] = sha256(model)
        atomic_json(str(model)+".json", dict(**checkpoint_info(model), sha256=sha256(model),
                                           origin="independent random initialization", config=config))
        c.save()
    finished = 0
    while not args.generations or finished < args.generations:
        if config["hours"]*3600-s["spent_seconds"] < 3:
            break
        # Consume outstanding credit before creating another generation. A
        # checkpoint's exact optimizer step determines credit spent on resume.
        if s["positions"] >= config["start"] and s["credit"] >= config["batch"]:
            source = Path(s["model"])
            target = c.folder / f"model-{s['sequence']+1:06d}.safetensors"
            before = checkpoint_info(source)["step"]
            steps = min(s["credit"]//config["batch"], 16)
            rc = c.phase([TOOL, "train", c.folder / "window.gnr", source, target, steps,
                          config["batch"], .001, args.backend, config["micro"], 300],
                         args.phase_seconds, "train")
            if rc is None:
                break
            if target.exists():
                info = checkpoint_info(target)
                used = info["step"]-before
                if not 0 <= used <= steps:
                    raise ValueError("invalid optimizer step transition")
                s["credit"] -= used*config["batch"]
                s["model"] = str(target)
                s["model_sha256"] = sha256(target)
                atomic_json(str(target)+".json", dict(**info, sha256=sha256(target),
                            parent_sha256=sha256(source), replay=s["replay"], config=config,
                            charged_seconds=s["spent_seconds"]))
                c.save()
            if rc != 0:
                break  # no spin on a phase too short to finish an update
            continue
        current_step = checkpoint_info(s["model"])["step"]
        if "replay" in s and s.get("validated_step") != current_step:
            rc = c.phase([TOOL, "validate", c.folder / "window.gnr", s["model"], args.backend, 512],
                         args.phase_seconds, "validate")
            if rc != 0:
                break
            s["validated_step"] = current_step
            c.save()
        shard = c.folder / f"selfplay-{s['seed']:07d}.gnr"
        seed = s["seed"]
        s["seed"] += 1
        c.save()  # never reuse a seed/game id, including abandoned work
        rc = c.phase([SELFPLAY, s["model"], shard, config["games"], config["nodes"],
                      config["threads"], config["max_plies"], seed, args.backend, s["generation"],
                      config["parallel"]],
                     args.phase_seconds, "selfplay")
        if rc is None:
            break
        if not shard.exists():
            raise RuntimeError("no published self-play shard; partial games were not imported")
        count = sum(1 for _ in record_index(shard))
        if not count:
            break
        s["shards"].append(str(shard))
        s["positions"] += count
        s["credit"] += 4*sum(game % 20 != 0 for _, _, game, _, _ in record_index(shard))
        s["replay"] = pack_window(s["shards"], c.folder / "window.gnr", config["window"])
        atomic_json(str(shard)+".json", dict(sha256=sha256(shard), positions=count, seed=seed,
                    generation=s["generation"], model_sha256=sha256(s["model"]),
                    trace_sha256=sha256(str(shard)+".games.jsonl")))
        s["generation"] += 1
        c.save()
        finished += 1
    print(json.dumps(dict(state=str(c.path), charged_hours=s["spent_seconds"]/3600,
                          model=s["model"], positions=s["positions"], strength_verified=False)))


if __name__ == "__main__":
    main()
