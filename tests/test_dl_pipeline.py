"""A native self-play/train/reload cycle with no Python ML dependencies."""
import json
from pathlib import Path
import subprocess
import tempfile
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from dl_campaign import checkpoint_info


def run(*args, **kwargs):
    result = subprocess.run(list(map(str, args)), cwd=ROOT, text=True,
                            capture_output=True, timeout=180, **kwargs)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return result.stdout


def main():
    # Keep generated artifacts in this repository (including GEMM workflows).
    with tempfile.TemporaryDirectory(prefix="dl-test-", dir=ROOT / "build") as tmp:
        folder = Path(tmp)
        model, trained, data = folder / "initial.safetensors", folder / "trained.safetensors", folder / "selfplay.gnr"
        tool = ROOT / "third_party/gemm/nn/build/gn_tool"
        run(tool, "init", model, 8, 2)
        run(ROOT / "build/dl/dl-selfplay", model, data, 2, 8, 2, 8, 7, "cpu", 1, 2)
        games = [json.loads(line) for line in Path(str(data) + ".games.jsonl").read_text().splitlines()]
        assert len(games) == 2 and all(len(g["moves"]) == 8 for g in games)
        metrics = [json.loads(line) for line in run(tool, "train", data, model, trained, 3, 4, .001, "cpu", 2, 1).splitlines()]
        assert metrics[-1]["step"] == 3
        assert trained.read_bytes() != model.read_bytes()
        assert checkpoint_info(trained)["step"] == 3
        validated = json.loads(run(tool, "validate", data, trained, "cpu", 100))
        assert validated["step"] == 3 and validated["validation_positions"] == 0
        run(sys.executable, "-B", ROOT / "tools/dl_campaign.py", "--run-dir", folder / "campaign",
            "--backend", "cpu", "--smoke", "--hours", .1, "--generations", 2)
        state = json.loads((folder / "campaign/state.json").read_text())
        assert state["positions"] == 32 and checkpoint_info(state["model"])["step"] == 16
        charged = state["spent_seconds"]
        run(sys.executable, "-B", ROOT / "tools/dl_campaign.py", "--run-dir", folder / "campaign",
            "--backend", "cpu", "--smoke", "--hours", .1, "--generations", 1)
        state = json.loads((folder / "campaign/state.json").read_text())
        assert state["positions"] == 48 and state["spent_seconds"] > charged
        assert checkpoint_info(state["model"])["step"] == 32
        output = run(ROOT / "build/dl/tinyshogi", input=(
            f"usi\nsetoption name DLModel value {trained}\n"
            "setoption name SearchMode value puct\nsetoption name Threads value 2\n"
            "isready\nposition startpos\ngo nodes 8\n"))
        assert "DL model loaded" in output and "readyok" in output
        assert "bestmove " in output and "bestmove resign" not in output
        broken = folder / "truncated.gnr"
        broken.write_bytes(data.read_bytes()[:-1])
        result = subprocess.run([str(tool), "train", str(broken), str(trained), str(folder / "bad.safetensors"), "1", "1", ".001", "cpu"], capture_output=True)
        assert result.returncode and not (folder / "bad.safetensors").exists()
    print("PASS native self-play -> packed replay -> train -> USI reload, truncated replay rejection")


if __name__ == "__main__":
    main()
