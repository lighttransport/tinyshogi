"""Shared, frozen benchmark configuration (legacy strict is separate)."""

import hashlib
import json
from pathlib import Path

MODEL = "1141d275bceec911156801f27303dc9ff5beb24f4f59144cc069306c59e80782"
OPPONENT_COMMIT = "33ccf1f907eb7184889fa23051243f81ab0bf973"
LEGACY_DEVELOPMENT = "c9104e0042cd95e56f617169bb533c70cbd8268fa931bd3c034bee7d834f4824"
LEGACY_HELDOUT = "c4864ddfb5c1672c19aabfa6891deea99407679e5bf32e9f81ed67ca8762be6a"
PHASES = ("development", "validation", "acceptance")


def node_budgets(protocol, direct=False):
    """Direct comparisons give both tinyshogi builds the candidate budget."""
    if protocol.get("version") == 2 and protocol.get("budget") == "equal-request-1000":
        return 1000, 1000
    if protocol.get("version") == 3 and protocol.get("budget") == "tiny-2000-yane-1000":
        return 2000, 2000 if direct else 1000
    raise ValueError("unsupported strength protocol budget")


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def position_key(sfen):
    return " ".join(sfen.removeprefix("sfen ").split()[:3])


def load_protocol(path):
    path = Path(path)
    protocol = json.loads(path.read_text())
    node_budgets(protocol)
    if (protocol.get("model_sha256") != MODEL
            or protocol.get("opponent", {}).get("commit") != OPPONENT_COMMIT):
        raise ValueError("unsupported strength protocol")
    seen = set()
    for phase in PHASES:
        split = protocol["splits"][phase]
        source = path.parent / split["file"]
        if sha256(source) != split["sha256"]:
            raise ValueError(f"modified {phase} split")
        keys = [position_key(line) for line in source.read_text().splitlines()]
        if len(keys) != 500 or len(set(keys)) != 500 or seen.intersection(keys):
            raise ValueError("overlapping, duplicate or incomplete opening splits")
        seen.update(keys)
    return protocol


def validate_match(args, options):
    """Validate before starting engines, including final effective USI options."""
    protocol = load_protocol(args.protocol)
    tiny_nodes, opponent_nodes = node_budgets(protocol, bool(args.opponent_eval_plugin))
    if args.strict:
        raise ValueError("--protocol and legacy --strict are mutually exclusive")
    if (args.movetime_ms is not None or (args.tinyshogi_nodes or args.nodes) != tiny_nodes
            or (args.opponent_nodes or args.nodes) != opponent_nodes or args.hash_mb != 64
            or args.tinyshogi_threads != 1 or args.opponent_threads != 1
            or args.fv_scale != 20 or args.max_plies != 512
            or args.tinyshogi_search_mode != "alphabeta"
            or args.tinyshogi_nn_bin is None or args.tinyshogi_eval_plugin is None
            or args.tinyshogi_node_overrun != 0 or args.random_openings
            or int(options[0].get("NodeOverrun", -1)) != 0):
        raise ValueError(f"protocol requires fixed shared NNUE, {tiny_nodes}/{opponent_nodes} node requests "
                         "and zero tinyshogi overrun")
    if sha256(args.tinyshogi_nn_bin) != MODEL:
        raise ValueError("wrong protocol weights")
    expected_opponent = protocol["opponent"]["sha256"]
    if args.opponent_eval_plugin:
        if args.phase == "acceptance":
            raise ValueError("acceptance requires YaneuraOu")
        expected_opponent = protocol["baseline_sha256"]
    elif args.yaneuraou_eval_dir is None:
        raise ValueError("protocol requires opponent NNUE directory")
    if sha256(args.yaneuraou) != expected_opponent:
        raise ValueError("opponent does not match frozen protocol")
    if args.openings is None or sha256(args.openings) != protocol["splits"][args.phase]["sha256"]:
        raise ValueError("openings do not match registered phase")
    if args.phase == "acceptance" and (args.games != 1000 or args.opening_offset != 0):
        raise ValueError("acceptance requires all 1000 games")
    if args.phase == "acceptance":
        validate_lock(args.candidate_lock, sha256(args.protocol), sha256(args.tinyshogi),
                      sha256(args.tinyshogi_eval_plugin), options[0])
    # Actual opponent overruns remain recorded, including those below 5%.
    args.tinyshogi_node_tolerance = args.opponent_node_tolerance = 0.0
    return protocol


def fatal_violations(violations, equal_requests=False):
    return [v for v in violations if not equal_requests or
            v["engine"] == "tinyshogi" or
            v.get("nodes", v.get("reported_nodes")) is None]


def validate_tuning_openings(openings, protocol_path=None):
    if protocol_path:
        protocol = load_protocol(protocol_path)
        permitted = protocol["splits"]["development"]["sha256"]
    else:
        permitted = LEGACY_DEVELOPMENT
    if sha256(openings) != permitted:
        raise ValueError("tuning requires the registered development split; reserved or unregistered openings are forbidden")


def validate_lock(path, protocol_sha, candidate_sha, plugin_sha, options):
    if path is None:
        raise ValueError("acceptance requires a candidate lock from qualified validation")
    lock = json.loads(Path(path).read_text())
    if (lock.get("version") != 1 or lock.get("protocol_sha256") != protocol_sha or
            lock.get("candidate_sha256") != candidate_sha or lock.get("plugin_sha256") != plugin_sha or
            lock.get("options") != json.loads(json.dumps(options, default=str))):
        raise ValueError("candidate lock does not match the experiment")
    for artifact, digest in lock["validation"].items():
        if sha256(artifact) != digest:
            raise ValueError("modified validation artifact")
    if lock["report"] not in lock["validation"]:
        raise ValueError("unregistered validation report")
    report = json.loads(Path(lock["report"]).read_text())
    if (not report.get("acceptance_eligible") or not report.get("promotion_supported") or
            report["candidate"]["games"] != 1000 or report["candidate"]["wins"] < 850):
        raise ValueError("validation has not qualified for acceptance")
    if sha256(lock["protocol_file"]) != protocol_sha:
        raise ValueError("modified validation protocol")
    # Recompute eligibility from the audited games rather than trusting flags
    # in a report. The local import avoids a transport/protocol import cycle.
    from compare_strength import audit_comparison
    records = lock["records"]
    for path in records.values():
        if any(path + suffix not in lock["validation"] for suffix in ("", ".manifest.json", ".games.jsonl")):
            raise ValueError("unregistered validation match")
    actual, candidate = audit_comparison(records["candidate"], records["baseline"], records["direct"],
                                        lock["protocol_file"])
    if (actual != report or candidate["engine_sha256"][0] != candidate_sha or
            candidate["plugin_sha256"] != plugin_sha or candidate["engine_options"][0] != lock["options"]):
        raise ValueError("candidate lock disagrees with validation games")
    return lock
