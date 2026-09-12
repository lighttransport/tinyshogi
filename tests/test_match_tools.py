#!/usr/bin/env python3
"""Offline tests for USI transport, referee history, and the strength audit."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import match_gate
import selfplay_match
import strength_protocol
import blackbox_optimize
import compare_strength
import prepare_strength
from types import SimpleNamespace
from usi_engine import Engine

ENGINE = Path(sys.argv.pop(1)).resolve() if len(sys.argv) > 1 else ROOT / "build/make/tinyshogi"
KINGS = "4k4/9/9/9/9/9/9/9/4K4 b - 1"
MATE = "4k4/4G4/2N1S1N2/9/9/9/9/9/4K4 w - 1"


class RefereeTests(unittest.TestCase):
    def setUp(self):
        self.engine = Engine("test", ENGINE, {}, 5)
        self.addCleanup(self.engine.close)

    def test_both_hands_and_white_opening(self):
        sfen = KINGS.replace("b -", "w S2Pb3p")
        state = self.engine.status(sfen)
        self.assertEqual(state["sfen"], sfen)
        self.assertIn("B*4e", state["legal_moves"])

    def test_history_changes_terminal_result(self):
        moves = ["5i5h", "5a5b", "5h5i", "5b5a"] * 3
        state = self.engine.status(KINGS, moves)
        self.assertEqual((state["result"], state["reason"]), ("draw", "repetition"))
        self.assertEqual(self.engine.status(state["sfen"])["result"], "ongoing")

    def test_perpetual_check_is_loss_for_checker(self):
        state = self.engine.status("4R3k/9/9/9/9/9/9/9/K8 w - 1",
                                   ["1a1b", "5a5b", "1b1a", "5b5a"] * 3)
        self.assertEqual((state["result"], state["reason"]), ("white", "perpetual_check"))

    def test_illegal_drop_and_position_are_rejected(self):
        state = self.engine.status("4k4/9/2NG1GN2/9/9/9/9/9/4K4 b P 1")
        self.assertNotIn("P*5b", state["legal_moves"])
        with self.assertRaisesRegex(RuntimeError, "invalid position"):
            self.engine.status(KINGS, ["P*5b"])

    def test_zero_move_terminal_game_is_recorded(self):
        args = selfplay_match.parse_args(["--tinyshogi", str(ENGINE), "--yaneuraou", str(ENGINE)])
        args.referee = ENGINE
        records, game = selfplay_match.play_game(args, 0, MATE, None, ({}, {}))
        self.assertEqual(records, [])
        self.assertEqual((game["result"], game["plies"], game["decisions"]), ("black", 0, 0))

    def test_declaration_is_available_but_requires_claim(self):
        # Ten camp pieces, king in camp, 28 points with both major pieces in hand.
        sfen = "4K4/PPPPPPPPP/4G4/9/9/9/9/9/4k4 b 2R2B 1"
        state = self.engine.status(sfen)
        self.assertTrue(state["declaration"])
        self.assertEqual(state["result"], "ongoing")

    def test_option_validation(self):
        for options in ({"NotAnOption": 1}, {"Threads": 0}, {"AlphaBetaPolicy": "typo"},
                        {"QuiescenceChecks": "yes"}, {"QuiescenceHash": "yes"},
                        {"RootUpdates": "typo"}, {"TranspositionHistory": "unsafe"}):
            with self.subTest(options=options), self.assertRaises((ValueError, RuntimeError)):
                Engine("test", ENGINE, options, 5)

    def test_node_tolerance_is_explicit_and_per_engine(self):
        args = selfplay_match.parse_args(["--tinyshogi", str(ENGINE), "--yaneuraou", str(ENGINE),
                                          "--tinyshogi-node-tolerance", "0.10"])
        selfplay_match.validate_args(args)
        self.assertEqual(args.tinyshogi_node_tolerance, 0.10)
        bad = selfplay_match.parse_args(["--tinyshogi", str(ENGINE), "--yaneuraou", str(ENGINE),
                                         "--tinyshogi-node-tolerance", "1.1"])
        with self.assertRaises(ValueError):
            selfplay_match.validate_args(bad)

    def test_search_statistics_partition_reported_nodes(self):
        engine = Engine("search", ENGINE, {"SearchMode": "alphabeta", "Threads": 1}, 5)
        self.addCleanup(engine.close)
        engine.set_position([])
        engine.send("go nodes 200")
        engine.read_until("bestmove")
        info = engine.last_info
        self.assertEqual(info["nodes"], 200)
        self.assertEqual(sum(info[key] for key in ("mainnodes", "qnodes", "rootnodes")), 200)
        self.assertLessEqual(info["transcutoffs"], info["ttcutoffs"])

    def test_default_mode_and_explicit_mcts(self):
        self.assertIn("default alphabeta", self.engine.option_specs["SearchMode"][1])
        for option, value in (("QuiescenceDepth", "4"), ("CompletedResults", "true"),
                              ("BucketHash", "true"), ("QuiescenceRecaptures", "false"),
                              ("AlphaBetaPolicy", "selective"), ("TranspositionHistory", "shallow"),
                              ("QuiescenceHistory", "true"), ("QuiescencePruning", "true"),
                              ("RootReductions", "false")):
            self.assertIn("default " + value, self.engine.option_specs[option][1])
        for options in ({}, {"SearchMode": "mcts", "Threads": 1}):
            with self.subTest(options=options):
                engine = Engine("mode", ENGINE, options, 5)
                try:
                    engine.bestmove(KINGS, "nodes 7")
                    self.assertLessEqual(engine.last_nodes, 7)
                finally:
                    engine.close()


class ProtocolTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        positions = []
        for black in range(81):
            for white in range(81):
                if max(abs(black // 9 - white // 9), abs(black % 9 - white % 9)) <= 1:
                    continue
                ranks = []
                for rank in range(9):
                    text, empty = "", 0
                    for file in range(9):
                        square = rank * 9 + file
                        piece = "K" if square == black else "k" if square == white else ""
                        if piece:
                            text += (str(empty) if empty else "") + piece
                            empty = 0
                        else:
                            empty += 1
                    ranks.append(text + (str(empty) if empty else ""))
                positions.append("/".join(ranks) + " b - 1")
        self.positions = positions
        self.protocol = dict(version=2, budget="equal-request-1000",
                             model_sha256=strength_protocol.MODEL,
                             opponent=dict(commit=strength_protocol.OPPONENT_COMMIT, sha256=selfplay_match.sha256(ENGINE)),
                             baseline_sha256=selfplay_match.sha256(ENGINE), splits={})
        for i, phase in enumerate(strength_protocol.PHASES):
            path = self.root / (phase + ".sfens")
            path.write_text("\n".join(positions[i * 500:(i + 1) * 500]) + "\n")
            self.protocol["splits"][phase] = dict(file=path.name, sha256=selfplay_match.sha256(path))
        self.path = self.root / "protocol.json"
        self.path.write_text(json.dumps(self.protocol))

    def test_tuner_allowlist_and_split_integrity(self):
        development = self.root / "development.sfens"
        strength_protocol.validate_tuning_openings(development, self.path)
        for name in ("validation.sfens", "acceptance.sfens"):
            with self.assertRaisesRegex(ValueError, "registered development"):
                strength_protocol.validate_tuning_openings(self.root / name, self.path)
        subset = self.root / "subset.sfens"
        subset.write_text(development.read_text().splitlines()[0] + "\n")
        with self.assertRaisesRegex(ValueError, "registered development"):
            strength_protocol.validate_tuning_openings(subset, self.path)
        reserved = self.root / "acceptance.sfens"
        reserved.write_text(development.read_text())
        with self.assertRaisesRegex(ValueError, "modified"):
            strength_protocol.load_protocol(self.path)
        self.protocol["splits"]["acceptance"]["sha256"] = selfplay_match.sha256(reserved)
        self.path.write_text(json.dumps(self.protocol))
        with self.assertRaisesRegex(ValueError, "overlapping"):
            strength_protocol.load_protocol(self.path)

    def test_equal_request_failure_classification(self):
        opponent = dict(engine="YaneuraOu", nodes=9624)
        self.assertEqual(strength_protocol.fatal_violations([opponent], True), [])
        self.assertEqual(strength_protocol.fatal_violations([opponent]), [opponent])
        for violation in (dict(engine="YaneuraOu", nodes=None), dict(engine="tinyshogi", nodes=1001)):
            self.assertEqual(strength_protocol.fatal_violations([violation], True), [violation])

    def test_optimizer_command_has_no_hidden_budget_or_resampling(self):
        args = SimpleNamespace(match_script=ROOT / "scripts/selfplay_match.py", tinyshogi=ENGINE,
                               tinyshogi_eval_plugin=ENGINE, nn_bin=ENGINE, yaneuraou=ENGINE,
                               yaneuraou_eval_dir=self.root, tinyshogi_threads=1, opponent_threads=1,
                               tinyshogi_nodes=1000, opponent_nodes=1000, games=100, max_plies=512,
                               openings=self.root / "development.sfens", opening_offset=50, jobs=1,
                               fv_scale=20, seed=1, timeout=30, protocol=self.path, diagnostic=False)
        with patch.object(blackbox_optimize.subprocess, "run") as run:
            blackbox_optimize.run_candidate(args, {}, self.root / "result")
        command = run.call_args.args[0]
        self.assertEqual(command[command.index("--tinyshogi-node-overrun") + 1], "0")
        self.assertNotIn("--random-openings", command)
        self.assertNotIn("--strict", command)
        self.assertIn("--protocol", command)

    def test_protocol_rejects_weight_and_effective_budget_changes(self):
        args = selfplay_match.parse_args(["--tinyshogi", str(ENGINE), "--yaneuraou", str(ENGINE),
                                         "--protocol", str(self.path), "--tinyshogi-eval-plugin", str(ENGINE),
                                         "--tinyshogi-nn-bin", str(ENGINE), "--yaneuraou-eval-dir", str(self.root),
                                         "--openings", str(self.root / "development.sfens")])
        options = selfplay_match.engine_options(args)
        with self.assertRaisesRegex(ValueError, "weights"):
            strength_protocol.validate_match(args, options)
        options[0]["NodeOverrun"] = 10
        with self.assertRaisesRegex(ValueError, "zero tinyshogi overrun"):
            strength_protocol.validate_match(args, options)

    def test_asymmetric_budgets_keep_direct_matches_equal(self):
        self.assertEqual(strength_protocol.node_budgets(self.protocol), (1000, 1000))
        self.protocol.update(version=3, budget="tiny-2000-yane-1000")
        self.path.write_text(json.dumps(self.protocol))
        self.assertEqual(strength_protocol.node_budgets(strength_protocol.load_protocol(self.path)), (2000, 1000))
        self.assertEqual(strength_protocol.node_budgets(self.protocol, direct=True), (2000, 2000))
        args = selfplay_match.parse_args(["--tinyshogi", str(ENGINE), "--yaneuraou", str(ENGINE),
                                         "--protocol", str(self.path), "--tinyshogi-eval-plugin", str(ENGINE),
                                         "--tinyshogi-nn-bin", str(ENGINE), "--yaneuraou-eval-dir", str(self.root),
                                         "--openings", str(self.root / "development.sfens")])
        options = selfplay_match.engine_options(args)
        # The budget is checked before loading weights: the right limit reaches
        # the deliberately invalid model; the wrong one fails immediately.
        with self.assertRaisesRegex(ValueError, "2000/1000"):
            strength_protocol.validate_match(args, options)
        args.tinyshogi_nodes = 2000
        with self.assertRaisesRegex(ValueError, "weights"):
            strength_protocol.validate_match(args, options)
        args.opponent_eval_plugin = ENGINE
        with self.assertRaisesRegex(ValueError, "2000/2000"):
            strength_protocol.validate_match(args, options)
        args.opponent_nodes = 2000
        with self.assertRaisesRegex(ValueError, "weights"):
            strength_protocol.validate_match(args, options)
        self.protocol["version"] = 2
        with self.assertRaisesRegex(ValueError, "unsupported"):
            strength_protocol.node_budgets(self.protocol)

    def test_fresh_split_excludes_both_historical_sets(self):
        sources = [self.root / (name + ".txt") for name in ("ply24", "ply32")]
        for i, source in enumerate(sources):
            source.write_text("\n".join(self.positions[i * 2500:(i + 1) * 2500]) + "\n")
        old = prepare_strength.split_openings(sources)
        fresh = prepare_strength.campaign_splits(sources)
        historical = {strength_protocol.position_key(sfen) for group in old for sfen in group}
        selected = [strength_protocol.position_key(sfen) for group in fresh.values() for sfen in group]
        self.assertEqual(len(selected), 1500)
        self.assertEqual(len(set(selected)), 1500)
        self.assertFalse(historical.intersection(selected))
        self.assertEqual(fresh, prepare_strength.campaign_splits(sources))
        next_round = prepare_strength.campaign_splits(sources, seed=20260913,
                            excluded_positions=[sfen for group in fresh.values() for sfen in group])
        next_keys = {strength_protocol.position_key(sfen) for group in next_round.values() for sfen in group}
        self.assertEqual(len(next_keys), 1500)
        self.assertFalse(next_keys.intersection(selected))
        self.assertFalse(next_keys.intersection(historical))

    def test_acceptance_requires_qualified_frozen_candidate(self):
        with self.assertRaisesRegex(ValueError, "requires a candidate lock"):
            strength_protocol.validate_lock(None, "protocol", "engine", "plugin", {})
        report = self.root / "comparison.json"
        report.write_text(json.dumps(dict(acceptance_eligible=False, promotion_supported=False,
                                         candidate=dict(games=1000, wins=340))))
        lock_path = self.root / "lock.json"
        lock = dict(version=1, protocol_sha256="protocol", candidate_sha256="engine", plugin_sha256="plugin",
                    options={}, report=str(report), validation={str(report): selfplay_match.sha256(report)})
        lock_path.write_text(json.dumps(lock))
        with self.assertRaisesRegex(ValueError, "not qualified"):
            strength_protocol.validate_lock(lock_path, "protocol", "engine", "plugin", {})
        with self.assertRaisesRegex(ValueError, "does not match"):
            strength_protocol.validate_lock(lock_path, "protocol", "different-engine", "plugin", {})
        report.write_text("{}")
        with self.assertRaisesRegex(ValueError, "modified validation"):
            strength_protocol.validate_lock(lock_path, "protocol", "engine", "plugin", {})

    def test_paired_comparison_counts_draws_correctly(self):
        games = [dict(initial_sfen=KINGS, tinyshogi_side="b", result="black"),
                 dict(initial_sfen=KINGS, tinyshogi_side="w", result="draw")]
        self.assertEqual(list(compare_strength.pair_values(games).values()), [1])
        self.assertEqual(list(compare_strength.pair_values(games, score=True).values()), [1.5])
        comparison = compare_strength.compare(games, games, games)
        self.assertEqual(comparison["paired_change_95_interval"], [0, 0])
        self.assertFalse(comparison["promotion_supported"])

    def test_equal_request_gate_checks_effective_protocol(self):
        args = selfplay_match.parse_args(["--tinyshogi", str(ENGINE), "--yaneuraou", str(ENGINE),
                                         "--protocol", str(self.path), "--phase", "validation",
                                         "--yaneuraou-eval-dir", str(self.root)])
        manifest = dict(version=4, strict=False, protocol=self.protocol,
                        protocol_sha256=selfplay_match.sha256(self.path), arguments=vars(args),
                        node_tolerance={"tinyshogi": 0.0, "YaneuraOu": 0.0},
                        engine_sha256=[selfplay_match.sha256(ENGINE)] * 2,
                        model_sha256=strength_protocol.MODEL, opponent_model_sha256=strength_protocol.MODEL,
                        openings_sha256=self.protocol["splits"]["validation"]["sha256"],
                        engine_options=selfplay_match.engine_options(args), node_audit_passed=False)
        sfen = (self.root / "validation.sfens").read_text().splitlines()[0]
        games = [dict(game=i, opening=0, initial_sfen=sfen, tinyshogi_side=side, result="draw")
                 for i, side in enumerate(("b", "w"))]
        violations = [dict(engine="YaneuraOu", nodes=1200)]
        self.assertEqual(match_gate.protocol_errors(manifest, games, violations, self.path, "validation"), [])
        for key, value in (("model_sha256", "wrong"), ("protocol_sha256", "modified"),
                           ("engine_sha256", [selfplay_match.sha256(ENGINE), "different-opponent"])):
            changed = copy.deepcopy(manifest)
            changed[key] = value
            self.assertTrue(match_gate.protocol_errors(changed, games, violations, self.path, "validation"))
        changed = copy.deepcopy(manifest)
        changed["engine_options"][0]["NodeOverrun"] = 10
        self.assertTrue(match_gate.protocol_errors(changed, games, violations, self.path, "validation"))
        violations[0]["nodes"] = None
        self.assertTrue(match_gate.protocol_errors(manifest, games, violations, self.path, "validation"))

        self.protocol.update(version=3, budget="tiny-2000-yane-1000")
        self.path.write_text(json.dumps(self.protocol))
        manifest["protocol_sha256"] = selfplay_match.sha256(self.path)
        manifest["arguments"]["tinyshogi_nodes"] = 2000
        self.assertEqual(match_gate.protocol_errors(manifest, games, [], self.path, "validation"), [])
        self.assertTrue(match_gate.protocol_errors(manifest, games,
                        [dict(engine="tinyshogi", nodes=2001)], self.path, "validation"))
        manifest["arguments"]["opponent_eval_plugin"] = str(ENGINE)
        self.assertTrue(match_gate.protocol_errors(manifest, games, [], self.path, "validation"))
        manifest["arguments"]["opponent_nodes"] = 2000
        self.assertEqual(match_gate.protocol_errors(manifest, games, [], self.path, "validation"), [])
        self.assertTrue(match_gate.protocol_errors(manifest, games,
                        [dict(engine="YaneuraOu", nodes=2001)], self.path, "validation"))

    def test_qualified_lock_recomputes_game_evidence(self):
        report = dict(acceptance_eligible=True, promotion_supported=True, candidate=dict(games=1000, wins=850))
        report_path = self.root / "report.json"
        report_path.write_text(json.dumps(report))
        artifacts = {str(report_path): selfplay_match.sha256(report_path)}
        records = {}
        for role in ("candidate", "baseline", "direct"):
            records[role] = str(self.root / (role + ".jsonl"))
            for suffix in ("", ".manifest.json", ".games.jsonl"):
                path = Path(records[role] + suffix)
                path.write_text("{}")
                artifacts[str(path)] = selfplay_match.sha256(path)
        protocol_sha = selfplay_match.sha256(self.path)
        lock = dict(version=1, protocol_sha256=protocol_sha, candidate_sha256="engine", plugin_sha256="plugin",
                    options={}, protocol_file=str(self.path), report=str(report_path), validation=artifacts, records=records)
        lock_path = self.root / "lock.json"
        lock_path.write_text(json.dumps(lock))
        candidate = dict(engine_sha256=["engine", "opponent"], plugin_sha256="plugin", engine_options=[{}, {}])
        with patch.object(compare_strength, "audit_comparison", return_value=(report, candidate)) as audit:
            self.assertEqual(strength_protocol.validate_lock(lock_path, protocol_sha, "engine", "plugin", {}), lock)
            audit.assert_called_once()
        with patch.object(compare_strength, "audit_comparison", return_value=({"acceptance_eligible": False}, candidate)):
            with self.assertRaisesRegex(ValueError, "disagrees with validation"):
                strength_protocol.validate_lock(lock_path, protocol_sha, "engine", "plugin", {})


class TransportTests(unittest.TestCase):
    def test_fragmented_stdout_and_large_stderr(self):
        with tempfile.TemporaryDirectory() as directory:
            program = Path(directory) / "engine"
            program.write_text("#!" + sys.executable + "\n" + '''
import os, sys
for line in sys.stdin:
    if line.strip() == 'usi':
        os.write(2, b'diagnostic ' * 100000)
        os.write(1, b'usi')
        os.write(1, b'ok\\n')
    elif line.strip() == 'isready':
        print('readyok', flush=True)
    elif line.strip() == 'quit':
        break
''')
            program.chmod(0o700)
            engine = Engine("fragmented", program, {}, 5)
            engine.close()
            self.assertIsNotNone(engine.process.poll())

    def test_continuous_info_does_not_extend_deadline(self):
        with tempfile.TemporaryDirectory() as directory:
            program = Path(directory) / "engine"
            program.write_text("#!" + sys.executable + "\n" + '''
import sys, time
for line in sys.stdin:
    if line.strip() == 'usi':
        print('usiok', flush=True)
    elif line.strip() == 'isready':
        print('readyok', flush=True)
    elif line.startswith('go'):
        for i in range(1000):
            print('info nodes 1', flush=True)
            time.sleep(.01)
''')
            program.chmod(0o700)
            engine = Engine("no-bestmove", program, {}, 5)
            engine.timeout = .2  # Test the search deadline, not Python startup under load.
            try:
                started = time.monotonic()
                with self.assertRaisesRegex(RuntimeError, "timeout"):
                    engine.bestmove(KINGS, "nodes 1")
                self.assertLess(time.monotonic() - started, 2)
            finally:
                engine.close()


class AuditTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "match.jsonl"
        self.games = [dict(game=i, opening=0, initial_sfen=KINGS, final_sfen=KINGS,
                           tinyshogi_side="b" if i == 0 else "w", result="black", complete=True,
                           decisions=0, plies=0, reason="no_legal_moves", node_violations=[])
                      for i in range(2)]
        self.manifest = dict(version=3, complete=True, completed_games=2,
                             arguments=dict(games=2, nodes=1000, movetime_ms=None),
                             model_sha256=None, node_audit_passed=True)
        self.records = []

    def save(self):
        self.path.write_text("".join(json.dumps(record) + "\n" for record in self.records))
        summaries = Path(str(self.path) + ".games.jsonl")
        summaries.write_text("".join(json.dumps(game) + "\n" for game in self.games))
        self.manifest.update(records_sha256=selfplay_match.sha256(self.path),
                             summaries_sha256=selfplay_match.sha256(summaries))
        Path(str(self.path) + ".manifest.json").write_text(json.dumps(self.manifest))

    def test_complete_zero_move_games_and_pair_bootstrap(self):
        self.save()
        _, games, violations, _, _ = match_gate.load_match(self.path)
        self.assertEqual(match_gate.summarize(games)["wins"], 1)
        self.assertEqual(match_gate.paired_counts(games), [1])
        self.assertEqual(match_gate.bootstrap_interval([1], samples=100), [.5, .5])
        self.assertEqual(violations, [])

    def test_corrupted_and_incomplete_artifacts(self):
        self.save()
        self.path.write_text("{}\n")
        with self.assertRaisesRegex(ValueError, "checksum"):
            match_gate.load_match(self.path)
        self.manifest["complete"] = False
        self.save()
        with self.assertRaisesRegex(ValueError, "incomplete"):
            match_gate.load_match(self.path)

    def test_missing_and_duplicate_games(self):
        self.games.pop()
        self.save()
        with self.assertRaisesRegex(ValueError, "missing"):
            match_gate.load_match(self.path)
        self.games.append(copy.deepcopy(self.games[0]))
        self.save()
        with self.assertRaisesRegex(ValueError, "duplicate"):
            match_gate.load_match(self.path)

    def test_per_game_node_audit_is_recomputed(self):
        self.games[1].update(decisions=1, plies=1)
        self.records = [dict(game=1, ply=0, side="b", sfen=KINGS, engine="YaneuraOu",
                             opening=0, move="5i5h", result="black", model_sha256=None,
                             reported_nodes=1051, node_limit=1000, elapsed_ms=1)]
        self.save()
        with self.assertRaisesRegex(ValueError, "node audit"):
            match_gate.load_match(self.path)
        self.games[1]["node_violations"] = [dict(ply=0, engine="YaneuraOu",
                                                reported_nodes=1051, node_limit=1000)]
        self.manifest["node_audit_passed"] = False
        self.save()
        self.assertEqual(len(match_gate.load_match(self.path)[2]), 1)
        self.records[0]["node_limit"] = 2000
        self.save()
        with self.assertRaisesRegex(ValueError, "budget"):
            match_gate.load_match(self.path)

    def test_draws_are_not_wins_and_pairs_must_be_distinct(self):
        self.games[1]["result"] = "draw"
        result = match_gate.summarize(self.games)
        self.assertEqual((result["win_rate"], result["score"]), (.5, .75))
        duplicate = copy.deepcopy(self.games)
        for game in duplicate:
            game["opening"] = 1
        with self.assertRaisesRegex(ValueError, "repeated opening"):
            match_gate.paired_counts(self.games + duplicate)
        with self.assertRaisesRegex(ValueError, "unmatched"):
            match_gate.paired_counts(self.games[:1])

    def test_v3_recomputes_tiny_node_partitions_including_direct_opponent(self):
        self.manifest["protocol"] = {"version": 3}
        self.manifest["arguments"]["opponent_eval_plugin"] = "baseline-plugin"
        for game, name in ((0, "tinyshogi"), (1, "YaneuraOu")):
            for summary in self.games:
                summary.update(decisions=0, plies=0)
            self.games[game].update(decisions=1, plies=1)
            self.records = [dict(game=game, ply=0, side="b", sfen=KINGS, engine=name,
                                 opening=0, move="5i5h", result="black", model_sha256=None,
                                 reported_nodes=1000, node_limit=1000, elapsed_ms=1,
                                 search_info=dict(nodes=1000, mainnodes=100, qnodes=800, rootnodes=100))]
            self.save()
            self.assertEqual(match_gate.load_match(self.path)[2], [])
            for field, value in (("qnodes", 799), ("rootnodes", None), ("nodes", 999)):
                original = self.records[0]["search_info"][field]
                self.records[0]["search_info"][field] = value
                self.save()
                with self.assertRaisesRegex(ValueError, "node categories"):
                    match_gate.load_match(self.path)
                self.records[0]["search_info"][field] = original

    def test_fixed_gate_cannot_be_relaxed(self):
        self.save()
        with patch.object(match_gate, "protocol_errors", return_value=[]), \
                patch.object(match_gate, "validation_errors", return_value=[]), patch("builtins.print"):
            self.assertEqual(match_gate.main([str(self.path), "--games", "2",
                                               "--minimum-wins", "1"]), 1)

    def test_validation_reports_bind_the_actual_artifacts(self):
        manifest = dict(engine_sha256=["candidate", "opponent"], plugin_sha256="plugin",
                        referee_sha256="referee")
        parity = Path(self.directory.name) / "parity.json"
        rules = Path(self.directory.name) / "rules.json"
        parity.write_text(json.dumps(dict(exact_match=True, positions=1000,
                          engine_sha256=manifest["engine_sha256"], plugin_sha256="plugin",
                          model_sha256=match_gate.PINNED_MODEL, fv_scale=20)))
        rules.write_text(json.dumps(dict(exact_match=True, positions=5000,
                         engine_sha256="referee", oracle="python-shogi", oracle_version="1.1.1")))
        self.assertEqual(match_gate.validation_errors(manifest, parity, rules), [])
        manifest["engine_sha256"] = ["changed", "opponent"]
        self.assertTrue(match_gate.validation_errors(manifest, parity, rules))
        self.assertEqual(len(match_gate.validation_errors(manifest, None, None)), 2)


if __name__ == "__main__":
    unittest.main()
