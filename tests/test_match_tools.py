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
            engine = Engine("no-bestmove", program, {}, .2)
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
