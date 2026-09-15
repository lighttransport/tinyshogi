# SPDX-License-Identifier: Apache-2.0
"""Offline replay, persisted-budget, and draw-aware confidence checks."""
import json
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import dl_campaign as campaign
import dl_match


class Tools(unittest.TestCase):
    def test_rocm_preflight_uses_actual_batch(self):
        for backend in ("hip", "hip-blaslt"):
            commands = campaign.preflight_commands(backend, ROOT / "build", 16, False)
            self.assertEqual(commands[1][1][1], "hip-fp32")
            self.assertEqual(commands[2][0], "preflight-full")
            self.assertEqual(commands[2][1][1], backend)
            self.assertEqual(commands[2][1][-2:], ["full", "16"])
            self.assertEqual(len(campaign.preflight_commands(backend, ROOT / "build", 2, True)), 2)

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(dir=ROOT / "build", prefix="dl-tools-")
        self.addCleanup(self.tmp.cleanup)
        self.folder = Path(self.tmp.name)

    def test_replay_window_and_split(self):
        shard = self.folder / "data.gnr"
        with shard.open("wb") as out:
            out.write(campaign.HEADER)
            for game in (19, 20, 21):
                for ply in range(3):
                    out.write(struct.pack("<QQIII", game, 1, ply, 1, 1))
                    out.write(bytes(campaign.FEATURE_BYTES))
                    out.write(struct.pack("<II", 139, 10))
        window = self.folder / "window.gnr"
        info = campaign.pack_window([shard], window, 5)
        self.assertEqual((info["positions"], info["training"], info["validation"]), (5, 3, 2))
        self.assertEqual([r[2] for r in campaign.record_index(window)], [20, 20, 21, 21, 21])
        broken = self.folder / "broken.gnr"
        broken.write_bytes(shard.read_bytes()[:-1])
        with self.assertRaisesRegex(ValueError, "truncated"):
            list(campaign.record_index(broken))

    def test_lease_debit_before_process_and_resume(self):
        config = dict(hours=1)
        c = campaign.Campaign(self.folder, config)
        self.addCleanup(c.lock.close)
        def process(*args, **kwargs):
            state = json.loads(c.path.read_text())
            self.assertEqual(state["spent_seconds"], 10)
            self.assertEqual(state["lease"]["seconds"], 10)
            return type("Result", (), {"returncode": 0})()
        with patch.object(campaign.subprocess, "run", side_effect=process), patch.object(
                campaign.time, "monotonic", side_effect=[100, 102]):
            self.assertEqual(c.phase(["no-execution-in-test"], 10, "test"), 0)
        self.assertEqual(c.state["spent_seconds"], 2)
        c.state["lease"] = dict(expires_unix=0)
        c.state["spent_seconds"] = 20
        c.save()
        c.lock.close()
        resumed = campaign.Campaign(self.folder, config)
        self.addCleanup(resumed.lock.close)
        self.assertIsNone(resumed.state["lease"])
        self.assertEqual(resumed.state["spent_seconds"], 20)
        resumed.state["spent_seconds"] = 3600
        self.assertIsNone(resumed.phase(["must-not-launch"], 10, "over-budget"))

    def test_draw_aware_paired_confidence(self):
        games = [dict(id=i, opening=i//2, initial_sfen=str(i//2),
                      candidate_side="b" if i%2 == 0 else "w", result="draw") for i in range(1000)]
        result = dl_match.score_interval(games, samples=100)
        self.assertEqual(result["score_ci95"], [.5, .5])
        self.assertTrue(result["passed"])
        for g in games:
            g["result"] = "white" if g["candidate_side"] == "b" else "black"
        self.assertFalse(dl_match.score_interval(games, samples=100)["passed"])
        with self.assertRaisesRegex(ValueError, "pair"):
            dl_match.score_interval(games[:-1], samples=100)

    def test_duplicate_openings(self):
        path = self.folder / "openings.sfens"
        path.write_text("4k4/9/9/9/9/9/9/9/4K4 b - 1\n4k4/9/9/9/9/9/9/9/4K4 b - 2\n")
        with self.assertRaisesRegex(ValueError, "duplicate"):
            dl_match.positions(path)

    def test_referee_claims_and_time_failure(self):
        class FakeEngine:
            name = "fake"
            last_elapsed_ms = 1000
            last_info = {}
            move = "resign"
            def new_game(self): pass
            def bestmove(self, *args): return self.move
        class Referee:
            declaration = False
            def status(self, *args):
                return dict(result="ongoing", sfen="4k4/9/9/9/9/9/9/9/4K4 b - 1",
                            declaration=self.declaration, legal_moves=["5i5h"])
        e, r = FakeEngine(), Referee()
        game = dl_match.play_game([e, e], r, "opening", 0, "b", 0)
        self.assertEqual((game["result"], game["reason"]), ("white", "resign"))
        e.move = "win"
        with self.assertRaisesRegex(RuntimeError, "illegal declaration"):
            dl_match.play_game([e, e], r, "opening", 0, "b", 0)
        r.declaration = True
        self.assertEqual(dl_match.play_game([e, e], r, "opening", 0, "b", 0)["result"], "black")
        e.last_elapsed_ms = 1200
        with self.assertRaisesRegex(RuntimeError, "overrun"):
            dl_match.play_game([e, e], r, "opening", 0, "b", 0)


if __name__ == "__main__":
    unittest.main()
