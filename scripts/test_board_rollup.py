#!/usr/bin/env python3
"""G6: tests for `scripts/board_rollup.py`.

The script's whole safety story is three claims, and each one is a test here:

1. **It appends, never edits.** A run may only add bytes at end of file; the
   bytes that were there before must survive byte-for-byte.
2. **It refuses to roll the same month twice.** A second rollup would be
   indistinguishable from a correction, which is exactly the ambiguity the
   append-only rule exists to prevent — unless `--force` is passed explicitly,
   and even then the old block is kept.
3. **`--dry-run` writes nothing.**

Plus the reporting behaviour a reader relies on: FAIL-first ordering,
`OBSERVED` excluded by design, month attribution, and parsing that skips
malformed lines rather than dying with the corpus.

Stdlib only — runs under `python3` anywhere, no pytest. Run directly:

    python3 scripts/test_board_rollup.py
"""
from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = importlib.util.spec_from_file_location(
    "board_rollup", os.path.join(HERE, "board_rollup.py")
)
board_rollup = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(board_rollup)

BOARD_LINES = [
    json.dumps({"record": "meta", "note": "not an entry"}),
    json.dumps(
        {
            "cursor": 2,
            "kind": "FACT",
            "worker": "w2",
            "ts": "2026-10-05T00:00:00Z",
            "text": "the gate is green",
        }
    ),
    json.dumps(
        {
            "cursor": 1,
            "kind": "FAIL",
            "worker": "w1",
            "ts": "2026-10-01T00:00:00Z",
            "text": "approach X failed",
            "detail": "because rank collapsed",
        }
    ),
    json.dumps(
        {
            "cursor": 3,
            "kind": "OBSERVED",
            "worker": "w3",
            "ts": "2026-10-06T00:00:00Z",
            "text": "a conclusion-free note",
        }
    ),
    json.dumps({"cursor": 4, "text": "no kind, no worker, no ts"}),
    json.dumps(
        {"cursor": 5, "kind": "CLAIM", "ts": "2026-09-30T00:00:00Z", "text": "september"}
    ),
    "{ this line is not json",
    json.dumps({"note": "no cursor and no text — not an entry"}),
]


def run_main(argv: list[str]) -> tuple[int, str, str]:
    """Call `main()` with `argv`, capturing stdout/stderr and its exit code."""
    out, err = io.StringIO(), io.StringIO()
    old_argv = sys.argv
    sys.argv = ["board_rollup.py", *argv]
    try:
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = board_rollup.main()
    finally:
        sys.argv = old_argv
    return code, out.getvalue(), err.getvalue()


class BoardRollupTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="board_rollup_test_")
        self.addCleanup(self.tmp.cleanup)
        self.board = os.path.join(self.tmp.name, "BOARD.ndjson")
        with open(self.board, "w", encoding="utf-8") as fh:
            fh.write("\n".join(BOARD_LINES) + "\n")
        # Pin the snapshot mtime: entries with no `ts` are bucketed by it, and
        # a test whose month depends on when it runs is a test that fails in
        # November. 1 759 276 800 = 2025-10-01 00:00 UTC.
        os.utime(self.board, (1_759_276_800, 1_759_276_800))
        self.plan = os.path.join(self.tmp.name, "CONSOLIDATED_PLAN.md")
        with open(self.plan, "w", encoding="utf-8") as fh:
            fh.write("# existing plan content\n")

    def plan_text(self) -> str:
        with open(self.plan, encoding="utf-8") as fh:
            return fh.read()

    # ---- parsing ----------------------------------------------------------

    def test_load_board_keeps_entries_and_skips_noise(self):
        entries = board_rollup.load_board(self.board)
        # meta line, malformed line, and cursor-less line all skipped; the five
        # real entries survive (the warn goes to stderr, not an exception).
        self.assertEqual(len(entries), 5)
        texts = [e["text"] for e in entries]
        self.assertIn("approach X failed", texts)
        self.assertIn("no kind, no worker, no ts", texts)

    def test_missing_board_is_a_system_exit_not_a_traceback(self):
        with self.assertRaises(SystemExit):
            board_rollup.load_board(os.path.join(self.tmp.name, "nope.ndjson"))

    def test_defaults_fill_kind_worker_and_ts(self):
        entries = board_rollup.load_board(self.board)
        bare = next(e for e in entries if e["text"] == "no kind, no worker, no ts")
        self.assertEqual(bare["kind"], "OBSERVED")
        self.assertEqual(bare["worker"], "?")

    # ---- month attribution ------------------------------------------------

    def test_month_prefers_the_writer_timestamp(self):
        self.assertEqual(
            board_rollup.month_of({"ts": "2026-10-01T12:00:00Z"}), "2026-10"
        )

    def test_month_falls_back_to_the_snapshot_mtime(self):
        # Entries written by Board::write carry no ts; the snapshot's mtime is
        # the honest "when did this reach disk" answer.
        entry = {"ts": "", "_snapshot_mtime": 1_759_276_800}  # 2025-10-01 UTC
        self.assertEqual(board_rollup.month_of(entry), "2025-10")

    def test_group_by_month_separates_entries(self):
        months = board_rollup.group_by_month(board_rollup.load_board(self.board))
        self.assertIn("2026-10", months)
        self.assertIn("2026-09", months)

    # ---- rendering --------------------------------------------------------

    def test_render_puts_fail_first_and_excludes_observed(self):
        entries = board_rollup.load_board(self.board)
        block = board_rollup.render("2026-10", entries)
        self.assertLess(
            block.index("### FAIL"), block.index("### FACT"), "FAIL must lead"
        )
        self.assertNotIn("a conclusion-free note", block)
        self.assertNotIn("No weighted entries this month", block)
        self.assertNotIn("### OBSERVED", block)

    def test_render_counts_only_weighted_kinds(self):
        entries = [
            {"cursor": 1, "kind": "FAIL", "worker": "w", "text": "a"},
            {"cursor": 2, "kind": "OBSERVED", "worker": "w", "text": "b"},
            {"cursor": 3, "kind": "FACT", "worker": "w", "text": "c"},
        ]
        block = board_rollup.render("2026-10", entries)
        # 2 weighted (FAIL+FACT) of 3 total — OBSERVED must not be counted.
        self.assertIn("**2** weighted entries across 3 total", block)

    def test_render_carries_the_append_only_and_no_lean_disclaimers(self):
        block = board_rollup.render(
            "2026-10", [{"cursor": 1, "kind": "FACT", "worker": "w", "text": "x"}]
        )
        self.assertIn(board_rollup.MARKER, block)
        self.assertIn("No `.lean` file was written or compiled", block)

    # ---- idempotence markers ---------------------------------------------

    def test_already_rolled_needs_our_marker_not_just_a_heading(self):
        month = "2026-10"
        needle = f"## State of the project — {month} (board rollup)"
        # A hand-written section with the same heading is NOT ours.
        with open(self.plan, "w", encoding="utf-8") as fh:
            fh.write(f"# plan\n\n{needle}\n")
        self.assertFalse(board_rollup.already_rolled(self.plan, month))
        # Ours (marker + month) is detected...
        with open(self.plan, "w", encoding="utf-8") as fh:
            fh.write(f"# plan\n\n{board_rollup.MARKER}\n{needle}\n")
        self.assertTrue(board_rollup.already_rolled(self.plan, month))
        # ...including for a *different* month's rollup: markers for other
        # months do not make this month look rolled.
        self.assertFalse(board_rollup.already_rolled(self.plan, "2026-11"))

    # ---- main(): the three claims ----------------------------------------

    def test_main_appends_once_then_refuses_and_never_edits(self):
        before = self.plan_text()
        code, _, err = run_main(
            ["--board", self.board, "--plan", self.plan, "--month", "2026-10"]
        )
        self.assertEqual(code, 0, err)
        after_first = self.plan_text()
        self.assertTrue(after_first.startswith(before), "append-only: prefix must survive")
        self.assertGreater(len(after_first), len(before))

        # Second run: refused (exit 1) and the file is byte-identical.
        code, _, err = run_main(
            ["--board", self.board, "--plan", self.plan, "--month", "2026-10"]
        )
        self.assertEqual(code, 1)
        self.assertIn("already has a rollup", err)
        self.assertEqual(self.plan_text(), after_first)

    def test_dry_run_writes_nothing(self):
        before = self.plan_text()
        code, out, _ = run_main(
            [
                "--board",
                self.board,
                "--plan",
                self.plan,
                "--month",
                "2026-10",
                "--dry-run",
            ]
        )
        self.assertEqual(code, 0)
        self.assertIn(board_rollup.MARKER, out)
        self.assertEqual(self.plan_text(), before)

    def test_force_appends_a_second_block_and_keeps_the_old_one(self):
        run_main(["--board", self.board, "--plan", self.plan, "--month", "2026-10"])
        first = self.plan_text()
        code, _, _ = run_main(
            [
                "--board",
                self.board,
                "--plan",
                self.plan,
                "--month",
                "2026-10",
                "--force",
            ]
        )
        self.assertEqual(code, 0)
        after = self.plan_text()
        self.assertTrue(after.startswith(first), "--force must keep the old block")
        self.assertEqual(after.count(board_rollup.MARKER), 2)
        self.assertIn("Forced re-roll", after)

    def test_missing_month_exits_1_and_absent_month_flag_exits_2(self):
        code, _, err = run_main(
            ["--board", self.board, "--plan", self.plan, "--month", "2001-01"]
        )
        self.assertEqual(code, 1)
        self.assertIn("no board entries for 2001-01", err)
        self.assertIn("2026-10", err)  # the error names what IS present

        code, _, err = run_main(["--board", self.board, "--plan", self.plan])
        self.assertEqual(code, 2)
        self.assertIn("--month is required", err)
        self.assertEqual(self.plan_text(), "# existing plan content\n")

    def test_list_months_prints_sorted_month_counts(self):
        code, out, _ = run_main(["--board", self.board, "--list-months"])
        self.assertEqual(code, 0)
        rows = [line.split("\t") for line in out.strip().splitlines()]
        self.assertEqual([m for m, _ in rows], sorted(m for m, _ in rows))
        counts = dict(rows)
        # 3 with an October ts + the ts-less entry bucketed by the pinned
        # snapshot mtime (2025-10); the September CLAIM stands alone.
        self.assertEqual(counts["2026-10"], "3")
        self.assertEqual(counts["2026-09"], "1")
        self.assertEqual(counts["2025-10"], "1")


if __name__ == "__main__":
    unittest.main(verbosity=2)
