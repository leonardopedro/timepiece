#!/usr/bin/env python3
"""G6: roll board observations up into CONSOLIDATED_PLAN.md.

## Why

`CONSOLIDATED_PLAN.md` is ~16,400 lines of append-only dated state entries, and
it absorbs every observation because it is the only place observations go. That
is the problem G6 names: the board is where *plan* knowledge belongs, so the plan
file can stop being a dumping ground.

This script is the bridge. It reads the board's NDJSON snapshot, groups entries
by month, and appends one rollup section per month to `CONSOLIDATED_PLAN.md`.

## The rule that matters

**It appends. It never edits.** `CONSOLIDATED_PLAN.md` is append-only by house
rule and roughly 16k lines long; a script that "tidies" it would silently
rewrite state entries other agents are citing. The only write this performs is a
single appended block at end of file, and it refuses to write twice for the same
month unless `--force` is passed.

That refusal is the whole safety story. A rollup that runs twice must not produce
two sections claiming to be the month's summary, because the second one would be
indistinguishable from a correction.

## It writes no Lean

Every entry this reads is prose about modules, theorems and dependencies. Nothing
here writes, compiles, or interprets a `.lean` file; those items are work orders
for the LLM-Lean4-specialist and are emitted as text only.

Usage:
    python3 scripts/board_rollup.py --board BOARD.ndjson --month 2026-10
    python3 scripts/board_rollup.py --board BOARD.ndjson --month 2026-10 --dry-run
    python3 scripts/board_rollup.py --board BOARD.ndjson --list-months
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Marker that identifies a rollup this script wrote. Idempotence is checked
# against this rather than against the section title, because the title carries a
# month that a hand-written entry could also contain.
MARKER = "<!-- board-rollup -->"

# The kinds that carry weight in a handover. `OBSERVED` is deliberately absent:
# it is by definition a conclusion-free note, and promoting a pile of them would
# bury the entries that actually tell a specialist something.
KIND_ORDER = ["FAIL", "FACT", "CLAIM", "PATCH_SUMMARY"]

KIND_MEANING = {
    "FACT": "established (ideally with evidence in the entry)",
    "FAIL": "an approach that did not work, and why — the highest-value kind",
    "CLAIM": "a scope a worker held",
    "PATCH_SUMMARY": "a change plus its machine-generated gate output",
}


def repo_root() -> str:
    """The timepiece root, found the same way every other script here does."""
    out = ROOT
    while out != "/":
        if os.path.isfile(os.path.join(out, "CONSOLIDATED_PLAN.md")):
            return out
        out = os.path.dirname(out)
    return ROOT


def load_board(path: str) -> list[dict]:
    """Parse the board NDJSON snapshot.

    Skips the meta line and any unparseable line rather than failing: this is a
    reporting script, and refusing to produce a handover because one line is
    malformed would make it useless exactly when the corpus is in trouble.
    """
    if not os.path.isfile(path):
        raise SystemExit(f"board snapshot not found: {path}")
    entries = []
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError as e:
                print(f"[warn] {path}:{lineno}: skipped ({e})", file=sys.stderr)
                continue
            if not isinstance(rec, dict) or rec.get("record") == "meta":
                continue
            if "cursor" not in rec or "text" not in rec:
                print(f"[warn] {path}:{lineno}: not an entry, skipped", file=sys.stderr)
                continue
            rec.setdefault("kind", "OBSERVED")
            rec.setdefault("worker", "?")
            rec.setdefault("ts", "")
            entries.append(rec)
    return entries


def month_of(entry: dict) -> str:
    """`YYYY-MM` for an entry.

    Entries written by `Board::write` carry no timestamp — the board is an
    in-process structure and adding wall-clock to it would make the log
    non-deterministic, which the cursor ordering exists to avoid. So a month comes
    from `ts` when the writer supplied one, and otherwise from the snapshot
    file's own mtime, which is the honest "when did this reach disk" answer.
    """
    ts = (entry.get("ts") or "").strip()
    if ts:
        m = re.match(r"(\d{4})-(\d{2})", ts)
        if m:
            return f"{m.group(1)}-{m.group(2)}"
    return _snapshot_month(entry)


def _snapshot_month(entry: dict) -> str:
    stamp = entry.get("_snapshot_mtime")
    if isinstance(stamp, (int, float)):
        return datetime.fromtimestamp(stamp, tz=timezone.utc).strftime("%Y-%m")
    return "undated"


def group_by_month(entries: list[dict]) -> dict[str, list[dict]]:
    out: dict[str, list[dict]] = {}
    for e in entries:
        out.setdefault(month_of(e), []).append(e)
    return out


def render(month: str, entries: list[dict], forced: bool = False) -> str:
    """Build the markdown block for one month."""
    by_kind: dict[str, list[dict]] = {}
    for e in entries:
        by_kind.setdefault(str(e.get("kind", "OBSERVED")).upper(), []).append(e)

    counted = sum(len(v) for k, v in by_kind.items() if k in KIND_ORDER)
    lines = [
        "",
        MARKER,
        f'## State of the project — {month} (board rollup)',
        "",
        f"Machine-generated from the shared board by `scripts/board_rollup.py`."
        f" **{counted}** weighted entr{'y' if counted == 1 else 'ies'} across"
        f" {len(entries)} total. This is a rollup of board observations, not a"
        f" plan: the authoritative work order per track is `CURRENT_WORK_ORDER.md`.",
        "",
    ]
    if forced:
        lines += [
            "> ⚠ **Forced re-roll.** A rollup for this month already existed and was"
            " replaced. The previous block is retained below this one rather than"
            " deleted, per the append-only house rule.",
            "",
        ]

    any_kind = False
    for kind in KIND_ORDER:
        group = by_kind.get(kind)
        if not group:
            continue
        any_kind = True
        lines.append(f"### {kind} — {KIND_MEANING[kind]}")
        lines.append("")
        for e in sorted(group, key=lambda r: r.get("cursor", 0)):
            worker = e.get("worker", "?")
            cursor = e.get("cursor", "?")
            text = str(e.get("text", "")).strip().replace("\n", " ")
            detail = e.get("detail")
            if detail:
                text += " — " + str(detail).strip().replace("\n", " ")
            lines.append(f"- `{worker}` (cursor {cursor}): {text}")
        lines.append("")

    if not any_kind:
        lines += [
            "No weighted entries this month. `OBSERVED` entries are excluded by"
            " design: they are conclusions-free notes, and surfacing them would"
            " bury the entries that tell a specialist something.",
            "",
        ]

    lines += [
        "**Handover note.** Every item above is a work order for the"
        " LLM-Lean4-specialist. No `.lean` file was written or compiled to produce"
        " this section.",
        "",
    ]
    return "\n".join(lines)


def already_rolled(plan_path: str, month: str) -> bool:
    """Whether a rollup for `month` is already present.

    Checked by marker *and* month, so a hand-written section that merely shares a
    heading is not mistaken for ours — and ours is not missed because someone
    reworded the title.
    """
    if not os.path.isfile(plan_path):
        return False
    with open(plan_path, encoding="utf-8") as fh:
        text = fh.read()
    needle = f'## State of the project — {month} (board rollup)'
    for block in text.split(MARKER)[1:]:
        if needle in block:
            return True
    return False


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--board", default="BOARD.ndjson", help="board NDJSON snapshot")
    ap.add_argument("--plan", default=None, help="CONSOLIDATED_PLAN.md to append to")
    ap.add_argument("--month", help="YYYY-MM to roll up")
    ap.add_argument(
        "--list-months", action="store_true", help="print the months present and exit"
    )
    ap.add_argument("--dry-run", action="store_true", help="print the block, write nothing")
    ap.add_argument(
        "--force",
        action="store_true",
        help="append a second rollup for a month that already has one (old one kept)",
    )
    args = ap.parse_args()

    root = repo_root()
    board_path = args.board if os.path.isabs(args.board) else os.path.join(root, args.board)
    plan_path = args.plan or os.path.join(root, "CONSOLIDATED_PLAN.md")

    entries = load_board(board_path)
    if not entries:
        print(f"[info] no board entries in {board_path}")
        return 0

    mtime = os.path.getmtime(board_path)
    for e in entries:
        e["_snapshot_mtime"] = mtime

    months = group_by_month(entries)
    if args.list_months:
        for month in sorted(months):
            print(f"{month}\t{len(months[month])}")
        return 0

    if not args.month:
        print(
            "[error] --month is required (or --list-months). Refusing to append a "
            "rollup for every month at once: a single run should produce one "
            "dated section.",
            file=sys.stderr,
        )
        return 2

    month = args.month
    if month not in months:
        print(
            f"[error] no board entries for {month}. Present: "
            f"{', '.join(sorted(months)) or '(none)'}",
            file=sys.stderr,
        )
        return 1

    dupe = already_rolled(plan_path, month)
    if dupe and not args.force:
        print(
            f"[error] {month} already has a rollup in {os.path.basename(plan_path)}. "
            "A second one would be indistinguishable from a correction. "
            "Pass --force to append anyway (the old block is kept).",
            file=sys.stderr,
        )
        return 1

    block = render(month, months[month], forced=dupe)
    if args.dry_run:
        print(block)
        return 0

    # Append-only. One write, at end of file, nothing else touched.
    with open(plan_path, "a", encoding="utf-8") as fh:
        fh.write(block)
    print(
        f"[ok] appended {len(months[month])} entr"
        f"{'y' if len(months[month]) == 1 else 'ies'} for {month} to "
        f"{os.path.basename(plan_path)}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())