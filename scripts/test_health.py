#!/usr/bin/env python3
"""test_health — regression tests for `scripts/health.sh`'s baseline reporting.

`health.sh` turns "known pre-existing findings" into `[warn]` (exit 0) and
everything *above* the recorded baseline into `[FAIL]` (exit 1).  That rule is
the whole gate: a baseline that silently absorbs a new finding is the same as no
gate at all, and a baseline that fails on its own recorded counts is unusable.

The tests do not run the real checks.  They copy `health.sh` into a temporary
repository next to stub `doc_index.py` / `import_components.py` /
`check-gitbook-drift` scripts whose findings are set by environment variables,
so each test drives exactly one branch of the classification:

  * clean           → three `[pass]`, exit 0
  * at baseline     → `[warn]`, exit 0 (6 unnamed components, 86 stale roots,
                      11 uncited Lean identifiers is the recorded state)
  * above baseline  → `[FAIL]`, exit 1 (7 / 87 / 12 — one over each)
  * hard structural → `[FAIL]` even when every count is at baseline
  * stale doc index → `[FAIL]`, exit 1
  * no ../test      → `[gap]`, exit 0 (the drift check is skipped, not passed)

Usage:  python3 scripts/test_health.py
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEALTH = ROOT / "scripts" / "health.sh"

DOC_STUB = '''#!/usr/bin/env python3
import os
import sys

if os.environ.get("DOC_STALE") == "1":
    print("[stale] DOC_INDEX.md (0 docs)")
    sys.exit(1)
print("[fresh] DOC_INDEX.md (3 docs)")
sys.exit(0)
'''

IMP_STUB = '''#!/usr/bin/env python3
import os
import sys

names = int(os.environ.get("IMP_NAMES", "0"))
roots = int(os.environ.get("IMP_ROOTS", "0"))
hard = int(os.environ.get("IMP_HARD", "0"))
for i in range(hard):
    print("[hard] component %d: cone of the roots differs" % i)
for i in range(names):
    print("MISSING NAME component%d" % i)
for i in range(roots):
    print("root%d not listed in lakefile.toml" % i)
sys.exit(0)
'''

DRIFT_STUB = '''#!/usr/bin/env bash
lean=${DRIFT_LEAN:-0}
rust=${DRIFT_RUST:-0}
for ((i = 0; i < lean; i++)); do echo "[MISS lean] identifier$i page.md"; done
for ((i = 0; i < rust; i++)); do echo "[MISS rust] suite$i page.md"; done
exit 0
'''


class HealthBaselineTest(unittest.TestCase):
    """Each test drives one branch of `health.sh`'s baseline classification."""

    def setUp(self) -> None:
        self.tmp = Path(tempfile.mkdtemp(prefix="health-test-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.repo = self.tmp / "repo"
        scripts = self.repo / "scripts"
        scripts.mkdir(parents=True)
        shutil.copy(HEALTH, scripts / "health.sh")
        (scripts / "doc_index.py").write_text(DOC_STUB)
        (scripts / "import_components.py").write_text(IMP_STUB)
        (scripts / "check-gitbook-drift").write_text(DRIFT_STUB)
        # `health.sh` looks for the GitBook at `../test` from the repo root.
        (self.tmp / "test").mkdir()

    def run_health(self, **env_overrides: str) -> tuple[int, str]:
        env = {k: v for k, v in os.environ.items() if not k.startswith(("IMP_", "DOC_", "DRIFT_"))}
        env.update(env_overrides)
        proc = subprocess.run(
            ["bash", str(self.repo / "scripts" / "health.sh")],
            capture_output=True,
            text=True,
            env=env,
        )
        return proc.returncode, proc.stdout + proc.stderr

    # -- the clean case ----------------------------------------------------

    def test_clean_run_passes_and_exits_zero(self) -> None:
        code, out = self.run_health()
        self.assertEqual(code, 0, out)
        self.assertIn("[pass] doc index fresh", out)
        self.assertIn("[pass] import components gate", out)
        self.assertIn("— health: 3 pass, 0 warn, 0 gap, 0 fail —", out)

    # -- the baseline is a warning, not a failure --------------------------

    def test_import_findings_at_baseline_warn(self) -> None:
        code, out = self.run_health(IMP_NAMES="6", IMP_ROOTS="86")
        self.assertEqual(code, 0, out)
        self.assertIn("[warn] import components gate — at baseline (6 unnamed comps, 86 stale roots", out)
        self.assertIn("— health: 2 pass, 1 warn, 0 gap, 0 fail —", out)

    def test_gitbook_citations_at_baseline_warn(self) -> None:
        code, out = self.run_health(DRIFT_LEAN="11")
        self.assertEqual(code, 0, out)
        self.assertIn("[warn] gitbook citation drift — at baseline (11 lean, 0 rust", out)

    # -- one finding over the baseline is a regression ---------------------

    def test_one_unnamed_component_above_baseline_fails(self) -> None:
        code, out = self.run_health(IMP_NAMES="7", IMP_ROOTS="86")
        self.assertEqual(code, 1, out)
        self.assertIn("[FAIL] import components gate — notices above baseline (+1 name", out)
        self.assertIn("— health: 2 pass, 0 warn, 0 gap, 1 fail —", out)

    def test_one_stale_root_above_baseline_fails(self) -> None:
        code, out = self.run_health(IMP_NAMES="6", IMP_ROOTS="87")
        self.assertEqual(code, 1, out)
        self.assertIn("[FAIL] import components gate — notices above baseline", out)
        self.assertIn("+1 root", out)

    def test_one_citation_above_baseline_fails(self) -> None:
        code, out = self.run_health(DRIFT_LEAN="12")
        self.assertEqual(code, 1, out)
        self.assertIn("[FAIL] gitbook citation drift — above baseline", out)

    # -- hard errors fail regardless of the counts -------------------------

    def test_hard_structural_error_fails_at_baseline_counts(self) -> None:
        code, out = self.run_health(IMP_NAMES="6", IMP_ROOTS="86", IMP_HARD="1")
        self.assertEqual(code, 1, out)
        self.assertIn("[FAIL] import components gate — 1 HARD structural error", out)
        self.assertNotIn("at baseline", out)

    def test_stale_doc_index_fails(self) -> None:
        code, out = self.run_health(DOC_STALE="1")
        self.assertEqual(code, 1, out)
        self.assertIn("[FAIL] doc index fresh", out)

    # -- a skipped check is a gap, never a pass ----------------------------

    def test_missing_gitbook_is_a_gap_not_a_pass(self) -> None:
        shutil.rmtree(self.tmp / "test")
        code, out = self.run_health()
        self.assertEqual(code, 0, out)
        self.assertIn("[gap]  ../test GitBook not present", out)
        self.assertIn("— health: 2 pass, 0 warn, 1 gap, 0 fail —", out)


if __name__ == "__main__":
    sys.exit(unittest.main())
