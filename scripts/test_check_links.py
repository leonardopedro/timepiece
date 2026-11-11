#!/usr/bin/env python3
"""Regression tests for `scripts/check-links`.

The gate's contract is one sentence — *a relative link in a document the
repository contains must resolve* — and the whole of its scope logic is which
documents those are.  Two rules carry it, and each has a test here:

1. **The default run checks git-*tracked* markdown.**  A file that is never
   committed, or is git-ignored (the root `.gitignore` lists the PDF-to-markdown
   dumps whose figures were never extracted with them), is not part of the
   repository, so it is skipped rather than allowed to fail the gate.
2. **An explicit `FILE` argument is checked regardless.**  Naming a document is
   a request to check it, not a request to check the index.
3. **A target outside the repository root is out of scope.**  A document may
   cite a sibling workspace (`../unfer/...`, `../papers/...`); that file is not
   this checkout's to contain.  `..` that stays inside the root is still
   checked — the rule is the root boundary, not parent references.

The gate is still a *gate*: a broken link in a tracked document must exit
non-zero, and the no-git fallback (when `git` cannot be consulted at all) must
fall back to the working tree instead of silently checking nothing.

Stdlib only — runs under `python3` anywhere, no pytest. Run directly:

    python3 scripts/test_check_links.py
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check-links")


def have_git() -> bool:
    return shutil.which("git") is not None


class LinkScopeTests(unittest.TestCase):
    """Document scope: tracked vs untracked vs git-ignored, and explicit FILEs."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = self._tmp.name
        # A copy of the gate at `<root>/scripts/check-links`, because the script
        # derives the repository root from its own location.
        os.makedirs(os.path.join(self.root, "scripts"))
        self.script = os.path.join(self.root, "scripts", "check-links")
        shutil.copyfile(SCRIPT, self.script)
        # `[x](missing.md)` is a broken relative link: missing.md is never created.
        self.doc = "# doc\n\nsee [the other one](missing.md)\n"

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write(self, name: str, text: str | None = None) -> str:
        path = os.path.join(self.root, name)
        os.makedirs(os.path.dirname(path), exist_ok=True) if os.path.dirname(path) else None
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(self.doc if text is None else text)
        return path

    def git(self, *args: str) -> None:
        subprocess.run(
            ["git", "-C", self.root, *args],
            check=True,
            capture_output=True,
        )

    def init_repo(self) -> None:
        self.git("init", "-q")
        self.git("config", "user.email", "test@example.com")
        self.git("config", "user.name", "test")

    def run_gate(self, *args: str, path: str | None = None) -> subprocess.CompletedProcess:
        env = dict(os.environ)
        if path is not None:
            env["PATH"] = path
        return subprocess.run(
            [sys.executable, self.script, *args],
            cwd=self.root,
            capture_output=True,
            text=True,
            env=env,
        )

    @unittest.skipUnless(have_git(), "git is not installed")
    def test_tracked_document_with_broken_link_fails(self) -> None:
        self.init_repo()
        self.write("tracked.md")
        self.git("add", "tracked.md")
        res = self.run_gate()
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        self.assertIn("tracked.md", res.stderr)
        self.assertIn("missing.md", res.stderr)

    @unittest.skipUnless(have_git(), "git is not installed")
    def test_git_ignored_document_is_skipped_by_default(self) -> None:
        self.init_repo()
        self.write(".gitignore", "dump.md\n")
        self.write("dump.md")  # broken link, but git-ignored
        self.git("add", ".gitignore")
        res = self.run_gate()
        # `dump.md` is the only markdown file; skipping it leaves nothing to
        # check, and "no documents" is a failure of its own.
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        self.assertIn("no markdown files found", res.stderr)
        self.assertNotIn("dump.md:", res.stderr)

    @unittest.skipUnless(have_git(), "git is not installed")
    def test_untracked_document_is_skipped_by_default(self) -> None:
        self.init_repo()
        self.write("untracked.md")  # never added to the index
        res = self.run_gate()
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        self.assertIn("no markdown files found", res.stderr)

    @unittest.skipUnless(have_git(), "git is not installed")
    def test_git_ignored_document_fails_when_named_explicitly(self) -> None:
        self.init_repo()
        self.write(".gitignore", "dump.md\n")
        self.write("dump.md")
        self.git("add", ".gitignore")
        res = self.run_gate("dump.md")
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        self.assertIn("dump.md", res.stderr)
        self.assertIn("missing.md", res.stderr)

    @unittest.skipUnless(have_git(), "git is not installed")
    def test_tracked_document_alone_reports_ok(self) -> None:
        self.init_repo()
        self.write("good.md", "# doc\n\nsee [the other one](tracked.md)\n")
        self.write("tracked.md", "# target\n")
        self.git("add", "good.md", "tracked.md")
        res = self.run_gate()
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertIn("2 document(s)", res.stdout)

    @unittest.skipUnless(have_git(), "git is not installed")
    def test_ignored_document_does_not_mask_a_tracked_failure(self) -> None:
        """The scoping is per document, not an escape hatch for the gate."""
        self.init_repo()
        self.write(".gitignore", "dump.md\n")
        self.write("dump.md")
        self.write("tracked.md")
        self.git("add", ".gitignore", "tracked.md")
        res = self.run_gate()
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        self.assertIn("tracked.md", res.stderr)
        self.assertNotIn("dump.md:", res.stderr)

    @unittest.skipUnless(have_git(), "git is not installed")
    def test_out_of_root_target_is_out_of_scope(self) -> None:
        """A sibling workspace's file is not this checkout's to contain."""
        self.init_repo()
        self.write("doc.md", "# doc\n\nsee [sibling](../sibling/missing.md)\n")
        self.git("add", "doc.md")
        res = self.run_gate()
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertIn("external skipped", res.stdout)

    @unittest.skipUnless(have_git(), "git is not installed")
    def test_out_of_root_target_does_not_mask_an_in_root_failure(self) -> None:
        self.init_repo()
        self.write("doc.md", "# doc\n\nsee [s](../sibling/missing.md) and [m](missing.md)\n")
        self.git("add", "doc.md")
        res = self.run_gate()
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        self.assertIn("missing.md", res.stderr)
        self.assertNotIn("sibling", res.stderr)

    @unittest.skipUnless(have_git(), "git is not installed")
    def test_parent_reference_inside_root_is_still_checked(self) -> None:
        """The boundary is the root, not the `..` itself."""
        self.init_repo()
        self.write("sub/doc.md", "# doc\n\nsee [up](../gone.md)\n")
        self.git("add", "sub/doc.md")
        res = self.run_gate()
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        self.assertIn("sub/doc.md:3: ../gone.md -> gone.md (missing)", res.stderr)

    def test_no_git_falls_back_to_the_working_tree(self) -> None:
        """Without `git` the index is unknowable, so every document is checked."""
        self.write("dump.md")
        res = self.run_gate(path=os.path.join(self.root, "no-such-bin"))
        self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
        self.assertIn("dump.md", res.stderr)
        self.assertIn("missing.md", res.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
