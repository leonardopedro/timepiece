#!/usr/bin/env bash
# Apply tracked patches to the (gitignored) Verso checkout under .lake/packages.
#
# Two patches are needed on top of stock Verso v4.28.0:
#   1. verso-0001-annotate-subparts.patch  — the Timepiece root manual includes 26
#      chapters; without annotating the sub-parts array the root `#doc` fails to
#      elaborate (stuck genre metavariable, `PartMetadata ?m`).
#   2. verso-0002-toc-fragment-links.patch — empty-path ToC entries must emit
#      `#fragment` anchors, not `href="/"`; otherwise the in-body Table of Contents
#      navigates to the output directory's file listing instead of scrolling.
# Because .lake/ is not tracked by git, this script must be re-run after any
# fresh clone or `lake update`.
#
# Usage:  ./patches/apply-verso-patches.sh
# Idempotent: safe to run multiple times.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERSO="$ROOT/.lake/packages/verso"

if [[ ! -d "$VERSO/.git" ]]; then
  echo "error: $VERSO is not a git checkout. Run 'lake build' (or 'lake update') first." >&2
  exit 1
fi

apply_one () {
  local patch="$1"
  local name="$(basename "$patch")"
  if git -C "$VERSO" apply --reverse --check "$patch" 2>/dev/null; then
    echo "skip   $name (already applied)"
  elif git -C "$VERSO" apply --check "$patch" 2>/dev/null; then
    git -C "$VERSO" apply "$patch"
    echo "applied $name"
  else
    echo "error: $name does not apply cleanly to $VERSO" >&2
    echo "       (verso version may have changed; rebase the patch)" >&2
    exit 1
  fi
}

apply_one "$ROOT/patches/verso-0001-annotate-subparts.patch"
apply_one "$ROOT/patches/verso-0002-toc-fragment-links.patch"
echo "Done. Rebuild with: lake build book && lake exe book"
