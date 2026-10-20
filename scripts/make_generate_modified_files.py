#!/usr/bin/env python3
"""Rebuild `generate_modified_files.sh` from the current state of the repository.

The generated script is self-contained: it embeds (as a base64 tar.gz) the exact
contents of every git-tracked file of the project except the excluded inputs listed
in EXCLUDE below, plus the list of paths that no longer exist in the project and must
be removed from an older checkout.

Usage (from the repository root):
    python3 scripts/make_generate_modified_files.py [--out generate_modified_files.sh]

Sources for the deletion list (all paths that are *absent* from the current tree):
  * the manifest and old-path list of the previous `generate_modified_files.sh`
    (if it exists when this script runs);
  * the old module paths in BOOKPROOF_PHASE1_MOVES.md, BOOKPROOF_PHASE2_MOVES.md,
    BOOKPROOF_PHASE2B_MOVES.md;
  * the removals recorded in BOOKPROOF_SPLIT_PLAN.md (the 9 empty legacy stubs and the
    junk-sweep files);
  * EXTRA_REMOVED below.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import io
import os
import re
import subprocess
import sys
import tarfile

EXCLUDE_PREFIXES = ("Downloads/",)
EXCLUDE_FILES = {
    "generate_modified_files.sh",  # the script itself
    "repomix-output.xml",          # unchanged input snapshot dump (23 MB)
}

# Removals recorded in BOOKPROOF_SPLIT_PLAN.md (§1 junk sweep, §9 Phase 0 residue).
LEGACY_STUBS = [
    "EsaClosure", "FarisLavine", "HashimotoShiftInvert", "HermiteCore",
    "NavierStokesFlow", "SirkSpectralGeometry", "Starobinsky",
    "YangMillsFriedrichs", "YangMillsHermite",
]
EXTRA_REMOVED = [f"BookProof/{n}.lean" for n in LEGACY_STUBS] + [
    "BookProof/faris_lavine_witness.lean",
    "BookProof/ChapterYangMillsFockESA_tmp.lean",
    "ScriptSketchInfo.lean",
    "BookProof/WeylSL2/ChapterWeylSl2.lean",  # Phase 3 rename -> ChapterWeylSL2Algebra
    "YNOT_IGNORED",
]
MOVE_TABLES = [
    "BOOKPROOF_PHASE1_MOVES.md",
    "BOOKPROOF_PHASE2_MOVES.md",
    "BOOKPROOF_PHASE2B_MOVES.md",
]

TEMPLATE_HEADER = r'''#!/usr/bin/env bash
# =============================================================================
# generate_modified_files.sh
#
# Brings a checkout of this repository to the current state of the project:
# the conversion of `Downloads/` to Lean 4.28.0 (`converted/`) and the execution
# of CONSOLIDATED_PLAN.md / BOOKPROOF_SPLIT_PLAN.md (Phases 0, 1, 1.5, 2, 2.2b, 3,
# QG flat-side transfer, ...).
#
# It embeds the exact current contents of @NFILES@ files (base64 tar.gz):
# every file of the project except the unchanged inputs `Downloads/**` and
# `repomix-output.xml` (and this script itself). Embedded paths include
#   * converted/**                        the whole conversion folder
#   * BookProof.lean, BookProof/**        incl. all moved modules at their new paths
#   * Book/**, Work/**, Audits/**, ...    every Lean file of the other libraries
#   * lakefile.toml, lean-toolchain, lake-manifest.json, the plan / status
#     documents, decl_graph*.jsonl, state/, scripts/ (incl. the generator
#     scripts/make_generate_modified_files.py that rebuilt this file)
#
# It also REMOVES the files that no longer exist in the project (@NREMOVED@
# recorded paths: old locations of the modules moved in split-plan Phases 1, 2
# and 2.2b, the Phase 0 orphan `BookProof/X/Part*.lean` split copies, the 9 empty
# legacy stubs, superseded `converted/` files, ...), plus — as a sweep — any
# other `*.lean` file under `BookProof/` and any file under `converted/` that is
# not part of the embedded snapshot (these two trees are fully regenerated).
#
# Usage:
#   bash generate_modified_files.sh [options] [TARGET_DIR]     (default TARGET_DIR: .)
#
# Options:
#   --list            only print the paths of the embedded files, write nothing
#   --list-removed    only print the recorded removed paths, write nothing
#   --verify          after writing, check every file against its SHA-256 checksum
#   --no-prune        write the files but delete nothing
#   --no-sweep        delete only the recorded removed paths (skip the sweep of
#                     unknown files under BookProof/ and converted/)
#   --dry-run         write nothing, delete nothing: print what would be deleted
#   -h, --help        show this help
#
# Existing files at the same paths are overwritten. Every deleted path is
# printed. Nothing outside TARGET_DIR is touched; `.lake/` is never touched.
# Requires: bash, tar, gzip, base64 (or openssl), sha256sum (or shasum) for --verify.
# =============================================================================
set -euo pipefail

LIST=0; LISTRM=0; VERIFY=0; PRUNE=1; SWEEP=1; DRYRUN=0; TARGET="."
while [ $# -gt 0 ]; do
  case "$1" in
    --list) LIST=1 ;;
    --list-removed) LISTRM=1 ;;
    --verify) VERIFY=1 ;;
    --no-prune) PRUNE=0 ;;
    --no-sweep) SWEEP=0 ;;
    --dry-run) DRYRUN=1 ;;
    -h|--help) awk 'NR > 1 && /^#/ { print; next } NR > 1 { exit }' "$0"; exit 0 ;;
    -*) echo "unknown option: $1" >&2; exit 2 ;;
    *) TARGET="$1" ;;
  esac
  shift
done

SELF=$(cd "$(dirname "$0")" && pwd)/$(basename "$0")
payload() {
  local line
  line=$(awk '/^__PAYLOAD_BELOW__$/ { print NR + 1; exit 0; }' "$SELF")
  tail -n +"$line" "$SELF" | { base64 -d 2>/dev/null || base64 -D 2>/dev/null || openssl base64 -d -A; }
}

checksums() {
cat <<'__SHA256SUMS__'
'''

TEMPLATE_MIDDLE = r'''__SHA256SUMS__
}

removed() {
cat <<'__REMOVED__'
'''

TEMPLATE_FOOTER = r'''__REMOVED__
}

if [ "$LIST" = 1 ]; then checksums | sed 's/^[0-9a-f]*  //'; exit 0; fi
if [ "$LISTRM" = 1 ]; then removed; exit 0; fi

mkdir -p "$TARGET"
cd "$TARGET"

if [ "$DRYRUN" = 0 ]; then
  echo "Writing @NFILES@ files into $(pwd) ..."
  payload | tar -xzf - --no-same-owner
  echo "Done."
fi

if [ "$VERIFY" = 1 ] && [ "$DRYRUN" = 0 ]; then
  if command -v sha256sum >/dev/null 2>&1; then SHA="sha256sum -c --quiet"; else SHA="shasum -a 256 -c --quiet"; fi
  if checksums | $SHA; then echo "Verify: all @NFILES@ files match."; else echo "Verify: MISMATCH (see above)." >&2; exit 1; fi
fi

if [ "$PRUNE" = 1 ]; then
  MANIFEST=$(mktemp)
  checksums | sed 's/^[0-9a-f]*  //' | sort > "$MANIFEST"
  DELS=$(mktemp); trap 'rm -f "$MANIFEST" "$DELS"' EXIT
  # 1. recorded removed paths (never a path of the current snapshot)
  while IFS= read -r p; do
    [ -n "$p" ] || continue
    if [ -e "$p" ] && ! grep -qxF -- "$p" "$MANIFEST"; then echo "$p" >> "$DELS"; fi
  done < <(removed)
  # 2. sweep: stale files in the fully regenerated trees
  if [ "$SWEEP" = 1 ]; then
    for root in BookProof converted; do
      [ -d "$root" ] || continue
      if [ "$root" = BookProof ]; then
        find "$root" -path '*/.lake' -prune -o -type f -name '*.lean' -print
      else
        find "$root" -path '*/.lake' -prune -o -type f -print
      fi
    done | sed 's#^\./##' | while IFS= read -r p; do
      if ! grep -qxF -- "$p" "$MANIFEST"; then echo "$p" >> "$DELS"; fi
    done
  fi
  sort -u "$DELS" | while IFS= read -r p; do
    [ -n "$p" ] || continue
    if [ "$DRYRUN" = 1 ]; then echo "would delete: $p"; else rm -f -- "$p"; echo "deleted: $p"; fi
  done
  if [ "$DRYRUN" = 0 ]; then
    for root in BookProof converted; do
      [ -d "$root" ] && find "$root" -mindepth 1 -type d -empty -delete
    done
  fi
fi
exit 0
__PAYLOAD_BELOW__
'''


def git_files() -> list[str]:
    out = subprocess.run(["git", "ls-files", "-z"], check=True, capture_output=True).stdout
    files = [f for f in out.decode().split("\0") if f]
    keep = []
    for f in files:
        if f in EXCLUDE_FILES or f.startswith(EXCLUDE_PREFIXES):
            continue
        if not os.path.isfile(f):
            continue
        keep.append(f)
    return sorted(keep)


def old_script_paths(path: str) -> set[str]:
    if not os.path.isfile(path):
        return set()
    paths: set[str] = set()
    mode = None
    with open(path, "r", errors="replace") as fh:
        for line in fh:
            s = line.rstrip("\n")
            if s == "__PAYLOAD_BELOW__":
                break
            if s in ("cat <<'__SHA256SUMS__'",):
                mode = "sum"; continue
            if s in ("cat <<'__OLDPATHS__'", "cat <<'__REMOVED__'"):
                mode = "old"; continue
            if s in ("__SHA256SUMS__", "__OLDPATHS__", "__REMOVED__"):
                mode = None; continue
            if mode == "sum":
                m = re.match(r"^[0-9a-f]{64}  (.+)$", s)
                if m:
                    paths.add(m.group(1))
            elif mode == "old" and s:
                paths.add(s)
    return paths


def move_table_paths() -> set[str]:
    paths: set[str] = set()
    for t in MOVE_TABLES:
        if not os.path.isfile(t):
            continue
        with open(t) as fh:
            for line in fh:
                m = re.match(r"^\|[^|]*\|\s*`(BookProof\.[A-Za-z0-9_.]+)`\s*\|\s*`(BookProof\.[A-Za-z0-9_.]+)`", line)
                if m:
                    paths.add(m.group(1).replace(".", "/") + ".lean")
    return paths


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="generate_modified_files.sh")
    args = ap.parse_args()

    files = git_files()
    fileset = set(files)

    candidates = old_script_paths(args.out) | move_table_paths() | set(EXTRA_REMOVED)
    removed = sorted(p for p in candidates if p not in fileset and not os.path.exists(p))

    sums = []
    for f in files:
        with open(f, "rb") as fh:
            sums.append(f"{hashlib.sha256(fh.read()).hexdigest()}  {f}")

    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz", compresslevel=9, format=tarfile.GNU_FORMAT) as tar:
        for f in files:
            ti = tar.gettarinfo(f, arcname=f)
            ti.uid = ti.gid = 0
            ti.uname = ti.gname = ""
            ti.mtime = 0
            ti.mode = 0o755 if os.access(f, os.X_OK) else 0o644
            with open(f, "rb") as fh:
                tar.addfile(ti, fh)
    b64 = base64.encodebytes(buf.getvalue()).decode()

    def fill(s: str) -> str:
        return s.replace("@NFILES@", str(len(files))).replace("@NREMOVED@", str(len(removed)))

    tmp = args.out + ".tmp"
    with open(tmp, "w") as out:
        out.write(fill(TEMPLATE_HEADER))
        out.write("\n".join(sums) + "\n")
        out.write(TEMPLATE_MIDDLE)
        if removed:
            out.write("\n".join(removed) + "\n")
        out.write(fill(TEMPLATE_FOOTER))
        out.write(b64)
    os.chmod(tmp, 0o755)
    os.replace(tmp, args.out)
    print(f"{args.out}: {len(files)} files embedded, {len(removed)} removed paths recorded, "
          f"{os.path.getsize(args.out)/1e6:.1f} MB", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
