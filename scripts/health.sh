#!/usr/bin/env bash
# Health gate for timepiece — one command, one exit code over the repo's
# EXISTING checks. Pattern adapted from `ax`'s `/healthz` endpoint
# (../ax, Apache-2.0): plain, dependency-free, healthy ⇔ exit 0.
#
# Severity model (cf. verify-invariants' [gap] discipline; baselines recorded
# in prove2me_workspace/PROJECT_REVIEW_AND_PLAN.md §P3-A1, verified against
# HEAD 8901a58 on 2026-09-24):
#   [pass] no findings
#   [warn] known pre-existing findings at or below baseline — does not fail
#   [FAIL] hard structural errors, or known finding classes ABOVE baseline
#          (i.e. a genuine new regression)
#
# Checks (NO Lean compilation, no `lake build`):
#   1. doc index freshness    scripts/doc_index.py --check
#   2. import-component gate  scripts/import_components.py BookProof --check
#   3. GitBook citation drift scripts/check-gitbook-drift   (skips w/o ../test)
#
# Known pre-existing baselines (NOT caused by this script; owned follow-ups
# are tracked in the cross-repo plan):
#   * 6 components without a stable name in COMPONENT_NAMES (split wave)
#   * 86 component roots absent from lakefile.toml's roots lists (split wave)
#   * 11 uncited-by-tree Lean identifiers in test/ prose (doc drift)
#
# Usage:  bash scripts/health.sh        (from repo root)
set -u
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root" || exit 1

BASE_MISSING_NAME=6
BASE_ROOT_NOT_LISTED=86
BASE_LEAN_MISS=11
BASE_RUST_MISS=0

PASSED=0; WARNED=0; FAILED=0; GAPS=0
HARD_RE='cone of the roots differs|MISSING TARGET|collides with a part|not a module of|straddles'

report() {  # $1=verdict $2=name
    local verdict="$1" name="$2"
    case "$verdict" in
        pass) echo "[pass] $name"; PASSED=$((PASSED+1)) ;;
        warn) echo "[warn] $name"; WARNED=$((WARNED+1)) ;;
        gap)  echo "[gap]  $name"; GAPS=$((GAPS+1)) ;;
        fail) echo "[FAIL] $name"; FAILED=$((FAILED+1)) ;;
    esac
}

# --- 1. doc index freshness -----------------------------------------------
if OUT=$(python3 scripts/doc_index.py --check 2>&1) && [[ $? -eq 0 ]]; then
    report pass "doc index fresh ($(echo "$OUT" | grep -o '[0-9]* docs' || true))"
else
    report fail "doc index fresh"
    echo "$OUT" | sed -n '1,4p' | sed 's/^/       /'
fi

# --- 2. import-component gate --------------------------------------------
IMP=$(python3 scripts/import_components.py BookProof --check 2>&1)
hard=$(echo "$IMP" | grep -cE "$HARD_RE")
nname=$(echo "$IMP" | grep -c "MISSING NAME")
nroot=$(echo "$IMP" | grep -c "not listed")
if [[ "$hard" -gt 0 ]]; then
    report fail "import components gate — $hard HARD structural error(s)"
    echo "$IMP" | grep -E "$HARD_RE" | sed -n '1,8p' | sed 's/^/       /'
elif [[ "$nname" -gt $BASE_MISSING_NAME || "$nroot" -gt $BASE_ROOT_NOT_LISTED ]]; then
    report fail "import components gate — notices above baseline (+$((nname-BASE_MISSING_NAME)) name, +$((nroot-BASE_ROOT_NOT_LISTED)) root)"
    echo "$IMP" | grep -E "MISSING NAME|not listed" | sed -n '1,8p' | sed 's/^/       /'
elif [[ "$nname" -gt 0 || "$nroot" -gt 0 ]]; then
    report warn "import components gate — at baseline ($nname unnamed comps, $nroot stale roots; known split-wave drift)"
else
    report pass "import components gate"
fi

# --- 3. GitBook citation drift -------------------------------------------
if [[ ! -d "../test" ]]; then
    report gap "../test GitBook not present — drift check skipped"
else
    DRIFT=$(bash scripts/check-gitbook-drift 2>&1)
    lmiss=$(echo "$DRIFT" | grep -c "\[MISS lean\]")
    rmiss=$(echo "$DRIFT" | grep -c "\[MISS rust\]")
    if [[ "$lmiss" -eq 0 && "$rmiss" -eq 0 ]]; then
        report pass "gitbook citation drift — 0 misses"
    elif [[ "$lmiss" -le $BASE_LEAN_MISS && "$rmiss" -le $BASE_RUST_MISS ]]; then
        report warn "gitbook citation drift — at baseline ($lmiss lean, $rmiss rust doc-drift citations)"
        echo "$DRIFT" | grep "\[MISS lean\]" | sed -n '1,4p' | sed 's/^/       /'
    else
        report fail "gitbook citation drift — above baseline (lean $lmiss > $BASE_LEAN_MISS or rust $rmiss > $BASE_RUST_MISS)"
        echo "$DRIFT" | grep "MISS" | sed -n '1,8p' | sed 's/^/       /'
    fi
fi

echo "— health: $PASSED pass, $WARNED warn, $GAPS gap, $FAILED fail —"
echo "  (baseline notices are known; see PROJECT_REVIEW_AND_PLAN.md §P3-A1)"
[[ $FAILED -eq 0 ]] || exit 1
exit 0
