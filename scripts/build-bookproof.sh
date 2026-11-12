#!/usr/bin/env bash
# Serialized aggregate build for the BookProof target (OOM guard).
#
# Why this script exists
# ----------------------
# `lake build` in this toolchain (Lake 5.0.0-src+7e01a1b / Lean 4.28.0) has NO
# job-limit: `lake build --help` and `lake --help` expose no -j/--jobs, and the
# binary has no LAKE_JOBS knob. Lake sizes its worker pool from the CPU count,
# so on this 12-core / 15.3 GB box an aggregate `lake build BookProof` runs up
# to 14 concurrent `lean` processes, several of them ~1.7 GB. Measured on
# 2026-11-11: available memory falls from 11 GB to ~600 MB within minutes of
# the start, and the kernel then OOM-kills a worker. Observed repeatedly: died
# at 8630/8968, 8654/8968, 8616/8948 and 8592/8948 jobs with no `error:` line.
#
# What DOES bound the pool is CPU affinity, because lake sizes its worker pool
# from the number of *visible* CPUs. Measured on 2026-11-11 with the same 8-module
# set: `taskset -c 0-3` -> 5 `lean` workers, 8.7 GB free (safe); `taskset -c 0-5`
# -> 12 workers, 703 MB free (about to OOM). An earlier note in this file claimed
# affinity does not help; that measurement was polluted by an orphaned concurrent
# build and was wrong. Affinity (`-j`, default 4) is therefore the primary bound
# and the chunk size is the secondary one: it also keeps a single heavy chapter
# from being scheduled beside six others.
#
# A memory gate backs both up: before each chunk the script waits until at least
# --min-free MB (default 4000) is available, so a box that is already loaded (an
# editor, a browser, another build) delays the run instead of OOM-killing it.
#
# What this script does instead
# -----------------------------
# Real serialization: it builds the modules that are actually out of date, in
# small chunks, one `lake build` invocation at a time. Peak memory is then one
# chunk's worth of `lean` processes rather than the whole dependency cone. A
# final full-target pass closes anything the staleness scan could miss.
#
# Staleness is mtime-based per module (missing `.olean`, or source newer). That
# is the same signal lake uses in the common case; a module that is stale only
# because a dependency changed content is caught by the final pass.
#
# Usage
# -----
#   bash scripts/build-bookproof.sh                  # chunks of 8, 4 CPUs (safe default)
#   bash scripts/build-bookproof.sh -c 1             # strictly one module at a time
#   bash scripts/build-bookproof.sh -j 2             # even smaller worker pool
#   bash scripts/build-bookproof.sh -j 0             # no affinity cap (fast, OOMs here)
#   bash scripts/build-bookproof.sh --min-free 6000  # wait longer before each chunk
#   bash scripts/build-bookproof.sh BookProof Layout # other targets
#   bash scripts/build-bookproof.sh --full           # plain `lake build`, no chunking
#   bash scripts/build-bookproof.sh --help
#
# Exit status is 0 only if every chunk and the final pass succeeded. The full
# log is kept and its path printed, so a killed run (no `error:` line) can be
# told apart from a failing one.
set -u

CHUNK=8
JOBS=4
MIN_FREE=4000
TARGETS=()
FULL=0
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

usage() {
    sed -n '/^# Usage$/,/^# Exit status/p' "$0" | sed 's/^# \{0,1\}//'
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        -c|--chunk)
            [[ $# -ge 2 ]] || { echo "build-bookproof: -c needs a value" >&2; exit 2; }
            CHUNK="$2"; shift 2 ;;
        --chunk=*) CHUNK="${1#*=}"; shift ;;
        -j|--jobs)
            [[ $# -ge 2 ]] || { echo "build-bookproof: -j needs a value" >&2; exit 2; }
            JOBS="$2"; shift 2 ;;
        --jobs=*) JOBS="${1#*=}"; shift ;;
        --min-free)
            [[ $# -ge 2 ]] || { echo "build-bookproof: --min-free needs a value" >&2; exit 2; }
            MIN_FREE="$2"; shift 2 ;;
        --min-free=*) MIN_FREE="${1#*=}"; shift ;;
        -f|--full) FULL=1; shift ;;
        -h|--help) usage; exit 0 ;;
        -*) echo "build-bookproof: unknown option '$1' (try --help)" >&2; exit 2 ;;
        *) TARGETS+=("$1"); shift ;;
    esac
done

[[ "$CHUNK" =~ ^[0-9]+$ ]] && (( CHUNK >= 1 )) \
    || { echo "build-bookproof: -c must be a positive integer" >&2; exit 2; }
[[ ${#TARGETS[@]} -gt 0 ]] || TARGETS=(BookProof)

export PATH="$HOME/.elan/bin:$PATH"
cd "$REPO_ROOT" || exit 1

if ! command -v lake >/dev/null 2>&1; then
    echo "build-bookproof: lake not found (elan toolchain missing?)" >&2
    exit 127
fi

LOG="${TMPDIR:-/tmp}/build-bookproof-$(date +%Y%m%d-%H%M%S).log"
: > "$LOG"

# Primary bound on lake's worker pool: the number of CPUs it can see (see
# header for the measurements). `-j 0` disables the cap.
[[ "$MIN_FREE" =~ ^[0-9]+$ ]] \
    || { echo "build-bookproof: --min-free must be a non-negative integer" >&2; exit 2; }
CMD=()
if (( JOBS > 0 )); then
    [[ "$JOBS" =~ ^[0-9]+$ ]] \
        || { echo "build-bookproof: -j must be a non-negative integer" >&2; exit 2; }
    NCPU="$(nproc)"
    (( JOBS > NCPU )) && JOBS="$NCPU"
    if command -v taskset >/dev/null 2>&1 && (( JOBS < NCPU )); then
        CMD=(taskset -c "0-$(( JOBS - 1 ))")
        echo "build-bookproof: capping CPU affinity to $JOBS of $NCPU CPUs"
    else
        echo "build-bookproof: no CPU cap (wide worker pool)"
    fi
else
    echo "build-bookproof: no CPU cap (wide worker pool, -j 0)"
fi

# Available memory in MB (the `available` column, which accounts for reclaimable
# page cache; `free` alone overstates the pressure).
avail_mb() { free -m | awk '/^Mem:/{print $7}'; }

# Backstop for the OOM: nothing starts while the box is short of memory. A run
# that cannot reach the threshold an hour in is reported rather than forced.
wait_for_memory() {
    local a waited=0
    (( MIN_FREE == 0 )) && return 0
    a="$(avail_mb)"
    while (( a < MIN_FREE )); do
        if (( waited % 60 == 0 )); then
            echo "build-bookproof: waiting — ${a} MB available, need ${MIN_FREE} MB"
        fi
        if (( waited >= 1800 )); then
            echo "build-bookproof: giving up after 30 min below ${MIN_FREE} MB available" >&2
            return 1
        fi
        sleep 10
        waited=$((waited + 10))
        a="$(avail_mb)"
    done
    return 0
}

# --- build machinery ------------------------------------------------------
# `setsid -w` puts lake in its own process group and waits for it, so a signal
# can take the whole tree down. Without that, killing lake leaves orphaned
# `lean` children running (observed: 13 orphans holding 1.9 GB) because lean
# processes re-parent and keep going.
LAKE_PID=""
CANCELLED=0
cleanup() {
    CANCELLED=1
    if [[ -n "$LAKE_PID" ]] && kill -0 "$LAKE_PID" 2>/dev/null; then
        kill -TERM -- "-$LAKE_PID" 2>/dev/null || kill -TERM "$LAKE_PID" 2>/dev/null
        sleep 1
        kill -KILL -- "-$LAKE_PID" 2>/dev/null || kill -KILL "$LAKE_PID" 2>/dev/null
    fi
}
trap cleanup INT TERM

run_lake() {  # $@ = lake build arguments; returns lake's status
    local tmp status
    tmp="$(mktemp)"
    if command -v setsid >/dev/null 2>&1; then
        setsid -w "${CMD[@]}" lake build "$@" >"$tmp" 2>&1 &
    else
        "${CMD[@]}" lake build "$@" >"$tmp" 2>&1 &
    fi
    LAKE_PID=$!
    wait "$LAKE_PID"
    status=$?
    LAKE_PID=""
    tee -a "$LOG" <"$tmp"
    rm -f "$tmp"
    return $status
}

# --- optional: single unmodified pass ------------------------------------
if (( FULL )); then
    echo "build-bookproof: ${CMD[*]:-} lake build ${TARGETS[*]} (no chunking)"
    echo "build-bookproof: log -> $LOG"
    wait_for_memory || exit 1
    run_lake "${TARGETS[@]}"
    STATUS=$?
    [[ $STATUS -eq 0 ]] && echo "build-bookproof: OK — $(grep -cE '^✔' "$LOG") jobs built/replayed"
    exit $STATUS
fi

# --- 1. collect the import closure, then pick what is out of date ---------
# Walk the closure from the targets rather than globbing the directories. The
# tree carries orphaned fragments left behind when chapters moved into
# per-area directories (e.g. BookProof/ChapterFockQuadraticEsa/Part4.lean,
# superseded by BookProof/Toolbox/ChapterFockQuadraticEsa). Nothing imports
# them and they do not elaborate — their `import` lines name modules that no
# longer exist — so globbing schedules dead files and turns a clean build into
# spurious `bad import` failures. Only the closure is the build.
#
# Target `Foo` maps to the file Foo.lean and/or the directory Foo/.
collect_closure() {
    local t f mod p
    local -a stack=()
    local -A seen=()
    for t in "${TARGETS[@]}"; do
        # `Foo` with a root `Foo.lean` is that module; only fall back to
        # globbing the directory when there is no such root module. Globbing a
        # directory that sits beside its root module is what drags the orphans
        # back in.
        if [[ -f "$t.lean" ]]; then
            stack+=("$t.lean")
        elif [[ -d "$t" ]]; then
            while IFS= read -r f; do stack+=("$f"); done \
                < <(find "$t" -name '*.lean' -type f 2>/dev/null | sort)
        fi
    done
    while (( ${#stack[@]} )); do
        f="${stack[-1]}"
        unset 'stack[-1]'
        [[ -n "${seen[$f]:-}" ]] && continue
        seen[$f]=1
        while IFS= read -r mod; do
            p="${mod//.//}.lean"
            # Only modules that live in this repo; Mathlib and the other
            # dependencies are lake's business, not this script's.
            [[ -f "$p" && -z "${seen[$p]:-}" ]] && stack+=("$p")
        done < <(sed -n 's/^import[[:space:]]\{1,\}\(.*\)$/\1/p' "$f" 2>/dev/null \
            | tr ' ' '\n' | grep -v '^--' | grep -v '^$')
    done
    printf '%s\n' "${!seen[@]}" | sort
}

mapfile -t CLOSURE < <(collect_closure)
[[ ${#CLOSURE[@]} -gt 0 ]] || { echo "build-bookproof: no source found for ${TARGETS[*]}" >&2; exit 1; }

PENDING=()
for f in "${CLOSURE[@]}"; do
    # The target root itself (BookProof.lean) is left to the final pass: a
    # chunk containing it would make lake rebuild its entire dependency cone at
    # once, which is the unpaced build this script exists to avoid.
    skip=0
    for t in "${TARGETS[@]}"; do [[ "$f" == "$t.lean" ]] && skip=1; done
    (( skip )) && continue
    o=".lake/build/lib/lean/${f%.lean}.olean"
    [[ -f "$o" && ! "$f" -nt "$o" ]] || PENDING+=("$f")
done
TOTAL_MODULES=${#CLOSURE[@]}

echo "build-bookproof: targets: ${TARGETS[*]}"
echo "build-bookproof: $TOTAL_MODULES module(s), ${#PENDING[@]} out of date"
echo "build-bookproof: chunk size $CHUNK, log -> $LOG"

# --- 2. build them in chunks --------------------------------------------
FAILED=0
DONE=0
for ((i = 0; i < ${#PENDING[@]}; i += CHUNK)); do
    if (( CANCELLED )); then
        echo "build-bookproof: interrupted — stopping before the next chunk" >&2
        exit 130
    fi
    CHUNK_ARGS=("${PENDING[@]:i:CHUNK}")
    wait_for_memory || exit 1
    DONE=$((DONE + ${#CHUNK_ARGS[@]}))
    echo "build-bookproof: [$DONE/${#PENDING[@]}] ${CHUNK_ARGS[*]}"
    if ! run_lake "${CHUNK_ARGS[@]}"; then
        FAILED=$((FAILED + ${#CHUNK_ARGS[@]}))
        echo "build-bookproof: chunk failed — continuing so every failure is reported" >&2
    fi
done

# --- 3. final pass over the whole target --------------------------------
# Catches modules that are stale through a changed dependency rather than their
# own mtime. Normally a near no-op, since step 2 just built everything.
echo "build-bookproof: final pass over ${TARGETS[*]}"
if ! { wait_for_memory && run_lake "${TARGETS[@]}"; }; then
    FINAL_OK=0
else
    FINAL_OK=1
fi

echo
if (( FAILED == 0 )) && (( FINAL_OK )); then
    echo "build-bookproof: OK — $(grep -cE '^✔' "$LOG") jobs built/replayed, log $LOG"
    exit 0
elif (( FAILED > 0 )); then
    echo "build-bookproof: FAILED — $FAILED module chunk(s) failed; see 'error:' in $LOG"
    exit 1
else
    echo "build-bookproof: FAILED in the final pass; see 'error:' in $LOG"
    exit 1
fi
