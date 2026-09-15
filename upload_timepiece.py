#!/usr/bin/env python3
"""
Fast upload of proved theorems from timepiece to Prove2me.
Uses grep + source reading to identify proved theorems, caches existing names.

Usage:
    python3 upload_timepiece.py --dry-run          # preview only
    python3 upload_timepiece.py --qym-only         # QYM priority only
    python3 upload_timepiece.py --limit 10         # test with 10
    python3 upload_timepiece.py                    # full upload
"""

import argparse, json, subprocess, sys, time, os, re
from pathlib import Path

PROVE2ME_API = "https://prove2.me/api/v1"
TOKEN = "eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIyOTcxODUyZS1iNWMxLTQ1ZDUtOWEwNC0xY2YwNGE4MjBlZDEiLCJhdWQiOiJhZ2VudC1hY2Nlc3MiLCJpYXQiOjE3ODg2NzI1NjcsImV4cCI6MTc4ODY3NjE2N30.WEmrJYfP2M5mJtn21oAFFsQ2i9LrmhyUMTyDR5ONiRY"
PROJECT_ROOT = Path("/home/leo/Projects/timepiece")
CACHE_FILE = Path("/tmp/prove2me_names_cache.txt")

QYM_KEYWORDS = [
    "yqm", "qym", "yang", "mills", "mass_gap", "massgap",
    "ghost", "brst", "sirk", "quantum", "chromo", "gauge",
    "fock", "scalaron", "starobinsky", "navier", "stokes",
    "einstein", "hilbert", "spacetime", "metric", "riemann",
    "band", "enclosure", "dyson", "schwinger", "lagrangian",
    "hamiltonian", "unitary", "hermitian", "spectral", "fermi",
    "boson", "fermion", "ghost", "auxiliary", "gauge_fixing",
    "constraint", "physical", "ghost_sector", "causal", "causality",
    "locality", "unitarity", "renormalization", "counterterm",
    "regularization", "cutoff", "scale", "mass", "gap",
    "positive_definite", "positivity", "pos_semidef", "coercivity",
    "continuity", "differentiability", "holomorphic", "analytic",
    "meromorphic", "resolvent", "spectral_theorem", "spectral",
    "bounded_below", "stability", "self_adjoint", "ess_sup",
    "essentially_self_adjoint", "essentially", "symmetric",
    "closed_operator", "operator_core", "core", "dense",
    "unbounded_operator", "form", "sesquilinear", "quadratic_form",
]

# ── API helpers ─────────────────────────────────────────────────────────────

def api_get(endpoint, params=None):
    url = f"{PROVE2ME_API}/{endpoint}"
    if params:
        url += "?" + "&".join(f"{k}={v}" for k, v in params.items())
    r = subprocess.run(["curl", "-s", url, "-H", f"Authorization: Bearer {TOKEN}"],
                       capture_output=True, text=True, timeout=30)
    return json.loads(r.stdout)

def api_post(endpoint, data):
    url = f"{PROVE2ME_API}/{endpoint}"
    r = subprocess.run(["curl", "-s", "-X", "POST", url,
                        "-H", f"Authorization: Bearer {TOKEN}",
                        "-H", "Content-Type: application/json",
                        "-d", json.dumps(data)],
                       capture_output=True, text=True, timeout=60)
    return json.loads(r.stdout)

def fetch_all_theorem_names():
    """Fetch all theorem names from Prove2me (cached)."""
    if CACHE_FILE.exists():
        with open(CACHE_FILE) as f:
            return set(line.strip() for line in f if line.strip())
    
    names = set()
    offset = 0
    while True:
        resp = api_get("theorems", {"limit": 100, "sort": "newest", "offset": offset})
        items = resp.get("theorems", resp) if isinstance(resp, dict) else resp
        if not items:
            break
        for t in items:
            names.add(t["theorem_name"])
        offset += 100
        if len(items) < 100:
            break
    
    with open(CACHE_FILE, "w") as f:
        for n in sorted(names):
            f.write(n + "\n")
    
    print(f"  Cached {len(names)} theorem names")
    return names

# ── Theorem discovery ───────────────────────────────────────────────────────

def find_theorems_in_file(filepath):
    """Find all theorem/lemma declarations in a Lean file."""
    try:
        with open(filepath, encoding="utf-8") as f:
            content = f.read()
    except:
        return []
    
    results = []
    for m in re.finditer(r'^(theorem|lemma)\s+(\S+)', content, re.MULTILINE):
        name = m.group(2)
        line_start = content.rfind('\n', 0, m.start()) + 1
        line_end = content.find('\n', m.end())
        line = content[line_start:line_end]
        if 'sorry' in line:
            continue
        results.append(name)
    return results

def scan_project_theorems():
    """Scan all project files for proved theorems."""
    prefixes = ["BookProof", "UsedRoute", "UnusedRoute", "RandomMap", "GapCertificate"]
    all_theorems = []
    
    for prefix in prefixes:
        dirpath = PROJECT_ROOT / prefix
        if not dirpath.exists():
            continue
        for filepath in sorted(dirpath.glob("*.lean")):
            names = find_theorems_in_file(filepath)
            for name in names:
                all_theorems.append((prefix, name, str(filepath)))
    
    return all_theorems

# ── QYM classification ─────────────────────────────────────────────────────

def is_qym(name):
    name_lower = name.lower()
    for kw in QYM_KEYWORDS:
        if kw in name_lower:
            return True
    return False

# ── Main ────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Upload timepiece proofs to Prove2me")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--limit", type=int, help="Max theorems to upload")
    parser.add_argument("--qym-only", action="store_true", help="QYM priority only")
    parser.add_argument("--skip-qym", action="store_true", help="Skip QYM theorems")
    parser.add_argument("--refresh-cache", action="store_true", help="Refresh cached theorem names")
    args = parser.parse_args()
    
    print("=" * 80)
    print("TIMEPIECE -> PROVE2ME UPLOAD PIPELINE")
    print("=" * 80)
    
    # Phase 1: Scan for proved theorems
    print("\n[1] Scanning project for proved theorems...")
    all_theorems = scan_project_theorems()
    print(f"    Found {len(all_theorems)} proved theorem declarations")
    
    # Phase 2: Load existing Prove2me theorems
    print("\n[2] Loading existing Prove2me theorems...")
    existing = fetch_all_theorem_names()
    print(f"    Loaded {len(existing)} existing names (from cache)")
    
    # Phase 3: Filter and prioritize
    print("\n[3] Filtering and prioritizing...")
    new = []
    qym_new = []
    skipped = 0
    
    for prefix, name, filepath in all_theorems:
        if name in existing:
            skipped += 1
            continue
        entry = (prefix, name, filepath)
        new.append(entry)
        if is_qym(name):
            qym_new.append(entry)
    
    print(f"    Skipped {skipped} duplicates")
    print(f"    New: {len(new)} ({len(qym_new)} QYM, {len(new)-len(qym_new)} other)")
    
    if args.qym_only:
        new = qym_new
        print(f"    Filtered to QYM-only: {len(new)}")
    elif args.skip_qym:
        new = [e for e in new if not is_qym(e[1])]
        print(f"    Filtered to non-QYM: {len(new)}")
    
    if args.limit:
        new = new[:args.limit]
        qym_new = [e for e in qym_new if e in new]
        print(f"    Limited to {args.limit}")
    
    if args.dry_run:
        print("\n[DRY RUN] Would upload:")
        for prefix, name, _ in new[:20]:
            tag = " [QYM]" if is_qym(name) else ""
            print(f"  {prefix}.{name}{tag}")
        if len(new) > 20:
            print(f"  ... and {len(new)-20} more")
        return
    
    if not new:
        print("\nNothing to upload!")
        return
    
    # Phase 4: Upload
    print(f"\n[4] Uploading {len(new)} theorems...")
    uploaded = 0
    failed = 0
    
    for i, (prefix, name, filepath) in enumerate(new):
        tag = " [QYM]" if is_qym(name) else ""
        print(f"  [{i+1}/{len(new)}] {prefix}.{name}{tag}")
        
        try:
            with open(filepath, encoding="utf-8") as f:
                source = f.read()
            
            pattern = rf'(theorem|lemma)\s+{re.escape(name)}\b'
            m = re.search(pattern, source)
            if not m:
                print(f"    SKIP: Declaration not found")
                failed += 1
                continue
            
            start = max(0, m.start() - 500)
            ctx = source[start:m.end()]
            
            stmt_m = re.search(r':=\s*by', ctx)
            if stmt_m:
                statement = ctx[:stmt_m.end()].strip() + " := by sorry"
            else:
                stmt_m = re.search(r':=\s*', ctx)
                if stmt_m:
                    statement = ctx[:stmt_m.end()].strip() + " := by sorry"
                else:
                    statement = ctx + " := by sorry"
            
            title = name.replace("_", " ").title()
            
            resp = api_post("submit-problem", {
                "theorem_name": name,
                "theorem_title": title,
                "formal_statement": statement,
                "description": f"From timepiece project: {prefix}.{name}",
                "tags": ["timepiece", "auto-upload"] + (["qym"] if is_qym(name) else [])
            })
            
            if "jobs" in resp:
                job_id = resp["jobs"][0]["job_id"]
                for _ in range(60):
                    time.sleep(3)
                    poll = api_get("publish-jobs", {"job_id": job_id})
                    status = poll.get("status", "")
                    if status in ("PUBLISHED", "FAILED", "ERROR"):
                        if status == "PUBLISHED":
                            print(f"    OK: {poll.get('theorem_id')}")
                            uploaded += 1
                        else:
                            print(f"    FAIL: {status}")
                            failed += 1
                        break
                else:
                    print(f"    TIMEOUT")
                    failed += 1
            else:
                print(f"    Submit error: {json.dumps(resp)[:150]}")
                failed += 1
        except Exception as e:
            print(f"    ERROR: {e}")
            failed += 1
        
        time.sleep(0.3)
    
    print(f"\n{'='*80}")
    print(f"DONE: {uploaded} ok, {failed} failed out of {len(new)}")
    print(f"{'='*80}")

if __name__ == "__main__":
    main()
