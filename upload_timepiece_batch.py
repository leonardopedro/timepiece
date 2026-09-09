#!/usr/bin/env python3
"""Resumable upload of timepiece theorems to Prove2me."""
import json, subprocess, time, re, sys, os
from pathlib import Path

PROVE2ME_API = "https://prove2.me/api/v1"
TOKEN = "eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIyOTcxODUyZS1iNWMxLTQ1ZDUtOWEwNC0xY2YwNGE4MjBlZDEiLCJhdWQiOiJhZ2VudC1hY2Nlc3MiLCJpYXQiOjE3ODg2Nzg1MTAsImV4cCI6MTc4ODY4MjExMH0.Q4Vk1xsqVyOhIkmO7fa-LbXdWx1A0nKXShns6eQ5N98"
PROJECT_ROOT = Path("/home/leo/Projects/timepiece")
CACHE_FILE = Path("/tmp/prove2me_names_cache.txt")
STATE_FILE = Path("/tmp/timepiece_upload_state.json")
LOG_FILE = Path("/tmp/timepiece_upload.log")

QYM_KEYWORDS = [
    "yqm","qym","yang","mills","mass_gap","massgap","ghost","brst",
    "sirk","quantum","chromo","gauge","fock","scalaron","starobinsky",
    "navier","stokes","einstein","hilbert","spacetime","metric","riemann",
    "band","enclosure","dyson","schwinger","lagrangian","hamiltonian",
    "unitary","hermitian","spectral","fermi","boson","fermion","ghost",
    "auxiliary","gauge_fixing","constraint","physical","ghost_sector",
    "causal","causality","locality","unitarity","renormalization",
    "counterterm","regularization","cutoff","scale","mass","gap",
    "positive_definite","positivity","pos_semidef","coercivity","continuity",
    "differentiability","holomorphic","analytic","meromorphic","resolvent",
    "spectral_theorem","spectral","bounded_below","stability","self_adjoint",
    "ess_sup","essentially_self_adjoint","essentially","symmetric",
    "closed_operator","operator_core","core","dense","unbounded_operator",
    "form","sesquilinear","quadratic_form",
]

def api_get(endpoint, params=None):
    url = f"{PROVE2ME_API}/{endpoint}"
    if params: url += "?" + "&".join(f"{k}={v}" for k,v in params.items())
    r = subprocess.run(["curl","-s",url,"-H",f"Authorization: Bearer {TOKEN}"],
                       capture_output=True, text=True, timeout=30)
    return json.loads(r.stdout)

def api_post(endpoint, data):
    url = f"{PROVE2ME_API}/{endpoint}"
    r = subprocess.run(["curl","-s","-X","POST",url,
                        "-H",f"Authorization: Bearer {TOKEN}",
                        "-H","Content-Type: application/json",
                        "-d",json.dumps(data)],
                       capture_output=True, text=True, timeout=60)
    return json.loads(r.stdout)

def is_qym(name):
    name_lower = name.lower()
    for kw in QYM_KEYWORDS:
        if kw in name_lower: return True
    return False

# Load existing names
existing = set()
with open(CACHE_FILE) as f:
    for line in f:
        name = line.strip()
        if name: existing.add(name)

# Find all new theorems
print("Scanning for new theorems...", file=sys.stderr)
new_theorems = []
prefixes = ["BookProof", "UsedRoute", "UnusedRoute", "RandomMap", "GapCertificate"]
for prefix in prefixes:
    dirpath = PROJECT_ROOT / prefix
    if not dirpath.exists(): continue
    for filepath in sorted(dirpath.glob("*.lean")):
        try:
            with open(filepath, encoding="utf-8") as f:
                content = f.read()
        except: continue
        for m in re.finditer(r'^(theorem|lemma)\s+(\S+)', content, re.MULTILINE):
            name = m.group(2)
            line_start = content.rfind('\n', 0, m.start()) + 1
            line_end = content.find('\n', m.end())
            line = content[line_start:line_end]
            if 'sorry' in line: continue
            if name in existing: continue
            new_theorems.append((prefix, name, str(filepath)))

# Sort: QYM first, then alphabetically
new_theorems.sort(key=lambda x: (0 if is_qym(x[1]) else 1, x[1]))
qym_count = sum(1 for _, n, _ in new_theorems if is_qym(n))
print(f"Total new: {len(new_theorems)} ({qym_count} QYM, {len(new_theorems)-qym_count} other)", file=sys.stderr)

# Load state
start_idx = 0
if STATE_FILE.exists():
    with open(STATE_FILE) as f:
        state = json.load(f)
    start_idx = state.get("next_index", 0)
    print(f"Resuming from index {start_idx}", file=sys.stderr)

uploaded = start_idx
failed = 0
for i in range(start_idx, len(new_theorems)):
    prefix, name, filepath = new_theorems[i]
    tag = " [QYM]" if is_qym(name) else ""
    
    # Write state every 100 uploads
    if i > 0 and i % 100 == 0:
        with open(STATE_FILE, "w") as f:
            json.dump({"next_index": i, "total": len(new_theorems)}, f)
    
    try:
        with open(filepath, encoding="utf-8") as f:
            source = f.read()
        
        pattern = rf'(theorem|lemma)\s+{re.escape(name)}\b'
        m = re.search(pattern, source)
        if not m:
            with open(LOG_FILE, "a") as f:
                f.write(f"SKIP (not found): {prefix}.{name}\n")
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
                    with open(LOG_FILE, "a") as f:
                        if status == "PUBLISHED":
                            f.write(f"OK: {prefix}.{name} -> {poll.get('theorem_id')}\n")
                            uploaded += 1
                        else:
                            f.write(f"FAIL ({status}): {prefix}.{name}\n")
                            failed += 1
                    break
            else:
                with open(LOG_FILE, "a") as f:
                    f.write(f"TIMEOUT: {prefix}.{name}\n")
                failed += 1
        else:
            with open(LOG_FILE, "a") as f:
                f.write(f"SUBMIT_ERR: {prefix}.{name}: {json.dumps(resp)[:150]}\n")
            failed += 1
    except Exception as e:
        with open(LOG_FILE, "a") as f:
            f.write(f"ERROR: {prefix}.{name}: {e}\n")
        failed += 1
    
    time.sleep(0.3)

with open(STATE_FILE, "w") as f:
    json.dump({"next_index": len(new_theorems), "total": len(new_theorems), "uploaded": uploaded, "failed": failed}, f)

with open(LOG_FILE, "a") as f:
    f.write(f"UPLOAD COMPLETE: {uploaded} ok, {failed} failed out of {len(new_theorems)} total\n")

print(f"UPLOAD COMPLETE: {uploaded} ok, {failed} failed out of {len(new_theorems)} total", file=sys.stderr)
