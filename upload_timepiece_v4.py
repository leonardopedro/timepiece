#!/usr/bin/env python3
"""
Upload timepiece theorems to Prove2me - FIXED version.
Polls for job completion after each submit-problem.

Usage:
    python3 upload_timepiece_v4.py --limit 5    # test
    python3 upload_timepiece_v4.py             # full
"""
import json, subprocess, sys, time, re, os
from pathlib import Path

API = "https://prove2.me/api/v1"
TOKEN = "eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIyOTcxODUyZS1iNWMxLTQ1ZDUtOWEwNC0xY2YwNGE4MjBlZDEiLCJhdWQiOiJhZ2VudC1hY2Nlc3MiLCJpYXQiOjE3ODg2Nzg1MTAsImV4cCI6MTc4ODY4MjExMH0.Q4Vk1xsqVyOhIkmO7fa-LbXdWx1A0nKXShns6eQ5N98"
PROJECT_ROOT = Path("/media/leo/e7ed9d6f-5f0a-4e19-a74e-83424bc154ba/timepiece331")
CACHE_FILE = Path("/tmp/prove2me_names_cache.txt")
STATE_FILE = Path("/tmp/timepiece_upload_v4_state.json")
LOG_FILE = Path("/tmp/timepiece_upload_v4.log")

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
    url = f"{API}/{endpoint}"
    if params: url += "?" + "&".join(f"{k}={v}" for k,v in params.items())
    r = subprocess.run(["curl","-s",url,"-H",f"Authorization: Bearer {TOKEN}"],
                       capture_output=True, text=True, timeout=30)
    return json.loads(r.stdout)

def api_post(endpoint, data):
    url = f"{API}/{endpoint}"
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
print(f"Loaded {len(existing)} existing theorem names", file=sys.stderr)

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

ok = start_idx
fail = 0
skip = 0

for i in range(start_idx, len(new_theorems)):
    prefix, name, filepath = new_theorems[i]
    tag = " [QYM]" if is_qym(name) else ""
    
    if i > 0 and i % 50 == 0:
        with open(STATE_FILE, "w") as f:
            json.dump({"next_index": i, "total": len(new_theorems)}, f)
    
    try:
        with open(filepath, encoding="utf-8") as f:
            source = f.read()
    except Exception as e:
        with open(LOG_FILE, "a") as f:
            f.write(f"READ_ERR: {prefix}.{name}: {e}\n")
        fail += 1
        continue
    
    pattern = rf'(theorem|lemma)\s+{re.escape(name)}\b'
    m = re.search(pattern, source)
    if not m:
        with open(LOG_FILE, "a") as f:
            f.write(f"SKIP: {prefix}.{name}\n")
        skip += 1
        continue
    
    start_ctx = max(0, m.start() - 500)
    ctx = source[start_ctx:m.end()]
    stmt_m = re.search(r':=\s*by', ctx)
    if stmt_m:
        statement = ctx[:stmt_m.end()].strip() + " := by sorry"
    else:
        stmt_m = re.search(r':=\s*', ctx)
        if stmt_m:
            statement = ctx[:stmt_m.end()].strip() + " := by sorry"
        else:
            statement = ctx + " := by sorry"
    
    docstring = ""
    doc_match = re.search(r'/--([\s\S]*?)\s*/', source[:m.start()])
    if doc_match:
        docstring = doc_match.group(1).strip()
    
    title = name.replace("_", " ").title()
    
    # Submit
    resp = api_post("submit-problem", {
        "theorem_name": name,
        "theorem_title": title,
        "formal_statement": statement,
        "natural_language_statement": docstring or f"Formal statement of {name}.",
        "description": f"From timepiece project: {prefix}.{name} (v4.28 → v4.33)",
        "tags": ["timepiece", "auto-upload", "v4-28-to-v4-33"] + (["qym"] if is_qym(name) else [])
    })
    
    if "jobs" not in resp or not resp["jobs"]:
        errors = resp.get("errors", [])
        with open(LOG_FILE, "a") as f:
            f.write(f"SUBMIT_FAIL: {prefix}.{name}: {errors}{tag}\n")
        fail += 1
        continue
    
    job_id = resp["jobs"][0]["job_id"]
    
    # Poll for PUBLISHED
    theorem_id = None
    for poll_i in range(30):
        time.sleep(2)
        poll = api_get("publish-jobs", {"job_id": job_id})
        status = poll.get("status", "")
        if status == "PUBLISHED":
            theorem_id = poll.get("theorem_id")
            with open(LOG_FILE, "a") as f:
                f.write(f"PUBLISHED: {prefix}.{name} -> {theorem_id}{tag}\n")
            break
        elif status in ("FAILED", "ERROR"):
            with open(LOG_FILE, "a") as f:
                f.write(f"PUBLISH_FAIL ({status}): {prefix}.{name}{tag}\n")
            fail += 1
            break
    else:
        with open(LOG_FILE, "a") as f:
            f.write(f"PUBLISH_TIMEOUT: {prefix}.{name}{tag}\n")
        fail += 1
        continue
    
    if not theorem_id:
        continue
    
    ok += 1

with open(STATE_FILE, "w") as f:
    json.dump({"next_index": len(new_theorems), "total": len(new_theorems), "ok": ok, "fail": fail}, f)

with open(LOG_FILE, "a") as f:
    f.write(f"DONE: {ok} ok, {fail} fail, {skip} skip out of {len(new_theorems)} total\n")

print(f"DONE: {ok} ok, {fail} fail, {skip} skip out of {len(new_theorems)} total", file=sys.stderr)
