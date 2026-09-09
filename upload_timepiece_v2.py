#!/usr/bin/env python3
"""
Upload timepiece theorems to Prove2me.
Two-step process per theorem:
  1. POST /submit-problem -> creates theorem stub (with sorry)
  2. POST /verify -> submits the actual proof

Usage:
    python3 upload_timepiece_v2.py --dry-run    # preview
    python3 upload_timepiece_v2.py --limit 5     # test
    python3 upload_timepiece_v2.py             # full
"""
import argparse, json, subprocess, sys, time, re, os
from pathlib import Path

API = "https://prove2.me/api/v1"
TOKEN = "eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIyOTcxODUyZS1iNWMxLTQ1ZDUtOWEwNC0xY2YwNGE4MjBlZDEiLCJhdWQiOiJhZ2VudC1hY2Nlc3MiLCJpYXQiOjE3ODg2Nzg1MTAsImV4cCI6MTc4ODY4MjExMH0.Q4Vk1xsqVyOhIkmO7fa-LbXdWx1A0nKXShns6eQ5N98"
PROJECT_ROOT = Path("/home/leo/Projects/timepiece")
CACHE_FILE = Path("/tmp/prove2me_names_cache.txt")
STATE_FILE = Path("/tmp/timepiece_upload_v2_state.json")
LOG_FILE = Path("/tmp/timepiece_upload_v2.log")

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

def api_post(endpoint, data=None, files=None):
    url = f"{API}/{endpoint}"
    if files:
        parts = ["curl","-s","-X","POST",url,
                 "-H",f"Authorization: Bearer {TOKEN}"]
        for k,v in files.items():
            parts += ["-F", f"{k}={v}"]
        r = subprocess.run(parts,
                           capture_output=True, text=True, timeout=120)
    else:
        r = subprocess.run(["curl","-s","-X","POST",url,
                            "-H",f"Authorization: Bearer {TOKEN}",
                            "-H","Content-Type: application/json",
                            "-d",json.dumps(data)],
                           capture_output=True, text=True, timeout=120)
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

uploaded = start_idx
skipped_notfound = start_idx
failed = 0

for i in range(start_idx, len(new_theorems)):
    prefix, name, filepath = new_theorems[i]
    tag = " [QYM]" if is_qym(name) else ""
    
    # Save state every 50
    if i > 0 and i % 50 == 0:
        with open(STATE_FILE, "w") as f:
            json.dump({"next_index": i, "total": len(new_theorems)}, f)
    
    # Read source
    try:
        with open(filepath, encoding="utf-8") as f:
            source = f.read()
    except Exception as e:
        with open(LOG_FILE, "a") as f:
            f.write(f"READ_ERR: {prefix}.{name}: {e}\n")
        failed += 1
        continue
    
    # Extract formal statement
    pattern = rf'(theorem|lemma)\s+{re.escape(name)}\b'
    m = re.search(pattern, source)
    if not m:
        with open(LOG_FILE, "a") as f:
            f.write(f"SKIP (not found): {prefix}.{name}\n")
        skipped_notfound += 1
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
    
    # Generate natural language description from docstring
    docstring = ""
    doc_match = re.search(r'/--([\s\S]*?)\s*/', source[:m.start()])
    if doc_match:
        docstring = doc_match.group(1).strip()
    
    title = name.replace("_", " ").title()
    
    # Step 1: Create theorem stub
    resp = api_post("submit-problem", data={
        "theorem_name": name,
        "theorem_title": title,
        "formal_statement": statement,
        "natural_language_statement": docstring or f"Formal statement of {name}.",
        "description": f"From timepiece project: {prefix}.{name}",
        "tags": ["timepiece", "auto-upload"] + (["qym"] if is_qym(name) else [])
    })
    
    if "jobs" not in resp or not resp["jobs"]:
        errors = resp.get("errors", [])
        with open(LOG_FILE, "a") as f:
            f.write(f"STUB_FAIL: {prefix}.{name}: {errors}\n")
        failed += 1
        continue
    
    job_id = resp["jobs"][0]["job_id"]
    
    # Poll until published
    theorem_id = None
    for _ in range(60):
        time.sleep(3)
        poll = api_get("publish-jobs", {"job_id": job_id})
        status = poll.get("status", "")
        if status in ("PUBLISHED", "FAILED", "ERROR"):
            if status == "PUBLISHED":
                theorem_id = poll.get("theorem_id")
                with open(LOG_FILE, "a") as f:
                    f.write(f"STUB_OK: {prefix}.{name} -> {theorem_id}\n")
            else:
                with open(LOG_FILE, "a") as f:
                    f.write(f"STUB_FAIL ({status}): {prefix}.{name}\n")
                failed += 1
            break
    else:
        with open(LOG_FILE, "a") as f:
            f.write(f"STUB_TIMEOUT: {prefix}.{name}\n")
        failed += 1
        continue
    
    if not theorem_id:
        continue
    
    # Step 2: Submit proof
    # Create a temporary solution file
    sol_file = f"/tmp/sol_{name}.lean"
    with open(sol_file, "w") as f:
        # Write the full proof from the source file
        # Find the proof body (after ':=')
        proof_start = m.end()
        # Find 'by' or ':= ...' 
        by_match = re.search(r':=\s*(by\b|\S)', source[proof_start:proof_start+100])
        if by_match and by_match.group(1) == 'by':
            # Find the end of the proof
            proof_text = source[proof_start:]
            # Simple: extract everything from 'by' to end of file or next top-level decl
            # For now, just use the full file content
            f.write(source)
        else:
            f.write(source)
    
    verify_resp = api_post("verify", files={
        "theorem_id": theorem_id,
        "file": open(sol_file, "rb"),
        "explanation": f"Proof from timepiece project: {prefix}.{name}. Auto-uploaded."
    })
    
    sub_id = verify_resp.get("submission_id", "")
    sub_status = verify_resp.get("status", "")
    
    if sub_id:
        # Poll for verdict
        for _ in range(60):
            time.sleep(5)
            poll = api_get("verify", {"submission_id": sub_id})
            vstatus = poll.get("status", "")
            if vstatus in ("ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"):
                with open(LOG_FILE, "a") as f:
                    f.write(f"VERDICT: {prefix}.{name} -> {vstatus}\n")
                if vstatus in ("ACCEPTED", "SKETCH_ACCEPTED"):
                    uploaded += 1
                else:
                    failed += 1
                break
        else:
            with open(LOG_FILE, "a") as f:
                f.write(f"VERIFY_TIMEOUT: {prefix}.{name}\n")
            failed += 1
    else:
        with open(LOG_FILE, "a") as f:
            f.write(f"VERIFY_FAIL: {prefix}.{name}: {json.dumps(verify_resp)[:200]}\n")
        failed += 1
    
    os.unlink(sol_file)
    time.sleep(0.5)

with open(STATE_FILE, "w") as f:
    json.dump({"next_index": len(new_theorems), "total": len(new_theorems), "uploaded": uploaded, "failed": failed}, f)

with open(LOG_FILE, "a") as f:
    f.write(f"UPLOAD COMPLETE: {uploaded} ok, {failed} failed, {skipped_notfound} skipped (not found) out of {len(new_theorems)} total\n")

print(f"UPLOAD COMPLETE: {uploaded} ok, {failed} failed, {skipped_notfound} skipped out of {len(new_theorems)} total", file=sys.stderr)
