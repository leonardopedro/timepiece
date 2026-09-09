#!/usr/bin/env python3
"""
Upload timepiece theorems to Prove2me - FIXED v5.
Proper statement extraction, skips docstrings.

Usage:
    python3 upload_timepiece_v5.py --limit 5    # test
    python3 upload_timepiece_v5.py             # full
"""
import json, subprocess, sys, time, re, os
from pathlib import Path

API = "https://prove2.me/api/v1"
TOKEN = "eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIyOTcxODUyZS1iNWMxLTQ1ZDUtOWEwNC0xY2YwNGE4MjBlZDEiLCJhdWQiOiJhZ2VudC1hY2Nlc3MiLCJpYXQiOjE3ODg2Nzg1MTAsImV4cCI6MTc4ODY4MjExMH0.Q4Vk1xsqVyOhIkmO7fa-LbXdWx1A0nKXShns6eQ5N98"
PROJECT_ROOT = Path("/home/leo/Projects/timepiece")
CACHE_FILE = Path("/tmp/prove2me_names_cache.txt")
STATE_FILE = Path("/tmp/timepiece_upload_v5_state.json")
LOG_FILE = Path("/tmp/timepiece_upload_v5.log")

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

def extract_theorem_statement(source, name):
    """Extract just the theorem/lemma declaration line (the statement)."""
    pattern = rf'^(theorem|lemma)\s+{re.escape(name)}\b'
    for m in re.finditer(pattern, source, re.MULTILINE):
        line_start = source.rfind('\n', 0, m.start()) + 1
        line_end = source.find('\n', m.end())
        line = source[line_start:line_end].strip()
        if 'sorry' in line:
            continue
        # Skip lines inside docstrings (contain '/--' or '**')
        if '/--' in line or line.startswith('**') or line.startswith('*') or line.startswith('---'):
            continue
        # This is the actual declaration
        return line
    return None

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
        
        # Split by docstring boundaries to avoid matching inside comments
        # Simple approach: skip lines that look like docstring content
        in_docstring = False
        for line in content.split('\n'):
            stripped = line.strip()
            # Skip module docstrings and regular comments
            if stripped.startswith('/--') or stripped.startswith('/-!') or stripped.startswith('/-'):
                in_docstring = True
                continue
            if in_docstring:
                if stripped.endswith('-/') or stripped == '-/':
                    in_docstring = False
                continue
            if stripped.startswith('**') or stripped.startswith('*') or stripped.startswith('---'):
                continue
            
            # Match theorem/lemma declarations
            m = re.match(r'^(theorem|lemma)\s+(\S+)', stripped)
            if m:
                name = m.group(2)
                if 'sorry' not in stripped and name not in existing:
                    new_theorems.append((prefix, name, str(filepath), stripped))

new_theorems.sort(key=lambda x: (0 if is_qym(x[1]) else 1, x[1]))
qym_count = sum(1 for _, n, _, _ in new_theorems if is_qym(n))
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
    prefix, name, filepath, decl_line = new_theorems[i]
    tag = " [QYM]" if is_qym(name) else ""
    
    if i > 0 and i % 50 == 0:
        with open(STATE_FILE, "w") as f:
            json.dump({"next_index": i, "total": len(new_theorems)}, f)
    
    # Extract full statement from source
    try:
        with open(filepath, encoding="utf-8") as f:
            source = f.read()
    except Exception as e:
        with open(LOG_FILE, "a") as f:
            f.write(f"READ_ERR: {prefix}.{name}: {e}\n")
        fail += 1
        continue
    
    # Find the declaration in source to get full context
    pattern = rf'(theorem|lemma)\s+{re.escape(name)}\b'
    m = re.search(pattern, source)
    if not m:
        with open(LOG_FILE, "a") as f:
            f.write(f"SKIP: {prefix}.{name}\n")
        skip += 1
        continue
    
    # Extract from the line containing the declaration up to ':='
    line_start = source.rfind('\n', 0, m.start()) + 1
    line_end = source.find('\n', m.end())
    first_line = source[line_start:line_end].strip()
    
    # Get more context to find ':='
    ctx_start = max(0, m.start() - 200)
    ctx = source[ctx_start:m.end() + 200]
    
    # Extract just the statement part (up to ':=')
    stmt_match = re.search(r':=\s*by', ctx)
    if stmt_match:
        statement = ctx[:stmt_match.end()].strip() + " := by sorry"
    else:
        stmt_match = re.search(r':=\s*', ctx)
        if stmt_match:
            statement = ctx[:stmt_match.end()].strip() + " := by sorry"
        else:
            statement = first_line + " := by sorry"
    
    docstring = ""
    doc_match = re.search(r'/--([\s\S]*?)\s*/', source[:m.start()])
    if doc_match:
        docstring = doc_match.group(1).strip()
    
    title = name.replace("_", " ").title()
    
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
                f.write(f"OK: {prefix}.{name} -> {theorem_id}{tag}\n")
            break
        elif status in ("FAILED", "ERROR"):
            with open(LOG_FILE, "a") as f:
                f.write(f"FAIL: {prefix}.{name} - {status}: {poll.get('error_message','')[:100]}{tag}\n")
            fail += 1
            break
    else:
        with open(LOG_FILE, "a") as f:
            f.write(f"TIMEOUT: {prefix}.{name}{tag}\n")
        fail += 1
        continue
    
    ok += 1

with open(STATE_FILE, "w") as f:
    json.dump({"next_index": len(new_theorems), "total": len(new_theorems), "ok": ok, "fail": fail}, f)

with open(LOG_FILE, "a") as f:
    f.write(f"DONE: {ok} ok, {fail} fail, {skip} skip out of {len(new_theorems)} total\n")

print(f"DONE: {ok} ok, {fail} fail, {skip} skip out of {len(new_theorems)} total", file=sys.stderr)
