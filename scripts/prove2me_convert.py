#!/usr/bin/env python3
"""Generate the Lean 4.28.0 conversion skeleton of the prove2.me downloads.

Reads `Downloads/manifest.json` and the verbatim solution sources under
`Downloads/<group>/`, and writes one module per downloaded solution under
`converted/Prove2me/<Group>/<Name>.lean` (module `Prove2me.<Group>.<Name>`).

Solutions that import platform library modules (`Definitions.Def_*`,
`Theorems.Thm_*`) that are not among the downloads are written to
`converted/blocked/<Group>/` instead: their text is prepared the same way but
they cannot be compiled until those platform modules are supplied.

Each generated module consists of
  1. an attribution / provenance header (platform theorem id, original name,
     statement author, solution author, submission id, source, platform
     Mathlib rev, Apache-2.0 notice);
  2. the import block, with `Theorems.Thm_<X>` imports re-pointed at the
     converted module of the downloaded item `X` when it exists;
  3. the verbatim solution body, with the single platform entry point
     `theorem solution` renamed to `Prove2me.Solution.<Name>` so that several
     converted modules can be imported together;
  4. the platform's formal statement (from the manifest), under its original
     name, proved by the renamed solution.

By default the script only writes modules that do not exist yet, so the hand
conversion edits made afterwards are never overwritten (`--force` regenerates
the blocked modules, `--force-all` every module).
The conversion record (unified diff original -> converted) is produced by
`scripts/prove2me_diff.py`.
"""
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DL = os.path.join(ROOT, "Downloads")
OUT = os.path.join(ROOT, "converted", "Prove2me")


def group_mod(group: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in group.split("-"))


def name_mod(theorem_name: str) -> str:
    return theorem_name.replace(".", "_")


def module_of(item) -> str:
    group = item["solution_file"].split("/")[0]
    return f"Prove2me.{group_mod(group)}.{name_mod(item['theorem_name'])}"


# Platform Mathlib (rev 0df444a360ea) -> this repository's Mathlib pin: lemma renames
# confirmed by name lookup in the pinned environment (old name absent, new name present).
RENAMES = {
    "continuous_finsetSum": "continuous_finset_sum",
    "tendsto_finsetSum": "tendsto_finset_sum",
    "intervalIntegral.integral_finsetSum": "intervalIntegral.integral_finset_sum",
    "integral_finsetSum": "integral_finset_sum",
    "integrable_finsetSum": "integrable_finset_sum",
    "memLp_finsetSum'": "memLp_finset_sum'",
    "HasDerivAt.fun_finsetProd": "HasDerivAt.fun_finset_prod",
    "HasFDerivAt.finsetProd": "HasFDerivAt.finset_prod",
}


def apply_renames(text: str) -> str:
    for old, new in RENAMES.items():
        text = re.sub(r"(?<![\w.'])" + re.escape(old) + r"(?![\w'])", new, text)
    return text


def platform_imports(item):
    """Non-Mathlib imports of the downloaded solution (platform library modules)."""
    src = os.path.join(DL, item["solution_file"])
    return [l.split()[1] for l in open(src, encoding="utf-8")
            if l.startswith("import ") and l.split()[1].startswith(("Definitions.", "Theorems."))]


def path_of(item) -> str:
    """Every converted solution lands in `converted/Prove2me/<Group>/<Name>.lean`.
    (Until the platform library was supplied on 2026-10-19, the solutions importing
    `Definitions.*` / `Theorems.*` modules were parked in `converted/blocked/`.)"""
    group = item["solution_file"].split("/")[0]
    return os.path.join(OUT, group_mod(group), name_mod(item["theorem_name"]) + ".lean")


def explicit_args(sig: str):
    """Names bound by the explicit `( ... )` binders of a declaration header
    (the text between the declaration name and its type colon)."""
    names, depth, i, start, opener = [], 0, 0, 0, ""
    while i < len(sig):
        c = sig[i]
        if depth == 0 and c == ":":
            break
        if c in "([{⦃":
            if depth == 0:
                start, opener = i, c
            depth += 1
        elif c in ")]}⦄":
            depth -= 1
            if depth == 0 and opener == "(":
                inner, d, j = sig[start + 1:i], 0, 0
                while j < len(inner):
                    if inner[j] in "([{":
                        d += 1
                    elif inner[j] in ")]}":
                        d -= 1
                    elif inner[j] == ":" and d == 0:
                        break
                    j += 1
                names += inner[:j].split()
        i += 1
    return names


def header(item) -> str:
    return f"""/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : {item['theorem_id']}
* original name       : `{item['theorem_name']}`
* title               : {item['theorem_title']}
* statement author    : {item['created_by_username']}
* solution author     : {item['submission_username']} (submission {item['submission_id']},
                        accepted {item['submission_accepted_at']})
* source              : {item['source']}
* platform Mathlib rev: {item['mathlib_rev']}
* original file       : Downloads/{item['solution_file']}

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/{name_mod(item['theorem_name'])}.diff`.
-/
"""


def main(force: bool, force_all: bool) -> None:
    manifest = json.load(open(os.path.join(DL, "manifest.json")))
    items = [i for i in manifest["items"] if i.get("solution_file")]
    by_key = {name_mod(i["theorem_name"]): i for i in items}
    written = 0
    for item in items:
        src = os.path.join(DL, item["solution_file"])
        dst = path_of(item)
        # the 21 hand-converted self-contained modules are only regenerated with
        # --force-all; --force regenerates the ones importing platform modules
        if os.path.exists(dst) and not (force_all or (force and platform_imports(item))):
            continue
        lines = open(src, encoding="utf-8").read().split("\n")
        pre, imports, body, seen_import, in_body = [], [], [], False, False
        for ln in lines:
            if not in_body and not ln.startswith("import "):
                if not seen_import:
                    pre.append(ln)
                    continue
                if ln.strip() == "":
                    continue
                in_body = True
            if not in_body:
                seen_import = True
                mod = ln.split()[1]
                if mod.startswith("Theorems.Thm_") and mod[len("Theorems.Thm_"):] in by_key:
                    dep = by_key[mod[len("Theorems.Thm_"):]]
                    if dep is item:
                        # a solution importing its own statement module: drop it
                        imports.append(f"-- (dropped self-import `{mod}`)")
                        continue
                    imports.append(f"import {module_of(dep)}  -- was `{mod}`")
                else:
                    imports.append(ln)
            else:
                body.append(ln)
        sol = f"Prove2me.Solution.{name_mod(item['theorem_name'])}"
        text = apply_renames("\n".join(body))
        text, n = re.subn(r"^(theorem|lemma) solution\b", rf"\1 _root_.{sol}", text,
                          count=1, flags=re.M)
        if n != 1:
            print("warning: no `theorem solution` in", src, file=sys.stderr)
        else:
            # later references to the entry point (`#print axioms solution`, uses in
            # proofs) follow the rename
            k0 = text.index(f"_root_.{sol}") + len(f"_root_.{sol}")
            text = text[:k0] + re.sub(r"(?<![\w.'])solution(?![\w'])", f"_root_.{sol}",
                                      text[k0:])
        # context lines of the platform preamble that the statement elaborates in
        body_lines = set(text.split("\n"))
        ctx, keep = [], False
        for l in (item.get("preamble") or "").split("\n"):
            if l[:1] in (" ", "\t") and l.strip():
                # continuation line of a multi-line `variable` / `open` command
                if keep:
                    ctx.append(l)
                continue
            keep = (l.startswith(("open ", "namespace ", "section", "noncomputable section",
                                  "variable", "universe ", "set_option "))
                    and not (l.startswith("universe ") and l in body_lines))
            if keep:
                ctx.append(l)
        stmt = item["formal_statement"].rstrip()
        # a `universe` line already declared by the solution body cannot be repeated
        stmt = "\n".join(l for l in stmt.split("\n")
                         if not (l.startswith("universe ") and l in body_lines))
        hd = re.search(r"theorem\s+([^\s\[({⦃]+)(.*?):=\s*by\s*sorry", stmt, re.S)
        args = explicit_args(hd.group(2)) if hd else []
        proof = (f":= by\n  first\n  | exact _root_.{sol}" + "".join(" " + a for a in args)
                 + f"\n  | (apply _root_.{sol} <;> assumption)\n\n")
        stmt, k = re.subn(r":=\s*by\s*sorry\s*", lambda _m: proof, stmt, count=1)
        if k != 1:
            print("warning: statement without `by sorry` in", src, file=sys.stderr)
        # close the namespaces / sections the preamble opened and the statement did not
        stack = []
        for l in ctx + stmt.split("\n"):
            if l.startswith("namespace "):
                stack.append(l.split()[1])
            elif l.startswith(("section", "noncomputable section")):
                stack.append(l.split()[-1] if l.split()[-1] != "section" else "")
            elif l.startswith("end") and stack:
                stack.pop()
        closers = "".join(f"end {x}\n".replace("end \n", "end\n") for x in reversed(stack))
        last = item["theorem_name"].split(".")[-1]
        declared = re.search(r"^\s*(private\s+|protected\s+)?(theorem|lemma)\s+(?!(_root_\.)?Prove2me\.Solution\.)(_root_\.)?(\S*\.)?"
                             + re.escape(last) + r"(?![\w'.])", text, re.M)
        pre_comments = [l for l in pre if l.strip()]
        out = header(item)
        if pre_comments:
            out += "\n".join(pre_comments) + "\n"
        out += "\n".join(imports) + "\n\n" + text.rstrip() + "\n\n"
        if declared:
            # the solution declares the platform theorem itself: restate the registered
            # statement as an `example`, so that it is still checked without a name clash
            stmt = re.sub(r"theorem\s+[^\s\[({⦃]+", "example", stmt, count=1)
            out += ("/-! ## Platform statement\n\nThe formal statement registered on prove2.me "
                    "(manifest `formal_statement`), checked against the solution above.  The solution "
                    f"declares the platform theorem `{item['theorem_name']}` itself, so the statement "
                    "is restated as an `example`. -/\n\n")
        else:
            out += ("/-! ## Platform statement\n\nThe formal statement registered on prove2.me "
                    "(manifest `formal_statement`), proved by the solution above. -/\n\n")
        out += "section Prove2meStatement\n\n"
        if ctx:
            out += "\n".join(ctx) + "\n\n"
        out += stmt.rstrip() + "\n\n" + closers + "\nend Prove2meStatement\n"
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, "w", encoding="utf-8").write(out)
        written += 1
    print(f"wrote {written} module(s)")


if __name__ == "__main__":
    main("--force" in sys.argv, "--force-all" in sys.argv)
