#!/usr/bin/env python3
"""Compute the *independent parts* of the Lean development.

Two modules of this repository are **dependent** if one imports the other
(directly or transitively); the connected components of that relation are the
parts of the project that can be compiled completely independently of each
other.  This script computes those components for a first-party library and

* prints a report (used to generate `BUILD_COMPONENTS.md`), and
* prints, with `--lakefile`, the `[[lean_lib]]` stanzas that give every
  multi-module component its own Lake target, whose `roots` are the maximal
  modules of the component (the modules that nothing else imports).  Building
  such a target builds exactly that component and nothing else.

Usage:

    python3 scripts/import_components.py BookProof
    python3 scripts/import_components.py BookProof --lakefile
    python3 scripts/import_components.py --all

Besides the independent parts, the tool knows the *sub-system targets* of
`SUB_SYSTEM_TARGETS` below: a view of one part, for a coherent sub-development
that is too connected to be a part of its own.  See `BUILD_COMPONENTS.md`.
"""

from __future__ import annotations

import argparse
import collections
import os
import re
import sys

LIBRARIES = [
    "BookProof",
    "Singularity",
    "Layout",
    "RandomMap",
    "UsedRoute",
    "UnusedRoute",
    "RiemannProof",
    "PnpProof",
    "Work",
    "Audits",
]

IMPORT_RE = re.compile(r"\s*import\s+([A-Za-z0-9_.]+)")

# Stable, hand-chosen target names for the multi-module components of
# `BookProof`, keyed by the alphabetically first module of the component.
# A component that is not listed keeps no dedicated target: a single-module
# component is already built by `lake build <module>`.
COMPONENT_NAMES = {
    "BookProof.ChapterA": "BookProofRealification",
    "BookProof.ChapterA3": "BookProofLieRep",
    "BookProof.ChapterAbelianAtomicCondensation": "BookProofAtomicDecomposition",
    "BookProof.ChapterAbelianClassificationList": "BookProofOperatorCore",
    "BookProof.ChapterAbelianDiagonal": "BookProofAttention",
    "BookProof.ChapterB": "BookProofMeasureFoundations",
    "BookProof.ChapterBell": "BookProofBell",
    "BookProof.ChapterBesselHarmonic": "BookProofHarmonicAnalysis",
    "BookProof.ChapterCausality": "BookProofCausality",
    "BookProof.ChapterConditional": "BookProofPauliGrover",
    "BookProof.ChapterConservative": "BookProofConservative",
    "BookProof.ChapterCountableDefinability": "BookProofDefinability",
    "BookProof.ChapterDensityMarginalConditional": "BookProofDensity",
    "BookProof.ChapterDeterministic": "BookProofReconstruction",
    "BookProof.ChapterEnergyBandDecomposition": "BookProofEnergyBand",
    "BookProof.ChapterFreeEMField": "BookProofFieldStrength",
    "BookProof.ChapterFreeFieldBorn": "BookProofFreeFieldBorn",
    "BookProof.ChapterGravityGenInverse": "BookProofGravityAlgebra",
    "BookProof.ChapterHilbertSumIntertwine": "BookProofInducedSystems",
    "BookProof.ChapterHolomorphic": "BookProofHolomorphic",
    "BookProof.ChapterKrylovShiftSpan": "BookProofKrylovShiftSpan",
    "BookProof.ChapterLorentzDecomp": "BookProofLorentz",
    "BookProof.ChapterOdeSampling": "BookProofSamplingTheory",
    "BookProof.ChapterPauliLorentz": "BookProofPauli",
    "BookProof.ChapterRoadmapAudit": "BookProofRoadmapAudit",
    "BookProof.ChapterWeylSL2Group": "BookProofWeylSL2",
    "BookProof.ChapterWignerLittleGroup": "BookProofWignerOrbit",
}

# Build-layout decision (2026-09-24e).  When a new module imports two previously
# independent parts, the merged component contains the anchors of *both* names.
# The name listed first here wins, so a target that the plan and the audits use
# as a gate is never silently renamed by a merge.  `BookProofOperatorCore` is the
# operator-theoretic core; the former `BookProofLieRep` part (the `ChapterA3*`
# Lie-representation chapters) was merged into it by the Standard-Model and
# gauge chapters, which import both, and is retired as a separate target.
NAME_PRECEDENCE = [
    "BookProofOperatorCore",
]


def component_name(comp: list[str]) -> str | None:
    """The Lake target name of a component (`None` if it has none).

    Default: the name keyed by the alphabetically first module of the
    component (the historical rule).  If the component contains the anchor
    modules of several names, `NAME_PRECEDENCE` decides.
    """
    members = set(comp)
    cands = [n for k, n in COMPONENT_NAMES.items() if k in members]
    if not cands:
        return None
    for n in NAME_PRECEDENCE:
        if n in cands:
            return n
    return COMPONENT_NAMES.get(comp[0], cands[0])


def aggregator_cone(lib: str) -> set[str] | None:
    """The modules reachable from the library root `<Lib>.lean`, or `None`."""
    mods = module_files(lib)
    if lib not in mods:
        return None
    inside = set(mods)
    imports = {n: imports_of(p, inside) for n, p in mods.items()}
    return cone_of([lib], imports)


# Sub-system targets: a *view* of one part, for a coherent sub-development that
# is far too connected to be a part of its own.
#
# A sub-system target's `roots` are the modules the sub-system is *about*, and
# its transitive import cone is what `lake build <name>` compiles -- necessarily
# a subset of the cone of the containing part, so the target can never duplicate
# work across jobs; it only lets one job compile less than the whole part.
#
# The derivative gauge.  The device these two chapters are about is to adjoin
# each derivative in space of a field as an independent canonical variable and
# let the gauge condition set it back equal to that derivative -- `u_{i,j}` for
# Navier-Stokes, the auxiliary `D_{mu nu}^i(k)` for gravity.  They cannot be a
# part of their own: their dependencies are shared with `BookProofOperatorCore`,
# which is what makes the sub-system target worth having instead.
#
# Keyed by library, because a sub-system is a sub-system *of one library*: a
# single global table would have `--check` demanding BookProof's roots inside
# `Work` and `Layout`.
SUB_SYSTEM_TARGETS = {
    "BookProof": {
        "BookProofDerivativeGauge": [
            "BookProof.ChapterNsBrstDerivativeGauge",
            "BookProof.ChapterNsFieldMomentumInverse",
            "BookProof.ChapterQgBrstDerivativeGauge",
        ],
    },
}


def cone_of(roots: list[str], imports: dict[str, list[str]]) -> set[str]:
    """The transitive import cone (inside one library) of a set of roots."""
    cone: set[str] = set()
    stack = list(roots)
    while stack:
        x = stack.pop()
        if x in cone:
            continue
        cone.add(x)
        stack.extend(imports.get(x, []))
    return cone


def module_files(lib: str) -> dict[str, str]:
    """All modules of a library: `<Lib>.lean` plus everything under `<Lib>/`."""
    mods: dict[str, str] = {}
    root = lib + ".lean"
    if os.path.exists(root):
        mods[lib] = root
    for base, _dirs, files in os.walk(lib):
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(base, f)
                mods[p[:-5].replace(os.sep, ".")] = p
    return mods


def imports_of(path: str, inside: set[str]) -> list[str]:
    out = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            m = IMPORT_RE.match(line)
            if m:
                if m.group(1) in inside:
                    out.append(m.group(1))
            elif line.strip() and not line.lstrip().startswith("--"):
                break
    return out


def components(lib: str, skip_root: bool = True):
    """Connected components of the import relation inside one library.

    The library root (`<Lib>.lean`, which imports every module) is excluded:
    it is the aggregator, not a mathematical dependency.
    """
    mods = module_files(lib)
    if skip_root and lib in mods and len(mods) > 1:
        # the library root is the aggregator that imports every module; it is
        # not a mathematical dependency, so it is left out of the graph
        if len(imports_of(mods[lib], set(mods) - {lib})) >= 2:
            # Build-layout decision (2026-09-24e): the parts partition exactly
            # what `lake build <Lib>` compiles.  Modules the aggregator does not
            # reach (stale split copies `X/Part*.lean` of a monolithic `X.lean`)
            # are left out of the graph and reported by `orphans`.
            reach = aggregator_cone(lib) or set(mods)
            mods = {n: p for n, p in mods.items() if n in reach}
            mods.pop(lib, None)
    inside = set(mods)
    imports = {n: imports_of(p, inside) for n, p in mods.items()}
    adj = collections.defaultdict(set)
    for n, deps in imports.items():
        for d in deps:
            adj[n].add(d)
            adj[d].add(n)
    indeg = collections.Counter()
    for deps in imports.values():
        for d in deps:
            indeg[d] += 1
    seen, comps = set(), []
    for n in sorted(mods):
        if n in seen:
            continue
        stack, comp = [n], []
        seen.add(n)
        while stack:
            x = stack.pop()
            comp.append(x)
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        comp.sort()
        roots = [m for m in comp if indeg[m] == 0]
        comps.append((comp, roots))
    comps.sort(key=lambda cr: (-len(cr[0]), cr[0][0]))
    return comps


def orphans(lib: str) -> list[str]:
    """Modules of the library that its aggregator `<Lib>.lean` does not reach.

    `lake build <Lib>` never compiles them, so they belong to no part and need
    no target.  In `BookProof` they are stale split copies `X/Part*.lean` of a
    monolithic `X.lean`; they are listed so that they can be deleted or wired in
    deliberately, never silently.
    """
    mods = module_files(lib)
    reach = aggregator_cone(lib)
    if reach is None:
        return []
    return sorted(n for n in mods if n not in reach)


def report(lib: str) -> None:
    comps = components(lib)
    multi = [c for c in comps if len(c[0]) > 1]
    print(f"## {lib}: {sum(len(c[0]) for c in comps)} modules, "
          f"{len(comps)} independent parts "
          f"({len(multi)} with more than one module)")
    for comp, roots in comps:
        name = (component_name(comp) or "")
        tag = f"  target `{name}`" if name else ""
        print(f"* {len(comp):4d} modules, {len(roots)} maximal "
              f"(first: {comp[0]}){tag}")


def markdown(lib: str) -> None:
    """One library's section of the `## Inventory` in `BUILD_COMPONENTS.md`.

    The committed inventory is this function's output, one section per library
    (`--all` for the whole file), so the tables and the module counts in the
    prose can be regenerated rather than transcribed.  The roots column is cut
    after six entries and says how many there are, which is a rendering choice:
    the `--lakefile` output always carries the complete list.
    """
    comps = components(lib)
    if not comps:
        return
    modules = {m for comp, _ in comps for m in comp}
    multi = [c for c in comps if len(c[0]) > 1]
    single = [c[0][0] for c in comps if len(c[0]) == 1]
    print(f"### `{lib}` — {len(modules)} modules, {len(comps)} independent parts "
          f"({len(multi)} with more than one module)")
    print()
    if multi:
        print("| modules | Lake target | maximal modules (the `roots` of the target) |")
        print("| ---: | --- | --- |")
        for comp, roots in multi:
            name = component_name(comp)
            cell = f"`{name}`" if name else "*(build its maximal modules directly)*"
            shown = ", ".join(f"`{r}`" for r in roots[:6])
            if len(roots) > 6:
                shown += f", … ({len(roots)} in total)"
            print(f"| {len(comp)} | {cell} | {shown} |")
        print()
    if single:
        print(f"The remaining {len(single)} parts are single modules, each built by "
              f"`lake build <module>`:")
        print()
        print(", ".join(f"`{m}`" for m in single))
        print()
    sub = sub_system_markdown(lib, comps)
    if sub:
        print(sub, end="")


PART_MARKER = "# Independent parts of `BookProof`, one Lake target each."
SUB_MARKER = "# Sub-system targets: a *view* of one part"


def write_lakefile(lib: str) -> None:
    """Regenerate the part and sub-system stanzas of `lakefile.toml` in place.

    Everything before the first generated `[[lean_lib]]` after `PART_MARKER`
    and the hand-written comment block starting at `SUB_MARKER` are kept
    verbatim; only the generated stanzas are replaced.
    """
    import contextlib
    import io
    text = open("lakefile.toml", encoding="utf-8").read()
    i = text.index(PART_MARKER)
    j = text.index("[[lean_lib]]", i)
    k = text.index(SUB_MARKER)
    k0 = text.rindex("# ----", 0, k)
    m = text.index("[[lean_lib]]", k)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        lakefile(lib)
    gen = buf.getvalue()
    subs = list(SUB_SYSTEM_TARGETS.get(lib, {}))
    cut = len(gen)
    for name in subs:
        pos = gen.find(f'[[lean_lib]]\nname = "{name}"')
        if pos != -1:
            cut = min(cut, pos)
    parts, subpart = gen[:cut], gen[cut:]
    new = text[:j] + parts + text[k0:m] + subpart.rstrip("\n") + "\n"
    open("lakefile.toml", "w", encoding="utf-8").write(new)


def lakefile(lib: str) -> None:
    mods = module_files(lib)
    inside = set(mods)
    imports = {n: imports_of(p, inside) for n, p in mods.items()}
    for comp, roots in components(lib):
        if len(comp) < 2:
            continue
        name = component_name(comp)
        if name is None:
            print(f"# UNNAMED component of {len(comp)} modules, first {comp[0]}",
                  file=sys.stderr)
            continue
        print("[[lean_lib]]")
        print(f'name = "{name}"')
        print(f"# independent part: {len(comp)} modules")
        print("roots = [" + ", ".join(f'"{r}"' for r in roots) + "]")
        print()
    for name, roots in SUB_SYSTEM_TARGETS.get(lib, {}).items():
        present = [r for r in roots if r in inside]
        if not present:
            continue
        n = len(cone_of(present, imports))
        print("[[lean_lib]]")
        print(f'name = "{name}"')
        print(f"# sub-system target: {len(present)} root(s), {n} modules in the cone")
        print("roots = [" + ", ".join(f'"{r}"' for r in present) + "]")
        print()


def sub_system_markdown(lib: str, comps) -> str:
    """The `### Sub-system targets` block of `BUILD_COMPONENTS.md`."""
    mods = module_files(lib)
    inside = set(mods)
    imports = {n: imports_of(p, inside) for n, p in mods.items()}
    part_of = {m: comp[0] for comp, _roots in comps for m in comp}
    part_names = {comp[0]: (component_name(comp) or "*(unnamed)*")
                  for comp, _roots in comps}
    rows, out = [], []
    for name, roots in SUB_SYSTEM_TARGETS.get(lib, {}).items():
        present = [r for r in roots if r in inside]
        if not present:
            continue
        cone = cone_of(present, imports)
        parts = sorted({part_names.get(part_of.get(m, ""), "?")
                        for m in cone if m in part_of})
        rows.append((name, present, cone, parts))
    if not rows:
        return ""
    out.append(f"### Sub-system targets of `{lib}`")
    out.append("")
    out.append("A sub-system target is a *view* of one part: a coherent piece of the "
               "development that is far too connected to be a part of its own. Its "
               "`roots` are the modules it is about, and its cone is a subset of the "
               "containing part's cone, so it never duplicates work across jobs -- it "
               "only lets one job compile less.")
    out.append("")
    out.append("| Lake target | roots | modules in the cone | inside the part |")
    out.append("| --- | --- | ---: | --- |")
    for name, roots, cone, parts in rows:
        shown = ", ".join(f"`{r}`" for r in roots)
        out.append(f"| `{name}` | {shown} | {len(cone)} | "
                   f"{', '.join('`' + p + '`' for p in parts)} |")
    out.append("")
    out.append("Unlike a part target, a sub-system target is not checked for "
               "closure: its cone is strictly larger than the sub-system, by "
               "construction. `--check` verifies instead that its roots are real "
               "modules, that they are exactly the maximal modules of the cone they "
               "generate, and that the cone stays inside a single part.")
    out.append("")
    return "\n".join(out)


def check(lib: str) -> int:
    """Verify the Lake targets against the sources.

    For every multi-module component: a target must exist in `lakefile.toml`,
    its `roots` must be exactly the maximal modules of the component, and the
    transitive import cone of those roots (inside the library) must be exactly
    the component — i.e. building the target builds that part and nothing more
    of this library.

    For every sub-system target of the library (which is a *view* of one part,
    so the closure requirement cannot apply): the roots must be real modules,
    they must be exactly the maximal modules of the cone they generate, and the
    cone must stay inside a single part.
    """
    text = open("lakefile.toml", encoding="utf-8").read()
    mods = module_files(lib)
    inside = set(mods)
    imports = {n: imports_of(p, inside) for n, p in mods.items()}
    bad = 0
    part_names = set(COMPONENT_NAMES.values())
    comps = components(lib)
    # Every module belongs to a part; a single-module part is identified by the
    # module itself, since it needs no target.
    part_of = {m: (component_name(comp) or comp[0]) for comp, _ in comps
               for m in comp}
    reachable = aggregator_cone(lib)
    for comp, roots in comps:
        if len(comp) < 2:
            continue
        name = component_name(comp)
        if name is None and reachable is not None and not (set(comp) & reachable):
            # An orphan part: none of its modules is imported by `<Lib>.lean`,
            # so `lake build <Lib>` never compiles it (typically a stale split
            # copy `X/Part*.lean` of a monolithic `X.lean`).  Reported, not a
            # failure: it needs no target because it is not part of the build.
            print(f"orphan (not imported by {lib}.lean, not built): "
                  f"{', '.join(comp)}")
            continue
        if name is None:
            print(f"MISSING NAME: component of {len(comp)} modules ({comp[0]})")
            bad += 1
            continue
        if f'name = "{name}"' not in text:
            print(f"MISSING TARGET in lakefile.toml: {name}")
            bad += 1
            continue
        for r in roots:
            if f'"{r}"' not in text:
                print(f"TARGET {name}: root {r} not listed")
                bad += 1
        cone = cone_of(roots, imports)
        if cone != set(comp):
            print(f"TARGET {name}: cone of the roots differs from the component "
                  f"({len(cone)} vs {len(comp)} modules)")
            bad += 1
        else:
            print(f"ok  {name}: {len(comp)} modules, closed under imports")

    # Sub-system targets: a view of one part.  What must hold is that the roots
    # are real modules, that they are exactly the maximal modules of the cone
    # they generate (a sub-system root nothing else in its cone imports), and
    # that the cone does not straddle two parts -- across parts the target would
    # redo work another job is already doing.
    for name, roots in SUB_SYSTEM_TARGETS.get(lib, {}).items():
        present = [r for r in roots if r in inside]
        missing = [r for r in roots if r not in inside]
        if missing:
            print(f"SUB-TARGET {name}: not a module of {lib}: {', '.join(missing)}")
            bad += 1
            continue
        if name in part_names:
            print(f"SUB-TARGET {name}: collides with a part target name")
            bad += 1
            continue
        if f'name = "{name}"' not in text:
            print(f"MISSING TARGET in lakefile.toml: {name}")
            bad += 1
            continue
        for r in present:
            if f'"{r}"' not in text:
                print(f"SUB-TARGET {name}: root {r} not listed")
                bad += 1
        cone = cone_of(present, imports)
        inner = {d for n in cone for d in imports.get(n, []) if d in cone}
        maxima = sorted(n for n in cone if n not in inner)
        if maxima != sorted(present):
            print(f"SUB-TARGET {name}: roots are not the maximal modules of the cone "
                  f"(maximal: {', '.join(maxima)})")
            bad += 1
        parts = sorted({part_of.get(m, m) for m in cone})
        if len(parts) != 1:
            print(f"SUB-TARGET {name}: cone straddles {len(parts)} parts: "
                  f"{', '.join(parts[:4])}{' …' if len(parts) > 4 else ''}")
            bad += 1
        else:
            print(f"ok  {name}: {len(cone)} modules, a view of {parts[0]}")
    orph = orphans(lib)
    if orph:
        print(f"note: {len(orph)} module(s) not imported by {lib}.lean "
              f"(not built, belong to no part): {', '.join(orph[:8])}"
              f"{' …' if len(orph) > 8 else ''}")
    return bad


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("library", nargs="?", default="BookProof")
    ap.add_argument("--all", action="store_true", help="report every library")
    ap.add_argument("--lakefile", action="store_true",
                    help="emit the [[lean_lib]] stanzas instead of the report")
    ap.add_argument("--write-lakefile", action="store_true",
                    help="regenerate the stanzas of lakefile.toml in place")
    ap.add_argument("--check", action="store_true",
                    help="verify the targets in lakefile.toml against the sources")
    ap.add_argument("--markdown", action="store_true",
                    help="emit the `## Inventory` of BUILD_COMPONENTS.md")
    args = ap.parse_args()
    if args.markdown:
        for lib in (LIBRARIES if args.all else [args.library]):
            if os.path.exists(lib) or os.path.exists(lib + ".lean"):
                markdown(lib)
                print()
        return
    if args.write_lakefile:
        write_lakefile(args.library)
        return
    if args.lakefile:
        lakefile(args.library)
        return
    if args.check:
        sys.exit(1 if check(args.library) else 0)
    for lib in (LIBRARIES if args.all else [args.library]):
        if os.path.exists(lib) or os.path.exists(lib + ".lean"):
            report(lib)
            print()


if __name__ == "__main__":
    main()
