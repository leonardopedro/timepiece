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


def report(lib: str) -> None:
    comps = components(lib)
    multi = [c for c in comps if len(c[0]) > 1]
    print(f"## {lib}: {sum(len(c[0]) for c in comps)} modules, "
          f"{len(comps)} independent parts "
          f"({len(multi)} with more than one module)")
    for comp, roots in comps:
        name = COMPONENT_NAMES.get(comp[0], "")
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
            name = COMPONENT_NAMES.get(comp[0])
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


def lakefile(lib: str) -> None:
    for comp, roots in components(lib):
        if len(comp) < 2:
            continue
        name = COMPONENT_NAMES.get(comp[0])
        if name is None:
            print(f"# UNNAMED component of {len(comp)} modules, first {comp[0]}",
                  file=sys.stderr)
            continue
        print("[[lean_lib]]")
        print(f'name = "{name}"')
        print(f"# independent part: {len(comp)} modules")
        print("roots = [" + ", ".join(f'"{r}"' for r in roots) + "]")
        print()


def check(lib: str) -> int:
    """Verify the Lake targets against the sources.

    For every multi-module component: a target must exist in `lakefile.toml`,
    its `roots` must be exactly the maximal modules of the component, and the
    transitive import cone of those roots (inside the library) must be exactly
    the component — i.e. building the target builds that part and nothing more
    of this library.
    """
    text = open("lakefile.toml", encoding="utf-8").read()
    mods = module_files(lib)
    inside = set(mods)
    imports = {n: imports_of(p, inside) for n, p in mods.items()}
    bad = 0
    for comp, roots in components(lib):
        if len(comp) < 2:
            continue
        name = COMPONENT_NAMES.get(comp[0])
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
        cone, stack = set(), list(roots)
        while stack:
            x = stack.pop()
            if x in cone:
                continue
            cone.add(x)
            stack.extend(imports.get(x, []))
        if cone != set(comp):
            print(f"TARGET {name}: cone of the roots differs from the component "
                  f"({len(cone)} vs {len(comp)} modules)")
            bad += 1
        else:
            print(f"ok  {name}: {len(comp)} modules, closed under imports")
    return bad


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("library", nargs="?", default="BookProof")
    ap.add_argument("--all", action="store_true", help="report every library")
    ap.add_argument("--lakefile", action="store_true",
                    help="emit the [[lean_lib]] stanzas instead of the report")
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
