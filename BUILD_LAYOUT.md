# Project layout and how to build as little as possible

This note describes how the Lean sources are organized and how to add and test a
new proof without recompiling the whole development.

## Directory layout

Every Lean module lives in the directory that matches its module name, so that
`import X.Y` resolves to the file `X/Y.lean`:

| Library (`lakefile.toml`) | Root file | Modules |
| --- | --- | --- |
| `BookProof` | `BookProof.lean` | `BookProof/Chapter*.lean` — the formal development |
| `Book` | `Book.lean` | `Book/*.lean` — the Verso book chapters |
| `Singularity` | `Singularity.lean` | `Singularity/*.lean` — the ODE / singularity core |
| `Layout` | `Layout.lean` | pure-core layout certificates |
| `GapCertificate` | `GapCertificate.lean` | the instantiated certified-gap arithmetic |
| `UsedRoute`, `UnusedRoute`, `RandomMap`, `PnpProof` | `<Name>.lean` | `<Name>/*.lean` — the Riemann-route libraries |
| `RiemannProof` | `RiemannProof.lean` | `RiemannProof/*.lean` — thin re-exports kept for historical import paths |
| `Audits` | `Audits.lean` | `Audits/*.lean` — `#print axioms` scripts, run on demand |
| `Work` | `Work.lean` | `Work/*.lean` — scratch space for new developments |

The default targets are `BookProof`, `Book`, `Singularity`, `Layout`; `Audits`
and `Work` are deliberately *not* default targets, and their roots import
nothing, so they never slow a full build down.

## Building everything

```
lake build            # the four default targets
lake build BookProof  # the whole formal development
```

`BookProof.lean` imports every chapter, so this is the expensive entry point:
it compiles the entire book.

## Building as little as possible

Lake builds exactly the import cone of the module you name. To check one
chapter, name that chapter — never the library root:

```
lake build BookProof.ChapterClosureUniqueness
```

For **new** work, put the file in `Work/` and import only the chapters it
actually needs:

```lean
-- Work/MyNewResult.lean
import BookProof.ChapterEsaClosure          -- only what is needed
```

```
lake build Work.MyNewResult
```

Because `Work` is not a default target and `Work.lean` is empty, this compiles
your file plus the (already built) cone of the chapters you imported, and
nothing else. Once the result is stable, move it to `BookProof/Chapter<Name>.lean`
and add the import to `BookProof.lean`.

Two further rules keep incremental builds cheap:

* import the **most specific** chapter that provides what you need, not
  `BookProof` (which pulls in everything);
* keep `#print axioms` audits in `Audits/` or `Work/`, not in a chapter that
  other chapters import — an audit file transitively imports what it audits, so
  putting one in the middle of the dependency graph makes every later build
  depend on it. `Work/ClosureUniquenessAudit.lean` is the pattern to copy.

## Two rules that make a *new* chapter cheap (2026-09-04)

Adding a file to `BookProof/` used to cost far more than the file itself. Two
things were responsible, and both are now fixed for the unbounded-operator
thread; apply the same recipe to any new development.

### 1. `import BookProof.Prelude`, not `import Mathlib`

`import Mathlib` pulls the whole library — about **8000** build jobs — into the
import cone of the file, and that cone is re-checked on every build of it.
`BookProof/Prelude.lean` collects the Mathlib theory the analysis chapters
actually use (tactics, inner product spaces and adjoints, positive operators,
the continuous functional calculus and its order theory, real powers and square
roots) in about **3200** jobs.

```lean
import BookProof.Prelude
import BookProof.Chapter<TheOneChapterYouNeed>
```

If something you need is outside that cone, add the *specific* Mathlib module to
`BookProof/Prelude.lean` (or to your file) rather than falling back to
`import Mathlib`.

### 2. Depend on a `…Core` chapter, not on a physics chapter

Mathematically abstract material must not be reachable only through concrete
applications. The unbounded-operator thread used to reach the graph/closure
theory through `ChapterEsaClosure`, whose cone contained the Navier–Stokes,
Yang–Mills, Hermite–Galerkin and Hashimoto chapters: **34 modules** had to be
built before a new operator-theory chapter could be compiled.

The abstract prefixes now live in their own modules, which depend on the prelude
alone and are re-exported by the old chapters (all names and namespaces are
unchanged, so nothing else had to move):

| Core module | Contents | Re-exported by |
| --- | --- | --- |
| `BookProof/ChapterFarisLavineCore.lean` | `SymmetricOn`, `DeficiencyTrivialAt`, `EssentiallySelfAdjointOn`, `quadForm`, `commForm`, the Faris–Lavine criterion | `ChapterFarisLavine` |
| `BookProof/ChapterComplexShiftCore.lean` | `closed_of_selfAdjointCriterion`, `cshiftMap`, `cshiftRange` and the non-real shift bounds | `ChapterHashimotoShiftInvert`, `ChapterHashimotoComplexShifts` |
| `BookProof/ChapterEsaClosureCore.lean` | `opGraph`, `clGraph`, `clDom`, `clExt`, the self-adjointness criterion, the Cayley transform | `ChapterEsaClosure` |

The cone of `BookProof.ChapterNonnegResolvent` — the current tip of the thread —
is now **10 modules instead of 34**, a cold build of the whole thread takes
about a minute and a half instead of four minutes, and re-elaborating the tip
after an edit takes **3 s instead of 9 s**.

## Long modules are split into parts (2026-09-12)

Lean re-elaborates a whole module whenever any line of it changes, so a
thousand-line chapter costs a thousand lines of elaboration for a one-line
edit. Every `BookProof` module longer than ~500 lines is therefore split into
sequential parts:

```
BookProof/ChapterFoo.lean          -- the module docstring + `import`s of the parts
BookProof/ChapterFoo/Part1.lean    -- header + first slice  + closing `end`s
BookProof/ChapterFoo/Part2.lean    -- header + second slice + closing `end`s (imports Part1)
…
```

Nothing else in the development had to change: the original module name still
exists and re-exports all the parts, so `import BookProof.ChapterFoo` keeps
working and every declaration keeps its fully qualified name. Each part repeats
the original imports, `namespace`, `open`s and section openers, plus those
top-level `variable` commands of the earlier slices that it actually mentions.

Editing the last part of a four-part chapter now re-elaborates ~250 lines
instead of ~1000; the parts before it are untouched, and the thin root module
costs a few seconds.

### Doing it for another module

```
python3 scripts/propose_split.py BookProof/ChapterFoo.lean   # prints the command
python3 scripts/split_module.py  BookProof/ChapterFoo.lean HEADER_END FOOTER_START SPLIT…
lake build BookProof.ChapterFoo                              # always verify
```

`propose_split.py` picks the header, the closing `end`s and the split points
(top-level `/-! ## …` section comments closest to an even division);
`split_module.py` performs the split. Both are conservative: they never move a
declaration and never split inside a `section`/`namespace`, so the set of
declarations is unchanged — check it with

```
diff <(git show HEAD:BookProof/ChapterFoo.lean | rg '^(theorem|lemma|def) ') \
     <(cat BookProof/ChapterFoo/Part*.lean   | rg '^(theorem|lemma|def) ')
```

## Compiling the independent parts separately (2026-09-12)

Splitting long modules makes *one* module cheap to re-check; the complementary
step is to know which groups of modules have no Lean dependency on each other at
all, so that they can be compiled separately.

Two modules are dependent when one imports the other, directly or transitively;
the connected components of that relation are the **independent parts** of the
development. `BookProof` has 110 of them. Every part with more than one module now
has its own Lake target whose `roots` are the maximal modules of the part, so

```
lake build BookProofMeasureFoundations   # 33 modules: measure/gauge foundations
lake build BookProofAttention            # 75 modules, disjoint from the above
lake build BookProof.ChapterBosonicCCR   # a part that is a single module
```

compiles exactly that part and nothing else — two such commands can run in
parallel jobs without either being able to invalidate the other. None of the part
targets is a default target, so `lake build` and `lake build BookProof` are
unchanged.

The targets are generated from the sources, not maintained by hand:

```
python3 scripts/import_components.py BookProof            # the report
python3 scripts/import_components.py BookProof --lakefile # the [[lean_lib]] stanzas
python3 scripts/import_components.py --all                # every library
python3 scripts/import_components.py BookProof --check     # verify the targets
```

`--check` re-derives the components from the sources and verifies, for every
multi-module part, that its target exists in `lakefile.toml`, that its `roots`
are listed, and that the transitive import cone of those roots is exactly the
part — so building the target cannot pull in a module of another part.

### Sub-system targets: a view of one part

Some coherent sub-developments are too connected to the rest to ever be a part of
their own — their dependencies are shared with a part — yet they are exactly what
one wants to compile while working on them. A **sub-system target** answers that:
its `roots` are the modules the sub-system is *about*, and its cone (everything
those roots import) is by construction a subset of the containing part's cone, so
the target can never duplicate work across jobs; it only lets one job compile
less.

```
lake build BookProofDerivativeGauge   # 188 modules: a view of BookProofOperatorCore
```

The derivative gauge is the sub-system so far: the two chapters that adjoin each
derivative in space of a field as an independent canonical variable and let the
gauge condition set it back equal to that derivative (`u_{i,j}` for
Navier–Stokes, the auxiliary `D_mu_nu^i(k)` for gravity), together with the 188
modules they rest on. `--check` verifies sub-system targets as well: the roots
must be real modules, they must be exactly the maximal modules of the cone they
generate, and the cone must stay inside a single part — a cone spanning two parts
would redo another job's work.

`BUILD_COMPONENTS.md` holds the generated inventory. Re-run the script after
adding modules: a new module that imports two previously independent parts merges
them, which the report makes visible immediately, and a new multi-module part is
flagged as `UNNAMED component` until a target name is added to `COMPONENT_NAMES`
in the script.

The practical rule that keeps the parts apart: **import the most specific chapter
that provides what you need, and prefer splitting a new development into one
module per part over one module importing several parts.** The gauge material
added in this pass follows it — the general theory
(`BookProof/ChapterGaugeIncompleteFixing.lean`) imports the gauge/measure
foundations only, and its `ℓ²(ℤ)` example
(`BookProof/ChapterGaugeShiftExample.lean`) imports the lattice-unitary chapter
only, so the two parts stay independent.
