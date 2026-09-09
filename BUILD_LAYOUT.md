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
