# "Unconstrained gauge-fixing" is satisfiable — the spectrum is the full spectrum of the basis

`book.tex` defines:

> "We define gauge-fixing as unconstrained whenever the gauge generators are
> necessarily excluded from the commutative von Neumann algebra and thus do not
> impose constraints on the spectrum of the commutative algebra."

An earlier note called an *auxiliary predicate* written for this sentence
unsatisfiable. That verdict concerned only that auxiliary predicate, which asked
for a function that is gauge invariant **and** changed by a gauge transformation
— a self-contradiction of the rendering, not of the book. The book's definition
itself **is satisfiable**, for the reason the definition intends: *the spectrum*
is the full spectrum labelled by the basis vectors `{e_x}`, not the spectrum of
the commutative subalgebra of (gauge-invariant) observables.

This is now formalized and proved in
`BookProof/ChapterGaugeUnconstrainedSpectrum.lean` (`sorry`-free; axiom audit
`Work/GaugeUnconstrainedSpectrumAudit.lean` reports only `propext`,
`Classical.choice`, `Quot.sound`).

## The model

The commutative von Neumann algebra of the gauge-fixing is given in its Gelfand
picture: the spectrum is the index type `X` of the basis, an element of the
algebra is a function `d : X → ℂ` acting as the diagonal operator
`diagOp d : f ↦ (x ↦ d x · f x)`, the point `y` of the spectrum is the basis
vector `basisVec y`, and a gauge transformation permuting the basis,
`e_y ↦ e_{σ y}`, is the operator `permOp σ`. An operator *is a function of the
spectrum* exactly when it belongs to that commutative algebra
(`IsFunctionOfSpectrum`).

## What is proved

* `diagOp_mul_comm` — the algebra of the gauge-fixing is commutative.
* `permOp_isFunctionOfSpectrum_iff` — a basis permutation is a function of the
  spectrum **iff** it is the identity: every non-trivial gauge transformation is
  *necessarily excluded* from the commutative algebra. This is the first half of
  the book's sentence.
* `IsUnconstrainedGaugeFixing` — the definition itself: no non-trivial gauge
  unitary is a function of the spectrum.
* `constrainedSpectrum_eq_univ_of_isUnconstrained` — the second half: the points
  of the spectrum that survive the constraints imposed by the gauge unitaries
  are *all* of them, because only an operator of the commutative algebra can
  impose a condition on the spectrum at all.
* `isUnconstrained_of_faithful`, `isUnconstrained_of_movesEveryPoint` — the
  definition is satisfied by every faithful permutation representation of the
  gauge group on the basis, in particular whenever every non-trivial gauge
  transformation moves every point of the spectrum (the book's other phrasing).
* `shift_isUnconstrainedGaugeFixing`, `exists_isUnconstrainedGaugeFixing` — the
  book's own example `e_k ↦ e_{k+1}` on the basis indexed by `ℤ` **is** an
  unconstrained gauge-fixing with full constrained spectrum: the definition is
  satisfiable, and satisfied by the gauge-fixing the book actually uses.
* `signRep_isNotUnconstrained`, `signRep_constrainedSpectrum` — the contrast of
  the book's two-basis discussion: in a basis in which the gauge unitaries *are*
  functions of the spectrum, the same kind of gauge group does cut the spectrum
  down to a proper subset.

## The two spectra

The new section 5 of the module states the distinction explicitly, since it is
the crux of the reading:

* `IsPhysicalFunction`, `observableSpectrum`, `isPhysicalFunction_iff_factors` —
  the gauge-invariant functions of the spectrum are exactly the functions of the
  orbit space `X/G`, which is the spectrum of the commutative **subalgebra of
  observables**.
* `shift_observableSpectrum_subsingleton`, `shift_isPhysicalFunction_const` — in
  the book's example that observable spectrum is a *single point* (the
  translations act transitively).
* `shift_full_spectrum_vs_observable_spectrum` — side by side: the gauge-fixing
  is unconstrained, the full spectrum of the basis is the infinite set `ℤ` and
  is left entirely unconstrained by the gauge generators, while the spectrum of
  the observable subalgebra is one point. Read as "the full spectrum defined by
  the basis vectors" the definition is satisfied; only the other reading would
  make it look empty.

## Status of the earlier auxiliary predicate

`ChapterG.IsUnconstrainedGaugeFixing` (in `BookProof/ChapterG/Part2.lean`) is
kept unchanged for the historical record, with a caveat in its docstring saying
that its unsatisfiability
(`ChapterGaugeIncompleteFixing.chapterG_isUnconstrainedGaugeFixing_vacuous`) is a
defect of that predicate only and that the book's definition is the one
formalized here.
