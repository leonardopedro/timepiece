# `math28/` — hypotheses supported by `math/`, in Lean v4.28.0

`math/` is a read-only snapshot of a Lean **v4.34.1** library (`OAI.*`). This repository pins
Lean **v4.28.0** with Mathlib `8f9d9cf`, so `math/` is **not compiled** here. Instead, this
folder (Lean library `Math28`, `srcDir = "math28"` in `lakefile.toml`) restates, on v4.28.0,
the `math/` results that bear on this project as **named hypotheses** (`def … : Prop`). It
also proves short **bridge theorems** that take those hypotheses as explicit arguments and
connect them to the project's own statements.

Build: `lake build Math28 Math28.Audit`. Green; no `sorry`, no new `axiom`. Every bridge
theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (see
`Math28/Audit.lean`).

## What "supported by `math/`" means here

For each hypothesis, the corresponding `math/` theorem was located and its import closure
was **scanned as text**: no `sorry`, `axiom` or `native_decide`. The `math/` proofs were
**not** re-elaborated, because they need Lean v4.34.1. Some closures also import packages
that are not in the snapshot, so for those the snapshot alone does not settle the proof (marked ⚠ below).
Treat every hypothesis as an assumption, never as a theorem of this repository.

| Module | Named hypotheses (source theorem) | Proved bridges | Source status |
|---|---|---|---|
| `Math28/Crouzeix.lean` | `CompleteCrouzeix.Main` (`OAI.CompleteCrouzeix.main`, constant 2 and its sharpness, matrix coefficients); `HilbertPolynomialBound` (scalar `m = 1` reading of `OAI.CrouzeixHilbert.hilbert`) | `norm_aeval_le_of_numRange_subset` (bound over any `Σ ⊇ W(A)`); `sirk_error_bound_of_hilbertPolynomialBound` (`BookProof.ChapterH4.sirk_error_bound` with its Crouzeix inputs discharged: error `≤ 4·D·‖v‖`) | closure clean, Mathlib + OAI only. Constant 2 is Crouzeix's conjecture (published constant `1+√2`) |
| `Math28/ZetaSevenEighths.lean` | `RiemannZetaSevenEighths`, `DirichletSevenEighths` (`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`) | `riemannZetaSevenEighths_of_dirichlet`; `re_mem_strip_of_zeta_eq_zero` (non-trivial zeros in `1/8 ≤ Re s ≤ 7/8`); `zeroFreeRightHalfPlane_iff_band` (RandomMap's RH proposition ⇔ zero-freeness of `1/2 < Re s ≤ 7/8`) | ⚠ imports `PrimeNumberTheoremAnd`, `RellichKondrachov`, which are not in the snapshot; far beyond known zero-free regions |
| `Math28/Correlations.lean` | `TwoPointCorrelations.LiouvilleLogSaving`, `.BinaryCorrectedElliott`, `.AffineCorrectedElliott` (`OAI.OrdinaryTwoPointCorrelations.*`); `OrdinaryCorrelations.BinaryCorrectedElliott` | `liouville_two_point_cesaro` (two-point Chowla-type Cesàro decay for `λ`) | ⚠ first three import `PrimeNumberTheoremAnd`/`StrongPNT`, which are not in the snapshot; the last is clean (628 modules) |
| `Math28/ErdosProgressions.lean` | `Erdos3.QuantitativeDensityTheorem`, `Erdos3.ReciprocalProgressionTheorem`, `Erdos3.ManuscriptMainTheorems` (`OAI.Erdos3.manuscript_main_theorems`) | `summable_dyadic_of_densityBound`; `reciprocalProgressionTheorem_of_quantitativeDensity`; `manuscriptMainTheorems_iff` (the source's main theorem ⇔ its density half) | closure clean (4,774 modules). The reciprocal statement is Erdős' conjecture on arithmetic progressions |

## Transcription notes

* Definitions are copied from `math/` with the names re-checked on v4.28.0. The one deviation is
  `TwoPointCorrelations.liouville`: it is defined as `(-1)^Ω(n)` (with value 0 at 0), because
  the pinned Mathlib has no `ArithmeticFunction.liouville`.
* `ZetaSevenEighths.ZeroFreeRightHalfPlane` repeats `RandomMap2RH.ZeroFreeRightHalfPlane`
  rather than importing it, because that module's import chain does not build on this pin.
* `HilbertPolynomialBound` is the `m = 1` case of a matrix-coefficient statement on `H ⊗ ℂᵐ`.
  The identification `H ⊗ ℂ¹ ≅ H` is a reading of the source, not a formal derivation.

## Not included

* NS (`SheetFlows`, `BalancedTransport`, `VelocityDetection`), Laughlin (`thm_fock`,
  `uniform_fock_gap`), Fourier and BoxTransport: their statements depend on large bespoke
  model files (state spaces, RAM/transport models) that would have to be transcribed
  wholesale. None matches an open hypothesis of the NS/QYM work order (`nsKoopman_esa_…`, the
  QYM form gap), so they were left out.
* Hecke and Siegel-zero results: they depend on the same missing packages as `DirichletL`.
* An earlier attempt to compile all of `math/` on v4.28.0 (a full copy with a compatibility shim)
  was abandoned and removed.
