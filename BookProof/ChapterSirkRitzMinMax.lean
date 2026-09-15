import BookProof.ChapterSirkRitzMinMax.Part1
import BookProof.ChapterSirkRitzMinMax.Part2

/-!
# Chapter SirkRitzMinMax — the higher Rayleigh–Ritz levels and the Ritz gap

`CONSOLIDATED_PLAN.md` §12.2 **Gap 2, QYM** asks for "the statement that the
Ritz/**gap** values converge to the spectrum of the selected extension as `m → ∞`".
`BookProof.ChapterSirkRitzSpectrum` settled the *lowest* Ritz value: it converges to
`sInf (spectrum ℝ A)`.  A gap statement needs the **second** level as well, and there
is no second Rayleigh quotient — the correct object is the Courant–Fischer min–max
level

  `minmaxLevel T k = inf { sup_{x ∈ S, ‖x‖ = 1} ⟪x, Tx⟫ : dim S = k + 1 }`.

This chapter introduces those levels for a bounded operator on a complex Hilbert
space, and proves that the **Galerkin (Rayleigh–Ritz) min–max levels of the
truncations converge to them**, hence that the computed gap converges to the
min–max gap.

## Deliverables

* `rayleighVal`, `rayleighSetOn`, `rayleighSup` — the Rayleigh quotient, its range
  over the unit sphere of a subspace, and the supremum, with the basic bounds
  (`rayleighSup_le_norm`, `rayleighSup_mono`).
* `minmaxLevel` / `minmaxLevelIn` — the Courant–Fischer levels of `T`, and the
  levels computed inside a fixed subspace `W` (the truncation the solver sees).
* `minmaxLevel_le_minmaxLevelIn` — the Ritz levels are always **upper** bounds
  (the variational principle in the direction the algorithm can certify).
* `minmaxLevel_mono` — the levels increase with `k`.
* `minmaxLevel_zero_eq_rayleighInf` and `minmaxLevel_zero_eq_sInf_spectrum` — the
  level `k = 0` is the bottom of the numerical range, hence the bottom of the
  spectrum: this chapter's ladder starts exactly where `ChapterSirkRitzSpectrum`
  stopped.
* `exists_galerkin_approx_subspace` — the approximation engine: any `(k+1)`-dimensional
  subspace can be pushed into a large enough Galerkin subspace with an arbitrarily
  small increase of its Rayleigh supremum.
* `galerkin_minmaxLevel_tendsto` — **headline**: for every `k`, the Galerkin min–max
  levels converge to `minmaxLevel T k`.
* `galerkin_gap_tendsto` — the computed **gap** `Λ₁(m) − Λ₀(m)` converges to
  `minmaxLevel T 1 − minmaxLevel T 0`, and `galerkin_gap_eventually_pos`: a positive
  min–max gap is eventually seen by the truncations.

## Honest boundary

The min–max levels are spectral quantities only below the essential spectrum;
nothing here claims that `minmaxLevel T k` is an eigenvalue for `k ≥ 1` (for
`k = 0` the identification with `sInf (spectrum ℝ T)` *is* proved).  The operator is
bounded throughout — the unbounded case is reached through the resolvent, not
directly.
-/
