import BookProof.ChapterMinMaxSpectrum.Part1
import BookProof.ChapterMinMaxSpectrum.Part2

/-!
# Chapter MinMaxSpectrum — every Courant–Fischer level is a point of the spectrum

`BookProof.ChapterSirkRitzMinMax` built the Courant–Fischer ladder

  `minmaxLevel T k = inf { sup_{x ∈ S, ‖x‖ = 1} ⟪x, Tx⟫ : dim S = k + 1 }`

and proved that the Galerkin (Rayleigh–Ritz) levels of the truncations converge to it,
hence that the **computed gap** converges to `minmaxLevel T 1 − minmaxLevel T 0`.  Its
recorded honest boundary was that only the bottom rung `k = 0` had been identified with
a *spectral* quantity (`minmaxLevel_zero_eq_sInf_spectrum`); nothing was claimed about
the levels `k ≥ 1`.

This chapter removes that boundary in the form that the numerics needs: **every** level
of the ladder is a point of the spectrum,

  `minmaxLevel_mem_spectrum : minmaxLevel T k ∈ spectrum ℝ T`,

for a bounded self-adjoint `T` on a complex Hilbert space (with the ladder defined, i.e.
with subspaces of dimension `k + 1` available).  Consequently the limit of the computed
Galerkin levels is a spectral value and the computed gap converges to the difference of
two spectral values — the statement `CONSOLIDATED_PLAN.md` §12.2 (Gap 2, QYM) asks for.

## The proof

The classical argument, run through the continuous functional calculus rather than a
Borel spectral measure.  If `a = minmaxLevel T k` were **not** in the spectrum, then —
the spectrum being closed — some `ε > 0` separates it: every spectral point is `≤ a − ε`
or `≥ a + ε`.  The continuous cutoff

  `cutoff a ε t = min 1 (max 0 ((a + ε − t) / (2ε)))`

is therefore `{0, 1}`-valued on the spectrum, so `P = cfc (cutoff a ε) T` is an
orthogonal projection commuting with `T`, `T ≤ a − ε` on its range and `T ≥ a + ε` on its
kernel (`rayleighVal_le_of_proj_fixed`, `le_rayleighVal_of_proj_zero`, both obtained from
the order-preservation of the functional calculus, `cfc_le_iff`).  Then:

* if the range of `P` contains a `(k+1)`-dimensional subspace, that subspace is a
  competitor with `rayleighSup ≤ a − ε`, so `a ≤ a − ε` — impossible;
* otherwise `P` is non-injective on every `(k+1)`-dimensional subspace `S`, so `S` meets
  the kernel of `P` in a unit vector and `rayleighSup T S ≥ a + ε` for **every**
  competitor, whence `a ≥ a + ε` — impossible.

## Deliverables

* `cutoff`, `cutoff_eq_one`, `cutoff_eq_zero` — the continuous `{0,1}`-valued cutoff.
* `re_inner_mono_of_le` — the operator order dominates the Rayleigh quotients.
* `rayleighVal_le_of_proj_fixed`, `le_rayleighVal_of_proj_fixed` — the two spectral
  half-space bounds, for a general `{0,1}`-valued continuous symbol.
* `minmaxLevel_mem_spectrum` — **headline**: `minmaxLevel T k ∈ spectrum ℝ T`;
  `sInf_spectrum_mem_spectrum` — in particular the bottom of the spectrum is attained.
* `galerkin_minmaxLevel_tendsto_spectrum` — the Galerkin min–max levels converge to a
  point of the spectrum; `galerkin_gap_tendsto_spectrum_sub` — the computed gap converges
  to the difference of two points of the spectrum.
* `rayleighVal_le_of_mem_range`, `exists_cfc_ne_zero`, `inner_range_eq_zero` — the
  spectral-subspace toolkit: the half-space bound on the range of `cfc p T` for an
  arbitrary continuous symbol, the non-triviality of a spectral subspace at a spectral
  point, and the orthogonality of the subspaces of disjoint symbols.
* `notMem_spectrum_of_mem_minmaxGap` / `spectrum_inter_minmaxGap_eq_empty` —
  **the computed gap is a gap of the spectrum**: no spectral point lies strictly between
  `minmaxLevel T 0` and `minmaxLevel T 1`.
* `exists_eigenvector_of_minmaxGap` — **a positive min–max gap makes the ground level an
  eigenvalue**: there is a non-zero `x` with `T x = minmaxLevel T 0 • x`.

## Honest boundary

The operator is **bounded** throughout (the unbounded case is reached through the
resolvent, not directly).  For a general level the statement is that it *lies in the
spectrum*; it is not claimed to be an eigenvalue — at or above the essential spectrum a
level is typically only a spectral point, and no essential-spectrum theory is developed
here.  What *is* proved is the eigenvalue statement for the ground level of a **positive**
min–max gap, which is the case the numerics is about.  Nothing here says that a computed
Galerkin gap is positive for the exact operator: the computed levels are upper bounds, and
that direction is the stability question of `ChapterSirkRitzPerturbation`.
-/
