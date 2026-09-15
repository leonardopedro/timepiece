import BookProof.ChapterResolventMinMaxLadder.Part1
import BookProof.ChapterResolventMinMaxLadder.Part2

/-!
# Chapter ResolventMinMaxLadder — the Courant–Fischer ladder of an **unbounded**
# non-negative self-adjoint relation, through its resolvent

`CONSOLIDATED_PLAN.md` records, as the QG next step, "the min–max ladder through the
resolvent for the continuum spectral claim", and the recorded honest boundary of
`BookProof.ChapterSirkRitzMinMax` / `BookProof.ChapterMinMaxSpectrum` is that *the operator
is bounded throughout — the unbounded case is reached through the resolvent, not directly*.

This chapter takes that step.  Let `T` be a non-negative self-adjoint linear relation on a
complex Hilbert space `F` (the object produced by the project's Friedrichs / essential
self-adjointness chapters) and let

```text
R = (T + 1)⁻¹      (`BookProof.NonnegSquareRoot.invCLMAt`, here `res hT`)
```

be its resolvent at `1`: a **bounded**, self-adjoint, non-negative operator, to which the
whole bounded min–max machinery applies.  The ladder of `T` is compared with the ladder of
`R` read **from the top** (`maxminLevel`), through the decreasing bijection
`λ ↦ 1/(1 + λ)`.

## The analytic core

For `(y, z) ∈ T` put `x = y + z`, so that `R x = y`.  Cauchy–Schwarz for the non-negative
form `(u, v) ↦ Re⟪u, R v⟫` applied to the pair `(x, R x)` gives `‖R x‖⁴ ≤ ⟪x, Rx⟫ ⟪Rx, RRx⟫`,
which in terms of `T` is the **pointwise ladder inequality**

```text
‖y‖⁴ ≤ (‖y‖² + Re⟪y, z⟫) · Re⟪y, R y⟫,
```

i.e. for a unit vector of the domain, `Re⟪y, z⟫ ≥ 1/Re⟪y, R y⟫ − 1`.  It is the operator
form of Jensen's inequality for the convex function `λ ↦ 1/(1 + λ)`, proved with no spectral
theory at all.

## Deliverables

* `posForm_cauchy_schwarz`, `normSq_sq_le_rayleigh_mul` — Cauchy–Schwarz for a non-negative
  bounded form, and its consequence `‖Rx‖⁴ ≤ rayleighVal R x · rayleighVal R (R x)`.
* `res`, `res_mem`, `res_eq_of_mem`, `res_injective` — the resolvent at `1` as an operator
  onto the domain of `T`.
* **`normSq_sq_le_rayleigh_graph`**, `one_le_add_mul_rayleigh_of_unit`,
  `inv_sub_one_le_of_rayleigh_le` — the pointwise ladder inequality.
* `rayleighInfOn`, `maxminSet`, `maxminLevel` — the Courant–Fischer ladder of a bounded
  operator read from the top, with `maxminLevel_zero_eq_sSup_rayleighSet`.
* `graphRayleighSet`, `graphRayleighSup`, `InDomain`, `graphMinmaxSet`,
  `graphMinmaxLevel` — the ladder of the **relation** `T`, over the finite-dimensional
  subspaces of its domain; `graphRayleighSet_bddAbove` (a closed operator is bounded on a
  finite-dimensional subspace of its domain) and `graphMinmaxSet_nonempty` (the resolvent
  supplies subspaces of every dimension inside the domain).
* **`resolvent_ladder_lower`** — for every `k`,
  `1 / maxminLevel R k − 1 ≤ graphMinmaxLevel T k`: the ladder of the unbounded `T` is
  bounded below by the ladder of the bounded resolvent, read from the top.
* **`graphMinmaxLevel_zero_eq`** — at the bottom rung the inequality is an **equality**:
  `graphMinmaxLevel T 0 = 1 / maxminLevel R 0 − 1`, and
  `graphMinmaxLevel_zero_eq_sSup_spectrum` writes it with the top of the spectrum of `R`.
* `maxminLevelIn`, `minmaxLevel_neg`, `maxminLevelIn_le_maxminLevel`,
  **`galerkin_maxminLevel_tendsto`**, `galerkin_maxmin_gap_eventually_pos` and
  **`graphMinmaxLevel_zero_le_of_computed`** — the computational side: the ladder from the
  top is the ladder of `−R` from the bottom, so the Galerkin levels of the resolvent
  converge to it, a computed Ritz level is a lower bound for the true level, and therefore
  `1/(computed level) − 1` is a rigorous **upper** bound for the ground level of `T`.
* **`graphMinmax_gap_lower`** — hence a gap of the resolvent's ladder is a gap of `T`'s:
  `graphMinmaxLevel T 1 − graphMinmaxLevel T 0 ≥ 1 / maxminLevel R 1 − 1 / maxminLevel R 0`,
  and `graphMinmax_gap_pos`: it is **positive** as soon as `maxminLevel R 1 < maxminLevel R 0`.

## Honest boundary

In *this* chapter only the bottom rung of the ladder is an equality; for `k ≥ 1` what is
proved here is the inequality `1/ν_k − 1 ≤ μ_k`, which is the direction a **gap** statement
needs (a lower bound for the excited level together with the exact ground level).  The
reverse inequality for `k ≥ 1` needs spectral projections of `R`; it is proved in
`BookProof.ChapterResolventMinMaxEquality`, where the ladder becomes an equality at every
rung.  Nothing in
this chapter produces a spectral gap for any particular Hamiltonian: it converts a gap of
the resolvent's numerical ladder into a gap of the ladder of `T`.
-/
