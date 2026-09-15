import Mathlib
import BookProof.ChapterMinMaxSpectrum
import BookProof.ChapterNonnegResolvent
import BookProof.ChapterResolventMinMaxLadder.Part1

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

noncomputable section

namespace BookProof.ResolventLadder

open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open BookProof.NonnegResolvent BookProof.PositiveSquareRoot
open BookProof.NonnegSquareRoot BookProof.ClosureUniqueness
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {T : Submodule ℂ (F × F)}
/-! ## 6. The ladder inequality -/

/-- **The ladder of `T` is bounded below by the ladder of its resolvent**, on every
competitor subspace. -/
theorem le_graphRayleighSup (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {S : Submodule ℂ F} {k : ℕ}
    (hrank : Module.finrank ℂ S = k + 1) (hdom : InDomain T S) :
    1 / maxminLevel (res hT) k - 1 ≤ graphRayleighSup T S := by
  have hfd : FiniteDimensional ℂ S := .of_finrank_pos (by rw [hrank]; omega)
  have hbdd := graphRayleighSet_bddAbove hsv hdom
  have hsupnn := graphRayleighSup_nonneg hT S
  rcases le_or_gt (maxminLevel (res hT) k) 0 with hν | hν
  · have h1 : 1 / maxminLevel (res hT) k ≤ 0 := by
      rcases eq_or_lt_of_le hν with h | h
      · rw [h]; simp
      · exact (one_div_neg.mpr h).le
    linarith
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ν := maxminLevel (res hT) k with hνdef
    have hε : 0 < δ * ν ^ 2 := by positivity
    obtain ⟨y, hyS, hy1, hlt⟩ := exists_unit_rayleigh_lt (res hT) hrank hε
    obtain ⟨z, hz⟩ := hdom y hyS
    have hc : 0 < ν + δ * ν ^ 2 := by nlinarith
    have hle := inv_sub_one_le_of_rayleigh_le hT hz hy1 hc hlt.le
    have hmem : (inner ℂ y z : ℂ).re ∈ graphRayleighSet T S := ⟨y, z, hz, hyS, hy1, rfl⟩
    have hsup : (inner ℂ y z : ℂ).re ≤ graphRayleighSup T S := le_csSup hbdd hmem
    have harith : 1 / ν ≤ 1 / (ν + δ * ν ^ 2) + δ := by
      rw [div_add' _ _ _ (ne_of_gt hc), div_le_div_iff₀ hν hc]
      nlinarith
    linarith

/-- **The ladder inequality**: for every `k`,
`1 / maxminLevel R k − 1 ≤ graphMinmaxLevel T k`. -/
theorem resolvent_ladder_lower (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (k : ℕ)
    (hne : (graphMinmaxSet T k).Nonempty) :
    1 / maxminLevel (res hT) k - 1 ≤ graphMinmaxLevel T k := by
  refine le_csInf hne ?_
  rintro t ⟨S, hrank, hdom, rfl⟩
  exact le_graphRayleighSup hT hsv hrank hdom

/-! ## 7. The bottom rung: an equality -/

theorem maxminLevel_zero_pos [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) : 0 < maxminLevel (res hT) 0 := by
  obtain ⟨x0, hx0⟩ := exists_ne (0 : F)
  set x : F := ‖x0‖⁻¹ • x0 with hxdef
  have hx1 : ‖x‖ = 1 := by
    rw [hxdef, norm_smul]
    simp [norm_ne_zero_iff.mpr hx0]
  have hxne : x ≠ 0 := by
    intro h
    rw [h] at hx1
    simp at hx1
  have hpos : 0 < rayleighVal (res hT) x := by
    rcases eq_or_lt_of_le (res_re_inner_nonneg hT x) with h | h
    · exfalso
      have hmain := normSq_sq_le_rayleigh_mul (res_isSelfAdjoint hT) (res_re_inner_nonneg hT) x
      rw [← h, zero_mul] at hmain
      have hzero : res hT x = 0 := by
        have h4 : ‖res hT x‖ ^ 4 = 0 := le_antisymm hmain (by positivity)
        exact norm_eq_zero.mp ((pow_eq_zero_iff (n := 4) (by norm_num)).mp h4)
      exact hxne (res_injective hT hsv (by rw [hzero, map_zero] : res hT x = res hT 0))
    · exact h
  have hle : rayleighInfOn (res hT) (Submodule.span ℂ {x}) ≤ maxminLevel (res hT) 0 :=
    rayleighInfOn_le_maxminLevel (res hT) (by simpa using finrank_span_singleton hxne)
  rw [rayleighInfOn_span_singleton (res hT) hx1] at hle
  linarith

/-- **The bottom rung of the ladder is exactly the transformed top of the resolvent's
ladder.** -/
theorem graphMinmaxLevel_zero_eq [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) :
    graphMinmaxLevel T 0 = 1 / maxminLevel (res hT) 0 - 1 := by
  obtain ⟨x0, hx0⟩ := exists_ne (0 : F)
  have hne : (graphMinmaxSet T 0).Nonempty :=
    graphMinmaxSet_nonempty hT hsv (W := Submodule.span ℂ {x0})
      (by simpa using finrank_span_singleton hx0)
  refine le_antisymm ?_ (resolvent_ladder_lower hT hsv 0 hne)
  set ν := maxminLevel (res hT) 0 with hνdef
  have hνpos : 0 < ν := maxminLevel_zero_pos hT hsv
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- pick a unit vector nearly maximizing the resolvent's Rayleigh quotient
  set ε : ℝ := min (ν / 2) (δ * ν ^ 2 / 2) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
  have hεν : ε ≤ ν / 2 := min_le_left _ _
  have hεδ : ε ≤ δ * ν ^ 2 / 2 := min_le_right _ _
  have hsup : ν = sSup (rayleighSet (res hT)) := maxminLevel_zero_eq_sSup_rayleighSet (res hT)
  obtain ⟨t, ht, htlt⟩ : ∃ t ∈ rayleighSet (res hT), ν - ε < t := by
    refine exists_lt_of_lt_csSup (rayleighSet_nonempty (res hT)) ?_
    rw [← hsup]
    linarith
  obtain ⟨x, hx1, rfl⟩ := ht
  set A : ℝ := rayleighVal (res hT) x with hA
  have hAle : A ≤ ν := by
    rw [hsup]
    exact le_csSup (rayleighSet_bddAbove (res hT)) ⟨x, hx1, rfl⟩
  have hApos : 0 < A := by
    have : ν - ε < A := htlt
    linarith
  set y : F := res hT x with hy
  have hAle2 : A ≤ ‖y‖ := by
    calc A = (inner ℂ x y : ℂ).re := rfl
      _ ≤ ‖(inner ℂ x y : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ = ‖y‖ := by rw [hx1, one_mul]
  have hypos : 0 < ‖y‖ := lt_of_lt_of_le hApos hAle2
  have hyne : y ≠ 0 := norm_pos_iff.mp hypos
  -- the line through `y` is a competitor
  have hmemT : (y, x - y) ∈ T := res_mem hT x
  have hdom : InDomain T (Submodule.span ℂ {y}) := by
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨c • (x - y), T.smul_mem c hmemT⟩
  have hrank : Module.finrank ℂ (Submodule.span ℂ {y}) = 0 + 1 := by
    simpa using finrank_span_singleton hyne
  -- every Rayleigh value on that line equals `A/‖y‖² − 1`
  have hval : ∀ t ∈ graphRayleighSet T (Submodule.span ℂ {y}), t = A / ‖y‖ ^ 2 - 1 := by
    rintro t ⟨u, w, huw, huS, hu1, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp huS
    have hw : w = c • (x - y) := graph_unique hsv huw (T.smul_mem c hmemT)
    have hc2 : ‖c‖ ^ 2 * ‖y‖ ^ 2 = 1 := by
      have : ‖c • y‖ = 1 := hu1
      rw [norm_smul] at this
      nlinarith [norm_nonneg c, norm_nonneg y]
    have hbase : (inner ℂ y (x - y) : ℂ).re = A - ‖y‖ ^ 2 := by
      rw [inner_sub_right, Complex.sub_re, inner_self_eq_norm_sq_to_K]
      have hyx : (inner ℂ y x : ℂ).re = A := by
        rw [hA, rayleighVal, ← hy, ← inner_conj_symm, Complex.conj_re]
      rw [hyx]
      norm_cast
    have hcc : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have hexp : (inner ℂ (c • y) w : ℂ).re = ‖c‖ ^ 2 * (inner ℂ y (x - y) : ℂ).re := by
      rw [hw, inner_smul_left, inner_smul_right, ← mul_assoc, hcc, Complex.re_ofReal_mul]
    rw [hexp, hbase]
    field_simp
    nlinarith [hc2]
  have hbdd : BddAbove (graphRayleighSet T (Submodule.span ℂ {y})) := by
    have : FiniteDimensional ℂ (Submodule.span ℂ {y}) := .of_finrank_pos (by rw [hrank]; omega)
    exact graphRayleighSet_bddAbove hsv hdom
  have hsetne : (graphRayleighSet T (Submodule.span ℂ {y})).Nonempty :=
    graphRayleighSet_nonempty (by rw [hrank]; omega) hdom
  have hsupval : graphRayleighSup T (Submodule.span ℂ {y}) ≤ A / ‖y‖ ^ 2 - 1 :=
    csSup_le hsetne fun t ht => le_of_eq (hval t ht)
  have hlow : graphMinmaxLevel T 0 ≤ graphRayleighSup T (Submodule.span ℂ {y}) :=
    csInf_le (graphMinmaxSet_bddBelow hT 0) ⟨_, hrank, hdom, rfl⟩
  -- arithmetic: `A/‖y‖² ≤ 1/A ≤ 1/(ν − ε) ≤ 1/ν + δ`
  have h1 : A / ‖y‖ ^ 2 ≤ 1 / A := by
    rw [div_le_div_iff₀ (by positivity) hApos]
    nlinarith [hAle2, hApos]
  have hAeq : (inner ℂ x y : ℂ).re = A := rfl
  have h2 : 1 / A ≤ 1 / (ν - ε) := by
    have hνε : 0 < ν - ε := by linarith
    exact one_div_le_one_div_of_le hνε (by rw [← hAeq]; linarith [htlt])
  have h3 : 1 / (ν - ε) ≤ 1 / ν + δ := by
    have hνε : 0 < ν - ε := by linarith
    rw [div_add' _ _ _ (ne_of_gt hνpos), div_le_div_iff₀ hνε hνpos]
    nlinarith
  linarith

/-- **The bottom rung, spectrally**: the lowest min–max level of `T` is determined by the
**top of the spectrum of its resolvent**. -/
theorem graphMinmaxLevel_zero_eq_sSup_spectrum [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) :
    graphMinmaxLevel T 0 = 1 / sSup (spectrum ℝ (res hT)) - 1 := by
  rw [graphMinmaxLevel_zero_eq hT hsv, maxminLevel_zero_eq_sSup_rayleighSet,
    sSup_rayleighSet_eq_sSup_spectrum (res hT) (res_isSelfAdjoint hT)]

/-! ## 8. The gap -/

/-- **A gap of the resolvent's ladder is a gap of the ladder of `T`.** -/
theorem graphMinmax_gap_lower [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0)
    (hne : (graphMinmaxSet T 1).Nonempty) :
    1 / maxminLevel (res hT) 1 - 1 / maxminLevel (res hT) 0
      ≤ graphMinmaxLevel T 1 - graphMinmaxLevel T 0 := by
  have h1 := resolvent_ladder_lower hT hsv 1 hne
  have h0 := graphMinmaxLevel_zero_eq hT hsv
  linarith

/-- **A strict gap of the resolvent's ladder gives a strictly positive gap for `T`.** -/
theorem graphMinmax_gap_pos [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0)
    (hne : (graphMinmaxSet T 1).Nonempty)
    (hgap : maxminLevel (res hT) 1 < maxminLevel (res hT) 0)
    (hpos : 0 < maxminLevel (res hT) 1) :
    0 < graphMinmaxLevel T 1 - graphMinmaxLevel T 0 := by
  have hlow := graphMinmax_gap_lower hT hsv hne
  have hstrict : 1 / maxminLevel (res hT) 0 < 1 / maxminLevel (res hT) 1 :=
    one_div_lt_one_div_of_lt hpos hgap
  linarith

/-! ## 9. What the numerics computes: the Galerkin levels of the resolvent

The shift-invert schemes of the project diagonalise finite compressions of the **resolvent**,
not of the Hamiltonian.  This section transports the Galerkin convergence theorem of
`ChapterSirkRitzMinMax` to the ladder read from the top (by applying it to `−R`), and turns a
computed Ritz level into a rigorous upper bound for the ground level of the unbounded
operator. -/

/-- The levels of `R` from the top, computed only inside a fixed subspace `W`: the Ritz
levels the solver produces from the truncation to `W`. -/
def maxminSetIn (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F, S ≤ W ∧ Module.finrank ℂ S = k + 1 ∧ t = rayleighInfOn R S}

/-- The `k`-th Rayleigh–Ritz level of the truncation of `R` to `W`, counted from the top. -/
def maxminLevelIn (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : ℝ := sSup (maxminSetIn R W k)

omit [CompleteSpace F] in
theorem rayleighVal_neg (R : F →L[ℂ] F) (x : F) : rayleighVal (-R) x = -rayleighVal R x := by
  simp [rayleighVal]

omit [CompleteSpace F] in
theorem rayleighSetOn_neg (R : F →L[ℂ] F) (S : Submodule ℂ F) :
    rayleighSetOn (-R) S = -rayleighSetOn R S := by
  ext t
  rw [Set.mem_neg]
  constructor
  · rintro ⟨x, hx, hx1, rfl⟩
    exact ⟨x, hx, hx1, by rw [rayleighVal_neg, neg_neg]⟩
  · rintro ⟨x, hx, hx1, hval⟩
    exact ⟨x, hx, hx1, by rw [rayleighVal_neg, ← hval, neg_neg]⟩

omit [CompleteSpace F] in
theorem rayleighSup_neg (R : F →L[ℂ] F) (S : Submodule ℂ F) :
    rayleighSup (-R) S = -rayleighInfOn R S := by
  rw [rayleighSup, rayleighSetOn_neg, Real.sSup_neg, rayleighInfOn]

omit [CompleteSpace F] in
theorem minmaxSet_neg (R : F →L[ℂ] F) (k : ℕ) : minmaxSet (-R) k = -maxminSet R k := by
  ext t
  rw [Set.mem_neg]
  constructor
  · rintro ⟨S, hrank, rfl⟩
    exact ⟨S, hrank, by rw [rayleighSup_neg, neg_neg]⟩
  · rintro ⟨S, hrank, hval⟩
    exact ⟨S, hrank, by rw [rayleighSup_neg, ← hval, neg_neg]⟩

omit [CompleteSpace F] in
/-- The ladder from the top is the ladder of `−R` from the bottom. -/
theorem minmaxLevel_neg (R : F →L[ℂ] F) (k : ℕ) :
    minmaxLevel (-R) k = -maxminLevel R k := by
  rw [minmaxLevel, minmaxSet_neg, Real.sInf_neg, maxminLevel]

omit [CompleteSpace F] in
theorem minmaxSetIn_neg (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    minmaxSetIn (-R) W k = -maxminSetIn R W k := by
  ext t
  rw [Set.mem_neg]
  constructor
  · rintro ⟨S, hle, hrank, rfl⟩
    exact ⟨S, hle, hrank, by rw [rayleighSup_neg, neg_neg]⟩
  · rintro ⟨S, hle, hrank, hval⟩
    exact ⟨S, hle, hrank, by rw [rayleighSup_neg, ← hval, neg_neg]⟩

omit [CompleteSpace F] in
theorem minmaxLevelIn_neg (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    minmaxLevelIn (-R) W k = -maxminLevelIn R W k := by
  rw [minmaxLevelIn, minmaxSetIn_neg, Real.sInf_neg, maxminLevelIn]

omit [CompleteSpace F] in
/-- **The variational principle for the ladder from the top**: a computed Ritz level is a
**lower** bound for the true level. -/
theorem maxminLevelIn_le_maxminLevel (R : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (maxminSetIn R W k).Nonempty) : maxminLevelIn R W k ≤ maxminLevel R k := by
  have hne' : (minmaxSetIn (-R) W k).Nonempty := by
    rw [minmaxSetIn_neg]
    obtain ⟨t, ht⟩ := hne
    exact ⟨-t, by rwa [Set.mem_neg, neg_neg]⟩
  have h := minmaxLevel_le_minmaxLevelIn (-R) W k hne'
  rw [minmaxLevel_neg, minmaxLevelIn_neg] at h
  linarith

omit [CompleteSpace F] in
/-- **The Galerkin levels of the resolvent converge to its Courant–Fischer levels from the
top.** -/
theorem galerkin_maxminLevel_tendsto (R : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) :
    Tendsto (fun m : ℕ => maxminLevelIn R (galerkinSpan b m) k) atTop
      (nhds (maxminLevel R k)) := by
  have h := galerkin_minmaxLevel_tendsto (-R) b k
  simp only [minmaxLevel_neg, minmaxLevelIn_neg] at h
  simpa using h.neg

omit [CompleteSpace F] in
/-- **A gap of the resolvent's ladder is eventually seen by the truncations.** -/
theorem galerkin_maxmin_gap_eventually_pos (R : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    (hgap : maxminLevel R 1 < maxminLevel R 0) :
    ∀ᶠ m : ℕ in atTop, 0 < maxminLevelIn R (galerkinSpan b m) 0
      - maxminLevelIn R (galerkinSpan b m) 1 :=
  (((galerkin_maxminLevel_tendsto R b 0).sub
    (galerkin_maxminLevel_tendsto R b 1)).eventually_const_lt (by linarith))

/-- **A computed Ritz level of the resolvent bounds the ground level of the unbounded
operator.**  Whatever finite subspace the solver retains, the level it computes there is a
lower bound for the top of the resolvent's ladder, hence `1/(computed) − 1` is a rigorous
**upper** bound for the lowest min–max level of `T`. -/
theorem graphMinmaxLevel_zero_le_of_computed [Nontrivial F] (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {W : Submodule ℂ F}
    (hne : (maxminSetIn (res hT) W 0).Nonempty)
    (hpos : 0 < maxminLevelIn (res hT) W 0) :
    graphMinmaxLevel T 0 ≤ 1 / maxminLevelIn (res hT) W 0 - 1 := by
  have hle := maxminLevelIn_le_maxminLevel (res hT) W 0 hne
  have hinv : 1 / maxminLevel (res hT) 0 ≤ 1 / maxminLevelIn (res hT) W 0 :=
    one_div_le_one_div_of_le hpos hle
  rw [graphMinmaxLevel_zero_eq hT hsv]
  linarith

end BookProof.ResolventLadder

end
