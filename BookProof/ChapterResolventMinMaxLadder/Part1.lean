import Mathlib
import BookProof.ChapterMinMaxSpectrum
import BookProof.ChapterNonnegResolvent

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

/-! ## 1. Cauchy–Schwarz for a non-negative bounded form -/

/-- A non-negative real quadratic polynomial has a non-positive discriminant. -/
theorem sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C) : B ^ 2 ≤ A * C := by
  have hA : 0 ≤ A := by simpa using h 0
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · -- `C = 0`: then `B = 0`.
    have hB : B = 0 := by
      by_contra hB
      have hlin : ∀ t : ℝ, 0 ≤ A + 2 * t * B := by
        intro t
        have := h t
        rw [← hC0] at this
        simpa using this
      have hval : 2 * (-(A + 1) / (2 * B)) * B = -(A + 1) := by field_simp
      have hkey := hlin (-(A + 1) / (2 * B))
      rw [hval] at hkey
      linarith
    rw [hB, ← hC0]
    simp
  · have hkey := h (-B / C)
    have hexp : A + 2 * (-B / C) * B + (-B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp
      ring
    rw [hexp] at hkey
    have hd : B ^ 2 / C ≤ A := by linarith
    calc B ^ 2 = B ^ 2 / C * C := by field_simp
      _ ≤ A * C := mul_le_mul_of_nonneg_right hd hCpos.le

/-- For a self-adjoint operator the real part of the form is symmetric. -/
theorem re_inner_symm_of_selfAdjoint {R : F →L[ℂ] F} (hsa : IsSelfAdjoint R) (x y : F) :
    (inner ℂ x (R y) : ℂ).re = (inner ℂ y (R x) : ℂ).re := by
  have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) y x
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← h, ← inner_conj_symm, Complex.conj_re]

/-- **Cauchy–Schwarz for the non-negative form `(u, v) ↦ Re⟪u, R v⟫`.** -/
theorem posForm_cauchy_schwarz {R : F →L[ℂ] F} (hsa : IsSelfAdjoint R)
    (hpos : ∀ x : F, 0 ≤ (inner ℂ x (R x) : ℂ).re) (x y : F) :
    ((inner ℂ x (R y) : ℂ).re) ^ 2 ≤ (inner ℂ x (R x) : ℂ).re * (inner ℂ y (R y) : ℂ).re := by
  refine sq_le_mul_of_quadratic_nonneg (hpos y) fun t => ?_
  have hsymm := re_inner_symm_of_selfAdjoint hsa x y
  have hexp : (inner ℂ (x + (t : ℂ) • y) (R (x + (t : ℂ) • y)) : ℂ).re
      = (inner ℂ x (R x) : ℂ).re + 2 * t * (inner ℂ x (R y) : ℂ).re
        + t ^ 2 * (inner ℂ y (R y) : ℂ).re := by
    rw [map_add, ContinuousLinearMap.map_smul, inner_add_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_ofReal,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [hsymm]
    ring
  have hnn := hpos (x + (t : ℂ) • y)
  rw [hexp] at hnn
  exact hnn

/-- `‖Rx‖⁴ ≤ ⟪x, Rx⟫ · ⟪Rx, R(Rx)⟫`: the Cauchy–Schwarz inequality at the pair
`(x, R x)`. -/
theorem normSq_sq_le_rayleigh_mul {R : F →L[ℂ] F} (hsa : IsSelfAdjoint R)
    (hpos : ∀ x : F, 0 ≤ (inner ℂ x (R x) : ℂ).re) (x : F) :
    ‖R x‖ ^ 4 ≤ rayleighVal R x * rayleighVal R (R x) := by
  have hmid : (inner ℂ x (R (R x)) : ℂ).re = ‖R x‖ ^ 2 := by
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) x (R x)
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [← h, inner_self_eq_norm_sq_to_K]
    norm_cast
  have h := posForm_cauchy_schwarz hsa hpos x (R x)
  rw [hmid] at h
  calc ‖R x‖ ^ 4 = (‖R x‖ ^ 2) ^ 2 := by ring
    _ ≤ rayleighVal R x * rayleighVal R (R x) := h

/-! ## 2. The resolvent at `1` of a non-negative self-adjoint relation -/

variable {T : Submodule ℂ (F × F)}

/-- The resolvent `R = (T + 1)⁻¹` of a non-negative self-adjoint relation. -/
def res (hT : IsNonnegSelfAdjoint T) : F →L[ℂ] F := invCLMAt hT (a := 1) one_pos

theorem res_mem (hT : IsNonnegSelfAdjoint T) (h : F) : (res hT h, h - res hT h) ∈ T := by
  have := invCLMAt_mem hT (a := 1) one_pos h
  simpa [res] using this

theorem res_eq_of_mem (hT : IsNonnegSelfAdjoint T) {y z : F} (hyz : (y, z) ∈ T) :
    res hT (y + z) = y := by
  refine invCLMAt_eq_of_mem hT (a := 1) one_pos ?_
  simpa using hyz

theorem res_isSelfAdjoint (hT : IsNonnegSelfAdjoint T) : IsSelfAdjoint (res hT) :=
  isSelfAdjoint_invCLMAt hT one_pos

theorem res_re_inner_nonneg (hT : IsNonnegSelfAdjoint T) (x : F) : 0 ≤ rayleighVal (res hT) x := by
  have hre : 0 ≤ (inner ℂ (res hT x) (x - res hT x) : ℂ).re := hT.nonneg _ (res_mem hT x)
  have hsplit : (inner ℂ (res hT x) (x - res hT x) : ℂ).re
      = (inner ℂ (res hT x) x : ℂ).re - ‖res hT x‖ ^ 2 := by
    rw [inner_sub_right, Complex.sub_re, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hsymm : (inner ℂ x (res hT x) : ℂ).re = (inner ℂ (res hT x) x : ℂ).re := by
    rw [← inner_conj_symm, Complex.conj_re]
  have hnn : (0:ℝ) ≤ ‖res hT x‖ ^ 2 := sq_nonneg _
  rw [rayleighVal, hsymm]
  linarith [hsplit ▸ hre]

omit [CompleteSpace F] in
/-- Single-valuedness of the relation: an operator has at most one value at each point. -/
theorem graph_unique (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {y z z' : F}
    (h : (y, z) ∈ T) (h' : (y, z') ∈ T) : z = z' := by
  have hsub : ((0 : F), z - z') ∈ T := by
    have := T.sub_mem h h'
    simpa using this
  exact sub_eq_zero.mp (hsv _ hsub)

theorem res_injective (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) :
    Function.Injective (res hT) := by
  intro a b hab
  have h0 : res hT (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hmem := res_mem hT (a - b)
  rw [h0] at hmem
  have := hsv _ (by simpa using hmem)
  exact sub_eq_zero.1 this

/-! ## 3. The pointwise ladder inequality -/

/-- **The pointwise ladder inequality**: for `(y, z)` on the graph of `T`,
`‖y‖⁴ ≤ (‖y‖² + Re⟪y, z⟫) · Re⟪y, R y⟫`.  It is the operator form of the convexity of
`λ ↦ 1/(1 + λ)`, and it is proved by Cauchy–Schwarz for the non-negative form of `R`. -/
theorem normSq_sq_le_rayleigh_graph (hT : IsNonnegSelfAdjoint T) {y z : F} (hyz : (y, z) ∈ T) :
    ‖y‖ ^ 4 ≤ (‖y‖ ^ 2 + (inner ℂ y z : ℂ).re) * rayleighVal (res hT) y := by
  have hx : res hT (y + z) = y := res_eq_of_mem hT hyz
  have hmain := normSq_sq_le_rayleigh_mul (res_isSelfAdjoint hT) (res_re_inner_nonneg hT) (y + z)
  rw [hx] at hmain
  have hA : rayleighVal (res hT) (y + z) = ‖y‖ ^ 2 + (inner ℂ y z : ℂ).re := by
    rw [rayleighVal, hx, inner_add_left, Complex.add_re, inner_self_eq_norm_sq_to_K]
    have hzy : (inner ℂ z y : ℂ).re = (inner ℂ y z : ℂ).re := by
      rw [← inner_conj_symm, Complex.conj_re]
    rw [hzy]
    norm_cast
  rw [hA] at hmain
  exact hmain

/-- The unit-vector form: `1 ≤ (1 + Re⟪y, z⟫) · Re⟪y, R y⟫`. -/
theorem one_le_add_mul_rayleigh_of_unit (hT : IsNonnegSelfAdjoint T) {y z : F}
    (hyz : (y, z) ∈ T) (hy : ‖y‖ = 1) :
    1 ≤ (1 + (inner ℂ y z : ℂ).re) * rayleighVal (res hT) y := by
  have h := normSq_sq_le_rayleigh_graph hT hyz
  rw [hy] at h
  simpa using h

/-- If the resolvent's Rayleigh quotient at a unit vector of the domain is at most `c > 0`,
then the Rayleigh quotient of `T` there is at least `1/c − 1`. -/
theorem inv_sub_one_le_of_rayleigh_le (hT : IsNonnegSelfAdjoint T) {y z : F}
    (hyz : (y, z) ∈ T) (hy : ‖y‖ = 1) {c : ℝ} (hc : 0 < c)
    (hle : rayleighVal (res hT) y ≤ c) : 1 / c - 1 ≤ (inner ℂ y z : ℂ).re := by
  have hg : 0 ≤ (inner ℂ y z : ℂ).re := hT.nonneg _ hyz
  have h1 := one_le_add_mul_rayleigh_of_unit hT hyz hy
  have h2 : (1 + (inner ℂ y z : ℂ).re) * rayleighVal (res hT) y
      ≤ (1 + (inner ℂ y z : ℂ).re) * c :=
    mul_le_mul_of_nonneg_left hle (by linarith)
  have h3 : 1 / c ≤ 1 + (inner ℂ y z : ℂ).re := by
    rw [div_le_iff₀ hc]
    linarith
  linarith

/-! ## 4. The ladder of a bounded operator, read from the top -/

/-- The bottom of the numerical range of `R` on a subspace. -/
def rayleighInfOn (R : F →L[ℂ] F) (S : Submodule ℂ F) : ℝ := sInf (rayleighSetOn R S)

/-- The values `inf_{x ∈ S, ‖x‖ = 1} ⟪x, Rx⟫` over the `(k+1)`-dimensional subspaces. -/
def maxminSet (R : F →L[ℂ] F) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F, Module.finrank ℂ S = k + 1 ∧ t = rayleighInfOn R S}

/-- The `k`-th Courant–Fischer level of a bounded operator, **counted from the top**. -/
def maxminLevel (R : F →L[ℂ] F) (k : ℕ) : ℝ := sSup (maxminSet R k)

omit [CompleteSpace F] in
theorem rayleighSetOn_bddBelow (R : F →L[ℂ] F) (S : Submodule ℂ F) :
    BddBelow (rayleighSetOn R S) := by
  refine ⟨-‖R‖, ?_⟩
  rintro t ⟨x, -, hx1, rfl⟩
  exact neg_norm_le_rayleighVal_of_unit R hx1

omit [CompleteSpace F] in
theorem rayleighInfOn_le_norm (R : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : rayleighInfOn R S ≤ ‖R‖ := by
  obtain ⟨x, hx, hx1⟩ := exists_unit_mem S hS
  refine csInf_le_of_le (rayleighSetOn_bddBelow R S) (b := rayleighVal R x) ⟨x, hx, hx1, rfl⟩ ?_
  exact rayleighVal_le_norm_of_unit R hx1

omit [CompleteSpace F] in
theorem maxminSet_bddAbove (R : F →L[ℂ] F) (k : ℕ) : BddAbove (maxminSet R k) := by
  refine ⟨‖R‖, ?_⟩
  rintro t ⟨S, hrank, rfl⟩
  exact rayleighInfOn_le_norm R (by rw [hrank]; omega)

omit [CompleteSpace F] in
theorem rayleighInfOn_le_maxminLevel (R : F →L[ℂ] F) {S : Submodule ℂ F} {k : ℕ}
    (hrank : Module.finrank ℂ S = k + 1) : rayleighInfOn R S ≤ maxminLevel R k :=
  le_csSup (maxminSet_bddAbove R k) ⟨S, hrank, rfl⟩

omit [CompleteSpace F] in
/-- Below the level plus `ε` there is a unit vector of every competitor subspace. -/
theorem exists_unit_rayleigh_lt (R : F →L[ℂ] F) {S : Submodule ℂ F} {k : ℕ}
    (hrank : Module.finrank ℂ S = k + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, ‖x‖ = 1 ∧ rayleighVal R x < maxminLevel R k + ε := by
  have hpos : 0 < Module.finrank ℂ S := by rw [hrank]; omega
  have hne := rayleighSetOn_nonempty R hpos
  have hle := rayleighInfOn_le_maxminLevel R hrank
  have hlt : sInf (rayleighSetOn R S) < maxminLevel R k + ε := by
    have : rayleighInfOn R S = sInf (rayleighSetOn R S) := rfl
    linarith [this ▸ hle]
  obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨x, hx, hx1, rfl⟩ := ht
  exact ⟨x, hx, hx1, htlt⟩

omit [CompleteSpace F] in
theorem rayleighInfOn_span_singleton (R : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    rayleighInfOn R (Submodule.span ℂ {x}) = rayleighVal R x := by
  rw [rayleighInfOn, rayleighSetOn_span_singleton R hx1, csInf_singleton]

omit [CompleteSpace F] in
/-- The top rung of the ladder ranges over the Rayleigh quotients of the unit vectors. -/
theorem maxminSet_zero_eq_rayleighSet (R : F →L[ℂ] F) : maxminSet R 0 = rayleighSet R := by
  ext t
  constructor
  · rintro ⟨S, hrank, rfl⟩
    have hfd : FiniteDimensional ℂ S := .of_finrank_pos (by rw [hrank]; omega)
    obtain ⟨x, hx, hx1⟩ := exists_unit_mem S (by rw [hrank]; omega)
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx1
      simp at hx1
    have hspan : Submodule.span ℂ {x} = S :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (by simpa using hx))
        (by rw [finrank_span_singleton hx0, hrank])
    rw [← hspan, rayleighInfOn_span_singleton R hx1]
    exact ⟨x, hx1, rfl⟩
  · rintro ⟨x, hx1, rfl⟩
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hx1
      simp at hx1
    exact ⟨Submodule.span ℂ {x}, by simpa using finrank_span_singleton hx0,
      (rayleighInfOn_span_singleton R hx1).symm⟩

omit [CompleteSpace F] in
theorem maxminLevel_zero_eq_sSup_rayleighSet (R : F →L[ℂ] F) :
    maxminLevel R 0 = sSup (rayleighSet R) := by
  rw [maxminLevel, maxminSet_zero_eq_rayleighSet]

omit [CompleteSpace F] in
theorem rayleighSet_bddAbove (R : F →L[ℂ] F) : BddAbove (rayleighSet R) := by
  refine ⟨‖R‖, ?_⟩
  rintro t ⟨x, hx1, rfl⟩
  exact rayleighVal_le_norm_of_unit R hx1

omit [CompleteSpace F] in
theorem rayleighSet_neg (R : F →L[ℂ] F) : rayleighSet (-R) = -rayleighSet R := by
  ext t
  rw [Set.mem_neg]
  constructor
  · rintro ⟨x, hx1, rfl⟩
    refine ⟨x, hx1, ?_⟩
    simp
  · rintro ⟨x, hx1, hx⟩
    refine ⟨x, hx1, ?_⟩
    have : (inner ℂ x ((-R) x) : ℂ).re = -(inner ℂ x (R x) : ℂ).re := by simp
    rw [this, ← hx, neg_neg]

/-- **The top of the numerical range is the top of the spectrum**, the mirror image of
`sInf_spectrum_eq_rayleighInf`. -/
theorem sSup_rayleighSet_eq_sSup_spectrum [Nontrivial F] (R : F →L[ℂ] F)
    (hR : IsSelfAdjoint R) : sSup (rayleighSet R) = sSup (spectrum ℝ R) := by
  have h := sInf_spectrum_eq_rayleighInf (-R) hR.neg
  rw [← spectrum.neg_eq, rayleighInf, rayleighSet_neg, Real.sInf_neg, Real.sInf_neg] at h
  linarith

/-! ## 5. The ladder of the relation -/

/-- The Rayleigh values of `T` at the unit vectors of a subspace of its domain. -/
def graphRayleighSet (T : Submodule ℂ (F × F)) (S : Submodule ℂ F) : Set ℝ :=
  {t : ℝ | ∃ y z : F, (y, z) ∈ T ∧ y ∈ S ∧ ‖y‖ = 1 ∧ t = (inner ℂ y z : ℂ).re}

/-- The top of the numerical range of `T` on a subspace of its domain. -/
def graphRayleighSup (T : Submodule ℂ (F × F)) (S : Submodule ℂ F) : ℝ :=
  sSup (graphRayleighSet T S)

/-- A subspace inside the domain of the relation. -/
def InDomain (T : Submodule ℂ (F × F)) (S : Submodule ℂ F) : Prop := ∀ y ∈ S, ∃ z, (y, z) ∈ T

/-- The values `sup_{y ∈ S, ‖y‖ = 1} ⟪y, Ty⟫` over the `(k+1)`-dimensional subspaces of the
domain. -/
def graphMinmaxSet (T : Submodule ℂ (F × F)) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F,
    Module.finrank ℂ S = k + 1 ∧ InDomain T S ∧ t = graphRayleighSup T S}

/-- The `k`-th Courant–Fischer level of the relation `T`. -/
def graphMinmaxLevel (T : Submodule ℂ (F × F)) (k : ℕ) : ℝ := sInf (graphMinmaxSet T k)

omit [CompleteSpace F] in
theorem graphRayleighSet_nonempty {S : Submodule ℂ F} (hS : 0 < Module.finrank ℂ S)
    (hdom : InDomain T S) : (graphRayleighSet T S).Nonempty := by
  obtain ⟨y, hy, hy1⟩ := exists_unit_mem S hS
  obtain ⟨z, hz⟩ := hdom y hy
  exact ⟨_, y, z, hz, hy, hy1, rfl⟩

omit [CompleteSpace F] in
theorem graphRayleighSet_nonneg (hT : IsNonnegSelfAdjoint T) {S : Submodule ℂ F} {t : ℝ}
    (ht : t ∈ graphRayleighSet T S) : 0 ≤ t := by
  obtain ⟨y, z, hyz, -, -, rfl⟩ := ht
  exact hT.nonneg _ hyz

omit [CompleteSpace F] in
theorem graphRayleighSup_nonneg (hT : IsNonnegSelfAdjoint T) (S : Submodule ℂ F) :
    0 ≤ graphRayleighSup T S :=
  Real.sSup_nonneg fun _ ht => graphRayleighSet_nonneg hT ht

omit [CompleteSpace F] in
/-- **A closed operator is bounded on a finite-dimensional subspace of its domain**, so the
Rayleigh values there are bounded above. -/
theorem graphRayleighSet_bddAbove (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0)
    {S : Submodule ℂ F} [FiniteDimensional ℂ S] (hdom : InDomain T S) :
    BddAbove (graphRayleighSet T S) := by
  classical
  have hchoose : ∀ y : S, ∃ z : F, ((y : F), z) ∈ T := fun y => hdom (y : F) y.2
  choose f hf using hchoose
  have hadd : ∀ a b : S, f (a + b) = f a + f b := by
    intro a b
    refine graph_unique hsv (hf (a + b)) ?_
    have := T.add_mem (hf a) (hf b)
    simpa using this
  have hsmul : ∀ (c : ℂ) (a : S), f (c • a) = c • f a := by
    intro c a
    refine graph_unique hsv (hf (c • a)) ?_
    have := T.smul_mem c (hf a)
    simpa using this
  let L : S →ₗ[ℂ] F :=
    { toFun := f
      map_add' := hadd
      map_smul' := by
        intro c a
        simpa using hsmul c a }
  let Lc : S →L[ℂ] F := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖, ?_⟩
  rintro t ⟨y, z, hyz, hyS, hy1, rfl⟩
  have hz : z = f ⟨y, hyS⟩ := graph_unique hsv hyz (hf ⟨y, hyS⟩)
  have hnorm : ‖f ⟨y, hyS⟩‖ ≤ ‖Lc‖ := by
    have hb := Lc.le_opNorm ⟨y, hyS⟩
    have hy' : ‖(⟨y, hyS⟩ : S)‖ = 1 := by simpa using hy1
    rw [hy', mul_one] at hb
    simpa [Lc, L, LinearMap.toContinuousLinearMap] using hb
  calc (inner ℂ y z : ℂ).re ≤ ‖(inner ℂ y z : ℂ)‖ := Complex.re_le_norm _
    _ ≤ ‖y‖ * ‖z‖ := norm_inner_le_norm _ _
    _ = ‖z‖ := by rw [hy1, one_mul]
    _ ≤ ‖Lc‖ := by rw [hz]; exact hnorm

omit [CompleteSpace F] in
theorem graphMinmaxSet_bddBelow (hT : IsNonnegSelfAdjoint T) (k : ℕ) :
    BddBelow (graphMinmaxSet T k) := by
  refine ⟨0, ?_⟩
  rintro t ⟨S, -, -, rfl⟩
  exact graphRayleighSup_nonneg hT S

/-- The resolvent supplies subspaces of every dimension inside the domain. -/
theorem graphMinmaxSet_nonempty (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {k : ℕ} {W : Submodule ℂ F}
    (hW : Module.finrank ℂ W = k + 1) : (graphMinmaxSet T k).Nonempty := by
  classical
  set R : F →ₗ[ℂ] F := (res hT : F →ₗ[ℂ] F) with hR
  have hinj : Function.Injective R := res_injective hT hsv
  have hfd : FiniteDimensional ℂ W := .of_finrank_pos (by rw [hW]; omega)
  have hequiv : W ≃ₗ[ℂ] (W.map R) := Submodule.equivMapOfInjective R hinj W
  have hrank : Module.finrank ℂ (W.map R) = k + 1 := by
    rw [← hequiv.finrank_eq, hW]
  have hdom : InDomain T (W.map R) := by
    rintro y hy
    obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hy
    exact ⟨w - res hT w, res_mem hT w⟩
  exact ⟨_, W.map R, hrank, hdom, rfl⟩

end BookProof.ResolventLadder

end
