import Mathlib

/-!
# Unconditional sums of orthogonal families

Elementary Hilbert-space facts that the infinite-dimensional versions of Mackey's and
Wigner's theorems need, and which are stated here once for both.

* `norm_sum_sq_of_orthogonal` — Pythagoras over a `Finset`;
* `summable_of_orthogonal_of_summable_norm_sq` — a pairwise orthogonal family whose squared
  norms are summable is (unconditionally) summable in a complete space;
* `hasSum_norm_sq_of_hasSum` — Parseval: if an orthogonal family sums to `ψ` then its
  squared norms sum to `‖ψ‖²`;
* `hasSum_smul_of_hasSum_norm_sq` — the converse of Bessel's inequality: a vector whose
  Fourier coefficients with respect to an orthonormal family saturate Bessel's inequality is
  the sum of its Fourier series.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace

namespace BookProof.ChapterOrthogonalSums

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Pythagoras over a `Finset`. -/
theorem norm_sum_sq_of_orthogonal {ι : Type*} (t : Finset ι) {v : ι → E}
    (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) :
    ‖∑ x ∈ t, v x‖ ^ 2 = ∑ x ∈ t, ‖v x‖ ^ 2 := by
  have hip : ⟪∑ x ∈ t, v x, ∑ x ∈ t, v x⟫_ℂ = ∑ x ∈ t, ⟪v x, v x⟫_ℂ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [inner_sum, Finset.sum_eq_single x]
    · intro y _ hy
      exact horth x y (Ne.symm hy)
    · intro h
      exact absurd hx h
  have h2 := congrArg (RCLike.re (K := ℂ)) hip
  rw [map_sum] at h2
  simp only [inner_self_eq_norm_sq] at h2
  exact h2

/-- A pairwise orthogonal family with summable squared norms is summable. -/
theorem summable_of_orthogonal_of_summable_norm_sq [CompleteSpace E] {ι : Type*} {v : ι → E}
    (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) (hsum : Summable fun x => ‖v x‖ ^ 2) :
    Summable v := by
  rw [summable_iff_vanishing]
  intro e he
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 he
  have hε2 : 0 < ε ^ 2 := by positivity
  obtain ⟨t₀, ht₀⟩ :=
    (summable_iff_vanishing.1 hsum) (Metric.ball 0 (ε ^ 2)) (Metric.ball_mem_nhds 0 hε2)
  refine ⟨t₀, fun t ht => hball ?_⟩
  have hnn : (0 : ℝ) ≤ ∑ x ∈ t, ‖v x‖ ^ 2 := Finset.sum_nonneg fun x _ => by positivity
  have h1 : ∑ x ∈ t, ‖v x‖ ^ 2 < ε ^ 2 := by
    have h := ht₀ t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h
    exact h
  have h2 : ‖∑ x ∈ t, v x‖ ^ 2 < ε ^ 2 := by
    rw [norm_sum_sq_of_orthogonal _ horth]
    exact h1
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [norm_nonneg (∑ x ∈ t, v x), hε]

/-- **Parseval** for an orthogonal family. -/
theorem hasSum_norm_sq_of_hasSum {ι : Type*} {v : ι → E} {psi : E} (h : HasSum v psi)
    (horth : ∀ x y, x ≠ y → ⟪v x, v y⟫_ℂ = 0) :
    HasSum (fun x => ‖v x‖ ^ 2) (‖psi‖ ^ 2) := by
  have hterm : ∀ x, ⟪psi, v x⟫_ℂ = ((‖v x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have hx : HasSum (fun y => ⟪v x, v y⟫_ℂ) ⟪v x, psi⟫_ℂ := h.mapL (innerSL ℂ (v x))
    have hx' : HasSum (fun y => ⟪v x, v y⟫_ℂ) ⟪v x, v x⟫_ℂ := by
      refine hasSum_single x ?_
      intro y hy
      exact horth x y (Ne.symm hy)
    have hxx : ⟪v x, psi⟫_ℂ = ⟪v x, v x⟫_ℂ := hx.unique hx'
    rw [← inner_conj_symm, hxx, inner_self_eq_norm_sq_to_K]
    simp
  have h1 : HasSum (fun x => ⟪psi, v x⟫_ℂ) ⟪psi, psi⟫_ℂ := h.mapL (innerSL ℂ psi)
  rw [inner_self_eq_norm_sq_to_K] at h1
  simp only [hterm] at h1
  have h2 := h1.mapL Complex.reCLM
  simpa [← Complex.ofReal_pow] using h2

/-- **Saturated Bessel inequality.**  If the squared moduli of the Fourier coefficients of
`y` with respect to an orthonormal family sum to `‖y‖²`, then `y` is the sum of its Fourier
series; in particular `y` lies in the closed span of the family. -/
theorem hasSum_smul_of_hasSum_norm_sq [CompleteSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal ℂ v) {y : E}
    (h : HasSum (fun k => ‖⟪v k, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2)) :
    HasSum (fun k => ⟪v k, y⟫_ℂ • v k) y := by
  classical
  set c : ι → ℂ := fun k => ⟪v k, y⟫_ℂ with hc
  have hnormv : ∀ k, ‖v k‖ = 1 := fun k => hv.1 k
  have horth : ∀ i j : ι, i ≠ j → ⟪c i • v i, c j • v j⟫_ℂ = 0 := by
    intro i j hij
    rw [inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hv i j, if_neg hij]
    simp
  have hnormterm : ∀ k, ‖c k • v k‖ ^ 2 = ‖c k‖ ^ 2 := by
    intro k
    rw [norm_smul, hnormv k, mul_one]
  have hsummable : Summable fun k => c k • v k := by
    refine summable_of_orthogonal_of_summable_norm_sq horth ?_
    simpa only [hnormterm] using h.summable
  obtain ⟨y', hy'⟩ := hsummable
  -- the Fourier coefficients of `y'` are the `c k`
  have hcoeff : ∀ k, ⟪v k, y'⟫_ℂ = c k := by
    intro k
    have h1 : HasSum (fun j => ⟪v k, c j • v j⟫_ℂ) ⟪v k, y'⟫_ℂ := hy'.mapL (innerSL ℂ (v k))
    have h2 : HasSum (fun j => ⟪v k, c j • v j⟫_ℂ) (⟪v k, c k • v k⟫_ℂ) := by
      refine hasSum_single k ?_
      intro j hj
      rw [inner_smul_right, orthonormal_iff_ite.mp hv k j, if_neg (Ne.symm hj)]
      simp
    have h3 : ⟪v k, y'⟫_ℂ = ⟪v k, c k • v k⟫_ℂ := h1.unique h2
    rw [h3, inner_smul_right, orthonormal_iff_ite.mp hv k k, if_pos rfl, mul_one]
  -- `⟪y, y'⟫ = ‖y‖²`
  have hyy' : ⟪y, y'⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : HasSum (fun k => ⟪y, c k • v k⟫_ℂ) ⟪y, y'⟫_ℂ := hy'.mapL (innerSL ℂ y)
    have hterm : ∀ k, ⟪y, c k • v k⟫_ℂ = ((‖c k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      have h4 : ⟪y, v k⟫_ℂ = (starRingEnd ℂ) (c k) := by rw [hc, inner_conj_symm]
      rw [inner_smul_right, h4, Complex.mul_conj, Complex.sq_norm]
    simp only [hterm] at h1
    have h2 : HasSum (fun k => ((‖c k‖ ^ 2 : ℝ) : ℂ)) ((‖y‖ ^ 2 : ℝ) : ℂ) :=
      h.mapL Complex.ofRealCLM
    exact h1.unique h2
  -- `‖y'‖² = ‖y‖²`
  have hnormy' : ‖y'‖ ^ 2 = ‖y‖ ^ 2 := by
    have h1 := hasSum_norm_sq_of_hasSum hy' horth
    simp only [hnormterm] at h1
    exact h1.unique h
  -- hence `y = y'`
  have hzero : ‖y - y'‖ ^ 2 = 0 := by
    have hre : RCLike.re (((‖y‖ ^ 2 : ℝ) : ℂ)) = ‖y‖ ^ 2 := Complex.ofReal_re _
    rw [norm_sub_sq (𝕜 := ℂ), hyy', hnormy', hre]
    ring
  have : y = y' := by
    have := norm_eq_zero.1 (by nlinarith [norm_nonneg (y - y')] : ‖y - y'‖ = 0)
    exact sub_eq_zero.1 this
  rw [this]
  simp only [hcoeff]
  exact hy'

end BookProof.ChapterOrthogonalSums
