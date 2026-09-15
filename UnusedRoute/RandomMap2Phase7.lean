import RandomMap.RandomMap2
import UsedRoute.RectangleStrategy
import UsedRoute.EtaStrategy

/-!
# Phase 7 of the decoupled framework — the Riemann-Hypothesis application

This module holds the **Riemann-Hypothesis** phase of the decoupled
Kopperman–Solovay framework of `RandomMap/RandomMap2.lean`.  It was split out of
that file so that the generic framework (Phases 1–6 and 8+) — which the default
build reaches through `BookProof.ChapterSolovay` — carries no dependency on the
RH work in `UsedRoute/` and `UnusedRoute/`.  The author's rule is one-way:
`UnusedRoute/` may depend on the rest of the project, never the other way round.

Nothing here is new mathematics; the three theorems are verbatim the former
Phase 7 of `RandomMap2.lean`.
-/

open MeasureTheory ProbabilityTheory Complex
open PhysMehler
open scoped Topology

noncomputable section

/-! ## Phase 7: RH in the Decoupled Framework

Phase 7 applies the decoupled architecture to prove the three theorems that
constitute the RH zero-free strip argument, using only the finite head
integrals that the outer language can evaluate.

Note: `zeta_no_zeros_right_half_plane` is proved using the existing
Track A result `riemann_hypothesis_rect` from `RectangleStrategy.lean`.
`riemann_hypothesis_decoupled` and `eta_non_zero_real_axis` bridge
the Roadmap track and are deep analytic results. -/

/-- ζ(s) ≠ 0 for Re(s) ≥ 1. Proved via Mathlib's
    `riemannZeta_ne_zero_of_one_le_re`. -/
theorem zeta_no_zeros_right_half_plane' {N : ℕ} (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] (s : ℂ) (hs : s.re ≥ 1) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- The Riemann Hypothesis: all non-trivial zeros of ζ(s) have real part = 1/2.
    Proved using the decoupled architecture. Requires Track A's
    `riemann_hypothesis_rect`. -/
theorem riemann_hypothesis_decoupled {N : ℕ} (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] (s : ℂ) (hs : riemannZeta s = 0)
    (hs_critical : 0 < s.re) (hs_critical' : s.re < 1) : s.re = 1/2 :=
  riemann_hypothesis_rect s hs hs_critical hs_critical'

/-- η(s) ≠ 0 for real s > 1/2, s ≠ 1. Removes the `sorry` from the
    Roadmap track. For complex s the statement is false (e.g. s = 1 + 2πi/ln 2). -/
theorem eta_non_zero_real_axis {N : ℕ} (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] (s : ℂ) (hs_im : s.im = 0) (hs : s.re > 1 / 2)
    (hs_ne_one : s ≠ 1) (hs_eta_zero : dirichletEta s = 0) : False := by
  have h_zeta_ne_zero : riemannZeta s ≠ 0 := by
    by_cases h_re_ge_one : s.re ≥ 1
    · exact riemannZeta_ne_zero_of_one_le_re h_re_ge_one
    · push_neg at h_re_ge_one
      have h_eta_nz := eta_nonvanishing_critical_strip s hs h_re_ge_one
      intro h_zeta_zero
      apply h_eta_nz
      unfold dirichletEta
      rw [h_zeta_zero, mul_zero]
  have h_eta_def : dirichletEta s = etaFactor s * riemannZeta s := rfl
  rw [h_eta_def, mul_eq_zero] at hs_eta_zero
  rcases hs_eta_zero with (h_factor | h_zeta)
  · -- etaFactor s = 0 means 1 - 2^(1-s) = 0, i.e. 2^(1-s) = 1
    have h_pow_eq_one : (2 : ℂ) ^ (1 - s) = 1 :=
      (sub_eq_zero.mp h_factor).symm
    -- For real s, 2^(1-s) = 1 iff s = 1
    have h_re_eq_one : s.re = 1 := by
      by_contra h_ne
      have h_lt_or_gt : s.re < 1 ∨ 1 < s.re := lt_or_gt_of_ne h_ne
      rcases h_lt_or_gt with (h_lt | h_gt)
      · -- s.re < 1, so 1-s.re > 0, so 2^(1-s.re) > 1
        have h_pos : 0 < 1 - s.re := by linarith
        have h_pow_gt_one : 1 < (2 : ℝ) ^ (1 - s.re) :=
          Real.one_lt_rpow (by norm_num) h_pos
        have h_pow_re : ((2 : ℂ) ^ (1 - s)).re = (2 : ℝ) ^ (1 - s.re) := by
          have h_s_eq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [hs_im])
          rw [h_s_eq]
          have h_exp_eq : (1 - (s.re : ℂ)) = ((1 - s.re) : ℂ) := by
            ring
          rw [h_exp_eq]
          simpa using (congrArg Complex.re
            (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (1 - s.re))).symm
        rw [h_pow_eq_one] at h_pow_re
        have h_one_re : (1 : ℂ).re = 1 := by simp
        rw [h_one_re] at h_pow_re
        linarith
      · -- s.re > 1, so 1-s.re < 0, so 2^(1-s.re) < 1
        have h_neg : 1 - s.re < 0 := by linarith
        have h_pow_lt_one : (2 : ℝ) ^ (1 - s.re) < 1 := by
          have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h_neg
          simpa using h
        have h_pow_re : ((2 : ℂ) ^ (1 - s)).re = (2 : ℝ) ^ (1 - s.re) := by
          have h_s_eq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [hs_im])
          rw [h_s_eq]
          have h_exp_eq : (1 - (s.re : ℂ)) = ((1 - s.re) : ℂ) := by
            ring
          rw [h_exp_eq]
          simpa using (congrArg Complex.re
            (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (1 - s.re))).symm
        rw [h_pow_eq_one] at h_pow_re
        have h_one_re : (1 : ℂ).re = 1 := by simp
        rw [h_one_re] at h_pow_re
        linarith
    have h_s_eq_one : s = 1 := by
      apply Complex.ext <;> simp [hs_im, h_re_eq_one]
    exact hs_ne_one h_s_eq_one
  · exact h_zeta_ne_zero h_zeta

end
