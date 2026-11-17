import Mathlib
import BookProof.MCMC.GaussianStein

/-!
# Chapter GaussianSteinLemma — Stein's lemma for polynomials against a Gaussian

Plan: `pcnl.md`, packet **T1**.  This is the analytic input for the general Mehler eigenvalue
`aⁿ` (see `GaussianARIterated`'s boundary note): for every real polynomial `p`,

`∫ y, (y - m) p.eval y ∂(gaussianReal m v) = v * ∫ y, (derivative p).eval y ∂(gaussianReal m v)`.

With it, the induction `P (X f) = a X (P f) + σ P f'` (and `P f' = a (P f)'`) turns the Hermite
derivative recurrence into `P Heₙ = aⁿ Heₙ`.

## What is proved here

* `integral_deriv_mul_exp_neg_mul_sq` — the integration-by-parts core against the *unshifted*
  weight `exp(-b z²)`.
* `integrable_polynomial_mul_exp_neg_mul_sq_sub` — the shifted integrability, by transporting the
  unshifted one along `z ↦ z - m` (`Integrable.comp_sub_right`).
* `integral_sub_mul_deriv_gaussianReal` — **Stein's lemma**: the statement above, for `v ≥ 0`.
  The `v = 0` case is the Dirac mass at `m`; for `v > 0`, the Gaussian density is
  `(√(2πv))⁻¹ exp(-(y-m)²/(2v))`, whose constant factors out of both sides.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter Set Polynomial
open scoped ENNReal NNReal Polynomial

/-- **Integration by parts against a Gaussian weight.**  For `b > 0` and a polynomial `q`,

`∫ z, q'(z) exp(-b z²) = 2 b ∫ z, z q(z) exp(-b z²)`,

which is `∫ q w' = -∫ q' w` for `w = exp(-b z²)`, `w' = -2 b z w`, with the boundary terms
supplied by integrability (`integral_mul_deriv_eq_deriv_mul_of_integrable`). -/
theorem integral_deriv_mul_exp_neg_mul_sq (q : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    ∫ z, (Polynomial.derivative q).eval z * Real.exp (-b * z ^ 2)
      = 2 * b * ∫ z, z * q.eval z * Real.exp (-b * z ^ 2) := by
  have hu : ∀ z : ℝ, HasDerivAt (fun z => q.eval z) ((Polynomial.derivative q).eval z) z :=
    fun z => Polynomial.hasDerivAt q z
  have hv : ∀ z : ℝ, HasDerivAt (fun z : ℝ => Real.exp (-b * z ^ 2))
      (-2 * b * z * Real.exp (-b * z ^ 2)) z := by
    intro z
    have h1 : HasDerivAt (fun z : ℝ => -b * z ^ 2) (-b * (2 * z)) z := by
      simpa using (hasDerivAt_pow 2 z).const_mul (-b)
    have h2 := h1.exp
    convert h2 using 1
    ring
  have hInt1 : Integrable (fun z : ℝ => q.eval z * (-2 * b * z * Real.exp (-b * z ^ 2))) := by
    have hp : Integrable
        (fun z : ℝ => (q * (Polynomial.C (-(2 * b)) * Polynomial.X)).eval z
          * Real.exp (-b * z ^ 2)) :=
      integrable_polynomial_mul_exp_neg_mul_sq hb _
    refine hp.congr (Eventually.of_forall fun z => ?_)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hInt2 : Integrable (fun z : ℝ => (Polynomial.derivative q).eval z * Real.exp (-b * z ^ 2)) :=
    integrable_polynomial_mul_exp_neg_mul_sq hb _
  have hInt3 : Integrable (fun z : ℝ => q.eval z * Real.exp (-b * z ^ 2)) :=
    integrable_polynomial_mul_exp_neg_mul_sq hb _
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv hInt1 hInt2 hInt3
  have h1 : ∫ z, q.eval z * (-2 * b * z * Real.exp (-b * z ^ 2))
      = (-2 * b) * ∫ z, z * q.eval z * Real.exp (-b * z ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  rw [h1] at hIBP
  linear_combination hIBP

/-- **Shifted polynomial-times-Gaussian integrability**: `p(y) exp(-b (y-m)²)` is integrable,
by transporting the unshifted statement along `z ↦ z - m`. -/
theorem integrable_polynomial_mul_exp_neg_mul_sq_sub {b : ℝ} (hb : 0 < b) (m : ℝ)
    (p : ℝ[X]) :
    Integrable (fun y : ℝ => p.eval y * Real.exp (-b * (y - m) ^ 2)) := by
  have hp : Integrable
      (fun z : ℝ => (p.comp (Polynomial.X + Polynomial.C m)).eval z * Real.exp (-b * z ^ 2)) :=
    integrable_polynomial_mul_exp_neg_mul_sq hb _
  refine (hp.comp_sub_right m).congr (Eventually.of_forall fun y => ?_)
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    sub_add_cancel]

/-- **Stein's lemma for polynomials against a Gaussian.**  For every `p : ℝ[X]`, `m : ℝ` and
`v : ℝ≥0`,

`∫ y, (y - m) p(y) ∂N(m, v) = v ∫ y, p'(y) ∂N(m, v)`.

This is the "multiplication by `y - m` is `v` times differentiation" identity that makes the
Hermite polynomials eigenfunctions of the Mehler operator. -/
theorem integral_sub_mul_deriv_gaussianReal (m : ℝ) (v : ℝ≥0) (p : ℝ[X]) :
    ∫ y, (y - m) * p.eval y ∂(gaussianReal m v)
      = (v : ℝ) * ∫ y, (Polynomial.derivative p).eval y ∂(gaussianReal m v) := by
  by_cases hv : v = 0
  · subst hv
    simp [gaussianReal_zero_var]
  · have hpos : 0 < v := lt_of_le_of_ne v.coe_nonneg (Ne.symm hv)
    set b : ℝ := (2 * (v : ℝ))⁻¹ with hb_def
    have hb : 0 < b := by
      rw [hb_def]
      positivity
    set W : ℝ → ℝ := fun y => Real.exp (-b * (y - m) ^ 2) with hW_def
    have hpdf : ∀ y : ℝ,
        gaussianPDFReal m v y = (√(2 * Real.pi * (v : ℝ)))⁻¹ * W y := by
      intro y
      simp only [gaussianPDFReal_def, hW_def, hb_def]
      rw [show -(y - m) ^ 2 / (2 * (v : ℝ)) = -((2 * (v : ℝ))⁻¹) * (y - m) ^ 2 from by
        rw [div_eq_inv_mul]
        ring]
    have hWderiv : ∀ y : ℝ, HasDerivAt W (-(1 / (v : ℝ)) * ((y - m) * W y)) y := by
      intro y
      have h0 : HasDerivAt (fun y : ℝ => y - m) 1 y := (hasDerivAt_id y).sub_const m
      have h1 : HasDerivAt (fun y : ℝ => -b * (y - m) ^ 2) (-b * (2 * (y - m))) y := by
        have h := (h0.pow 2).const_mul (-b)
        simpa [mul_comm, mul_assoc] using h
      have h2 := h1.exp
      rw [hW_def]
      convert h2 using 1
      rw [hb_def]
      field_simp
    have hu : ∀ y : ℝ, HasDerivAt (fun y => p.eval y) ((Polynomial.derivative p).eval y) y :=
      fun y => Polynomial.hasDerivAt p y
    have hInt1 : Integrable (fun y : ℝ => p.eval y * (-(1 / (v : ℝ)) * ((y - m) * W y))) := by
      have hp : Integrable (fun y : ℝ => ((Polynomial.X - Polynomial.C m) * p).eval y
          * Real.exp (-b * (y - m) ^ 2)) :=
        integrable_polynomial_mul_exp_neg_mul_sq_sub hb m _
      refine (hp.const_mul (-(1 / (v : ℝ)))).congr (Eventually.of_forall fun y => ?_)
      simp only [hW_def, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    have hInt2 : Integrable (fun y : ℝ => (Polynomial.derivative p).eval y * W y) := by
      have hp : Integrable (fun y : ℝ => (Polynomial.derivative p).eval y
          * Real.exp (-b * (y - m) ^ 2)) :=
        integrable_polynomial_mul_exp_neg_mul_sq_sub hb m _
      exact hp.congr (Eventually.of_forall fun y => by rw [hW_def])
    have hInt3 : Integrable (fun y : ℝ => p.eval y * W y) := by
      have hp : Integrable (fun y : ℝ => p.eval y * Real.exp (-b * (y - m) ^ 2)) :=
        integrable_polynomial_mul_exp_neg_mul_sq_sub hb m p
      exact hp.congr (Eventually.of_forall fun y => by rw [hW_def])
    have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable hu hWderiv hInt1 hInt2 hInt3
    have hvne : (v : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hpos)
    have hA : ∫ y, p.eval y * (-(1 / (v : ℝ)) * ((y - m) * W y))
        = (-(1 / (v : ℝ))) * ∫ y, (y - m) * p.eval y * W y := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    rw [hA] at hIBP
    have hI : ∫ y, (y - m) * p.eval y * W y
        = (v : ℝ) * ∫ y, (derivative p).eval y * W y := by
      field_simp at hIBP
      linarith [hIBP]
    have hL : ∫ y, (y - m) * p.eval y ∂(gaussianReal m v)
        = (√(2 * Real.pi * (v : ℝ)))⁻¹ * ∫ y, (y - m) * p.eval y * W y := by
      rw [integral_gaussianReal_eq_integral_smul hv]
      simp only [smul_eq_mul]
      rw [show (fun y => gaussianPDFReal m v y * ((y - m) * p.eval y))
          = fun y => (√(2 * Real.pi * (v : ℝ)))⁻¹ * ((y - m) * p.eval y * W y) from by
        funext y
        rw [hpdf y]
        ring]
      rw [integral_const_mul]
    have hR : ∫ y, (Polynomial.derivative p).eval y ∂(gaussianReal m v)
        = (√(2 * Real.pi * (v : ℝ)))⁻¹ * ∫ y, (Polynomial.derivative p).eval y * W y := by
      rw [integral_gaussianReal_eq_integral_smul hv]
      simp only [smul_eq_mul]
      rw [show (fun y => gaussianPDFReal m v y * (Polynomial.derivative p).eval y)
          = fun y => (√(2 * Real.pi * (v : ℝ)))⁻¹ * ((Polynomial.derivative p).eval y * W y) from by
        funext y
        rw [hpdf y]
        ring]
      rw [integral_const_mul]
    rw [hL, hR, hI]
    ring

end BookProof.MCMC
