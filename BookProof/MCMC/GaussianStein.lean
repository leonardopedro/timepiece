import Mathlib
import BookProof.MCMC.GaussianARBenchmark

/-!
# Chapter GaussianStein — the analytic input for general Mehler eigenvalues

Plan: `pcnl.md`, packet **T1** (the general `n`-th eigenvalue `aⁿ`).  The eigenfunction
induction recorded in `GaussianARIterated` reduces to one analytic fact, **Stein's lemma for
polynomials**: for every `p : ℝ[X]`,

`∫ y, (y - m) p.eval y ∂(gaussianReal m v) = v * ∫ y, (derivative p).eval y ∂(gaussianReal m v)`.

Every integration-by-parts formulation in Mathlib demands integrability of the three products
`p * v'`, `p' * v`, `p * v` against Lebesgue measure.  This chapter supplies the integrability
input, which the pinned Mathlib does not have: it knows `z ↦ exp(-b z²)` and
`z ↦ z * exp(-b z²)`, and higher monomials only for *real* exponents (`rpow`, which is not the
natural power on `ℝ<0`).

## What is proved here

* `integrableOn_abs_pow_mul_exp_neg_mul_sq` — the positive half, from Mathlib's
  `integrableOn_rpow_mul_exp_neg_mul_sq` together with `Real.rpow_natCast`.
* `integrableOn_abs_pow_mul_exp_neg_mul_sq_Iic` — the negative half, by transporting along
  `z ↦ -z` with `Measure.measurePreserving_neg`.
* `integrable_abs_pow_mul_exp_neg_mul_sq`, `integrable_pow_mul_exp_neg_mul_sq` — the whole line,
  and the natural power (integrability depends only on the norm).
* `integrable_polynomial_mul_exp_neg_mul_sq` — the polynomial version, by expanding in the
  monomial basis.
* `Polynomial.derivative_hermite_succ`, `Polynomial.derivative_hermite_succ_nsmul` — the Hermite
  derivative recurrence `Heₙ₊₁' = (n+1) Heₙ` over `ℤ[X]`, which the pinned Mathlib does not have
  (it has the three-term recurrence and the Rodrigues identity, but not this one).

## Honest boundary

Stein's lemma itself is **not** proved here.  Beyond this integrability input it needs
(i) the derivative of the Gaussian density,
`deriv (gaussianPDFReal m v) y = -(y - m)/v * gaussianPDFReal m v y` for `v ≠ 0`, and
(ii) the transfer of integrability from `gaussianReal m v` to Lebesgue measure
(`MeasureTheory.integrable_withDensity_iff` with `ProbabilityTheory.toReal_gaussianPDF`), which
is what turns "`p` is integrable against the Gaussian" into "`p * density` is integrable".  The
IBP step is then `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable` with `u = p` and
`v` the Gaussian weight.  These are recorded as the next steps, not claimed.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter Set
open Polynomial
open scoped ENNReal NNReal Polynomial

/-- **Positive-axis integrability of `|z|ⁿ` against a Gaussian.** -/
theorem integrableOn_abs_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) :
    IntegrableOn (fun z : ℝ => |z| ^ k * Real.exp (-b * z ^ 2)) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ))
    (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Real.rpow_natCast, abs_of_pos hz]

/-- **Integrability of `|z|ⁿ` against a Gaussian on the negative axis**, by transporting along
`z ↦ -z`. -/
theorem integrableOn_abs_pow_mul_exp_neg_mul_sq_Iic {b : ℝ} (hb : 0 < b) (k : ℕ) :
    IntegrableOn (fun z : ℝ => |z| ^ k * Real.exp (-b * z ^ 2)) (Iic 0) := by
  have hpos : IntegrableOn (fun z : ℝ => |z| ^ k * Real.exp (-b * z ^ 2)) (Ioi 0) :=
    integrableOn_abs_pow_mul_exp_neg_mul_sq hb k
  have hpos' : IntegrableOn (fun z : ℝ => |z| ^ k * Real.exp (-b * z ^ 2)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (b := 0)).mpr hpos
  have hiff := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding
    (f := fun z : ℝ => |z| ^ k * Real.exp (-b * z ^ 2)) (s := Iic 0)
  rw [← hiff, neg_preimage, neg_Iic, neg_zero]
  convert hpos' using 2
  simp

/-- **Integrability of `|z|ⁿ` against a Gaussian.** -/
theorem integrable_abs_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun z : ℝ => |z| ^ k * Real.exp (-b * z ^ 2)) := by
  rw [← integrableOn_univ, ← @Iic_union_Ioi _ _ (0 : ℝ), integrableOn_union]
  exact ⟨integrableOn_abs_pow_mul_exp_neg_mul_sq_Iic hb k,
    integrableOn_abs_pow_mul_exp_neg_mul_sq hb k⟩

/-- **Natural-power integrability against a Gaussian**: `zⁿ exp(-b z²)` is integrable for
`b > 0`, for every `n : ℕ`. -/
theorem integrable_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun z : ℝ => z ^ k * Real.exp (-b * z ^ 2)) := by
  refine (integrable_norm_iff ?_).mp ?_
  · fun_prop
  · refine (integrable_abs_pow_mul_exp_neg_mul_sq hb k).congr
      (Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]

/-- **Polynomial integrability against a Gaussian**: for `b > 0` and any real polynomial `p`,
`z ↦ p(z) exp(-b z²)` is integrable against Lebesgue measure. -/
theorem integrable_polynomial_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (p : ℝ[X]) :
    Integrable (fun z : ℝ => p.eval z * Real.exp (-b * z ^ 2)) := by
  have hsum : (fun z : ℝ => p.eval z * Real.exp (-b * z ^ 2))
      = fun z : ℝ => ∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * (z ^ i * Real.exp (-b * z ^ 2)) := by
    funext z
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  exact integrable_finset_sum _ fun i _ => (integrable_pow_mul_exp_neg_mul_sq hb i).const_mul _


end BookProof.MCMC

namespace Polynomial
/-! ## 2. The Hermite derivative recurrence -/

/-- **The Hermite derivative recurrence**: `Heₙ₊₁' = (n+1) Heₙ` over `ℤ[X]`.

The pinned Mathlib has the three-term recurrence `hermite (n+1) = X * hermite n - derivative
(hermite n)` but not this derivative identity, which the Mehler eigenfunction induction needs in
order to replace `P Heₙ'` by `n P Heₙ₋₁`.  The proof is a two-step induction: differentiating the
three-term recurrence at level `n+2` and substituting the recurrence one level down leaves the
factored form `(1 + C(n+2)) * (X Heₙ₊₁ - C(n+1) Heₙ)`, and `1 + C(n+2) = C(n+3)`.

Mathlib's `Polynomial.derivative_hermite_succ` does not exist, so this is stated in the
`Polynomial` namespace where it belongs. -/
theorem derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = C ((n : ℤ) + 1) * hermite n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [hermite_succ 0]
    simp
  | one =>
    rw [hermite_succ 1]
    simp [Polynomial.derivative_X]
    ring
  | more n ih ih' =>
    have hs : hermite (n + 2) = X * hermite (n + 1) - C ((n : ℤ) + 1) * hermite n := by
      rw [hermite_succ (n + 1), ih]
    have e1 : C ((↑(n + 1) : ℤ) + 1) = C (2 + (n : ℤ)) := by
      congr 1
      push_cast
      ring
    have e2 : C ((↑(n + 2) : ℤ) + 1) = C (3 + (n : ℤ)) := by
      congr 1
      push_cast
      ring
    have hC : (1 : Polynomial ℤ) + C (2 + (n : ℤ)) = C (3 + (n : ℤ)) := by
      rw [← C_1, ← C_add, C_inj]
      ring
    rw [e2, hs, hermite_succ (n + 2), derivative_sub, derivative_mul, derivative_X, ih', e1,
      derivative_mul, derivative_C, zero_mul, zero_add, ih]
    linear_combination (X * hermite (n + 1) - C ((n : ℤ) + 1) * hermite n) * hC + hs

/-- The same recurrence in `nsmul` form, matching the Hermite eigenvalue bookkeeping. -/
theorem derivative_hermite_succ_nsmul (n : ℕ) :
    derivative (Polynomial.hermite (n + 1)) = (n + 1) •
      Polynomial.hermite n := by
  rw [derivative_hermite_succ, nsmul_eq_mul]
  congr 1

end Polynomial
