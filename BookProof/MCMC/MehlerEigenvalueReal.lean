import Mathlib
import BookProof.MCMC.GaussianSteinLemma

/-!
# Chapter MehlerEigenvalueReal — the general Mehler eigenvalue `aⁿ` by the Stein induction

Plan: `pcnl.md`, packet **T1**.  `GaussianARBenchmark` proves the degree-1 and degree-2 Mehler
eigenvalue identities, and its honest boundary records the general `n`-th eigenvalue `aⁿ` as
missing, together with the input it needs: **Stein's lemma for polynomials**, now proved in
`GaussianSteinLemma.integral_sub_mul_deriv_gaussianReal`.  This chapter closes the general case.

## Contents

* `integrable_polynomial_gaussianReal` — every polynomial is `gaussianReal m v`-integrable
  (`v = 0` is a Dirac mass; for `v > 0` the density is `(√(2πv))⁻¹ exp(-(y-m)²/(2v))` and the
  product is handled by `integrable_polynomial_mul_exp_neg_mul_sq_sub`).
* `integral_id_mul_gaussianReal` — the multiplication form of Stein's lemma,
  `∫ y, y p(y) ∂N(m,v) = m ∫ p ∂N(m,v) + v ∫ p' ∂N(m,v)`, by splitting `y = m + (y - m)`.
* `hermiteReal` — the probabilists' Hermite polynomials over `ℝ`, as the image of Mathlib's
  `Polynomial.hermite : ℕ → ℤ[X]`, with the three-term recurrence `hermiteReal_succ_succ` and the
  derivative recurrence `derivative_hermiteReal`.  (Mathlib's `Polynomial.derivative_hermite_succ`
  is proved in `GaussianStein`.)
* `mehlerHermiteReal_recur` — **the Stein/Mehler recursion** for the moments
  `Aₙ = ∫ Heₙ ∂N(m,v)`: `Aₙ₊₁ = m Aₙ + (v - 1) n Aₙ₋₁`.  It is `Aₙ₊₁ + n Aₙ₋₁ = ∫ y Heₙ`
  (from `X Heₙ = Heₙ₊₁ + n Heₙ₋₁`) combined with `∫ y Heₙ = m Aₙ + v n Aₙ₋₁` (Stein).
* **`mehlerHermiteReal`** — **the general Mehler eigenvalue**: for `a² ≤ 1`, `n : ℕ` and `u : ℝ`,
  `∫ y, Heₙ(y) ∂N(a u, 1 - a²) = aⁿ Heₙ(u)`, by two-step induction on the recursion with
  `v - 1 = -a²` and `Heₙ₊₂ = X Heₙ₊₁ - (n+1) Heₙ`.  So the Hermite polynomials are eigenfunctions
  of one pCN/Mehler step with eigenvalue `aⁿ`, which is the spectral statement P1 reads off, and
  the eigenvalue the `n`-step chain of `GaussianARIterated` needs.

## Honest boundary

* The statement is at the level of the **standardised** Hermite polynomials against
  `N(a u, 1 - a²)`, i.e. the pCN step with multiplier `a` on the unit-variance Gaussian prior.
  Transferring it to the affine kernel `κ(a, c, σ)` of `GaussianARBenchmark` at an arbitrary
  innovation variance `σ` requires rescaling the state variable by the stationary standard
  deviation `√(σ/(1-a²))`; that rescaling of `gaussianReal` is not done here, so the kernel-level
  statement `P Heₙ = aⁿ Heₙ` for `gaussianARKernel a c σ` is not claimed.
* The physicists' normalisation (weight `e^{-y²}`, variance `1/2`) is the one already available
  in `MehlerEigenfunction.mehler_hermite`; the two normalisations are different eigenbases of
  the same operator, and neither implies the other without a rescaling argument.
* No `sorry`, no new axiom: the only inputs are Stein's lemma and the Hermite recurrences.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter Set Polynomial
open scoped ENNReal NNReal Polynomial

/-! ## 1. Polynomials against a Gaussian measure -/

/-- **Every polynomial is integrable against a Gaussian measure.**  For `v = 0` the measure is
the Dirac mass at `m`; for `v > 0` the density is `(√(2πv))⁻¹ exp(-(y-m)²/(2v))`, and the
polynomial-times-Gaussian product is integrable by `integrable_polynomial_mul_exp_neg_mul_sq_sub`.
-/
theorem integrable_polynomial_gaussianReal (m : ℝ) (v : ℝ≥0) (p : ℝ[X]) :
    Integrable (fun y : ℝ => p.eval y) (gaussianReal m v) := by
  by_cases hv : v = 0
  · rw [hv, gaussianReal_zero_var]
    exact integrable_dirac (by simp)
  · have hpos : 0 < v := lt_of_le_of_ne v.coe_nonneg (Ne.symm hv)
    rw [gaussianReal_of_var_ne_zero m hv]
    rw [integrable_withDensity_iff (measurable_gaussianPDF m v)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    set b : ℝ := (2 * (v : ℝ))⁻¹ with hb_def
    have hb : 0 < b := by
      rw [hb_def]
      positivity
    refine ((integrable_polynomial_mul_exp_neg_mul_sq_sub hb m p).const_mul
      (√(2 * Real.pi * (v : ℝ)))⁻¹).congr (Eventually.of_forall fun x => ?_)
    simp only [toReal_gaussianPDF, gaussianPDFReal_def, hb_def]
    rw [show -(x - m) ^ 2 / (2 * (v : ℝ)) = -((2 * (v : ℝ))⁻¹) * (x - m) ^ 2 from by
      rw [div_eq_inv_mul]
      ring]
    ring

/-- **The multiplication form of Stein's lemma**: `y` times `p` against a Gaussian is the mean
times the mass plus the variance times the derivative. -/
theorem integral_id_mul_gaussianReal (m : ℝ) (v : ℝ≥0) (p : ℝ[X]) :
    ∫ y, y * p.eval y ∂(gaussianReal m v)
      = m * ∫ y, p.eval y ∂(gaussianReal m v)
        + (v : ℝ) * ∫ y, (derivative p).eval y ∂(gaussianReal m v) := by
  have hstein := integral_sub_mul_deriv_gaussianReal m v p
  have hpt : (fun y : ℝ => y * p.eval y)
      = fun y => (y - m) * p.eval y + m * p.eval y := by
    funext y
    ring
  rw [hpt, integral_add]
  · rw [hstein, integral_const_mul]
    ring
  · have h : Integrable (fun y : ℝ => ((X - C m) * p).eval y) (gaussianReal m v) :=
      integrable_polynomial_gaussianReal m v _
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  · exact (integrable_polynomial_gaussianReal m v p).const_mul m

/-! ## 2. The probabilists' Hermite polynomials over `ℝ` -/

/-- The probabilists' Hermite polynomials over `ℝ`: the image of Mathlib's `ℤ[X]` Hermite
polynomials.  (`Polynomial.hermite` is `ℤ`-valued in the pinned Mathlib.) -/
noncomputable def hermiteReal (n : ℕ) : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)

@[simp]
theorem hermiteReal_zero : hermiteReal 0 = 1 := by
  simp [hermiteReal]

@[simp]
theorem hermiteReal_one : hermiteReal 1 = X := by
  simp [hermiteReal]

/-- The derivative recurrence `Heₙ₊₁' = (n+1) Heₙ` over `ℝ`. -/
theorem derivative_hermiteReal_succ (n : ℕ) :
    derivative (hermiteReal (n + 1)) = C ((n : ℝ) + 1) * hermiteReal n := by
  rw [hermiteReal, hermiteReal, Polynomial.derivative_map, Polynomial.derivative_hermite_succ,
    Polynomial.map_mul, Polynomial.map_C]
  rw [show ((Int.castRingHom ℝ) ((n : ℤ) + 1)) = ((n : ℝ) + 1) from by simp]

/-- The derivative recurrence in the form `Heₙ' = n Heₙ₋₁`, with the `n = 0` case degenerate. -/
theorem derivative_hermiteReal (n : ℕ) :
    derivative (hermiteReal n) = C (n : ℝ) * hermiteReal (n - 1) := by
  rcases n with _ | k
  · simp [hermiteReal]
  · rw [show k + 1 - 1 = k from rfl, derivative_hermiteReal_succ k,
      show (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 from by push_cast; ring]

/-- The three-term recurrence `Heₙ₊₂ = X Heₙ₊₁ - (n+1) Heₙ`. -/
theorem hermiteReal_succ_succ (n : ℕ) :
    hermiteReal (n + 2) = X * hermiteReal (n + 1) - C ((n : ℝ) + 1) * hermiteReal n := by
  rw [hermiteReal, hermiteReal, hermiteReal, Polynomial.hermite_succ (n + 1),
    Polynomial.derivative_hermite_succ n, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
  rw [show ((Int.castRingHom ℝ) ((n : ℤ) + 1)) = ((n : ℝ) + 1) from by simp]

/-- The recurrence solved for `X Heₙ`, valid also at `n = 0` with `He₋₁` meaningless: the
coefficient `n` vanishes there. -/
theorem X_mul_hermiteReal (n : ℕ) :
    X * hermiteReal n = hermiteReal (n + 1) + C (n : ℝ) * hermiteReal (n - 1) := by
  rcases n with _ | k
  · simp
  · rw [show k + 1 + 1 = k + 2 from rfl,
      show (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 from by push_cast; ring,
      show k + 1 - 1 = k from rfl, hermiteReal_succ_succ k]
    ring

/-! ## 3. The Stein/Mehler recursion for the Hermite moments -/

/-- **The Stein/Mehler recursion.**  For the moments `Aₙ = ∫ y, Heₙ(y) ∂N(m, v)` of the
probabilists' Hermite polynomials against a Gaussian,
`Aₙ₊₁ = m Aₙ + (v - 1) n Aₙ₋₁`.

It is the difference of two computations of `∫ y Heₙ(y)`: the polynomial recurrence
`X Heₙ = Heₙ₊₁ + n Heₙ₋₁` gives `Aₙ₊₁ + n Aₙ₋₁`, and the multiplication form of Stein's lemma
gives `m Aₙ + v n Aₙ₋₁`. -/
theorem mehlerHermiteReal_recur (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    (∫ y, (hermiteReal (n + 1)).eval y ∂(gaussianReal m v))
      = m * (∫ y, (hermiteReal n).eval y ∂(gaussianReal m v))
        + ((v : ℝ) - 1) * (n : ℝ)
          * (∫ y, (hermiteReal (n - 1)).eval y ∂(gaussianReal m v)) := by
  set A : ℕ → ℝ := fun k => ∫ y, (hermiteReal k).eval y ∂(gaussianReal m v)
  change A (n + 1) = m * A n + ((v : ℝ) - 1) * (n : ℝ) * A (n - 1)
  have hderiv : ∫ y, (derivative (hermiteReal n)).eval y ∂(gaussianReal m v)
      = (n : ℝ) * A (n - 1) := by
    rw [derivative_hermiteReal]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [integral_const_mul]
  have h1 : ∫ y, y * (hermiteReal n).eval y ∂(gaussianReal m v)
      = m * A n + (v : ℝ) * ((n : ℝ) * A (n - 1)) := by
    rw [integral_id_mul_gaussianReal m v (hermiteReal n), hderiv]
  have h2 : ∫ y, y * (hermiteReal n).eval y ∂(gaussianReal m v)
      = A (n + 1) + (n : ℝ) * A (n - 1) := by
    have hpt : (fun y : ℝ => y * (hermiteReal n).eval y) = fun y =>
        (hermiteReal (n + 1)).eval y + (n : ℝ) * (hermiteReal (n - 1)).eval y := by
      funext y
      have h := congrArg (fun p : ℝ[X] => p.eval y) (X_mul_hermiteReal n)
      simpa only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C] using h
    rw [hpt, integral_add (integrable_polynomial_gaussianReal m v _)
      ((integrable_polynomial_gaussianReal m v _).const_mul (n : ℝ)), integral_const_mul]
  have key : A (n + 1) = m * A n + (v : ℝ) * ((n : ℝ) * A (n - 1)) - (n : ℝ) * A (n - 1) :=
    by linarith [h1, h2]
  rw [key]
  ring

/-! ## 4. The general Mehler eigenvalue `aⁿ` -/

/-- `1 - a²` as an `ℝ≥0`: the variance of one pCN/Mehler step with multiplier `a ∈ [-1, 1]`. -/
def oneSubSq (a : ℝ) (ha : a ^ 2 ≤ 1) : ℝ≥0 := ⟨1 - a ^ 2, by linarith⟩

/-- **The general Mehler eigenvalue.**  For `a² ≤ 1`, the probabilists' Hermite polynomial `Heₙ`
is an eigenfunction of the pCN/Mehler operator `T_a f (u) = ∫ f ∂N(a u, 1 - a²)` with eigenvalue
`aⁿ`:

`∫ y, Heₙ(y) ∂N(a u, 1 - a²) = aⁿ Heₙ(u)`.

Proved by two-step induction on the Stein/Mehler recursion `mehlerHermiteReal_recur`, where
`v - 1 = -a²` and `Heₙ₊₂ = X Heₙ₊₁ - (n+1) Heₙ` close the induction. -/
theorem mehlerHermiteReal (a : ℝ) (ha : a ^ 2 ≤ 1) (n : ℕ) (u : ℝ) :
    ∫ y, (hermiteReal n).eval y ∂(gaussianReal (a * u) (oneSubSq a ha))
      = a ^ n * (hermiteReal n).eval u := by
  have hvcoe : ((oneSubSq a ha : ℝ≥0) : ℝ) = 1 - a ^ 2 := rfl
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [mehlerHermiteReal_recur (a * u) (oneSubSq a ha) 0]
    simp [hvcoe]
  | more n ih ih' =>
    rw [mehlerHermiteReal_recur (a * u) (oneSubSq a ha) (n + 1)]
    rw [show n + 1 + 1 = n + 2 from rfl, show n + 1 - 1 = n from rfl, ih, ih']
    rw [show (hermiteReal (n + 2)).eval u
        = u * (hermiteReal (n + 1)).eval u
          - ((n : ℝ) + 1) * (hermiteReal n).eval u from by
      rw [hermiteReal_succ_succ]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C]]
    simp only [hvcoe]
    have hp1 : a ^ (n + 1) = a * a ^ n := by rw [pow_succ]; ring
    have hp2 : a ^ (n + 2) = a ^ 2 * a ^ n := by
      rw [show n + 2 = 2 + n by ring, pow_add]
    push_cast
    rw [hp1, hp2]
    ring

end BookProof.MCMC
