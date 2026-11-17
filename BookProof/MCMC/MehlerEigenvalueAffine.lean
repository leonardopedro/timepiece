import Mathlib
import BookProof.MCMC.GaussianARBenchmark
import BookProof.MCMC.MehlerEigenvalueReal

/-!
# Chapter MehlerEigenvalueAffine — the `aⁿ` eigenvalue of the affine Gaussian kernel

Plan: `pcnl.md`, packet **T1**.  `MehlerEigenvalueReal.mehlerHermiteReal` proves the eigenvalue
identity for the **standardised** pCN/Mehler step,

`∫ y, Heₙ(y) ∂N(a u, 1 - a²) = aⁿ Heₙ(u)`,

and its boundary records that the transfer to the affine kernel `gaussianARKernel a c σ` of
`GaussianARBenchmark` — whose state measure at `x` is `N(a x + c, σ)` with an arbitrary
innovation variance `σ` — was still open.  This chapter performs that transfer by rescaling the
state variable with the stationary standard deviation `s = √(σ/(1-a²))`.

## Contents

* `integral_gaussianReal_affine_scale` — **the change of variables** for a Gaussian measure
  under the *standardising* map `y ↦ (y - m)/s`:
  `∫ y, F((y-m)/s) ∂N(μ,σ) = ∫ z, F z ∂N((μ-m)/s, σ/s²)`, from `integral_map` and
  `gaussianReal_affine_map`.
* **`mehlerHermiteReal_affine`** — **the `aⁿ` eigenvalue at arbitrary innovation variance**:
  for `a² < 1`, `σ ≠ 0`, with `m = c/(1-a)` the stationary mean and `s = √(σ/(1-a²))` the
  stationary standard deviation,

  `∫ y, Heₙ((y - m)/s) ∂(gaussianARKernel a c σ x) = aⁿ Heₙ((x - m)/s)`,

  i.e. the standardised Hermite polynomials are eigenfunctions of the affine chain's operator
  with eigenvalue `aⁿ`.  The two structural facts are `a m + c = m` (so the centred state moves
  by the multiplier `a`) and `s² = σ/(1-a²)` (so the standardised innovation variance is
  exactly `1 - a²`).

## Initial cases

`mehlerHermiteReal_affine_one` and `mehlerHermiteReal_affine_two` specialise the eigenvalue
identity to `n = 1` and `n = 2` and rewrite it in centred form, `hermiteReal_two` (`He₂ = X² - 1`)
supplying the degree-two polynomial.  The resulting statements are *identical* to
`gaussianARKernel_integral_sub` and `gaussianARKernel_integral_sub_sq` of
`GaussianARBenchmark`, which prove the same two identities directly from the Gaussian moments.
So the pair is a genuine cross-check: the moment route and the Mehler route agree on the `a` and
`a²` eigenvalues, including at `σ = 0`.

## Honest boundary

* The statement is for the *standardised* Hermite polynomials `Heₙ((· - m)/s)`; it does not
  claim the un-standardised form `Heₙ(· - m)` (which is not an eigenfunction unless
  `s = 1`), nor an `L²(π)` operator statement — that is the `Lp` chapter's business.
* `σ ≠ 0` is required for the general `n`: at `σ = 0` the stationary variance vanishes, `s = 0`,
  and the standardising map is not defined; the chain degenerates to `x ↦ a x + c`.  The `n = 1`
  and `n = 2` instances do cover that degenerate case (`integral_dirac` plus `a m + c = a m`),
  but no general-`n` `σ = 0` statement is claimed.
* Degenerate `σ = 0` at `n = 1, 2` is proved by unfolding the Dirac integral directly, not by
taking a limit of the `σ > 0` identity.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Polynomial

/-- **Standardising change of variables for a Gaussian measure.**  For `s > 0`,

`∫ y, F((y - m)/s) ∂N(μ, v) = ∫ z, F z ∂N((μ - m)/s, v/s²)`.

Proof: `integral_map` moves the integral to the pushforward under `y ↦ (y-m)/s`, which is the
affine map `y ↦ s⁻¹ y + (-m/s)`; `gaussianReal_affine_map` identifies that pushforward. -/
theorem integral_gaussianReal_affine_scale (m μ : ℝ) (v : ℝ≥0) {s : ℝ} (hs : 0 < s)
    (F : ℝ → ℝ) (hF : Measurable F) :
    ∫ y, F ((y - m) / s) ∂(gaussianReal μ v)
      = ∫ z, F z ∂(gaussianReal ((μ - m) / s) ⟨v / s ^ 2, by
          have : (0 : ℝ) < s ^ 2 := by positivity
          exact div_nonneg v.coe_nonneg (le_of_lt this)⟩) := by
  have hsne : s ≠ 0 := ne_of_gt hs
  have hfun : (fun y : ℝ => (y - m) / s) = fun y => s⁻¹ * y + (-m / s) := by
    funext y
    field_simp
    ring
  rw [← integral_map (φ := fun y : ℝ => (y - m) / s) (by fun_prop) hF.aestronglyMeasurable]
  congr 1
  rw [hfun, gaussianReal_affine_map]
  congr 1
  · field_simp
    ring
  · refine NNReal.coe_inj.mp ?_
    simp only [NNReal.coe_mul, nnrealSq, NNReal.coe_mk]
    field_simp

/-! ## 2. The `aⁿ` eigenvalue of the affine kernel -/

/-- **The Mehler eigenvalue `aⁿ` at arbitrary innovation variance.**  With `m = c/(1-a)` the
stationary mean and `s = √(σ/(1-a²))` the stationary standard deviation, the standardised
probabilists' Hermite polynomial is an eigenfunction of the affine Gaussian chain's operator:

`∫ y, Heₙ((y - m)/s) ∂N(a x + c, σ) = aⁿ Heₙ((x - m)/s)`.

The proof standardises the state variable (`integral_gaussianReal_affine_scale`), using
`a m + c = m` for the mean and `s² = σ/(1-a²)` for the variance, and then applies the
standardised eigenvalue identity `mehlerHermiteReal`. -/
theorem mehlerHermiteReal_affine (a c : ℝ) (σ : ℝ≥0) (ha : a ^ 2 < 1) (hσ : σ ≠ 0)
    (n : ℕ) (x : ℝ) :
    ∫ y, (hermiteReal n).eval
        ((y - gaussianARMean a c) / Real.sqrt (gaussianARVar a σ ha : ℝ))
        ∂(gaussianARKernel a c σ x)
      = a ^ n * (hermiteReal n).eval
          ((x - gaussianARMean a c) / Real.sqrt (gaussianARVar a σ ha : ℝ)) := by
  set m := gaussianARMean a c with hm
  set v : ℝ≥0 := gaussianARVar a σ ha with hv
  have hσcoe : (σ : ℝ) ≠ 0 := by simpa using hσ
  have hσpos : (0 : ℝ) < (σ : ℝ) := lt_of_le_of_ne σ.coe_nonneg (Ne.symm hσcoe)
  have hone : (0 : ℝ) < 1 - a ^ 2 := by linarith
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    rw [hv, gaussianARVar, NNReal.coe_mk]
    exact div_pos hσpos hone
  set s := Real.sqrt (v : ℝ) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hvpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs2 : s ^ 2 = (v : ℝ) := Real.sq_sqrt (le_of_lt hvpos)
  have hmc : a * m + c = m := by
    rw [hm]
    exact gaussianARMean_eq a c ha
  have hσv : (σ : ℝ) = (v : ℝ) * (1 - a ^ 2) := by
    rw [hv, gaussianARVar, NNReal.coe_mk]
    field_simp
  rw [gaussianARKernel_apply]
  -- the standardised mean of one step is `a` times the standardised state
  have hw : (a * x + c - m) / s = a * ((x - m) / s) := by
    field_simp
    linarith
  -- the standardised innovation variance is `1 - a²`
  have hvariance : (⟨(σ : ℝ) / s ^ 2, by positivity⟩ : ℝ≥0) = oneSubSq a (le_of_lt ha) := by
    refine NNReal.coe_inj.mp ?_
    simp only [NNReal.coe_mk, oneSubSq]
    rw [hσv, ← hs2]
    field_simp
  set w := (x - m) / s with hwdef
  calc ∫ y, (hermiteReal n).eval ((y - m) / s) ∂(gaussianReal (a * x + c) σ)
      = ∫ z, (hermiteReal n).eval z
          ∂(gaussianReal ((a * x + c - m) / s) ⟨(σ : ℝ) / s ^ 2, by positivity⟩) :=
        integral_gaussianReal_affine_scale (m := m) (μ := a * x + c) (v := σ) (s := s) hspos
          (fun z => (hermiteReal n).eval z) (by fun_prop)
    _ = ∫ z, (hermiteReal n).eval z ∂(gaussianReal (a * w) (oneSubSq a (le_of_lt ha))) := by
        rw [hw, hvariance, hwdef]
    _ = a ^ n * (hermiteReal n).eval w := mehlerHermiteReal a (le_of_lt ha) n w

/-! ## 3. The `n = 1` and `n = 2` instances, matching the centred moment proofs -/

/-- `He₂ = X² - 1`. -/
theorem hermiteReal_two : hermiteReal 2 = (Polynomial.X : ℝ[X]) ^ 2 - (1 : ℝ[X]) := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, hermiteReal_succ_succ 0]
  simp [pow_two]

/-- **Degree-1 instance of `mehlerHermiteReal_affine`.**  This is the `n = 1` case of the
general eigenvalue identity, rewritten in the centred form that `GaussianARBenchmark` proves
directly from the Gaussian moments (`gaussianARKernel_integral_sub`):

`∫ y, (y - m) ∂κ(a,c,σ) x = a (x - m)`, with `m = c/(1-a)`.

Here it is *derived* from the Mehler eigenvalue `a¹ = a` rather than from the moments, which is
the consistency check between the two routes.  The degenerate case `σ = 0` is the Dirac chain
`x ↦ a x + c`. -/
theorem mehlerHermiteReal_affine_one (a c : ℝ) (σ : ℝ≥0) (ha : a ^ 2 < 1) (x : ℝ) :
    ∫ y, (y - gaussianARMean a c) ∂(gaussianARKernel a c σ x)
      = a * (x - gaussianARMean a c) := by
  by_cases hσ : σ = 0
  · rw [hσ, gaussianARKernel_apply, gaussianReal_zero_var, integral_dirac]
    linarith [gaussianARMean_eq a c ha]
  · have hσcoe : (σ : ℝ) ≠ 0 := by simpa using hσ
    have hvpos : (0 : ℝ) < (gaussianARVar a σ ha : ℝ) := by
      rw [gaussianARVar, NNReal.coe_mk]
      exact div_pos (lt_of_le_of_ne σ.coe_nonneg (Ne.symm hσcoe)) (by linarith)
    have hspos : 0 < Real.sqrt (gaussianARVar a σ ha : ℝ) := Real.sqrt_pos.2 hvpos
    have hsne : Real.sqrt (gaussianARVar a σ ha : ℝ) ≠ 0 := ne_of_gt hspos
    have h := mehlerHermiteReal_affine a c σ ha hσ 1 x
    simp only [hermiteReal_one, Polynomial.eval_X, pow_one] at h
    have h1 : Real.sqrt (gaussianARVar a σ ha : ℝ)
          * ∫ y, (y - gaussianARMean a c) / Real.sqrt (gaussianARVar a σ ha : ℝ)
              ∂(gaussianARKernel a c σ x)
        = ∫ y, (y - gaussianARMean a c) ∂(gaussianARKernel a c σ x) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun y => by field_simp)
    rw [h] at h1
    rw [← h1]
    field_simp

/-- **Degree-2 instance of `mehlerHermiteReal_affine`.**  The `n = 2` case in the centred form
that `GaussianARBenchmark` proves from the Gaussian moments
(`gaussianARKernel_integral_sub_sq`):

`∫ y, ((y - m)² - s) ∂κ(a,c,σ) x = a² ((x - m)² - s)`,

with `m = c/(1-a)` and `s = σ/(1-a²)` the stationary variance.  Here it is derived from the
Mehler eigenvalue `a²` together with `He₂ = X² - 1`, and `s` enters as the square of the
standardising scale. -/
theorem mehlerHermiteReal_affine_two (a c : ℝ) (σ : ℝ≥0) (ha : a ^ 2 < 1) (x : ℝ) :
    ∫ y, ((y - gaussianARMean a c) ^ 2 - (gaussianARVar a σ ha : ℝ))
        ∂(gaussianARKernel a c σ x)
      = a ^ 2 * ((x - gaussianARMean a c) ^ 2 - (gaussianARVar a σ ha : ℝ)) := by
  by_cases hσ : σ = 0
  · have hv0 : (gaussianARVar a 0 ha : ℝ) = 0 := by
      rw [gaussianARVar, NNReal.coe_mk]
      norm_num
    rw [hσ, gaussianARKernel_apply, gaussianReal_zero_var, integral_dirac, hv0]
    rw [show a * x + c - gaussianARMean a c = a * (x - gaussianARMean a c) from by
      linarith [gaussianARMean_eq a c ha]]
    ring
  · have hσcoe : (σ : ℝ) ≠ 0 := by simpa using hσ
    have hvpos : (0 : ℝ) < (gaussianARVar a σ ha : ℝ) := by
      rw [gaussianARVar, NNReal.coe_mk]
      exact div_pos (lt_of_le_of_ne σ.coe_nonneg (Ne.symm hσcoe)) (by linarith)
    have hspos : 0 < Real.sqrt (gaussianARVar a σ ha : ℝ) := Real.sqrt_pos.2 hvpos
    have hsne : Real.sqrt (gaussianARVar a σ ha : ℝ) ≠ 0 := ne_of_gt hspos
    have hs2 : Real.sqrt (gaussianARVar a σ ha : ℝ) ^ 2 = (gaussianARVar a σ ha : ℝ) :=
      Real.sq_sqrt (le_of_lt hvpos)
    have hev : ∀ u : ℝ, (hermiteReal 2).eval u = u ^ 2 - 1 := by
      intro u
      rw [hermiteReal_two]
      simp [pow_two]
    have h := mehlerHermiteReal_affine a c σ ha hσ 2 x
    simp only [hev] at h
    have h1 : Real.sqrt (gaussianARVar a σ ha : ℝ) ^ 2
          * ∫ y, ((y - gaussianARMean a c) / Real.sqrt (gaussianARVar a σ ha : ℝ)) ^ 2 - 1
              ∂(gaussianARKernel a c σ x)
        = ∫ y, ((y - gaussianARMean a c) ^ 2 - (gaussianARVar a σ ha : ℝ))
            ∂(gaussianARKernel a c σ x) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun y => by
        field_simp
        rw [hs2])
    rw [h] at h1
    rw [← h1, ← hs2]
    field_simp
    rw [Real.sqrt_sq hspos.le]

end BookProof.MCMC
