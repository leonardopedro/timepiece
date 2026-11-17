import Mathlib
import BookProof.MCMC.GaussianARBenchmark

/-!
# Chapter GaussianARIterated — the `n`-step affine Gaussian chain and its `aⁿ` structure

Plan: `pcnl.md`, packet **T1**.  `GaussianARBenchmark.lean` proves the one-step stationary
law and the degree-1/degree-2 Mehler eigenvalues.  This chapter proves the **`n`-step**
statements, which is where the `aⁿ` recursion actually lives, and which the finite-step bias
formulas of T1 need:

* `gaussianReal_bind_affine_gaussian` — one Gaussian step pushes a Gaussian mean affinely and
  adds variances: `N(m, σ₁).bind (y ↦ N(a y + b, σ₂)) = N(a m + b, a²σ₁ + σ₂)`.
* `gaussianARKernel_comp` — **the semigroup law**: composing two affine Gaussian kernels is
  again an affine Gaussian kernel,
  `κ(a₂,c₂,σ₂) ∘ₖ κ(a₁,c₁,σ₁) = κ(a₂a₁, a₂c₁+c₂, a₂²σ₁+σ₂)`.
* `gaussianARNthMean`, `gaussianARNthVar`, `gaussianARKernel_iterate` — the iterate:
  `κ^[n] = κ(aⁿ, c(1+a+…+aⁿ⁻¹), σ(1+a²+…+a²⁽ⁿ⁻¹⁾))`.  The multiplier of the `n`-step map is
  exactly `aⁿ`, which is the spectral statement P1's benchmark reads off.
* `gaussianARKernel_iterate_integral_id`, `gaussianARKernel_iterate_integral_sub` — the
  `n`-step mean and the exact finite-step bias: for `a ≠ 1`,
  `E[x_n] - m = aⁿ (x - m)` with `m = c/(1-a)` the stationary mean.
* `gaussianARNthVar_eq`, `gaussianARNthVar_tendsto` — the `n`-step variance in closed form
  `σ (1 - a²ⁿ)/(1 - a²)` and its convergence to the stationary variance for `a² < 1`.
* `canary_nthVar_linear`, `canary_nthVar_linear_three`, `canary_nthMean_linear` — the plan's
  `β = 0.6`, `b = 1`, `κ = 0` cell: `n`-step variance `1 - 0.64ⁿ` (so `0.737856` at `n = 3`),
  stationary variance exactly `1`, and `n`-step mean `0.9 + 0.8ⁿ (x - 0.9)`.

## Honest boundary (inherited and sharpened from `GaussianARBenchmark`)

The degree-`n` Mehler *eigenfunction* identity — `∫ Heₙ dκx = aⁿ Heₙ x` for the probabilists'
Hermite polynomials `Heₙ` — is **not** proved here.  It is not a matter of defining the
polynomials: Mathlib already has `Polynomial.hermite` (monic, degree `n`, the recurrence
`Heₙ₊₁ = X Heₙ - Heₙ'`, and the Rodrigues identity
`deriv^[n] exp(-x²/2) = (-1)ⁿ Heₙ(x) exp(-x²/2)`).  What is missing is the analytic input that
turns a monomial into a Gaussian moment, namely **Stein's lemma for polynomials**:

`∫ y, (y - m) p y ∂(gaussianReal m v) = v * ∫ y, deriv p y ∂(gaussianReal m v)`,

for `p : ℝ[X]`.  Given that identity, the induction on `n` is short: with
`P f x = ∫ y, f y ∂(gaussianARKernel a c σ x)` one gets `P (X f) = a X (P f) + σ P f'` and
`P f' = a (P f)'`, hence `P Heₙ₊₁ = a X (P Heₙ) + σ n aⁿ⁻¹ Heₙ₋₁ - n aⁿ⁻¹ Heₙ₋₁
= aⁿ⁺¹ Heₙ₊₁` using `1 - σ = a²`.  Stein's lemma itself follows from
`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable` applied to `u = p` and the
unnormalised Gaussian weight, and is the next concrete step for T1; it is not claimed here.

**Status update.**  Both steps now exist: `GaussianSteinLemma.integral_sub_mul_deriv_gaussianReal`
is the Stein lemma, and `MehlerEigenvalueReal.mehlerHermiteReal` is the degree-`n` identity
`∫ Heₙ(y) ∂N(a u, 1 - a²) = aⁿ Heₙ(u)` for the probabilists' Hermite polynomials `hermiteReal`,
by exactly the two-step induction described above.  What is still not proved is the transfer to
the affine kernel at an arbitrary innovation variance (the rescaling of `gaussianReal` recorded
in the boundary of `MehlerEigenvalueReal`).
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal MeasureTheory NNReal Topology

/-! ## 1. One affine Gaussian step on a Gaussian -/

/-- **Pushing a Gaussian through one affine Gaussian step.**  Sampling `N(a y + b, σ₂)` from
`y ~ N(m, σ₁)` gives `N(a m + b, a² σ₁ + σ₂)`: the mean moves affinely, the variance is scaled
by `a²` and gets the innovation variance added. -/
theorem gaussianReal_bind_gaussianARKernel (a b m : ℝ) (σ₁ σ₂ : ℝ≥0) :
    (gaussianReal m σ₁).bind (gaussianARKernel a b σ₂)
      = gaussianReal (a * m + b) (nnrealSq a * σ₁ + σ₂) := by
  have hkey : (gaussianReal m σ₁).bind (gaussianARKernel a b σ₂)
      = ((gaussianReal m σ₁).prod (gaussianReal 0 σ₂)).map
          (fun p : ℝ × ℝ => a * p.1 + b + p.2) := by
    ext t ht
    rw [Measure.bind_apply ht (Kernel.aemeasurable _), Measure.map_apply (by fun_prop) ht,
      Measure.prod_apply (measurableSet_preimage (by fun_prop) ht)]
    refine lintegral_congr fun y => ?_
    have hmap : gaussianReal (a * y + b) σ₂
        = (gaussianReal 0 σ₂).map (fun ξ : ℝ => a * y + b + ξ) := by
      rw [gaussianReal_map_const_add (μ := 0) (v := σ₂) (a * y + b)]
      norm_num
    rw [gaussianARKernel_apply a b σ₂ y, hmap, Measure.map_apply (by fun_prop) ht]
    rfl
  rw [hkey]
  conv_lhs => rw [show (fun p : ℝ × ℝ => a * p.1 + b + p.2)
      = (fun q : ℝ × ℝ => q.1 + q.2) ∘ (Prod.map (fun y : ℝ => a * y + b) id) from rfl]
  rw [← Measure.map_map (g := fun q : ℝ × ℝ => q.1 + q.2) (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), Measure.map_id,
    gaussianReal_affine_map]
  change Measure.conv (gaussianReal (a * m + b) (nnrealSq a * σ₁)) (gaussianReal 0 σ₂) = _
  rw [gaussianReal_conv_gaussianReal, add_zero]

/-! ## 2. The semigroup law -/

/-- **Composition of affine Gaussian kernels.**  Two steps of the affine Gaussian chain are one
step with multiplier `a₂ a₁`, the accumulated drift, and the accumulated innovation variance. -/
theorem gaussianARKernel_comp (a₁ c₁ : ℝ) (σ₁ : ℝ≥0) (a₂ c₂ : ℝ) (σ₂ : ℝ≥0) :
    (gaussianARKernel a₂ c₂ σ₂) ∘ₖ (gaussianARKernel a₁ c₁ σ₁)
      = gaussianARKernel (a₂ * a₁) (a₂ * c₁ + c₂) (nnrealSq a₂ * σ₁ + σ₂) := by
  ext x : 1
  rw [Kernel.comp_apply, gaussianARKernel_apply a₁ c₁ σ₁ x,
    gaussianReal_bind_gaussianARKernel, gaussianARKernel_apply]
  congr 1
  ring

/-! ## 3. The `n`-step mean and variance -/

/-- The `n`-step drift of the affine Gaussian chain: `c (1 + a + … + aⁿ⁻¹)`. -/
def gaussianARNthMean (a c : ℝ) (n : ℕ) : ℝ :=
  c * ∑ k ∈ Finset.range n, a ^ k

/-- The `n`-step innovation variance: `σ (1 + a² + … + a²⁽ⁿ⁻¹⁾)`. -/
def gaussianARNthVar (a : ℝ) (σ : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  σ * ⟨(∑ k ∈ Finset.range n, (a ^ 2) ^ k),
    Finset.sum_nonneg fun k _ => pow_nonneg (sq_nonneg a) k⟩

/-- The `n`-step drift recursion: `a * (c Sₙ) + c = c Sₙ₊₁`. -/
theorem gaussianARNthMean_succ (a c : ℝ) (n : ℕ) :
    a * gaussianARNthMean a c n + c = gaussianARNthMean a c (n + 1) := by
  unfold gaussianARNthMean
  rw [Finset.sum_range_succ', pow_zero]
  simp only [pow_succ]
  rw [← Finset.sum_mul]
  ring

/-- The real identity behind the `n`-step variance recursion. -/
theorem gaussianARNthVarSum_succ (a : ℝ) (n : ℕ) :
    a ^ 2 * (∑ k ∈ Finset.range n, (a ^ 2) ^ k) + 1
      = ∑ k ∈ Finset.range (n + 1), (a ^ 2) ^ k := by
  rw [Finset.sum_range_succ', pow_zero]
  simp only [pow_succ]
  rw [← Finset.sum_mul]
  ring

/-- The `n`-step variance recursion: `a² (σ Sₙ) + σ = σ Sₙ₊₁`. -/
theorem gaussianARNthVar_succ (a : ℝ) (σ : ℝ≥0) (n : ℕ) :
    nnrealSq a * gaussianARNthVar a σ n + σ = gaussianARNthVar a σ (n + 1) := by
  refine NNReal.coe_inj.mp ?_
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nnrealSq, gaussianARNthVar]
  have h := gaussianARNthVarSum_succ a n
  calc a ^ 2 * ((σ : ℝ) * ∑ k ∈ Finset.range n, (a ^ 2) ^ k) + (σ : ℝ)
      = (σ : ℝ) * (a ^ 2 * (∑ k ∈ Finset.range n, (a ^ 2) ^ k) + 1) := by ring
    _ = (σ : ℝ) * ∑ k ∈ Finset.range (n + 1), (a ^ 2) ^ k := by rw [h]

/-! ## 4. The iterate and the `aⁿ` bias -/

/-- The `n`-fold composition power of a Markov kernel (right-associated). -/
def kernelIterate (κ : Kernel ℝ ℝ) : ℕ → Kernel ℝ ℝ
  | 0 => Kernel.id
  | n + 1 => κ ∘ₖ kernelIterate κ n

@[simp]
theorem kernelIterate_zero (κ : Kernel ℝ ℝ) : kernelIterate κ 0 = Kernel.id := rfl

@[simp]
theorem kernelIterate_succ (κ : Kernel ℝ ℝ) (n : ℕ) :
    kernelIterate κ (n + 1) = κ ∘ₖ kernelIterate κ n := rfl

/-- **The `n`-step kernel.**  Iterating the affine Gaussian chain `n` times gives the affine
Gaussian chain with multiplier `aⁿ`. -/
theorem gaussianARKernel_iterate (a c : ℝ) (σ : ℝ≥0) (n : ℕ) :
    kernelIterate (gaussianARKernel a c σ) n
      = gaussianARKernel (a ^ n) (gaussianARNthMean a c n) (gaussianARNthVar a σ n) := by
  induction n with
  | zero =>
    have h0 : gaussianARNthVar a σ 0 = 0 := by
      simp [gaussianARNthVar]
    rw [kernelIterate_zero, h0, gaussianARNthMean, Finset.range_zero, Finset.sum_empty,
      mul_zero, pow_zero]
    ext x : 1
    rw [Kernel.id_apply, gaussianARKernel_apply]
    simp
  | succ n ih =>
    rw [kernelIterate_succ, ih, gaussianARKernel_comp, gaussianARNthMean_succ,
      gaussianARNthVar_succ, ← pow_succ']

/-- **The `n`-step mean**: `E[xₙ] = aⁿ x + c (1 + a + … + aⁿ⁻¹)`. -/
theorem gaussianARKernel_iterate_integral_id (a c : ℝ) (σ : ℝ≥0) (n : ℕ) (x : ℝ) :
    ∫ y, y ∂(kernelIterate (gaussianARKernel a c σ) n x)
      = a ^ n * x + gaussianARNthMean a c n := by
  rw [gaussianARKernel_iterate, gaussianARKernel_apply, integral_id_gaussianReal]

/-- **The geometric sum** `1 + a + … + aⁿ⁻¹ = (1 - aⁿ)/(1 - a)` for `a ≠ 1`. -/
theorem geom_sum_one_sub (a : ℝ) (ha : a ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, a ^ k = (1 - a ^ n) / (1 - a) := by
  rw [geom_sum_eq (x := a) (by simpa using ha)]
  have h1 : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have h2 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  field_simp
  ring

/-- **The exact finite-step bias.**  For `a ≠ 1` the deviation from the stationary mean `m`
decays exactly as `aⁿ`: `E[xₙ] - m = aⁿ (x - m)`.  This is the `aⁿ` recursion of P1's
benchmark, stated for the whole transient, not only at stationarity. -/
theorem gaussianARKernel_iterate_integral_sub (a c : ℝ) (σ : ℝ≥0) (n : ℕ) (x : ℝ)
    (ha : a ≠ 1) :
    ∫ y, y ∂(kernelIterate (gaussianARKernel a c σ) n x) - gaussianARMean a c
      = a ^ n * (x - gaussianARMean a c) := by
  rw [gaussianARKernel_iterate_integral_id, gaussianARMean, gaussianARNthMean,
    geom_sum_one_sub a ha n]
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  field_simp
  ring

/-! ## 5. Closed form and limit of the `n`-step variance -/

/-- **The `n`-step variance in closed form**: `σ (1 - a²ⁿ)/(1 - a²)` for `a² ≠ 1`. -/
theorem gaussianARNthVar_eq (a : ℝ) (σ : ℝ≥0) (n : ℕ) (ha : a ^ 2 ≠ 1) :
    (gaussianARNthVar a σ n : ℝ) = (σ : ℝ) * (1 - (a ^ 2) ^ n) / (1 - a ^ 2) := by
  rw [gaussianARNthVar, NNReal.coe_mul, NNReal.coe_mk,
    geom_sum_one_sub (a ^ 2) ha n]
  ring

/-- **The `n`-step variance approaches the stationary variance.**  For `a² < 1`,
`σ (1 + a² + … + a²⁽ⁿ⁻¹⁾) → σ/(1 - a²)`, which is `gaussianARVar`. -/
theorem gaussianARNthVar_tendsto (a : ℝ) (σ : ℝ≥0) (ha : a ^ 2 < 1) :
    Tendsto (fun n => (gaussianARNthVar a σ n : ℝ)) atTop
      (𝓝 ((σ : ℝ) / (1 - a ^ 2))) := by
  have h1 : (1 : ℝ) - a ^ 2 ≠ 0 := by linarith
  have h2 : ‖a ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
    exact ha
  have hpow : Tendsto (fun n : ℕ => (a ^ 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one h2
  have hlim := (((tendsto_const_nhds (x := (σ : ℝ))).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow)).div_const (1 - a ^ 2))
  simp only [mul_one, sub_zero] at hlim
  refine hlim.congr (fun n => ?_)
  rw [gaussianARNthVar_eq a σ n (by intro h; linarith [ha, h])]

/-- **T1 canary: the plan's `β = 0.6`, `b = 1`, `κ = 0` cell.**  With `ρ = 0.8`, `h = 0.18`
the chain has `a = 0.8`, `c = 0.18`, innovation variance `σ = 0.36 = 1 - 0.64`, so the
stationary variance is exactly `1` and the `n`-step variance is exactly `1 - 0.64ⁿ`.  At
`n = 3` this is `0.737856`. -/
theorem canary_nthVar_linear (n : ℕ) :
    (gaussianARNthVar 0.8 0.36 n : ℝ) = 1 - (0.64 : ℝ) ^ n := by
  rw [gaussianARNthVar_eq 0.8 0.36 n (by norm_num)]
  norm_num

/-- The same cell at `n = 3`, as an explicit decimal. -/
theorem canary_nthVar_linear_three :
    (gaussianARNthVar 0.8 0.36 3 : ℝ) = 0.737856 := by
  rw [canary_nthVar_linear]
  norm_num

/-- **T1 canary: the `n`-step mean in the same cell.**  Starting from `x`, the mean after `n`
steps is `0.8ⁿ x + 0.18 (1 + 0.8 + … + 0.8ⁿ⁻¹)`, i.e. `0.9 + 0.8ⁿ (x - 0.9)`: the transient
bias decays exactly at rate `0.8ⁿ`. -/
theorem canary_nthMean_linear (n : ℕ) (x : ℝ) :
    ∫ y, y ∂(kernelIterate (gaussianARKernel 0.8 0.18 0.36) n x)
      = 0.9 + 0.8 ^ n * (x - 0.9) := by
  rw [gaussianARKernel_iterate_integral_id, gaussianARNthMean,
    geom_sum_one_sub 0.8 (by norm_num) n]
  norm_num
  ring

end BookProof.MCMC
