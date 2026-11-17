import Mathlib
import BookProof.MCMC.GaussianKernelBridge

/-!
# Chapter GaussianARBenchmark — exact Gaussian targets, bias and stability

Plan: `pcnl.md`, packet **T1** ("exact Gaussian targets that distinguish a gap from
posterior accuracy"), deliverable `GaussianARBenchmark.lean`.

The benchmark chain is the affine Gaussian autoregression

`x_{t+1} = a x_t + c + ξ_t,   ξ_t ~ N(0, σ²)`,

written as a Markov kernel `gaussianARKernel a c σ` on `ℝ`.  In the crate's coefficient
convention (plan T1) one sets `a = ρ - h κ`, `c = h b`, `h = β²/2`, `ρ = √(1-β²)`,
`σ = β²`, so the chain is the full-gradient unadjusted update of the whitened quadratic
potential `Φ(x) = κ x²/2 - b x`.

## What is proved here

* `gaussianARKernel a c σ` — the chain as a `ProbabilityTheory.Kernel ℝ ℝ`, with the Markov
  instance and state measure `κ x = N(a x + c, σ)`, plus the joint representation
  `gaussianARKernel_bind`.
* `gaussianARKernel_invariant` — the **exact stationary law**: for `a² < 1`, the law
  `N(m, s)` with `m = c/(1-a)` and `s = σ/(1-a²)` is invariant.  This is the plan's
  `π_β = N(m_β, s_β²)` formula, proved from the same Mehler pushforward as
  `GaussianKernelBridge`.
* `gaussianARKernel_integral_sub` and `gaussianARKernel_integral_sub_sq` — the first two
  **Hermite eigenvalue identities**: with `m` the stationary mean and `s` the stationary
  variance,
  `P (x ↦ x - m) = a (x - m)` and `P (x ↦ (x-m)² - s) = a² ((x-m)² - s)`.
  So the mean mode has eigenvalue `a` and the degree-2 Hermite mode eigenvalue `a²`.  The
  absolute contraction of the squared mode is `1 - a²`, while the absolute gap on mean-zero
  observables is `1 - |a|`: the two numbers the plan insists must stay distinct.
* `linearCase_mean`, `linearCase_var`, `linearCase_bias`, `linearCase_bias_bound` — at
  `κ = 0` the stationary mean is `b (1+ρ)/2`, **not** `b`, with bias exactly `-b (1-ρ)/2`,
  while the stationary variance is exactly `1`.  The bias is at most `|b| β²`: the exact
  `O(β²)` rate constant.
* `canary_mean_beta06`, `canary_unstable_kappa11` — the plan's hand-check cells:
  `β = 0.6`, `b = 1` gives `ρ = 0.8`, `h = 0.18`, stationary mean `0.9`; adding `κ = 11`
  gives `a = -1.18`, hence `|a| ≥ 1` (unstable) although the target `N(1/12, 1/12)` is a
  perfectly normalizable posterior.
* `minibatchVar` — with independent Gaussian gradient noise `N(0, v)` the innovation
  variance becomes `β² + h² v`, and the stationary variance is `(β² + h² v)/(1-a²)`: the
  exact inflation factor of mini-batch noise.

## Honest boundary

* Only the degree-1 and degree-2 Mehler eigenvalues are proved **in this chapter**.  The
  general `n`-th eigenvalue needs a Gaussian Hermite basis, which the pinned Mathlib does not
  have in the probabilists' normalisation over `ℝ`; that basis and the eigenvalue `aⁿ` are now
  in `MehlerEigenvalueReal` (`∫ Heₙ(y) ∂N(a u, 1 - a²) = aⁿ Heₙ(u)`), for the standardised
  step.  The transfer to this chapter's affine kernel at an arbitrary innovation variance is
  still open and recorded in that chapter's boundary.
* Reversibility of the affine kernel inherits the two-dimensional joint-symmetry gap
  recorded in `GaussianKernelBridge`.
* The plan's `O(β²)` claims are recorded as exact closed forms (`linearCase_bias`,
  `linearCase_bias_bound`) and exact numerical cells, not as asymptotic little-o statements.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory NNReal

/-! ## 1. The affine Gaussian benchmark kernel -/

/-- **The affine Gaussian AR kernel** `x' = a x + c + ξ`, `ξ ~ N(0, σ²)`. -/
noncomputable def gaussianARKernel (a c : ℝ) (σ : ℝ≥0) : Kernel ℝ ℝ :=
  Kernel.map (Kernel.compProd Kernel.id (Kernel.const (ℝ × ℝ) (gaussianReal 0 σ)))
    (fun p : ℝ × ℝ => a * p.1 + c + p.2)

/-- The affine Gaussian chain is a Markov kernel. -/
instance instIsMarkovKernel_gaussianARKernel (a c : ℝ) (σ : ℝ≥0) :
    IsMarkovKernel (gaussianARKernel a c σ) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- **State measure**: `κ x = N(a x + c, σ)`. -/
theorem gaussianARKernel_apply (a c : ℝ) (σ : ℝ≥0) (x : ℝ) :
    gaussianARKernel a c σ x = gaussianReal (a * x + c) σ := by
  unfold gaussianARKernel
  rw [Kernel.map_apply _ (by fun_prop) x, Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.id_apply]
  have hsect : Kernel.sectR (Kernel.const (ℝ × ℝ) (gaussianReal 0 σ)) x
      = Kernel.const ℝ (gaussianReal 0 σ) := by
    ext b s hs
    rfl
  rw [hsect, Measure.compProd_const, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rw [show ((fun p : ℝ × ℝ => a * p.1 + c + p.2) ∘ Prod.mk x)
      = (fun ξ : ℝ => ξ + (a * x + c)) from by
    funext ξ; simp
    ring]
  rw [gaussianReal_map_add_const, zero_add]

/-- The NNReal-valued square used for the stationary variance of the affine chain. -/
def nnrealSq (a : ℝ) : ℝ≥0 := ⟨a ^ 2, sq_nonneg a⟩

/-- The stationary mean of the affine chain: `m = c/(1-a)`. -/
def gaussianARMean (a c : ℝ) : ℝ := c / (1 - a)

/-- The stationary variance of the affine chain: `s = σ/(1-a²)`, for `a² < 1`. -/
def gaussianARVar (a : ℝ) (σ : ℝ≥0) (ha : a ^ 2 < 1) : ℝ≥0 :=
  ⟨(σ : ℝ) / (1 - a ^ 2), div_nonneg σ.coe_nonneg (by linarith)⟩

/-- The stationary mean identity `a m + c = m`. -/
theorem gaussianARMean_eq (a c : ℝ) (ha : a ^ 2 < 1) :
    a * gaussianARMean a c + c = gaussianARMean a c := by
  have h1 : (1 : ℝ) - a ≠ 0 := by nlinarith [ha]
  rw [gaussianARMean, mul_div_assoc', div_add' _ _ _ h1]
  exact (div_eq_div_iff h1 h1).mpr (by ring)

/-- The stationary variance identity `a² s + σ = s`, in `ℝ`. -/
theorem gaussianARVar_eq (a : ℝ) (σ : ℝ≥0) (ha : a ^ 2 < 1) :
    a ^ 2 * (gaussianARVar a σ ha : ℝ) + (σ : ℝ) = (gaussianARVar a σ ha : ℝ) := by
  have h1 : (1 : ℝ) - a ^ 2 ≠ 0 := by linarith
  rw [gaussianARVar]
  simp only [NNReal.coe_mk]
  rw [mul_div_assoc', div_add' _ _ _ h1]
  exact (div_eq_div_iff h1 h1).mpr (by ring)

/-- **The joint representation of one affine step.** -/
theorem gaussianARKernel_bind (a c : ℝ) (σ : ℝ≥0) (m : ℝ) (s : ℝ≥0) :
    (gaussianReal m s).bind (gaussianARKernel a c σ)
      = ((gaussianReal m s).prod (gaussianReal 0 σ)).map
          (fun p : ℝ × ℝ => a * p.1 + c + p.2) := by
  ext t ht
  rw [Measure.bind_apply ht (Kernel.aemeasurable _), Measure.map_apply (by fun_prop) ht,
    Measure.prod_apply (measurableSet_preimage (by fun_prop) ht)]
  refine lintegral_congr fun x => ?_
  have hset : (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => a * p.1 + c + p.2) ⁻¹' t))
      = (fun ξ : ℝ => ξ + (a * x + c)) ⁻¹' t := by
    ext ξ; simp [add_comm]
  rw [gaussianARKernel_apply, hset, ← Measure.map_apply (by fun_prop) ht,
    gaussianReal_map_add_const, zero_add]

/-- The affine pushforward of a Gaussian is Gaussian: `N(m,s).map (a· + c) = N(a m + c, a²s)`. -/
theorem gaussianReal_affine_map (a c m : ℝ) (s : ℝ≥0) :
    (gaussianReal m s).map (fun x : ℝ => a * x + c)
      = gaussianReal (a * m + c) (nnrealSq a * s) := by
  rw [show (fun x : ℝ => a * x + c) = (fun x : ℝ => x + c) ∘ (fun x : ℝ => a * x) from rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  rfl

/-- **Exact stationary law of the affine chain.**  If `a² < 1`, then `N(m, s)` with
`m = c/(1-a)` and `s = σ/(1-a²)` is invariant for `gaussianARKernel a c σ`. -/
theorem gaussianARKernel_invariant (a c : ℝ) (σ : ℝ≥0) (ha : a ^ 2 < 1) :
    (gaussianARKernel a c σ).Invariant
      (gaussianReal (gaussianARMean a c) (gaussianARVar a σ ha)) := by
  rw [ProbabilityTheory.Kernel.Invariant, gaussianARKernel_bind]
  have hcomp : (fun p : ℝ × ℝ => a * p.1 + c + p.2)
      = (fun q : ℝ × ℝ => q.1 + q.2) ∘
          (Prod.map (fun x : ℝ => a * x + c) (id : ℝ → ℝ)) := rfl
  conv_lhs => rw [hcomp]
  rw [← Measure.map_map (g := fun q : ℝ × ℝ => q.1 + q.2) (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), Measure.map_id,
    gaussianReal_affine_map]
  change Measure.conv (gaussianReal (a * gaussianARMean a c + c)
      (nnrealSq a * gaussianARVar a σ ha)) (gaussianReal 0 σ)
    = gaussianReal (gaussianARMean a c) (gaussianARVar a σ ha)
  have hvar : nnrealSq a * gaussianARVar a σ ha + σ = gaussianARVar a σ ha := by
    refine NNReal.coe_inj.mp ?_
    rw [NNReal.coe_add, NNReal.coe_mul, nnrealSq, NNReal.coe_mk]
    exact gaussianARVar_eq a σ ha
  rw [gaussianReal_conv_gaussianReal, gaussianARMean_eq a c ha, add_zero, hvar]

/-! ## 2. Gaussian moments and the Hermite eigenvalue identities -/

/-- The centred first moment of a Gaussian vanishes: `∫ y, (y - M) ∂N(M,σ) = 0`. -/
theorem integral_centered_gaussianReal (M : ℝ) (σ : ℝ≥0) :
    ∫ y, (y - M) ∂(gaussianReal M σ) = 0 := by
  have hint : Integrable (fun y : ℝ => y) (gaussianReal M σ) :=
    (memLp_id_gaussianReal (μ := M) (v := σ) 1).integrable le_rfl
  rw [integral_sub hint (integrable_const M), integral_id_gaussianReal, integral_const,
    probReal_univ, one_smul, sub_self]

/-- The centred square is integrable for a Gaussian. -/
theorem integrable_centered_sq_gaussianReal (M t : ℝ) (σ : ℝ≥0) :
    Integrable (fun y : ℝ => (y - t) ^ 2) (gaussianReal M σ) := by
  have h : MemLp (fun y : ℝ => y - t) 2 (gaussianReal M σ) :=
    (memLp_id_gaussianReal (μ := M) (v := σ) 2).sub (memLp_const t)
  simpa only [Real.norm_eq_abs, sq_abs] using h.integrable_norm_pow'

/-- The centred second moment of a Gaussian is its variance:
`∫ y, (y - M)² ∂N(M,σ) = σ`. -/
theorem integral_centered_sq_gaussianReal (M : ℝ) (σ : ℝ≥0) :
    ∫ y, (y - M) ^ 2 ∂(gaussianReal M σ) = (σ : ℝ) := by
  have h := variance_eq_integral (μ := gaussianReal M σ) (X := fun y : ℝ => y)
    measurable_id'.aemeasurable
  rw [integral_id_gaussianReal] at h
  rw [← h]
  exact variance_fun_id_gaussianReal

/-- The second moment about an arbitrary centre: `∫ y, (y-t)² ∂N(M,σ) = σ + (M-t)²`. -/
theorem integral_sq_sub_gaussianReal (M t : ℝ) (σ : ℝ≥0) :
    ∫ y, (y - t) ^ 2 ∂(gaussianReal M σ) = (σ : ℝ) + (M - t) ^ 2 := by
  have h1 : Integrable (fun y : ℝ => (y - M) ^ 2) (gaussianReal M σ) :=
    integrable_centered_sq_gaussianReal M M σ
  have h2 : Integrable (fun y : ℝ => y - M) (gaussianReal M σ) :=
    ((memLp_id_gaussianReal (μ := M) (v := σ) 1).sub (memLp_const M)).integrable le_rfl
  have hi : Integrable (fun y : ℝ => (y - M) ^ 2 + 2 * (M - t) * (y - M))
      (gaussianReal M σ) :=
    h1.add (h2.const_mul _)
  rw [show (fun y : ℝ => (y - t) ^ 2)
      = (fun y : ℝ => (y - M) ^ 2 + 2 * (M - t) * (y - M) + (M - t) ^ 2) from by
    funext y; ring]
  rw [integral_add hi (integrable_const _), integral_add h1 (h2.const_mul _),
    integral_const_mul, integral_centered_gaussianReal, integral_centered_sq_gaussianReal,
    integral_const, probReal_univ, one_smul]
  ring

/-- The first moment of the affine step: `E[x_{t+1}] = a x + c`. -/
theorem gaussianARKernel_integral_id (a c : ℝ) (σ : ℝ≥0) (x : ℝ) :
    ∫ y, y ∂(gaussianARKernel a c σ x) = a * x + c := by
  rw [gaussianARKernel_apply, integral_id_gaussianReal]

/-- **Degree-1 Hermite eigenfunction.**  With `m = c/(1-a)` the stationary mean,
`P (x ↦ x - m) = a · (x - m)`: the mean mode has eigenvalue `a`. -/
theorem gaussianARKernel_integral_sub (a c : ℝ) (σ : ℝ≥0) (ha : a ^ 2 < 1) (x : ℝ) :
    ∫ y, (y - gaussianARMean a c) ∂(gaussianARKernel a c σ x)
      = a * (x - gaussianARMean a c) := by
  have hint : Integrable (fun y : ℝ => y) (gaussianReal (a * x + c) σ) :=
    (memLp_id_gaussianReal (μ := a * x + c) (v := σ) 1).integrable le_rfl
  rw [gaussianARKernel_apply, integral_sub hint (integrable_const _), integral_id_gaussianReal,
    integral_const, probReal_univ, one_smul]
  linarith [gaussianARMean_eq a c ha]

/-- **Degree-2 Hermite eigenfunction.**  With `m = c/(1-a)` and `s = σ/(1-a²)` the
stationary moments, `P (x ↦ (x-m)² - s) = a² · ((x-m)² - s)`: the squared mode has eigenvalue
`a²`, so its absolute contraction is `1 - a²`. -/
theorem gaussianARKernel_integral_sub_sq (a c : ℝ) (σ : ℝ≥0) (ha : a ^ 2 < 1) (x : ℝ) :
    ∫ y, ((y - gaussianARMean a c) ^ 2 - (gaussianARVar a σ ha : ℝ))
        ∂(gaussianARKernel a c σ x)
      = a ^ 2 * ((x - gaussianARMean a c) ^ 2 - (gaussianARVar a σ ha : ℝ)) := by
  have hInt : Integrable (fun y : ℝ => (y - gaussianARMean a c) ^ 2)
      (gaussianReal (a * x + c) σ) :=
    integrable_centered_sq_gaussianReal (a * x + c) (gaussianARMean a c) σ
  rw [gaussianARKernel_apply, integral_sub hInt (integrable_const _),
    integral_sq_sub_gaussianReal, integral_const, probReal_univ, one_smul]
  have hcenter : a * x + c - gaussianARMean a c = a * (x - gaussianARMean a c) := by
    linarith [gaussianARMean_eq a c ha]
  rw [hcenter]
  nlinarith [gaussianARVar_eq a σ ha]

/-! ## 3. The linear canary: bias without a discretization-free mean -/

/-- In the linear cell `κ = 0` the stationary mean is `b (1+ρ)/2`; here `a = ρ`, `c = h b`
with `h = β²/2` and `ρ = √(1-β²)`. -/
theorem linearCase_mean (β b ρ : ℝ) (hβ1 : β ^ 2 ≤ 1) (hρ : ρ = Real.sqrt (1 - β ^ 2))
    (hρ1 : ρ < 1) :
    gaussianARMean ρ (β ^ 2 / 2 * b) = b * (1 + ρ) / 2 := by
  have hsq : ρ ^ 2 = 1 - β ^ 2 := by
    rw [hρ, Real.sq_sqrt (by linarith)]
  have h1 : (1 : ℝ) - ρ ≠ 0 := by linarith
  have hsq' : β ^ 2 = 1 - ρ ^ 2 := by linarith [hsq]
  rw [gaussianARMean, div_eq_iff h1, hsq']
  ring

/-- In the same cell the stationary variance is exactly `1`. -/
theorem linearCase_var (β ρ : ℝ) (hβ : 0 < β) (hβ1 : β ^ 2 ≤ 1)
    (hρ : ρ = Real.sqrt (1 - β ^ 2)) (ha : ρ ^ 2 < 1) :
    gaussianARVar ρ ⟨β ^ 2, sq_nonneg β⟩ ha = 1 := by
  have hsq : ρ ^ 2 = 1 - β ^ 2 := by
    rw [hρ, Real.sq_sqrt (by linarith)]
  refine NNReal.coe_inj.mp ?_
  simp only [gaussianARVar, NNReal.coe_mk, NNReal.coe_one]
  rw [hsq]
  field_simp
  ring

/-- The exact mean bias of the linear cell: `b(1+ρ)/2 - b = -b (1-ρ)/2`. -/
theorem linearCase_bias (β b ρ : ℝ) (hβ1 : β ^ 2 ≤ 1) (hρ : ρ = Real.sqrt (1 - β ^ 2))
    (hρ1 : ρ < 1) :
    gaussianARMean ρ (β ^ 2 / 2 * b) - b = -b * (1 - ρ) / 2 := by
  rw [linearCase_mean β b ρ hβ1 hρ hρ1]
  ring

/-- **The bias rate.**  For `0 < β ≤ 1` the mean bias factor `1-ρ` is at most `β²`. -/
theorem one_sub_sqrt_le_sq (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1 - Real.sqrt (1 - β ^ 2) ≤ β ^ 2 := by
  set ρ := Real.sqrt (1 - β ^ 2)
  have hsq : ρ ^ 2 = 1 - β ^ 2 := by
    rw [Real.sq_sqrt]; nlinarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith
  nlinarith

/-- The linear-cell mean bias is bounded by `|b| β²`. -/
theorem linearCase_bias_bound (β b : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    |gaussianARMean (Real.sqrt (1 - β ^ 2)) (β ^ 2 / 2 * b) - b| ≤ |b| * β ^ 2 := by
  have hρ1 : Real.sqrt (1 - β ^ 2) < 1 := by
    have hsq : (Real.sqrt (1 - β ^ 2)) ^ 2 = 1 - β ^ 2 := Real.sq_sqrt (by nlinarith)
    nlinarith [Real.sqrt_nonneg (1 - β ^ 2)]
  rw [linearCase_bias β b _ (by nlinarith) rfl hρ1, abs_div, abs_mul,
    abs_neg, abs_two]
  have hbound : |1 - Real.sqrt (1 - β ^ 2)| ≤ β ^ 2 := by
    rw [abs_of_nonneg (by linarith [Real.sqrt_le_one.2 (by nlinarith : 1 - β ^ 2 ≤ 1)])]
    exact one_sub_sqrt_le_sq β hβ hβ1
  nlinarith [abs_nonneg b, hbound]

/-- **The `β = 0.6` canary**: the linear cell has stationary mean `0.9` instead of `1`. -/
theorem canary_mean_beta06 :
    gaussianARMean ((0.8 : ℝ) - 0.18 * 0) (0.18 * 1) = 0.9 := by
  rw [gaussianARMean]
  norm_num

/-- **The unstable canary**: the same cell with `κ = 11` has `a = 0.8 - 0.18 * 11 = -1.18`,
so `|a| ≥ 1` — the unadjusted update is unstable. -/
theorem canary_unstable_kappa11 : (1 : ℝ) ≤ |(0.8 : ℝ) - 0.18 * 11| := by
  norm_num

/-- The intended posterior of the unstable cell is nonetheless normalizable:
`π = N(b/(1+κ), 1/(1+κ))` has positive variance `1/12`. -/
theorem canary_target_normalizable : (0 : ℝ) < 1 / (1 + 11) := by
  norm_num

/-! ## 4. Mini-batch noise inflation -/

/-- With independent Gaussian gradient noise of variance `v`, the innovation variance is
`β² + h² v` (the update's noise is `β ξ - h ζ`), and the stationary variance is therefore
`(β² + h² v)/(1-a²)`. -/
theorem minibatchVar (a β h v : ℝ) (ha : a ^ 2 < 1) (hσ : 0 ≤ β ^ 2 + h ^ 2 * v) :
    (gaussianARVar a ⟨β ^ 2 + h ^ 2 * v, hσ⟩ ha : ℝ) = (β ^ 2 + h ^ 2 * v) / (1 - a ^ 2) := by
  simp [gaussianARVar]

end BookProof.MCMC
