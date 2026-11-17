import Mathlib
import BookProof.MCMC.GaussianKernelBridge

/-!
# Chapter GaussianReversibility — detailed balance of the Gaussian pCN proposal

Plan: `pcnl.md`, packets **T0** and **P1**.  `GaussianKernelBridge.lean` reduces
reversibility of the Gaussian proposal to the symmetry of its joint law
(`isReversible_of_swap_invariant_joint`) and records that symmetry as the boundary of that
file.  This chapter closes that boundary.

The mathematics is the classical one: the joint law of one Mehler step,
`(x, ξ) ⊢→ (x, ρ x + s ξ)` with `x, ξ` independent standard normals, has density

`g(x, y) = (2π s)⁻¹ exp(-(x² - 2ρxy + y²)/(2s²))`

with respect to Lebesgue measure on `ℝ × ℝ`, which is symmetric under `x ↔ y`.  The whole
content is the identity

`y² s² + (x - ρ y)² = x² s² + (y - ρ x)²` whenever `ρ² + s² = 1`,

which turns the cross term `-2ρxy` into the same expression in both coordinates.

Mathlib's `gaussianReal` is *defined* as `volume.withDensity (gaussianPDF μ v)`, so this
density computation is available at the pinned version: no bivariate Gaussian theory is
needed, only `gaussianPDFReal_def`.

## What is proved here

* `mehler_exponent_comm` — the arithmetic identity behind the symmetry.
* `gaussianPDFReal_mehler_comm`, `gaussianPDF_mehler_comm` — the density is symmetric.
* `gaussianPCNKernel_apply_eq_withDensity` — the state measure as a Gaussian density.
* `mehlerJointDensity`, `gaussianPCNKernel_compProd_eq` — the joint law as
  `(volume.prod volume).withDensity` of the joint density.
* `map_withDensity_prodSwap` — pushing a density through the coordinate swap.
* `gaussianPCNKernel_swap_invariant_joint` — **joint symmetry**:
  `(π ⊗ₘ κ).map Prod.swap = π ⊗ₘ κ` for `ρ² + s² = 1`, `s > 0`.
* `gaussianPCNKernel_isReversible` — **detailed balance**, via the bridge lemma.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory NNReal

/-! ## 1. The arithmetic identity -/

/-- **The Mehler exponent is symmetric.**  With `ρ² + s² = 1` the cross terms agree:

`y² s² + (x - ρ y)² = x² s² + (y - ρ x)²`.

This is the only algebraic input to the exchangeability of the joint law. -/
theorem mehler_exponent_comm (ρ s x y : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    y ^ 2 * s ^ 2 + (x - ρ * y) ^ 2 = x ^ 2 * s ^ 2 + (y - ρ * x) ^ 2 := by
  nlinarith [hρs]

/-! ## 2. The Gaussian density is symmetric -/

/-- The exponent of the joint density, `x²/2 + (y - ρ x)²/(2 s²)`, is symmetric under
swapping the coordinates when `ρ² + s² = 1`. -/
theorem mehler_exponent_div_comm (ρ s x y : ℝ) (hs : s ≠ 0) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    y ^ 2 / 2 + (x - ρ * y) ^ 2 / (2 * s ^ 2)
      = x ^ 2 / 2 + (y - ρ * x) ^ 2 / (2 * s ^ 2) := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  rw [div_add_div _ _ (by norm_num) (by positivity), div_add_div _ _ (by norm_num) (by positivity)]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [mehler_exponent_comm ρ s x y hρs]

/-- **The standard normal density at `0, 1`.** -/
theorem gaussianPDFReal_zero_one_eq (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  rw [gaussianPDFReal_def]
  norm_num

/-- **The normalised density at mean `ρ y` and variance `s²`**, with the square root pulled
off the variance: `√(2 π s²) = √(2 π) s` for `s > 0`. -/
theorem gaussianPDFReal_mehler_eq (ρ s y x : ℝ) (hs : 0 < s) :
    gaussianPDFReal (ρ * y) ⟨s ^ 2, sq_nonneg s⟩ x
      = (√(2 * Real.pi) * s)⁻¹ * Real.exp (-(x - ρ * y) ^ 2 / (2 * s ^ 2)) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_mk]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]

/-- **The joint density is symmetric in its two coordinates.** -/
theorem gaussianPDFReal_mehler_comm (ρ s x y : ℝ) (hs : 0 < s) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    gaussianPDFReal 0 1 y * gaussianPDFReal (ρ * y) ⟨s ^ 2, sq_nonneg s⟩ x
      = gaussianPDFReal 0 1 x * gaussianPDFReal (ρ * x) ⟨s ^ 2, sq_nonneg s⟩ y := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  rw [gaussianPDFReal_zero_one_eq, gaussianPDFReal_zero_one_eq,
    gaussianPDFReal_mehler_eq ρ s y x hs, gaussianPDFReal_mehler_eq ρ s x y hs]
  set c : ℝ := (√(2 * Real.pi))⁻¹
  set d : ℝ := (√(2 * Real.pi) * s)⁻¹
  have key : ∀ u v : ℝ, c * Real.exp u * (d * Real.exp v) = c * d * Real.exp (u + v) := by
    intro u v
    rw [Real.exp_add]
    ring
  rw [key, key]
  have harg : -y ^ 2 / 2 + -(x - ρ * y) ^ 2 / (2 * s ^ 2)
      = -x ^ 2 / 2 + -(y - ρ * x) ^ 2 / (2 * s ^ 2) := by
    have h := mehler_exponent_div_comm ρ s x y hs0 hρs
    linear_combination -h
  rw [harg]

/-- **Symmetry of the `ℝ≥0∞`-valued joint density** (`s > 0`, `ρ² + s² = 1`). -/
theorem gaussianPDF_mehler_comm' (ρ s x y : ℝ) (hs : 0 < s) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    gaussianPDF 0 1 y * gaussianPDF (ρ * y) ⟨s ^ 2, sq_nonneg s⟩ x
      = gaussianPDF 0 1 x * gaussianPDF (ρ * x) ⟨s ^ 2, sq_nonneg s⟩ y := by
  simp only [gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    gaussianPDFReal_mehler_comm ρ s x y hs hρs]

/-! ## 3. The state measure as a density -/

/-- The variance parameter `⟨s², _⟩` is nonzero as soon as `s` is. -/
theorem nnrealSq_ne_zero {s : ℝ} (hs : s ≠ 0) : (⟨s ^ 2, sq_nonneg s⟩ : ℝ≥0) ≠ 0 := by
  intro h
  have h' : s ^ 2 = 0 := by
    simpa using congrArg (fun v : ℝ≥0 => (v : ℝ)) h
  exact hs (pow_eq_zero_iff two_ne_zero |>.mp h')

/-- The Gaussian density is measurable in the pair `(mean, point)` when the mean is affine
in the first coordinate and the variance is fixed. -/
theorem measurable_gaussianPDF_comp (v : ℝ≥0) (c : ℝ) :
    Measurable (fun p : ℝ × ℝ => gaussianPDF (c * p.1) v p.2) := by
  have h : Measurable (fun p : ℝ × ℝ => (√(2 * Real.pi * (v : ℝ)))⁻¹ *
      Real.exp (-(p.2 - c * p.1) ^ 2 / (2 * (v : ℝ)))) := by
    fun_prop
  simpa [gaussianPDF_def, gaussianPDFReal_def] using h.ennreal_ofReal

/-- **State measure as a Gaussian density**: for `s ≠ 0` the proposal at `x` is
`volume.withDensity (gaussianPDF (ρ x) s²)`. -/
theorem gaussianPCNKernel_apply_eq_withDensity (ρ s : ℝ) (hs : s ≠ 0) (x : ℝ) :
    gaussianPCNKernel ρ s x
      = volume.withDensity (gaussianPDF (ρ * x) ⟨s ^ 2, sq_nonneg s⟩) := by
  rw [gaussianPCNKernel_apply]
  have h1 : (gaussianReal 0 1).map (fun ξ : ℝ => s * ξ)
      = gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩ := by
    simpa using gaussianReal_map_const_mul (μ := 0) (v := 1) s
  have h2 : (gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩).map (fun ξ : ℝ => ξ + ρ * x)
      = gaussianReal (ρ * x) ⟨s ^ 2, sq_nonneg s⟩ := by
    simpa using gaussianReal_map_add_const (μ := 0) (v := ⟨s ^ 2, sq_nonneg s⟩) (ρ * x)
  have hcomp : (fun ξ : ℝ => ρ * x + s * ξ)
      = (fun ξ : ℝ => ξ + ρ * x) ∘ (fun ξ : ℝ => s * ξ) := by
    funext ξ
    simp only [Function.comp_apply]
    ring
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1, h2,
    gaussianReal_of_var_ne_zero (μ := ρ * x) (nnrealSq_ne_zero hs)]

/-- **The proposal kernel is a density kernel** over `volume`: for `s ≠ 0`,
`κ = (Kernel.const ℝ volume).withDensity (x, y) ↦ gaussianPDF (ρ x) s² y`. -/
theorem gaussianPCNKernel_eq_withDensity (ρ s : ℝ) (hs : s ≠ 0) :
    gaussianPCNKernel ρ s
      = (Kernel.const ℝ volume).withDensity
          (fun x y => gaussianPDF (ρ * x) ⟨s ^ 2, sq_nonneg s⟩ y) := by
  ext x : 1
  rw [Kernel.withDensity_apply _ (measurable_gaussianPDF_comp ⟨s ^ 2, sq_nonneg s⟩ ρ),
    Kernel.const_apply, gaussianPCNKernel_apply_eq_withDensity ρ s hs x]

/-! ## 4. The joint law as a density -/

/-- **The joint density of one Mehler step.** -/
noncomputable def mehlerJointDensity (ρ s : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  gaussianPDF 0 1 p.1 * gaussianPDF (ρ * p.1) ⟨s ^ 2, sq_nonneg s⟩ p.2

/-- The joint density is a measurable function of the pair. -/
theorem measurable_mehlerJointDensity (ρ s : ℝ) : Measurable (mehlerJointDensity ρ s) := by
  unfold mehlerJointDensity
  exact Measurable.mul ((measurable_gaussianPDF 0 1).comp measurable_fst)
    (measurable_gaussianPDF_comp ⟨s ^ 2, sq_nonneg s⟩ ρ)

/-- **The joint law of one Mehler step is the Lebesgue product measure weighted by the
joint density.** -/
theorem gaussianPCNKernel_compProd_eq (ρ s : ℝ) (hs : s ≠ 0) :
    (gaussianReal 0 1) ⊗ₘ (gaussianPCNKernel ρ s)
      = (volume.prod volume).withDensity (mehlerJointDensity ρ s) := by
  have hv : (⟨s ^ 2, sq_nonneg s⟩ : ℝ≥0) ≠ 0 := nnrealSq_ne_zero hs
  haveI : IsSFiniteKernel ((Kernel.const ℝ volume).withDensity
      (fun x y => gaussianPDF (ρ * x) ⟨s ^ 2, sq_nonneg s⟩ y)) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => gaussianPDF_ne_top)
  rw [gaussianPCNKernel_eq_withDensity ρ s hs,
    Measure.compProd_withDensity (f := fun x y => gaussianPDF (ρ * x) ⟨s ^ 2, sq_nonneg s⟩ y)
      (measurable_gaussianPDF_comp ⟨s ^ 2, sq_nonneg s⟩ ρ),
    Measure.compProd_const,
    gaussianReal_of_var_ne_zero (μ := 0) (v := 1) (by norm_num),
    MeasureTheory.prod_withDensity_left (measurable_gaussianPDF 0 1),
    ← MeasureTheory.withDensity_mul _ (by fun_prop)
      (measurable_gaussianPDF_comp ⟨s ^ 2, sq_nonneg s⟩ ρ)]
  rfl

/-! ## 5. Pushing a density through the swap -/

/-- **Pushing a Lebesgue density through the coordinate swap.**  Swapping coordinates is a
measure-preserving involution of `volume.prod volume`, so its action on a density is just the
pullback of the density along the swap. -/
theorem map_withDensity_prodSwap (G : ℝ × ℝ → ℝ≥0∞) :
    ((volume.prod volume).withDensity G).map Prod.swap
      = (volume.prod volume).withDensity (fun p => G p.swap) := by
  ext s hs
  have hs' : MeasurableSet (Prod.swap ⁻¹' s) := hs.preimage measurable_swap
  rw [Measure.map_apply measurable_swap hs, withDensity_apply _ hs', withDensity_apply _ hs,
    ← lintegral_indicator hs', ← lintegral_indicator hs,
    show ∫⁻ p, s.indicator (fun p => G p.swap) p ∂volume.prod volume
        = ∫⁻ p, s.indicator (fun p => G p.swap) p.swap ∂volume.prod volume
      from (lintegral_prod_swap _).symm]
  refine lintegral_congr fun p => ?_
  by_cases hp : p.swap ∈ s
  · simp [Set.indicator_of_mem, hp]
  · simp [Set.indicator_of_notMem, hp]

/-! ## 6. Joint symmetry and detailed balance -/

/-- **Joint symmetry of one Mehler step.**  For `s > 0` and `ρ² + s² = 1` the joint law of
`(x, ρ x + s ξ)` is invariant under exchanging its two coordinates. -/
theorem gaussianPCNKernel_swap_invariant_joint (ρ s : ℝ) (hs : 0 < s)
    (hρs : ρ ^ 2 + s ^ 2 = 1) :
    ((gaussianReal 0 1) ⊗ₘ (gaussianPCNKernel ρ s)).map Prod.swap
      = (gaussianReal 0 1) ⊗ₘ (gaussianPCNKernel ρ s) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  rw [gaussianPCNKernel_compProd_eq ρ s hs0,
    map_withDensity_prodSwap _]
  refine withDensity_congr_ae (ae_of_all _ fun p => ?_)
  exact gaussianPDF_mehler_comm' ρ s p.1 p.2 hs hρs

/-- **Detailed balance of the Gaussian pCN proposal.**  For `s > 0` and `ρ² + s² = 1` the
Mehler proposal `x' = ρ x + s ξ` is reversible with respect to the standard normal. -/
theorem gaussianPCNKernel_isReversible (ρ s : ℝ) (hs : 0 < s) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    (gaussianPCNKernel ρ s).IsReversible (gaussianReal 0 1) :=
  isReversible_of_swap_invariant_joint _ _ (gaussianPCNKernel_swap_invariant_joint ρ s hs hρs)

end BookProof.MCMC
