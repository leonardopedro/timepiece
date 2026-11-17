import Mathlib
import BookProof.MCMC.MehlerEigenvalueReal
import BookProof.MCMC.LpKernelOperator

/-!
# Chapter GaussianPCNSpectrum — the degenerate pCN proposal and the Hermite eigenrelation

Plan: `pcnl.md`, packets **T0**/**T1**.  `LpKernelOperator` packages the pCN operator as a
contraction on `Lp ℂ 2 (gaussianReal 0 1)`, and `MehlerEigenvalueReal` proves the Mehler
eigenvalue for the standardised probabilists' Hermite polynomials.  This chapter joins the two
and treats the case the packaging deliberately excludes, `s = 0`.

## What is proved here

### The degenerate proposal `s = 0`

* `gaussianPCNKernel_zero_s` — at `s = 0` the proposal is deterministic: `κ x = dirac (ρ x)`.
* `kernelIntegral_gaussianPCNKernel_zero_s` — hence the action is evaluation: `P f x = f (ρ x)`.
* `map_const_mul_gaussianReal` — for `ρ² = 1` the map `x ↦ ρ x` preserves `π = N(0,1)`.
* `eLpNorm_gaussianPCNKernel_zero_s` — **the degenerate pCN step is an isometry of `L²(π)`**:
  `‖P f‖₂ = ‖f‖₂`, not merely a contraction.
* `memLp_two_gaussianPCNKernel_zero_s` — consequently `P` preserves `L²(π)`.
* `kernelIntegral_gaussianPCNKernel_zero_s_hermiteReal` — the eigenrelation survives `s = 0`,
  where it is the parity identity `Hen(ρ x) = ρⁿ Hen(x)`.
* `gaussianPCNOpZero_pow_toLp` — the `k`-step form `P₀ᵏ [Heₙ] = ρ^{kn} • [Heₙ]`: the degenerate
  step transports each mode by the scalar `ρ^{kn}` (no decay, since it is an isometry).

### The Hermite eigenrelation

* `memLp_two_hermiteReal` — `Hen ∈ L²(π)`.
* **`kernelIntegral_gaussianPCNKernel_hermiteReal`** — **the pCN kernel eigenrelation**:
  `P Hen = ρⁿ Hen` whenever `ρ² + s² = 1`, obtained from `mehlerHermiteReal` after identifying
  the state measure `κ x = N(ρ x, s²)` with the Mehler input `N(a u, 1 - a²)` at `a = ρ`, `u = x`.
* **`eLpNorm_gaussianPCNKernel_hermiteReal_le`** — the contraction `‖P f‖₂ ≤ ‖f‖₂` at `f = Hen`.
* **`gaussianPCNOp_hermiteReal`** — **the eigenrelation on `Lp ℂ 2 π`**: the packaged operator
  satisfies `P [Hen] = ρⁿ • [Hen]`.

## Honest boundary

* `s = 0` is a *degenerate* pCN step: `ρ² + s² = 1` then forces `ρ² = 1`, so the "proposal" is
  the identity (`ρ = 1`) or the reflection (`ρ = -1`).  Its state measure `dirac (ρ x)` is not
  absolutely continuous with respect to `π`, so `markovOpLp` — whose hypotheses include
  `∀ x, κ x ≪ π` — does not apply.  The `Lp` operator is built by a different route:
  the measure-preserving composition `f ↦ f ∘ (ρ ·)` (see `gaussianPCNOpZero` below).
* It is *not* a Markov-operator instance: `markovOpLp` needs `κ x ≪ π` for every `x`, false
  here.  It **is** a continuous linear isometry of `Lp ℂ 2 π`, though: `gaussianPCNOpZero` below
  is the composition `f ↦ f ∘ (ρ ·)` packaged through `Lp.compMeasurePreservingₗᵢ` and
  `measurePreserving_const_mul_gaussianReal`; `gaussianPCNOpZero_toLp_kernelIntegral`
  identifies its action with `kernelIntegral` on representatives.
* The eigenrelation is stated for the probabilists' Hermite polynomials `hermiteReal n` of
  `MehlerEigenvalueReal`, i.e. for the standardised prior `N(0,1)`; no rescaling to a Gaussian
  prior of another variance is claimed.
* `|ρ| ≤ 1` follows from `ρ² + s² = 1`, so `‖ρⁿ‖ ≤ 1` and the eigenrelation is consistent with
  the contraction.  No spectral-theorem statement is made *in this chapter*: eigenbasis
  completeness is proved separately in `GaussianPCNCompleteness` (`dense_span_hermiteReal`), and
  the Hilbert-basis and diagonalisation forms are in `GaussianPCNGap`.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Polynomial
open scoped ENNReal NNReal

/-- The probabilists' Hermite polynomial `Hen` viewed as a complex-valued function on `ℝ`.
The `ℂ`-valued form is what `kernelIntegral` and `eLpNorm` accept. -/
noncomputable def hermiteRealComplex (n : ℕ) : ℝ → ℂ :=
  fun y => ((Polynomial.eval y (hermiteReal n) : ℝ) : ℂ)

@[simp]
theorem hermiteRealComplex_apply (n : ℕ) (y : ℝ) :
    hermiteRealComplex n y = ((Polynomial.eval y (hermiteReal n) : ℝ) : ℂ) :=
  rfl

theorem continuous_hermiteRealComplex (n : ℕ) : Continuous (hermiteRealComplex n) :=
  Complex.continuous_ofReal.comp (Polynomial.continuous (hermiteReal n))

/-! ## 1. The degenerate proposal `s = 0` -/

/-- **At `s = 0` the pCN proposal is deterministic**: the state measure is the Dirac mass at
`ρ x`. -/
theorem gaussianPCNKernel_zero_s (ρ x : ℝ) :
    gaussianPCNKernel ρ 0 x = Measure.dirac (ρ * x) := by
  rw [gaussianPCNKernel_apply]
  have h : (fun ξ : ℝ => ρ * x + 0 * ξ) = fun _ => ρ * x := by
    funext ξ
    ring
  rw [h, Measure.map_const]
  simp

/-- **The degenerate action is evaluation** at the proposal point: `P f x = f (ρ x)`. -/
theorem kernelIntegral_gaussianPCNKernel_zero_s (ρ : ℝ) {f : ℝ → ℂ} (x : ℝ) :
    kernelIntegral (gaussianPCNKernel ρ 0) f x = f (ρ * x) := by
  unfold kernelIntegral
  rw [gaussianPCNKernel_zero_s, integral_dirac]

/-- **For `ρ² = 1`, the map `x ↦ ρ x` preserves the unit Gaussian.** -/
theorem map_const_mul_gaussianReal {ρ : ℝ} (hρ : ρ ^ 2 = 1) :
    (gaussianReal 0 1).map (fun x : ℝ => ρ * x) = gaussianReal 0 1 := by
  rw [gaussianReal_map_const_mul]
  have hvar : (⟨ρ ^ 2, sq_nonneg ρ⟩ : NNReal) * 1 = 1 := by
    rw [mul_one]
    exact Subtype.ext (by simpa using hρ)
  rw [mul_zero, hvar]

/-- **`L²(π)` is preserved isometrically by the degenerate step.** -/
theorem eLpNorm_gaussianPCNKernel_zero_s {ρ : ℝ} (hρ : ρ ^ 2 = 1) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (gaussianReal 0 1)) :
    eLpNorm (kernelIntegral (gaussianPCNKernel ρ 0) f) 2 (gaussianReal 0 1)
      = eLpNorm f 2 (gaussianReal 0 1) := by
  have hcomp : kernelIntegral (gaussianPCNKernel ρ 0) f = f ∘ fun x : ℝ => ρ * x := by
    funext x
    exact kernelIntegral_gaussianPCNKernel_zero_s ρ x
  rw [hcomp, ← eLpNorm_map_measure (μ := gaussianReal 0 1) (g := f)
    (f := fun x : ℝ => ρ * x) ?_ (by fun_prop : AEMeasurable (fun x : ℝ => ρ * x)
      (gaussianReal 0 1))]
  · rw [map_const_mul_gaussianReal hρ]
  · rw [map_const_mul_gaussianReal hρ]
    exact hf

/-- **The degenerate step preserves `L²(π)`**, with equality of norms. -/
theorem memLp_two_gaussianPCNKernel_zero_s {ρ : ℝ} (hρ : ρ ^ 2 = 1) {f : ℝ → ℂ}
    (hf : MemLp f 2 (gaussianReal 0 1)) :
    MemLp (kernelIntegral (gaussianPCNKernel ρ 0) f) 2 (gaussianReal 0 1) := by
  refine ⟨?_, ?_⟩
  · have hcomp : kernelIntegral (gaussianPCNKernel ρ 0) f = f ∘ fun x : ℝ => ρ * x := by
      funext x
      exact kernelIntegral_gaussianPCNKernel_zero_s ρ x
    rw [hcomp]
    have hmap : AEStronglyMeasurable f
        (Measure.map (fun x : ℝ => ρ * x) (gaussianReal 0 1)) := by
      rw [map_const_mul_gaussianReal hρ]
      exact hf.aestronglyMeasurable
    exact hmap.comp_measurable (by fun_prop : Measurable (fun x : ℝ => ρ * x))
  · rw [eLpNorm_gaussianPCNKernel_zero_s hρ hf.aestronglyMeasurable]
    exact hf.2

/-! ## 2. The Hermite eigenrelation -/

/-- **The probabilists' Hermite polynomials are in `L²(π)`.**  The square is a polynomial, hence
integrable against the Gaussian; `‖z‖² = normSq z` and `normSq` of a real number identifies the
`L²` integrand with that polynomial square. -/
theorem memLp_two_hermiteReal (n : ℕ) :
    MemLp (hermiteRealComplex n) 2 (gaussianReal 0 1) := by
  have hmeas : AEStronglyMeasurable (hermiteRealComplex n) (gaussianReal 0 1) :=
    (continuous_hermiteRealComplex n).stronglyMeasurable.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hpoly : Integrable
      (fun y : ℝ => (hermiteReal n).eval y * (hermiteReal n).eval y) (gaussianReal 0 1) := by
    simpa only [Polynomial.eval_mul] using
      integrable_polynomial_gaussianReal 0 1 ((hermiteReal n) * (hermiteReal n))
  refine hpoly.congr (Filter.Eventually.of_forall fun y => ?_)
  show (hermiteReal n).eval y * (hermiteReal n).eval y = ‖hermiteRealComplex n y‖ ^ 2
  rw [hermiteRealComplex_apply, Complex.sq_norm, Complex.normSq_ofReal]

/-- **The pCN kernel eigenrelation**: for `ρ² + s² = 1` the probabilists' Hermite polynomial
`Hen` satisfies `P Hen = ρⁿ Hen`, where `(P f)(x) = ∫ y, f y ∂(κ x)`.

The state measure is `κ x = N(ρ x, s²)` with `s² = 1 - ρ²`, exactly the Mehler input
`N(a u, 1 - a²)` at `a = ρ`, `u = x`; the complex-valued integral is the real one pushed through
`Complex.ofRealCLM`. -/
theorem kernelIntegral_gaussianPCNKernel_hermiteReal {ρ s : ℝ} (hρs : ρ ^ 2 + s ^ 2 = 1)
    (n : ℕ) (x : ℝ) :
    kernelIntegral (gaussianPCNKernel ρ s) (hermiteRealComplex n) x
      = (ρ ^ n : ℂ) * hermiteRealComplex n x := by
  have ha : ρ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg s]
  have hv : (⟨s ^ 2, sq_nonneg s⟩ : NNReal) * 1 = oneSubSq ρ ha := by
    apply NNReal.coe_injective
    simp only [mul_one, NNReal.coe_mk, oneSubSq]
    linarith
  unfold kernelIntegral
  rw [gaussianPCNKernel_apply_eq_gaussianReal, hv]
  have hint : Integrable (fun y : ℝ => (hermiteReal n).eval y)
      (gaussianReal (ρ * x) (oneSubSq ρ ha)) :=
    integrable_polynomial_gaussianReal _ _ _
  have hcast := Complex.ofRealCLM.integral_comp_comm (φ := fun y : ℝ => (hermiteReal n).eval y)
    hint
  change ∫ y, Complex.ofRealCLM ((hermiteReal n).eval y)
      ∂gaussianReal (ρ * x) (oneSubSq ρ ha) = (ρ ^ n : ℂ) * hermiteRealComplex n x
  rw [hcast, mehlerHermiteReal ρ ha n x]
  rw [hermiteRealComplex_apply, Complex.ofRealCLM_apply]
  push_cast
  ring

/-- **The Hermite eigenrelation survives the degenerate limit.**  At `s = 0` we have `ρ² = 1`,
and the statement is the special case `s = 0` of the general eigenrelation. -/
theorem kernelIntegral_gaussianPCNKernel_zero_s_hermiteReal {ρ : ℝ} (hρ : ρ ^ 2 = 1) (n : ℕ)
    (x : ℝ) :
    kernelIntegral (gaussianPCNKernel ρ 0) (hermiteRealComplex n) x
      = (ρ ^ n : ℂ) * hermiteRealComplex n x :=
  kernelIntegral_gaussianPCNKernel_hermiteReal (by rw [hρ]; ring) n x

/-! ## 3. The degenerate step packaged on `Lp ℂ 2 π` -/

/-- **For `ρ² = 1`, the map `x ↦ ρ x` is measure preserving** for the unit Gaussian. -/
theorem measurePreserving_const_mul_gaussianReal {ρ : ℝ} (hρ : ρ ^ 2 = 1) :
    MeasurePreserving (fun x : ℝ => ρ * x) (gaussianReal 0 1) (gaussianReal 0 1) :=
  ⟨by fun_prop, map_const_mul_gaussianReal hρ⟩

/-- **The degenerate pCN step as a continuous linear isometry of `Lp ℂ 2 π`.**  For `ρ² = 1` the
step `f ↦ f ∘ (ρ ·)` is composition with a measure-preserving map, hence an isometry; this is the
`Lp` packaging that the immeasurable density `d(dirac (ρ x))/dπ` rules out for `markovOpLp`. -/
noncomputable def gaussianPCNOpZero (ρ : ℝ) (hρ : ρ ^ 2 = 1) :
    Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1) :=
  (Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (fun x : ℝ => ρ * x)
    (measurePreserving_const_mul_gaussianReal hρ)).toContinuousLinearMap

/-- **The action of the packaged degenerate step is post-composition**: on representatives,
`f ↦ f (ρ ·)`. -/
theorem gaussianPCNOpZero_coeFn (ρ : ℝ) (hρ : ρ ^ 2 = 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    (↑↑(gaussianPCNOpZero ρ hρ f) : ℝ → ℂ) =ᵐ[gaussianReal 0 1]
      f ∘ fun x : ℝ => ρ * x :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_const_mul_gaussianReal hρ)

/-- **`gaussianPCNOpZero` is an isometry of `Lp ℂ 2 π`**: `‖P f‖₂ = ‖f‖₂`. -/
theorem norm_gaussianPCNOpZero_apply (ρ : ℝ) (hρ : ρ ^ 2 = 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ‖gaussianPCNOpZero ρ hρ f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (measurePreserving_const_mul_gaussianReal hρ)

/-- **The operator norm of the degenerate step is at most one** (it is an isometry). -/
theorem norm_gaussianPCNOpZero_le_one (ρ : ℝ) (hρ : ρ ^ 2 = 1) :
    ‖gaussianPCNOpZero ρ hρ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [norm_gaussianPCNOpZero_apply, one_mul]

/-- **The packaged degenerate step agrees with the kernel action** on representatives: for
`f ∈ L²(π)`, `P [f]` is the class of `x ↦ ∫ y, f y ∂(κ x)` with `κ x = dirac (ρ x)`. -/
theorem gaussianPCNOpZero_toLp_kernelIntegral (ρ : ℝ) (hρ : ρ ^ 2 = 1) {f : ℝ → ℂ}
    (hf : MemLp f 2 (gaussianReal 0 1)) :
    (↑↑(gaussianPCNOpZero ρ hρ (MemLp.toLp f hf)) : ℝ → ℂ) =ᵐ[gaussianReal 0 1]
      kernelIntegral (gaussianPCNKernel ρ 0) f := by
  filter_upwards [gaussianPCNOpZero_coeFn ρ hρ (MemLp.toLp f hf),
    (measurePreserving_const_mul_gaussianReal hρ).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp hf)] with x h1 h2
  rw [h1, Function.comp_apply, kernelIntegral_gaussianPCNKernel_zero_s]
  simpa only [Function.comp_apply] using h2

/-- **The degenerate eigenrelation on `Lp ℂ 2 π`**: `P [Heₙ] = ρⁿ • [Heₙ]`, with `P` the
packaged isometry `gaussianPCNOpZero` rather than the (unavailable) Markov operator. -/
theorem gaussianPCNOpZero_hermiteReal (ρ : ℝ) (hρ : ρ ^ 2 = 1) (n : ℕ) :
    gaussianPCNOpZero ρ hρ (MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n))
      = (ρ ^ n : ℂ) • MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n) := by
  apply Lp.ext
  filter_upwards [gaussianPCNOpZero_toLp_kernelIntegral ρ hρ (memLp_two_hermiteReal n),
    Lp.coeFn_smul (ρ ^ n : ℂ)
      (MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n)),
    MemLp.coeFn_toLp (memLp_two_hermiteReal n)] with x h1 h3 h2
  rw [h1, h3]
  simp only [Pi.smul_apply]
  rw [h2]
  exact kernelIntegral_gaussianPCNKernel_zero_s_hermiteReal hρ n x

/-- **The contraction, applied to a Hermite polynomial.** -/
theorem eLpNorm_gaussianPCNKernel_hermiteReal_le {ρ s : ℝ} (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) (n : ℕ) :
    eLpNorm (kernelIntegral (gaussianPCNKernel ρ s) (hermiteRealComplex n)) 2
        (gaussianReal 0 1)
      ≤ eLpNorm (hermiteRealComplex n) 2 (gaussianReal 0 1) :=
  eLpNorm_gaussianPCNKernel_le hρs hs (continuous_hermiteRealComplex n).stronglyMeasurable
    (memLp_two_hermiteReal n)

/-- **The eigenvalue statement in norm form**: `‖ρⁿ Hen‖₂ ≤ ‖Hen‖₂`, the eigenrelation read
through the contraction. -/
theorem eLpNorm_hermiteReal_eigen_le {ρ s : ℝ} (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (n : ℕ) :
    eLpNorm (fun x : ℝ => (ρ ^ n : ℂ) * hermiteRealComplex n x) 2 (gaussianReal 0 1)
      ≤ eLpNorm (hermiteRealComplex n) 2 (gaussianReal 0 1) := by
  convert eLpNorm_gaussianPCNKernel_hermiteReal_le hρs hs n using 2
  funext x
  exact (kernelIntegral_gaussianPCNKernel_hermiteReal hρs n x).symm

/-- **The eigenrelation on `Lp ℂ 2 π`**: the packaged pCN operator sends the class of `Hen` to
`ρⁿ` times the class of `Hen`. -/
theorem gaussianPCNOp_hermiteReal (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) (n : ℕ) :
    gaussianPCNOp ρ s hρs hs (MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n))
      = (ρ ^ n : ℂ) • MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n) := by
  apply Lp.ext
  filter_upwards [gaussianPCNOp_coeFn ρ s hρs hs
      (MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n)),
    MemLp.coeFn_toLp (memLp_two_hermiteReal n),
    Lp.coeFn_smul (ρ ^ n : ℂ)
      (MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n))] with x h1 h2 h3
  rw [h1, h3]
  simp only [Pi.smul_apply]
  rw [h2]
  rw [show kernelIntegral (gaussianPCNKernel ρ s)
      (⇑(MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n)) : ℝ → ℂ) x
      = kernelIntegral (gaussianPCNKernel ρ s) (hermiteRealComplex n) x
      from markovOpFun_congr _ _ (gaussianPCNKernel_absolutelyContinuous hs)
        (MemLp.coeFn_toLp (memLp_two_hermiteReal n)) x]
  exact kernelIntegral_gaussianPCNKernel_hermiteReal hρs n x

/-- **The `k`-step degenerate mode rate**: `P₀ᵏ [Heₙ] = ρ^{kn} • [Heₙ]`.  The `s = 0` step is an
isometry, so this records that the mode is *transported* rather than contracted. -/
theorem gaussianPCNOpZero_pow_toLp (ρ : ℝ) (hρ : ρ ^ 2 = 1) (k n : ℕ) :
    ((gaussianPCNOpZero ρ hρ) ^ k)
        (MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n))
      = (ρ ^ (k * n) : ℂ) • MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, gaussianPCNOpZero_hermiteReal,
      smul_smul, ← pow_add, Nat.succ_mul]

end BookProof.MCMC
