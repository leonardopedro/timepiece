import Mathlib
import BookProof.MCMC.GaussianPCNL2
import BookProof.MCMC.LpDescent

/-!
# Chapter LpKernelOperator — the pCN operator as a continuous linear map on `L²(π)`

Plan: `pcnl.md`, packet **T0**.  `LpMarkovOperator` proves the function-level layer
(`P f ∈ L²(π)` and `‖P f‖₂ ≤ ‖f‖₂`), and `LpDescent` proves that the action respects
`π`-almost-everywhere classes.  Both record the same remaining step: assembling the
`ContinuousLinearMap Lp ℂ 2 π →L[ℂ] Lp ℂ 2 π`.  This chapter does that assembly for the pCN
proposal.

## What is proved here

* `ae_integrable_kernel_of_aestronglyMeasurable` — **the `L²(π)` class, not a chosen
  representative, is what the a.e. integrability needs**: for an only a.e. strongly measurable
  `f` with `∫⁻ ‖f‖ₑ < ⊤`, `f` is `κ x`-integrable for `π`-almost every `x`.  The proof takes the
  strongly measurable representative `hfm.mk f`, applies `ae_integrable_kernel` to it, and
  transfers back along `κ x ≪ π`.
* `ae_integrable_kernel_of_memLp`, `ae_integrable_kernel_sq_norm_of_memLp` — the two a.e.
  integrability hypotheses of `memLp_two_kernelIntegral` and `eLpNorm_kernelIntegral_le`,
  discharged from `MemLp f 2 π` alone.  This is what removes the `StronglyMeasurable` hypothesis
  of the earlier chapters at the `Lp` level.
* `memLp_two_kernelIntegral_of_memLp` and `eLpNorm_kernelIntegral_le_of_memLp` — the same two
  statements with `MemLp f 2 π` as the only hypothesis on `f`.
* **`markovOpLp`** — **the Markov operator as a continuous linear map on `Lp ℂ 2 π`**:
  `(markovOpLp κ π f)` is the `L²(π)` class of `x ↦ ∫ y, f y ∂(κ x)`.  Linearity is proved on
  the `Lp` quotient: representatives only agree a.e., so additivity is an a.e. statement
  (`integral_add` holds off the null set where both terms fail to be integrable), which is
  exactly the descent `markovOpFun_congr` supplies.
* **`norm_markovOpLp_le_one`** — **`‖markovOpLp κ π‖ ≤ 1`**: the operator is a contraction.
* `gaussianPCNOp` — the pCN proposal packaged, `‖gaussianPCNOp ρ s‖ ≤ 1` for `ρ² + s² = 1`,
  `s ≠ 0`.

## Honest boundary

* The `Lp`-level eigenrelation `P Heₙ = ρⁿ Heₙ` is `gaussianPCNOp_hermiteReal` in
  `GaussianPCNSpectrum`; the degenerate proposal `s = 0` is there too.
* `∀ x, κ x ≪ π` is a hypothesis of the packaging, and it is what makes the pointwise action a
  function of the class (`markovOpFun_congr`).  For pCN it fails exactly at `s = 0`, and it fails
  for any kernel with a Dirac state measure; the `s = 0` action is therefore built separately,
  not through this operator.
* The Bochner integral is still junk wherever `f` is not `κ x`-integrable, but those `x` form a
  `π`-null set (`ae_integrable_kernel_of_memLp`), and every `Lp`-level statement below is
  therefore an *a.e.* statement — which is all a class-level operator may claim.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. A.e. integrability from the `L²` class -/

/-- **A.e. integrability at the state measures from a.e. strong measurability.**  The pointwise
action is only defined up to null sets, so a representative is not needed: take the strongly
measurable representative `hfm.mk f`, apply `ae_integrable_kernel` to it, and transfer the
conclusion back along `κ x ≪ π`. -/
theorem ae_integrable_kernel_of_aestronglyMeasurable {E : Type} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) (hac : ∀ x, κ x ≪ π) {f : α → E}
    (hfm : AEStronglyMeasurable f π) (hfi : ∫⁻ y, ‖f y‖ₑ ∂π ≠ ⊤) :
    ∀ᵐ x ∂π, Integrable f (κ x) := by
  have hfi' : ∫⁻ y, ‖hfm.mk f y‖ₑ ∂π ≠ ⊤ := by
    rw [lintegral_congr_ae (hfm.ae_eq_mk.mono fun y hy => by rw [← hy])]
    exact hfi
  filter_upwards [ae_integrable_kernel κ π hπ hfm.stronglyMeasurable_mk hfi' hac] with x hx
  exact hx.congr (Filter.EventuallyEq.symm
    (show f =ᵐ[κ x] hfm.mk f from (hac x).ae_le hfm.ae_eq_mk))

/-- **Every `L²(π)` class is `κ x`-integrable at `π`-almost every state.** -/
theorem ae_integrable_kernel_of_memLp (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) (hac : ∀ x, κ x ≪ π) {f : α → ℂ}
    (hf : MemLp f 2 π) : ∀ᵐ x ∂π, Integrable f (κ x) := by
  refine ae_integrable_kernel_of_aestronglyMeasurable κ π hπ hac hf.aestronglyMeasurable ?_
  rw [← eLpNorm_one_eq_lintegral_enorm]
  exact (hf.mono_exponent (by norm_num)).eLpNorm_lt_top.ne

/-- **Every squared `L²(π)` class is `κ x`-integrable at `π`-almost every state.** -/
theorem ae_integrable_kernel_sq_norm_of_memLp (κ : Kernel α α) [IsMarkovKernel κ]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : κ.Invariant π) (hac : ∀ x, κ x ≪ π)
    {f : α → ℂ} (hf : MemLp f 2 π) :
    ∀ᵐ x ∂π, Integrable (fun y => ‖f y‖ ^ 2) (κ x) := by
  have hsq : Integrable (fun y => ‖f y‖ ^ 2) π := hf.integrable_norm_pow (p := 2) (by norm_num)
  refine ae_integrable_kernel_of_aestronglyMeasurable (E := ℝ) κ π hπ hac ?_ ?_
  · exact AEStronglyMeasurable.pow (AEStronglyMeasurable.norm hf.aestronglyMeasurable) 2
  · exact (hasFiniteIntegral_iff_enorm.1 hsq.2).ne

/-- **The action preserves `L²(π)` for any class in `L²(π)`.** -/
theorem memLp_two_kernelIntegral_of_memLp (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) (hac : ∀ x, κ x ≪ π) {f : α → ℂ}
    (hf : MemLp f 2 π) : MemLp (kernelIntegral κ f) 2 π :=
  memLp_two_kernelIntegral κ π hπ hf (ae_integrable_kernel_of_memLp κ π hπ hac hf)
    (ae_integrable_kernel_sq_norm_of_memLp κ π hπ hac hf)

/-- **The norm contraction for any class in `L²(π)`.** -/
theorem eLpNorm_kernelIntegral_le_of_memLp (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) (hac : ∀ x, κ x ≪ π) {f : α → ℂ}
    (hf : MemLp f 2 π) : eLpNorm (kernelIntegral κ f) 2 π ≤ eLpNorm f 2 π :=
  eLpNorm_kernelIntegral_le κ π hπ hf.aestronglyMeasurable
    (ae_integrable_kernel_of_memLp κ π hπ hac hf)
    (ae_integrable_kernel_sq_norm_of_memLp κ π hπ hac hf)

/-! ## 2. The packaged operator -/

section Packaged

variable (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α) [IsProbabilityMeasure π]
  (hπ : κ.Invariant π) (hac : ∀ x, κ x ≪ π)

/-- The `L²(π)` class of the pointwise action, for a class `f` of `L²(π)`. -/
private def markovOpLpFun (f : Lp ℂ 2 π) : Lp ℂ 2 π :=
  (memLp_two_kernelIntegral_of_memLp κ π hπ hac (Lp.memLp f)).toLp
    (kernelIntegral κ (f : α → ℂ))

/-- The defining property of the packaged action: as a function, it is the pointwise action of
a representative, almost everywhere. -/
private theorem markovOpLpFun_coeFn (f : Lp ℂ 2 π) :
    ((markovOpLpFun κ π hπ hac f : Lp ℂ 2 π) : α → ℂ)
      =ᵐ[π] kernelIntegral κ (f : α → ℂ) :=
  MemLp.coeFn_toLp _

private theorem markovOpLpFun_add (f g : Lp ℂ 2 π) :
    markovOpLpFun κ π hπ hac (f + g) = markovOpLpFun κ π hπ hac f + markovOpLpFun κ π hπ hac g := by
  have h5 : ((f + g : Lp ℂ 2 π) : α → ℂ) =ᵐ[π] (f : α → ℂ) + (g : α → ℂ) :=
    Lp.coeFn_add f g
  apply Lp.ext
  filter_upwards [markovOpLpFun_coeFn κ π hπ hac (f + g),
    markovOpLpFun_coeFn κ π hπ hac f, markovOpLpFun_coeFn κ π hπ hac g,
    Lp.coeFn_add (markovOpLpFun κ π hπ hac f) (markovOpLpFun κ π hπ hac g),
    h5,
    ae_integrable_kernel_of_memLp κ π hπ hac (Lp.memLp f),
    ae_integrable_kernel_of_memLp κ π hπ hac (Lp.memLp g)] with x h1 h2 h3 h4 h5x hf hg
  rw [h1, h4]
  simp only [Pi.add_apply]
  rw [h2, h3]
  show kernelIntegral κ ((f + g : Lp ℂ 2 π) : α → ℂ) x
      = kernelIntegral κ (f : α → ℂ) x + kernelIntegral κ (g : α → ℂ) x
  rw [show kernelIntegral κ ((f + g : Lp ℂ 2 π) : α → ℂ) x
      = kernelIntegral κ ((f : α → ℂ) + (g : α → ℂ)) x from markovOpFun_congr κ π hac h5 x]
  exact integral_add hf hg

private theorem markovOpLpFun_smul (c : ℂ) (f : Lp ℂ 2 π) :
    markovOpLpFun κ π hπ hac (c • f) = c • markovOpLpFun κ π hπ hac f := by
  have h4 : ((c • f : Lp ℂ 2 π) : α → ℂ) =ᵐ[π] c • (f : α → ℂ) := Lp.coeFn_smul c f
  apply Lp.ext
  filter_upwards [markovOpLpFun_coeFn κ π hπ hac (c • f),
    markovOpLpFun_coeFn κ π hπ hac f,
    Lp.coeFn_smul c (markovOpLpFun κ π hπ hac f), h4] with x h1 h2 h3 h4x
  rw [h1, h3]
  simp only [Pi.smul_apply]
  rw [h2]
  show kernelIntegral κ ((c • f : Lp ℂ 2 π) : α → ℂ) x = c • kernelIntegral κ (f : α → ℂ) x
  rw [show kernelIntegral κ ((c • f : Lp ℂ 2 π) : α → ℂ) x
      = kernelIntegral κ (c • (f : α → ℂ)) x from markovOpFun_congr κ π hac h4 x]
  exact integral_smul c (f : α → ℂ)

private theorem markovOpLpFun_norm_le (f : Lp ℂ 2 π) :
    ‖markovOpLpFun κ π hπ hac f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  rw [eLpNorm_congr_ae (markovOpLpFun_coeFn κ π hπ hac f)]
  exact eLpNorm_kernelIntegral_le_of_memLp κ π hπ hac (Lp.memLp f)

/-- **The Markov operator as a continuous linear map on `Lp ℂ 2 π`.**  The hypotheses are
`π` invariant for the Markov kernel and `κ x ≪ π` for every `x` — the latter is what makes the
action depend on the `L²` class rather than on a representative. -/
noncomputable def markovOpLp : Lp ℂ 2 π →L[ℂ] Lp ℂ 2 π :=
  LinearMap.mkContinuous
    { toFun := markovOpLpFun κ π hπ hac
      map_add' := markovOpLpFun_add κ π hπ hac
      map_smul' := markovOpLpFun_smul κ π hπ hac }
    1 (by
      intro f
      show ‖markovOpLpFun κ π hπ hac f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact markovOpLpFun_norm_le κ π hπ hac f)

/-- The coercion of the packaged operator is the pointwise action of a representative,
`π`-almost everywhere. -/
theorem markovOpLp_coeFn (f : Lp ℂ 2 π) :
    ((markovOpLp κ π hπ hac f : Lp ℂ 2 π) : α → ℂ) =ᵐ[π] kernelIntegral κ (f : α → ℂ) :=
  markovOpLpFun_coeFn κ π hπ hac f

/-- **The packaged Markov operator is a contraction**, `‖markovOpLp κ π‖ ≤ 1`. -/
theorem norm_markovOpLp_le_one : ‖markovOpLp κ π hπ hac‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The pointwise contraction: `‖P f‖ ≤ ‖f‖` for every class. -/
theorem norm_markovOpLp_apply_le (f : Lp ℂ 2 π) : ‖markovOpLp κ π hπ hac f‖ ≤ ‖f‖ := by
  have h : ‖markovOpLp κ π hπ hac‖ ≤ 1 := norm_markovOpLp_le_one κ π hπ hac
  calc ‖markovOpLp κ π hπ hac f‖ ≤ ‖markovOpLp κ π hπ hac‖ * ‖f‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right h (norm_nonneg f)
    _ = ‖f‖ := one_mul _

end Packaged

/-! ## 3. The pCN proposal -/

/-- **The pCN operator on `Lp ℂ 2 (gaussianReal 0 1)`.**  For `ρ² + s² = 1` and `s ≠ 0`, the
pCN kernel is `π`-invariant with Gaussian, nondegenerate state measures, so the packaged operator
applies with no further hypothesis. -/
noncomputable def gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1) :=
  markovOpLp (gaussianPCNKernel ρ s) (gaussianReal 0 1)
    (gaussianPCNKernel_invariant ρ s hρs) (gaussianPCNKernel_absolutelyContinuous hs)

/-- **The pCN operator is a contraction.** -/
theorem norm_gaussianPCNOp_le_one (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    ‖gaussianPCNOp ρ s hρs hs‖ ≤ 1 :=
  norm_markovOpLp_le_one _ _ _ _

/-- The pCN operator acts as the pointwise pCN integral, almost everywhere. -/
theorem gaussianPCNOp_coeFn (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ((gaussianPCNOp ρ s hρs hs f : Lp ℂ 2 (gaussianReal 0 1)) : ℝ → ℂ)
      =ᵐ[gaussianReal 0 1] kernelIntegral (gaussianPCNKernel ρ s) (f : ℝ → ℂ) :=
  markovOpLp_coeFn _ _ _ _ f

end BookProof.MCMC
