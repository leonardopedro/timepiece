import Mathlib
import BookProof.MCMC.KernelContract

/-!
# Chapter LpMarkovOperator — the Markov operator through the joint measure

Plan: `pcnl.md`, packet **T0**.  `KernelContract` proves the pointwise Jensen estimate and the
`L²(π)` contraction `∫⁻ x, ‖P f x‖² ∂π ≤ ∫⁻ y, ‖f y‖² ∂π` for an *invariant* `π`, and
`LpDescent` proves that the action is well defined on almost-everywhere classes.  Both chapters
record the same missing ingredient: the pointwise integral `P f x = ∫ y, f y ∂(κ x)` is junk
(`0`) wherever `f` is not `κ x`-integrable, and for a Gaussian proposal the density
`d(κ x)/dπ` is unbounded, so `f ∈ L²(π)` does **not** imply `∀ x, Integrable f (κ x)`.

The docstrings of those chapters point at the sound route: read the action through the **joint
measure** `π ⊗ₘ κ` (equivalently the conditional expectation of `f ∘ snd` given the first
coordinate), where Fubini makes the integral exist *almost everywhere*.  This chapter supplies
that layer.

## What is proved here

* `fst_compProd_eq` — the first marginal of the joint measure is `π`: `(π ⊗ₘ κ).fst = π`
  (Mathlib's `Measure.fst_compProd` for a Markov kernel).
* `lintegral_comp_snd_compProd` — **the second-moment identity on the joint measure**:
  `∫⁻ z, g z.2 ∂(π ⊗ₘ κ) = ∫⁻ y, g y ∂π` for invariant `π`.  This is Fubini
  (`Measure.lintegral_bind`) together with invariance.
* **`ae_integrable_kernel`** — **the a.e. existence of the pointwise action**: if `f` is
  `π`-integrable and `κ x ≪ π` for every `x`, then `f` is `κ x`-integrable for `π`-almost every
  `x`.  This is exactly the gap both `KernelContract` and `LpDescent` describe: the pointwise
  integral is not junk off a null set, so the action is a genuine (a.e.-defined) function rather
  than an arbitrary choice of `0` on a large set.  The proof computes
  `∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(κ x) ∂π = ∫⁻ y, ‖f y‖ₑ ∂π < ∞` — the joint measure's Fubini identity —
  and concludes that the inner integral is finite for a.e. `x`.
* `lintegral_kernelIntegral_sq_le_ae` — the `L²(π)` contraction of `KernelContract`, restated
  with the *almost-everywhere* integrability hypotheses that `ae_integrable_kernel` supplies
  (the pointwise version needs them everywhere, which is what the Gaussian proposal cannot
  deliver).
* `aestronglyMeasurable_kernelIntegral` — **a.e. strong measurability of the action**, from
  `AEStronglyMeasurable.integral_kernel_comp` with the kernel read as the composition
  `κ ∘ₖ const π` (whose associated measure is `κ ∘ₘ π = π` by invariance).  No strongly
  measurable representative has to be chosen by hand.
* **`memLp_two_kernelIntegral`** — **the action preserves `L²(π)`**: for `f ∈ L²(π)` that is
  `κ x`-integrable (together with `‖f‖²`) at `π`-almost every state, `P f ∈ L²(π)`.  This is
  `memLp_two_iff_integrable_sq_norm` fed by the measurability above and the finiteness of
  `∫⁻ ‖P f‖²` from the `ℝ≥0∞` contraction.
* `enorm_rpow_two` — the bridge `‖z‖ₑ ^ (2:ℝ) = ofReal ‖z‖²` between the `eLpNorm` integrand
  and the `ofReal` integrand of the contraction.
* **`eLpNorm_kernelIntegral_le`** — **the norm contraction** `‖P f‖₂ ≤ ‖f‖₂` in `eLpNorm`
  form (`eLpNorm_eq_lintegral_rpow_enorm_toReal` together with the monotonicity of `rpow`).

## Honest boundary

* **Status update.**  The quotient step this chapter left open is supplied in
  `LpKernelOperator`: `markovOpLp` is the `ContinuousLinearMap` on `Lp ℂ 2 π` with
  `norm_markovOpLp_le_one : ‖markovOpLp κ π hπ hac‖ ≤ 1`, built by `LinearMap.mkContinuous` from
  a.e. measurability plus the norm estimate.  Representative independence needs
  `κ x ≪ π` for every `x` (`markovOpFun_congr` in `LpDescent`), so `markovOpLp` keeps that as a
  hypothesis: it is what the Gaussian proposal supplies only for `s ≠ 0`.  What is *proved*
  here is the function-level layer that packaging consumes: a.e. measurability
  (`aestronglyMeasurable_kernelIntegral`), membership in `L²(π)` (`memLp_two_kernelIntegral`)
  and the norm estimate (`eLpNorm_kernelIntegral_le`).
* The conditional-expectation identification — that the joint-measure conditional expectation
  `(π ⊗ₘ κ)[f ∘ snd | comap Prod.fst]` equals `P f ∘ Prod.fst` — is proved in
  `MarkovOperatorCondExp.condExp_compProd_eq_kernelIntegral`, not here.
* Nothing here is specific to the Gaussian proposal: the hypotheses are `IsMarkovKernel κ`,
  invariance of `π`, and `∀ x, κ x ≪ π`, all of which `GaussianKernelBridge` and
  `GaussianReversibility` discharge for pCN.  The two a.e. integrability hypotheses of
  `memLp_two_kernelIntegral` and `eLpNorm_kernelIntegral_le` are *not* discharged here for the
  Gaussian proposal (that needs the density `d(κ x)/dπ`, hence `s ≠ 0`).
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. The joint measure and its first marginal -/

/-- **The first marginal of the joint measure** `π ⊗ₘ κ` is `π`, for any Markov kernel. -/
theorem fst_compProd_eq (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α) [SFinite π] :
    (π.compProd κ).fst = π :=
  Measure.fst_compProd π κ

/-- **The second-moment identity on the joint measure.**  For a `π`-invariant Markov kernel and a
measurable `g : α → ℝ≥0∞`, integrating `g` of the second coordinate against the joint measure
`π ⊗ₘ κ` is integrating `g` against `π`.

This is Fubini for the composition product (`Measure.lintegral_bind`) followed by invariance. -/
theorem lintegral_comp_snd_compProd (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z : α × α, g z.2 ∂(π.compProd κ) = ∫⁻ y, g y ∂π := by
  rw [← lintegral_map hg measurable_snd]
  rw [show Measure.map Prod.snd (π.compProd κ) = ⇑κ ∘ₘ π from Measure.snd_compProd π κ,
    Measure.lintegral_bind (Kernel.aemeasurable κ) hg.aemeasurable]
  exact lintegral_kernel_eq κ π hπ hg.aemeasurable

/-! ## 2. The pointwise action exists almost everywhere -/

/-- **The pointwise action exists `π`-almost everywhere.**  If `f` is `π`-integrable, `π` is
invariant for the Markov kernel `κ`, and every state measure is absolutely continuous with
respect to `π`, then `f` is `κ x`-integrable for `π`-almost every `x`.

The proof is the joint-measure computation
`∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(κ x) ∂π = ∫⁻ y, ‖f y‖ₑ ∂π ≠ ⊤`: the inner integral is finite off a null
set, and `κ x ≪ π` transfers strong measurability.  Hence the Bochner integral defining
`P f x` is not junk on a set of positive measure. -/
theorem ae_integrable_kernel {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) {f : α → E} (hf : StronglyMeasurable f)
    (hfi : ∫⁻ y, ‖f y‖ₑ ∂π ≠ ⊤) (hac : ∀ x, κ x ≪ π) :
    ∀ᵐ x ∂π, Integrable f (κ x) := by
  have hinner : Measurable fun x => ∫⁻ y, ‖f y‖ₑ ∂(κ x) := hf.enorm.lintegral_kernel
  have hjoint : ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(κ x) ∂π = ∫⁻ y, ‖f y‖ₑ ∂π :=
    lintegral_kernel_eq κ π hπ hf.enorm.aemeasurable
  have hfin : ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ∂(κ x) ∂π ≠ ⊤ := by
    rw [hjoint]
    exact hfi
  filter_upwards [ae_lt_top hinner hfin] with x hx
  exact ⟨hf.aestronglyMeasurable.mono_ac (hac x), hx⟩

/-! ## 3. The `L²` contraction with almost-everywhere hypotheses -/

/-- **`L²(π)` contraction, almost-everywhere form.**  Same conclusion as
`KernelContract.lintegral_kernelIntegral_sq_le`, but the integrability of `f` and of `‖f‖²`
against the state measures is only required `π`-almost everywhere — which is what
`ae_integrable_kernel` provides for the Gaussian proposal. -/
theorem lintegral_kernelIntegral_sq_le_ae (κ : Kernel α α) [IsMarkovKernel κ]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : κ.Invariant π) (f : α → ℂ)
    (hf : ∀ᵐ x ∂π, Integrable f (κ x))
    (hfsq : ∀ᵐ x ∂π, Integrable (fun y => ‖f y‖ ^ 2) (κ x))
    (hfm : AEMeasurable (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) π) :
    ∫⁻ x, ENNReal.ofReal (‖kernelIntegral κ f x‖ ^ 2) ∂π
      ≤ ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂π := by
  have hstep : ∀ᵐ x ∂π, ENNReal.ofReal (‖kernelIntegral κ f x‖ ^ 2)
      ≤ ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂(κ x) := by
    filter_upwards [hf, hfsq] with x hx hxsq
    refine (ENNReal.ofReal_le_ofReal (kernel_jensen κ f x hx hxsq)).trans_eq ?_
    exact ofReal_integral_eq_lintegral_ofReal hxsq (ae_of_all _ fun y => sq_nonneg _)
  calc ∫⁻ x, ENNReal.ofReal (‖kernelIntegral κ f x‖ ^ 2) ∂π
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂(κ x) ∂π :=
        lintegral_mono_ae hstep
    _ = ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂(κ ∘ₘ π) :=
        (Measure.lintegral_bind (Kernel.aemeasurable κ)
          (by rw [show κ ∘ₘ π = π from hπ]; exact hfm)).symm
    _ = ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂π := by rw [show κ ∘ₘ π = π from hπ]

/-! ## 4. The action lands in `L²(π)` -/

/-- **The action is almost everywhere strongly measurable.**  For a `π`-invariant Markov kernel
and an `L²(π)` class `f`, the pointwise action `x ↦ ∫ y, f y ∂(κ x)` is a.e. strongly
measurable.  The proof reads the kernel as the composition `κ ∘ₖ const π`, whose associated
measure at every point is `κ ∘ₘ π = π` by invariance, and applies
`AEStronglyMeasurable.integral_kernel_comp`. -/
theorem aestronglyMeasurable_kernelIntegral (κ : Kernel α α) [IsMarkovKernel κ]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : κ.Invariant π) {f : α → ℂ}
    (hf : AEStronglyMeasurable f π) : AEStronglyMeasurable (fun x => ∫ y, f y ∂(κ x)) π := by
  haveI := nonempty_of_isProbabilityMeasure π
  have hcomp : AEStronglyMeasurable f ((κ ∘ₖ Kernel.const α π) (Classical.arbitrary α)) := by
    rw [show (κ ∘ₖ Kernel.const α π) (Classical.arbitrary α) = κ ∘ₘ π from by
      simp [Kernel.const_apply], hπ]
    exact hf
  have h := AEStronglyMeasurable.integral_kernel_comp (κ := Kernel.const α π) (η := κ)
    (a := Classical.arbitrary α) (f := f) hcomp
  simpa [Kernel.const_apply] using h

/-- **The action preserves `L²(π)`.**  If `f ∈ L²(π)` and `f`, `‖f‖²` are integrable at
`π`-almost every state measure, then `Pf` is again in `L²(π)`.

The proof is `memLp_two_iff_integrable_sq_norm`: a.e. strong measurability is
`aestronglyMeasurable_kernelIntegral`, and the finiteness of `∫⁻ ‖Pf‖²` is the `ℝ≥0∞`
contraction `lintegral_kernelIntegral_sq_le_ae` bounded by `∫⁻ ‖f‖² < ⊤`. -/
theorem memLp_two_kernelIntegral (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) {f : α → ℂ} (hf : MemLp f 2 π)
    (hint : ∀ᵐ x ∂π, Integrable f (κ x))
    (hintsq : ∀ᵐ x ∂π, Integrable (fun y => ‖f y‖ ^ 2) (κ x)) :
    MemLp (kernelIntegral κ f) 2 π := by
  have hA : AEStronglyMeasurable (kernelIntegral κ f) π :=
    aestronglyMeasurable_kernelIntegral κ π hπ hf.aestronglyMeasurable
  have hfm : AEMeasurable (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) π :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hf.aestronglyMeasurable.aemeasurable.norm).pow_const 2)
  have hsq : Integrable (fun y => ‖f y‖ ^ 2) π := hf.integrable_norm_pow (p := 2) (by norm_num)
  have hfin : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂π ≠ ⊤ := by
    have hlt : ∫⁻ y, ‖‖f y‖ ^ 2‖ₑ ∂π < ⊤ := hasFiniteIntegral_iff_enorm.1 hsq.2
    refine ne_of_lt ?_
    rw [← lintegral_congr fun y => Real.enorm_eq_ofReal (sq_nonneg (‖f y‖))]
    exact hlt
  refine (memLp_two_iff_integrable_sq_norm hA).2 ⟨hA.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ x, ‖‖kernelIntegral κ f x‖ ^ 2‖ₑ ∂π
      = ∫⁻ x, ENNReal.ofReal (‖kernelIntegral κ f x‖ ^ 2) ∂π :=
        lintegral_congr fun x => Real.enorm_eq_ofReal (sq_nonneg _)
    _ ≤ ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂π :=
        lintegral_kernelIntegral_sq_le_ae κ π hπ f hint hintsq hfm
    _ < ⊤ := lt_top_iff_ne_top.2 hfin

/-! ## 5. The `eLpNorm` contraction -/

/-- `‖z‖ₑ ^ (2:ℝ) = ofReal ‖z‖²`, the bridge between the `eLpNorm` integrand and the
`ofReal` integrand used by the `ℝ≥0∞` contraction. -/
theorem enorm_rpow_two (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast,
    ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg z)]

/-- **The `L²(π)` contraction, `eLpNorm` form.**  Under the same a.e. integrability
hypotheses as `memLp_two_kernelIntegral`, the action does not increase the `L²(π)` norm:
`‖Pf‖₂ ≤ ‖f‖₂`.  This is `lintegral_kernelIntegral_sq_le_ae` read through
`eLpNorm_eq_lintegral_rpow_enorm_toReal`. -/
theorem eLpNorm_kernelIntegral_le (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) {f : α → ℂ} (hfm : AEStronglyMeasurable f π)
    (hint : ∀ᵐ x ∂π, Integrable f (κ x))
    (hintsq : ∀ᵐ x ∂π, Integrable (fun y => ‖f y‖ ^ 2) (κ x)) :
    eLpNorm (kernelIntegral κ f) 2 π ≤ eLpNorm f 2 π := by
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) π :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hfm.aemeasurable.norm).pow_const 2)
  have hlin : ∫⁻ x, ‖kernelIntegral κ f x‖ₑ ^ (2 : ℝ) ∂π
      ≤ ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂π := by
    simp_rw [enorm_rpow_two]
    exact lintegral_kernelIntegral_sq_le_ae κ π hπ f hint hintsq hmeas
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  exact ENNReal.rpow_le_rpow hlin (by norm_num)

end BookProof.MCMC
