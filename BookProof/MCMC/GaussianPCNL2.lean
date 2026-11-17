import Mathlib
import BookProof.MCMC.GaussianKernelBridge
import BookProof.MCMC.LpMarkovOperator

/-!
# Chapter GaussianPCNL2 — the pCN operator on `L²(π)`, end to end

Plan: `pcnl.md`, packet **T0**.  `LpMarkovOperator` proves the abstract contraction
`‖P f‖₂ ≤ ‖f‖₂` for any `π`-invariant Markov kernel whose state measures are absolutely
continuous with respect to `π`, but leaves two hypotheses open: the `κ x`-integrability of `f`
and of `‖f‖²` at `π`-almost every state.  For the pCN proposal those are *not* free from
`f ∈ L²(π)` — the density `d(κ x)/dπ` is unbounded — and they are exactly what this chapter
discharges for the Gaussian proposal.

## What is proved here

* `gaussianPCNKernel_apply_eq_gaussianReal` — the state measures are Gaussian:
  `κ x = gaussianReal (ρ x) (s² · 1)`, from the map lemmas `gaussianReal_map_const_mul` and
  `gaussianReal_map_const_add`.
* `gaussianPCNKernel_absolutelyContinuous` — for `s ≠ 0`, every state measure is absolutely
  continuous with respect to `π = gaussianReal 0 1` (both are absolutely continuous with
  respect to Lebesgue measure, in the right order).
* `ae_integrable_gaussianPCNKernel` — **the a.e. existence of the action** for the pCN kernel:
  for any normed group `E`, a strongly measurable `f` with `∫⁻ ‖f‖ₑ < ⊤` is `κ x`-integrable
  at `π`-almost every `x`.  This is `LpMarkovOperator.ae_integrable_kernel` with the two
  hypotheses `IsMarkovKernel`/invariance/absolute continuity supplied.
* **`memLp_two_gaussianPCNKernel`** — **`P` preserves `L²(π)` for pCN**, with no integrability
  hypothesis beyond `f ∈ L²(π)` and strong measurability.
* **`eLpNorm_gaussianPCNKernel_le`** — **the contraction `‖P f‖₂ ≤ ‖f‖₂` for pCN**.

## Honest boundary

* **Status update.**  Only the function-level statement is proved *here*:
  `eLpNorm (P f) 2 π ≤ eLpNorm f 2 π`.  The packaged `ContinuousLinearMap` is
  `LpKernelOperator.gaussianPCNOp` (`norm_gaussianPCNOp_le_one`), and `GaussianPCNSpectrum`
  reads off the eigenvalue consequence on the Hermite polynomials.
* The hypotheses are `ρ ^ 2 + s ^ 2 = 1` (invariance, `gaussianPCNKernel_invariant`) and
  `s ≠ 0` (nondegeneracy of the proposal).  The degenerate case `s = 0` — a deterministic
  proposal, `κ x = dirac (ρ x)` — is excluded *from this chapter's contraction*:
  `gaussianPCNKernel_absolutelyContinuous` is false there, and so is the hypothesis
  `κ x ≪ π`.  `GaussianPCNSpectrum` treats it separately, as an isometry of `L²(π)`.
* `StronglyMeasurable f` is required, not merely `AEStronglyMeasurable f`: the argument that
  `x ↦ ∫⁻ y, ‖f y‖ₑ ∂(κ x)` is measurable in `x` (`StronglyMeasurable.lintegral_kernel`) is a
  pointwise statement, and `κ x ≪ π` is not enough to transfer it from an a.e. representative
  without choosing one.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

variable {ρ s : ℝ}

/-! ## 1. The state measures are Gaussian -/

/-- **The pCN state measures are Gaussian with mean `ρ x` and variance `s²`.** -/
theorem gaussianPCNKernel_apply_eq_gaussianReal (ρ s x : ℝ) :
    gaussianPCNKernel ρ s x = gaussianReal (ρ * x) (⟨s ^ 2, sq_nonneg s⟩ * 1) := by
  rw [gaussianPCNKernel_apply,
    show (fun ξ : ℝ => ρ * x + s * ξ) = (fun y : ℝ => ρ * x + y) ∘ fun ξ : ℝ => s * ξ from
      rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul s,
    gaussianReal_map_const_add, mul_zero, zero_add]

/-- **Every pCN state measure is absolutely continuous with respect to the prior.**  Both are
absolutely continuous with respect to Lebesgue measure; `s ≠ 0` makes the state measure
nondegenerate, which is what lets the comparison go through Lebesgue measure. -/
theorem gaussianPCNKernel_absolutelyContinuous (hs : s ≠ 0) (x : ℝ) :
    gaussianPCNKernel ρ s x ≪ gaussianReal 0 1 := by
  rw [gaussianPCNKernel_apply_eq_gaussianReal]
  have hv : (⟨s ^ 2, sq_nonneg s⟩ * 1 : ℝ≥0) ≠ 0 := by
    rw [mul_one]
    exact fun h => pow_ne_zero 2 hs (congrArg Subtype.val h)
  exact (gaussianReal_absolutelyContinuous (ρ * x) hv).trans
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero)

/-! ## 2. The action exists almost everywhere and preserves `L²(π)` -/

/-- **The pCN action exists `π`-almost everywhere.**  `LpMarkovOperator.ae_integrable_kernel`
with the kernel hypotheses of the pCN proposal supplied. -/
theorem ae_integrable_gaussianPCNKernel {E : Type} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] {f : ℝ → E} (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hf : StronglyMeasurable f) (hfi : ∫⁻ y, ‖f y‖ₑ ∂(gaussianReal 0 1) ≠ ⊤) :
    ∀ᵐ x ∂(gaussianReal 0 1), Integrable f (gaussianPCNKernel ρ s x) :=
  ae_integrable_kernel (κ := gaussianPCNKernel ρ s) (π := gaussianReal 0 1) (f := f)
    (gaussianPCNKernel_invariant ρ s hρs) hf hfi (gaussianPCNKernel_absolutelyContinuous hs)

/-- **`P` preserves `L²(π)` for the pCN proposal.**  No integrability hypothesis at the state
measures is left open: `κ x ≪ π` and the joint-measure computation supply them. -/
theorem memLp_two_gaussianPCNKernel (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {f : ℝ → ℂ}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 (gaussianReal 0 1)) :
    MemLp (kernelIntegral (gaussianPCNKernel ρ s) f) 2 (gaussianReal 0 1) := by
  have hf1 : MemLp f 1 (gaussianReal 0 1) := hf.mono_exponent (by norm_num)
  have hfi : ∫⁻ y, ‖f y‖ₑ ∂(gaussianReal 0 1) ≠ ⊤ := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact hf1.eLpNorm_lt_top.ne
  have hsq : Integrable (fun y => ‖f y‖ ^ 2) (gaussianReal 0 1) :=
    hf.integrable_norm_pow (p := 2) (by norm_num)
  have hfisq : ∫⁻ y, ‖‖f y‖ ^ 2‖ₑ ∂(gaussianReal 0 1) ≠ ⊤ :=
    (hasFiniteIntegral_iff_enorm.1 hsq.2).ne
  refine memLp_two_kernelIntegral (gaussianPCNKernel ρ s) (gaussianReal 0 1)
    (gaussianPCNKernel_invariant ρ s hρs) hf ?_ ?_
  · exact ae_integrable_gaussianPCNKernel hρs hs hfm hfi
  · exact ae_integrable_gaussianPCNKernel (E := ℝ) hρs hs (by fun_prop) hfisq

/-- **The pCN contraction `‖P f‖₂ ≤ ‖f‖₂`.** -/
theorem eLpNorm_gaussianPCNKernel_le (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {f : ℝ → ℂ}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 (gaussianReal 0 1)) :
    eLpNorm (kernelIntegral (gaussianPCNKernel ρ s) f) 2 (gaussianReal 0 1)
      ≤ eLpNorm f 2 (gaussianReal 0 1) := by
  have hf1 : MemLp f 1 (gaussianReal 0 1) := hf.mono_exponent (by norm_num)
  have hfi : ∫⁻ y, ‖f y‖ₑ ∂(gaussianReal 0 1) ≠ ⊤ := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact hf1.eLpNorm_lt_top.ne
  have hsq : Integrable (fun y => ‖f y‖ ^ 2) (gaussianReal 0 1) :=
    hf.integrable_norm_pow (p := 2) (by norm_num)
  have hfisq : ∫⁻ y, ‖‖f y‖ ^ 2‖ₑ ∂(gaussianReal 0 1) ≠ ⊤ :=
    (hasFiniteIntegral_iff_enorm.1 hsq.2).ne
  refine eLpNorm_kernelIntegral_le (gaussianPCNKernel ρ s) (gaussianReal 0 1)
    (gaussianPCNKernel_invariant ρ s hρs) hfm.aestronglyMeasurable ?_ ?_
  · exact ae_integrable_gaussianPCNKernel hρs hs hfm hfi
  · exact ae_integrable_gaussianPCNKernel (E := ℝ) hρs hs (by fun_prop) hfisq

end BookProof.MCMC
