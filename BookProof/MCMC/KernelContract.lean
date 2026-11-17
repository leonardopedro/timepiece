import Mathlib

/-!
# Chapter KernelContract — an actual reversible kernel and its `L²` action

Plan: `pcnl.md`, packet **T0** ("reuse the actual kernel API, then build its `L²` action"),
the first review gate of the current work order.

`pcnl.md` replaces the earlier coefficient-model development by a contract stated on the
*actual* kernel object: a Markov kernel `κ : Kernel α α`, a probability measure `π`, and the
observable action `(P f)(x) = ∫ f d(κ x)`.  Mathlib already supplies every definitional
ingredient — `ProbabilityTheory.Kernel`, `IsMarkovKernel`, `Kernel.Invariant` and
`Kernel.IsReversible`, together with `Kernel.IsReversible.invariant` — so this chapter
introduces no second stationarity predicate.  This is the T0 requirement: one translation,
not two.

## What is proved here

* `kernelIntegral` — the integral action `(P f)(x) = ∫ y, f y ∂(κ x)` on observables;
  `kernelIntegral_add` and `kernelIntegral_smul` record its linearity.
* `kernelIntegral_one` — **`P 1 = 1`** for a Markov kernel.
* `kernel_jensen` — **the pointwise Jensen estimate**
  `‖P f x‖² ≤ P (‖f‖²) x`, i.e. `‖∫ f d(κ x)‖² ≤ ∫ ‖f‖² d(κ x)`.
  Its proof is `‖∫ f‖ ≤ ∫ ‖f‖` followed by Jensen's inequality for the convex function
  `t ↦ t²` on `[0, ∞)` applied to `y ↦ ‖f y‖`.  (This is the plan's `|Pf(x)|² ≤ P(|f|²)(x)`,
  written in the norm conventions of Mathlib.)
* `lintegral_kernelIntegral_sq_le` — **the `L²(π)` contraction**
  `∫⁻ x, ‖P f x‖² ∂π ≤ ∫⁻ y, ‖f y‖² ∂π`, obtained by integrating the Jensen estimate
  against an invariant `π` and evaluating the resulting double integral with
  `Measure.lintegral_bind`.  A representative change is invisible here because the statement
  is one for the `ℝ≥0∞`-valued square of the norm; the descent to `Lp ℂ 2 π` is recorded as a
  boundary below.
* `lintegral_kernel_eq` — **preservation of the mean** in extended-valued form:
  `∫⁻ x, ∫⁻ y, f y ∂(κ x) ∂π = ∫⁻ y, f y ∂π` for invariant `π` and measurable `f`.
* `isReversible_const` — the **constant (prior-refresh) proposal** `Kernel.const α π` is
  reversible with respect to `π`, hence invariant by
  `Kernel.IsReversible.invariant`.  This is the kernel Q1 proposes as its exact refresh
  primitive, and it is the concrete reversible kernel of the T0 gate.
* `invariant_const` — invariance of that kernel, via the Mathlib receiver.

## Honest boundary

* The contraction is proved for the extended-valued integral of `‖P f‖²`.  The plan also asks
  for the descended continuous linear map on `Lp ℂ 2 π` and for the duality that identifies
  density evolution with the adjoint.  Those transport steps are not in this chapter: the
  pointwise Jensen bound and the invariance identity above are their two analytic inputs.
* The pinned Mathlib has `Measure.lintegral_bind` but no Bochner `integral_bind`; the mean
  identity is therefore stated in `ℝ≥0∞` form, which is what the `Lp` and Dirichlet-form
  arguments consume.  A signed Bochner version would first need the positive/negative
  decomposition transported through the bind.
* The constant proposal is reversible but is *not* a Metropolis kernel; Q1's acceptance
  filter `min 1 (L y / L x)` and its minorization `α(x,y) ≥ L(y)/M` are separate content
  (`pcnl.md` Q1), not claimed here.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. The integral action -/

/-- The action of a Markov kernel on observables: `(P f)(x) = ∫ y, f y ∂(κ x)`. -/
def kernelIntegral (κ : Kernel α α) (f : α → ℂ) (x : α) : ℂ :=
  ∫ y, f y ∂(κ x)

/-- The integral action is additive, on kernels whose state measures integrate both terms. -/
theorem kernelIntegral_add (κ : Kernel α α) (f g : α → ℂ) (x : α)
    (hf : Integrable f (κ x)) (hg : Integrable g (κ x)) :
    kernelIntegral κ (f + g) x = kernelIntegral κ f x + kernelIntegral κ g x := by
  unfold kernelIntegral
  exact integral_add hf hg

/-- The integral action is `ℂ`-homogeneous. -/
theorem kernelIntegral_smul (κ : Kernel α α) (c : ℂ) (f : α → ℂ) (x : α) :
    kernelIntegral κ (c • f) x = c • kernelIntegral κ f x := by
  unfold kernelIntegral
  exact integral_smul c f

/-- **`P 1 = 1`** for a Markov kernel: each state measure `κ x` is a probability measure. -/
theorem kernelIntegral_one (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    kernelIntegral κ (fun _ => (1 : ℂ)) x = 1 := by
  unfold kernelIntegral
  rw [integral_const]
  simp [Measure.real]

/-! ## 2. The pointwise Jensen estimate -/

/-- **Jensen for `t²` on `[0, ∞)` against a probability measure**:
`(∫ y, ‖f y‖ ∂μ)² ≤ ∫ y, ‖f y‖² ∂μ`.

This is `ConvexOn.map_integral_le` for the convex function `t ↦ t²` restricted to
`Set.Ici 0`, on which every value `‖f y‖` lies. -/
theorem sq_integral_norm_le {μ : Measure α} [IsProbabilityMeasure μ] (f : α → ℂ)
    (hf : Integrable f μ) (hfsq : Integrable (fun y => ‖f y‖ ^ 2) μ) :
    (∫ y, ‖f y‖ ∂μ) ^ 2 ≤ ∫ y, ‖f y‖ ^ 2 ∂μ := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ 2) := convexOn_pow 2
  have hcont : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Ici (0 : ℝ)) :=
    (continuous_pow 2).continuousOn
  have hmem : ∀ᵐ y ∂μ, ‖f y‖ ∈ Set.Ici (0 : ℝ) := ae_of_all _ fun y => norm_nonneg _
  have hfi : Integrable (fun y => ‖f y‖) μ := hf.norm
  have hgi : Integrable ((fun t : ℝ => t ^ 2) ∘ (fun y => ‖f y‖)) μ := hfsq
  have h := ConvexOn.map_integral_le hconv hcont isClosed_Ici hmem hfi hgi
  simpa [Function.comp] using h

/-- **The pointwise Jensen estimate for a Markov kernel**:
`‖P f x‖² ≤ P (‖f‖²) x`, i.e. `‖∫ y, f y ∂(κ x)‖² ≤ ∫ y, ‖f y‖² ∂(κ x)`.

The first factor is `norm_integral_le_integral_norm`; the second is `sq_integral_norm_le`. -/
theorem kernel_jensen (κ : Kernel α α) [IsMarkovKernel κ] (f : α → ℂ) (x : α)
    (hf : Integrable f (κ x)) (hfsq : Integrable (fun y => ‖f y‖ ^ 2) (κ x)) :
    ‖kernelIntegral κ f x‖ ^ 2 ≤ ∫ y, ‖f y‖ ^ 2 ∂(κ x) := by
  have h1 : ‖∫ y, f y ∂(κ x)‖ ≤ ∫ y, ‖f y‖ ∂(κ x) :=
    norm_integral_le_integral_norm f
  have h2 : (∫ y, ‖f y‖ ∂(κ x)) ^ 2 ≤ ∫ y, ‖f y‖ ^ 2 ∂(κ x) :=
    sq_integral_norm_le f hf hfsq
  have h3 : ‖kernelIntegral κ f x‖ ^ 2 ≤ (∫ y, ‖f y‖ ∂(κ x)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact le_trans h3 h2

/-! ## 3. The `L²(π)` contraction under invariance -/

/-- **`L²(π)` contraction of the integral action.**  If `π` is invariant for the Markov
kernel `κ` and `f` is square-integrable against every state measure, then

`∫⁻ x, ‖P f x‖² ∂π ≤ ∫⁻ y, ‖f y‖² ∂π`.

Proof: integrate `kernel_jensen` against `π`, rewrite the inner real integral as a
`lintegral` (`ofReal_integral_eq_lintegral_ofReal`), and evaluate
`∫⁻ x, ∫⁻ y, g y ∂(κ x) ∂π` by `Measure.lintegral_bind` together with
`κ.Invariant π`. -/
theorem lintegral_kernelIntegral_sq_le (κ : Kernel α α) [IsMarkovKernel κ]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : κ.Invariant π) (f : α → ℂ)
    (hf : ∀ x, Integrable f (κ x)) (hfsq : ∀ x, Integrable (fun y => ‖f y‖ ^ 2) (κ x))
    (hfm : AEMeasurable (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) π) :
    ∫⁻ x, ENNReal.ofReal (‖kernelIntegral κ f x‖ ^ 2) ∂π
      ≤ ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂π := by
  have hstep : ∀ x, ENNReal.ofReal (‖kernelIntegral κ f x‖ ^ 2)
      ≤ ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂(κ x) := by
    intro x
    refine (ENNReal.ofReal_le_ofReal (kernel_jensen κ f x (hf x) (hfsq x))).trans_eq ?_
    exact ofReal_integral_eq_lintegral_ofReal (hfsq x) (ae_of_all _ fun y => sq_nonneg _)
  calc ∫⁻ x, ENNReal.ofReal (‖kernelIntegral κ f x‖ ^ 2) ∂π
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂(κ x) ∂π :=
        lintegral_mono hstep
    _ = ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂(κ ∘ₘ π) :=
        (Measure.lintegral_bind (Kernel.aemeasurable κ)
          (by rw [show κ ∘ₘ π = π from hπ]; exact hfm)).symm
    _ = ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂π := by rw [show κ ∘ₘ π = π from hπ]

/-- **Preservation of the mean**, in extended-valued form: for invariant `π` and measurable
`f`, `∫⁻ x, ∫⁻ y, f y ∂(κ x) ∂π = ∫⁻ y, f y ∂π`.

This is `Measure.lintegral_bind` read through `κ.Invariant π`. -/
theorem lintegral_kernel_eq (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    (hπ : κ.Invariant π) {f : α → ℝ≥0∞} (hf : AEMeasurable f π) :
    ∫⁻ x, ∫⁻ y, f y ∂(κ x) ∂π = ∫⁻ y, f y ∂π := by
  have h := (Measure.lintegral_bind (Kernel.aemeasurable κ)
    (by rw [show κ ∘ₘ π = π from hπ]; exact hf)).symm
  rwa [show κ ∘ₘ π = π from hπ] at h

/-! ## 4. A concrete reversible kernel: the prior-refresh proposal -/

/-- **The constant proposal is reversible.**  The kernel `Kernel.const α π`, which ignores the
current state and proposes an independent draw from `π`, satisfies detailed balance for `π`:
both flows through measurable `A, B` equal `π A * π B`.

This is the exact prior-refresh primitive that `pcnl.md` Q1 builds its whole-state-space
Doeblin certificate on (before the Metropolis filter is applied). -/
theorem isReversible_const (π : Measure α) [IsProbabilityMeasure π] :
    Kernel.IsReversible (Kernel.const α π) π := by
  intro A B hA hB
  simp only [Kernel.const_apply]
  rw [lintegral_const, lintegral_const]
  simp [mul_comm]

/-- **Invariance of the constant proposal**, through Mathlib's reversibility receiver. -/
theorem invariant_const (π : Measure α) [IsProbabilityMeasure π] :
    Kernel.Invariant (Kernel.const α π) π :=
  (isReversible_const π).invariant

end BookProof.MCMC
