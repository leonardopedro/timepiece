import Mathlib
import BookProof.MCMC.LpMarkovOperator

/-!
# Chapter MarkovOperatorCondExp — the joint-measure conditional expectation

Plan: `pcnl.md`, packet **T0**.  The boundary of `LpMarkovOperator` records the two steps that
stand between the joint-measure layer and the `L²` Markov operator: the identification of the
conditional expectation `(π ⊗ₘ κ)[f ∘ snd | comap Prod.fst]` with `P f ∘ Prod.fst`, and the
`Lp` assembly.  This chapter supplies the integrability layer that identification needs, stated
in the exact form `ae_eq_condExp_of_forall_setIntegral_eq` consumes:

* `integrable_comp_snd_compProd` — `f ∈ L¹(π)` implies `f ∘ snd ∈ L¹(π ⊗ₘ κ)` (for invariant
  `π`), via `Measure.integrable_compProd_snd_iff`.
* `integrable_comp_fst_compProd` — a function of the **first** coordinate is `π ⊗ₘ κ`-integrable
  iff it is `π`-integrable (the first marginal is `π`), via `integrable_map_measure`.
* `integrable_kernelIntegral_compProd` — **the candidate conditional expectation is
  integrable**: `z ↦ ∫ y, f y ∂(κ z.1)` is `π ⊗ₘ κ`-integrable whenever `f` is `π`-integrable.
  The dominating function is `z ↦ ∫ y, ‖f y‖ ∂(κ z.1)`, which is `π`-integrable by
  `integrable_integral_norm_of_integrable_comp` and then lifted along `Prod.fst`.
* `aestronglyMeasurable_kernelIntegral_compProd` — the same function is a.e. strongly measurable,
  from `StronglyMeasurable.integral_kernel` composed with `Prod.fst`.

## What was the boundary, and its status

The identity itself — the piece `LpMarkovOperator` recorded as missing — is now
`condExp_compProd_eq_kernelIntegral`:

`(π ⊗ₘ κ)[f ∘ snd | comap Prod.fst] =ᵐ[π ⊗ₘ κ] fun z => ∫ y, f y ∂(κ z.1)`.

The two ingredients are `MeasurableSpace.measurableSet_comap` (a `comap Prod.fst`-measurable set
is `Prod.fst ⁻¹' T` for a measurable `T`, i.e. `T ×ˢ univ`) and `Measure.setIntegral_compProd`
(restricted Fubini over such a product set); on the right-hand side the inner integral of the
constant `∫ y, f y ∂(κ a)` against the probability measure `κ a` is itself.

## Honest boundary

* The statement is for `f ∈ L¹(π)` (expressed as `StronglyMeasurable f` plus
  `∫⁻ ‖f‖ₑ ∂π ≠ ⊤`).  The `L²` version, the `Lp` quotient and the continuous linear map
  `Lp ℂ 2 π →L[ℂ] Lp ℂ 2 π` with `‖P f‖ ≤ ‖f‖` remain undone; the norm bound would combine
  `eLpNorm_condExp_le` (Mathlib) with the a.e. contraction in `LpMarkovOperator`.
* No Gaussian-specific input is used: only `IsMarkovKernel κ`, invariance of `π`, and
  `f ∈ L¹(π)`.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. Integrability on the joint measure -/

/-- **`f ∘ snd` is `π ⊗ₘ κ`-integrable** when `f` is `π`-integrable and `π` is invariant. -/
theorem integrable_comp_snd_compProd (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) {f : α → ℂ} (hf : Integrable f π) :
    Integrable (fun z : α × α => f z.2) (π ⊗ₘ κ) := by
  have hcomp : κ ∘ₘ π = π := hπ
  refine (Measure.integrable_compProd_snd_iff (μ := π) (κ := κ) ?_).2 ?_
  · rw [hcomp]
    exact hf.1
  · rw [hcomp]
    exact hf

/-- **A function of the first coordinate is `π ⊗ₘ κ`-integrable iff it is `π`-integrable**: the
first marginal of the joint measure is `π`. -/
theorem integrable_comp_fst_compProd (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [SFinite π] {E : Type*} [NormedAddCommGroup E] {F : α → E} (hF : Integrable F π) :
    Integrable (fun z : α × α => F z.1) (π ⊗ₘ κ) := by
  have hmap : Measure.map Prod.fst (π ⊗ₘ κ) = π := Measure.fst_compProd π κ
  have hg : AEStronglyMeasurable F (Measure.map Prod.fst (π ⊗ₘ κ)) := by
    rw [hmap]
    exact hF.1
  have h := (integrable_map_measure hg measurable_fst.aemeasurable).mp ?_
  · simpa only [Function.comp_def] using h
  · rw [hmap]
    exact hF

/-- **The kernel integral is a.e. strongly measurable on the joint measure**, as a function of
the first coordinate. -/
theorem aestronglyMeasurable_kernelIntegral_compProd (κ : Kernel α α) {f : α → ℂ}
    (hf : StronglyMeasurable f) (π : Measure α) [SFinite π] :
    AEStronglyMeasurable (fun z : α × α => ∫ y, f y ∂(κ z.1)) (π ⊗ₘ κ) :=
  ((hf.integral_kernel (κ := κ)).comp_measurable measurable_fst).aestronglyMeasurable

/-- **The candidate conditional expectation is `π ⊗ₘ κ`-integrable.**  For `π`-invariant `κ` and
strongly measurable `f` with `f ∈ L¹(π)`, the function `z ↦ ∫ y, f y ∂(κ z.1)` is integrable
against the joint measure: it is dominated by `z ↦ ∫ y, ‖f y‖ ∂(κ z.1)`, which is a function of
the first coordinate, `π`-integrable by `integrable_integral_norm_of_integrable_comp`. -/
theorem integrable_kernelIntegral_compProd (κ : Kernel α α) [IsMarkovKernel κ]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : κ.Invariant π) {f : α → ℂ}
    (hf : StronglyMeasurable f) (hfi : ∫⁻ y, ‖f y‖ₑ ∂π ≠ ⊤) :
    Integrable (fun z : α × α => ∫ y, f y ∂(κ z.1)) (π ⊗ₘ κ) := by
  have hcomp : κ ∘ₘ π = π := hπ
  have hfint : Integrable f π := ⟨hf.aestronglyMeasurable, lt_top_iff_ne_top.2 hfi⟩
  set D : α → ℝ := fun x => ∫ y, ‖f y‖ ∂(κ x) with hD
  have hdomπ : Integrable D π := by
    rw [hD]
    refine Measure.integrable_integral_norm_of_integrable_comp (μ := π) (κ := κ) ?_
    rw [hcomp]
    exact hfint
  have hdom : Integrable (fun z : α × α => D z.1) (π ⊗ₘ κ) :=
    integrable_comp_fst_compProd (F := D) κ π hdomπ
  refine Integrable.mono' hdom (aestronglyMeasurable_kernelIntegral_compProd κ hf π) ?_
  exact Eventually.of_forall fun z => by
    rw [hD]
    exact norm_integral_le_integral_norm f

/-- The candidate conditional expectation is a.e. strongly measurable **with respect to the
conditioning σ-algebra** `comap Prod.fst m`, which is what the defining property of the
conditional expectation asks for. -/
theorem aestronglyMeasurable_kernelIntegral_comap (κ : Kernel α α) {f : α → ℂ}
    (hf : StronglyMeasurable f) (π : Measure α) [SFinite π] :
    AEStronglyMeasurable[MeasurableSpace.comap Prod.fst ‹MeasurableSpace α›]
      (fun z : α × α => ∫ y, f y ∂(κ z.1)) (π ⊗ₘ κ) := by
  have hH : StronglyMeasurable (fun x => ∫ y, f y ∂(κ x)) := hf.integral_kernel (κ := κ)
  have hfst : Measurable[MeasurableSpace.comap Prod.fst ‹MeasurableSpace α›]
      (Prod.fst : α × α → α) := by
    rw [measurable_iff_comap_le]
  exact (hH.comp_measurable hfst).aestronglyMeasurable

/-! ## 2. The conditional-expectation identification -/

omit [MeasurableSpace α] in
/-- A preimage under `Prod.fst` is the product set `T ×ˢ univ`. -/
theorem fst_preimage_eq_prod (T : Set α) :
    (Prod.fst ⁻¹' T : Set (α × α)) = T ×ˢ (Set.univ : Set α) := by
  ext p
  simp

/-- **The kernel integral is `π`-integrable.**  If `f` is strongly measurable and `f ∈ L¹(π)`,
then `x ↦ ∫ y, f y ∂(κ x)` is `π`-integrable: it is dominated by
`x ↦ ∫ y, ‖f y‖ ∂(κ x)`. -/
theorem integrable_kernelIntegral (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    [IsProbabilityMeasure π] (hπ : κ.Invariant π) {f : α → ℂ} (hf : StronglyMeasurable f)
    (hfi : ∫⁻ y, ‖f y‖ₑ ∂π ≠ ⊤) :
    Integrable (fun x => ∫ y, f y ∂(κ x)) π := by
  have hcomp : κ ∘ₘ π = π := hπ
  have hfint : Integrable f π := ⟨hf.aestronglyMeasurable, lt_top_iff_ne_top.2 hfi⟩
  set D : α → ℝ := fun x => ∫ y, ‖f y‖ ∂(κ x) with hD
  have hDint : Integrable D π := by
    rw [hD]
    refine Measure.integrable_integral_norm_of_integrable_comp (μ := π) (κ := κ) (f := f) ?_
    rw [hcomp]
    exact hfint
  refine Integrable.mono' hDint (hf.integral_kernel (κ := κ)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by
    rw [hD]
    exact norm_integral_le_integral_norm f

/-- **The joint-measure conditional expectation is the kernel integral.**  For a `π`-invariant
Markov kernel and `f ∈ L¹(π)` strongly measurable,

`(π ⊗ₘ κ)[f ∘ snd | comap Prod.fst] =ᵐ[π ⊗ₘ κ] fun z => ∫ y, f y ∂(κ z.1)`.

Proof: the defining property of the conditional expectation
(`ae_eq_condExp_of_forall_setIntegral_eq`).  A `comap Prod.fst`-measurable set is
`Prod.fst ⁻¹' T` for some measurable `T` (`measurableSet_comap`), i.e. the product set
`T ×ˢ univ`; on such a set both sides reduce, by `Measure.setIntegral_compProd`, to the same
iterated integral `∫ a in T, ∫ y, f y ∂(κ a) ∂π` — on the right because `κ a` is a probability
measure, so the inner integral of the constant `∫ y, f y ∂(κ a)` is itself. -/
theorem condExp_compProd_eq_kernelIntegral (κ : Kernel α α) [IsMarkovKernel κ]
    (π : Measure α) [IsProbabilityMeasure π] (hπ : κ.Invariant π) {f : α → ℂ}
    (hf : StronglyMeasurable f) (hfi : ∫⁻ y, ‖f y‖ₑ ∂π ≠ ⊤) :
    (π ⊗ₘ κ)[(fun z : α × α => f z.2) | MeasurableSpace.comap Prod.fst ‹MeasurableSpace α›]
      =ᵐ[π ⊗ₘ κ] fun z => ∫ y, f y ∂(κ z.1) := by
  have hle : MeasurableSpace.comap Prod.fst ‹MeasurableSpace α› ≤
      (inferInstance : MeasurableSpace (α × α)) :=
    measurable_fst.comap_le
  have hfint : Integrable f π := ⟨hf.aestronglyMeasurable, lt_top_iff_ne_top.2 hfi⟩
  have hg : Integrable (fun z : α × α => f z.2) (π ⊗ₘ κ) :=
    integrable_comp_snd_compProd κ π hπ hfint
  have hHint : Integrable (fun x => ∫ y, f y ∂(κ x)) π := integrable_kernelIntegral κ π hπ hf hfi
  have hH : Integrable (fun z : α × α => ∫ y, f y ∂(κ z.1)) (π ⊗ₘ κ) :=
    integrable_comp_fst_compProd (F := fun x => ∫ y, f y ∂(κ x)) κ π hHint
  refine (ae_eq_condExp_of_forall_setIntegral_eq (m₀ := Prod.instMeasurableSpace) hle hg ?_ ?_
    (aestronglyMeasurable_kernelIntegral_comap κ hf π)).symm
  · intro s _ _
    exact hH.integrableOn
  · intro s hs _
    obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    rw [fst_preimage_eq_prod,
      Measure.setIntegral_compProd hT MeasurableSet.univ hH.integrableOn,
      Measure.setIntegral_compProd hT MeasurableSet.univ hg.integrableOn]
    congr 1 with a
    simp

end BookProof.MCMC
