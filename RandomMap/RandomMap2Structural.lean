import Mathlib
import Mathlib.Probability.CondVar

/-!
# Structural product-measure extensions for RandomMap2

This module implements the next sound structural items R34--R37 from
`FORMALIZATION_ROADMAP.md`.

The roadmap's phrase “L² of an independent sum = tensor product” is not a
well-typed theorem without choosing a completed Hilbert tensor product and an
identification theorem. The mathematically load-bearing pure-tensor statement
is the exact factorization of its squared L² integral; this is what
`independentLpEquiv` proves below. Likewise, `productLpEquiv_cond` records the
canonical cylindrical L² linear isometry supplied by composition with the
first, measure-preserving marginal projection.
-/

open MeasureTheory ProbabilityTheory Complex

noncomputable section

namespace RandomMap2Structural

/-- The first projection of a product of probability measures is
measure-preserving. -/
theorem fst_measurePreserving {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (Prod.fst : X × Y → X) (μ.prod ν) μ :=
  measurePreserving_fst

/-- **R34.** Canonical cylindrical L² embedding along the first projection.
It is a linear isometry, so it is the precise product-L² identification needed
by the finite-head reduction. -/
noncomputable def productLpEquivCond {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst (fst_measurePreserving μ ν)

/-- The canonical product-L² embedding is represented almost everywhere by
composition with the first projection. -/
theorem productLpEquiv_cond {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Lp ℂ 2 μ) :
    (productLpEquivCond μ ν f : X × Y → ℂ) =ᵐ[μ.prod ν]
      (fun z => f z.1) := by
  simpa [productLpEquivCond] using
    Lp.coeFn_compMeasurePreserving f (fst_measurePreserving μ ν)

/-- **R35 (sound pure-tensor form).** For independent factors, the squared
L² integral of a pure tensor factors exactly into the product of the squared
integrals. This is the concrete product-measure identity required by RandomMap2,
without asserting an unchosen global Hilbert-tensor-space equivalence.

This integral identity in fact holds without separate integrability hypotheses:
Mathlib's Bochner integral convention assigns zero to non-integrable functions. -/
theorem independentLpEquiv {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → ℂ) (g : Y → ℂ) :
    ∫ z : X × Y, ‖f z.1 * g z.2‖ ^ 2 ∂(μ.prod ν) =
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ y, ‖g y‖ ^ 2 ∂ν) := by
  rw [← MeasureTheory.integral_prod_mul]
  simp only [norm_mul, mul_pow]

/-- **R36.** Expectation under the first marginal agrees with expectation of
its pullback to the product probability space. -/
theorem marginal_expectation_eq {X Y E : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → E) (hf : Integrable f μ) :
    ∫ z : X × Y, f z.1 ∂(μ.prod ν) = ∫ x, f x ∂μ := by
  rw [← MeasureTheory.integral_map]
  · rw [(fst_measurePreserving μ ν).map_eq]
  · exact measurable_fst.aemeasurable
  · rw [(fst_measurePreserving μ ν).map_eq]
    exact hf.aestronglyMeasurable

/-- **R37.** The expected conditional variance is at most the unconditional
variance. This is the inequality part of the law of total variance. -/
theorem conditional_variance_bound {Ω : Type*}
    {m₀ m : MeasurableSpace Ω} (hm : m ≤ m₀)
    (μ : Measure[m₀] Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    ∫ ω, (Var[X; μ | m]) ω ∂μ ≤ Var[X; μ] := by
  have htotal := integral_condVar_add_variance_condExp hm hX
  have hnonneg : 0 ≤ Var[μ[X | m]; μ] := variance_nonneg _ _
  linarith

end RandomMap2Structural
