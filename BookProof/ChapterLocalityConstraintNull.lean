import Mathlib

/-!
# The local velocity constraint has null measure

Source: `book.tex`, chapter *"Gauge symmetry and dissipative dynamics in probability
spaces"*, §*"Balancing discretization and locality"* (`book.tex` line ~2487), closing
paragraph:

> *"The main difficulty lies in defining a probability measure when the velocity is
> constrained by the position at each time, since the subset defined by the constraints
> has null measure when considering the Gaussian measure for the position and
> (unconstrained) velocity."*

This file proves that statement, in the generality in which it is used: the *constraint
set* is the graph

```
graphSet f = { (x, v) | v = f x }
```

of the map `f` expressing the constrained variable (the velocity) in terms of the free one
(the position), and the claim is that it is a null set for **every** product measure whose
second factor is atomless — in particular for a Gaussian law on the unconstrained velocity,
and for the two-dimensional Lebesgue measure.

The mechanism is Fubini: every vertical section of the graph is the single point `f x`, and
an atomless measure gives no mass to a point.  The consequence the chapter draws is also
recorded: the naive conditioning of the joint law on the constraint is not a probability
measure — the restricted measure is identically zero (`restrict_graphSet_eq_zero`), so a
coherent "uncertainty after the constraint" must be built differently (which is what the
wave-function parametrization of the other chapters does).

## Main results

* `graphSet_null` — the constraint set is null for `μ.prod ν` whenever `ν` is atomless.
* `graphSet_volume_null` — the two-dimensional Lebesgue special case.
* `graphSet_gaussian_null` — the Gaussian special case stated in the book.
* `restrict_graphSet_eq_zero`, `not_isProbabilityMeasure_restrict_graphSet` — conditioning
  the joint law on the constraint yields the zero measure, not a probability measure.
-/

namespace BookProof.LocalityConstraint

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

/-- The constraint set: the graph of the map `f` giving the constrained variable (the
velocity) as a function of the free variable (the position). -/
def graphSet (f : α → ℝ) : Set (α × ℝ) := {p : α × ℝ | p.2 = f p.1}

theorem measurableSet_graphSet {f : α → ℝ} (hf : Measurable f) :
    MeasurableSet (graphSet f) :=
  measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)

omit [MeasurableSpace α] in
@[simp] theorem preimage_mk_graphSet (f : α → ℝ) (x : α) :
    Prod.mk x ⁻¹' graphSet f = {f x} := by
  ext v; simp [graphSet]

/-- **The book's claim.**  When the velocity is constrained by the position, the constraint
set is null for the joint law of position and unconstrained velocity, provided the law of
the velocity is atomless (e.g. Gaussian). -/
theorem graphSet_null (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    {f : α → ℝ} (hf : Measurable f) :
    (μ.prod ν) (graphSet f) = 0 := by
  refine Measure.measure_prod_null_of_ae_null (measurableSet_graphSet hf) ?_
  filter_upwards with x
  simp

/-- The two-dimensional Lebesgue version: the graph of a measurable function is a
Lebesgue-null subset of the plane. -/
theorem graphSet_volume_null {f : ℝ → ℝ} (hf : Measurable f) :
    (volume : Measure (ℝ × ℝ)) (graphSet f) = 0 := by
  rw [Measure.volume_eq_prod]
  exact graphSet_null _ _ hf

/-- The Gaussian version literally stated in the book: with a Gaussian law for the position
and an (unconstrained) Gaussian law for the velocity, the constraint set has null
measure. -/
theorem graphSet_gaussian_null (m₁ m₂ : ℝ) (v₁ : ℝ≥0) (v₂ : ℝ≥0) (hv₂ : v₂ ≠ 0)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ((gaussianReal m₁ v₁).prod (gaussianReal m₂ v₂)) (graphSet f) = 0 := by
  have : NullSingletonClass (gaussianReal m₂ v₂) := nullSingletonClass_gaussianReal hv₂
  exact graphSet_null _ _ hf

/-- **The consequence.**  Conditioning the joint law on the constraint gives the zero
measure: the local constraint cannot be imposed by naive conditioning. -/
theorem restrict_graphSet_eq_zero (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    {f : α → ℝ} (hf : Measurable f) :
    (μ.prod ν).restrict (graphSet f) = 0 :=
  Measure.restrict_eq_zero.mpr (graphSet_null μ ν hf)

/-- In particular the conditioned law is not a probability measure. -/
theorem not_isProbabilityMeasure_restrict_graphSet (μ : Measure α) (ν : Measure ℝ)
    [SFinite ν] [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) :
    ¬ IsProbabilityMeasure ((μ.prod ν).restrict (graphSet f)) := by
  intro h
  have h1 : ((μ.prod ν).restrict (graphSet f)) Set.univ = 1 := h.measure_univ
  rw [restrict_graphSet_eq_zero μ ν hf] at h1
  simp at h1

end BookProof.LocalityConstraint
