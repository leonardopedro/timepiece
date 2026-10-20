/-
prove2.me platform library module `Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TraceEstimation_Hutchinson_hutchinsonEstimator.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TraceEstimation.Hutchinson

open MeasureTheory ProbabilityTheory Matrix

/-- The Rademacher law on `ℝ`: the values `1` and `-1`, each with probability `1/2`
(Avron–Toledo, Lemma 2.1 and Lemma 7.2: `Pr(z_i = ±1) = 1/2`). -/
noncomputable def rademacher : Measure ℝ :=
  (2⁻¹ : ENNReal) • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ))

instance rademacher_isProbabilityMeasure : IsProbabilityMeasure rademacher := by
  constructor
  simp only [rademacher, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The law of one Rademacher vector `z ∈ ℝⁿ`: its `n` entries are i.i.d. Rademacher. -/
noncomputable def rademacherVectorMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => rademacher

/-- The sample space of Hutchinson's trace estimator with `M` samples in dimension `n`:
`M` independent random vectors `z_1, …, z_M ∈ ℝⁿ` whose `M·n` entries are i.i.d. Rademacher
(Avron–Toledo, Definition 3.3, p. 8:3). -/
noncomputable def hutchinsonSampleMeasure (n M : ℕ) : Measure (Fin M → Fin n → ℝ) :=
  Measure.pi fun _ : Fin M => rademacherVectorMeasure n

/-- Hutchinson's trace estimator `H_M = (1/M) ∑_{i=1}^M z_iᵀ A z_i` of Definition 3.3
(Avron–Toledo, p. 8:3), as a function of the sample `ω = (z_1, …, z_M)`. -/
noncomputable def hutchinsonEstimator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (M : ℕ)
    (ω : Fin M → Fin n → ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i : Fin M, ω i ⬝ᵥ (A *ᵥ ω i)

end TraceEstimation.Hutchinson
