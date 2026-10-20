/-
prove2.me platform library module `Definitions.Def_TraceEstimation_Shared_IsApproximator`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TraceEstimation_Shared_IsApproximator.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TraceEstimation.Shared

open MeasureTheory

/-- Definition 4.1 (Avron–Toledo, p. 8:5): a randomized trace estimator `T`, a real random
variable on a probability space `(Ω, P)`, is an `(ε, δ)`-approximator of `trace(A)` if
`Pr(|T - trace(A)| ≤ ε · trace(A)) ≥ 1 - δ`. -/
def IsApproximator {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω → ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (ε δ : ℝ) : Prop :=
  1 - δ ≤ P.real {ω | |T ω - A.trace| ≤ ε * A.trace}

end TraceEstimation.Shared
