/-
prove2.me platform library module `Definitions.Def_TeschlQM_Shared_spectralMeasure`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Shared_spectralMeasure.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open MeasureTheory
open scoped ENNReal

namespace TeschlQM.Shared

open Classical in
/-- Teschl, p. 89: the **spectral measure** `μ_ψ` of the vector `ψ` with respect to the
projection-valued measure `P`, the finite Borel measure with `μ_ψ(Ω) = ⟨ψ, P(Ω)ψ⟩ = ‖P(Ω)ψ‖²`.
It is built with `Measure.ofMeasurable` from `Ω ↦ ‖P(Ω)ψ‖²` whenever that set function vanishes
on `∅` and is countably additive on Borel sets (which holds for every projection-valued
measure); for any other `P` the value is the zero measure, a junk value that never occurs in
the statements of this mission, all of which assume `P` is a projection-valued measure. -/
noncomputable def spectralMeasure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : Set ℝ → (H →L[ℂ] H)) (ψ : H) : Measure ℝ :=
  if h : ((‖P ∅ ψ‖₊ : ℝ≥0∞) ^ 2 = 0 ∧
      ∀ ⦃Ω : ℕ → Set ℝ⦄, (∀ n, MeasurableSet (Ω n)) → Pairwise (Function.onFun Disjoint Ω) →
        (‖P (⋃ n, Ω n) ψ‖₊ : ℝ≥0∞) ^ 2 = ∑' n, (‖P (Ω n) ψ‖₊ : ℝ≥0∞) ^ 2) then
    Measure.ofMeasurable (fun Ω _ => (‖P Ω ψ‖₊ : ℝ≥0∞) ^ 2) h.1 (fun _ hΩ hd => h.2 hΩ hd)
  else 0

end TeschlQM.Shared
