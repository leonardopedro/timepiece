/-
prove2.me platform library module `Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Shared_IsProjValuedMeasure.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Shared

/-- Teschl, p. 88, (3.5): a **projection-valued measure** on the complex Hilbert space `H`.
`P` assigns to every Borel set `Ω ⊆ ℝ` an orthogonal projection `P Ω` (`P(Ω)* = P(Ω) = P(Ω)²`)
such that (i) `P(ℝ) = 𝕀` and (ii) for pairwise disjoint Borel sets `Ω n`, the series
`∑ₙ P(Ωₙ)ψ` converges to `P(⋃ₙ Ωₙ)ψ` for every `ψ` (strong σ-additivity; not norm convergence).
Only the values of `P` on Borel sets are constrained; its values on other sets play no role. -/
def IsProjValuedMeasure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Prop :=
  (∀ Ω : Set ℝ, MeasurableSet Ω → IsSelfAdjoint (P Ω) ∧ IsIdempotentElem (P Ω)) ∧
  P Set.univ = 1 ∧
  ∀ Ω : ℕ → Set ℝ, (∀ n, MeasurableSet (Ω n)) → Pairwise (Function.onFun Disjoint Ω) →
    ∀ ψ : H, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, P (Ω n) ψ) Filter.atTop
      (nhds (P (⋃ n, Ω n) ψ))

end TeschlQM.Shared
