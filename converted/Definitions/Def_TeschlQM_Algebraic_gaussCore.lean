/-
prove2.me platform library module `Definitions.Def_TeschlQM_Algebraic_gaussCore`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Algebraic_gaussCore.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Algebraic

open MeasureTheory

/-- The function `x ↦ x^α e^{−ω|x|²/2}` on `ℝⁿ` (`x^α = x₁^{α₁} ⋯ xₙ^{αₙ}`, `α ∈ ℕ₀ⁿ`), with
`|x|` the Euclidean norm. For `ω = 1` these span Teschl's `𝔇` of (8.20)/(8.34), p. 176/178. -/
noncomputable def gaussMonomial (n : ℕ) (ω : ℝ) (α : Fin n → ℕ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => ((∏ j : Fin n, x j ^ α j) * Real.exp (-(ω * ‖x‖ ^ 2) / 2) : ℝ)

/-- The linear span, inside the space of all functions `ℝⁿ → ℂ`, of the functions
`x^α e^{−ω|x|²/2}`, `α ∈ ℕ₀ⁿ`. -/
noncomputable def coreFun (n : ℕ) (ω : ℝ) : Submodule ℂ (EuclideanSpace ℝ (Fin n) → ℂ) :=
  Submodule.span ℂ (Set.range (gaussMonomial n ω))

/-- Teschl (8.20)/(8.34): the subspace `𝔇_ω = span{x^α e^{−ω|x|²/2} | α ∈ ℕ₀ⁿ} ⊆ L²(ℝⁿ)`, the span
of the `L²` classes of the functions `gaussMonomial n ω α`. Teschl's `𝔇` is the case `ω = 1`. -/
noncomputable def core (n : ℕ) (ω : ℝ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  Submodule.span ℂ
    {ψ | ∃ α : Fin n → ℕ, (ψ : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] gaussMonomial n ω α}

end TeschlQM.Algebraic
