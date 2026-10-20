/-
prove2.me platform library module `Definitions.Def_TeschlQM_Spectral_boundedSpectralIntegral`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Spectral_boundedSpectralIntegral.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_Spectral_spectralMeasure

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 90: `f` belongs to `B(ℝ)`, the bounded Borel functions `ℝ → ℂ`. -/
def IsBoundedBorel (f : ℝ → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

open Classical in
/-- Teschl, p. 90, (3.17), (3.20): for a bounded Borel function `f`, `P(f) = ∫_ℝ f(λ) dP(λ)` as a
bounded operator on `H`: the bounded operator `T` with `⟨ψ, Tψ⟩ = ∫_ℝ f(λ) dμ_ψ(λ)` for all
`ψ ∈ H` (over `ℂ` a bounded operator is determined by its quadratic form); the zero operator if
there is none, which never happens for a projection-valued measure and `f ∈ B(ℝ)`. -/
noncomputable def boundedSpectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) : H →L[ℂ] H :=
  if h : ∃ T : H →L[ℂ] H, ∀ ψ : H, ⟪ψ, T ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ then h.choose
  else 0

end TeschlQM.Spectral
