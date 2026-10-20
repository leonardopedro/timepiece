/-
prove2.me platform library module `Definitions.Def_TeschlQM_Shared_IsSpectralIntegral`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Shared_IsSpectralIntegral.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_Shared_spectralMeasure

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Shared

/-- Teschl, p. 91, (3.25): `𝔇_f = {ψ ∈ ℌ | ∫_ℝ |f(λ)|² dμ_ψ(λ) < ∞}`, the domain of `P(f)`. -/
def spectralDomain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) : Set H :=
  {ψ | ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P ψ < ∞}

/-- Teschl, pp. 90–92, (3.17), (3.25), (3.28): the operator `T` is the spectral integral
`P(f) = ∫_ℝ f(λ) dP(λ)`: its domain is `𝔇_f` and `⟨ψ, Tψ⟩ = ∫_ℝ f(λ) dμ_ψ(λ)` for every `ψ` in
it. For a projection-valued measure there is at most one such operator: over `ℂ` the quadratic
form on the (dense) domain determines the operator by polarization. With `f(λ) = λ` this says
`T = ∫ λ dP(λ)`, the self-adjoint operator whose projection-valued measure is `P` (Thm 3.7). -/
def IsSpectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (T : H →ₗ.[ℂ] H) : Prop :=
  (T.domain : Set H) = spectralDomain P f ∧
  ∀ ψ : T.domain, ⟪(ψ : H), T ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ

end TeschlQM.Shared
