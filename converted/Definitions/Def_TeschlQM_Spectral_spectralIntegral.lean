/-
prove2.me platform library module `Definitions.Def_TeschlQM_Spectral_spectralIntegral`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Spectral_spectralIntegral.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_Spectral_spectralMeasure

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

/-- Teschl, p. 91, (3.25): `𝔇_f = {ψ ∈ H | ∫_ℝ |f(λ)|² dμ_ψ(λ) < ∞}`, the domain of `P(f)`. -/
def spectralDomain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) : Set H :=
  {ψ | ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂spectralMeasure P ψ < ∞}

/-- Teschl, pp. 90–92, (3.17), (3.25), (3.28): the (possibly unbounded) operator `T` is the
spectral integral `∫_ℝ f(λ) dP(λ)`: its domain is `𝔇_f` and `⟨ψ, Tψ⟩ = ∫_ℝ f(λ) dμ_ψ(λ)` for
every `ψ` in it. For a projection-valued measure and a Borel function `f` there is exactly one
such operator, since `𝔇_f` is a dense subspace and, over `ℂ`, the quadratic form on a dense
subspace determines the operator there by polarization. -/
def IsSpectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) (T : H →ₗ.[ℂ] H) : Prop :=
  (T.domain : Set H) = spectralDomain P f ∧
  ∀ ψ : T.domain, ⟪(ψ : H), T ψ⟫_ℂ = ∫ x, f x ∂spectralMeasure P ψ

open Classical in
/-- Teschl, p. 92, (3.28): `P(f) = ∫_ℝ f(λ) dP(λ)` with `𝔇(P(f)) = 𝔇_f`, as a partially defined
linear operator: the operator characterized by `IsSpectralIntegral P f` (the zero operator if no
such operator exists, which never happens for a projection-valued measure and a Borel `f`). -/
noncomputable def spectralIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (f : ℝ → ℂ) : H →ₗ.[ℂ] H :=
  if h : ∃ T, IsSpectralIntegral P f T then h.choose else 0

end TeschlQM.Spectral
