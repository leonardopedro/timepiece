/-
prove2.me platform library module `Definitions.Def_TeschlQM_Shared_resolventSet`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Shared_resolventSet.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Shared

/-- Teschl (2.66), p. 73: `R ∈ 𝔏(ℌ)` is the resolvent `R_A(z) = (A - z)⁻¹` of `A` at `z`, i.e.
`A - z : 𝔇(A) → ℌ` is a bijection and `R` is its bounded inverse: `R` maps `ℌ` into `𝔇(A)` with
`(A - z) R φ = φ` for every `φ ∈ ℌ`, and `R (A - z) ψ = ψ` for every `ψ ∈ 𝔇(A)`. Such an `R` is
unique when it exists. -/
def IsResolventAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) ∧
    ∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ

/-- Teschl (2.66), p. 73: the resolvent set `ρ(A) = {z ∈ ℂ | (A - z)⁻¹ ∈ 𝔏(ℌ)}`: `A - z` is a
bijection of `𝔇(A)` onto `ℌ` with a bounded inverse. -/
def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, IsResolventAt A z R}

/-- Teschl (2.67), p. 73: the spectrum `σ(A) = ℂ \ ρ(A)`. -/
def spectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  (resolventSet A)ᶜ

end TeschlQM.Shared
