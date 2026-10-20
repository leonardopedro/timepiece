/-
prove2.me platform library module `Definitions.Def_TeschlQM_Spectral_spectrum`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Spectral_spectrum.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Spectral

/-- Teschl, p. 73, (2.66): the **resolvent set** `ρ(A) = {z ∈ ℂ | (A − z)⁻¹ ∈ 𝔏(H)}`: `z ∈ ρ(A)`
iff `A − z : 𝔇(A) → H` is bijective and its inverse is bounded, i.e. there is a bounded,
everywhere defined `R` that is a two-sided inverse of `A − z` on `𝔇(A)`. (Teschl defines it for
closed operators; it is used here only for self-adjoint ones.) -/
def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, (∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ) ∧
      ∀ φ : H, ∃ hφ : R φ ∈ A.domain, A ⟨R φ, hφ⟩ - z • R φ = φ}

/-- Teschl, p. 73, (2.67): the **spectrum** `σ(A) = ℂ \ ρ(A)`. -/
def spectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  (resolventSet A)ᶜ

end TeschlQM.Spectral
