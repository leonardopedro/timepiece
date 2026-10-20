/-
prove2.me platform library module `Definitions.Def_TeschlQM_MinMax_spectrum`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_MinMax_spectrum.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.MinMax

/-- Teschl, p. 73, (2.66): the **resolvent set** `ρ(A) = {z ∈ ℂ | (A − z)⁻¹ ∈ 𝔏(ℌ)}`: `z ∈ ρ(A)`
iff `A − z : 𝔇(A) → ℌ` is bijective with a bounded inverse, i.e. there is a bounded, everywhere
defined `R` that maps `ℌ` into `𝔇(A)` and is a two-sided inverse of `A − z` there. -/
def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, (∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ) ∧
      ∀ φ : H, ∃ hφ : R φ ∈ A.domain, A ⟨R φ, hφ⟩ - z • R φ = φ}

/-- Teschl, p. 73, (2.67): the **spectrum** `σ(A) = ℂ \ ρ(A)`. -/
def spectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  (resolventSet A)ᶜ

end TeschlQM.MinMax
