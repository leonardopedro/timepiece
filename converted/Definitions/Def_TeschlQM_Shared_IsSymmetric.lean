/-
prove2.me platform library module `Definitions.Def_TeschlQM_Shared_IsSymmetric`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Shared_IsSymmetric.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Shared

open scoped InnerProductSpace

/-- Teschl (2.17), p. 58: a linear operator `A : 𝔇(A) → ℌ` (a `LinearPMap`) is *symmetric* if it is
densely defined and `⟨φ, Aψ⟩ = ⟨Aφ, ψ⟩` for all `ψ, φ ∈ 𝔇(A)`. Density is part of the book's
definition. -/
def IsSymmetric {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Prop :=
  Dense (A.domain : Set H) ∧ ∀ φ ψ : A.domain, ⟪(φ : H), A ψ⟫_ℂ = ⟪A φ, (ψ : H)⟫_ℂ

end TeschlQM.Shared
