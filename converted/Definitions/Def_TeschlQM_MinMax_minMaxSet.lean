/-
prove2.me platform library module `Definitions.Def_TeschlQM_MinMax_minMaxSet`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_MinMax_minMaxSet.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open scoped InnerProductSpace

namespace TeschlQM.MinMax

/-- Teschl, p. 118, (4.28): for `ψ₁, …, ψ_m ∈ ℌ`,
`U(ψ₁, …, ψ_m) = {ψ ∈ 𝔇(A) | ‖ψ‖ = 1, ψ ∈ span{ψ₁, …, ψ_m}^⊥}`, as a set of elements of `𝔇(A)`.
The `ψ_j` range over all of `ℌ`, not only over `𝔇(A)`. -/
def minMaxSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) {m : ℕ} (ψ : Fin m → H) : Set A.domain :=
  {φ | ‖(φ : H)‖ = 1 ∧ (φ : H) ∈ (Submodule.span ℂ (Set.range ψ))ᗮ}

end TeschlQM.MinMax
