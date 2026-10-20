/-
prove2.me platform library module `Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Shared_IsBoundedBelowBy.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Shared

open scoped InnerProductSpace

/-- Teschl (2.59), p. 70: `A` is *bounded from below by* `γ ∈ ℝ`, written `A ≥ γ`, if
`q_A(ψ) = ⟨ψ, Aψ⟩ ≥ γ‖ψ‖²` for all `ψ ∈ 𝔇(A)`. The book applies this to symmetric operators, for
which `⟨ψ, Aψ⟩` is real; the real part is taken so that the inequality lives in `ℝ`. -/
def IsBoundedBelowBy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (γ : ℝ) : Prop :=
  ∀ ψ : A.domain, γ * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re

end TeschlQM.Shared
