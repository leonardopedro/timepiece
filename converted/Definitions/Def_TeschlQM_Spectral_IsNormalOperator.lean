/-
prove2.me platform library module `Definitions.Def_TeschlQM_Spectral_IsNormalOperator`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Spectral_IsNormalOperator.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Spectral

/-- Teschl, p. 91: an unbounded operator `T` is **normal** if `𝔇(T) = 𝔇(T*)` and
`‖Tψ‖ = ‖T*ψ‖` for all `ψ ∈ 𝔇(T)`. The adjoint `T*` is only defined for densely defined `T`
(Teschl, Sec. 2.1), so density of `𝔇(T)` is part of the notion; Mathlib's `LinearPMap.adjoint`
is a junk value otherwise. -/
def IsNormalOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →ₗ.[ℂ] H) : Prop :=
  Dense (T.domain : Set H) ∧ T.adjoint.domain = T.domain ∧
  ∀ (ψ : T.domain) (ψ' : T.adjoint.domain), (ψ : H) = ψ' → ‖T ψ‖ = ‖T.adjoint ψ'‖

end TeschlQM.Spectral
