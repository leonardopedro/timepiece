/-
prove2.me platform library module `Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SelfAdjoint_IsCayleyTransform.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar

namespace TeschlQM.SelfAdjoint

/-- Teschl, p. 81 (Theorem 2.25): an operator `V` is *isometric* if `‖Vφ‖ = ‖φ‖` for all
`φ ∈ 𝔇(V)`. -/
def IsIsometric {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (V : H →ₗ.[ℂ] H) : Prop :=
  ∀ φ : V.domain, ‖V φ‖ = ‖(φ : H)‖

/-- `Ran(1 - V) = {φ - Vφ | φ ∈ 𝔇(V)}`. -/
def rangeOneSub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (V : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  LinearMap.range (V.domain.subtype - V.toFun)

/-- Teschl (2.102), p. 81: `V` is the *Cayley transform* of `A`,
`V = (A - i)(A + i)⁻¹ : Ran(A + i) → Ran(A - i)`. That is, `𝔇(V) = Ran(A + i)` and
`V((A + i)ψ) = (A - i)ψ` for every `ψ ∈ 𝔇(A)`. -/
def IsCayleyTransform {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A V : H →ₗ.[ℂ] H) : Prop :=
  V.domain = rangeAdd A Complex.I ∧
    ∀ ψ : A.domain, ∀ h : A ψ + Complex.I • (ψ : H) ∈ V.domain,
      V ⟨A ψ + Complex.I • (ψ : H), h⟩ = A ψ - Complex.I • (ψ : H)

end TeschlQM.SelfAdjoint
