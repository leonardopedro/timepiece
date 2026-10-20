/-
prove2.me platform library module `Definitions.Def_TeschlQM_SelfAdjoint_addScalar`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SelfAdjoint_addScalar.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.SelfAdjoint

/-- The operator `A + z` of Teschl, for `z ∈ ℂ`: same domain `𝔇(A)`, `(A + z)ψ = Aψ + zψ`.
(Mathlib's `f +ᵥ g` adds a total linear map to a partial one on the partial one's domain.)
`A - z` is `addScalar A (-z)`. -/
noncomputable def addScalar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : H →ₗ.[ℂ] H :=
  (z • LinearMap.id : H →ₗ[ℂ] H) +ᵥ A

/-- `Ran(A + z) = {Aψ + zψ | ψ ∈ 𝔇(A)}` as a subspace of `ℌ`. -/
noncomputable def rangeAdd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  LinearMap.range (addScalar A z).toFun

/-- `Ker(A + z) = {ψ ∈ 𝔇(A) | Aψ + zψ = 0}` as a subspace of `ℌ`. -/
noncomputable def kerAdd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  (LinearMap.ker (addScalar A z).toFun).map (addScalar A z).domain.subtype

end TeschlQM.SelfAdjoint
