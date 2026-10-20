/-
prove2.me platform library module `Definitions.Def_TeschlQM_MinMax_eigenspace`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_MinMax_eigenspace.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.MinMax

/-- Teschl, p. 77: the **eigenspace** `Ker(A − z) = {ψ ∈ 𝔇(A) | Aψ = zψ}` of the operator `A`
at `z ∈ ℂ`, as a subspace of `ℌ`. It is `{0}` unless `z` is an eigenvalue; its dimension is
the multiplicity of the eigenvalue `z`. -/
def eigenspace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  Submodule.map A.domain.subtype (LinearMap.ker (A.toFun - z • A.domain.subtype))

end TeschlQM.MinMax
