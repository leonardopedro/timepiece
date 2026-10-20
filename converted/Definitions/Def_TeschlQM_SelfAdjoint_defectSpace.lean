/-
prove2.me platform library module `Definitions.Def_TeschlQM_SelfAdjoint_defectSpace`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SelfAdjoint_defectSpace.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar

namespace TeschlQM.SelfAdjoint

/-- Teschl (2.101), p. 81: the defect space `K₊ = Ran(A + i)^⊥` (`= Ker(A* - i)`). -/
noncomputable def defectPlus {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (rangeAdd A Complex.I)ᗮ

/-- Teschl (2.101), p. 81: the defect space `K₋ = Ran(A - i)^⊥` (`= Ker(A* + i)`). -/
noncomputable def defectMinus {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (rangeAdd A (-Complex.I))ᗮ

/-- Teschl (2.101), p. 81: the defect indices `d±(A) = dim K±` are equal. The dimension is the
Hilbert dimension (cardinality of an orthonormal basis), and two Hilbert spaces have the same
Hilbert dimension exactly when there is a unitary (a surjective linear isometry) between them;
this is the formulation used here. -/
def HasEqualDefectIndices {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Prop :=
  Nonempty (defectPlus A ≃ₗᵢ[ℂ] defectMinus A)

end TeschlQM.SelfAdjoint
