/-
prove2.me platform library module `Theorems.Thm_TeschlQM_SelfAdjoint_selfAdjoint_of_range_eq_top`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_TeschlQM_SelfAdjoint_selfAdjoint_of_range_eq_top.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar

namespace TeschlQM.SelfAdjoint

open ComplexConjugate

/-- Teschl, Lemma 2.3 (p. 63): if `A` is symmetric and `Ran(A + z) = Ran(A + z*) = ℌ` for one
`z ∈ ℂ`, then `A` is self-adjoint. -/
theorem selfAdjoint_of_range_eq_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ)
    (hz : rangeAdd A z = ⊤) (hz' : rangeAdd A (conj z) = ⊤) :
    IsSelfAdjoint A := by sorry

end TeschlQM.SelfAdjoint
