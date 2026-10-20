/-
prove2.me platform library module `Definitions.Def_TeschlQM_Shared_IsEssentiallySelfAdjoint`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Shared_IsEssentiallySelfAdjoint.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Shared

/-- Teschl, p. 63: `A` is *essentially self-adjoint* if its closure `Ā` is self-adjoint.
`LinearPMap.closure` is the operator whose graph is the closure of the graph of `A` (for a closable
`A`); self-adjointness is Mathlib's `IsSelfAdjoint`, i.e. `Ā† = Ā`. -/
def IsEssentiallySelfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) : Prop :=
  IsSelfAdjoint A.closure

end TeschlQM.Shared
