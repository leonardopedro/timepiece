/-
prove2.me platform library module `Definitions.Def_TeschlQM_Shared_compactOperators`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_Shared_compactOperators.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.Shared

/-- Teschl, p. 127: `K ∈ 𝔏(ℌ)` is a **finite rank operator** if its range is finite dimensional. -/
def IsFiniteRank {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : H →L[ℂ] H) : Prop :=
  FiniteDimensional ℂ (LinearMap.range (K : H →ₗ[ℂ] H))

/-- Teschl, p. 128: the set `ℭ(ℌ)` of **compact operators** is the closure in `𝔏(ℌ)` (operator
norm topology) of the set of all finite rank operators. -/
def compactOperators (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Set (H →L[ℂ] H) :=
  closure {K : H →L[ℂ] H | IsFiniteRank K}

end TeschlQM.Shared
