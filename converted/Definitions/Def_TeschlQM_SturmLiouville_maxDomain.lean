/-
prove2.me platform library module `Definitions.Def_TeschlQM_SturmLiouville_maxDomain`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SturmLiouville_maxDomain.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_SolvesTau

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl (9.3), p. 182: the maximal domain
`D(τ) = {f ∈ L²(I, r dx) | f, p f′ ∈ AC_loc(I), τ f ∈ L²(I, r dx)}`.
`f` is a function (the `AC_loc` representative), `L.measure` is `r dx` on `I`. -/
def InMaxDomain (L : SLData) (f : ℝ → ℂ) : Prop :=
  MemLp f 2 L.measure ∧ ∃ g : ℝ → ℂ, SolvesTau L f g ∧ MemLp g 2 L.measure

end TeschlQM.SturmLiouville
