/-
prove2.me platform library module `Definitions.Def_TeschlQM_SturmLiouville_IsACloc`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SturmLiouville_IsACloc.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- `AC_loc(I)` for a complex-valued function on an open interval `I`: `f` is absolutely
continuous on every compact subinterval of `I`. Equivalently (fundamental theorem of calculus for
absolutely continuous functions), there is a locally integrable `h` on `I` with
`f(y) − f(x) = ∫_x^y h(t) dt` for all `x, y ∈ I`; `h` is then the a.e. derivative `f′`.
This integral form is the encoding used here. -/
def IsACloc (I : Set ℝ) (f : ℝ → ℂ) : Prop :=
  ∃ h : ℝ → ℂ, LocallyIntegrableOn h I ∧
    ∀ x ∈ I, ∀ y ∈ I, f y - f x = ∫ t in x..y, h t

end TeschlQM.SturmLiouville
