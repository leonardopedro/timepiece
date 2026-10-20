/-
prove2.me platform library module `Theorems.Thm_HamburgerMoment_hankelPosDef_of_isMomentSequence`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_HamburgerMoment_hankelPosDef_of_isMomentSequence.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HamburgerMoment

theorem hankelPosDef_of_isMomentSequence (m : ℕ → ℝ) (hm : IsMomentSequence m) :
    HankelPosDef m := by sorry

end HamburgerMoment
