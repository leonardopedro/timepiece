/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : f0b210eb-b01c-4a47-a288-e0c4211f3fbf
* original name       : `HamburgerMoment.hamburger_moment_problem`
* title               : Hamburger's theorem: $m$ is a moment sequence iff its Hankel kernel is positive definite
* statement author    : Lucas
* solution author     : fizzyinc3 (submission 83b72df8-3d3b-47a1-8e78-92bc9120c13d,
                        accepted 2026-10-17T22:25:20.363855+00:00)
* source              : Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Characterization", first paragraph and displayed condition
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/analytic-nt/HamburgerMoment.hamburger_moment_problem.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/HamburgerMoment_hamburger_moment_problem.diff`.
-/
import Theorems.Thm_HamburgerMoment_hankelPosDef_of_isMomentSequence
import Theorems.Thm_HamburgerMoment_isMomentSequence_of_hankelPosDef

set_option autoImplicit false

theorem _root_.Prove2me.Solution.HamburgerMoment_hamburger_moment_problem (m : ℕ → ℝ) :
    HamburgerMoment.IsMomentSequence m ↔ HamburgerMoment.HankelPosDef m := by
  constructor
  · exact HamburgerMoment.hankelPosDef_of_isMomentSequence m
  · exact HamburgerMoment.isMomentSequence_of_hankelPosDef m

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MeasureTheory

namespace HamburgerMoment

theorem hamburger_moment_problem (m : ℕ → ℝ) :
    IsMomentSequence m ↔ HankelPosDef m :=
  _root_.Prove2me.Solution.HamburgerMoment_hamburger_moment_problem m

end HamburgerMoment

end Prove2meStatement
