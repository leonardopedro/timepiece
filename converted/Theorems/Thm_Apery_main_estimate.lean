/-
prove2.me platform library module `Theorems.Thm_Apery_main_estimate`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Apery_main_estimate.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceValue

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem main_estimate :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∃ Q : ℤ[X],
      (∃ c' : ℚ, 0 < c' ∧ Q.map (Int.castRingHom ℚ) = C c' * F n) ∧
      Q.natDegree = 37 * n ∧
      0 < aeval zeta5 Q ∧ aeval zeta5 Q < Real.exp (-c * (n : ℝ) ^ 2) := by sorry

end Apery
