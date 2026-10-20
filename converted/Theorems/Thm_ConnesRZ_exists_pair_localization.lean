/-
prove2.me platform library module `Theorems.Thm_ConnesRZ_exists_pair_localization`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ConnesRZ_exists_pair_localization.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory

namespace ConnesRZ

theorem exists_pair_localization :
∀ s : ℂ, IsCriticalZero s → s.re ≠ 1 / 2 →
      ∃ g : ℝ → ℂ, IsTest g ∧
        IsCriticalZero (1 - (starRingEnd ℂ) s) ∧
        0 < zeroMult s ∧ 0 < zeroMult (1 - (starRingEnd ℂ) s) ∧
        mellinHat g s = 1 ∧ mellinHat g (1 - (starRingEnd ℂ) s) = -1 ∧
        ∃ r : ℝ, r < 1 ∧ HasSum
          (fun ρ : {z : ℂ // IsCriticalZero z} =>
            if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then 0 else
              ((zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 *
                (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))).re) r := by sorry

end ConnesRZ
