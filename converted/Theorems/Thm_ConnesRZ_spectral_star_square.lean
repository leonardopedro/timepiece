/-
prove2.me platform library module `Theorems.Thm_ConnesRZ_spectral_star_square`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ConnesRZ_spectral_star_square.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory

namespace ConnesRZ

theorem spectral_star_square (g : ℝ → ℂ) (hg : IsTest g) :
    HasSum (fun ρ : {s : ℂ // IsCriticalZero s} =>
      (zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 *
        (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1))))
      (weilDistribution (conv g (starInv g))) := by sorry

end ConnesRZ
