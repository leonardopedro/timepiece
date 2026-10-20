/-
prove2.me platform library module `Theorems.Thm_KSat_sat_ram_threeCNF_normalizer`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_KSat_sat_ram_threeCNF_normalizer.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_WordRAM_Complexity_BitIO
import Definitions.Def_KSat_Languages

set_option autoImplicit false

theorem KSat.sat_ram_threeCNF_normalizer :
    ∃ (A : WordRAM.Complexity.Algorithm .restricted)
      (f : List Bool → List Bool),
      WordRAM.Complexity.RAMPolyTimeComputable A f ∧
      ∀ x, ∃ φ : CookLevin.Formula,
        f x = CookLevin.encodeFormula φ ∧ KSat.IsKCNF 3 φ ∧
        (CookLevin.SAT x ↔ CookLevin.Satisfiable φ) := by sorry
