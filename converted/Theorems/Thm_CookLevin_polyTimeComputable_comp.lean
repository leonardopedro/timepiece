/-
prove2.me platform library module `Theorems.Thm_CookLevin_polyTimeComputable_comp`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_CookLevin_polyTimeComputable_comp.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CookLevin_Complexity

set_option autoImplicit false

theorem CookLevin.polyTimeComputable_comp
    (f g : List Bool → List Bool)
    (hf : CookLevin.IsPolyTimeComputable f)
    (hg : CookLevin.IsPolyTimeComputable g) :
    CookLevin.IsPolyTimeComputable (fun x => g (f x)) := by sorry
