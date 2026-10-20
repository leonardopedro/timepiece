/-
prove2.me platform library module `Theorems.Thm_SubsetSumNP_threeSAT_reduces_subsetSum`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_SubsetSumNP_threeSAT_reduces_subsetSum.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_SubsetSum_Language
import Definitions.Def_KSat_Languages
set_option autoImplicit false

theorem SubsetSumNP.threeSAT_reduces_subsetSum :
    CookLevin.PolyReducible (KSat.KSAT 3) SubsetSumNP.SUBSET_SUM := by sorry
