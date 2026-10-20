/-
prove2.me platform library module `Theorems.Thm_UhlenbeckGauge_yangMills_ge_boundaryChernSimons`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_UhlenbeckGauge_yangMills_ge_boundaryChernSimons.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem yangMills_ge_boundaryChernSimons {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A : Connection n) (hA : IsSUConnection A) :
    -(boundaryChernSimons a b A).re ≤ yangMills a b A ∧
      (boundaryChernSimons a b A).re ≤ yangMills a b A := by sorry

end UhlenbeckGauge
