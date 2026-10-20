/-
prove2.me platform library module `Theorems.Thm_UhlenbeckGauge_yangMills_eq_boundaryChernSimons_iff`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_UhlenbeckGauge_yangMills_eq_boundaryChernSimons_iff.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem yangMills_eq_boundaryChernSimons_iff {n : ℕ} (a b : R4) (hab : ∀ μ, a μ < b μ)
    (A : Connection n) (hA : IsSUConnection A) :
    (yangMills a b A = -(boundaryChernSimons a b A).re ↔
        ∀ x ∈ Set.Icc a b, IsSelfDual (curvature A x)) ∧
      (yangMills a b A = (boundaryChernSimons a b A).re ↔
        ∀ x ∈ Set.Icc a b, IsAntiSelfDual (curvature A x)) := by sorry

end UhlenbeckGauge
