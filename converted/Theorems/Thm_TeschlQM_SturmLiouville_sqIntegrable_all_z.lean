/-
prove2.me platform library module `Theorems.Thm_TeschlQM_SturmLiouville_sqIntegrable_all_z`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_TeschlQM_SturmLiouville_sqIntegrable_all_z.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_IsLimitCircle
import Definitions.Def_TeschlQM_SturmLiouville_IsSqIntegrableNear

namespace TeschlQM.SturmLiouville

theorem sqIntegrable_all_z (L : SLData) :
    ((∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearLeft L u) →
      ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearLeft L u) ∧
    ((∃ z₀ : ℂ, ∀ u : ℝ → ℂ, IsSolution L z₀ 0 u → IsSqIntegrableNearRight L u) →
      ∀ z : ℂ, ∀ u : ℝ → ℂ, IsSolution L z 0 u → IsSqIntegrableNearRight L u) := by sorry

end TeschlQM.SturmLiouville
