/-
prove2.me platform library module `Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Probability_ThreeState_RadialDerivatives.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/RadialDerivatives.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation
import Definitions.Def_OAI_Probability_ThreeState_Update
import Definitions.Def_OAI_Probability_ThreeState_RadialMoments

namespace OAI

/-! Radial logarithmic derivatives and the entropy inequality. -/

namespace ThreeState.Radial

noncomputable def ray (v : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ := fun i => t*v i
noncomputable def logAvg (v : Fin 3 → ℝ) := avg (fun i => Real.log (1+v i))
noncomputable def logVariance (v : Fin 3 → ℝ) := avg (fun i => (centeredLog v i)^2)
noncomputable def weightedLogVariance (v : Fin 3 → ℝ) :=
  avg (fun i => (1+v i)*(centeredLog v i)^2)
 
noncomputable def energy (v : Fin 3 → ℝ) :=
  3*logAvg v+2*logMoment v+(2/5 : ℝ)*weightedLogVariance v
 
noncomputable def gapY (v : Fin 3 → ℝ) :=
  1-invMoment v 1-6*logAvg v-2*logMoment v-(2/5 : ℝ)*weightedLogVariance v-
    (2/5 : ℝ)*logVariance v+(4/5 : ℝ)*invMoment v 1*logMoment v-(momentX v)^2
 
noncomputable def gapZ (v : Fin 3 → ℝ) :=
  6*logAvg v-5+(26/5 : ℝ)*invMoment v 1-invMoment v 2+
    (4/5 : ℝ)*logVariance v+(4/5 : ℝ)*(invMoment v 2-2*invMoment v 1)*logMoment v+
    (4/5 : ℝ)*logInvMoment v 1+(4/5 : ℝ)*(invMoment v 1)^2-3*(momentX v)^2

end ThreeState.Radial
namespace ThreeState.Radial

@[simp] lemma ray_zero (v : Fin 3 → ℝ) : ray v 0 = 0 := by ext i; simp [ray]
@[simp] lemma ray_one (v : Fin 3 → ℝ) : ray v 1 = v := by ext i; simp [ray]
@[simp] lemma logAvg_zero : logAvg 0 = 0 := by norm_num [logAvg, avg_expand]
@[simp] lemma centeredLog_zero (i : Fin 3) : centeredLog 0 i = 0 := by
  norm_num [centeredLog, avg_expand]
@[simp] lemma logMoment_zero : logMoment 0 = 0 := by norm_num [logMoment, avg_expand]
@[simp] lemma logVariance_zero : logVariance 0 = 0 := by norm_num [logVariance, avg_expand]
@[simp] lemma weightedLogVariance_zero : weightedLogVariance 0 = 0 := by
  norm_num [weightedLogVariance, avg_expand]
@[simp] lemma invMoment_zero (n : ℕ) : invMoment 0 n = 1 := by
  norm_num [invMoment, avg_expand]
@[simp] lemma logInvMoment_zero (n : ℕ) : logInvMoment 0 n = 0 := by
  norm_num [logInvMoment, avg_expand]
@[simp] lemma momentX_zero : momentX 0 = 0 := by norm_num [momentX, avg_expand]
@[simp] lemma energy_zero : energy 0 = 0 := by norm_num [energy]
@[simp] lemma gapY_zero : gapY 0 = 0 := by norm_num [gapY]
@[simp] lemma gapZ_zero : gapZ 0 = 0 := by norm_num [gapZ]

 
end ThreeState.Radial
namespace ThreeState.Radial

 
 
end ThreeState.Radial

end OAI
