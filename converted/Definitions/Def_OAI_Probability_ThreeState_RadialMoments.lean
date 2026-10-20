/-
prove2.me platform library module `Definitions.Def_OAI_Probability_ThreeState_RadialMoments`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Probability_ThreeState_RadialMoments.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/RadialMoments.lean by skeleton subtraction
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

namespace OAI

/-! Three-coordinate moment identities and positive radial polynomials. -/

namespace ThreeState.Radial

end ThreeState.Radial

 

namespace ThreeState.Radial

noncomputable def avg (v : Fin 3 → ℝ) : ℝ := (∑ i, v i) / 3
noncomputable def momentX (v : Fin 3 → ℝ) : ℝ := avg (fun i => (v i)^2) / 2
noncomputable def centeredLog (v : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  Real.log (1+v i) - avg (fun j => Real.log (1+v j))

lemma avg_expand (v : Fin 3 → ℝ) : avg v = (v 0+v 1+v 2)/3 := by
  simp [avg, Fin.sum_univ_succ]; ring

noncomputable def invMoment (v : Fin 3 → ℝ) (j : ℕ) :=
  avg (fun i => ((1+v i)⁻¹)^j)
noncomputable def logInvMoment (v : Fin 3 → ℝ) (j : ℕ) :=
  avg (fun i => centeredLog v i*((1+v i)⁻¹)^j)
noncomputable def logMoment (v : Fin 3 → ℝ) := avg (fun i => v i*centeredLog v i)

 
 

end ThreeState.Radial

end OAI
