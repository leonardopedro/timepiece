/-
prove2.me platform library module `Definitions.Def_OAI_Probability_ThreeState_Supercritical`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Probability_ThreeState_Supercritical.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Supercritical.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives
import Definitions.Def_OAI_Probability_ThreeState_PosteriorMoments
import Definitions.Def_OAI_Probability_ThreeState_PoissonCritical

namespace OAI

/-! Boundary score moments and reconstruction above the Kesten–Stigum threshold. -/

namespace ThreeState

noncomputable def listScore {α : Type*} (f : α → ℝ) (as : List α) : ℝ := (as.map f).sum
noncomputable def multisetScore {α : Type*} (f : α → ℝ) (as : Multiset α) : ℝ := (as.map f).sum

 

 

def spinScore (i : Spin) : ℝ := if i=0 then 2 else -1

noncomputable def boundaryScore : (n : ℕ) → Observation n → ℝ
  | 0 => spinScore
  | n+1 => multisetScore (boundaryScore n)

noncomputable def scoreSecond (d e lam : ℝ) (h : Admissible lam) : ℕ → Spin → ℝ
  | 0, i => (spinScore i)^2
  | n+1, i => d*mean (channelPMF lam h i) (scoreSecond d e lam h n) +
      e*((d*lam)^n*lam*spinScore i)^2

 
 

end ThreeState

namespace ThreeState

 
noncomputable def posteriorTV {α : Type*} (law : Spin → PMF α) (y : α) : ℝ :=
  (∑ i : Spin, |posterior law y i-1/3|)/2

noncomputable def posteriorScore {α : Type*} (law : Spin → PMF α) (y : α) : ℝ :=
  3*posterior law y 0-1

 

end ThreeState

namespace ThreeState

 

 

 

 

end ThreeState

end OAI
