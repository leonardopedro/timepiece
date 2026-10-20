/-
prove2.me platform library module `Definitions.Def_OAI_Probability_ThreeState_PoissonCritical`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Probability_ThreeState_PoissonCritical.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/PoissonCritical.lean by skeleton subtraction
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

namespace OAI

/-! Informative posterior mass and positive critical Poisson non-reconstruction. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

@[simp] lemma normalizer_uninformative (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    normalizer lam h (fun _ : Fin n => uninformative) = 1 := by
  simp [normalizer,productWeight,edgeMessage,uninformative]

@[simp] lemma combineMessage_uninformative (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    combineMessage lam h (fun _ : Fin n => uninformative) = uninformative := by
  simp only [combineMessage,normalizer_uninformative,one_ne_zero,↓reduceDIte,div_one]
  apply Subtype.ext
  funext i
  simp [productWeight,edgeMessage,uninformative]

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

@[simp] lemma messageX_uninformative : messageX uninformative = 0 := by
  simp [messageX,Radial.momentX,Radial.avg_expand,messageDeviation,uninformative]

end ThreeState
namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

 
end ThreeState

end OAI
