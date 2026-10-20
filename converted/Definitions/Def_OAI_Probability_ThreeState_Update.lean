/-
prove2.me platform library module `Definitions.Def_OAI_Probability_ThreeState_Update`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Probability_ThreeState_Update.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Update.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Branchwise likelihood updates and their independent product measures. -/

namespace ThreeState
open MeasureTheory
open scoped Classical

noncomputable def edgeMessage (lam : ℝ) (h : Admissible lam) (m : Message) : Message :=
  ⟨fun i => 1+lam*(m i-1), by
    constructor
    · intro i
      have hl := Message.nonneg m i
      have hu := Message.le_three m i
      by_cases hp : 0 ≤ lam
      · nlinarith [h.2]
      · have hn : lam ≤ 0 := le_of_not_ge hp
        nlinarith [h.1]
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Message.sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num⟩

 
noncomputable def productWeight (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) (i : Spin) : ℝ :=
  ∏ j, edgeMessage lam h (m j) i

noncomputable def normalizer (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) : ℝ :=
  (∑ i : Spin, productWeight lam h m i)/3

lemma productWeight_nonneg (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) (i : Spin) :
    0 ≤ productWeight lam h m i :=
  Finset.prod_nonneg (fun index _ => Message.nonneg (edgeMessage lam h (m index)) i)

lemma normalizer_nonneg (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    0 ≤ normalizer lam h m := div_nonneg (Finset.sum_nonneg (fun i _ => productWeight_nonneg _ _ _ _)) (by norm_num)

lemma productWeight_sum (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) :
    ∑ i, productWeight lam h m i = 3*normalizer lam h m := by dsimp [normalizer]; ring

noncomputable def combineMessage (lam : ℝ) (h : Admissible lam) {n : ℕ} (m : Fin n → Message) : Message :=
  if hz : normalizer lam h m = 0 then uninformative else
    ⟨fun i => productWeight lam h m i / normalizer lam h m, by
      constructor
      · intro i
        exact div_nonneg (productWeight_nonneg _ _ _ _) (normalizer_nonneg _ _ _)
      · rw [← Finset.sum_div, productWeight_sum]
        field_simp⟩

end ThreeState
namespace ThreeState
open MeasureTheory
open scoped Classical

end ThreeState

end OAI
