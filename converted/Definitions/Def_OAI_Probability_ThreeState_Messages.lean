/-
prove2.me platform library module `Definitions.Def_OAI_Probability_ThreeState_Messages`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Probability_ThreeState_Messages.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Messages.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations

namespace OAI

/-! Likelihood messages, compact couplings and subsequential posterior limits. -/

namespace ThreeState
open MeasureTheory

 
abbrev Message := {m : Spin → ℝ // (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3}

instance : CoeFun Message (fun _ => Spin → ℝ) := ⟨Subtype.val⟩

lemma Message.nonneg (m : Message) (i : Spin) : 0 ≤ m i := m.2.1 i
lemma Message.sum (m : Message) : ∑ i, m i = 3 := m.2.2
lemma Message.le_three (m : Message) (i : Spin) : m i ≤ 3 := by
  calc
    m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Message.nonneg m j) (Finset.mem_univ i)
    _ = 3 := Message.sum m

lemma message_isCompact : IsCompact {m : Spin → ℝ | (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3} := by
  have hc : IsClosed {m : Spin → ℝ | (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3} := by
    apply IsClosed.inter
    · have he : {m : Spin → ℝ | ∀ i, 0 ≤ m i} =
          ⋂ i : Spin, {m : Spin → ℝ | 0 ≤ m i} := by ext m; simp
      change IsClosed {m : Spin → ℝ | ∀ i, 0 ≤ m i}
      rw [he]
      exact isClosed_iInter (fun i : Spin => isClosed_le (continuous_const (y := (0:ℝ)))
          (continuous_apply i : Continuous (fun m : Spin → ℝ => m i)))
    · exact isClosed_eq (continuous_finset_sum _ (fun i _ => continuous_apply i)) continuous_const
  apply (isCompact_Icc (a := (fun _ : Spin => (0:ℝ))) (b := fun _ => (3:ℝ))).of_isClosed_subset hc
  intro m hm
  exact ⟨hm.1, fun i => Message.le_three ⟨m,hm⟩ i⟩

instance : CompactSpace Message := isCompact_iff_compactSpace.mp message_isCompact
noncomputable def uninformative : Message := ⟨fun _ => 1, by simp⟩

 
end ThreeState

namespace ThreeState
open MeasureTheory

 
end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology

 

end ThreeState

end OAI
