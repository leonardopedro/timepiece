/-
prove2.me platform library module `Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_Combinatorics_MatchingPSD_TensorBounds.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TensorBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {C : Type u_1} [Fintype C] [DecidableEq C]

end MatchingSmoothing

namespace MatchingSmoothing
open Matrix
variable {H : Type u_2} {C : Type u_3} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

noncomputable def commonColoringsProdEquiv (σ : Equiv.Perm (H × Bool)) :
    ({f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} ×
      {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)}) ≃
    {f : H × Bool → C × C // pairConstant f ∧ pairConstant (f ∘ σ)} where
  toFun fg := ⟨fun v => (fg.1.1 v, fg.2.1 v),
    ⟨fun i => Prod.ext (fg.1.2.1 i) (fg.2.2.1 i),
      fun i => Prod.ext (fg.1.2.2 i) (fg.2.2.2 i)⟩⟩
  invFun f := (⟨fun v => (f.1 v).1, ⟨fun i => congrArg Prod.fst (f.2.1 i),
      fun i => congrArg Prod.fst (f.2.2 i)⟩⟩,
    ⟨fun v => (f.1 v).2, ⟨fun i => congrArg Prod.snd (f.2.1 i),
      fun i => congrArg Prod.snd (f.2.2 i)⟩⟩)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def normalizedPairMatrix (γ : Matrix C C ℝ) (π : C → ℝ) : Matrix C C ℝ :=
  fun i j => γ i j / (Real.sqrt (π i) * Real.sqrt (π j))

end MatchingSmoothing

end OAI
