/-
prove2.me platform library module `Theorems.Thm_AnosovPlugs_exists_flow_contDiffOn_of_lipschitz`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_AnosovPlugs_exists_flow_contDiffOn_of_lipschitz.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

theorem exists_flow_contDiffOn_of_lipschitz
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v : E → E) (hv : ContDiff ℝ 1 v) (K : NNReal) (hK : LipschitzWith K v) :
    ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, (∀ x, α x 0 = x) ∧
      (∀ x, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (α x) (v (α x t)) t) ∧
      ContDiffOn ℝ 1 (fun p : E × ℝ => α p.1 p.2) (univ ×ˢ Ioo (-ε) ε) := by sorry

end AnosovPlugs
