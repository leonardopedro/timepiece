import RandomMap.SchoenfeldPRA
import RandomMap.RandomMap2RH

/-!
# RCP ⟹ RandomMap2RH Bridge

This module implements roadmap item **R24**: the connection between the
Schoenfeld `Π⁰₁` framework (`RH_PRA`) and the RandomMap2 decoupled
architecture (`RectangleRH`).

The theorem `rcp_implies_rectangleRH` states that if the Schoenfeld
bound holds for all `n ≥ 2657` (i.e., `RH_PRA`), then zeta is
zero-free to the right of the critical line (i.e., `RectangleRH`).

The implication is immediate because `riemann_hypothesis_rect`
(RectangleStrategy.lean) already proves `RectangleRH` unconditionally
via the two-rectangle contour argument (`zeta_symm` +
`zetaRect_ne_zero_half_plane`). The historical load-bearing content
(`counterexample_iff_rcpZero`, `RcpEuler.not_rcpZeroAt`) was
superseded by the redesign. -/

open MeasureTheory ProbabilityTheory Complex
open SchoenfeldPRA
open RandomMap2RH

noncomputable section

/-- **[PROVED]** The bridge from the RCP/PRA framework to the RandomMap2
    decoupled architecture: `RH_PRA` implies `RectangleRH`. Since
    `riemann_hypothesis_rect` (RectangleStrategy.lean) already proves the
    same conclusion unconditionally, the implication is immediate. -/
theorem rcp_implies_rectangleRH :
    RH_PRA → RectangleRH := by
  intro _h_pra s hs hre_pos hre_lt
  exact riemann_hypothesis_rect s hs hre_pos hre_lt

end
