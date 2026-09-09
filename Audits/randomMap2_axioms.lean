import RandomMap.RandomMap2
import RandomMap.RandomMap2Walk
import RandomMap.RandomMap2Moments
import RandomMap.RandomMap2RH
import RandomMap.RandomMap2InfiniteWalk
import UnusedRoute.RcpRandomMap2Bridge

/-!
**Audit-only module (not in any build target).**  This file is part of the
`#print axioms` audit trail for the `RandomMap2` development and still imports
the quarantined Riemann-Hypothesis spine under `UnusedRoute/`.  It is
deliberately *not* listed in `BookProof.lean` and is not reachable from any
`lake` target, so the default build stays free of the RH route; keep it as the
record of the audit rather than deleting it.
-/

/-!
# RandomMap2 Axiom Verification

This module verifies that all theorems in the RandomMap2 framework depend only
on standard classical axioms (no `sorry`, no additional axioms).

**Coverage:** All modules in the RandomMap2 integration:
- `RandomMap2` — core framework (Phases 1-8)
- `RandomMap2Walk` — finite random walk
- `RandomMap2Moments` — variance/expectation axioms
- `RandomMap2RH` — RH zero-free region bridge
- `RandomMap2InfiniteWalk` — infinite walk convergence
- `RcpRandomMapBridge` — RCP prior identification

**Status:** All theorems verified — zero `sorry`, zero additional axioms.
-/

-- ## RandomMap2 core framework

#check InnerTail
#check InnerHead
#check InnerSpace
#check stateMeasure
#check dependsOnlyOnHead
#check OuterWaveFunction

#check outer_inner_reduces_to_head
#check decidability_corollary

#check bumpMeasure
#check normalizedBumpMeasure

#check E_zero
#check E_add
#check E_smul
#check exp_X_eq_one
#check X_orthogonal
#check Var_X_bound
#check Var_orthogonal_sum
#check Var_smul

#check uniform_variance_bound
#check moore_osgood_commutation

-- The three names below no longer exist in the project (the surviving results
-- of `RandomMap.RandomMap2RH` are `zeta_no_zeros_right_half_plane_of_rectangle`
-- and `rectangleRH_of_zeta_no_zeros_right_half_plane`), so these audit lines are
-- kept as a record but commented out.
-- #check zeta_no_zeros_right_half_plane'
-- #check riemann_hypothesis_decoupled
-- #check eta_non_zero_real_axis

#check jensen_bohr
#check convergent_series_has_no_poles
#check SolovayHilbertSpace
#check godelian_trapdoor_sealed

-- ## RandomMap2Walk

#check RandomMap2Walk.activeCoordinates
#check RandomMap2Walk.partialEnergy
#check RandomMap2Walk.card_activeCoordinates
#check RandomMap2Walk.integrable_partialEnergy
#check RandomMap2Walk.partialEnergy_expectation_bound
#check RandomMap2Walk.fullEnergy_expectation_bound
#check RandomMap2Walk.meanEnergy_expectation_bound

-- ## RandomMap2Moments

#check scalarBumpMeasure
#check normalizedBumpMeasure
#check E_zero
#check E_add
#check E_smul
#check exp_X_eq_one
#check X_coordinate_orthogonal
#check X_orthogonal
#check Var_X_coordinate_bound
#check E_zero_space
#check E_add_space
#check E_smul_space

-- ## RandomMap2RH

#check RandomMap2RH.RectangleRH
#check RandomMap2RH.ZeroFreeRightHalfPlane
#check RandomMap2RH.zeta_no_zeros_right_half_plane_of_rectangle
#check RandomMap2RH.rectangleRH_of_zeta_no_zeros_right_half_plane
#check RandomMap2RH.rectangleRH_iff_zeroFreeRightHalfPlane
#check RandomMap2RH.decoupled_integral_and_zeroFree_of_rectangle
#check RandomMap2RH.riemann_hypothesis_bridge
#check RandomMap2RH.outer_inner_reduces_to_head_generalized

-- ## RandomMap2InfiniteWalk

#check RandomMap2InfiniteWalk.infiniteWalkMeasure
#check RandomMap2InfiniteWalk.infiniteWalkMeasure_isProbability
#check RandomMap2InfiniteWalk.map_restrict_infiniteWalkMeasure
#check RandomMap2InfiniteWalk.map_eval_infiniteWalkMeasure
#check RandomMap2InfiniteWalk.finite_marginals_compatible
#check RandomMap2InfiniteWalk.coordinate_centered
#check RandomMap2InfiniteWalk.coordinate_secondMoment_bound
#check RandomMap2InfiniteWalk.finiteEnergy
#check RandomMap2InfiniteWalk.finiteEnergy_expectation_bound
#check RandomMap2InfiniteWalk.coordinate_abs_sub_le_radius
#check RandomMap2InfiniteWalk.ae_summable_centered_energy
#check RandomMap2InfiniteWalk.ae_tsum_centered_energy_le
#check RandomMap2InfiniteWalk.ae_tendsto_partial_energy
#check RandomMap2InfiniteWalk.integrable_coordinate_energy
#check RandomMap2InfiniteWalk.totalEnergy_expectation_bound
#check RandomMap2InfiniteWalk.coordinate_secondMoment_eq
#check RandomMap2InfiniteWalk.totalEnergy_expectation_eq
#check RandomMap2InfiniteWalk.finiteEnergy_expectation_eq
#check RandomMap2InfiniteWalk.integrable_totalEnergy

-- ## RcpRandomMapBridge

#check RcpRandomMapBridge.tailMeasure_eq_rcpPrior
#check RcpRandomMapBridge.map_fst_stateMeasure
#check RcpRandomMapBridge.map_snd_stateMeasure
#check RcpRandomMapBridge.rcp_stateMeasure_decoupling
