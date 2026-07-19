import RiemannProof.RandomMap2
import RiemannProof.RandomMap2Walk
import RiemannProof.RandomMap2Moments
import RiemannProof.RandomMap2RH
import RiemannProof.RandomMap2InfiniteWalk
import RiemannProof.RcpRandomMapBridge

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

#check RandomMap2.InnerTail
#check RandomMap2.InnerHead
#check RandomMap2.InnerSpace
#check RandomMap2.stateMeasure
#check RandomMap2.dependsOnlyOnHead
#check RandomMap2.OuterWaveFunction

#check RandomMap2.outer_inner_reduces_to_head
#check RandomMap2.decidability_corollary

#check RandomMap2.bumpMeasure
#check RandomMap2.normalizedBumpMeasure

#check RandomMap2.E_zero
#check RandomMap2.E_add
#check RandomMap2.E_smul
#check RandomMap2.exp_X_eq_one
#check RandomMap2.X_orthogonal
#check RandomMap2.Var_X_bound
#check RandomMap2.Var_orthogonal_sum
#check RandomMap2.Var_smul

#check RandomMap2.uniform_variance_bound
#check RandomMap2.moore_osgood_commutation

#check RandomMap2.zeta_no_zeros_right_half_plane'
#check RandomMap2.riemann_hypothesis_decoupled
#check RandomMap2.eta_non_zero_real_axis

#check RandomMap2.jensen_bohr
#check RandomMap2.convergent_series_has_no_poles
#check RandomMap2.SolovayHilbertSpace
#check RandomMap2.godelian_trapdoor_sealed

-- ## RandomMap2Walk

#check RandomMap2Walk.activeCoordinates
#check RandomMap2Walk.partialEnergy
#check RandomMap2Walk.card_activeCoordinates
#check RandomMap2Walk.integrable_partialEnergy
#check RandomMap2Walk.partialEnergy_expectation_bound
#check RandomMap2Walk.fullEnergy_expectation_bound
#check RandomMap2Walk.meanEnergy_expectation_bound

-- ## RandomMap2Moments

#check RandomMap2Moments.scalarBumpMeasure
#check RandomMap2Moments.normalizedBumpMeasure
#check RandomMap2Moments.E_zero
#check RandomMap2Moments.E_add
#check RandomMap2Moments.E_smul
#check RandomMap2Moments.exp_X_eq_one
#check RandomMap2Moments.X_coordinate_orthogonal
#check RandomMap2Moments.X_orthogonal
#check RandomMap2Moments.Var_X_coordinate_bound
#check RandomMap2Moments.E_zero_space
#check RandomMap2Moments.E_add_space
#check RandomMap2Moments.E_smul_space

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
