/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import BookProof.RoadmapAudit.ChapterRoadmapAuditImports

/-!
# Roadmap headline certificate — audit ledger, slice 8 of 8

Slice 8 of the eight slices of the `#audit_axioms` ledger that used to sit at the end of
`BookProof/RoadmapAudit/ChapterRoadmapAudit.lean`.  The directives are the original ones,
verbatim and in the original order; the split exists only so that Lake elaborates eight modules in
parallel instead of one, which is where the aggregate build's 25 minutes went.

Each line prints the stock `'name' depends on axioms: [...]` line for one declaration; nothing
here asserts an axiom set.
-/

namespace BookProof.ChapterRoadmapAudit

open BookProof.AxiomAudit

-- `ChapterConformalFiberDeficiency` (plan QG-2, Case B — the conformal fiber): an explicit
-- non-negative exponential wall whose wrong-sign (conformal) fiber, in rescaled standard
-- form, has a square-integrable classical solution at `z = i`, so essential self-adjointness
-- on the compactly supported smooth core fails.
#audit_axioms BookProof.ConformalFiberDeficiency.cfSol_isL2Ode
#audit_axioms BookProof.ConformalFiberDeficiency.cfV_not_deficiencyTrivialAt_I
#audit_axioms BookProof.ConformalFiberDeficiency.cfV_not_deficiencyTrivialAt_negI
#audit_axioms BookProof.ConformalFiberDeficiency.cfV_not_essentiallySelfAdjoint
#audit_axioms BookProof.ConformalFiberDeficiency.cfV_tendsto_atBot
#audit_axioms BookProof.ConformalFiberDeficiency.cfV_tendsto_atTop
#audit_axioms BookProof.ConformalFiberDeficiency.cfWall_nonneg
#audit_axioms BookProof.ConformalFiberDeficiency.cfWall_tendsto_atBot
#audit_axioms BookProof.ConformalFiberDeficiency.cfWall_tendsto_atTop
#audit_axioms
  BookProof.ConformalFiberDeficiency.exists_wall_potential_wrongSign_not_essentiallySelfAdjoint

-- `ChapterBddBelowWallEsa` (plan QG-2, Case A — the one-dimensional input): `-d²/dx² + V` is
-- essentially self-adjoint on the compactly supported smooth core of `L²(ℝ)` for every smooth
-- potential `V` bounded below, proved by a cutoff energy estimate rather than convexity.
#audit_axioms BookProof.BddBelowWallEsa.ode_solution_eq_zero_of_bddBelow
#audit_axioms BookProof.BddBelowWallEsa.wallHam_deficiencyTrivialAt_of_bddBelow
#audit_axioms BookProof.BddBelowWallEsa.wallHam_essentiallySelfAdjoint_of_bddBelow
#audit_axioms BookProof.BddBelowWallEsa.wallHam_essentiallySelfAdjoint_of_bddBelow'
#audit_axioms BookProof.BddBelowWallEsa.wallHam_essentiallySelfAdjoint_of_nonneg

-- `ChapterBddBelowFiberSumEsa` (plan QG-2, Case A — the composed operator): the orthogonal
-- direct sum `⊕ᵢ (−d²/dxᵢ² + Vᵢ)` of bounded-below fibres is essentially self-adjoint on the
-- glued core, generates a unitary flow, and (under a uniform lower bound) has a form bound.
#audit_axioms BookProof.BddBelowFiberSumEsa.fiberCore_dense
#audit_axioms BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow
#audit_axioms BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow'
#audit_axioms BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_nonneg
#audit_axioms BookProof.BddBelowFiberSumEsa.fiberSumHam_stone_flow
#audit_axioms BookProof.BddBelowFiberSumEsa.dsOp_semibounded
#audit_axioms BookProof.BddBelowFiberSumEsa.fiberSumHam_semibounded
#audit_axioms BookProof.BddBelowFiberSumEsa.fiberSumHam_nonneg_form
#audit_axioms BookProof.BddBelowFiberSumEsa.qgFiberSum_esa
#audit_axioms BookProof.BddBelowFiberSumEsa.qgFiberSum_nonneg_form

-- `ChapterHalfLineLimitCircle` (plan QG-2 / 29f Case B — the endpoint): the free half-line
-- kinetic operator is not essentially self-adjoint, and neither is its sign flip.
#audit_axioms BookProof.HalfLineLimitCircle.hlKin_not_deficiencyTrivialAt_I
#audit_axioms BookProof.HalfLineLimitCircle.hlKin_not_essentiallySelfAdjointOn
#audit_axioms BookProof.HalfLineLimitCircle.hlKin_neg_not_essentiallySelfAdjointOn
#audit_axioms BookProof.HalfLineLimitCircle.hlCore_ne_bot

-- `ChapterFockDifferingBasesEsa` (plan QG-3.2-exec): a Hamiltonian built from one-particle
-- Hermitian operators conserves the particle number, hence its commutator form against the
-- diagonal comparison operator `N = dΓ(ω) + 𝒩 + 1` vanishes identically; Faris–Lavine then
-- gives essential self-adjointness on the finite-particle core under the unweighted gate
-- `∑ₖ ‖gₖ‖ < ∞`, for summands each diagonal in its own basis and mutually non-commuting.
#audit_axioms BookProof.FockDifferingBases.sig_tgt_eq_of_balanced
#audit_axioms BookProof.FockDifferingBases.pairOp_commForm_eq_zero
#audit_axioms BookProof.FockDifferingBases.balanced_xIdx
#audit_axioms BookProof.FockDifferingBases.balancedH_symmetricOn
#audit_axioms BookProof.FockDifferingBases.balancedH_norm_le
#audit_axioms BookProof.FockDifferingBases.balancedH_commForm_eq_zero
#audit_axioms BookProof.FockDifferingBases.balancedH_essentiallySelfAdjointOn_core
#audit_axioms BookProof.FockDifferingBases.exchangeH_commForm_eq_zero
#audit_axioms BookProof.FockDifferingBases.exchangeH_essentiallySelfAdjointOn_core
#audit_axioms BookProof.FockDifferingBases.summable_specAmp
#audit_axioms BookProof.FockDifferingBases.spectralFamily_essentiallySelfAdjointOn_core
#audit_axioms BookProof.FockDifferingBases.spectralFamily_finite_essentiallySelfAdjointOn_core
#audit_axioms BookProof.FockDifferingBases.sumOfTwo_essentiallySelfAdjointOn_core
#audit_axioms BookProof.FockDifferingBases.specEntry_ne_zero
#audit_axioms BookProof.FockDifferingBases.specEntry_not_commute
#audit_axioms BookProof.FockDifferingBases.nestedFock_essentiallySelfAdjointOn_core

-- `ChapterQgOuterFockEsa` (plan QG outer Fock): the gauge-fixed gravity Hamiltonian on the
-- outer Fock space `𝔉 = ⊕ₙ L²(ℝ^{84n})` is essentially self-adjoint on the finite-particle
-- core, sector by sector via the general quadratic (Carleman) theorem and the direct-sum
-- gluing instrument.
#audit_axioms BookProof.QgOuterFock.sqSumOp_essentiallySelfAdjointOn
#audit_axioms BookProof.QgOuterFock.qgSectorPoly_eq_sum_particles
#audit_axioms BookProof.QgOuterFock.qgSectorHam_essentiallySelfAdjointOn
#audit_axioms BookProof.QgOuterFock.qgOuterCore_dense
#audit_axioms BookProof.QgOuterFock.qgOuterFock_esa
#audit_axioms BookProof.QgOuterFock.qgOuterHam_stone_flow
#audit_axioms BookProof.QgOuterFock.qgOuterN_quadForm_nonneg
#audit_axioms BookProof.QgOuterFock.qgOuterN_esa

-- `ChapterQgOuterFockFarisLavine` (plan QG outer Fock, Faris–Lavine route): comparison
-- operators, the Friedrichs extension as one, its lift to an `ℓ²`-direct sum, and Faris–Lavine
-- on the direct sum under uniform fibre data.
#audit_axioms BookProof.QgOuterFockFL.Comparison.selfAdjoint
#audit_axioms BookProof.QgOuterFockFL.Comparison.essentiallySelfAdjointOn
#audit_axioms BookProof.QgOuterFockFL.friedrichsComparison_extends
#audit_axioms BookProof.QgOuterFockFL.dsCompOp_surj
#audit_axioms BookProof.QgOuterFockFL.dsFibOp_hasSum_commForm
#audit_axioms BookProof.QgOuterFockFL.dsFibOp_commForm_le
#audit_axioms BookProof.QgOuterFockFL.dsFibOp_essentiallySelfAdjointOn
#audit_axioms BookProof.QgOuterFockFL.qgOuterFriedN_surj
#audit_axioms BookProof.QgOuterFockFL.qgOuterFriedN_isPositiveSelfAdjointExtension
#audit_axioms BookProof.QgOuterFockFL.qgOuterFriedN_esa
#audit_axioms BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine

-- `ChapterQgOuterFockEllipticFL` (plan QG outer Fock, Faris–Lavine route, unconditional case):
-- positivity of the sum-of-squares Hamiltonian for a nonnegative signature, the general
-- Friedrichs lift to an `ℓ²`-direct sum, and the elliptic gravity Hamiltonian on the outer
-- Fock space.
#audit_axioms BookProof.QgOuterFockElliptic.quadForm_sumSquares_nonneg
#audit_axioms BookProof.QgOuterFockElliptic.sqSumOp_quadForm_nonneg
#audit_axioms BookProof.QgOuterFockElliptic.dsCore_le_dsFriedDom
#audit_axioms BookProof.QgOuterFockElliptic.dsFriedComparison_isPositiveSelfAdjointExtension
#audit_axioms BookProof.QgOuterFockElliptic.dsFriedComparison_esa
#audit_axioms BookProof.QgOuterFockElliptic.sectorHam_quadForm_nonneg
#audit_axioms BookProof.QgOuterFockElliptic.outerHam_qgKappa
#audit_axioms BookProof.QgOuterFockElliptic.outer_esa_farisLavine
#audit_axioms BookProof.QgOuterFockElliptic.outer_isPositiveSelfAdjointExtension
#audit_axioms BookProof.QgOuterFockElliptic.qgOuterEllipticFock_esa_farisLavine

-- `ChapterHermiteLadderShift` (plan QG outer Fock, Faris–Lavine route): weighted shifts of an
-- orthonormal family, and the abstract relative bound against a diagonal comparison operator.
#audit_axioms BookProof.HermiteLadder.norm_sum_shift_sq
#audit_axioms BookProof.HermiteLadder.apply_sum_of_shift
#audit_axioms BookProof.HermiteLadder.norm_shift_le_of_diagonal

-- `ChapterGaussCoreQuadBounds` (plan QG outer Fock, Faris–Lavine route): the Gaussian-integral
-- estimates on the Gauss–polynomial core, with constants independent of the dimension.
#audit_axioms BookProof.GaussCoreQuadBounds.coreD_X_comm
#audit_axioms BookProof.GaussCoreQuadBounds.quadForm_harm_eq
#audit_axioms BookProof.GaussCoreQuadBounds.quadForm_harm_nonneg
#audit_axioms BookProof.GaussCoreQuadBounds.norm_sq_le_quadForm_harm
#audit_axioms BookProof.GaussCoreQuadBounds.norm_weighted_kin_le
#audit_axioms BookProof.GaussCoreQuadBounds.norm_mul_le_of_pointwise

-- `ChapterSqSumFarisLavine` (plan QG outer Fock, Faris–Lavine route): the two Faris–Lavine
-- inequalities for `½ Σ_j κ_j π_j² + ½ Σ_r L_r²`, with dimension-free constants.
#audit_axioms BookProof.SqSumFarisLavine.schur_bound
#audit_axioms BookProof.SqSumFarisLavine.potFun_le_of_schur
#audit_axioms BookProof.SqSumFarisLavine.sum_gradFun_sq_le_of_schur
#audit_axioms BookProof.SqSumFarisLavine.commPoly_eq
#audit_axioms BookProof.SqSumFarisLavine.commForm_sqSumOp_le
#audit_axioms BookProof.SqSumFarisLavine.norm_sqSumOp_le

-- `ChapterQgOuterFockCoreFL` (plan QG outer Fock, Faris–Lavine route): the extension of a
-- relatively bounded symmetric operator from a graph core to the whole comparison domain.
#audit_axioms BookProof.QgOuterFockCoreFL.shiftOp_injective
#audit_axioms BookProof.QgOuterFockCoreFL.CoreData.coreRange_dense
#audit_axioms BookProof.QgOuterFockCoreFL.CoreData.ext_core
#audit_axioms BookProof.QgOuterFockCoreFL.CoreData.ext_norm_le
#audit_axioms BookProof.QgOuterFockCoreFL.CoreData.ext_symmetricOn
#audit_axioms BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_le
#audit_axioms BookProof.QgOuterFockCoreFL.CoreData.ext_essentiallySelfAdjointOn

-- `ChapterQgOuterFockFullFL` (plan QG outer Fock, Faris–Lavine route, **unconditional, physical
-- hyperbolic signature**): the sector data of `qgOuterFock_esa_farisLavine` discharged, and the
-- full gauge-fixed 3D quantum-gravity Hamiltonian essentially self-adjoint on the domain of the
-- lifted Friedrichs extension of the positive one-particle operator.
#audit_axioms BookProof.QgOuterFockFullFL.isGraphCore_of_eigenbasis
#audit_axioms BookProof.QgOuterFockFullFL.harmFried_isGraphCore
#audit_axioms BookProof.QgOuterFockFullFL.qgTorsionVecN_row_le
#audit_axioms BookProof.QgOuterFockFullFL.qgTorsionVecN_col_le
#audit_axioms BookProof.QgOuterFockFullFL.qgSectorHam_norm_le
#audit_axioms BookProof.QgOuterFockFullFL.qgSectorHam_commForm_le
#audit_axioms BookProof.QgOuterFockFullFL.qgSectorExt_symmetricOn
#audit_axioms BookProof.QgOuterFockFullFL.qgSectorExt_commForm_le
#audit_axioms BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full

-- `ChapterQgOuterFockInteractionFL` (plan QG outer Fock, Faris–Lavine route, **interacting**):
-- uniform families of sector Hamiltonians whose linear forms may mix the coordinates of
-- different particles, and the gauge-fixed 3D gravity Hamiltonian with nearest-neighbour torsion
-- couplings, essentially self-adjoint on the outer Fock space by Faris–Lavine.
#audit_axioms BookProof.QgOuterFockInteractionFL.QgFamily.secHam_norm_le
#audit_axioms BookProof.QgOuterFockInteractionFL.QgFamily.secHam_commForm_le
#audit_axioms BookProof.QgOuterFockInteractionFL.QgFamily.secExt_commForm_le
#audit_axioms BookProof.QgOuterFockInteractionFL.QgFamily.outerHam_esa
#audit_axioms BookProof.QgOuterFockInteractionFL.QgFamily.esa_farisLavine
#audit_axioms BookProof.QgOuterFockInteractionFL.qgIntVec_row_le
#audit_axioms BookProof.QgOuterFockInteractionFL.qgIntVec_col_le
#audit_axioms BookProof.QgOuterFockInteractionFL.qgCoupling_spans_two_particles
#audit_axioms BookProof.QgOuterFockInteractionFL.qgInt_coupling_nontrivial
#audit_axioms BookProof.QgOuterFockInteractionFL.qgInteracting_esa_core
#audit_axioms BookProof.QgOuterFockInteractionFL.qgInteracting_esa_farisLavine

-- `ChapterScalaronFiberFL` (the scalaron fibre with the full exponential wall): essential
-- self-adjointness of `−∂²_φ + φ²/4 + V(φ) + s` on the compactly supported smooth core, its
-- quadratic form, the shift-uniform relative bounds, and the Friedrichs extension as a
-- Faris–Lavine comparison operator with the core as a graph core.
#audit_axioms BookProof.ScalaronFiberFL.WallPot.ham_esa
#audit_axioms BookProof.ScalaronFiberFL.ham_quadForm
#audit_axioms BookProof.ScalaronFiberFL.norm_sq_le_quadForm
#audit_axioms BookProof.ScalaronFiberFL.ham_x_comm
#audit_axioms BookProof.ScalaronFiberFL.WallPot.isGraphCore_core

-- `ChapterScalaronOuterFockFL` (the full quantum-gravity Hamiltonian on the outer Fock space):
-- symmetry, the Schur relative bound, the Faris–Lavine commutator bound and essential
-- self-adjointness on the domain of the lifted Friedrichs extension `N`.
#audit_axioms BookProof.ScalaronOuterFockFL.secN_isGraphCore
#audit_axioms BookProof.ScalaronOuterFockFL.secHam_rel
#audit_axioms BookProof.ScalaronOuterFockFL.secHam_symmetricOn
#audit_axioms BookProof.ScalaronOuterFockFL.imA_le
#audit_axioms BookProof.ScalaronOuterFockFL.imB_le
#audit_axioms BookProof.ScalaronOuterFockFL.secHam_commForm_le
#audit_axioms BookProof.ScalaronOuterFockFL.secData_ext_core
#audit_axioms BookProof.ScalaronOuterFockFL.secHam_essentiallySelfAdjointOn

-- `ChapterQgVielbeinModeInstance` (the concrete 3D gauge-fixed vielbein lattice mode data).
#audit_axioms BookProof.QgVielbeinModeInstance.ofBounds
#audit_axioms BookProof.QgVielbeinModeInstance.ofFintype
#audit_axioms BookProof.QgVielbeinModeInstance.torsionGram_herm
#audit_axioms BookProof.QgVielbeinModeInstance.qgLattice_essentiallySelfAdjointOn
#audit_axioms BookProof.QgVielbeinModeInstance.qgLattice_ext_core
#audit_axioms BookProof.QgVielbeinModeInstance.starobinsky_qgLattice_esa

-- `ChapterQgContinuumModeInstance` (the non-lattice mode data: infinitely many exact Fourier
-- modes, exact derivative symbols).
#audit_axioms BookProof.QgContinuumModeInstance.contTorsionGram_herm
#audit_axioms BookProof.QgContinuumModeInstance.norm_contTorsionGram_le
#audit_axioms BookProof.QgContinuumModeInstance.contTorsionGram_ne_zero
#audit_axioms BookProof.QgContinuumModeInstance.qgContinuum_essentiallySelfAdjointOn
#audit_axioms BookProof.QgContinuumModeInstance.qgContinuum_ext_core
#audit_axioms BookProof.QgContinuumModeInstance.starobinsky_qgContinuum_esa

-- `ChapterQgBrstDerivativeGauge` (BRST gauge fixing of an auxiliary variable to a spatial
-- derivative, and the restriction principle for the mode data).
#audit_axioms BookProof.QgBrstDerivativeGauge.restrict_essentiallySelfAdjointOn
#audit_axioms BookProof.QgBrstDerivativeGauge.gaugeReduce_extTorsionCoef
#audit_axioms BookProof.QgBrstDerivativeGauge.gaugeReduce_gram
#audit_axioms BookProof.QgBrstDerivativeGauge.brstGaugeFixed_esa
#audit_axioms BookProof.QgBrstDerivativeGauge.starobinsky_brstGaugeFixed_esa
#audit_axioms BookProof.QgBrstDerivativeGauge.gaugeFixedSubset_esa

-- `ChapterQgOuterFockFlow` (the unitary dynamics and its numerical transfer).
#audit_axioms BookProof.QgOuterFockFlow.comparison_dom_dense
#audit_axioms BookProof.QgOuterFockFlow.qgOuterFock_stone_flow
#audit_axioms BookProof.QgOuterFockFlow.starobinsky_qgContinuum_stone_flow
#audit_axioms BookProof.QgOuterFockFlow.qgOuterFock_numerical_flow_convergence
#audit_axioms BookProof.QgOuterFockFlow.starobinsky_qgContinuum_numerical_flow_convergence

-- `ChapterQgOuterFockOneParticle` (the outer Hamiltonian as a one-particle operator between a
-- creation and an annihilation operator).
#audit_axioms BookProof.QgOuterFockOneParticle.secHam_single
#audit_axioms BookProof.QgOuterFockOneParticle.secHam_matrix_element
#audit_axioms BookProof.QgOuterFockOneParticle.oneParticleOp_herm
#audit_axioms BookProof.QgOuterFockOneParticle.secHam_eq_sum_oneParticle
#audit_axioms BookProof.QgOuterFockOneParticle.starobinsky_qgContinuum_matrix_element

-- `ChapterQgTruncationResolvent` (strong resolvent convergence of the mode truncations, and
-- the resulting unconditional convergence of the numerical flows).
#audit_axioms BookProof.QgTruncationResolvent.esa_core_of_ext
#audit_axioms BookProof.QgTruncationResolvent.strongResolventConvergence_of_core
#audit_axioms BookProof.QgTruncationResolvent.secHam_esa_core
#audit_axioms BookProof.QgTruncationResolvent.secHam_truncate_eventually_eq
#audit_axioms BookProof.QgTruncationResolvent.qgOuterFock_truncation_flow_convergence
#audit_axioms
  BookProof.QgTruncationResolvent.starobinsky_qgContinuum_momentumCutoff_flow_convergence
#audit_axioms BookProof.QgTruncationResolvent.isShiftInvertC_neg_resCLM
#audit_axioms BookProof.QgTruncationResolvent.qg_truncation_hashimoto_shiftInvert_tendsto

-- `ChapterQgTimeStepping` (the time half of a concrete scheme: the Crank–Nicolson/Cayley
-- step, its unitarity, its consistency and the convergence of the fully discrete evolution).
#audit_axioms BookProof.QgTimeStepping.norm_cnStep_apply
#audit_axioms BookProof.QgTimeStepping.cnStep_second_order
#audit_axioms BookProof.QgTimeStepping.norm_cnStep_sub_stoneU_le
#audit_axioms BookProof.QgTimeStepping.norm_iterate_cnStep_sub_stoneU_le
#audit_axioms BookProof.QgTimeStepping.tendsto_iterate_cnStep
#audit_axioms BookProof.QgTimeStepping.qgOuterFock_fullyDiscrete_convergence

-- `ChapterSirkSingleTimeShift` (no time discretization is needed: one shift, one finite
-- time).  The resolvent identity, normality of the resolvent, shift-independence of strong
-- resolvent convergence, the single-finite-time flow convergence, the Hashimoto shift-invert
-- operator at an arbitrary complex shift, the SIRK bound at one finite time, and the
-- quantum-gravity instances.
#audit_axioms BookProof.SirkSingleTime.res_sub_res
#audit_axioms BookProof.SirkSingleTime.norm_res_neg
#audit_axioms BookProof.SirkSingleTime.strongResAt_of_abs_sub_lt
#audit_axioms BookProof.SirkSingleTime.strongResAt_neg
#audit_axioms BookProof.SirkSingleTime.strongResAt_of_ne_zero
#audit_axioms BookProof.SirkSingleTime.strongResolventConvergence_of_strongResAt
#audit_axioms BookProof.SirkSingleTime.singleTime_flow_tendsto_of_strongResAt
#audit_axioms BookProof.SirkSingleTime.isShiftInvertC_neg_resCLM_shift
#audit_axioms BookProof.SirkSingleTime.norm_neg_resCLM_apply_le
#audit_axioms BookProof.SirkSingleTime.sirk_single_time_shiftInvert_bound
#audit_axioms BookProof.SirkSingleTime.qgOuterFock_singleTime_shiftInvert_convergence
#audit_axioms
  BookProof.SirkSingleTime.starobinsky_qgContinuum_singleTime_shiftInvert_convergence

-- `ChapterQgManifoldModeInstance` (the same quantum-gravity Hamiltonian over a general
-- spatial manifold rather than a periodic box).
#audit_axioms BookProof.QgManifoldModeInstance.qgManifold_essentiallySelfAdjointOn
#audit_axioms BookProof.QgManifoldModeInstance.starobinsky_qgManifold_esa
#audit_axioms
  BookProof.QgManifoldModeInstance.starobinsky_qgManifold_cutoff_flow_convergence
#audit_axioms
  BookProof.QgManifoldModeInstance.starobinsky_qgManifold_fullyDiscrete_convergence

-- `ChapterQgTimeIndependentFlow` (the gauge-fixed Hamiltonian carries no time dependence,
-- so the propagator is a one-parameter group evaluated at a single finite time): the
-- two-parameter propagator, its Chapman–Kolmogorov law and time-translation invariance,
-- uniqueness of the solution of the Schrödinger equation with the fixed generator, and the
-- quantum-gravity instances (3D BRST gauge-fixed continuum model, general manifold).
#audit_axioms BookProof.QgTimeIndependent.prop_apply_prop
#audit_axioms BookProof.QgTimeIndependent.prop_time_translation
#audit_axioms BookProof.QgTimeIndependent.isSchrodingerSolution_prop
#audit_axioms BookProof.QgTimeIndependent.eq_prop_of_isSchrodingerSolution
#audit_axioms BookProof.QgTimeIndependent.qgOuterFock_timeIndependent_singleTime
#audit_axioms
  BookProof.QgTimeIndependent.starobinsky_brstGaugeFixed_timeIndependent_singleTime
#audit_axioms
  BookProof.QgTimeIndependent.starobinsky_qgManifold_timeIndependent_singleTime

-- `ChapterFiniteSectionSingleTime` (the finite-section/Galerkin scheme on an `ℓ²` mode
-- space): the mode projections, the bounded self-adjoint finite section, its convergence to
-- the Hamiltonian on the core, the single-shift/single-finite-time package, and the
-- propagator of a selected self-adjoint extension.
#audit_axioms BookProof.FiniteSectionSingleTime.projW_apply_tendsto
#audit_axioms BookProof.FiniteSectionSingleTime.secOp_isSelfAdjoint
#audit_axioms BookProof.FiniteSectionSingleTime.secOp_tendsto_core
#audit_axioms BookProof.FiniteSectionSingleTime.isSelfAdjointExtension_ofBounded
#audit_axioms BookProof.FiniteSectionSingleTime.finiteSection_singleTime
#audit_axioms BookProof.FiniteSectionSingleTime.timeIndependent_of_selfAdjointExtension
#audit_axioms BookProof.FiniteSectionSingleTime.windowOfEquiv_exhausts

-- `ChapterNsTimeIndependentFlow` (the `y`-gauge-fixed Navier–Stokes Hamiltonian is
-- autonomous, and one finite time suffices): the Eulerian fiber Hamiltonian, the same with
-- the gauge-fixing identities as first conjuncts, and the canonical Lagrangian Hamiltonian.
#audit_axioms BookProof.NsTimeIndependent.nsEulerian_timeIndependent_singleTime
#audit_axioms BookProof.NsTimeIndependent.nsGaugeY_timeIndependent_singleTime
#audit_axioms BookProof.NsTimeIndependent.nsLagrangian_timeIndependent_singleTime

-- `ChapterQymTimeIndependentFlow` (the Weyl-gauge quantum Yang–Mills Hamiltonian is
-- autonomous, and one finite time suffices): the Friedrichs realization with its
-- time-translation-invariant propagator, the finite-section package under essential
-- self-adjointness, and its unconditional diagonal-basis instance.
#audit_axioms BookProof.QymTimeIndependent.ymFock_weylGauge_timeIndependent
#audit_axioms BookProof.QymTimeIndependent.ymFock_timeIndependent_singleTime_of_esa
#audit_axioms
  BookProof.QymTimeIndependent.ymFock_diagonalBasis_timeIndependent_singleTime

-- `ChapterSqSumOuterFamily` (the outer-Fock Faris–Lavine instrument at an arbitrary fibre
-- dimension): the finite-particle core inside the domain of the lifted comparison operator,
-- and the Faris–Lavine headline for a uniform kinetic-plus-squares family.
#audit_axioms BookProof.SqSumOuterFamily.outerCore_le_friedDom
#audit_axioms BookProof.SqSumOuterFamily.outerFriedN_esa
#audit_axioms BookProof.SqSumOuterFamily.SqFamily.esa_farisLavine

-- `ChapterNsOuterFockFarisLavine` (the gauge-fixed Navier–Stokes Hamiltonian on the outer
-- Fock space, by Faris–Lavine): the Schur data uniform in the parcel number, the genuinely
-- inter-parcel coupling of the derivative gauge-fixing forms, essential self-adjointness on
-- the finite-particle core, and the headline on the domain of the lifted Friedrichs
-- extension of `N₁ = −Δ + ‖x‖²/4`.
#audit_axioms BookProof.NsOuterFock.nsVec_row_le
#audit_axioms BookProof.NsOuterFock.nsVec_col_le
#audit_axioms BookProof.NsOuterFock.linForm_nsConstraint
#audit_axioms BookProof.NsOuterFock.linForm_nsTie
#audit_axioms BookProof.NsOuterFock.linForm_nsLap
#audit_axioms BookProof.NsOuterFock.linForm_nsGaugeY
#audit_axioms BookProof.NsOuterFock.nsVec_coupling
#audit_axioms BookProof.NsOuterFock.ns_interaction_nontrivial
#audit_axioms BookProof.NsOuterFock.nsOuterHam_symmetricOn
#audit_axioms BookProof.NsOuterFock.nsOuterHam_esa_core
#audit_axioms BookProof.NsOuterFock.nsOuterFock_esa_farisLavine

-- 2026-10-15b work order (CONSOLIDATED_PLAN.md, "closing the two open halves of the
-- transformed-ESA entry"): the real-shift lemma; ODE-C.1–3; NS-L-C.1–3 (the lifted comparison
-- `dΓ(N) + 1`); QG-D-C.2–3 (QG-D-C.1 is the named open hypothesis `hflat`).
#audit_axioms BookProof.EsaRealShift.deficiencyTrivialAt_of_essentiallySelfAdjointOn
#audit_axioms BookProof.EsaRealShift.essentiallySelfAdjointOn_add_const
#audit_axioms BookProof.MomentumChart.momentum_essentiallySelfAdjointOn
#audit_axioms BookProof.OdeChartTransfer.conj_essentiallySelfAdjointOn
#audit_axioms BookProof.OdeChartTransfer.chartUnitary_apply
#audit_axioms BookProof.OdeChartTransfer.chartHam_essentiallySelfAdjointOn
#audit_axioms BookProof.OdeChartTransfer.chartHam_apply_ae
#audit_axioms BookProof.OdeChartTransfer.chartHam_stone_flow
#audit_axioms BookProof.NsComparisonEsa.lagConstr_esa
#audit_axioms BookProof.NsComparisonEsa.lagConstr_hasZeroDeficiencyOn
#audit_axioms BookProof.NsComparisonEsa.lagCompN_eq
#audit_axioms BookProof.NsComparisonEsa.lagCompN_esa
#audit_axioms BookProof.NsComparisonEsa.lagCompN_nonneg
#audit_axioms BookProof.NsComparisonEsa.lagCompN_add_one_ge
#audit_axioms BookProof.LiftedComparisonEsa.liftedComparison_dGamma_esa
#audit_axioms BookProof.LiftedComparisonEsa.liftedComparison_esa
#audit_axioms BookProof.LiftedComparisonEsa.liftedComparison_resolvent_deficiency
#audit_axioms BookProof.LiftedComparisonEsa.lagKoopman_liftedComparison_esa_of_comparison_esa
#audit_axioms BookProof.QgAssembledTransfer.assembled_transfer
#audit_axioms BookProof.QgAssembledTransfer.qg_assembled_halfDensity_transfer
#audit_axioms BookProof.QgAssembledTransfer.qg_assembled_conformal_hasZeroDeficiencyOn
#audit_axioms BookProof.QgAssembledTransfer.qg_assembled_stone_flow_of_flat
#audit_axioms BookProof.NsLagrangianComparisonEsa.lagComparison_esa
#audit_axioms BookProof.NsLagrangianComparisonEsa.lagKoopman_esa
#audit_axioms BookProof.QgFlatContinuumEsa.flatOp_esa
#audit_axioms BookProof.QgFlatContinuumEsa.flatOp_deficiencyTrivialAt
#audit_axioms BookProof.QgFlatContinuumEsa.flatOp_stone_flow
#audit_axioms BookProof.QgFlatContinuumEsa.schOp_esa
#audit_axioms BookProof.QgFlatContinuumEsa.exists_schOp_repr
#audit_axioms BookProof.QgFlatContinuumEsa.qgFlat_esa
#audit_axioms BookProof.QgFlatContinuumEsa.qgFlat_deficiencyTrivialAt
#audit_axioms BookProof.QgFlatContinuumEsa.prodUnitary_tmul_ae
#audit_axioms BookProof.QgFlatContinuumEsa.qgFlatL2Op_tmul
#audit_axioms BookProof.QgFlatContinuumEsa.qgFlatL2_esa
#audit_axioms BookProof.QgFlatContinuumEsa.qgFlatL2_deficiencyTrivialAt
#audit_axioms BookProof.QgFlatContinuumEsa.qgFlatL2_stone_flow
#audit_axioms BookProof.QgFlatContinuumEsa.qgFlat84_deficiencyTrivialAt
#audit_axioms BookProof.QgFlatContinuumEsa.esa_of_unitary_intertwines
#audit_axioms BookProof.QgFlatContinuumEsa.qg_flat_transfer_esa
-- QG-D-C step 2a (CONSOLIDATED_PLAN.md §"2026-10-17"): the assembled transfer without `hflat`
#audit_axioms BookProof.QgAssembledFlatTransfer.deficiencyTrivialAt_total_of_flat
#audit_axioms BookProof.QgAssembledFlatTransfer.qg_assembled_flat_hasZeroDeficiencyOn
#audit_axioms BookProof.QgAssembledFlatTransfer.qg_assembled_flat_hasZeroDeficiencyOn_termwise
#audit_axioms BookProof.QgAssembledFlatTransfer.qg_assembled_flat_stone_flow


end BookProof.ChapterRoadmapAudit
