/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import BookProof.RoadmapAudit.ChapterRoadmapAuditImports

/-!
# Roadmap headline certificate — audit ledger, slice 4 of 8

Slice 4 of the eight slices of the `#audit_axioms` ledger that used to sit at the end of
`BookProof/RoadmapAudit/ChapterRoadmapAudit.lean`.  The directives are the original ones,
verbatim and in the original order; the split exists only so that Lake elaborates eight modules in
parallel instead of one, which is where the aggregate build's 25 minutes went.

Each line prints the stock `'name' depends on axioms: [...]` line for one declaration; nothing
here asserts an axiom set.
-/

namespace BookProof.ChapterRoadmapAudit

open BookProof.AxiomAudit

-- `ChapterNavierStokesDiffHashimoto`: the Hashimoto/SIRK selection theorem on the
-- *differential* realization of the Navier–Stokes fiber generator.  The Weyl-ordered
-- polynomial operator `∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)` is Gauss symmetric, so the differential operator is
-- symmetric on the Gauss–polynomial core of `L²(du₁du₂du₃)`; with the essential
-- self-adjointness of `ChapterNavierStokesDifferentialL2` its closure is the unique
-- self-adjoint extension, and for an arbitrary sequence of non-real shifts the SIRK
-- resolvents exist, are bounded by `1/|Im γⱼ|`, share the domain of the generator, satisfy
-- the resolvent identity and the Hashimoto–Nodera relation, have strongly convergent
-- Galerkin truncations, and each determines the generator completely.
#audit_axioms BookProof.NavierStokesFlow.DiffHashimoto.nsDiffPoly_polySym
#audit_axioms BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_eq_coreOp
#audit_axioms BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_symmetricOn
#audit_axioms BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension
#audit_axioms BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension_unique
#audit_axioms BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_hashimoto_selects
#audit_axioms BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_shiftInvert_selects
#audit_axioms BookProof.NavierStokesFlow.DiffHashimoto.nsQuadraticDiffH_hashimoto_selects
#audit_axioms BookProof.NavierStokesFlow.DiffHashimoto.exists_l2dHilbertBasisNat

-- `ChapterStarobinskyPotential`: the `R + αR²` potentials and the flow of the regularized
-- conformal mode.  `f(R) = (M²/2)ψR − U(ψ)` is the ghost-free scalar–tensor form; the
-- Einstein-frame scalaron potential is a square, hence non-negative, vanishing at the
-- Minkowski vacuum, with the inflationary plateau `M⁴/(16α)` at `φ → +∞` and an exponential
-- wall at `φ → −∞`; completing the square shows the conformal-mode potential is bounded below
-- by `−M⁴/(16α)` precisely when `α > 0` (and unbounded below at `α = 0`, which is pure
-- general relativity).  At the mode level the resulting Hamiltonian is symmetric and
-- essentially self-adjoint on a dense maximal domain, so the Stone bridge gives it a complete
-- unitary flow.
#audit_axioms BookProof.Starobinsky.fR_eq_scalarTensor
#audit_axioms BookProof.Starobinsky.starobinskyV_nonneg
#audit_axioms BookProof.Starobinsky.starobinskyV_zero
#audit_axioms BookProof.Starobinsky.starobinskyV_tendsto_plateau
#audit_axioms BookProof.Starobinsky.starobinskyV_tendsto_atBot_atTop
#audit_axioms BookProof.Starobinsky.confV_completed_square
#audit_axioms BookProof.Starobinsky.confV_ge
#audit_axioms BookProof.Starobinsky.confV_bddBelow
#audit_axioms BookProof.Starobinsky.confV_zero_alpha_tendsto_atBot
#audit_axioms BookProof.Starobinsky.mulSymbolDomain_dense
#audit_axioms BookProof.Starobinsky.qgR2Mode_potential_ge
#audit_axioms BookProof.Starobinsky.qgR2Mode_esa
#audit_axioms BookProof.Starobinsky.qgR2Mode_deficiencyTrivialAt
#audit_axioms BookProof.Starobinsky.qgR2_stone_flow

-- `ChapterScalaronCoreEsa`: the scalaron sector with its exponential wall.  The compactly
-- supported smooth core of `L²` is dense (`ccDomain_dense`), and on it multiplication by an
-- *arbitrary smooth* real potential is symmetric with trivial deficiency at every non-real
-- point, hence essentially self-adjoint — no temperate growth, no boundedness and no
-- semiboundedness hypothesis.  The Einstein-frame scalaron potential is smooth but provably
-- *not* of temperate growth, so this is exactly the generality it needs; the full gauge-fixed
-- `R + αR²` potential (conformal parabola plus scalaron) is likewise essentially self-adjoint
-- and bounded below by `−M⁴/(16α)`.  `□ + V` is a symmetric operator on that dense core and
-- each of its localizations is essentially self-adjoint on the Schwartz core.  At the mode
-- level the Hamiltonian including the scalaron potential is essentially self-adjoint on its
-- dense maximal domain and carries a complete unitary flow.
#audit_axioms BookProof.ScalaronEsa.ccDomain_dense
#audit_axioms BookProof.ScalaronEsa.smoothPotential_symmetric
#audit_axioms BookProof.ScalaronEsa.smoothPotential_deficiencyTrivial
#audit_axioms BookProof.ScalaronEsa.smoothPotential_essentiallySelfAdjoint
#audit_axioms BookProof.ScalaronEsa.contDiff_starobinskyV
#audit_axioms BookProof.ScalaronEsa.starobinskyV_not_hasTemperateGrowth
#audit_axioms BookProof.ScalaronEsa.starobinskyV_essentiallySelfAdjoint
#audit_axioms BookProof.ScalaronEsa.scalaronFullPotential_ge
#audit_axioms BookProof.ScalaronEsa.scalaronFullPotential_essentiallySelfAdjoint
#audit_axioms BookProof.ScalaronEsa.wave_add_scalaron_symmetric
#audit_axioms BookProof.ScalaronEsa.wave_add_smoothTruncatedPotential_essentiallySelfAdjoint
#audit_axioms BookProof.ScalaronEsa.wave_add_scalaronTruncated_esa
#audit_axioms BookProof.ScalaronEsa.wave_add_smoothPotential_esa_of_finiteSpeed
#audit_axioms BookProof.ScalaronEsa.wave_add_scalaron_esa_of_finiteSpeed
#audit_axioms BookProof.ScalaronEsa.qgScalaronMode_potential_ge
#audit_axioms BookProof.ScalaronEsa.qgScalaronMode_esa
#audit_axioms BookProof.ScalaronEsa.qgScalaron_stone_flow

-- `ChapterScalaronFockEsa`: from one particle to the **nested Fock space**.  The sector cores
-- glue to a dense core of `⊕ₙ L²(Eₙ)`; the sector-wise multiplication operator by an arbitrary
-- family of smooth potentials is symmetric, has trivial deficiency at every non-real point,
-- is essentially self-adjoint and generates the unitary group.  Applied to the gauge-fixed
-- `R + αR²` many-body potential `∑ⱼ (V₃(R_c ⱼ) + V(φ ⱼ))` — smooth, bounded below by
-- `−n·M⁴/(16α)`, and at `n = 1` the one-particle potential of `ChapterScalaronCoreEsa` — this
-- gives essential self-adjointness and the unitary group `e^{−itH}` of the scalaron
-- Hamiltonian on the whole finite-particle Fock space, and likewise in the mode realisation.
#audit_axioms BookProof.ScalaronFock.nestedCore_dense
#audit_axioms BookProof.ScalaronFock.fockSmoothPotential_symmetric
#audit_axioms BookProof.ScalaronFock.fockSmoothPotential_deficiencyTrivialAt
#audit_axioms BookProof.ScalaronFock.fockSmoothPotential_esa
#audit_axioms BookProof.ScalaronFock.fockSmoothPotential_stone_flow
#audit_axioms BookProof.ScalaronFock.qgManyPotential_apply
#audit_axioms BookProof.ScalaronFock.qgManyPotential_one
#audit_axioms BookProof.ScalaronFock.contDiff_qgManyPotential
#audit_axioms BookProof.ScalaronFock.qgManyPotential_ge
#audit_axioms BookProof.ScalaronFock.qgManyPotential_esa
#audit_axioms BookProof.ScalaronFock.qgFockCore_dense
#audit_axioms BookProof.ScalaronFock.qgScalaronFock_symmetric
#audit_axioms BookProof.ScalaronFock.qgScalaronFock_deficiencyTrivialAt
#audit_axioms BookProof.ScalaronFock.qgScalaronFock_esa
#audit_axioms BookProof.ScalaronFock.qgScalaronFock_stone_flow
#audit_axioms BookProof.ScalaronFock.modeFockCore_dense
#audit_axioms BookProof.ScalaronFock.qgScalaronModeFock_symmetric
#audit_axioms BookProof.ScalaronFock.qgScalaronModeFock_deficiencyTrivialAt
#audit_axioms BookProof.ScalaronFock.qgScalaronModeFock_esa
#audit_axioms BookProof.ScalaronFock.qgScalaronModeFock_stone_flow
#audit_axioms BookProof.ScalaronFock.qgScalaronModeFock_potential_ge

-- `ChapterNavierStokesDiffFarisLavine`: the two Faris–Lavine inequalities for the Navier–Stokes
-- quadratic symbol as an actual differential operator on `L²(du₁du₂du₃)` (plan item A4).  The
-- comparison operator is the differential harmonic oscillator
-- `nsDiffN μ = 2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1`, identified with the transported number operator by the
-- polynomial identity `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½` (`oscOp_eq_number`); the Gauss–polynomial core
-- *is* the transported finite-mode core (`embedCore_surjective`).  On that core the relative
-- bound `‖Hf‖² ≤ a‖Nf‖² + b‖f‖²` and the form-commutator bound `|⟪f, i[H,N]f⟫| ≤ c⟪f, Nf⟫` hold,
-- and the same pair on the maximal domain of `N` in `L²(ℝ³)` yields essential self-adjointness
-- of the differentially written symbol directly from the Faris–Lavine criterion — the
-- alternative route to `ChapterNavierStokesDifferentialL2.nsDiffH_essentiallySelfAdjointOn_core`.
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.crd_numSeq
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.velNcore_eq_diagMax
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.oscPoly_eq
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.oscOp_eq_number
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_eq_ladder
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.intertwined_nsDiffN
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.embedCore_surjective
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_symmetricOn
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_quadForm_ge_norm_sq
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_relative_bound
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_commForm_bound
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_symmetricOn
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_quadForm_nonneg
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_add_one_surjective
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_core_approx
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_relative_bound
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_commForm_bound
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_restrict
#audit_axioms BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine

-- `ChapterScalaronDensitizedTransfer`: step 2 of plan item A5 — the conformal-mode potential
-- after the densitized change of variables `e = y²`.  `densConfV M α y = V₃(y²)` is the
-- pullback of the conformal-mode potential along `y = √e`; it is still bounded below by
-- `−M⁴/(16α)` (`densConfV_ge`), and still unbounded below at `α = 0`
-- (`densConfV_zero_alpha_tendsto_atBot`), so the bound is bought by `αR²` and not by the
-- densitization.  The half-density unitary of `ChapterQuantumGravityHalfDensity` carries the
-- bounded-energy core of `L²((0,∞), de)` onto that of `L²((0,∞), 2y dy)` and intertwines the
-- two multiplication Hamiltonians, so vanishing adjoint deficiency transfers along it
-- (`physConf_hasZeroDeficiencyOn_transfer`), with the Stone flows on both sides.  At the
-- operator level, a pointwise lower bound on the multiplier is semiboundedness of the
-- operator (`multOp_quadForm_eq`, `multOp_quadForm_ge`, `densConfOp_quadForm_ge`).
#audit_axioms BookProof.ScalaronDensitized.densConfV_comp_densY
#audit_axioms BookProof.ScalaronDensitized.densConfV_ge
#audit_axioms BookProof.ScalaronDensitized.densConfV_bddBelow
#audit_axioms BookProof.ScalaronDensitized.densConfV_zero_alpha_tendsto_atBot
#audit_axioms BookProof.ScalaronDensitized.physConfCore_dense
#audit_axioms BookProof.ScalaronDensitized.densConfCore_dense
#audit_axioms BookProof.ScalaronDensitized.physConfOp_symmetricOn
#audit_axioms BookProof.ScalaronDensitized.densConfOp_symmetricOn
#audit_axioms BookProof.ScalaronDensitized.halfDensityUnitary_mem_densConfCore
#audit_axioms BookProof.ScalaronDensitized.halfDensityUnitary_densConfCore_surjective
#audit_axioms BookProof.ScalaronDensitized.halfDensityUnitary_intertwines
#audit_axioms BookProof.ScalaronDensitized.densConf_hasZeroDeficiencyOn
#audit_axioms BookProof.ScalaronDensitized.physConf_hasZeroDeficiencyOn_transfer
#audit_axioms BookProof.ScalaronDensitized.physConf_esa
#audit_axioms BookProof.ScalaronDensitized.densConf_esa
#audit_axioms BookProof.ScalaronDensitized.integral_norm_sq_eq_norm_sq
#audit_axioms BookProof.ScalaronDensitized.multOp_quadForm_eq
#audit_axioms BookProof.ScalaronDensitized.multOp_quadForm_ge
#audit_axioms BookProof.ScalaronDensitized.densConfOp_quadForm_ge
#audit_axioms BookProof.ScalaronDensitized.physConfOp_quadForm_ge
#audit_axioms BookProof.ScalaronDensitized.densConf_stone_flow
#audit_axioms BookProof.ScalaronDensitized.physConf_stone_flow

-- `ChapterSirkEndToEnd`: the end-to-end SIRK reliability assembly (plan §12 Gap 1).
-- `sirk_error_bound_at` is the pointwise-transfer strengthening of `ChapterH4.sirk_error_bound`
-- that makes the composition possible; `sirk_end_to_end` then has no transfer hypothesis left,
-- discharging it from the isometry, the Krylov invariance and the invertible denominator via
-- `ChapterH8.compress_rational_transfer`.  `crouzeix_domain_transfer` shows one convex domain
-- serves both Crouzeix bounds; `sirk_flow_error_tendsto_zero` and
-- `sirk_flow_error_uniform_in_time` are the convergence conclusions (§12 Gap 3, bound half);
-- `sirkReconstruction_isIdempotent`/`_isSelfAdjoint` identify reconstruction with the
-- orthogonal projection onto the retained subspace (§12 Gap 4a).
#audit_axioms BookProof.ChapterSirkEndToEnd.sirkApprox_id
#audit_axioms BookProof.ChapterSirkEndToEnd.sirkReconstruction_isIdempotent
#audit_axioms BookProof.ChapterSirkEndToEnd.sirkReconstruction_isSelfAdjoint
#audit_axioms BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le
#audit_axioms BookProof.ChapterSirkEndToEnd.norm_sirkApprox_apply_le_of_isometry
#audit_axioms BookProof.ChapterSirkEndToEnd.sirk_error_bound_at
#audit_axioms BookProof.ChapterSirkEndToEnd.crouzeix_domain_transfer
#audit_axioms BookProof.ChapterSirkEndToEnd.crouzeix_domain_uniform
#audit_axioms BookProof.ChapterSirkEndToEnd.sirk_end_to_end
#audit_axioms BookProof.ChapterSirkEndToEnd.tendsto_zero_of_le_sirkBound
#audit_axioms BookProof.ChapterSirkEndToEnd.sirk_flow_error_tendsto_zero
#audit_axioms BookProof.ChapterSirkEndToEnd.sirk_flow_error_uniform_in_time
#audit_axioms BookProof.ChapterSirkEndToEnd.sirk_end_to_end_satisfiable

-- `ChapterSirkMultiShift`: the multi-shift forward-sequence span identity (plan §12 Gap 4b),
-- with the general triangular criterion behind it and the shift-schedule independence of the
-- compressed subspace.
#audit_axioms BookProof.ChapterSirkMultiShift.triangularSpan_eq_krylovSpan
#audit_axioms BookProof.ChapterSirkMultiShift.multiShiftSeq_sub_pow_mem
#audit_axioms BookProof.ChapterSirkMultiShift.krylov_multiShift_eq_standard
#audit_axioms BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts
#audit_axioms BookProof.ChapterSirkMultiShift.multiShiftSeq_const

-- `ChapterSirkRestart`: the restart cycle and its accumulated error (plan §12 Gap 4a).
#audit_axioms BookProof.ChapterSirkRestart.norm_pow_apply_le_of_contraction
#audit_axioms BookProof.ChapterSirkRestart.restart_error_accumulation
#audit_axioms BookProof.ChapterSirkRestart.restart_error_accumulation_sirk
#audit_axioms BookProof.ChapterSirkRestart.restart_error_tendsto_zero
#audit_axioms BookProof.ChapterSirkRestart.comp_pow_of_comm
#audit_axioms BookProof.ChapterSirkRestart.brst_leakage_zero_of_exact
#audit_axioms BookProof.ChapterSirkRestart.brst_leakage_bound

-- `ChapterSirkWhitening`: the reduced operator depends only on the retained subspace
-- (plan §12 Gap 4c) — same range projection, unitary change of whitening, conjugate
-- compressions, and an identical reconstructed operator on the ambient space.
#audit_axioms BookProof.ChapterSirkWhitening.rangeProj_adjoint
#audit_axioms BookProof.ChapterSirkWhitening.rangeProj_isSelfAdjoint
#audit_axioms BookProof.ChapterSirkWhitening.rangeProj_comp_self
#audit_axioms BookProof.ChapterSirkWhitening.rangeProj_eq_of_range_eq
#audit_axioms BookProof.ChapterSirkWhitening.adjoint_comp_rangeProj
#audit_axioms BookProof.ChapterSirkWhitening.whiteningEquiv_isometry
#audit_axioms BookProof.ChapterSirkWhitening.whiteningEquiv_left_inverse
#audit_axioms BookProof.ChapterSirkWhitening.compress_conj_whitening
#audit_axioms BookProof.ChapterSirkWhitening.compress_reconstruct_eq
#audit_axioms BookProof.ChapterSirkWhitening.sirkApprox_eq_of_range_eq

-- `ChapterSirkSpectralGeometry`: the Crouzeix domain of the shift-invert (plan §12 Gap 2,
-- abstract half) — a real segment in the positive/Friedrichs regime, a disc at a non-real
-- shift, inherited by every Krylov compression, and the end-to-end bound in domain form.
#audit_axioms BookProof.ChapterSirkSpectralGeometry.convex_realSegment
#audit_axioms BookProof.ChapterSirkSpectralGeometry.realSegment_subset_closedBall
#audit_axioms BookProof.ChapterSirkSpectralGeometry.numRange_subset_realSegment_of_shiftInvert
#audit_axioms BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvert
#audit_axioms BookProof.ChapterSirkSpectralGeometry.numRange_subset_closedBall_of_shiftInvertC
#audit_axioms BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvertC
#audit_axioms BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_crouzeix_domain
#audit_axioms BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_convexHull
#audit_axioms BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvert
#audit_axioms BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvertC

-- `ChapterSirkPerSystem`: the same domain, instantiated for each physical Hamiltonian
-- (plan §12 Gap 2, concrete half), including the new QG shift-invert.
#audit_axioms BookProof.ChapterSirkPerSystem.ym_sirk_crouzeix_domain
#audit_axioms BookProof.ChapterSirkPerSystem.ns_sirk_crouzeix_domain
#audit_axioms BookProof.ChapterSirkPerSystem.nsDiff_sirk_crouzeix_domain
#audit_axioms BookProof.ChapterSirkPerSystem.lagrangian_sirk_crouzeix_domain
#audit_axioms BookProof.ChapterSirkPerSystem.diagKR_sirk_crouzeix_domain
#audit_axioms BookProof.ChapterSirkPerSystem.qgR2_shiftInvert_selects
#audit_axioms BookProof.ChapterSirkPerSystem.qgR2_sirk_crouzeix_domain

-- `ChapterSirkTruncation`: the rank-truncated Gram case (plan §12 Gap 4c, remaining half).
#audit_axioms BookProof.ChapterSirkTruncation.compress_comp
#audit_axioms BookProof.ChapterSirkTruncation.isometry_comp
#audit_axioms BookProof.ChapterSirkTruncation.sirk_error_bound_at_leaky
#audit_axioms BookProof.ChapterSirkTruncation.transfer_defect_le_of_leakage
#audit_axioms BookProof.ChapterSirkTruncation.adjoint_reconstruction_eq
#audit_axioms BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated
#audit_axioms BookProof.ChapterSirkTruncation.sirk_end_to_end_truncated_of_exact

-- `ChapterSirkGroupTransfer`: the unitary-group transfer for bounded generators
-- (plan §12 Gap 3, the bounded half).
#audit_axioms BookProof.ChapterSirkGroupTransfer.norm_pow_le_of_le
#audit_axioms BookProof.ChapterSirkGroupTransfer.norm_pow_sub_pow_le
#audit_axioms BookProof.ChapterSirkGroupTransfer.norm_exp_sub_exp_le
#audit_axioms BookProof.ChapterSirkGroupTransfer.norm_groupFlow_sub_le
#audit_axioms BookProof.ChapterSirkGroupTransfer.groupFlow_transfer_uniform_on_interval

-- `ChapterSirkTrotterKato`: the Trotter–Kato transfer for unbounded self-adjoint
-- generators (plan §12 Gap 3, the unbounded half).
#audit_axioms BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub
#audit_axioms BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_apply
#audit_axioms BookProof.ChapterSirkTrotterKato.resolvent_commutator_eq
#audit_axioms BookProof.ChapterSirkTrotterKato.hasDerivAt_duhamel
#audit_axioms BookProof.ChapterSirkTrotterKato.norm_res_stoneU_sub_stoneU_res_le
#audit_axioms BookProof.ChapterSirkTrotterKato.tendsto_uniformly_on_isCompact_of_tendsto
#audit_axioms BookProof.ChapterSirkTrotterKato.exists_res_domain_approx
#audit_axioms BookProof.ChapterSirkTrotterKato.trotterKato_uniform_of_mem_range
#audit_axioms BookProof.ChapterSirkTrotterKato.trotterKato_uniform_on_interval
#audit_axioms BookProof.ChapterSirkTrotterKato.trotterKato_tendsto
#audit_axioms BookProof.ChapterSirkTrotterKato.trotterKato_tendstoUniformlyOn

-- `ChapterSirkTrotterKatoGalerkin`: the Galerkin instance of the transfer.
#audit_axioms BookProof.ChapterSirkTrotterKato.resCLM_ofBounded
#audit_axioms BookProof.ChapterSirkTrotterKato.strongResolventConvergence_ofBounded
#audit_axioms BookProof.ChapterSirkTrotterKato.flow_transfer_of_strong_tendsto
#audit_axioms BookProof.ChapterSirkTrotterKato.flow_tendsto_of_strong_tendsto
#audit_axioms BookProof.ChapterSirkTrotterKato.galerkin_flow_transfer
#audit_axioms BookProof.ChapterSirkTrotterKato.galerkin_flow_tendsto

-- `ChapterSirkLagrangianCanonical`: the canonical (ladder) and Fock/momentum Lagrangian
-- realizations acquire their Hashimoto/SIRK selection (plan §12 Gap 2, NS Lagrangian).
#audit_axioms BookProof.ChapterSirkLagrangianCanonical.lagCan_hashimoto_selects
#audit_axioms BookProof.ChapterSirkLagrangianCanonical.lagCan_shiftInvert_selects
#audit_axioms BookProof.ChapterSirkLagrangianCanonical.lagCan_sirk_crouzeix_domain
#audit_axioms BookProof.ChapterSirkLagrangianCanonical.fockLag_esa
#audit_axioms BookProof.ChapterSirkLagrangianCanonical.fockLag_hashimoto_selects
#audit_axioms BookProof.ChapterSirkLagrangianCanonical.fockLag_shiftInvert_selects
#audit_axioms BookProof.ChapterSirkLagrangianCanonical.fockLag_sirk_crouzeix_domain
#audit_axioms BookProof.ChapterSirkLagrangianCanonical.fockLag_stone_flow

-- `ChapterSirkRitzSpectrum`: the Ritz values converge to the bottom of the spectrum of the
-- selected extension (plan §12 Gap 2, QYM).
#audit_axioms BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum
#audit_axioms BookProof.ChapterSirkRitzSpectrum.spectrum_real_nonempty
#audit_axioms BookProof.ChapterSirkRitzSpectrum.spectrum_real_bddBelow
#audit_axioms BookProof.ChapterSirkRitzSpectrum.sInf_spectrum_eq_rayleighInf
#audit_axioms BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_eq_rayleighInf
#audit_axioms BookProof.ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum
#audit_axioms BookProof.ChapterSirkRitzSpectrum.galerkin_ritz_tendsto_sInf_spectrum_of_selected

-- `ChapterSirkDiffusiveDecay`: the laminar decay rate, and its preservation under the SIRK
-- reduction (plan §12 Gap 2, NS Lagrangian).
#audit_axioms BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_apply
#audit_axioms BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_normSq
#audit_axioms BookProof.ChapterSirkDiffusiveDecay.isCoercive_add_algebraMap
#audit_axioms BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_apply_le
#audit_axioms BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_le
#audit_axioms BookProof.ChapterSirkDiffusiveDecay.isCoercive_compress
#audit_axioms BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_compress_apply_le

-- `ChapterQgHermiteCore`: the one-particle Hamiltonian of the gauge-fixed `R + αR²` model
-- is well defined on the Gauss–polynomial (Hermite) core (plan §10.6.1, target 1).
#audit_axioms BookProof.QgHermiteCore.exp_abs_le_const_mul_exp_sq
#audit_axioms BookProof.QgHermiteCore.exp_abs_mul_gaussH_le
#audit_axioms BookProof.QgHermiteCore.tendsto_exp_abs_mul_gaussH_atTop
#audit_axioms BookProof.QgHermiteCore.expBounded_poly
#audit_axioms BookProof.QgHermiteCore.expBounded_starobinskyV
#audit_axioms BookProof.QgHermiteCore.memLp_gaussPoly
#audit_axioms BookProof.QgHermiteCore.memLp_mul_gaussPoly_of_expBounded
#audit_axioms BookProof.QgHermiteCore.memLp_starobinskyV_mul_gaussPoly
#audit_axioms BookProof.QgHermiteCore.memLp_scalaronFull1D_mul_gaussPoly
#audit_axioms BookProof.QgHermiteCore.hasDerivAt_gaussPoly
#audit_axioms BookProof.QgHermiteCore.deriv2_gaussPoly
#audit_axioms BookProof.QgHermiteCore.memLp_hamiltonian_gaussPoly
#audit_axioms BookProof.QgHermiteCore.memLp_scalaronHamiltonian_gaussPoly
#audit_axioms BookProof.QgHermiteCore.integral_gaussPoly_mul
#audit_axioms BookProof.QgHermiteCore.gint_gaussPolyDeriv_antisymm
#audit_axioms BookProof.QgHermiteCore.gint_gaussPolyDeriv_two_symm
#audit_axioms BookProof.QgHermiteCore.integral_kinetic_symm
#audit_axioms BookProof.QgHermiteCore.integral_hamiltonian_symm
#audit_axioms BookProof.QgHermiteCore.integral_scalaronHamiltonian_symm
#audit_axioms BookProof.QgHermiteCore.exists_exp_bound_mvPolyEval
#audit_axioms BookProof.QgHermiteCore.memLp_mul_pgFun_of_expBounded
#audit_axioms BookProof.QgHermiteCore.memLp_scalaronSectorPotential_mul_pgFun

-- `ChapterQgHermiteFriedrichs`: the one-particle Hamiltonian `−Δ + W` on the
-- Gauss–polynomial (Hermite) core is symmetric and semibounded, hence has a canonical
-- Friedrichs realization (plan §10.6.1, towards target 4).
#audit_axioms BookProof.QgHermiteFriedrichs.cpoly_kinPoly
#audit_axioms BookProof.QgHermiteFriedrichs.gaussInt_coreD
#audit_axioms BookProof.QgHermiteFriedrichs.gaussInt_kinPoly
#audit_axioms BookProof.QgHermiteFriedrichs.hamCore_pgLp
#audit_axioms BookProof.QgHermiteFriedrichs.hamCore_symmetricOn
#audit_axioms BookProof.QgHermiteFriedrichs.re_gaussInt_kinPoly_self
#audit_axioms BookProof.QgHermiteFriedrichs.hamCore_quadForm_ge
#audit_axioms BookProof.QgHermiteFriedrichs.hamCore_quadForm_nonneg
#audit_axioms BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension
#audit_axioms BookProof.QgHermiteFriedrichs.hermiteCore_friedrichs_extension_of_nonneg
#audit_axioms BookProof.QgHermiteFriedrichs.qgOneParticleHermite_friedrichs
#audit_axioms BookProof.QgHermiteFriedrichs.qgOneParticleSector_friedrichs
#audit_axioms BookProof.QgHermiteFriedrichs.hasDerivAt_pgFun_coord

-- `ChapterQgHermiteOscillatorEsa`: essential self-adjointness on the Gauss–polynomial core
-- for the harmonic potential, and for bounded perturbations of it (plan §10.6.1, target 4
-- for the parabolic potential).
#audit_axioms BookProof.QgHermiteOscillator.deficiencyTrivialAt_of_eigenbasis
#audit_axioms BookProof.QgHermiteOscillator.essentiallySelfAdjointOn_of_eigenbasis
#audit_axioms BookProof.QgHermiteOscillator.potLp_harmW
#audit_axioms BookProof.QgHermiteOscillator.coreD_sq_add_harm
#audit_axioms BookProof.QgHermiteOscillator.kinPoly_add_harmPoly
#audit_axioms BookProof.QgHermiteOscillator.crePoly_annPoly_hermiteMv
#audit_axioms BookProof.QgHermiteOscillator.harmCore_hermiteMvLp
#audit_axioms BookProof.QgHermiteOscillator.harmonicCore_essentiallySelfAdjoint
#audit_axioms BookProof.QgHermiteOscillator.harmonicCore_stone_flow
#audit_axioms BookProof.QgHermiteOscillator.norm_potLp_le
#audit_axioms BookProof.QgHermiteOscillator.hamCore_add_potential
#audit_axioms BookProof.QgHermiteOscillator.harmonic_add_bounded_essentiallySelfAdjoint

-- `ChapterScalaronHermiteEsa`: essential self-adjointness on the Gauss–polynomial core for
-- an exponentially growing potential — the scalaron potential and the full `(R_c, φ)`
-- sector potential (plan §10.6.1, target 4 for the scalaron potential term).
#audit_axioms BookProof.ScalaronHermiteEsa.gaussExpDecay_of_memLp_mul
#audit_axioms BookProof.ScalaronHermiteEsa.integrable_pgFun_mul_of_gaussExpDecay
#audit_axioms BookProof.ScalaronHermiteEsa.fourier_gaussD_mul_eq_zero_of_gaussExpDecay
#audit_axioms BookProof.ScalaronHermiteEsa.ae_eq_zero_of_moments_of_gaussExpDecay
#audit_axioms BookProof.ScalaronHermiteEsa.gaussExpDecay_potential_sub
#audit_axioms BookProof.ScalaronHermiteEsa.moments_of_deficiency
#audit_axioms BookProof.ScalaronHermiteEsa.potCore_deficiencyTrivialAt
#audit_axioms BookProof.ScalaronHermiteEsa.potCore_essentiallySelfAdjoint
#audit_axioms BookProof.ScalaronHermiteEsa.scalaronPot_essentiallySelfAdjoint
#audit_axioms BookProof.ScalaronHermiteEsa.potCore_stone_flow
#audit_axioms BookProof.ScalaronHermiteEsa.scalaronPot_stone_flow
#audit_axioms BookProof.ScalaronHermiteEsa.scalaronSector_essentiallySelfAdjoint
#audit_axioms BookProof.ScalaronHermiteEsa.scalaronSector_stone_flow


end BookProof.ChapterRoadmapAudit
