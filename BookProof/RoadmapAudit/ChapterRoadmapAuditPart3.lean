/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import BookProof.RoadmapAudit.ChapterRoadmapAuditImports

/-!
# Roadmap headline certificate — audit ledger, slice 3 of 8

Slice 3 of the eight slices of the `#audit_axioms` ledger that used to sit at the end of
`BookProof/RoadmapAudit/ChapterRoadmapAudit.lean`.  The directives are the original ones,
verbatim and in the original order; the split exists only so that Lake elaborates eight modules in
parallel instead of one, which is where the aggregate build's 25 minutes went.

Each line prints the stock `'name' depends on axioms: [...]` line for one declaration; nothing
here asserts an axiom set.
-/

namespace BookProof.ChapterRoadmapAudit

open BookProof.AxiomAudit

-- `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F.11: the second quantization of the
-- field-space Yang–Mills Hamiltonian on the finite-occupation states over the core.
#audit_axioms BookProof.FockSecondQuantization.ccr_annA_creA
#audit_axioms BookProof.FockSecondQuantization.inner_creA_left
#audit_axioms BookProof.FockSecondQuantization.dGamma_one_particle
#audit_axioms BookProof.FockSecondQuantization.dGammaOp_symmetricOn
#audit_axioms BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg
#audit_axioms BookProof.FockSecondQuantization.dGamma_friedrichs_extension
#audit_axioms BookProof.FockSecondQuantization.secondQuantization_friedrichs
#audit_axioms BookProof.FockSecondQuantization.ym_fock_friedrichs_extension
#audit_axioms BookProof.FockSecondQuantization.finiteModeDomain_fockBasisN
#audit_axioms BookProof.FockSecondQuantization.dGamma_hashimoto_selects
#audit_axioms BookProof.FockSecondQuantization.secondQuantization_hashimoto_selects
#audit_axioms BookProof.FockSecondQuantization.ym_fock_hashimoto_selects

-- `CONSOLIDATED_PLAN.md` §9 item 9: the Lagrangian (parcel) route.  Kato–Rellich
-- control of the first-order drift by the positive second-order part obtained
-- from the change of variables, and the Hashimoto/SIRK selection on the
-- Lagrangian side.
#audit_axioms BookProof.KatoRellich.norm_le_of_relBound
#audit_axioms BookProof.KatoRellich.dense_range_add_relBounded
#audit_axioms BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.norm_P_sq_le
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.norm_P_le
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_relBound
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_essentiallySelfAdjointOn
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_hasZeroDeficiencyOn
#audit_axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.hasZeroDeficiencyOn_of_lagrangian_katoRellich
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension
#audit_axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension_unique
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_hashimoto_selects
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_shiftInvert_selects
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_drift_not_bounded
#audit_axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_hFull_essentiallySelfAdjointOn
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_hashimoto_selects
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.norm_sum_P_le
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.drift_dominated_of_drive_eq_P
#audit_axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_hasZeroDeficiencyOn_of_drive_eq_P
#audit_axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.jacobiLag_secondOrder_eq_zero
#audit_axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.jacobiLag_drift_not_relativelyBounded

-- from the Stone bridge and the concrete flows (2026-08-20i): the packaging of a
-- selected self-adjoint extension into the bundled UnboundedSelfAdjoint
-- structure, and the complete unitary flows of the Eulerian NS, Lagrangian NS
-- and QYM Hamiltonians.
#audit_axioms BookProof.StoneBridge.dense_domain_of_isSelfAdjointExtension
#audit_axioms BookProof.StoneBridge.isSelfAdjointOn_of_isSelfAdjointExtension
#audit_axioms BookProof.StoneBridge.isStoneFlow_stoneU
#audit_axioms BookProof.StoneBridge.exists_stone_flow_of_selfAdjointExtension
#audit_axioms BookProof.StoneBridge.exists_stone_flow_of_positive
#audit_axioms BookProof.StoneBridge.exists_stone_flow_of_esa
#audit_axioms BookProof.StoneFlows.ns_stone_flow
#audit_axioms BookProof.StoneFlows.lagrangian_stone_flow
#audit_axioms BookProof.StoneFlows.diagKR_stone_flow
#audit_axioms BookProof.StoneFlows.ym_fock_stone_flow

-- `CONSOLIDATED_PLAN.md` §9 item 11 ("the Lagrangian / Eulerian parity closure"):
-- the canonical (ladder) realization of the Lagrangian second-order part on the
-- trajectory-space Hermite basis, its essential self-adjointness, the essential
-- self-adjointness of the full transformed Hamiltonian and its complete flow.
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.inner_ann_cre
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.posSq_add_momSq
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.comm_lagP_lagQ
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.comm_lagP_lagQ_of_ne
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.half_lagPSq_add_nu_lagQSq
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_secondOrder_eq
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.lagT_hasZeroDeficiencyOn
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.lagT_not_bounded
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_esa
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_hFull_hasZeroDeficiencyOn
#audit_axioms BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_stone_flow

-- Backlog item A1 (`CONSOLIDATED_PLAN.md` §9.5, `STRICHARTZ_WAVE_ESA.md`): the
-- hyperbolic operator with an indefinite quadratic potential.  `H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)`
-- is symmetric and essentially self-adjoint on the Hermite core of `L²(ℝᵈ)` for every
-- real weight vector `c`, and for the Minkowski weights it is `□ + V` with
-- `V(t,x) = (t² − ‖x‖²)/4`.
#audit_axioms BookProof.HyperbolicQuadratic.symmetricOn_of_diagonal
#audit_axioms BookProof.HyperbolicQuadratic.deficiencyTrivialAt_of_diagonal
#audit_axioms BookProof.HyperbolicQuadratic.oscPoly_hermiteMv
#audit_axioms BookProof.HyperbolicQuadratic.quadOp_hermiteMvLp
#audit_axioms BookProof.HyperbolicQuadratic.quadOp_symmetric
#audit_axioms BookProof.HyperbolicQuadratic.quadOp_essentiallySelfAdjoint
#audit_axioms BookProof.HyperbolicQuadratic.quadOp_not_bounded
#audit_axioms BookProof.HyperbolicQuadratic.quadPoly_apply_eq_differential
#audit_axioms BookProof.HyperbolicQuadratic.wave_indefiniteQuadratic_essentiallySelfAdjoint
#audit_axioms BookProof.HyperbolicQuadratic.minkowski_apply_eq_differential
#audit_axioms BookProof.HyperbolicQuadratic.quadOp_add_boundedPotential_essentiallySelfAdjoint
#audit_axioms BookProof.HyperbolicQuadratic.quadOp_add_realBoundedPotential_essentiallySelfAdjoint
#audit_axioms BookProof.HermiteRelative.posL_symmetric
#audit_axioms BookProof.HermiteRelative.momL_symmetric
#audit_axioms BookProof.HermiteRelative.re_inner_oscL_eq
#audit_axioms BookProof.HermiteRelative.norm_posL_le
#audit_axioms BookProof.HermiteRelative.norm_momL_le
#audit_axioms BookProof.HermiteRelative.quadOp_add_firstOrder_essentiallySelfAdjoint
#audit_axioms BookProof.HermiteRelative.hermiteMvBasis_repr_quadOp
#audit_axioms BookProof.HermiteRelative.foOp_linear_apply_eq_mul
#audit_axioms BookProof.HermiteRelative.harmonicOsc_add_linearPotential_essentiallySelfAdjoint

-- Backlog item A1, continued: the *general* (non-diagonal) quadratic Hamiltonian.  For
-- every real symmetric matrix `A`, `H_A = ∑_{k,l} A_{kl}(π_k π_l + x_k x_l/4)` is
-- symmetric and essentially self-adjoint on the same Hermite core, by the orthogonal
-- change of coordinates that diagonalizes `A`.
#audit_axioms BookProof.QuadraticRotation.pderiv_rotPoly
#audit_axioms BookProof.QuadraticRotation.rotPoly_mulXPoly
#audit_axioms BookProof.QuadraticRotation.rotPoly_momPoly
#audit_axioms BookProof.QuadraticRotation.quadPolyMat_rotPoly
#audit_axioms BookProof.QuadraticRotation.quadPolyMat_diagonal
#audit_axioms BookProof.QuadraticRotation.gaussInt_rotPoly
#audit_axioms BookProof.QuadraticRotation.inner_pgLp_rotPoly
#audit_axioms BookProof.QuadraticRotation.orthonormal_rotHermiteLp
#audit_axioms BookProof.QuadraticRotation.span_rotHermiteLp
#audit_axioms BookProof.QuadraticRotation.quadOpMat_rotHermiteLp
#audit_axioms BookProof.QuadraticRotation.exists_rotConj
#audit_axioms BookProof.QuadraticRotation.quadOpMat_symmetric
#audit_axioms BookProof.QuadraticRotation.quadOpMat_essentiallySelfAdjoint
#audit_axioms BookProof.QuadraticRotation.wave_rotated_essentiallySelfAdjoint
#audit_axioms BookProof.QuadraticRotation.quadOpMat_not_bounded
#audit_axioms BookProof.QuadraticRotationPerturbed.rotHermiteBasis_apply
#audit_axioms BookProof.QuadraticRotationPerturbed.rotU_hermiteMvLp
#audit_axioms BookProof.QuadraticRotationPerturbed.rotU_pgLp
#audit_axioms BookProof.QuadraticRotationPerturbed.rotPoly_foPoly
#audit_axioms BookProof.QuadraticRotationPerturbed.rotVec_transpose
#audit_axioms BookProof.QuadraticRotationPerturbed.rotU_intertwine
#audit_axioms BookProof.QuadraticRotationPerturbed.exists_lower_bound_eigenvalues
#audit_axioms BookProof.QuadraticRotationPerturbed.quadOpMat_add_firstOrder_symmetric
#audit_axioms BookProof.QuadraticRotationPerturbed.quadOpMat_add_firstOrder_essentiallySelfAdjoint
#audit_axioms
  BookProof.QuadraticRotationPerturbed.anisotropicOsc_add_linearPotential_essentiallySelfAdjoint

-- `ChapterShiftedHermiteCore`: the translated, modulated Gauss–polynomial core
-- `D_{a,k} = { p(x − a) e^{−‖x − a‖²/4} e^{i⟨k, x⟩} }` of `L²(ℝᵈ)`.  Translation and
-- modulation are unitary substitutions, so the core is dense, the recentred Hermite
-- family is orthonormal and total in it, and the canonical pair acts on polynomials by
-- `mulXTPoly = mulXPoly i + aᵢ`, `momTPoly = momPoly i + kᵢ`.
#audit_axioms BookProof.ShiftedHermiteCore.norm_phaseFun
#audit_axioms BookProof.ShiftedHermiteCore.conj_mul_phaseFun
#audit_axioms BookProof.ShiftedHermiteCore.memLp_pgFunT
#audit_axioms BookProof.ShiftedHermiteCore.inner_pgLpT
#audit_axioms BookProof.ShiftedHermiteCore.pgMapT_injective
#audit_axioms BookProof.ShiftedHermiteCore.polyGaussCoreT_dense
#audit_axioms BookProof.ShiftedHermiteCore.orthonormal_hermiteTLp
#audit_axioms BookProof.ShiftedHermiteCore.span_hermiteTLp
#audit_axioms BookProof.ShiftedHermiteCore.hermiteTLp_total
#audit_axioms BookProof.ShiftedHermiteCore.coreOpT_coe
#audit_axioms BookProof.ShiftedHermiteCore.hasDerivAt_pgFunT_sec
#audit_axioms BookProof.ShiftedHermiteCore.pgFunT_mulXTPoly
#audit_axioms BookProof.ShiftedHermiteCore.pgFunT_momTPoly
-- `ChapterShiftedQuadraticEsa`: the indefinite inhomogeneous quadratic Hamiltonian
-- `H = ∑ᵢ (cᵢ(πᵢ² + xᵢ²/4) + bᵢ xᵢ + b'ᵢ πᵢ)` with weights `cᵢ ≠ 0` of arbitrary sign.
-- Completing the square in both position and momentum makes `H` diagonal in the
-- Hermite basis recentred at `aᵢ = −2bᵢ/cᵢ` and boosted to `kᵢ = −b'ᵢ/(2cᵢ)`, hence
-- symmetric and essentially self-adjoint there, with the pointwise identification of
-- the differential expression; the Minkowski weights give `□ + V` plus an arbitrary
-- constant external field and boost.
#audit_axioms BookProof.ShiftedQuadratic.shiftedHPoly_term
#audit_axioms BookProof.ShiftedQuadratic.shiftedHPoly_eq_quadPoly
#audit_axioms BookProof.ShiftedQuadratic.shiftedHOp_hermiteTLp
#audit_axioms BookProof.ShiftedQuadratic.shiftedHOp_symmetric
#audit_axioms BookProof.ShiftedQuadratic.shiftedHOp_deficiencyTrivialAt
#audit_axioms BookProof.ShiftedQuadratic.shiftedHOp_essentiallySelfAdjoint
#audit_axioms BookProof.ShiftedQuadratic.shiftedCore_dense
#audit_axioms BookProof.ShiftedQuadratic.shiftedHOp_stone_flow
#audit_axioms BookProof.ShiftedQuadratic.shiftedHOp_not_bounded
#audit_axioms BookProof.ShiftedQuadratic.pgFunT_momTPoly_sq
#audit_axioms BookProof.ShiftedQuadratic.shiftedHPoly_apply_eq_differential
#audit_axioms BookProof.ShiftedQuadratic.shiftedHOp_coe_eq_pgLpT
#audit_axioms
  BookProof.ShiftedQuadratic.wave_indefiniteQuadratic_linear_essentiallySelfAdjoint

-- `ChapterShiftedQuadraticMatrixEsa`: the indefinite inhomogeneous quadratic Hamiltonian
-- **with cross terms**.  For every real symmetric *invertible* matrix `A` of arbitrary
-- signature and arbitrary real `b, b'`, `H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is symmetric and
-- essentially self-adjoint on the translated, modulated core with `a = −2A⁻¹b` and
-- `k = −A⁻¹b'/2`: completing the square in matrix form leaves `H_A` plus a constant, and
-- `H_A` is diagonal on the *rotated* Hermite polynomials, so the translated, modulated,
-- rotated Hermite functions are an orthonormal total family of eigenvectors.
#audit_axioms BookProof.ShiftedQuadraticMatrix.quadTermT_apply
#audit_axioms BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand
#audit_axioms BookProof.ShiftedQuadraticMatrix.foTPoly_apply_expand
#audit_axioms BookProof.ShiftedQuadraticMatrix.shiftedHMatPoly_eq_quadPolyMat
#audit_axioms BookProof.ShiftedQuadraticMatrix.orthonormal_hermiteTRLp
#audit_axioms BookProof.ShiftedQuadraticMatrix.span_hermiteTRLp
#audit_axioms BookProof.ShiftedQuadraticMatrix.hermiteTRLp_total
#audit_axioms BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp
#audit_axioms BookProof.ShiftedQuadraticMatrix.mulVec_matShiftVec
#audit_axioms BookProof.ShiftedQuadraticMatrix.mulVec_matBoostVec
#audit_axioms BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_symmetric
#audit_axioms BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_essentiallySelfAdjoint
#audit_axioms BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_not_bounded
#audit_axioms BookProof.ShiftedQuadraticMatrix.shiftedHMatCore_dense
#audit_axioms BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_stone_flow
#audit_axioms BookProof.ShiftedQuadraticMatrix.rotConj_det
#audit_axioms BookProof.ShiftedQuadraticMatrix.wave_rotated_linear_essentiallySelfAdjoint

-- `ChapterStoneEigenflow`: explicit dynamics.  A self-adjoint extension keeps the
-- eigenvectors of the core operator, and *any* Stone flow of a self-adjoint operator acts
-- on an eigenvector by the phase `e^{−iλt}`; consequently a symmetric, essentially
-- self-adjoint core operator with a family of eigenvectors generates a flow which is
-- diagonal on that family.
#audit_axioms BookProof.StoneEigenflow.isSelfAdjointExtension_eigenvector
#audit_axioms BookProof.StoneEigenflow.stoneFlow_apply_eigenvector
#audit_axioms BookProof.StoneEigenflow.stoneFlow_apply_core_eigenvector
#audit_axioms BookProof.StoneEigenflow.exists_diagonal_stone_flow

-- `ChapterShiftedQuadraticDegenerate`: the singular case.  The classical equilibrium
-- equation `A a = w` is solvable exactly when `w ⊥ ker A`, and under that condition the
-- inhomogeneous quadratic Hamiltonian of an *arbitrary* real symmetric `A` — invertible
-- or singular, of arbitrary signature — is symmetric and essentially self-adjoint on the
-- translated, modulated core, generates a complete unitary flow, and that flow acts on
-- the Hermite eigenbasis by an explicit phase.
#audit_axioms BookProof.ShiftedQuadraticDegenerate.equilibrium_orthogonal_to_kernel
#audit_axioms BookProof.ShiftedQuadraticDegenerate.exists_equilibrium
#audit_axioms BookProof.ShiftedQuadraticDegenerate.exists_equilibrium_iff
#audit_axioms BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_symmetric_of_equilibrium
#audit_axioms
  BookProof.ShiftedQuadraticDegenerate.shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium
#audit_axioms BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_esa_of_kernel_orthogonal
#audit_axioms BookProof.ShiftedQuadraticDegenerate.diagonal_degenerate_essentiallySelfAdjoint
#audit_axioms BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow
#audit_axioms BookProof.ShiftedQuadraticDegenerate.exists_shiftedH_diagonal_flow

-- `ChapterFourierMultiplierEsa`: the Plancherel argument as an instrument.  Any Fourier
-- multiplier with a real, smooth symbol is symmetric and essentially self-adjoint on the
-- Schwartz core of `L²(V)`; in particular the momentum family `∑ᵢ cᵢ(−i∂_{wᵢ})` and the
-- full constant-coefficient operator `∑ᵢ cᵢ∂_{wᵢ}² + ∑ᵢ aᵢ(−i∂_{wᵢ}) + κ` are.
#audit_axioms BookProof.FourierMultiplierEsa.symmetricOn_of_real_symbol
#audit_axioms BookProof.FourierMultiplierEsa.deficiencyTrivialAt_of_real_symbol
#audit_axioms BookProof.FourierMultiplierEsa.essentiallySelfAdjointOn_of_real_symbol
#audit_axioms BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply
#audit_axioms BookProof.FourierMultiplierEsa.firstOrderOp_symmetric
#audit_axioms BookProof.FourierMultiplierEsa.firstOrderOp_essentiallySelfAdjoint
#audit_axioms BookProof.FourierMultiplierEsa.momentumOp_essentiallySelfAdjoint
#audit_axioms BookProof.FourierMultiplierEsa.mixedOp_symmetric
#audit_axioms BookProof.FourierMultiplierEsa.mixedOp_essentiallySelfAdjoint

-- `ChapterMixedLinearEsa`: the mixed first-order operator `⟪x, b⟫ − i ∂_m`.  The position
-- operator is essentially self-adjoint by a compactly supported division argument, compactly
-- supported test functions detect the deficiency spaces of the momentum operator (a cut-off
-- plus dominated convergence argument), and the quadratic gauge `e^{iθ}`,
-- `θ(x) = −⟪x,b⟫⟪x,m⟫/‖m‖² + ⟪b,m⟫⟪x,m⟫²/(2‖m‖⁴)`, intertwines the two.
#audit_axioms BookProof.MixedLinearEsa.posOp_symmetric
#audit_axioms BookProof.MixedLinearEsa.posOp_essentiallySelfAdjoint
#audit_axioms BookProof.MixedLinearEsa.momentum_test_compactSupport_extend
#audit_axioms BookProof.MixedLinearEsa.momentumOp_eq_zero_of_compactSupport_test
#audit_axioms BookProof.MixedLinearEsa.mixedLinearOp_gauge
#audit_axioms BookProof.MixedLinearEsa.mixedLinearOp_symmetric
#audit_axioms BookProof.MixedLinearEsa.mixedLinearOp_essentiallySelfAdjoint
#audit_axioms BookProof.MixedLinearEsa.polyPotential_add_momentum_essentiallySelfAdjoint

-- `ChapterUnboundedSpectralModel`: the spectral theorem in multiplication form for an
-- *unbounded* self-adjoint operator.  The resolvent `R = (A − i)⁻¹` is a bounded normal
-- operator, injective, with range exactly the domain of `A`; the bounded multiplication
-- model of `ChapterSpectralDirectSum` therefore applies to `R`, the representing measure
-- is carried by the Cayley circle `|z|² = Im z` and gives no mass to `z = 0`, and `A` is
-- multiplication by the real function `Re z/|z|²`.
#audit_axioms BookProof.UnboundedSpectralModel.resOp_injective
#audit_axioms BookProof.UnboundedSpectralModel.exists_resOp_eq
#audit_axioms BookProof.UnboundedSpectralModel.adjoint_resCLM
#audit_axioms BookProof.UnboundedSpectralModel.isStarNormal_resOp
#audit_axioms BookProof.UnboundedSpectralModel.model_apply
#audit_axioms BookProof.UnboundedSpectralModel.model_ae_circle
#audit_axioms BookProof.UnboundedSpectralModel.model_ae_ne_zero
#audit_axioms BookProof.UnboundedSpectralModel.model_ae_real_multiplier
#audit_axioms BookProof.UnboundedSpectralModel.unbounded_multiplication_model_cyclic
#audit_axioms BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general
#audit_axioms BookProof.UnboundedSpectralModel.unbounded_multiplication_model_separable

-- `ChapterQuadratureEsa`: the quadrature `∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` on the Gauss–polynomial
-- (product Hermite) core.  A moment lemma with no `L²` hypothesis makes the deficiency
-- equation of the purely positional quadrature solvable on that core; the diagonal phase
-- unitary `ψ_α ↦ ζ^α ψ_α` of the product Hermite basis is the metaplectic rotation, and it
-- carries the positional quadrature `∑ᵢ|wᵢ|xᵢ` onto the general one, `wᵢ = bᵢ + ib'ᵢ/2`.
#audit_axioms BookProof.QuadratureEsa.ae_eq_zero_of_moments'
#audit_axioms BookProof.QuadratureEsa.foOp_pos_essentiallySelfAdjoint
#audit_axioms BookProof.QuadratureEsa.phaseU_hermiteMvLp
#audit_axioms BookProof.QuadratureEsa.foOp_hermiteCore
#audit_axioms BookProof.QuadratureEsa.phaseU_foOp_hermiteCore
#audit_axioms BookProof.QuadratureEsa.foOp_essentiallySelfAdjoint
#audit_axioms BookProof.QuadratureEsa.foOp_stone_flow

-- `ChapterHermiteCarlemanEsa`: the Carleman criterion on the multi-index lattice of the
-- product Hermite basis, and the inhomogeneous diagonal quadratic Hamiltonian with an
-- arbitrary first-order term on the plain Gauss–polynomial core.  The imaginary part of
-- the coefficient recursion, summed over a cube of multi-indices, telescopes to the flux
-- through the boundary faces (`flux_identity`), which is at most `√(N+1)` times the
-- `ℓ²`-mass of those faces (`flux_bound`); the faces are disjoint, so that mass is
-- summable, while `∑ 1/√(N+1)` diverges.
#audit_axioms BookProof.HermiteCarleman.flux_identity
#audit_axioms BookProof.HermiteCarleman.flux_bound
#audit_axioms BookProof.HermiteCarleman.ladder_eq_zero
#audit_axioms BookProof.HermiteCarleman.mixOp_hermiteCore
#audit_axioms BookProof.HermiteCarleman.mixOp_symmetric
#audit_axioms BookProof.HermiteCarleman.mixOp_deficiencyTrivialAt
#audit_axioms BookProof.HermiteCarleman.mixOp_essentiallySelfAdjoint
#audit_axioms BookProof.HermiteCarleman.mixOp_stone_flow
#audit_axioms BookProof.HermiteCarleman.wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint

-- `ChapterCarlemanTwoStep`: the same flux argument for a recursion whose hops move a
-- single excitation number by one **or two**, with amplitudes `O(N)`.  Faces of thickness
-- two are no longer disjoint, so Bessel's inequality is used with a multiplicity bound
-- (`sum_range_of_multiplicity`, `faceK_multiplicity`), and the divergence is
-- `∑ 1/(N+1) = ∞`.
#audit_axioms BookProof.CarlemanTwoStep.sum_cube_hop_im
#audit_axioms BookProof.CarlemanTwoStep.flux_identity2
#audit_axioms BookProof.CarlemanTwoStep.flux_boundG
#audit_axioms BookProof.CarlemanTwoStep.sum_range_of_multiplicity
#audit_axioms BookProof.CarlemanTwoStep.ladder2_eq_zero

-- `ChapterModeQuadraticEsa`: the general **mode-diagonal** real quadratic Hamiltonian
-- `∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`, for arbitrary real
-- coefficients, is essentially self-adjoint on the plain Gauss–polynomial core, and
-- generates a complete unitary flow.  In particular the generator of dilations does.
#audit_axioms BookProof.ModeQuadratic.lop_lop_hermiteMv
#audit_axioms BookProof.ModeQuadratic.mqQuadPoly_hermiteMv
#audit_axioms BookProof.ModeQuadratic.mqOp_hermiteCore
#audit_axioms BookProof.ModeQuadratic.mqOp_symmetric
#audit_axioms BookProof.ModeQuadratic.mqOp_deficiencyTrivialAt
#audit_axioms BookProof.ModeQuadratic.mqOp_essentiallySelfAdjoint
#audit_axioms BookProof.ModeQuadratic.mqOp_stone_flow
#audit_axioms BookProof.ModeQuadratic.dilation_essentiallySelfAdjoint
#audit_axioms BookProof.ModeQuadratic.dilation_stone_flow

-- `ChapterCarlemanSimplex`: the Carleman flux argument rerun on the **simplex** shells
-- `{α : |α| ≤ N}` of the multi-index lattice.  This grading by total degree is the one
-- adapted to a general quadratic ladder: the degree-preserving mode-exchange hops
-- `α ↦ α − eⱼ + eᵢ` carry no flux at all when their amplitude matrix is Hermitian
-- (`sum_mterm_im`), while the degree-changing pair hops `α ↦ α ± (eᵢ + eⱼ)` leak only
-- through a boundary shell of thickness two, of controlled multiplicity.
#audit_axioms BookProof.CarlemanSimplex.sum_simplex_hop_im
#audit_axioms BookProof.CarlemanSimplex.sum_mterm_im
#audit_axioms BookProof.CarlemanSimplex.flux_identityQ
#audit_axioms BookProof.CarlemanSimplex.flux_bound_on
#audit_axioms BookProof.CarlemanSimplex.sBd_multiplicity
#audit_axioms BookProof.CarlemanSimplex.ladderQ_eq_zero

-- `ChapterFullQuadraticEsa`: the **general** real quadratic-plus-linear Hamiltonian
-- `∑_{i,j} (Pᵢⱼπᵢπⱼ + Qᵢⱼxᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`, for arbitrary
-- real matrices `P, Q, S` and vectors `b, b'` — distinct modes coupled arbitrarily — is
-- essentially self-adjoint on the plain Gauss–polynomial core and generates a complete
-- unitary flow.  In particular the purely off-diagonal cross term does.
#audit_axioms BookProof.FullQuadratic.lop_lop_hermiteMv_gen
#audit_axioms BookProof.FullQuadratic.weyl_hermiteMv_gen
#audit_axioms BookProof.FullQuadratic.fqExch_hermitian
#audit_axioms BookProof.FullQuadratic.fqQuadPoly_hermiteMv
#audit_axioms BookProof.FullQuadratic.fqOp_hermiteCore
#audit_axioms BookProof.FullQuadratic.fqOp_symmetric
#audit_axioms BookProof.FullQuadratic.fqOp_deficiencyTrivialAt
#audit_axioms BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint
#audit_axioms BookProof.FullQuadratic.fqOp_stone_flow
#audit_axioms BookProof.FullQuadratic.crossTerm_essentiallySelfAdjoint
#audit_axioms BookProof.FullQuadratic.crossTerm_stone_flow
#audit_axioms BookProof.FullQuadratic.fqQuadPoly_rotMat
#audit_axioms BookProof.FullQuadratic.angularMomentum_essentiallySelfAdjoint
#audit_axioms BookProof.FullQuadratic.angularMomentum_stone_flow


-- `ChapterOperatorSeriesEsa`: the Faris–Lavine bounds — a relative bound `‖Hx‖ ≤ A‖Nx‖`
-- and a commutator-form bound `|⟪x, i[H, N]x⟫| ≤ B⟪x, Nx⟫` — are additive, and survive an
-- **infinite sum** of operators as soon as the two families of constants are summable.
#audit_axioms BookProof.OperatorSeries.commForm_eq_neg_two_im
#audit_axioms BookProof.OperatorSeries.seriesOp_symmetricOn
#audit_axioms BookProof.OperatorSeries.seriesOp_norm_le
#audit_axioms BookProof.OperatorSeries.seriesOp_commForm_le
#audit_axioms BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds
#audit_axioms BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series

-- `ChapterFockQuadraticEsa`: the general quadratic boson Hamiltonian with **infinitely
-- many modes**.  On the Fock space `ℓ²(ι →₀ ℕ)` of occupation-number configurations, with
-- an arbitrary mode set `ι`, an arbitrary non-negative and possibly unbounded dispersion
-- `ω`, and an arbitrary family of quadratic monomials `a^{†Pₖ}a^{Qₖ}` (`|Pₖ| + |Qₖ| ≤ 2`)
-- with couplings `gₖ` subject only to `∑ₖ ‖gₖ‖(ω(Pₖ) + ω(Qₖ) + 2) < ∞`, the Hamiltonian
-- is essentially self-adjoint on the finite-particle core.  Bogoliubov pair creation is
-- the special case `Pₖ = eₘₖ + eₙₖ`, `Qₖ = 0`.
#audit_axioms BookProof.FockQuadratic.amp_symm
#audit_axioms BookProof.FockQuadratic.hopOp_norm_le
#audit_axioms BookProof.FockQuadratic.hopOp_pairing
#audit_axioms BookProof.FockQuadratic.pairOp_symmetricOn
#audit_axioms BookProof.FockQuadratic.pairOp_norm_le
#audit_axioms BookProof.FockQuadratic.pairOp_commForm_le
#audit_axioms BookProof.FockQuadratic.freeOp_symmetricOn
#audit_axioms BookProof.FockQuadratic.freeOp_commForm
#audit_axioms BookProof.FockQuadratic.fockH_essentiallySelfAdjointOn_core
#audit_axioms BookProof.FockQuadratic.bogoliubov_essentiallySelfAdjointOn_core

-- `ChapterDirectSumEsa`: essential self-adjointness **glues along an orthogonal direct
-- sum**.  Testing the deficiency identity against single-fibre states shows that every
-- coordinate of a deficiency vector of `⊕ᵢ Hᵢ` is a deficiency vector of the fibre
-- operator `Hᵢ`, so fibrewise triviality gives triviality; the glued core is dense as soon
-- as every fibre core is.  Applied to the parcel sectors of the continuum Navier–Stokes
-- Fock space `⊕ₙ L²(ℝⁿ)`, this gives the second-quantized Hamiltonian
-- `ĥ = ∫ w(ξ)a†(ξ)a(ξ)dξ` on the Fock space itself, for an arbitrary measurable field `w`,
-- and — through the Stone bridge — its complete unitary flow `e^{−itĥ}`.
#audit_axioms BookProof.DirectSumEsa.dsOp_single
#audit_axioms BookProof.DirectSumEsa.dsOp_symmetricOn
#audit_axioms BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt
#audit_axioms BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn
#audit_axioms BookProof.DirectSumEsa.dsOpD_hasZeroDeficiencyOn
#audit_axioms BookProof.DirectSumEsa.dsOpD_isSymmetricDom
#audit_axioms BookProof.DirectSumEsa.dsCore_dense
#audit_axioms BookProof.DirectSumEsa.fockCore_dense
#audit_axioms BookProof.DirectSumEsa.fockH_isSymmetricDom
#audit_axioms BookProof.DirectSumEsa.fockH_hasZeroDeficiencyOn
#audit_axioms BookProof.DirectSumEsa.essentiallySelfAdjointOn_of_hasZeroDeficiencyOn
#audit_axioms BookProof.DirectSumEsa.dsOpD_stone_flow
#audit_axioms BookProof.DirectSumEsa.fockH_essentiallySelfAdjointOn
#audit_axioms BookProof.DirectSumEsa.fockH_stone_flow

-- `ChapterCarlemanGeneralHop`: the Carleman flux argument for a hop of the completely
-- general shape `α ↦ α + p − m`, the one a quadratic Hamiltonian coupling two *distinct*
-- modes produces (`α ↦ α ± (eᵢ + eⱼ)` and the non-monotone `α ↦ α ± (eᵢ − eⱼ)`).  The
-- imaginary part of the flux is carried by two boundary layers, the outgoing `A \ B` and the
-- incoming `B \ A`; both have bounded multiplicity, so Bessel's inequality controls them and
-- the divergence `∑ 1/(N+1) = ∞` again forces a square-summable solution to vanish.
#audit_axioms BookProof.CarlemanGeneralHop.hshift_hshift
#audit_axioms BookProof.CarlemanGeneralHop.sum_ltG
#audit_axioms BookProof.CarlemanGeneralHop.sum_hop_im
#audit_axioms BookProof.CarlemanGeneralHop.flux_bound_gen
#audit_axioms BookProof.CarlemanGeneralHop.flux_identityH
#audit_axioms BookProof.CarlemanGeneralHop.ladderH_eq_zero


end BookProof.ChapterRoadmapAudit
