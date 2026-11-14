/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import BookProof.RoadmapAudit.ChapterRoadmapAuditImports

/-!
# Roadmap headline certificate — audit ledger, slice 5 of 8

Slice 5 of the eight slices of the `#audit_axioms` ledger that used to sit at the end of
`BookProof/RoadmapAudit/ChapterRoadmapAudit.lean`.  The directives are the original ones,
verbatim and in the original order; the split exists only so that Lake elaborates eight modules in
parallel instead of one, which is where the aggregate build's 25 minutes went.

Each line prints the stock `'name' depends on axioms: [...]` line for one declaration; nothing
here asserts an axiom set.
-/

namespace BookProof.ChapterRoadmapAudit

open BookProof.AxiomAudit

-- `ChapterHermiteExpWall`: the exponential wall is *not* a relatively bounded perturbation
-- on the Gauss–polynomial core, neither of the kinetic term nor of the conformal-mode
-- oscillator (plan §10.6.1, target 2, restated and refuted).
#audit_axioms BookProof.HermiteExpWall.gaussMoment_tilt_ge
#audit_axioms BookProof.HermiteExpWall.gaussMoment_shift_eight
#audit_axioms BookProof.HermiteExpWall.quadForm_scalaron_ge
#audit_axioms BookProof.HermiteExpWall.l2_scalaron_ge
#audit_axioms BookProof.HermiteExpWall.neg_deriv2_psi
#audit_axioms BookProof.HermiteExpWall.osc_psi
#audit_axioms BookProof.HermiteExpWall.l2_kin_le
#audit_axioms BookProof.HermiteExpWall.l2_osc_le
#audit_axioms BookProof.HermiteExpWall.not_relatively_bounded_of_cubic
#audit_axioms BookProof.HermiteExpWall.scalaronV_not_kinetic_relativelyBounded
#audit_axioms BookProof.HermiteExpWall.scalaronV_not_oscillator_relativelyBounded

-- `ChapterHermiteQuadraticEsa`: the positive counterpart — the harmonic potential is
-- relatively bounded with constant `1` against `−Δ + ‖x‖²/4`, so every continuous potential
-- dominated by `a‖x‖²/4 + b` with `a < 1` keeps the Gauss–polynomial core a core, with the
-- conformal-mode instance for `0 < α < 1/2` (plan §10.6.1, target 4, unbounded half).
#audit_axioms BookProof.HermiteQuadraticEsa.gaussInt_anticommutator
#audit_axioms BookProof.HermiteQuadraticEsa.two_re_inner_kin_harm_ge
#audit_axioms BookProof.HermiteQuadraticEsa.norm_sq_harmPoly_mul_le
#audit_axioms BookProof.HermiteQuadraticEsa.norm_harmPoly_mul_le
#audit_axioms BookProof.HermiteQuadraticEsa.norm_potLp_le_of_le_harm
#audit_axioms BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_essentiallySelfAdjoint
#audit_axioms BookProof.HermiteQuadraticEsa.harmonic_add_subquadratic_stone_flow
#audit_axioms BookProof.HermiteQuadraticEsa.quadraticGrowth_essentiallySelfAdjoint
#audit_axioms BookProof.HermiteQuadraticEsa.harmonic_add_linearGrowth_essentiallySelfAdjoint
#audit_axioms BookProof.HermiteQuadraticEsa.scaledHarmonic_essentiallySelfAdjoint
#audit_axioms BookProof.HermiteQuadraticEsa.confV_essentiallySelfAdjoint
#audit_axioms BookProof.HermiteQuadraticEsa.confV_stone_flow
#audit_axioms BookProof.HermiteQuadraticEsa.expBounded_of_growth_bound
#audit_axioms BookProof.HermiteQuadraticEsa.abs_sectorQuadW_sub_harmW_le
#audit_axioms BookProof.HermiteQuadraticEsa.sectorQuad_essentiallySelfAdjoint
#audit_axioms BookProof.HermiteQuadraticEsa.sectorQuad_stone_flow
#audit_axioms BookProof.HermiteQuadraticEsa.tendsto_starobinskyV_div_sq
#audit_axioms BookProof.HermiteQuadraticEsa.sectorHarmonicApprox_essentiallySelfAdjoint

-- `ChapterFriedrichsCanonical`: the Friedrichs extension as a named operator, and its
-- canonicity — it dominates every symmetric extension whose domain lies in the form
-- domain, hence is the unique self-adjoint extension with that property; with the QG
-- scalaron instance (plan §10.6.1 / §11.4).
#audit_axioms BookProof.FriedrichsCanonical.dom_le_formDomain
#audit_axioms BookProof.FriedrichsCanonical.friedrichsDomain_le_formDomain
#audit_axioms BookProof.FriedrichsCanonical.friedrichsOp_resolvent
#audit_axioms BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension
#audit_axioms BookProof.FriedrichsCanonical.eq_zero_of_inner_coe_eq_zero
#audit_axioms BookProof.FriedrichsCanonical.friedrichs_canonical
#audit_axioms BookProof.FriedrichsCanonical.friedrichs_unique_selfAdjoint
#audit_axioms BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical
#audit_axioms BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_unique
#audit_axioms BookProof.FriedrichsCanonical.isSemibounded_of_isPositive_shift
#audit_axioms BookProof.FriedrichsCanonical.isPositive_shift_of_isSemibounded
open BookProof.FriedrichsCanonical in
#audit_axioms semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension
#audit_axioms BookProof.FriedrichsCanonical.semibounded_friedrichs_unique
#audit_axioms BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical
#audit_axioms BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique
#audit_axioms BookProof.FriedrichsCanonical.unbounded_friedrichs_canonical_example

-- `ChapterFermionFock`: the fermionic (CAR) half of the graded second quantization —
-- Jordan-Wigner signs, the four canonical anticommutation relations, the adjoint pairing,
-- the second quantization dGamma^a with its Friedrichs extension and Hashimoto/SIRK
-- selection, the fermion-number parity, and the realization of the abstract BRST ghost
-- relations (plan §10.6.2 item 3).
#audit_axioms BookProof.FermionFock.car_annF_creF_self
#audit_axioms BookProof.FermionFock.car_creF_creF
#audit_axioms BookProof.FermionFock.creF_creF_self
#audit_axioms BookProof.FermionFock.car_annF_annF
#audit_axioms BookProof.FermionFock.car_annF_creF_of_ne
#audit_axioms BookProof.FermionFock.inner_creF_left
#audit_axioms BookProof.FermionFock.dGammaF_one_particle
#audit_axioms BookProof.FermionFock.dGammaOpF_symmetricOn
#audit_axioms BookProof.FermionFock.dGammaOpF_quadForm_nonneg
#audit_axioms BookProof.FermionFock.dGammaF_friedrichs_extension
#audit_axioms BookProof.FermionFock.secondQuantizationF_friedrichs
#audit_axioms BookProof.FermionFock.dGammaF_hashimoto_selects
#audit_axioms BookProof.FermionFock.secondQuantizationF_hashimoto_selects
#audit_axioms BookProof.FermionFock.parityF_involutive
#audit_axioms BookProof.FermionFock.parityF_creF
#audit_axioms BookProof.FermionFock.parityF_annF
#audit_axioms BookProof.FermionFock.ghostCAR_creF_annF
#audit_axioms BookProof.FermionFock.brst_charge_nilpotent_fermiFock

-- `ChapterGradedFock`: the graded Fock space Gamma^s (x) Gamma^a, the lifts of the
-- operators of the two tensor factors, the single unified graded canonical relation
-- (the book's Koszul-sign formula) and the Z2 grading (plan §10.6.2 item 3).
#audit_axioms BookProof.GradedFock.liftFst_liftSnd_comm
#audit_axioms BookProof.GradedFock.super_canonical
#audit_axioms BookProof.GradedFock.super_canonical_cre
#audit_axioms BookProof.GradedFock.super_canonical_ann
#audit_axioms BookProof.GradedFock.gradeOp_involutive
#audit_axioms BookProof.GradedFock.gradeOp_bcre
#audit_axioms BookProof.GradedFock.gradeOp_fcre
#audit_axioms BookProof.GradedFock.even_add_odd
#audit_axioms BookProof.GradedFock.gradeOp_evenPart
#audit_axioms BookProof.GradedFock.gradeOp_oddPart

-- `ChapterFockSecondQuantization`: the off-diagonal bosonic canonical commutation
-- relations added for the graded superalgebra.
#audit_axioms BookProof.FockSecondQuantization.ccr_annA_creA_of_ne
#audit_axioms BookProof.FockSecondQuantization.ccr_annA_annA
#audit_axioms BookProof.FockSecondQuantization.ccr_creA_creA

-- `ChapterGradedFriedrichs`: the analytic half of the graded second quantization —
-- the generic transport of the finitely supported model into l^2, the slice calculus
-- of the tensor product, the inheritance of symmetry and positivity by the one-factor
-- lifts, and the Friedrichs extension of dGamma^s(A) (x) 1 + 1 (x) dGamma^a(B).
#audit_axioms BookProof.GradedFriedrichs.ainner_eq_sum
#audit_axioms BookProof.GradedFriedrichs.algEquivL2
#audit_axioms BookProof.GradedFriedrichs.opOfAlg_symmetricOn
#audit_axioms BookProof.GradedFriedrichs.opOfAlg_quadForm_nonneg
#audit_axioms BookProof.GradedFriedrichs.algOp_friedrichs_extension
#audit_axioms BookProof.GradedFriedrichs.sliceFst_apply
#audit_axioms BookProof.GradedFriedrichs.sliceSnd_apply
#audit_axioms BookProof.GradedFriedrichs.sliceFst_liftFst
#audit_axioms BookProof.GradedFriedrichs.sliceSnd_liftSnd
#audit_axioms BookProof.GradedFriedrichs.ainner_eq_sum_sliceFst
#audit_axioms BookProof.GradedFriedrichs.ainner_eq_sum_sliceSnd
#audit_axioms BookProof.GradedFriedrichs.isSymAlg_liftFst
#audit_axioms BookProof.GradedFriedrichs.isPosAlg_liftFst
#audit_axioms BookProof.GradedFriedrichs.isSymAlg_liftSnd
#audit_axioms BookProof.GradedFriedrichs.isPosAlg_liftSnd
#audit_axioms BookProof.GradedFriedrichs.gradedHamiltonian_symmetricOn
#audit_axioms BookProof.GradedFriedrichs.gradedHamiltonian_quadForm_nonneg
#audit_axioms BookProof.GradedFriedrichs.gradedHamiltonian_friedrichs_extension
#audit_axioms BookProof.GradedFriedrichs.gradedSecondQuantization_friedrichs
#audit_axioms BookProof.GradedFriedrichs.gradedNumber_one_particle
#audit_axioms BookProof.GradedFriedrichs.gradedNumber_friedrichs_extension

-- `ChapterGradedHashimoto`: the graded Hamiltonian is an even operator (it commutes
-- with the Z2 grading (-1)^{N_f}, so it preserves the even and odd subspaces), and the
-- Hashimoto/SIRK shift-invert limit selects its Friedrichs extension, with the concrete
-- instance of the total number operator N_b (x) 1 + 1 (x) N_f.
#audit_axioms BookProof.GradedHashimoto.gradedHamiltonianAlg_otimes
#audit_axioms BookProof.GradedHashimoto.parityF_creVecF
#audit_axioms BookProof.GradedHashimoto.parityF_dGammaF
#audit_axioms BookProof.GradedHashimoto.gradeOp_gradedHamiltonianAlg
#audit_axioms BookProof.GradedHashimoto.gradedHamiltonianAlg_evenPart
#audit_axioms BookProof.GradedHashimoto.gradedHamiltonianAlg_oddPart
#audit_axioms BookProof.GradedHashimoto.gradedHamiltonianB_symmetricOn
#audit_axioms BookProof.GradedHashimoto.gradedHamiltonianB_quadForm_nonneg
#audit_axioms BookProof.GradedHashimoto.graded_hashimoto_selects
#audit_axioms BookProof.GradedHashimoto.gradedSecondQuantization_hashimoto_selects
#audit_axioms BookProof.GradedHashimoto.gradedNumber_hashimoto_selects
#audit_axioms BookProof.GradedHashimoto.graded_stone_flow
#audit_axioms BookProof.GradedHashimoto.gradedNumber_stone_flow

-- `ChapterKrylovShiftSpan`: the multi-shift (rational) Krylov spaces used by the
-- SIRK/Hashimoto solver coincide with the plain Krylov space: the shifted forward
-- sequence spans it for any shift sequence, and the resolvent (rational) Krylov space
-- is its image under the product of all the resolvents.
#audit_axioms BookProof.KrylovShiftSpan.forwardProd_mem_krylovSpan
#audit_axioms BookProof.KrylovShiftSpan.pow_mem_forwardSpan
#audit_axioms BookProof.KrylovShiftSpan.forwardSpan_eq_krylovSpan
#audit_axioms BookProof.KrylovShiftSpan.forwardSpan_eq_forwardSpan
#audit_axioms BookProof.KrylovShiftSpan.commute_resolvent_shiftOp
#audit_axioms BookProof.KrylovShiftSpan.commute_resolvent
#audit_axioms BookProof.KrylovShiftSpan.forwardProd_eq_tailProd_mul
#audit_axioms BookProof.KrylovShiftSpan.resProd_mul_tailProd
#audit_axioms BookProof.KrylovShiftSpan.tailProd_eq_forwardProd_rev
#audit_axioms BookProof.KrylovShiftSpan.tailSpan_eq_krylovSpan
#audit_axioms BookProof.KrylovShiftSpan.resolventSpan_eq_map_krylovSpan
#audit_axioms BookProof.KrylovShiftSpan.forwardProd_mul_resProd
#audit_axioms BookProof.KrylovShiftSpan.krylovSpan_eq_map_resolventSpan
#audit_axioms BookProof.KrylovShiftSpan.resolventSpan_eq_span_resVec
#audit_axioms BookProof.KrylovShiftSpan.resProd_of_perm
#audit_axioms BookProof.KrylovShiftSpan.resolventSpan_of_perm

-- `ChapterSirkGramWhitening`: the Gram whitening the solver performs really is an
-- orthonormalization of the retained Krylov subspace — the synthesis map, the Gram
-- operator/matrix, `T∗GT = 1` implies `V∗V = 1`, and such a `T` exists.
#audit_axioms BookProof.ChapterSirkGramWhitening.range_synthesis
#audit_axioms BookProof.ChapterSirkGramWhitening.synthesis_adjoint_eq
#audit_axioms BookProof.ChapterSirkGramWhitening.synthesis_injective_of_linearIndependent
#audit_axioms BookProof.ChapterSirkGramWhitening.gramOp_apply
#audit_axioms BookProof.ChapterSirkGramWhitening.inner_gramOp
#audit_axioms BookProof.ChapterSirkGramWhitening.gramOp_isSelfAdjoint
#audit_axioms BookProof.ChapterSirkGramWhitening.gramOp_nonneg
#audit_axioms BookProof.ChapterSirkGramWhitening.whitened_adjoint_comp_self
#audit_axioms BookProof.ChapterSirkGramWhitening.norm_whitened_apply
#audit_axioms BookProof.ChapterSirkGramWhitening.range_whitened
#audit_axioms BookProof.ChapterSirkGramWhitening.onbEmbedding_isometry
#audit_axioms BookProof.ChapterSirkGramWhitening.range_onbEmbedding
#audit_axioms BookProof.ChapterSirkGramWhitening.exists_isometry_range_eq_span
#audit_axioms BookProof.ChapterSirkGramWhitening.exists_isometry_fin_range_eq_span
#audit_axioms BookProof.ChapterSirkGramWhitening.exists_isWhitening
#audit_axioms BookProof.ChapterSirkGramWhitening.exists_whitened_isometry_onto_span
#audit_axioms BookProof.ChapterSirkGramWhitening.sirkApprox_gram_whitening_eq
#audit_axioms BookProof.ChapterSirkGramWhitening.compress_gram_whitening_conj
#audit_axioms BookProof.ChapterSirkGramWhitening.gramMatrix_conjTranspose
#audit_axioms BookProof.ChapterSirkGramWhitening.gramOp_eq_toEuclideanCLM
#audit_axioms BookProof.ChapterSirkGramWhitening.isWhitening_of_matrix
#audit_axioms BookProof.ChapterSirkGramWhitening.isWhitening_one_of_orthonormal
#audit_axioms BookProof.ChapterSirkGramWhitening.sum_norm_coord_le
#audit_axioms BookProof.ChapterSirkGramWhitening.norm_defect_synthesis_le
#audit_axioms BookProof.ChapterSirkGramWhitening.sirk_end_to_end_truncated_gram

-- `ChapterSirkGramCutoff`: the numerical cutoff on the Gram eigenvalues bounds the
-- truncation defect (`δ ≤ √tol`), and the inverse-square-root embedding the solver
-- builds from the retained eigenpairs is an isometric embedding of the retained subspace.
#audit_axioms BookProof.ChapterSirkGramCutoff.norm_sq_sum_orthogonal
#audit_axioms BookProof.ChapterSirkGramCutoff.exists_gramEigen
#audit_axioms BookProof.ChapterSirkGramCutoff.inner_synthesis_gramEigen
#audit_axioms BookProof.ChapterSirkGramCutoff.norm_sq_synthesis_gramEigen
#audit_axioms BookProof.ChapterSirkGramCutoff.gramEigen_nonneg
#audit_axioms BookProof.ChapterSirkGramCutoff.norm_sub_proj_le_of_mem_range
#audit_axioms BookProof.ChapterSirkGramCutoff.synthesis_eq_sum_gramEigen
#audit_axioms BookProof.ChapterSirkGramCutoff.dist_synthesis_retained_le
#audit_axioms BookProof.ChapterSirkGramCutoff.synthesis_single
#audit_axioms BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff
#audit_axioms BookProof.ChapterSirkGramCutoff.sirk_end_to_end_truncated_cutoff
#audit_axioms BookProof.ChapterSirkGramCutoff.retainedVec_orthonormal
#audit_axioms BookProof.ChapterSirkGramCutoff.synthesis_isometry_of_orthonormal
#audit_axioms BookProof.ChapterSirkGramCutoff.retainedEmbedding_isometry
#audit_axioms BookProof.ChapterSirkGramCutoff.range_retainedEmbedding
#audit_axioms BookProof.ChapterSirkGramCutoff.mem_range_retainedEmbedding
#audit_axioms BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff_retained

-- Wave (2026-08-24, gate re-run): the four modules that had never been in a build target.
-- `ChapterNavierStokesCarleman`: Carleman's criterion for a Jacobi operator on `ℓ²(ℕ)` and
-- the half-line realization of the full Navier–Stokes Hamiltonian.
#audit_axioms BookProof.NavierStokesFlow.Carleman.tridiagOp_isSymmetricDom
#audit_axioms BookProof.NavierStokesFlow.Carleman.tridiag_wronskian
#audit_axioms BookProof.NavierStokesFlow.Carleman.wron_eq_sum
#audit_axioms BookProof.NavierStokesFlow.Carleman.sum_normSq_le
#audit_axioms BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman
#audit_axioms BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp
#audit_axioms BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian
#audit_axioms BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn
#audit_axioms BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn
#audit_axioms BookProof.NavierStokesFlow.Carleman.linearFull_not_bounded

-- The three attention-layer modules of the same wave.
#audit_axioms BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_monotone_of_max
#audit_axioms BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_antitone_of_min
#audit_axioms BookProof.ChapterAttentionResponse.deriv_headOutput
#audit_axioms BookProof.ChapterAttentionResponse.norm_headOutput_sub_le_temperature
#audit_axioms BookProof.ChapterAttentionCapacity.exists_beta_forall_retrieval

-- The Cayley-transform wave (plan §9 backlog item 3): the unbounded self-adjoint layer is
-- encoded by a unitary, and back.
#audit_axioms BookProof.ChapterCayleyTransform.norm_shift_one_eq_norm_shift_neg_one
#audit_axioms BookProof.ChapterCayleyTransform.cayleyMap_shift
#audit_axioms BookProof.ChapterCayleyTransform.norm_cayleyMap
#audit_axioms BookProof.ChapterCayleyTransform.cayleyMap_surjective
#audit_axioms BookProof.ChapterCayleyTransform.cayley_shift
#audit_axioms BookProof.ChapterCayleyTransform.sub_cayley_shift
#audit_axioms BookProof.ChapterCayleyTransform.add_cayley_shift
#audit_axioms BookProof.ChapterCayleyTransform.one_sub_cayley_injective
#audit_axioms BookProof.ChapterCayleyTransform.cayley_apply_ne_self
#audit_axioms BookProof.ChapterCayleyTransform.range_one_sub_cayley
#audit_axioms BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley
#audit_axioms BookProof.ChapterCayleyTransform.op_eq_cayley
#audit_axioms BookProof.ChapterCayleyTransform.coe_eq_cayley
#audit_axioms BookProof.ChapterCayleyInverse.isSelfAdjointOn_of_surjective
#audit_axioms BookProof.ChapterCayleyInverse.invCayleyOp_symmetric
#audit_axioms BookProof.ChapterCayleyInverse.invCayleyOp_add_i
#audit_axioms BookProof.ChapterCayleyInverse.invCayleyOp_sub_i
#audit_axioms BookProof.ChapterCayleyInverse.invCayleyOp_isSelfAdjointOn
#audit_axioms BookProof.ChapterCayleyInverse.cayley_ofUnitary
#audit_axioms BookProof.ChapterCayleyInverse.invCayleyDomain_cayley
#audit_axioms BookProof.ChapterCayleyInverse.invCayleyOp_cayley

#audit_axioms BookProof.ChapterCayleySpectralModel.res_neg_one_eq_cayley
#audit_axioms BookProof.ChapterCayleySpectralModel.res_one_eq_cayley
#audit_axioms BookProof.ChapterCayleySpectralModel.isStarNormal_cayleyCLM
#audit_axioms BookProof.ChapterCayleySpectralModel.cfcHom_resSymbol
#audit_axioms BookProof.ChapterCayleySpectralModel.cfcHom_opSymbol
#audit_axioms BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol
#audit_axioms BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol
#audit_axioms BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model

-- The BRST truncation-leakage wave (plan §12.2 Gap 5): the leakage of the truncated flow
-- out of the physical subspace, quantified by the discarded block of the Hamiltonian.
#audit_axioms BookProof.BrstLeakage.flow_mem_unitary
#audit_axioms BookProof.BrstLeakage.norm_unitary_apply
#audit_axioms BookProof.BrstLeakage.norm_flow_apply
#audit_axioms BookProof.BrstLeakage.omega_flow_apply
#audit_axioms BookProof.BrstLeakage.norm_omega_flow_eq
#audit_axioms BookProof.BrstLeakage.flow_mem_ker_omega
#audit_axioms BookProof.BrstLeakage.hasDerivAt_duhamel
#audit_axioms BookProof.BrstLeakage.norm_flow_sub_flow_apply_le
#audit_axioms BookProof.BrstLeakage.norm_flow_sub_flow_apply_le'
#audit_axioms BookProof.BrstLeakage.flow_neg_gen
#audit_axioms BookProof.BrstLeakage.norm_flow_sub_flow_apply_le_abs
#audit_axioms BookProof.BrstLeakage.norm_flow_sub_flow_le
#audit_axioms BookProof.BrstLeakage.leakage_le
#audit_axioms BookProof.BrstLeakage.leakage_le_of_physical
#audit_axioms BookProof.BrstLeakage.leakage_le_abs
#audit_axioms BookProof.BrstLeakage.truncGen_isSelfAdjoint
#audit_axioms BookProof.BrstLeakage.flow_truncGen_mem
#audit_axioms BookProof.BrstLeakage.truncation_leakage_le
#audit_axioms BookProof.BrstLeakage.truncation_leakage_le_abs
#audit_axioms BookProof.BrstLeakage.truncation_leakage_le_of_physical
#audit_axioms BookProof.BrstLeakage.norm_leakageIter
#audit_axioms BookProof.BrstLeakage.leakage_iterate_le
#audit_axioms BookProof.BrstLeakage.norm_flow_sub_flow_le_cycle
#audit_axioms BookProof.BrstLeakage.brst_leakage_bound_of_generator

-- The unbounded-hop Carleman wave (plan §10.6.1 target 3): the flux criterion for
-- infinite-range Hermitian kernels on `ℓ²(ℕ)`, and a genuinely infinite-range instance.
#audit_axioms BookProof.CarlemanUnboundedHop.flux_identity
#audit_axioms BookProof.CarlemanUnboundedHop.eq_zero_of_flux_small
#audit_axioms BookProof.CarlemanUnboundedHop.Theta_antitone
#audit_axioms BookProof.CarlemanUnboundedHop.two_norm_flux_le
#audit_axioms BookProof.CarlemanUnboundedHop.summable_cutMass
#audit_axioms BookProof.CarlemanUnboundedHop.exists_mul_lt_of_not_summable_inv
#audit_axioms BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman
#audit_axioms BookProof.CarlemanUnboundedHop.memℓp_kernelFun
#audit_axioms BookProof.CarlemanUnboundedHop.kernelOp_symmetric
#audit_axioms BookProof.CarlemanUnboundedHop.ladderRec_of_deficiency
#audit_axioms BookProof.CarlemanUnboundedHop.kernelOp_deficiencyTrivialAt
#audit_axioms BookProof.CarlemanUnboundedHop.kernelOp_essentiallySelfAdjoint
#audit_axioms BookProof.CarlemanUnboundedHop.kernelOp_stone_flow
#audit_axioms BookProof.CarlemanUnboundedHop.geoHop_isL2Kernel
#audit_axioms BookProof.CarlemanUnboundedHop.geoHop_essentiallySelfAdjoint
#audit_axioms BookProof.CarlemanUnboundedHop.geoHop_stone_flow

-- The unbounded-generator BRST leakage wave (plan §12.2 Gap 5, unbounded half): the Duhamel
-- estimate against the Stone group of an unbounded self-adjoint operator, and the leakage of
-- the finite-dimensional compression `P T P`.
#audit_axioms BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply
#audit_axioms BookProof.BrstUnboundedLeakage.hasDerivAt_flow
#audit_axioms BookProof.BrstUnboundedLeakage.flow_apply_flow
#audit_axioms BookProof.BrstUnboundedLeakage.hasDerivAt_duhamel_stone
#audit_axioms BookProof.BrstUnboundedLeakage.norm_flow_sub_stoneU_le
#audit_axioms BookProof.BrstUnboundedLeakage.norm_omega_stoneU_eq
#audit_axioms BookProof.BrstUnboundedLeakage.leakage_le
#audit_axioms BookProof.BrstUnboundedLeakage.leakage_le_of_physical
#audit_axioms BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint
#audit_axioms BookProof.BrstUnboundedLeakage.flow_mem_of_proj
#audit_axioms BookProof.BrstUnboundedLeakage.flow_truncGen_mem
#audit_axioms BookProof.BrstUnboundedLeakage.defect_eq_truncDefect
#audit_axioms BookProof.BrstUnboundedLeakage.norm_flow_truncGen_sub_stoneU_le
#audit_axioms BookProof.BrstUnboundedLeakage.truncation_leakage_le
#audit_axioms BookProof.BrstUnboundedLeakage.truncation_leakage_le_of_physical
#audit_axioms BookProof.BrstUnboundedLeakage.restartGen_isSelfAdjoint
#audit_axioms BookProof.BrstUnboundedLeakage.norm_restartIter
#audit_axioms BookProof.BrstUnboundedLeakage.restart_leakage_le
-- The BRST-reduced transfer wave (plan §10.6.2 item 4): the physical subspace and the exact
-- states are invariant under anything commuting with the BRST charge, so the unitary group
-- descends to BRST cohomology as a norm-preserving one-parameter group of automorphisms.
#audit_axioms BookProof.BrstReducedTransfer.exactStates_le_physicalStates
#audit_axioms BookProof.BrstReducedTransfer.physicalStates_invariant
#audit_axioms BookProof.BrstReducedTransfer.exactStates_invariant
#audit_axioms BookProof.BrstReducedTransfer.transfer_zero
#audit_axioms BookProof.BrstReducedTransfer.transfer_comp
#audit_axioms BookProof.BrstReducedTransfer.transfer_bijective
#audit_axioms BookProof.BrstReducedTransfer.infDist_exactStates_eq_of_comm_explicit
#audit_axioms BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_of_comm_explicit
#audit_axioms BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_of_comm_explicit
#audit_axioms BookProof.BrstReducedTransfer.stoneTransfer_comp
#audit_axioms BookProof.BrstReducedTransfer.stoneTransfer_bijective
#audit_axioms BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_of_comm_explicit


end BookProof.ChapterRoadmapAudit
