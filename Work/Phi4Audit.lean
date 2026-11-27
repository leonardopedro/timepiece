/-
Axiom audit for the real scalar `λφ⁴` formalization (`BookProof.Phi4.*`).

Each module below contributes its public theorems.  The chain claims: the Mehler-core
one-particle Hamiltonian is essentially self-adjoint with a Stone flow; the continuous
momentum-space rank-one bounds and the two-sided return interval at `t = 1/100` hold with
kernel-checked rational constants; the unit inner fibre has a positive lower bound on its closure;
the symmetric outer Fock Hamiltonian has a vacuum ground state; and second quantization obeys the shift law `dΓ(h + c·1) = dΓ(h) + c·N_out`
together with the one-particle sector identification.  Every declaration must rest on
`propext`, `Classical.choice`, `Quot.sound` only.

Run with the project toolchain: `lake build Work.Phi4Audit` (or
`lake env lean Work/Phi4Audit.lean`).
-/

import BookProof.Phi4.ChapterScalarMehler
import BookProof.Phi4.ChapterScalarMomentum
import BookProof.Phi4.ChapterScalarMomentumGap
import BookProof.Phi4.ChapterScalarFourierIntegral
import BookProof.Phi4.ChapterScalarMomRankTwo
import BookProof.Phi4.ChapterScalarMomOrbit
import BookProof.Phi4.ChapterScalarPacketForm
import BookProof.Phi4.ChapterScalarOuter
import BookProof.Phi4.ChapterScalarEnergy
import BookProof.Phi4.ChapterScalarWindows
import BookProof.Phi4.ChapterScalarSectorOps
import BookProof.RoadmapAudit.AxiomAudit

/-! ## `ChapterScalarMehler` -/

#audit_axioms BookProof.Phi4.real_wall
#audit_axioms BookProof.Phi4.site_wall_energy
#audit_axioms BookProof.Phi4.Model.innerHam_pgLp
#audit_axioms BookProof.Phi4.Model.symmetric
#audit_axioms BookProof.Phi4.Model.nonneg
#audit_axioms BookProof.Phi4.Model.inner_esa
#audit_axioms BookProof.Phi4.Model.positive_extension
#audit_axioms BookProof.Phi4.Model.closure_nonneg
#audit_axioms BookProof.Phi4.Model.inner_flow
#audit_axioms BookProof.Phi4.Model.mehler_sirk
#audit_axioms BookProof.Phi4.Model.outer_esa
#audit_axioms BookProof.Phi4.coordinate_ladders
#audit_axioms BookProof.Phi4.momentum_ladders
#audit_axioms BookProof.Phi4.coordinate_momentum_commutator
#audit_axioms BookProof.Phi4.unitCell_vacuum_column
#audit_axioms BookProof.Phi4.vacuum_residual_squared
#audit_axioms BookProof.Phi4.vacuum_window_generator
#audit_axioms BookProof.Phi4.two_site_vertex

/-! ## `ChapterScalarMomentum` -/

#audit_axioms BookProof.Phi4.unitMomCont_forms
#audit_axioms BookProof.Phi4.unitMomCont_vacuum_column
#audit_axioms BookProof.Phi4.unitMomCont_defect_norm_sq
#audit_axioms BookProof.Phi4.unitMomCont_rankOne_error
#audit_axioms BookProof.Phi4.unitMomCont_return_probability

/-! ## `ChapterScalarMomentumGap` -/

#audit_axioms BookProof.Phi4.coreP_symmetric
#audit_axioms BookProof.Phi4.coreX_symmetric
#audit_axioms BookProof.Phi4.momOp_mulOp_comm
#audit_axioms BookProof.Phi4.coreP_coreX_comm
#audit_axioms BookProof.Phi4.inner_coreP_coreX
#audit_axioms BookProof.Phi4.harmonic_lower_bound
#audit_axioms BookProof.Phi4.contGap_pos
#audit_axioms BookProof.Phi4.fieldReflMatrix_orth
#audit_axioms BookProof.Phi4.spatialReflMatrix_orth
#audit_axioms BookProof.Phi4.coreRot_pgLp
#audit_axioms BookProof.Phi4.coreRot_inner
#audit_axioms BookProof.Phi4.fieldParity_inner
#audit_axioms BookProof.Phi4.spatialParity_inner
#audit_axioms BookProof.Phi4.unit_wall_completion
#audit_axioms BookProof.Phi4.unitMomCont_inner_gap
#audit_axioms BookProof.Phi4.unitMomCont_closure_floor
#audit_axioms BookProof.Phi4.shifted_well_comparison_false

/-! ## `ChapterScalarFourierIntegral` -/

#audit_axioms BookProof.Phi4.fourier_grad_sq_identity
#audit_axioms BookProof.Phi4.psiField_eq_fourier_mul
#audit_axioms BookProof.Phi4.fourier_phi4_composite_integral
#audit_axioms BookProof.Phi4.localizedWall_fourier
#audit_axioms BookProof.Phi4.localizedWall_energy

/-! ## `ChapterScalarMomRankTwo` -/

#audit_axioms BookProof.Phi4.MomRankTwo.gram_hermitian
#audit_axioms BookProof.Phi4.MomRankTwo.window_hermitian
#audit_axioms BookProof.Phi4.MomRankTwo.gram_inverse
#audit_axioms BookProof.Phi4.MomRankTwo.physical_dual
#audit_axioms BookProof.Phi4.MomRankTwo.dual_basis
#audit_axioms BookProof.Phi4.MomRankTwo.res5_inverse
#audit_axioms BookProof.Phi4.MomRankTwo.compressed_inverse
#audit_axioms BookProof.Phi4.MomRankTwo.hashimoto_generator
#audit_axioms BookProof.Phi4.MomRankTwo.dissipation
#audit_axioms BookProof.Phi4.MomRankTwo.differs_from_projected_h
#audit_axioms BookProof.Phi4.MomRankTwo.full_defect_gram
#audit_axioms BookProof.Phi4.MomRankTwo.full_defect_hs_squared
#audit_axioms BookProof.Phi4.MomRankTwo.seed_variance
#audit_axioms BookProof.Phi4.MomRankTwo.cont_fullColumns_action
#audit_axioms BookProof.Phi4.MomRankTwo.contMode_inner
#audit_axioms BookProof.Phi4.MomRankTwo.contMode_inner_normalized
#audit_axioms BookProof.Phi4.MomRankTwo.synthesis_inner

/-! ## `ChapterScalarMomOrbit` -/

#audit_axioms BookProof.Phi4.MomRankTwo.toComplex_star
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_mul
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_one
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_conjTranspose
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_trace
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_hermitian
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_add
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_neg
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_smul
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_nsmul
#audit_axioms BookProof.Phi4.MomRankTwo.dot_mulVec_conjTranspose
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_mulVec
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_smul
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_neg
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_nsmul
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_diagonal_nonneg
#audit_axioms BookProof.Phi4.MomRankTwo.dot_conj_hermitian
#audit_axioms BookProof.Phi4.MomRankTwo.dot_add
#audit_axioms BookProof.Phi4.MomRankTwo.dot_hasDerivAt
#audit_axioms BookProof.Phi4.MomRankTwo.HasDerivAt.mulVec
#audit_axioms BookProof.Phi4.MomRankTwo.HasDerivAt.const_mulVec
#audit_axioms BookProof.Phi4.MomRankTwo.hasDerivAt_normSqC
#audit_axioms BookProof.Phi4.MomRankTwo.two_re_dot_eq_normSqC
#audit_axioms BookProof.Phi4.MomRankTwo.W2C_hermitian
#audit_axioms BookProof.Phi4.MomRankTwo.c_zero
#audit_axioms BookProof.Phi4.MomRankTwo.expGC_mul
#audit_axioms BookProof.Phi4.MomRankTwo.c_deriv_eq
#audit_axioms BookProof.Phi4.MomRankTwo.hasDerivAt_c
#audit_axioms BookProof.Phi4.MomRankTwo.hasDerivAt_c1
#audit_axioms BookProof.Phi4.MomRankTwo.hasDerivAt_c2
#audit_axioms BookProof.Phi4.MomRankTwo.dissipation_C
#audit_axioms BookProof.Phi4.MomRankTwo.dissipation_form
#audit_axioms BookProof.Phi4.MomRankTwo.metricC_diagonal
#audit_axioms BookProof.Phi4.MomRankTwo.leak_form_nonneg
#audit_axioms BookProof.Phi4.MomRankTwo.dissipation_nonpos
#audit_axioms BookProof.Phi4.MomRankTwo.orbit_contractive
#audit_axioms BookProof.Phi4.MomRankTwo.cont_orbit_contractive
#audit_axioms BookProof.Phi4.MomRankTwo.cont_orbit_contractive1
#audit_axioms BookProof.Phi4.MomRankTwo.cont_orbit_contractive2
#audit_axioms BookProof.Phi4.MomRankTwo.fullMetric_im_zero
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_fullMetric_apply
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_fullMetric_apply
#audit_axioms BookProof.Phi4.MomRankTwo.norm_synthesize_sq
#audit_axioms BookProof.Phi4.MomRankTwo.norm_pgLp_one_sq
#audit_axioms BookProof.Phi4.MomRankTwo.Vmat_gram
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_Vmat
#audit_axioms BookProof.Phi4.MomRankTwo.synthesize_mem
#audit_axioms BookProof.Phi4.MomRankTwo.hasDerivAt_synthesize
#audit_axioms BookProof.Phi4.MomRankTwo.y_zero
#audit_axioms BookProof.Phi4.MomRankTwo.hasDerivAt_y
#audit_axioms BookProof.Phi4.MomRankTwo.hasDerivAt_v
#audit_axioms BookProof.Phi4.MomRankTwo.y_norm_sq
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_W2C_e0
#audit_axioms BookProof.Phi4.MomRankTwo.defectC_gram
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_defectC
#audit_axioms BookProof.Phi4.MomRankTwo.defect_rate_e0
#audit_axioms BookProof.Phi4.MomRankTwo.y_norm_contractive
#audit_axioms BookProof.Phi4.MomRankTwo.Vmat_retained
#audit_axioms BookProof.Phi4.MomRankTwo.VmatC_mulVec_retained
#audit_axioms BookProof.Phi4.MomRankTwo.VmatC_mulVec_of_three_le
#audit_axioms BookProof.Phi4.MomRankTwo.synthesizeC_eq_sum
#audit_axioms BookProof.Phi4.MomRankTwo.sum_fin_eleven_eq_sum_three
#audit_axioms BookProof.Phi4.MomRankTwo.toComplex_of_im_zero
#audit_axioms BookProof.Phi4.MomRankTwo.fullColumns_im_zero
#audit_axioms BookProof.Phi4.MomRankTwo.fullColumnsC_apply
#audit_axioms BookProof.Phi4.MomRankTwo.pgLp_sum_smul
#audit_axioms BookProof.Phi4.MomRankTwo.innerHam_synthesizeC
#audit_axioms BookProof.Phi4.MomRankTwo.innerHam_y
#audit_axioms BookProof.Phi4.MomRankTwo.synthesize_add
#audit_axioms BookProof.Phi4.MomRankTwo.synthesize_sub
#audit_axioms BookProof.Phi4.MomRankTwo.synthesize_smul
#audit_axioms BookProof.Phi4.MomRankTwo.defect_split
#audit_axioms BookProof.Phi4.MomRankTwo.defectC_split
#audit_axioms BookProof.Phi4.MomRankTwo.innerHam_residual
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_sub
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_fin_two
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_fin_two_nonneg
#audit_axioms BookProof.Phi4.MomRankTwo.toComplex_mk
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_apply_re
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_apply_im
#audit_axioms BookProof.Phi4.MomRankTwo.toComplex_defectBound
#audit_axioms BookProof.Phi4.MomRankTwo.defectGram_hermitian
#audit_axioms BookProof.Phi4.MomRankTwo.defectPSD_hermitian
#audit_axioms BookProof.Phi4.MomRankTwo.defectPSD_00
#audit_axioms BookProof.Phi4.MomRankTwo.defectPSD_11
#audit_axioms BookProof.Phi4.MomRankTwo.defectPSD_det
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_defectPSD
#audit_axioms BookProof.Phi4.MomRankTwo.normSq_toCMat_apply
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_defectPSD_real
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_defectGram_le
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_speedMat
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_accMat
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_speedMat
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_accMat
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_e0_eq
#audit_axioms BookProof.Phi4.MomRankTwo.c1_zero
#audit_axioms BookProof.Phi4.MomRankTwo.c2_zero
#audit_axioms BookProof.Phi4.MomRankTwo.speedMat_rate
#audit_axioms BookProof.Phi4.MomRankTwo.accMat_rate
#audit_axioms BookProof.Phi4.MomRankTwo.speed_rate
#audit_axioms BookProof.Phi4.MomRankTwo.accel_rate
#audit_axioms BookProof.Phi4.MomRankTwo.norm_synthesize_defectC_e0
#audit_axioms BookProof.Phi4.MomRankTwo.norm_synthesize_defectC_le
#audit_axioms BookProof.Phi4.MomRankTwo.residual_bound
#audit_axioms BookProof.Phi4.MomRankTwo.state_error_bound
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_transvMat
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_transvMat
#audit_axioms BookProof.Phi4.MomRankTwo.transvMat_hermitian
#audit_axioms BookProof.Phi4.MomRankTwo.transvPSD_hermitian
#audit_axioms BookProof.Phi4.MomRankTwo.transvPSD_00
#audit_axioms BookProof.Phi4.MomRankTwo.transvPSD_11
#audit_axioms BookProof.Phi4.MomRankTwo.transvPSD_det
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_transvPSD
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_transvMat_le
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_transvSpeedMat
#audit_axioms BookProof.Phi4.MomRankTwo.normSqC_transvSpeed_le
#audit_axioms BookProof.Phi4.MomRankTwo.transvSpeedMat_rate
#audit_axioms BookProof.Phi4.MomRankTwo.zvec_norm_sq
#audit_axioms BookProof.Phi4.MomRankTwo.z_norm_sq
#audit_axioms BookProof.Phi4.MomRankTwo.hasDerivAt_z
#audit_axioms BookProof.Phi4.MomRankTwo.hasDerivAt_zvec_c1
#audit_axioms BookProof.Phi4.MomRankTwo.seedProj_Vmat_zero
#audit_axioms BookProof.Phi4.MomRankTwo.toCMat_seedProjVmat_e0
#audit_axioms BookProof.Phi4.MomRankTwo.z_zero
#audit_axioms BookProof.Phi4.MomRankTwo.transv_speed_rate
#audit_axioms BookProof.Phi4.MomRankTwo.z_deriv_lower
#audit_axioms BookProof.Phi4.MomRankTwo.z_deriv2_bound
#audit_axioms BookProof.Phi4.MomRankTwo.z_velocity_lipschitz
#audit_axioms BookProof.Phi4.MomRankTwo.z_transverse_lower
#audit_axioms BookProof.Phi4.MomRankTwo.norm_pgLp_one_pos
#audit_axioms BookProof.Phi4.MomRankTwo.inner_pgLp_self
#audit_axioms BookProof.Phi4.MomRankTwo.norm_pgLp_one_sq_coe
#audit_axioms BookProof.Phi4.MomRankTwo.inner_pgLp_projE
#audit_axioms BookProof.Phi4.MomRankTwo.inner_pgLp_orthE
#audit_axioms BookProof.Phi4.MomRankTwo.inner_projE_orthE
#audit_axioms BookProof.Phi4.MomRankTwo.pyth
#audit_axioms BookProof.Phi4.MomRankTwo.projE_norm_sq
#audit_axioms BookProof.Phi4.MomRankTwo.inner_pgLp_norm_sq
#audit_axioms BookProof.Phi4.MomRankTwo.orthE_add
#audit_axioms BookProof.Phi4.MomRankTwo.orthE_norm_le
#audit_axioms BookProof.Phi4.MomRankTwo.synthesize_seedVec
#audit_axioms BookProof.Phi4.MomRankTwo.inner_pgLp_synthesize
#audit_axioms BookProof.Phi4.MomRankTwo.seedProj_Vmat_row_zero
#audit_axioms BookProof.Phi4.MomRankTwo.seedProj_Vmat_of_ne
#audit_axioms BookProof.Phi4.MomRankTwo.seedProj_Vmat_mulVec
#audit_axioms BookProof.Phi4.MomRankTwo.orthE_y
#audit_axioms BookProof.Phi4.MomRankTwo.orthE_flow_lower
#audit_axioms BookProof.Phi4.MomRankTwo.unitMomCont_return_interval

/-! ## `ChapterScalarOuter` -/

#audit_axioms BookProof.Phi4.Model.outerCore_dense
#audit_axioms BookProof.Phi4.Model.outer_symmetric
#audit_axioms BookProof.Phi4.Model.outer_flow
#audit_axioms BookProof.Phi4.Model.outer_zero_sector
#audit_axioms BookProof.Phi4.Model.outer_number_conserving
#audit_axioms BookProof.Phi4.Model.outer_vacuum_action
#audit_axioms BookProof.Phi4.Model.vacuum_norm
#audit_axioms BookProof.Phi4.Model.vacuum_energy_zero

/-! ## `ChapterScalarEnergy` -/

#audit_axioms BookProof.Phi4.Model.outer_nonneg
#audit_axioms BookProof.Phi4.Model.outer_positive_extension
#audit_axioms BookProof.Phi4.Model.outer_closure_nonneg
#audit_axioms BookProof.Phi4.Model.vacuum_ground

/-! ## `ChapterScalarWindows` -/

#audit_axioms BookProof.Phi4.Model.window_le_domain
#audit_axioms BookProof.Phi4.Model.window_solve_convergence

/-! ## `ChapterScalarSectorOps` -/

#audit_axioms BookProof.Phi4.Model.derPow_succ
#audit_axioms BookProof.Phi4.Model.derPow_add
#audit_axioms BookProof.Phi4.Model.derPow_smul
#audit_axioms BookProof.Phi4.Model.derPow_subtype
#audit_axioms BookProof.Phi4.Model.pushOp_add
#audit_axioms BookProof.Phi4.Model.pushOp_smul
#audit_axioms BookProof.Phi4.Model.sectorOp_add
#audit_axioms BookProof.Phi4.Model.sectorOp_smul
#audit_axioms BookProof.Phi4.Model.fockSectorOp_add
#audit_axioms BookProof.Phi4.Model.fockSectorOp_smul
#audit_axioms BookProof.Phi4.Model.cbosonicSectorOp_add
#audit_axioms BookProof.Phi4.Model.cbosonicSectorOp_smul
#audit_axioms BookProof.Phi4.Model.cbosonicSectorOp_subtype
#audit_axioms BookProof.Phi4.Model.hbosonicFockOp_add_scalar
#audit_axioms BookProof.Phi4.Model.derPow_one
#audit_axioms BookProof.Phi4.Model.inclPow_one
#audit_axioms BookProof.Phi4.Model.sectorOp_one
#audit_axioms BookProof.Phi4.Model.cbosonicSectorOp_oneParticle
#audit_axioms BookProof.Phi4.Model.outerHam_add_const
#audit_axioms BookProof.Phi4.Model.outerHam_oneParticle_eq

/-! ## `ChapterScalarPacketForm` -/

#audit_axioms BookProof.Phi4.packetGram_isSymm
#audit_axioms BookProof.Phi4.packetKinetic_comm
#audit_axioms BookProof.Phi4.packetKineticMat_isSymm
#audit_axioms BookProof.Phi4.packetGram_mul_packetDualKinetic
#audit_axioms BookProof.Phi4.packetWall_isSymm
#audit_axioms BookProof.Phi4.packetMixed_comm
#audit_axioms BookProof.Phi4.packetMixed_eq_ordered_product
#audit_axioms BookProof.Phi4.packetMixed_smul
#audit_axioms BookProof.Phi4.packetNormalizedMixed_smul
