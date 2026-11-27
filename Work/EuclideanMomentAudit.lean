/-
Axiom audit for `BookProof.OSReconstruction.EuclideanMomentHierarchy` (C2, first slice).

The module builds the regulated Euclidean moment hierarchy for a bounded generator on a
complete complex Hilbert space: `e^{-tK}` and its semigroup law, ordered words and their
extension convention, the empty-word normalization, two-point positivity at coincident times,
and a free one-mode regulator whose moment is a strictly positive, genuinely time-dependent
scalar.  It also covers the C3a coarse-graining step of a reference Gaussian, where the coarse
density is `E[|Psi|² | G]` rather than `|E[Psi | G]|²`, and the chain that applies that step
twice, together with the C3b covariance and activity estimates proved for it, and finally the
`n`-step chain of `GaussianChainScales`, whose accumulated covariance is bounded uniformly in
the number of scales.  Every declaration below must rest on `propext`, `Classical.choice`,
`Quot.sound` only.

Run with the project toolchain: `lake build Work.EuclideanMomentAudit`.
-/
import BookProof.OSReconstruction.EuclideanMomentHierarchy
import BookProof.OSReconstruction.EuclideanMehlerCalibration
import BookProof.OSReconstruction.GaussianBlockCoarseDensity
import BookProof.OSReconstruction.GaussianChainScales
import BookProof.OSReconstruction.HalfSpaceInteractingReflectionPositivity
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms euclidEvol_zero
#audit_axioms commute_euclidEvol
#audit_axioms euclidEvol_add
#audit_axioms euclidWord_append
#audit_axioms euclidMoment_nil
#audit_axioms euclidMoment_one_nil
#audit_axioms euclidMoment_zero_adjoint
#audit_axioms euclidMoment_zero_adjoint_re_nonneg
#audit_axioms euclidEvol_scalarK
#audit_axioms euclidMoment_scalarK
#audit_axioms euclidMoment_scalarK_re_pos
#audit_axioms scalarMoment_ne_one
#audit_axioms twoPoint_eq
#audit_axioms twoPoint_zero
#audit_axioms twoPoint_adjoint_zero
#audit_axioms euclidMoment_adjoint_pair
#audit_axioms inner_euclidEvol_selfAdjoint
#audit_axioms euclidEvol_isSelfAdjoint
#audit_axioms euclidMoment_adjoint_eq_inner
#audit_axioms reflectedForm_eq_inner
#audit_axioms reflectedForm_re_nonneg
#audit_axioms twoPoint_reflected_eq_normSq
#audit_axioms twoPoint_reflected_re_nonneg
#audit_axioms scalarK_isSelfAdjoint
#audit_axioms reflectedForm_scalarK_re_nonneg

/-! ## The moment hierarchy's definitions

The definitions the theorems are about, audited for the same reason: a definition that pulled in an
axiom would poison every statement below without appearing in any of their reports.
-/

#audit_axioms euclidEvol
#audit_axioms euclidWord
#audit_axioms euclidMoment
#audit_axioms scalarK
#audit_axioms twoPoint
#audit_axioms twoPoint_eq_euclidMoment
#audit_axioms ofReal_sq_re
#audit_axioms ofReal_sq_re_nonneg
#audit_axioms reflectedVector
#audit_axioms reflectedPair
#audit_axioms reflectedForm
#audit_axioms familyVector
#audit_axioms familyVectorLM
#audit_axioms familyPair
#audit_axioms familyForm
#audit_axioms toInsertions

/-! ## The reflected form as a positive semidefinite form -/

#audit_axioms reflectedPair_self
#audit_axioms reflectedPair_eq_inner
#audit_axioms reflectedPair_conj_swap
#audit_axioms reflectedForm_re_eq_normSq
#audit_axioms reflectedForm_eq_zero_iff
#audit_axioms reflectedPair_eq_zero_of_null
#audit_axioms reflectedPair_cauchy_schwarz
#audit_axioms twoPoint_cauchy_schwarz

/-! ## The pre-Hilbert space of the reconstruction -/

#audit_axioms familyVector_add
#audit_axioms familyVector_smul
#audit_axioms familyPair_eq_reflectedPair
#audit_axioms familyPair_add_left
#audit_axioms familyPair_add_right
#audit_axioms familyForm_eq_normSq
#audit_axioms familyForm_re_nonneg
#audit_axioms familyForm_eq_zero_iff
#audit_axioms familyPair_eq_zero_of_null
#audit_axioms familyPair_congr_left
#audit_axioms familyForm_sub_re_eq_dist_sq
#audit_axioms familyPair_cauchy_schwarz
#audit_axioms reflected_reconstruction

/-! ## The C1 calibration -/

#audit_axioms euclidMoment_scalarK_sqrt
#audit_axioms euclidMoment_scalarK_sqrt_zero
#audit_axioms sliceCross_eq_shiftVariance
#audit_axioms sliceDiagonal_eq_shiftVariance_add_noiseVariance
#audit_axioms sliceDiagonal_pos
#audit_axioms sliceCross_pos
#audit_axioms sliceCross_lt_sliceDiagonal
#audit_axioms free_regulator_reproduces_slice_covariance
#audit_axioms free_regulator_twoPoint_reflected_re_nonneg

/-! ## The reference flow's definitions -/

#audit_axioms shellLaw
#audit_axioms shellDensity
#audit_axioms streamField
#audit_axioms streamCovariance

/-! ## The block coarse-graining definitions

The objects the C3a/C3b theorems are about: the block step, the unit law it averages against, the
block law and its densities.  Audited with the rest so that a definition importing an axiom cannot
hide behind the theorems' reports.
-/

#audit_axioms blockUnit
#audit_axioms blockStep
#audit_axioms blockIntegral
#audit_axioms blockField
#audit_axioms blockLaw
#audit_axioms naiveDensity
#audit_axioms coarseDensity
#audit_axioms blockNaiveChainDensity
#audit_axioms blockChainDensity
#audit_axioms blockChainField
#audit_axioms blockChainLaw
#audit_axioms blockChainCovariance
#audit_axioms blockActivityNorm
#audit_axioms blockChainActivityNorm

/-! ## C3a: the exact coarse-graining step -/

#audit_axioms integral_blockIntegral
#audit_axioms blockIntegral_const
#audit_axioms blockIntegral_add
#audit_axioms blockIntegral_nonneg
#audit_axioms blockIntegral_exterior
#audit_axioms blockIntegral_mul_exterior
#audit_axioms integral_id_blockUnit
#audit_axioms integral_sq_blockUnit
#audit_axioms integral_fst_blockLaw
#audit_axioms integral_fst_sq_blockLaw
#audit_axioms integral_fst_mul_snd_blockLaw
#audit_axioms integral_snd_sq_blockLaw
#audit_axioms blockIntegral_blockField
#audit_axioms blockIntegral_blockField_sq
#audit_axioms coarseDensity_eq_naiveDensity_add
#audit_axioms coarseDensity_ne_naiveDensity
#audit_axioms integral_blockField_sq
#audit_axioms integral_naiveDensity
#audit_axioms integral_naiveDensity_add_one
#audit_axioms integral_coarseDensity_eq_integral_blockField_sq
#audit_axioms variance_decomposition

/-! ## C3a/C3b: the two-step chain, its covariance bound and the activity norm -/

#audit_axioms integral_blockChainDensity
#audit_axioms blockChainDensity_const
#audit_axioms blockChainDensity_nonneg
#audit_axioms blockChainDensity_add
#audit_axioms blockChainDensity_exterior
#audit_axioms blockStep_blockChainField
#audit_axioms blockChainDensity_blockChainField
#audit_axioms blockChainDensity_blockChainField_independent
#audit_axioms integral_sq_add_blockUnit
#audit_axioms blockIntegral_sq_add
#audit_axioms blockStep_blockChainField_sq
#audit_axioms integral_sq_affine_blockUnit
#audit_axioms blockChainDensity_blockChainField_sq
#audit_axioms blockChainDensity_eq_naive_add
#audit_axioms blockChainCovariance_eq
#audit_axioms blockChainCovariance_independent_of_background
#audit_axioms blockChainCovariance_small_field
#audit_axioms integral_abs_partialIntegral_le
#audit_axioms integral_abs_blockIntegral_le
#audit_axioms integral_abs_blockChainDensity_le
#audit_axioms blockChainDensity_eq_iterated

/-! ## The interacting half-space inequality (C2 / E3) -/

#audit_axioms intWeight
#audit_axioms measurable_intWeight
#audit_axioms intState
#audit_axioms intState_univ
#audit_axioms intState_reflectionPositive
#audit_axioms intState_expectation_re_nonneg

/-! ## The interaction as a convergent expansion (C2 / E3) -/

#audit_axioms intStateSum
#audit_axioms intStateSum_univ
#audit_axioms intStateSum_reflectionPositive
#audit_axioms covState_reflectionPositive_of_integrable
#audit_axioms measurePreserving_covMarginal_left
#audit_axioms measurePreserving_covMarginal_right
#audit_axioms covState_reflectionPositive_of_memLp
#audit_axioms intState_reflectionPositive_of_integrable
#audit_axioms intState_reflectionPositive_of_memLp
#audit_axioms memLp_shift_mul_of_bound
#audit_axioms intState_reflectionPositive_of_memLp_of_bounded
#audit_axioms memLp_shift_mul_of_memLp
#audit_axioms intState_reflectionPositive_of_memLp_unbounded
#audit_axioms generalWeight_pos
#audit_axioms generalWeight_swap
#audit_axioms generalWeight_osForm
#audit_axioms not_reflectionPositive_of_generalWeight
#audit_axioms productState_reflectionPositive

/-! ## C3c at reference scale: the totals and the large-field complement -/

#audit_axioms integral_blockNaiveChainDensity
#audit_axioms integral_blockChainDensity_sq
#audit_axioms integral_blockChainDensity_eq_integral_naive_add
#audit_axioms blockNaiveChainDensity_zero_background
#audit_axioms blockChainDensity_sq_zero_background
#audit_axioms blockChainCovariance_le_coupling_sq
#audit_axioms blockChainCovariance_le_mul_density

/-! ## C3d, first slice: the step iterated through arbitrarily many scales -/

#audit_axioms shellDensity_succ
#audit_axioms streamField_succ
#audit_axioms streamField_cons
#audit_axioms streamCovariance_succ
#audit_axioms integral_quadratic_blockUnit
#audit_axioms shellDensity_quadratic
#audit_axioms shellDensity_streamField
#audit_axioms shellDensity_streamField_sq
#audit_axioms shellDensity_streamField_covariance
#audit_axioms streamCovariance_nonneg
#audit_axioms sum_range_pow_succ
#audit_axioms streamCovariance_closed_form
#audit_axioms streamCovariance_le_card
#audit_axioms streamCovariance_le_inv
#audit_axioms integral_shellDensity_streamField_sq
#audit_axioms integral_shellLaw_cons

/-! ## C3d, second slice: the fixed point of the reference flow -/

#audit_axioms streamCovariance_inv_sub
#audit_axioms streamCovariance_lt_inv
#audit_axioms tendsto_streamCovariance
#audit_axioms tendsto_integral_shellDensity_streamField_sq

/-! ## C3c at arbitrary scale: the large-field tail -/

#audit_axioms shellDensity_congr
#audit_axioms shellDensity_nonneg
#audit_axioms integrable_poly_blockUnit
#audit_axioms shellDensity_affine_field_le
#audit_axioms shellTail
#audit_axioms shellTail_le

/-! ## C3d, third slice: the tower identity at every scale -/

#audit_axioms fin_cons_snoc
#audit_axioms fin_snoc_castSucc_last
#audit_axioms measurable_fin_cons
#audit_axioms measurable_fin_snoc
#audit_axioms measurable_fin_snoc_prod
#audit_axioms measurable_comp_fin_cons
#audit_axioms measurable_comp_fin_snoc
#audit_axioms integral_shellLaw_cons_succ
#audit_axioms abs_shellDensity_le
#audit_axioms shellDensity_eq_integral_snoc
#audit_axioms integral_shellDensity_eq
#audit_axioms measurable_streamField
#audit_axioms shellTail_eq_integral_snoc

/-! ## The completion of the pre-Hilbert space, and products of families -/

#audit_axioms reconstructionVectors
#audit_axioms familyProduct
#audit_axioms familyVector_sum
#audit_axioms familyForm_familyProduct
#audit_axioms familyForm_familyProduct_re_nonneg
#audit_axioms norm_familyVector_le_add
#audit_axioms zero_mem_reconstructionVectors
#audit_axioms add_mem_reconstructionVectors
#audit_axioms smul_mem_reconstructionVectors
#audit_axioms reconPreHilbert
#audit_axioms span_reconstructionVectors
#audit_axioms reconSpace
#audit_axioms reconSpace_isClosed
#audit_axioms closure_reconPreHilbert
#audit_axioms reconSpace_complete
#audit_axioms familyVector_mem_reconSpace
#audit_axioms reconSpace_minimal
#audit_axioms reconSpace_inner_familyPair
#audit_axioms memLp_mul_of_memLp_top

/-! ## C3e, first slice: the law-level tail and tightness -/

#audit_axioms shellDensity_subst_last
#audit_axioms renormField
#audit_axioms shellLargeSet
#audit_axioms shellTailLaw
#audit_axioms measurable_renormField
#audit_axioms measurableSet_shellLargeSet
#audit_axioms indicator_shellLargeSet
#audit_axioms shellTail_eq_density_renorm
#audit_axioms integral_shellTail_eq
#audit_axioms shellTailLaw_eq_integral
#audit_axioms shellTail_nonneg
#audit_axioms shellTailLaw_nonneg
#audit_axioms shellTailLaw_le_one
#audit_axioms shellTailLaw_le
#audit_axioms shellTailLaw_le_inv
#audit_axioms exists_shellTailLaw_le

/-! ## C3e, second slice: affine images of the renormalised observable -/

#audit_axioms shellAffineLargeSet
#audit_axioms shellAffineTail
#audit_axioms shellAffineTailLaw
#audit_axioms measurable_affine_renormField
#audit_axioms measurableSet_shellAffineLargeSet
#audit_axioms indicator_shellAffineLargeSet
#audit_axioms shellAffineTail_eq
#audit_axioms shellAffineTail_nonneg
#audit_axioms shellAffineTail_le
#audit_axioms integral_shellAffineTail_eq
#audit_axioms shellAffineTailLaw_eq_integral
#audit_axioms shellAffineTailLaw_nonneg
#audit_axioms shellAffineTailLaw_le_one
#audit_axioms shellAffineTailLaw_le
#audit_axioms shellAffineTailLaw_le_inv
#audit_axioms exists_shellAffineTailLaw_le
#audit_axioms shellAffineTailLaw_one_zero

/-! ## C3e, third packet: the `L¹` moment identity at the law level -/

#audit_axioms integral_sq_affine_const_blockUnit
#audit_axioms measurable_fin_cons_prod
#audit_axioms measurable_shellDensity_param
#audit_axioms shellDensity_sq_min_le
#audit_axioms tendsto_shellDensity_sq_min
#audit_axioms measurable_shellDensity
#audit_axioms ofReal_iSup_of_tendsto
#audit_axioms iSup_ofReal_min
#audit_axioms truncated_moment_eq
#audit_axioms lintegral_shellLaw_sq
#audit_axioms integrable_sq_affine
#audit_axioms integral_shellLaw_sq
#audit_axioms integrable_streamField
#audit_axioms integral_shellLaw_streamField
#audit_axioms integral_shellLaw_centered_sq
#audit_axioms variance_shellLaw_le

/-! ## C3f: the two-point functions of the reference law -/

#audit_axioms integral_shellLaw_coord
#audit_axioms integrable_shellLaw_coord
#audit_axioms integrable_shellLaw_coord_sq
#audit_axioms integral_shellLaw_coord_sq
#audit_axioms integrable_streamField_mul_last
#audit_axioms integral_shellLaw_streamField_mul_last
#audit_axioms integral_shellLaw_renormField
#audit_axioms integral_shellLaw_renormField_mul_last
#audit_axioms integral_shellLaw_renormField_sq
#audit_axioms integral_shellLaw_renormField_centered_sq
#audit_axioms variance_renormField_le
#audit_axioms covariance_pair_shellLaw

/-! ## C3g: the interior cross moments and the two-point kernel of linear statistics -/

#audit_axioms integrable_shellLaw_coord_mul
#audit_axioms integral_shellLaw_coord_mul_coord
#audit_axioms streamField_eq_sum_coeff
#audit_axioms integral_shellLaw_linear_mul_coord
#audit_axioms integral_shellLaw_linear_mul_linear
#audit_axioms integral_shellLaw_streamField_mul_linear

/-! ## C3h: the cross-scale covariance and the coordinate-moment factorization -/

#audit_axioms truncCoeff_castLE
#audit_axioms sum_truncCoeff_mul
#audit_axioms sum_streamCoeff_mul_pow
#audit_axioms integral_shellLaw_streamField_mul_coord
#audit_axioms integral_shellLaw_streamField_mul_smaller
#audit_axioms integral_shellLaw_prod_coord_pow

/-! ## C3i: the three- and four-point functions of the reference law -/

#audit_axioms shellLaw_eq_productGauss
#audit_axioms integral_shellLaw_prod_coord
#audit_axioms pairingSet_four
#audit_axioms pairingProd01
#audit_axioms pairingProd02
#audit_axioms pairingProd03
#audit_axioms wickSum_four
#audit_axioms integral_pow_odd_blockUnit
#audit_axioms exists_odd_card_fiber_three
#audit_axioms integral_shellLaw_coord_three
#audit_axioms integral_shellLaw_coord_four

/-! ## C3j: the five- and six-point functions, uniformly in the number of fields -/

#audit_axioms integral_shellLaw_prod_coord_eq_wickSum
#audit_axioms integral_shellLaw_prod_coord_odd
#audit_axioms integral_shellLaw_prod_coord_even
#audit_axioms integral_shellLaw_coord_five
#audit_axioms pairingSet_six
#audit_axioms pairingSet_six_card
#audit_axioms pairingProdSix01
#audit_axioms pairingProdSix02
#audit_axioms pairingProdSix03
#audit_axioms pairingProdSix04
#audit_axioms pairingProdSix05
#audit_axioms pairingProdSix06
#audit_axioms pairingProdSix07
#audit_axioms pairingProdSix08
#audit_axioms pairingProdSix09
#audit_axioms pairingProdSix10
#audit_axioms pairingProdSix11
#audit_axioms pairingProdSix12
#audit_axioms pairingProdSix13
#audit_axioms pairingProdSix14
#audit_axioms pairingProdSix15
#audit_axioms wickSum_six
#audit_axioms integral_shellLaw_coord_six

/-! ## C3k: the connected four-point function of the reference law -/

#audit_axioms connectedFour
#audit_axioms shellFace
#audit_axioms shellFace_empty
#audit_axioms shellFace_singleton
#audit_axioms connectedFourShell
#audit_axioms connectedFourShell_eq
#audit_axioms shellFace_univ
#audit_axioms shellFace_pair
#audit_axioms connectedFourShell_eq_pair
#audit_axioms connectedFourShell_eq_zero
#audit_axioms connectedFour_coord_eq
#audit_axioms connectedFour_coord_eq_zero

/-! ## C3l: the connected five-point function of the reference law -/

#audit_axioms connectedFive
#audit_axioms connectedFive_one
#audit_axioms shellFace5
#audit_axioms shellFace5_singleton
#audit_axioms shellFace5_card_one
#audit_axioms shellFace5_card_three
#audit_axioms shellFace5_univ
#audit_axioms shellFace5_univ_eq_zero
#audit_axioms connectedFiveShell
#audit_axioms connectedFive_eq_zero
#audit_axioms connectedFiveShell_eq_zero
#audit_axioms connectedFive_coord_eq_zero
