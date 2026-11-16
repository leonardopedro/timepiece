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
#audit_axioms intState_reflectionPositive_of_integrable
