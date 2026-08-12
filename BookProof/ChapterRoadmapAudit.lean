/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import BookProof.ChapterH4
import BookProof.ChapterF4
import BookProof.ChapterHolomorphic
import BookProof.ChapterB4
import BookProof.ChapterMajoranaFourier
import BookProof.ChapterFreeFieldBornFiberSpectrum
import BookProof.ChapterFreeFieldBornSignOrientationKernel
import BookProof.ChapterA3x
import BookProof.ChapterBoseEinstein
import BookProof.ChapterThermalMaxEntropy
import BookProof.ChapterLinftyMultiplication
import BookProof.ChapterSoftmaxJacobian
import BookProof.ChapterAttentionOutput
import BookProof.ChapterAttentionMasking
import BookProof.ChapterCoherentDynamics
import BookProof.ChapterCoherentThermalFidelity
import BookProof.ChapterSolovayTailDimension
import BookProof.ChapterSolovaySeparableExistence
import BookProof.ChapterSolovayHilbertTensor
import BookProof.ChapterAbelianAtomicCondensation
import BookProof.ChapterLinftyMaximalAbelian
import BookProof.ChapterTensorCompleteness
import BookProof.ChapterAbelianGelfandModel
import BookProof.ChapterSpectralMultiplication
import BookProof.ChapterSpectralCommutant
import BookProof.ChapterCyclicDecomposition
import BookProof.ChapterCyclicDirectSum
import BookProof.ChapterSpectralDirectSum
import BookProof.ChapterAbelianCyclicModel
import BookProof.ChapterAbelianCyclicCommutant
import BookProof.ChapterAbelianDirectSum
import BookProof.ChapterMeasureAtomicDiffuse
import BookProof.ChapterDiffuseCdfModel
import BookProof.ChapterDiffuseUnitaryModel
import BookProof.ChapterAtomicDiagonalModel
import BookProof.ChapterLpRestrictSplit
import BookProof.ChapterLpScaleMeasure
import BookProof.ChapterAbelianClassificationList
import BookProof.ChapterStandardBorelClassification
import BookProof.ChapterSeparableSpectrum
import BookProof.ChapterSeparableL2Model
import BookProof.ChapterAttentionFactorization
import BookProof.ChapterRotaryPosition
import BookProof.ChapterAttentionRetrieval
import BookProof.ChapterAttentionEquivariance
import BookProof.ChapterAttentionMixture
import BookProof.ChapterCrossEntropyGradient
import BookProof.ChapterAttentionCollision
import BookProof.ChapterAttentionConcentration
import BookProof.ChapterAttentionMarkov
import BookProof.ChapterScaledDotProduct
import BookProof.ChapterAttentionOutputVariance
import BookProof.ChapterAttentionLowRank
import BookProof.ChapterLayerNorm
import BookProof.ChapterSinusoidalPosition
import BookProof.ChapterAttentionMixing
import BookProof.ChapterAttentionTemperature
import BookProof.ChapterAttentionSink
import BookProof.ChapterAttentionCoarseGrain
import BookProof.ChapterAttentionQKCircuit
import BookProof.ChapterResidualStream
import BookProof.ChapterAttentionFreeEnergy
import BookProof.ChapterAttentionSparse
import BookProof.ChapterAttentionOVCircuit
import BookProof.ChapterAttentionSaturation
import BookProof.ChapterAttentionPrior
import BookProof.ChapterAttentionStreaming
import BookProof.ChapterAttentionLocality
import BookProof.ChapterAttentionCalibration
import BookProof.ChapterAttentionTopK

/-!
# Roadmap headline certificate

This module turns the roadmap's final prose-only hygiene audit into a checked
Lean artifact.  The aggregate theorem below simultaneously exposes three
representative mathematical headlines from independent work packages:

* the two-dimensional pure-state obstruction from the Gleason chapter;
* the Cauchy–Riemann characterization of holomorphicity on open sets;
* unitarity of the concrete Majorana–Fourier boost block.

The imported Count-Sketch, Misra–Gries, and SIRK headlines are also checked in
this module by the `#print axioms` commands at the end.
-/

namespace BookProof.ChapterRoadmapAudit

open Matrix

/-
A single kernel-checked certificate collecting representative headline
results whose final roadmap audit had previously only been recorded in prose.
-/
theorem roadmap_headline_certificate :
    (¬ ∃ ρ, BookProof.ChapterB4.IsPureState ρ ∧
      Matrix.trace (ρ * BookProof.ChapterB4.P1) = 1 / 2 ∧
      Matrix.trace (ρ * BookProof.ChapterB4.P2) = 1 / 2) ∧
    (∀ (f : ℂ → ℂ) (s : Set ℂ), IsOpen s →
      (∀ z ∈ s, DifferentiableAt ℝ f z) →
      ((∀ z ∈ s, fderiv ℝ f z Complex.I =
          Complex.I • fderiv ℝ f z 1) ↔ AnalyticOn ℂ f s)) ∧
    (∀ (m q : ℝ), 0 ≤ m → 0 < q →
      ∀ n : Fin 3 → ℝ, (∑ i, (n i) ^ 2) = 1 →
      (BookProof.ChapterMajoranaFourier.boostBlock
          (BookProof.ChapterMajoranaFourier.boostC m q)
          (BookProof.ChapterMajoranaFourier.boostS m q)
          (BookProof.ChapterMajoranaFourier.Aop n))ᴴ *
        BookProof.ChapterMajoranaFourier.boostBlock
          (BookProof.ChapterMajoranaFourier.boostC m q)
          (BookProof.ChapterMajoranaFourier.boostS m q)
          (BookProof.ChapterMajoranaFourier.Aop n) = 1) := by
  refine ⟨BookProof.ChapterB4.no_pure_state_satisfies_both, ?_, ?_⟩
  · exact fun _ _ hs hf ↦
      BookProof.ChapterHolomorphic.cauchyRiemann_iff_analyticOn hs hf
  · exact fun m q hm hq n hn ↦
      BookProof.ChapterMajoranaFourier.majoranaFourier_boostBlock_unitary
        m q hm hq n hn

/-
A second checked certificate covers the final finite Born-fiber and sign-gauge
integration wave.  It records both the complete spectrum of possible fiber
cardinalities and the index-two parity law for the orientation character.
-/
theorem roadmap_finite_born_certificate :
    (∀ (n c : ℕ),
      (∃ p : ↥(stdSimplex ℝ (Fin n)),
          Nat.card ↥(BookProof.ChapterFreeFieldBornQuotient.bornMapSphere n ⁻¹' {p}) = c) ↔
        ∃ k, 1 ≤ k ∧ k ≤ n ∧ c = 2 ^ k) ∧
    (∀ (n : ℕ) (b₁ b₂ : Fin n → Bool),
      BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix
          (fun k => xor (b₁ k) (b₂ k)) ∈
          Matrix.specialOrthogonalGroup (Fin n) ℝ ↔
        (BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix b₁ ∈
            Matrix.specialOrthogonalGroup (Fin n) ℝ ↔
         BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix b₂ ∈
            Matrix.specialOrthogonalGroup (Fin n) ℝ)) := by
  constructor
  · intro n c
    exact BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff
  · intro n b₁ b₂
    exact
      BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff
        b₁ b₂

#print axioms roadmap_headline_certificate
#print axioms roadmap_finite_born_certificate
#print axioms BookProof.ChapterH4.sirk_error_bound
#print axioms BookProof.ChapterF4.misraGries_bound
#print axioms BookProof.ChapterF4.countsketch_unbiased
#print axioms BookProof.ChapterF4.countSketch_unbiased
#print axioms BookProof.ChapterA3x.tensorCube_complete_reducibility
#print axioms BookProof.ChapterBoseEinstein.thermalProb_boseEinstein
#print axioms BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein_eq_coth
#print axioms BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy
#print axioms BookProof.ChapterLinftyMultiplication.vonNeumann_abelian_class_Linfty
#print axioms BookProof.ChapterSoftmaxJacobian.hasDerivAt_scoreSoftmax_score
#print axioms BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form
#print axioms BookProof.ChapterAttentionOutput.tendsto_headOutput
#print axioms BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional
#print axioms BookProof.ChapterCoherentDynamics.bornWeightC_isometry
#print axioms BookProof.ChapterCoherentDynamics.bornWeightC_translation_invariant
#print axioms BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul
#print axioms BookProof.ChapterAttentionFactorization.shannonEntropy_prodSoftmax
#print axioms BookProof.ChapterRotaryPosition.inner_rotaryEncode
#print axioms BookProof.ChapterRotaryPosition.bornWeightC_rotaryEncode_shift
#print axioms BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin
#print axioms BookProof.ChapterAttentionRetrieval.scoreSoftmax_ge_inv_of_margin
#print axioms BookProof.ChapterAttentionEquivariance.headOutput_perm
#print axioms BookProof.ChapterAttentionMixture.multiHead_output_eq_mean
#print axioms BookProof.ChapterAttentionMixture.le_shannonEntropy_mixture
#print axioms BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score
#print axioms BookProof.ChapterAttentionCollision.renyi2_le_shannonEntropy
#print axioms BookProof.ChapterAttentionCollision.effectiveSupport_scoreSoftmax_mem_Icc
#print axioms BookProof.ChapterAttentionConcentration.neg_log_le_shannonEntropy
#print axioms BookProof.ChapterAttentionConcentration.card_filter_le_inv
#print axioms BookProof.ChapterAttentionMarkov.l1dist_push_attentionMatrix_le
#print axioms BookProof.ChapterAttentionMarkov.push_compose
#print axioms BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq
#print axioms BookProof.ChapterScaledDotProduct.rademacherMean_scaledDot_sq_of_unit_entries
#print axioms BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq
#print axioms BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes
#print axioms BookProof.ChapterAttentionLowRank.rank_scoreMatrix_le
#print axioms BookProof.ChapterAttentionLowRank.not_exists_scoreMatrix_one
#print axioms BookProof.ChapterLayerNorm.sum_sq_layerNorm
#print axioms BookProof.ChapterLayerNorm.scoreSoftmax_layerNorm_ge
#print axioms BookProof.ChapterSinusoidalPosition.peInner_eq_sum_cos
#print axioms BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_shift
#print axioms BookProof.ChapterAttentionMixing.l1dist_pushIter_le
#print axioms BookProof.ChapterAttentionMixing.tendsto_l1dist_pushIter_attentionMatrix

#print axioms BookProof.ChapterAttentionTemperature.scoreSoftmax_monotone_of_isMax
#print axioms BookProof.ChapterAttentionTemperature.log_card_sub_le_shannonEntropy
#print axioms BookProof.ChapterAttentionSink.scoreSoftmax_sink_succ
#print axioms BookProof.ChapterAttentionSink.shannonEntropy_sink
#print axioms BookProof.ChapterAttentionCoarseGrain.observableExpectation_merge
#print axioms BookProof.ChapterAttentionCoarseGrain.shannonEntropy_mergeWeights_le
#print axioms BookProof.ChapterAttentionQKCircuit.qkScore_gauge
#print axioms BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le
#print axioms BookProof.ChapterResidualStream.residual_injective
#print axioms BookProof.ChapterResidualStream.norm_iterate_residual_sub_le

#print axioms BookProof.ChapterAttentionFreeEnergy.abs_logPartition_div_sub_le
#print axioms BookProof.ChapterAttentionFreeEnergy.sub_meanScore_le
#print axioms BookProof.ChapterAttentionFreeEnergy.tendsto_meanScore_atTop
#print axioms BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq
#print axioms BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le
#print axioms BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput
#print axioms BookProof.ChapterAttentionOVCircuit.rank_ovMatrix_le
#print axioms BookProof.ChapterAttentionSaturation.sum_abs_softmaxJacobian_row
#print axioms BookProof.ChapterAttentionSaturation.sum_abs_softmaxJacobian_le_of_confident
#print axioms BookProof.ChapterAttentionPrior.priorSoftmax_eq_posterior
#print axioms BookProof.ChapterAttentionPrior.priorSoftmax_odds
#print axioms BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias

#print axioms BookProof.ChapterAttentionStreaming.scoreSoftmax_snoc_castSucc
#print axioms BookProof.ChapterAttentionStreaming.headOutput_snoc
#print axioms BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le
#print axioms BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le
#print axioms BookProof.ChapterAttentionCalibration.attentionEntropy_strictAntiOn
#print axioms BookProof.ChapterAttentionCalibration.existsUnique_beta_attentionEntropy_eq
#print axioms BookProof.ChapterAttentionTopK.sum_le_sum_of_isTop
#print axioms BookProof.ChapterAttentionTopK.l1dist_maskedSoftmax_le_of_isTop

#print axioms BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq
#print axioms BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum_eq_fidelityC
#print axioms BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_width_eq
open BookProof.ChapterCoherentThermalFidelity in
#print axioms thermalTemperature_eq_fidelity_width_sub_coherent_half
#print axioms BookProof.ChapterCoherentThermalFidelity.dtOverlap_coherentParameter

#print axioms BookProof.ChapterSolovayTailDimension.substrateBasisVector_orthonormal
#print axioms BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional
#print axioms BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction
open BookProof.ChapterSolovaySeparableExistence in
#print axioms exists_separable_prob_with_arbitrary_finite_law
open BookProof.ChapterSolovaySeparableExistence in
#print axioms exists_separable_prob_with_arbitrary_finite_law_substrate
#print axioms BookProof.ChapterSolovaySeparableExistence.prod_disintegration

#print axioms BookProof.ChapterSolovayHilbertTensor.measurePreserving_prodProdProdComm
#print axioms BookProof.ChapterSolovayHilbertTensor.solovayTensorEquiv_map
#print axioms BookProof.ChapterSolovayHilbertTensor.inner_tensorLp

#print axioms BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff
#print axioms BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal
#print axioms BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy

#print axioms BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le
#print axioms BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp
#print axioms BookProof.ChapterLinftyMaximalAbelian.multOp_algebra_maximal_abelian
#print axioms BookProof.ChapterLinftyMaximalAbelian.unitInterval_multOp_maximal_abelian

#print axioms BookProof.ChapterTensorCompleteness.indicator_mem_tensorSpan
#print axioms BookProof.ChapterTensorCompleteness.tensorSpan_eq_top
#print axioms BookProof.ChapterTensorCompleteness.pureTensors_dense
#print axioms BookProof.ChapterTensorCompleteness.exists_tensor_approx
#print axioms BookProof.ChapterTensorCompleteness.inner_tensorOf
#print axioms BookProof.ChapterTensorCompleteness.orthonormal_tensorOf
#print axioms BookProof.ChapterTensorCompleteness.tensorFamily_span_eq_top
#print axioms BookProof.ChapterTensorCompleteness.tensorHilbertBasis_repr_apply
#print axioms BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis
#print axioms BookProof.ChapterTensorCompleteness.hasSum_sq_norm_inner_tensorHilbertBasis

#print axioms BookProof.ChapterAbelianGelfandModel.integral_rieszStateMeasure
#print axioms BookProof.ChapterAbelianGelfandModel.isProbabilityMeasure_rieszStateMeasure
#print axioms BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state
#print axioms BookProof.ChapterAbelianGelfandModel.mulRepHom_injective
#print axioms BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep
#print axioms BookProof.ChapterAbelianGelfandModel.norm_oneVec
#print axioms BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication

#print axioms BookProof.ChapterSpectralMultiplication.vectorState_star_mul_self
#print axioms BookProof.ChapterSpectralMultiplication.integral_spectralMeasure
#print axioms BookProof.ChapterSpectralMultiplication.norm_cfcHom_apply
#print axioms BookProof.ChapterSpectralMultiplication.spectralUnitary_toLp
#print axioms BookProof.ChapterSpectralMultiplication.spectralUnitary_intertwines_cfc
#print axioms BookProof.ChapterSpectralMultiplication.spectralUnitary_intertwines
#print axioms BookProof.ChapterSpectralMultiplication.spectral_multiplication_model

#print axioms BookProof.ChapterSpectralCommutant.centralizer_multAlgebra
#print axioms BookProof.ChapterSpectralCommutant.bicommutant_multAlgebra
#print axioms BookProof.ChapterSpectralCommutant.contCommutant_eq_multOp
#print axioms BookProof.ChapterSpectralCommutant.centralizer_cfcSet
#print axioms BookProof.ChapterSpectralCommutant.centralizer_multModel
#print axioms BookProof.ChapterSpectralCommutant.bicommutant_cfcSet
#print axioms BookProof.ChapterSpectralCommutant.commutant_cfcSet_isCommutative

#print axioms BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace
#print axioms BookProof.ChapterCyclicDecomposition.invariant_orthogonal
#print axioms BookProof.ChapterCyclicDecomposition.cyclicSubspace_le_orthogonal
#print axioms BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition

#print axioms BookProof.ChapterCyclicDirectSum.orthogonalFamily_cyclicSubspace
#print axioms BookProof.ChapterCyclicDirectSum.isHilbertSum_cyclicSubspace
#print axioms BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace
#print axioms BookProof.ChapterCyclicDirectSum.commute_starProjection_cfcHom
#print axioms BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes
#print axioms BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace

#print axioms BookProof.ChapterSpectralDirectSum.denseRange_cfcVecTo
#print axioms BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding
#print axioms BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc
#print axioms BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines
#print axioms BookProof.ChapterSpectralDirectSum.orthogonalFamily_cyclicEmbedding
#print axioms BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general
#print axioms BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily
#print axioms BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_separable

#print axioms BookProof.ChapterAbelianCyclicModel.repState_star_mul_self
#print axioms BookProof.ChapterAbelianCyclicModel.integral_repMeasure
#print axioms BookProof.ChapterAbelianCyclicModel.norm_rep_apply
#print axioms BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_toLp
#print axioms BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines
#print axioms BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model
#print axioms BookProof.ChapterAbelianCyclicModel.abelian_algebra_multiplication_model

#print axioms BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet
#print axioms BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep
#print axioms BookProof.ChapterAbelianCyclicCommutant.bicommutant_repSet
#print axioms BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative
#print axioms BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic

#print axioms BookProof.ChapterAbelianDirectSum.repInvariant_orthogonal
#print axioms BookProof.ChapterAbelianDirectSum.exists_rep_cyclic_decomposition
#print axioms BookProof.ChapterAbelianDirectSum.exists_isHilbertSum_repCyclicSubspace
#print axioms BookProof.ChapterAbelianDirectSum.starProjection_commutes_rep
#print axioms BookProof.ChapterAbelianDirectSum.range_repEmbedding
#print axioms BookProof.ChapterAbelianDirectSum.repEmbedding_intertwines
#print axioms BookProof.ChapterAbelianDirectSum.abelian_multiplication_model_general
#print axioms BookProof.ChapterAbelianDirectSum.abelian_multiplication_model_separable
#print axioms BookProof.ChapterAbelianDirectSum.abelian_algebra_multiplication_model_general

#print axioms BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet
#print axioms BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_add_restrict_compl
#print axioms BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac
#print axioms BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition
#print axioms BookProof.ChapterMeasureAtomicDiffuse.abelian_multiplication_model_atomic_diffuse

#print axioms BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms
#print axioms BookProof.ChapterDiffuseCdfModel.exists_cdf_eq
#print axioms BookProof.ChapterDiffuseCdfModel.measure_cdf_le
#print axioms BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc

#print axioms BookProof.ChapterDiffuseUnitaryModel.measurePreserving_cdf
#print axioms BookProof.ChapterDiffuseUnitaryModel.measureDense_cdfAlgebra
#print axioms BookProof.ChapterDiffuseUnitaryModel.cdfRange_eq_top
#print axioms BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines
#print axioms BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform

#print axioms BookProof.ChapterAtomicDiagonalModel.orthonormal_atomVec
#print axioms BookProof.ChapterAtomicDiagonalModel.atomBasis
#print axioms BookProof.ChapterAtomicDiagonalModel.multOp_atomVec
#print axioms BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal

#print axioms BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl
#print axioms BookProof.ChapterLpRestrictSplit.isHilbertSum_splitEmbed
#print axioms BookProof.ChapterLpRestrictSplit.restrictEmbed_intertwines

#print axioms BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines
#print axioms BookProof.ChapterLpScaleMeasure.normalized_multiplication_model

#print axioms BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model
#print axioms BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model
#print axioms BookProof.ChapterAbelianClassificationList.vonNeumann_abelian_classification_list

#print axioms BookProof.ChapterStandardBorelClassification.transportUnitary_intertwines
#print axioms BookProof.ChapterStandardBorelClassification.purelyAtomic_of_countable
open BookProof.ChapterStandardBorelClassification in
#print axioms standardBorel_multiplication_model_transport
#print axioms BookProof.ChapterStandardBorelClassification.standardBorel_classification_list
#print axioms BookProof.ChapterStandardBorelClassification.abelian_multiplication_model_classified
open BookProof.ChapterStandardBorelClassification in
#print axioms spectral_multiplication_model_classified

#print axioms BookProof.ChapterSeparableSpectrum.metrizableSpace_of_separable_continuousMap
#print axioms BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap
#print axioms BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace
open BookProof.ChapterSeparableSpectrum in
#print axioms abelian_multiplication_model_classified_separable
open BookProof.ChapterSeparableSpectrum in
#print axioms abelian_algebra_multiplication_model_classified

#print axioms BookProof.ChapterSeparableL2Model.exists_countable_dense_continuous
open BookProof.ChapterSeparableL2Model in
#print axioms separable_Lp_realizes_standard_type
open BookProof.ChapterSeparableL2Model in
#print axioms abelian_multiplication_model_classified_separable_hilbert
open BookProof.ChapterSeparableL2Model in
#print axioms abelian_algebra_multiplication_model_classified_separable_hilbert

end BookProof.ChapterRoadmapAudit
