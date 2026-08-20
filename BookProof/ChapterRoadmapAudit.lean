/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import BookProof.ChapterH4
import BookProof.ChapterNavierStokesGaugeY2
import BookProof.ChapterNavierStokesBilinearEsa
import BookProof.ChapterNavierStokesAffineFiberEsa
import BookProof.ChapterNavierStokesAffineBlockEsa
import BookProof.ChapterNavierStokesSignFlip
import BookProof.ChapterNavierStokesSignedShift
import BookProof.ChapterNavierStokesThreeComponent
import BookProof.ChapterNavierStokesCanonicalVector
import BookProof.ChapterEsaClosure
import BookProof.ChapterNavierStokesHashimoto
import BookProof.ChapterNavierStokesLagrangianKatoRellich
import BookProof.ChapterStoneFlows
import BookProof.ChapterGaugeFixing
import BookProof.ChapterQuantumGravityDensitized
import BookProof.ChapterQuantumGravityHalfDensity
import BookProof.ChapterYangMillsFriedrichs
import BookProof.ChapterYangMillsFriedrichsLimit
import BookProof.ChapterHermiteGalerkinFriedrichs
import BookProof.ChapterHashimotoShiftInvert
import BookProof.ChapterHashimotoComplexShifts
import BookProof.ChapterFriedrichsExtension
import BookProof.ChapterHermiteProductCore
import BookProof.ChapterYangMillsHermite
import BookProof.ChapterFockSecondQuantization
import BookProof.ChapterWaveUnboundedPotential
import BookProof.ChapterHarmonicOscillatorEsa
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
import BookProof.ChapterWeakValue
import BookProof.ChapterContinuityUnitary
import BookProof.ChapterContinuityUnitaryInfinite
import BookProof.ChapterBornMeasure
import BookProof.ChapterUnboundedPosition
import BookProof.ChapterUnitaryTransport
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

#print axioms BookProof.ChapterWeakValue.weakValue_wellDefined
#print axioms BookProof.ChapterWeakValue.weakValue_unique
#print axioms BookProof.ChapterWeakValue.weakValue_diag
#print axioms BookProof.ChapterWeakValue.weakValue_diag_isReal
#print axioms BookProof.ChapterWeakValue.weakValue_linear
#print axioms BookProof.ChapterWeakValue.weakValue_proj_sum
#print axioms BookProof.ChapterWeakValue.jointProb_eq_normSq_weakNumerator
#print axioms BookProof.ChapterWeakValue.condProb_eq_weakNumerator_ratio
#print axioms BookProof.ChapterWeakValue.dslit_weakValue

#print axioms BookProof.ChapterContinuityUnitary.momentum_hermitian
#print axioms BookProof.ChapterContinuityUnitary.continuityHamiltonian_hermitian
#print axioms BookProof.ChapterContinuityUnitary.momentum_mul_velocityOp_not_hermitian
#print axioms BookProof.ChapterContinuityUnitary.continuityUnitary_unitary
#print axioms BookProof.ChapterContinuityUnitary.continuityUnitary_add
#print axioms BookProof.ChapterContinuityUnitary.bornRecover_univ
#print axioms BookProof.ChapterContinuityUnitary.condProb_of_continuity
#print axioms BookProof.ChapterContinuityUnitary.tensorIsom_tmul
#print axioms BookProof.ChapterContinuityUnitary.bornRecover_product_state

#print axioms BookProof.ChapterContinuityUnitaryInfinite.momentum_isSelfAdjoint
#print axioms BookProof.ChapterContinuityUnitaryInfinite.velocityOp_isSelfAdjoint
#print axioms BookProof.ChapterContinuityUnitaryInfinite.continuityHamiltonian_isSelfAdjoint
#print axioms BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_unitary
#print axioms BookProof.ChapterContinuityUnitaryInfinite.continuityUnitary_add
#print axioms BookProof.ChapterContinuityUnitaryInfinite.bornRecover_tsum_univ
#print axioms BookProof.ChapterContinuityUnitaryInfinite.condProb_of_continuity_infinite

#print axioms BookProof.ChapterBornMeasure.lintegral_bornDensity
#print axioms BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure
#print axioms BookProof.ChapterBornMeasure.bornMeasure_absolutelyContinuous
#print axioms BookProof.ChapterBornMeasure.bornMeasure_iUnion
#print axioms BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics

#print axioms BookProof.ChapterUnboundedPosition.mulOp_symmetric
#print axioms BookProof.ChapterUnboundedPosition.mulDomain_dense
#print axioms BookProof.ChapterUnboundedPosition.position_unbounded
#print axioms BookProof.ChapterUnboundedPosition.position_not_boundedOperator
#print axioms BookProof.ChapterUnboundedPosition.adjointDomain_eq_mulDomain
#print axioms BookProof.ChapterUnboundedPosition.adjoint_eq_mulOp
#print axioms BookProof.ChapterUnboundedPosition.phaseUnitary_add
#print axioms BookProof.ChapterUnboundedPosition.tendsto_phaseUnitary
#print axioms BookProof.ChapterUnboundedPosition.tendsto_slope_phaseUnitary

#print axioms BookProof.ChapterUnitaryTransport.transportDomain_dense
#print axioms BookProof.ChapterUnitaryTransport.transportOp_symmetric
#print axioms BookProof.ChapterUnitaryTransport.transport_adjointDomain
#print axioms BookProof.ChapterUnitaryTransport.transport_isSelfAdjointOn
#print axioms BookProof.ChapterUnitaryTransport.tendsto_transportUnitary
#print axioms BookProof.ChapterUnitaryTransport.tendsto_slope_transportUnitary
#print axioms BookProof.ChapterUnitaryTransport.transported_position_isSelfAdjointOn
#print axioms BookProof.ChapterUnitaryTransport.tendsto_slope_transported_position

#print axioms BookProof.NavierStokesGaugeY2.uField2_pderiv_y
#print axioms BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice
#print axioms BookProof.NavierStokesGaugeY2.genY2_leibniz
#print axioms BookProof.NavierStokesGaugeY2.genY2_uField2
#print axioms BookProof.NavierStokesGaugeY2.genY2_uDField
#print axioms BookProof.NavierStokesGaugeY2.genY_uField2_ne_zero
#print axioms BookProof.NavierStokesGaugeY2.genY2_uField_ne_zero
#print axioms BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero
#print axioms BookProof.NavierStokesGaugeY2.genY2_genY2_commute
#print axioms BookProof.NavierStokesGaugeY2.genX_genY2_commute
#print axioms BookProof.NavierStokesGaugeY2.genY_genY2_not_commute
#print axioms BookProof.NavierStokesGaugeY2.genY2_nsSymbol2
#print axioms BookProof.NavierStokesGaugeY2.genX_nsSymbol2
#print axioms BookProof.NavierStokesGaugeY2.setYZero_nsSymbol2

#print axioms BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun
#print axioms BookProof.NavierStokesFlow.BilinearEsa.hasSum_inner_blocks
#print axioms BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH
#print axioms BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn
#print axioms BookProof.NavierStokesFlow.BilinearEsa.deficiencyTrivialAt_bilH
#print axioms BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero
#print axioms BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense
#print axioms BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded

#print axioms BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_symmetricOn
#print axioms BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_relative_bound
#print axioms BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_commForm_bound
#print axioms BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.AffineFiber.affH_symmetricOn
#print axioms BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ
#print axioms BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ
#print axioms BookProof.NavierStokesFlow.AffineFiber.affH_ne_zero_of_pos_shear
#print axioms BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded
#print axioms BookProof.NavierStokesFlow.AffineFiber.affH_domain_dense

#print axioms BookProof.NavierStokesFlow.AffineBlock.affFun_embFun
#print axioms BookProof.NavierStokesFlow.AffineBlock.blockVec_affBlockH
#print axioms BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn
#print axioms BookProof.NavierStokesFlow.AffineBlock.deficiencyTrivialAt_affBlockH
#print axioms BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.AffineBlock.affBlockH_domain_dense
#print axioms BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded

#print axioms BookProof.NavierStokesFlow.SignFlip.essentiallySelfAdjointOn_of_intertwine
#print axioms BookProof.NavierStokesFlow.SignFlip.shiftH_flip
#print axioms BookProof.NavierStokesFlow.SignFlip.saffH_symmetricOn
#print axioms BookProof.NavierStokesFlow.SignFlip.saffH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.SignFlip.saffH_ne_zero_of_shear
#print axioms BookProof.NavierStokesFlow.SignFlip.sblockH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.SignFlip.sblockH_domain_dense

#print axioms BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_symmetricOn
#print axioms BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_relative_bound
#print axioms BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_commForm_bound
#print axioms BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.SignedShift.listH_symmetricOn
#print axioms BookProof.NavierStokesFlow.SignedShift.listH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.SignedShift.gaffH_symmetricOn
#print axioms BookProof.NavierStokesFlow.SignedShift.gaffH_essentiallySelfAdjointOn_core

#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_symmetricOn
#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_coord_pair
#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_coord_rot
#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_coord_shear
#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_coord_diag
#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_ne_zero_of_strain
#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_ne_zero_of_vorticity
#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_not_bounded
#print axioms BookProof.NavierStokesFlow.ThreeComponent.velH_domain_dense

-- `CONSOLIDATED_PLAN.md` §9 item 4: the canonical (ladder / differential) realization
-- of the full quadratic Navier-Stokes symbol at one fiber.
#print axioms BookProof.NavierStokesFlow.CanonicalVector.comm_ann_cre
#print axioms BookProof.NavierStokesFlow.CanonicalVector.comm_mom_pos
#print axioms BookProof.NavierStokesFlow.CanonicalVector.comm_mom_pos_of_ne
#print axioms BookProof.NavierStokesFlow.CanonicalVector.canFun_eq_ladFun
#print axioms BookProof.NavierStokesFlow.CanonicalVector.canH_eq_velH
#print axioms BookProof.NavierStokesFlow.CanonicalVector.canH_essentiallySelfAdjointOn_core
#print axioms BookProof.NavierStokesFlow.CanonicalVector.canH_not_bounded
#print axioms BookProof.NavierStokesFlow.CanonicalVector.canH_domain_dense
#print axioms BookProof.NavierStokesFlow.CanonicalVector.nsQuadraticH_essentiallySelfAdjointOn_core

-- `CONSOLIDATED_PLAN.md` §9 item 8: essential self-adjointness selects a unique
-- self-adjoint operator (the closure), and the Hashimoto/SIRK shift-invert limit
-- computes with it -- instantiated for the Navier-Stokes fiber generator.
#print axioms BookProof.EsaClosure.clGraph_inner
#print axioms BookProof.EsaClosure.clExt_symmetricOn
#print axioms BookProof.EsaClosure.clExt_extends
#print axioms BookProof.EsaClosure.clExt_selfAdjointCriterion
#print axioms BookProof.EsaClosure.exists_isSelfAdjointExtension_of_esa
#print axioms BookProof.EsaClosure.selfAdjointExtension_eq_adjoint
#print axioms BookProof.EsaClosure.isSelfAdjointExtension_unique_of_esa
#print axioms BookProof.EsaClosure.positiveExtension_eq_closure_of_esa
#print axioms BookProof.EsaClosure.norm_add_I_eq_norm_sub_I
#print axioms BookProof.EsaClosure.exists_cayley_unitary
#print axioms BookProof.EsaClosure.exists_selfAdjointExtension_and_cayley_of_esa
#print axioms BookProof.EsaClosure.hashimoto_multishift_selects_esa
#print axioms BookProof.NavierStokesFlow.NSHashimoto.velCore_symmetricOn
#print axioms BookProof.NavierStokesFlow.NSHashimoto.velCore_esa
#print axioms BookProof.NavierStokesFlow.NSHashimoto.ns_selfAdjoint_extension
#print axioms BookProof.NavierStokesFlow.NSHashimoto.ns_selfAdjoint_extension_unique
#print axioms BookProof.NavierStokesFlow.NSHashimoto.ns_hashimoto_selects
#print axioms BookProof.NavierStokesFlow.NSHashimoto.ns_shiftInvert_selects
#print axioms BookProof.NavierStokesFlow.NSHashimoto.exists_velHilbertBasis

#print axioms BookProof.GaugeFixing.s_c_eq_zero
#print axioms BookProof.GaugeFixing.s_B_eq_zero
#print axioms BookProof.GaugeFixing.s_gaugeField
#print axioms BookProof.GaugeFixing.L_gf_evaluation
#print axioms BookProof.GaugeFixing.L_gf_invariant
#print axioms BookProof.GaugeFixing.int_L_gf_eq_zero
#print axioms BookProof.GaugeFixing.int_L_gf_evaluated
#print axioms BookProof.GaugeFixing.matrixModel_c_ne_zero
#print axioms BookProof.GaugeFixing.matrixModel_B_ne_zero
#print axioms BookProof.GaugeFixing.matrixModel_Psi_ne_zero
#print axioms BookProof.GaugeFixing.matrixModel_s_Psi_ne_zero
#print axioms BookProof.GaugeFixing.matrixModelIntegral_ne_zero

#print axioms BookProof.QuantumGravityDensitized.inv_eq_four_mul_deriv_densY_sq
#print axioms BookProof.QuantumGravityDensitized.kinetic_absorption
#print axioms BookProof.QuantumGravityDensitized.conformal_absorption
#print axioms BookProof.QuantumGravityDensitized.densTetrad_det
#print axioms BookProof.QuantumGravityDensitized.densTetrad_recover
#print axioms BookProof.QuantumGravityDensitized.tendsto_inv_det_atTop
#print axioms BookProof.QuantumGravityDensitized.tendsto_densY_zero
#print axioms BookProof.QuantumGravityDensitized.qgSymbol_eq_metric_form
#print axioms BookProof.QuantumGravityDensitized.qgMetric_det_ne_zero
#print axioms BookProof.QuantumGravityDensitized.qgSymbol_indefinite
#print axioms BookProof.QuantumGravityDensitized.christoffel_eq_zero_of_const
#print axioms BookProof.QuantumGravityDensitized.qgMetric_christoffel_zero
#print axioms BookProof.QuantumGravityDensitized.qgFullSymbol_scaling
#print axioms BookProof.QuantumGravityDensitized.qgModeHamiltonian_essentiallySelfAdjoint
#print axioms BookProof.QuantumGravityDensitized.qgModeHamiltonian_deficiencyTrivialAt
#print axioms BookProof.QuantumGravityDensitized.qgModeHamiltonian_not_bounded
#print axioms BookProof.QuantumGravityDensitized.strichartz_esa_of_finiteSpeed
#print axioms BookProof.QuantumGravityDensitized.strichartz_finiteSpeed_satisfiable
#print axioms BookProof.QuantumGravityDensitized.qg_esa_of_farisLavine
#print axioms BookProof.QuantumGravityDensitized.densitized_hasZeroDeficiencyOn_transfer

#print axioms BookProof.QuantumGravityHalfDensity.qgSrcMeasure_density_eq_halfDensity_sq
#print axioms BookProof.QuantumGravityHalfDensity.measurePreserving_qgSquare
#print axioms BookProof.QuantumGravityHalfDensity.measurePreserving_qgSqrt
#print axioms BookProof.QuantumGravityHalfDensity.halfDensityUnitary_apply
#print axioms BookProof.QuantumGravityHalfDensity.halfDensityUnitary_symm_apply
#print axioms BookProof.QuantumGravityHalfDensity.exists_halfDensity_unitary
#print axioms BookProof.QuantumGravityHalfDensity.qg_halfDensity_transfer

#print axioms BookProof.YangMillsFriedrichs.formNormSq_ge_normSq
#print axioms BookProof.YangMillsFriedrichs.re_formInner_sq_le
#print axioms BookProof.YangMillsFriedrichs.form_closable
#print axioms BookProof.YangMillsFriedrichs.weylOpDom_symmetricOn
#print axioms BookProof.YangMillsFriedrichs.weylOpDom_quadForm
#print axioms BookProof.YangMillsFriedrichs.weylOpDom_quadForm_nonneg
#print axioms BookProof.YangMillsFriedrichs.weylForm_closable
#print axioms BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded
#print axioms BookProof.YangMillsFriedrichs.friedrichs_hypothesis_satisfiable
#print axioms BookProof.YangMillsFriedrichs.weyl_friedrichs_extension
#print axioms BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_antitone
#print axioms BookProof.YangMillsFriedrichs.weylKrylov_bestApprox_tendsto_zero

#print axioms BookProof.YangMillsFriedrichsLimit.symmetricOn_top_of_dense
#print axioms BookProof.YangMillsFriedrichsLimit.quadForm_top_nonneg_of_dense
#print axioms BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded
#print axioms BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_nontrivial_example
#print axioms BookProof.YangMillsFriedrichsLimit.not_mem_span_of_repr_ne_zero
#print axioms BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_proper_domain_example
#print axioms BookProof.YangMillsFriedrichsLimit.krylov_starProjection_tendsto
#print axioms BookProof.YangMillsFriedrichsLimit.sirk_compression_tendsto
#print axioms BookProof.YangMillsFriedrichsLimit.sirk_limit_unique
#print axioms BookProof.YangMillsFriedrichsLimit.sirk_limit_eq_positive_selfadjoint_extension
#print axioms BookProof.YangMillsFriedrichsLimit.weyl_friedrichs_bounded

#print axioms BookProof.HermiteGalerkin.starProjection_tendsto_of_monotone_dense
#print axioms BookProof.HermiteGalerkin.compression_tendsto_of_starProjection_tendsto
#print axioms BookProof.HermiteGalerkin.exists_mem_galerkinSpan
#print axioms BookProof.HermiteGalerkin.galerkinProj_tendsto
#print axioms BookProof.HermiteGalerkin.galerkinCompression_tendsto
#print axioms BookProof.HermiteGalerkin.inner_galerkinCompression
#print axioms BookProof.HermiteGalerkin.ritzInf_antitone
#print axioms BookProof.HermiteGalerkin.ritzInf_tendsto_domainInf
#print axioms BookProof.HermiteGalerkin.ritzInf_extension_le
#print axioms BookProof.HermiteGalerkin.norm_sub_smul_ge
#print axioms BookProof.HermiteGalerkin.norm_resolvent_apply_le
#print axioms BookProof.HermiteGalerkin.resolvent_tendsto_of_strong_tendsto
#print axioms BookProof.HermiteGalerkin.isSelfAdjoint_galerkinCompression
#print axioms BookProof.HermiteGalerkin.galerkinResolvent_tendsto
#print axioms BookProof.HermiteGalerkin.positive_selfadjoint_extension_unique
#print axioms BookProof.HermiteGalerkin.hermiteGalerkin_selects_friedrichs
#print axioms BookProof.HermiteGalerkin.finiteModeRestrict_selects_operator
#print axioms BookProof.HermiteGalerkin.finiteModeDomain_ne_top

#print axioms BookProof.HashimotoShiftInvert.norm_shiftMap_ge
#print axioms BookProof.HashimotoShiftInvert.shiftMap_injective
#print axioms BookProof.HashimotoShiftInvert.closed_of_selfAdjointCriterion
#print axioms BookProof.HashimotoShiftInvert.shiftRange_isClosed
#print axioms BookProof.HashimotoShiftInvert.shiftRange_orthogonal_eq_bot
#print axioms BookProof.HashimotoShiftInvert.shiftMap_surjective
#print axioms BookProof.HashimotoShiftInvert.exists_isShiftInvert
#print axioms BookProof.HashimotoShiftInvert.IsShiftInvert.opNorm_le
#print axioms BookProof.HashimotoShiftInvert.IsShiftInvert.isSelfAdjoint
#print axioms BookProof.HashimotoShiftInvert.IsShiftInvert.inner_nonneg
#print axioms BookProof.HashimotoShiftInvert.IsShiftInvert.dom_eq_range
#print axioms BookProof.HashimotoShiftInvert.shiftInvert_determines
#print axioms BookProof.HashimotoShiftInvert.isShiftInvert_unique
#print axioms BookProof.HashimotoShiftInvert.isShiftInvert_invShiftOperator
#print axioms BookProof.HashimotoShiftInvert.invShiftOperator_isPositiveSelfAdjointExtension
#print axioms BookProof.HashimotoShiftInvert.galerkinCompression_shiftInvert_tendsto
#print axioms BookProof.HashimotoShiftInvert.galerkinResolvent_shiftInvert_tendsto
#print axioms BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_selects_friedrichs
#print axioms BookProof.HashimotoShiftInvert.ell2ExampleMatrix_unbounded
#print axioms BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_unbounded_example

#print axioms BookProof.HashimotoShiftInvert.norm_cshiftMap_ge
#print axioms BookProof.HashimotoShiftInvert.cshiftMap_injective
#print axioms BookProof.HashimotoShiftInvert.cshiftRange_isClosed
#print axioms BookProof.HashimotoShiftInvert.cshiftRange_orthogonal_eq_bot
#print axioms BookProof.HashimotoShiftInvert.cshiftMap_surjective
#print axioms BookProof.HashimotoShiftInvert.exists_isShiftInvertC
#print axioms BookProof.HashimotoShiftInvert.IsShiftInvertC.opNorm_le
#print axioms BookProof.HashimotoShiftInvert.IsShiftInvertC.inner_adjoint
#print axioms BookProof.HashimotoShiftInvert.IsShiftInvertC.dom_eq_range
#print axioms BookProof.HashimotoShiftInvert.shiftInvertC_determines
#print axioms BookProof.HashimotoShiftInvert.isShiftInvertC_unique
#print axioms BookProof.HashimotoShiftInvert.isShiftInvertC_neg_of_isShiftInvert
#print axioms BookProof.HashimotoShiftInvert.shiftInvertC_resolvent_identity
#print axioms BookProof.HashimotoShiftInvert.shiftInvertC_commute
#print axioms BookProof.HashimotoShiftInvert.shiftInvertC_comp_one_sub
#print axioms BookProof.HashimotoShiftInvert.sirkDen_rkVec
#print axioms BookProof.HashimotoShiftInvert.rkCompression_tendsto
#print axioms BookProof.HashimotoShiftInvert.hashimoto_multishift_selects_friedrichs
#print axioms BookProof.HashimotoShiftInvert.ell2Resolvent_isShiftInvertC
#print axioms BookProof.HashimotoShiftInvert.hashimoto_multishift_unbounded_example

#print axioms BookProof.FriedrichsExtension.FormDom.norm_toAmbient_le
#print axioms BookProof.FriedrichsExtension.FormDom.formExt_coe
#print axioms BookProof.FriedrichsExtension.FormDom.inner_coe_eq
#print axioms BookProof.FriedrichsExtension.FormDom.formExt_injective
#print axioms BookProof.FriedrichsExtension.FormDom.formRiesz_spec
#print axioms BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_isSelfAdjoint
#print axioms BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_pos
#print axioms BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_injective
#print axioms BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_shift
#print axioms BookProof.FriedrichsExtension.friedrichs_extension_exists
#print axioms BookProof.FriedrichsExtension.friedrichs_hypothesis_holds
#print axioms BookProof.FriedrichsExtension.weyl_friedrichs_extension_unconditional
#print axioms BookProof.FriedrichsExtension.friedrichs_extension_of_semibounded_below
#print axioms BookProof.FriedrichsExtension.friedrichs_hashimoto_selects
#print axioms BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs
#print axioms BookProof.FriedrichsExtension.unbounded_friedrichs_example

#print axioms BookProof.StrichartzWave.potentialOp_symmetric
#print axioms BookProof.StrichartzWave.potentialOp_deficiencyTrivial
#print axioms BookProof.StrichartzWave.potentialOp_essentiallySelfAdjoint
#print axioms BookProof.StrichartzWave.polynomialPotential_essentiallySelfAdjoint
#print axioms BookProof.StrichartzWave.wave_add_potentialOp_symmetric
#print axioms BookProof.StrichartzWave.multiplierOp_symmetric
#print axioms BookProof.StrichartzWave.multiplierOp_deficiencyTrivial
#print axioms BookProof.StrichartzWave.multiplierOp_essentiallySelfAdjoint
#print axioms BookProof.StrichartzWave.constCoeffOp_eq_multiplierOp
#print axioms BookProof.StrichartzWave.polyharmonic_multiplier_essentiallySelfAdjoint
#print axioms BookProof.StrichartzWave.opL2_potentialOp_eq_mulL2
#print axioms BookProof.StrichartzWave.wave_add_boundedPotentialOp_essentiallySelfAdjoint
#print axioms BookProof.StrichartzWave.wave_add_truncatedPotential_essentiallySelfAdjoint

#print axioms BookProof.HarmonicOscillator.hermiteC_oscillator
#print axioms BookProof.HarmonicOscillator.harmonicOscOp_hermiteLp
#print axioms BookProof.HarmonicOscillator.harmonicOscOp_apply_eq_differential
#print axioms BookProof.HarmonicOscillator.harmonicOsc_symmetric
#print axioms BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint
#print axioms BookProof.HarmonicOscillator.harmonicOsc_not_bounded

-- `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F: the field-space (Gauss–polynomial /
-- product Hermite) realization of the Weyl-gauge Yang–Mills Hamiltonian.
#print axioms BookProof.HermiteProductCore.pgMap_injective
#print axioms BookProof.HermiteProductCore.polyGaussCore_dense
#print axioms BookProof.HermiteProductCore.gaussInt_pderiv
#print axioms BookProof.HermiteProductCore.span_range_coreBasis
#print axioms BookProof.HermiteProductCore.polyGaussCore_eq_hermiteSpan
#print axioms BookProof.YangMillsHermite.momOp_polySym
#print axioms BookProof.YangMillsHermite.commutator_coord_mom
#print axioms BookProof.YangMillsHermite.weylProd_polySym
#print axioms BookProof.YangMillsHermite.realCoeff_magPoly
#print axioms BookProof.YangMillsHermite.ymHamiltonian_symmetricOn
#print axioms BookProof.YangMillsHermite.ymHamiltonian_quadForm_nonneg
#print axioms BookProof.YangMillsHermite.ym_hermite_friedrichs_extension
#print axioms BookProof.YangMillsHermite.ym_hermite_hashimoto_selects

-- `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F.11: the second quantization of the
-- field-space Yang–Mills Hamiltonian on the finite-occupation states over the core.
#print axioms BookProof.FockSecondQuantization.ccr_annA_creA
#print axioms BookProof.FockSecondQuantization.inner_creA_left
#print axioms BookProof.FockSecondQuantization.dGamma_one_particle
#print axioms BookProof.FockSecondQuantization.dGammaOp_symmetricOn
#print axioms BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg
#print axioms BookProof.FockSecondQuantization.dGamma_friedrichs_extension
#print axioms BookProof.FockSecondQuantization.secondQuantization_friedrichs
#print axioms BookProof.FockSecondQuantization.ym_fock_friedrichs_extension
#print axioms BookProof.FockSecondQuantization.finiteModeDomain_fockBasisN
#print axioms BookProof.FockSecondQuantization.dGamma_hashimoto_selects
#print axioms BookProof.FockSecondQuantization.secondQuantization_hashimoto_selects
#print axioms BookProof.FockSecondQuantization.ym_fock_hashimoto_selects

-- `CONSOLIDATED_PLAN.md` §9 item 9: the Lagrangian (parcel) route.  Kato–Rellich
-- control of the first-order drift by the positive second-order part obtained
-- from the change of variables, and the Hashimoto/SIRK selection on the
-- Lagrangian side.
#print axioms BookProof.KatoRellich.norm_le_of_relBound
#print axioms BookProof.KatoRellich.dense_range_add_relBounded
#print axioms BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.norm_P_sq_le
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.norm_P_le
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_relBound
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_essentiallySelfAdjointOn
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_hasZeroDeficiencyOn
#print axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.hasZeroDeficiencyOn_of_lagrangian_katoRellich
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension
#print axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension_unique
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_hashimoto_selects
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_shiftInvert_selects
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_drift_not_bounded
#print axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_hFull_essentiallySelfAdjointOn
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR_hashimoto_selects
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.norm_sum_P_le
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.drift_dominated_of_drive_eq_P
#print axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_hasZeroDeficiencyOn_of_drive_eq_P
#print axioms BookProof.NavierStokesFlow.LagrangianKatoRellich.jacobiLag_secondOrder_eq_zero
#print axioms
  BookProof.NavierStokesFlow.LagrangianKatoRellich.jacobiLag_drift_not_relativelyBounded

-- from the Stone bridge and the concrete flows (2026-08-20i): the packaging of a
-- selected self-adjoint extension into the bundled UnboundedSelfAdjoint
-- structure, and the complete unitary flows of the Eulerian NS, Lagrangian NS
-- and QYM Hamiltonians.
#print axioms BookProof.StoneBridge.dense_domain_of_isSelfAdjointExtension
#print axioms BookProof.StoneBridge.isSelfAdjointOn_of_isSelfAdjointExtension
#print axioms BookProof.StoneBridge.isStoneFlow_stoneU
#print axioms BookProof.StoneBridge.exists_stone_flow_of_selfAdjointExtension
#print axioms BookProof.StoneBridge.exists_stone_flow_of_positive
#print axioms BookProof.StoneBridge.exists_stone_flow_of_esa
#print axioms BookProof.StoneFlows.ns_stone_flow
#print axioms BookProof.StoneFlows.lagrangian_stone_flow
#print axioms BookProof.StoneFlows.diagKR_stone_flow
#print axioms BookProof.StoneFlows.ym_fock_stone_flow

end BookProof.ChapterRoadmapAudit
