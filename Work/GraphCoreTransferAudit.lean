import BookProof.ChapterGraphCoreTransfer
import BookProof.ChapterTensorGraphCore
import BookProof.ChapterSecondQuantizationCoreEsa
import BookProof.ChapterScalarDGammaEsa
import BookProof.ChapterTensorOperatorBound
import BookProof.ChapterBoundedDGammaEsa
import BookProof.ChapterEsaPairDGamma
import BookProof.ChapterDiagonalDGammaEsa
import BookProof.ChapterFlowDGammaEsa

/-!
# Axiom audit for the core transfer route to second quantization

Every result of `BookProof/ChapterGraphCoreTransfer.lean`,
`BookProof/ChapterTensorGraphCore.lean` and
`BookProof/ChapterSecondQuantizationCoreEsa.lean` should report only the three standard
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

open BookProof.GraphCore BookProof.TensorCore BookProof.SecondQuantizationCore

-- the core transfer principle
#print axioms BookProof.GraphCore.deficiencyTrivialAt_of_graphCore
#print axioms BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore
#print axioms BookProof.GraphCore.IsGraphCore.refl
#print axioms BookProof.GraphCore.IsGraphCore.trans
#print axioms BookProof.GraphCore.symmetricOn_restrictOp
#print axioms BookProof.GraphCore.pushOp_apply
#print axioms BookProof.GraphCore.symmetricOn_pushOp
#print axioms BookProof.GraphCore.isGraphCore_pushOp

-- the multilinear core estimate
#print axioms BookProof.TensorCore.norm_tmul_sub_le
#print axioms BookProof.TensorCore.graphPow_tmul_mem_closure
#print axioms BookProof.TensorCore.graphPow_range_le_closure
#print axioms BookProof.TensorCore.exists_core_approx
#print axioms BookProof.TensorCore.sectorOp_apply
#print axioms BookProof.TensorCore.isGraphCore_sectorCore
#print axioms BookProof.TensorCore.essentiallySelfAdjointOn_sectorCore
#print axioms BookProof.TensorCore.derPow_symm
#print axioms BookProof.TensorCore.symmetricOn_sectorOp
#print axioms BookProof.TensorCore.exists_ne_zero_mem_sectorCore_one

-- the assembly
#print axioms BookProof.SecondQuantizationCore.isGraphCore_fockSectorCore
#print axioms BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore
#print axioms BookProof.SecondQuantizationCore.symmetricOn_fockSectorOp
#print axioms BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp
#print axioms BookProof.SecondQuantizationCore.dGamma_essentiallySelfAdjointOn_fockCore
#print axioms BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain

-- the bounded criterion and the unconditional scalar instance
#print axioms BookProof.GraphCore.deficiencyTrivialAt_of_bounded_dense
#print axioms BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense
#print axioms BookProof.ScalarDGamma.symmetricOn_scalarOp
#print axioms BookProof.ScalarDGamma.isGraphCore_scalarOp
#print axioms BookProof.ScalarDGamma.derPow_scalar
#print axioms BookProof.ScalarDGamma.sectorDom_top
#print axioms BookProof.ScalarDGamma.dense_fockSectorDom
#print axioms BookProof.ScalarDGamma.norm_fockSectorOp_scalar_le
#print axioms BookProof.ScalarDGamma.essentiallySelfAdjointOn_fockSectorDom_scalar
#print axioms BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore

-- the tensor operator bound and the bounded (no positivity) instance
#print axioms BookProof.TensorOpBound.norm_sum_tmul_orthonormal
#print axioms BookProof.TensorOpBound.exists_orthonormal_repr
#print axioms BookProof.TensorOpBound.norm_map_left_le
#print axioms BookProof.TensorOpBound.norm_map_right_le
#print axioms BookProof.TensorOpBound.norm_map_le
#print axioms BookProof.BoundedDGamma.norm_derPow_le
#print axioms BookProof.BoundedDGamma.norm_sectorOp_le
#print axioms BookProof.BoundedDGamma.norm_fockSectorOp_le
#print axioms BookProof.BoundedDGamma.isGraphCore_of_bounded
#print axioms BookProof.BoundedDGamma.essentiallySelfAdjointOn_fockSectorDom_bounded
#print axioms BookProof.BoundedDGamma.dGamma_bounded_essentiallySelfAdjointOn_fockCore
#print axioms BookProof.BoundedDGamma.dGamma_neg_id_essentiallySelfAdjointOn_fockCore

-- the packaged form
#print axioms BookProof.EsaPair.ESAPair.norm_sub_smul_sq
#print axioms BookProof.EsaPair.ESAPair.symmetricOn_toOp
#print axioms BookProof.EsaPair.ESAPair.dGamma_essentiallySelfAdjoint
#print axioms BookProof.EsaPair.ESAPair.dGamma_symmetricOn
#print axioms BookProof.EsaPair.ESAPair.exists_ne_zero_mem_domain
#print axioms BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded

-- the unbounded (pure point spectrum) instance: the sector hypothesis discharged without
-- any boundedness assumption on the one-particle operator
#print axioms BookProof.DiagonalDGamma.deficiencyTrivialAt_of_dense_eigenvectors
#print axioms BookProof.DiagonalDGamma.essentiallySelfAdjointOn_of_dense_eigenvectors
#print axioms BookProof.DiagonalDGamma.derPow_eigTensor
#print axioms BookProof.DiagonalDGamma.dense_eigSpan
#print axioms BookProof.DiagonalDGamma.dense_span_fockEigVec
#print axioms BookProof.DiagonalDGamma.essentiallySelfAdjointOn_fockSectorDom_diagonal
#print axioms BookProof.DiagonalDGamma.dGamma_diagonal_essentiallySelfAdjointOn_fockCore
#print axioms BookProof.DiagonalDGamma.symmetricOn_diagOp
#print axioms BookProof.DiagonalDGamma.essentiallySelfAdjointOn_diagOp
#print axioms BookProof.DiagonalDGamma.not_bounded_diagOp
#print axioms BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore
#print axioms BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore_self

-- the fully general case: an arbitrary self-adjoint one-particle operator, via the
-- invariant-domain (Nelson) argument run on the tensor sectors
#print axioms BookProof.FlowDGamma.deficiencyTrivialAt_of_orbits
#print axioms BookProof.FlowDGamma.essentiallySelfAdjointOn_of_orbits
#print axioms BookProof.FlowDGamma.hasDerivAt_tmul
#print axioms BookProof.FlowDGamma.OneParticleFlow.norm_tpow
#print axioms BookProof.FlowDGamma.OneParticleFlow.hasDerivAt_tpow
#print axioms BookProof.FlowDGamma.OneParticleFlow.hasDerivAt_fockOrbit
#print axioms BookProof.FlowDGamma.OneParticleFlow.essentiallySelfAdjointOn_fockSectorDom_flow
#print axioms BookProof.FlowDGamma.OneParticleFlow.dGamma_flow_essentiallySelfAdjointOn_fockCore
#print axioms BookProof.FlowDGamma.essentiallySelfAdjointOn_fockSectorDom_selfAdjoint
#print axioms BookProof.FlowDGamma.dGamma_selfAdjoint_essentiallySelfAdjointOn_fockCore
#print axioms BookProof.FlowDGamma.dGamma_position_essentiallySelfAdjointOn_fockCore
#print axioms BookProof.FlowDGamma.position_not_bounded
#print axioms BookProof.FlowDGamma.esaPairOfSelfAdjoint
