import BookProof.Toolbox.ChapterTensorSumEsa
import BookProof.Toolbox.ChapterTensorSumChain
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for `BookProof/Toolbox/ChapterTensorSumEsa.lean`: every headline result of the two-factor
tensor sum `A ⊗ 1 + 1 ⊗ B`.  Each line must report only `propext`, `Classical.choice`,
`Quot.sound`.
-/

#audit_axioms BookProof.TensorSumEsa.sumPoly_symm
#audit_axioms BookProof.TensorSumEsa.symmetricOn_pairOp
#audit_axioms BookProof.TensorSumEsa.symmetricOn_cpairOp
#audit_axioms BookProof.TensorSumEsa.dense_pairDom
#audit_axioms BookProof.TensorSumEsa.dense_cpairDom
#audit_axioms BookProof.TensorSumEsa.norm_pflow
#audit_axioms BookProof.TensorSumEsa.hasDerivAt_pflow
#audit_axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairDom_flow
#audit_axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairDom_selfAdjoint
#audit_axioms BookProof.TensorSumEsa.exists_pair_core_approx
#audit_axioms BookProof.TensorSumEsa.isGraphCore_pairCore
#audit_axioms BookProof.TensorSumEsa.isGraphCore_cpairCore
#audit_axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairCore
#audit_axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairCore_selfAdjoint
#audit_axioms BookProof.TensorSumEsa.exists_pair_of_mem_pairCorePoly
#audit_axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairDom_esa
#audit_axioms BookProof.TensorSumEsa.tensorSum_stone_flow
#audit_axioms BookProof.TensorSumEsa.tensorSum_stone_flow_esa
#audit_axioms BookProof.TensorSumEsa.positionCube_essentiallySelfAdjoint
#audit_axioms BookProof.TensorSumEsa.positionCube_first_not_bounded

-- The `n`-factor chain (`BookProof/Toolbox/ChapterTensorSumChain.lean`).
#audit_axioms BookProof.TensorSumChain.pair_op_tmul
#audit_axioms BookProof.TensorSumChain.chain_dense
#audit_axioms BookProof.TensorSumChain.chain_symmetric
#audit_axioms BookProof.TensorSumChain.chain_esa
#audit_axioms BookProof.TensorSumChain.chain_stone_flow
#audit_axioms BookProof.TensorSumChain.positionChain_esa
#audit_axioms BookProof.TensorSumChain.posEsaOp_not_bounded
