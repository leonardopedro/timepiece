import BookProof.ChapterTensorSumEsa
import BookProof.ChapterTensorSumChain

/-!
Axiom audit for `BookProof/ChapterTensorSumEsa.lean`: every headline result of the two-factor
tensor sum `A ⊗ 1 + 1 ⊗ B`.  Each line must report only `propext`, `Classical.choice`,
`Quot.sound`.
-/

#print axioms BookProof.TensorSumEsa.sumPoly_symm
#print axioms BookProof.TensorSumEsa.symmetricOn_pairOp
#print axioms BookProof.TensorSumEsa.symmetricOn_cpairOp
#print axioms BookProof.TensorSumEsa.dense_pairDom
#print axioms BookProof.TensorSumEsa.dense_cpairDom
#print axioms BookProof.TensorSumEsa.norm_pflow
#print axioms BookProof.TensorSumEsa.hasDerivAt_pflow
#print axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairDom_flow
#print axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairDom_selfAdjoint
#print axioms BookProof.TensorSumEsa.exists_pair_core_approx
#print axioms BookProof.TensorSumEsa.isGraphCore_pairCore
#print axioms BookProof.TensorSumEsa.isGraphCore_cpairCore
#print axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairCore
#print axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairCore_selfAdjoint
#print axioms BookProof.TensorSumEsa.exists_pair_of_mem_pairCorePoly
#print axioms BookProof.TensorSumEsa.essentiallySelfAdjointOn_cpairDom_esa
#print axioms BookProof.TensorSumEsa.tensorSum_stone_flow
#print axioms BookProof.TensorSumEsa.tensorSum_stone_flow_esa
#print axioms BookProof.TensorSumEsa.positionCube_essentiallySelfAdjoint
#print axioms BookProof.TensorSumEsa.positionCube_first_not_bounded

-- The `n`-factor chain (`BookProof/ChapterTensorSumChain.lean`).
#print axioms BookProof.TensorSumChain.pair_op_tmul
#print axioms BookProof.TensorSumChain.chain_dense
#print axioms BookProof.TensorSumChain.chain_symmetric
#print axioms BookProof.TensorSumChain.chain_esa
#print axioms BookProof.TensorSumChain.chain_stone_flow
#print axioms BookProof.TensorSumChain.positionChain_esa
#print axioms BookProof.TensorSumChain.posEsaOp_not_bounded
