import BookProof.ChapterTensorPermutation
import BookProof.ChapterPermutationSectorEsa

/-!
# Axiom audit for the `n`-particle symmetrization wave

Every result of `BookProof/ChapterTensorPermutation.lean` and
`BookProof/ChapterPermutationSectorEsa.lean` should report only the three standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- pure tensors
#print axioms BookProof.TensorPerm.purePow_succ
#print axioms BookProof.TensorPerm.span_purePow_eq_top
#print axioms BookProof.TensorPerm.linearMap_ext_purePow
#print axioms BookProof.TensorPerm.inner_purePow
#print axioms BookProof.TensorPerm.purePow_ne_zero

-- the two elementary isometries and the recursion
#print axioms BookProof.TensorPerm.swapAux_tmul
#print axioms BookProof.TensorPerm.swapFirst_tmul
#print axioms BookProof.TensorPerm.liftTail_tmul
#print axioms BookProof.TensorPerm.swap0_succ
#print axioms BookProof.TensorPerm.permOp_succ

-- the combinatorics
#print axioms BookProof.TensorPerm.permSucc_zero
#print axioms BookProof.TensorPerm.permSucc_succ
#print axioms BookProof.TensorPerm.permSucc_swap_conj
#print axioms BookProof.TensorPerm.swap_decomposeFin

-- the action on pure tensors and the group law
#print axioms BookProof.TensorPerm.liftTail_purePow
#print axioms BookProof.TensorPerm.swapFirst_purePow
#print axioms BookProof.TensorPerm.swap0_purePow
#print axioms BookProof.TensorPerm.permOp_purePow
#print axioms BookProof.TensorPerm.permOp_one
#print axioms BookProof.TensorPerm.permOp_mul
#print axioms BookProof.TensorPerm.permOp_inner
#print axioms BookProof.TensorPerm.permRep_act
#print axioms BookProof.TensorPerm.signRep_act

-- the three compatibilities
#print axioms BookProof.PermSector.tensor_triple_induction
#print axioms BookProof.PermSector.good_refl
#print axioms BookProof.PermSector.good_trans
#print axioms BookProof.PermSector.good_liftTail
#print axioms BookProof.PermSector.good_swapFirst
#print axioms BookProof.PermSector.good_swap0
#print axioms BookProof.PermSector.good_permOp

-- the consequences for the sector operator
#print axioms BookProof.PermSector.inclPow_permOp
#print axioms BookProof.PermSector.derPow_permOp
#print axioms BookProof.PermSector.corePow_permOp
#print axioms BookProof.PermSector.permOp_mem_sectorDom
#print axioms BookProof.PermSector.permOp_mem_sectorCore
#print axioms BookProof.PermSector.sectorOp_permOp
#print axioms BookProof.PermSector.restrictOp_sectorOp_permOp

-- the two sectors
#print axioms BookProof.PermSector.isReducingProjection_bosonicProj
#print axioms BookProof.PermSector.isReducingProjection_fermionicProj
#print axioms BookProof.PermSector.mem_bosonicSector_iff
#print axioms BookProof.PermSector.mem_fermionicSector_iff

-- domain, core and commutation for the two representations
#print axioms BookProof.PermSector.permRep_mem_sectorDom
#print axioms BookProof.PermSector.signRep_mem_sectorDom
#print axioms BookProof.PermSector.permRep_mem_sectorCore
#print axioms BookProof.PermSector.signRep_mem_sectorCore
#print axioms BookProof.PermSector.permRep_commutes_sectorDom
#print axioms BookProof.PermSector.signRep_commutes_sectorDom
#print axioms BookProof.PermSector.permRep_commutes_sectorCore
#print axioms BookProof.PermSector.signRep_commutes_sectorCore

-- the headline statements
#print axioms BookProof.PermSector.essentiallySelfAdjointOn_bosonic
#print axioms BookProof.PermSector.essentiallySelfAdjointOn_fermionic
#print axioms BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core
#print axioms BookProof.PermSector.essentiallySelfAdjointOn_fermionic_core
#print axioms BookProof.PermSector.symmetricOn_bosonic
#print axioms BookProof.PermSector.symmetricOn_fermionic

-- pure tensors inside the domain and the core, and non-vacuity
#print axioms BookProof.PermSector.inclPow_purePow
#print axioms BookProof.PermSector.purePow_mem_corePow
#print axioms BookProof.PermSector.purePow_mem_sectorCore
#print axioms BookProof.PermSector.exists_ne_zero_bosonic
#print axioms BookProof.PermSector.exists_ne_zero_fermionic

-- consistency with the two-particle chapter
#print axioms BookProof.PermSector.permOp_two_eq_swapH
