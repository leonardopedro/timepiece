import BookProof.Toolbox.ChapterTensorPermutation
import BookProof.ChapterPermutationSectorEsa
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for the `n`-particle symmetrization wave

Every result of `BookProof/Toolbox/ChapterTensorPermutation.lean` and
`BookProof/Toolbox/ChapterPermutationSectorEsa.lean` should report only the three standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- pure tensors
#audit_axioms BookProof.TensorPerm.purePow_succ
#audit_axioms BookProof.TensorPerm.span_purePow_eq_top
#audit_axioms BookProof.TensorPerm.linearMap_ext_purePow
#audit_axioms BookProof.TensorPerm.inner_purePow
#audit_axioms BookProof.TensorPerm.purePow_ne_zero

-- the two elementary isometries and the recursion
#audit_axioms BookProof.TensorPerm.swapAux_tmul
#audit_axioms BookProof.TensorPerm.swapFirst_tmul
#audit_axioms BookProof.TensorPerm.liftTail_tmul
#audit_axioms BookProof.TensorPerm.swap0_succ
#audit_axioms BookProof.TensorPerm.permOp_succ

-- the combinatorics
#audit_axioms BookProof.TensorPerm.permSucc_zero
#audit_axioms BookProof.TensorPerm.permSucc_succ
#audit_axioms BookProof.TensorPerm.permSucc_swap_conj
#audit_axioms BookProof.TensorPerm.swap_decomposeFin

-- the action on pure tensors and the group law
#audit_axioms BookProof.TensorPerm.liftTail_purePow
#audit_axioms BookProof.TensorPerm.swapFirst_purePow
#audit_axioms BookProof.TensorPerm.swap0_purePow
#audit_axioms BookProof.TensorPerm.permOp_purePow
#audit_axioms BookProof.TensorPerm.permOp_one
#audit_axioms BookProof.TensorPerm.permOp_mul
#audit_axioms BookProof.TensorPerm.permOp_inner
#audit_axioms BookProof.TensorPerm.permRep_act
#audit_axioms BookProof.TensorPerm.signRep_act

-- the three compatibilities
#audit_axioms BookProof.PermSector.tensor_triple_induction
#audit_axioms BookProof.PermSector.good_refl
#audit_axioms BookProof.PermSector.good_trans
#audit_axioms BookProof.PermSector.good_liftTail
#audit_axioms BookProof.PermSector.good_swapFirst
#audit_axioms BookProof.PermSector.good_swap0
#audit_axioms BookProof.PermSector.good_permOp

-- the consequences for the sector operator
#audit_axioms BookProof.PermSector.inclPow_permOp
#audit_axioms BookProof.PermSector.derPow_permOp
#audit_axioms BookProof.PermSector.corePow_permOp
#audit_axioms BookProof.PermSector.permOp_mem_sectorDom
#audit_axioms BookProof.PermSector.permOp_mem_sectorCore
#audit_axioms BookProof.PermSector.sectorOp_permOp
#audit_axioms BookProof.PermSector.restrictOp_sectorOp_permOp

-- the two sectors
#audit_axioms BookProof.PermSector.isReducingProjection_bosonicProj
#audit_axioms BookProof.PermSector.isReducingProjection_fermionicProj
#audit_axioms BookProof.PermSector.mem_bosonicSector_iff
#audit_axioms BookProof.PermSector.mem_fermionicSector_iff

-- domain, core and commutation for the two representations
#audit_axioms BookProof.PermSector.permRep_mem_sectorDom
#audit_axioms BookProof.PermSector.signRep_mem_sectorDom
#audit_axioms BookProof.PermSector.permRep_mem_sectorCore
#audit_axioms BookProof.PermSector.signRep_mem_sectorCore
#audit_axioms BookProof.PermSector.permRep_commutes_sectorDom
#audit_axioms BookProof.PermSector.signRep_commutes_sectorDom
#audit_axioms BookProof.PermSector.permRep_commutes_sectorCore
#audit_axioms BookProof.PermSector.signRep_commutes_sectorCore

-- the headline statements
#audit_axioms BookProof.PermSector.essentiallySelfAdjointOn_bosonic
#audit_axioms BookProof.PermSector.essentiallySelfAdjointOn_fermionic
#audit_axioms BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core
#audit_axioms BookProof.PermSector.essentiallySelfAdjointOn_fermionic_core
#audit_axioms BookProof.PermSector.symmetricOn_bosonic
#audit_axioms BookProof.PermSector.symmetricOn_fermionic

-- pure tensors inside the domain and the core, and non-vacuity
#audit_axioms BookProof.PermSector.inclPow_purePow
#audit_axioms BookProof.PermSector.purePow_mem_corePow
#audit_axioms BookProof.PermSector.purePow_mem_sectorCore
#audit_axioms BookProof.PermSector.exists_ne_zero_bosonic
#audit_axioms BookProof.PermSector.exists_ne_zero_fermionic

-- consistency with the two-particle chapter
#audit_axioms BookProof.PermSector.permOp_two_eq_swapH
