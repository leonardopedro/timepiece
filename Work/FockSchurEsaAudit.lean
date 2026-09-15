import BookProof.ChapterFockSchurEsa

/-!
Axiom audit for the wave that adds the **Schur gate** for second quantization
(`CONSOLIDATED_PLAN.md`): the number bound `‖dΓ(A)u‖ ≤ K‖𝒩u‖` and essential
self-adjointness of `dΓ(A)` on the finite-occupation core, together with the
core-bounds instrument it runs on.  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- The core-bounds instrument.
#print axioms BookProof.CoreBounds.tendsto_trunc
#print axioms BookProof.CoreBounds.tendsto_diag_trunc
#print axioms BookProof.CoreBounds.coreExt_core
#print axioms BookProof.CoreBounds.norm_coreExt_le
#print axioms BookProof.CoreBounds.coreExt_symmetricOn
#print axioms BookProof.CoreBounds.coreExt_commForm_le
#print axioms BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds
#print axioms BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm

-- Particle number, sectors and number conservation.
#print axioms BookProof.FockSchur.ndeg_up
#print axioms BookProof.FockSchur.ndeg_dn
#print axioms BookProof.FockSchur.annA_inSector
#print axioms BookProof.FockSchur.creA_inSector
#print axioms BookProof.FockSchur.dGamma_inSector

-- The number bound.
#print axioms BookProof.FockSchur.normSq_annA
#print axioms BookProof.FockSchur.sum_normSq_annA
#print axioms BookProof.FockSchur.schur_test
#print axioms BookProof.FockSchur.norm_dGamma_le_of_sector
#print axioms BookProof.FockSchur.normSq_sum_of_sectors
#print axioms BookProof.FockSchur.norm_dGamma_le

-- Essential self-adjointness on the finite-occupation core.
#print axioms BookProof.FockSchur.dGammaOp_coreRelBound
#print axioms BookProof.FockSchur.dGammaOp_commForm_zero
#print axioms BookProof.FockSchur.dGamma_essentiallySelfAdjointOn_core

-- Non-vacuity: the nearest-neighbour hopping matrix.
#print axioms BookProof.FockSchur.isHermCol_hopCol
#print axioms BookProof.FockSchur.schurBound_hopCol
#print axioms BookProof.FockSchur.hopCol_not_summable
#print axioms BookProof.FockSchur.hop_essentiallySelfAdjointOn_core

-- The unique self-adjoint realization and its unitary group.
#print axioms BookProof.FockSchur.dGamma_stone_flow
#print axioms BookProof.FockSchur.dGamma_positiveExtension_eq_closure
#print axioms BookProof.FockSchur.hop_stone_flow
