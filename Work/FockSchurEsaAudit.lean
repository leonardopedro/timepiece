import BookProof.Toolbox.ChapterFockSchurEsa
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the wave that adds the **Schur gate** for second quantization
(`CONSOLIDATED_PLAN.md`): the number bound `‖dΓ(A)u‖ ≤ K‖𝒩u‖` and essential
self-adjointness of `dΓ(A)` on the finite-occupation core, together with the
core-bounds instrument it runs on.  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- The core-bounds instrument.
#audit_axioms BookProof.CoreBounds.tendsto_trunc
#audit_axioms BookProof.CoreBounds.tendsto_diag_trunc
#audit_axioms BookProof.CoreBounds.coreExt_core
#audit_axioms BookProof.CoreBounds.norm_coreExt_le
#audit_axioms BookProof.CoreBounds.coreExt_symmetricOn
#audit_axioms BookProof.CoreBounds.coreExt_commForm_le
#audit_axioms BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds
#audit_axioms BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm

-- Particle number, sectors and number conservation.
#audit_axioms BookProof.FockSchur.ndeg_up
#audit_axioms BookProof.FockSchur.ndeg_dn
#audit_axioms BookProof.FockSchur.annA_inSector
#audit_axioms BookProof.FockSchur.creA_inSector
#audit_axioms BookProof.FockSchur.dGamma_inSector

-- The number bound.
#audit_axioms BookProof.FockSchur.normSq_annA
#audit_axioms BookProof.FockSchur.sum_normSq_annA
#audit_axioms BookProof.FockSchur.schur_test
#audit_axioms BookProof.FockSchur.norm_dGamma_le_of_sector
#audit_axioms BookProof.FockSchur.normSq_sum_of_sectors
#audit_axioms BookProof.FockSchur.norm_dGamma_le

-- Essential self-adjointness on the finite-occupation core.
#audit_axioms BookProof.FockSchur.dGammaOp_coreRelBound
#audit_axioms BookProof.FockSchur.dGammaOp_commForm_zero
#audit_axioms BookProof.FockSchur.dGamma_essentiallySelfAdjointOn_core

-- Non-vacuity: the nearest-neighbour hopping matrix.
#audit_axioms BookProof.FockSchur.isHermCol_hopCol
#audit_axioms BookProof.FockSchur.schurBound_hopCol
#audit_axioms BookProof.FockSchur.hopCol_not_summable
#audit_axioms BookProof.FockSchur.hop_essentiallySelfAdjointOn_core

-- The unique self-adjoint realization and its unitary group.
#audit_axioms BookProof.FockSchur.dGamma_stone_flow
#audit_axioms BookProof.FockSchur.dGamma_positiveExtension_eq_closure
#audit_axioms BookProof.FockSchur.hop_stone_flow
