import BookProof.Qym.ChapterYangMillsBandBounds
import BookProof.Qed.ChapterQedAbelianConsolidation
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the 2026-09-07 wave: the **band calculus of arbitrary order** and the
Hermite matrix data (sparsity, band radius, entry bounds) of the **full non-abelian**
gauge-fixed Yang–Mills Hamiltonian; the **Faddeev–Popov ghost sector** of the gauge-fixed
Yang–Mills Hamiltonian and its essential self-adjointness in the abelian (QED) case; and the
abelian/QED consolidation index.  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- The band calculus of arbitrary order.
#audit_axioms BookProof.HermiteBandHigher.gpow_mono
#audit_axioms BookProof.HermiteBandHigher.gpow_add
#audit_axioms BookProof.HermiteBandHigher.Band.monoR
#audit_axioms BookProof.HermiteBandHigher.Band.monoG
#audit_axioms BookProof.HermiteBandHigher.Band.compGen
#audit_axioms BookProof.HermiteBandHigher.IsBandR.comp
#audit_axioms BookProof.HermiteBandHigher.IsBandR.add
#audit_axioms BookProof.HermiteBandHigher.IsBandR.sum
#audit_axioms BookProof.HermiteBandHigher.IsBandDeg.comp
#audit_axioms BookProof.HermiteBandHigher.isBandR1_mulXPoly
#audit_axioms BookProof.HermiteBandHigher.isBandR1_momPoly
#audit_axioms BookProof.HermiteBandHigher.isBandR_one_op
#audit_axioms BookProof.HermiteBandHigher.isBandDeg_mulOp_multiset
#audit_axioms BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial
#audit_axioms BookProof.HermiteBandHigher.isBandDeg_mulOp

-- The Yang–Mills matrix data.
#audit_axioms BookProof.YangMillsBandBounds.ymHermOp_eq
#audit_axioms BookProof.YangMillsBandBounds.ymHermCol_eq
#audit_axioms BookProof.YangMillsBandBounds.isHermCol_ymHermCol
#audit_axioms BookProof.YangMillsBandBounds.isBandR2_magMulOp
#audit_axioms BookProof.YangMillsBandBounds.isBandR4_ymPoly
#audit_axioms BookProof.YangMillsBandBounds.gradedBand_of_isBandR
#audit_axioms BookProof.YangMillsBandBounds.ym_hermCol_band_bounds

-- The ghost sector.
#audit_axioms BookProof.YangMillsGhost.ghostCore_dense
#audit_axioms BookProof.YangMillsGhost.fibreHam_symmetricOn
#audit_axioms BookProof.YangMillsGhost.ymGhostHam_symmetricOn
#audit_axioms BookProof.YangMillsGhost.ymGhostHam_preserves_ghostNumber
#audit_axioms BookProof.YangMillsGhost.ymGhostHam_vacuum_fibre
#audit_axioms BookProof.YangMillsGhost.fibreHam_abelian_esa
#audit_axioms BookProof.YangMillsGhost.ymGhostHam_essentiallySelfAdjointOn_core
#audit_axioms BookProof.YangMillsGhost.ymGhostHam_stone_flow
#audit_axioms BookProof.YangMillsGhost.ymGhostHam_add_bounded_coupling_esa

-- The abelian/QED index.
#audit_axioms BookProof.QedConsolidation.qed_one_particle_esa
#audit_axioms BookProof.QedConsolidation.qed_fock_esa
#audit_axioms BookProof.QedConsolidation.qed_fock_exists_selfAdjoint_realization
#audit_axioms BookProof.QedConsolidation.qed_fock_time_translation
#audit_axioms BookProof.QedConsolidation.qed_no_one_particle_form_gap
#audit_axioms BookProof.QedConsolidation.qed_photon_no_one_particle_gap
#audit_axioms BookProof.QedConsolidation.qed_ghost_esa
#audit_axioms BookProof.QedConsolidation.qed_ghost_vacuum_decouples
