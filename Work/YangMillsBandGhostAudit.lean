import BookProof.ChapterYangMillsBandBounds
import BookProof.ChapterQedAbelianConsolidation

/-!
Axiom audit for the 2026-09-07 wave: the **band calculus of arbitrary order** and the
Hermite matrix data (sparsity, band radius, entry bounds) of the **full non-abelian**
gauge-fixed Yang–Mills Hamiltonian; the **Faddeev–Popov ghost sector** of the gauge-fixed
Yang–Mills Hamiltonian and its essential self-adjointness in the abelian (QED) case; and the
abelian/QED consolidation index.  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- The band calculus of arbitrary order.
#print axioms BookProof.HermiteBandHigher.gpow_mono
#print axioms BookProof.HermiteBandHigher.gpow_add
#print axioms BookProof.HermiteBandHigher.Band.monoR
#print axioms BookProof.HermiteBandHigher.Band.monoG
#print axioms BookProof.HermiteBandHigher.Band.compGen
#print axioms BookProof.HermiteBandHigher.IsBandR.comp
#print axioms BookProof.HermiteBandHigher.IsBandR.add
#print axioms BookProof.HermiteBandHigher.IsBandR.sum
#print axioms BookProof.HermiteBandHigher.IsBandDeg.comp
#print axioms BookProof.HermiteBandHigher.isBandR1_mulXPoly
#print axioms BookProof.HermiteBandHigher.isBandR1_momPoly
#print axioms BookProof.HermiteBandHigher.isBandR_one_op
#print axioms BookProof.HermiteBandHigher.isBandDeg_mulOp_multiset
#print axioms BookProof.HermiteBandHigher.isBandDeg_mulOp_monomial
#print axioms BookProof.HermiteBandHigher.isBandDeg_mulOp

-- The Yang–Mills matrix data.
#print axioms BookProof.YangMillsBandBounds.ymHermOp_eq
#print axioms BookProof.YangMillsBandBounds.ymHermCol_eq
#print axioms BookProof.YangMillsBandBounds.isHermCol_ymHermCol
#print axioms BookProof.YangMillsBandBounds.isBandR2_magMulOp
#print axioms BookProof.YangMillsBandBounds.isBandR4_ymPoly
#print axioms BookProof.YangMillsBandBounds.gradedBand_of_isBandR
#print axioms BookProof.YangMillsBandBounds.ym_hermCol_band_bounds

-- The ghost sector.
#print axioms BookProof.YangMillsGhost.ghostCore_dense
#print axioms BookProof.YangMillsGhost.fibreHam_symmetricOn
#print axioms BookProof.YangMillsGhost.ymGhostHam_symmetricOn
#print axioms BookProof.YangMillsGhost.ymGhostHam_preserves_ghostNumber
#print axioms BookProof.YangMillsGhost.ymGhostHam_vacuum_fibre
#print axioms BookProof.YangMillsGhost.fibreHam_abelian_esa
#print axioms BookProof.YangMillsGhost.ymGhostHam_essentiallySelfAdjointOn_core
#print axioms BookProof.YangMillsGhost.ymGhostHam_stone_flow
#print axioms BookProof.YangMillsGhost.ymGhostHam_add_bounded_coupling_esa

-- The abelian/QED index.
#print axioms BookProof.QedConsolidation.qed_one_particle_esa
#print axioms BookProof.QedConsolidation.qed_fock_esa
#print axioms BookProof.QedConsolidation.qed_fock_exists_selfAdjoint_realization
#print axioms BookProof.QedConsolidation.qed_fock_time_translation
#print axioms BookProof.QedConsolidation.qed_no_one_particle_form_gap
#print axioms BookProof.QedConsolidation.qed_photon_no_one_particle_gap
#print axioms BookProof.QedConsolidation.qed_ghost_esa
#print axioms BookProof.QedConsolidation.qed_ghost_vacuum_decouples
