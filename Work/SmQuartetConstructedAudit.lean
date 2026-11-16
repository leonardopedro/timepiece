/-
Axiom audit for §47.5 and §50/§8 of `BookProof.SmQuartet` — the physical projector
constructed from the b-ghost, and the Standard Model's own b-ghost.

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
The construction removes `V` as an assumption: it is computed from `P` by
`physProjOf Q P = 1 − (QP + PQ) + Q P² Q`, and `bGhostOf Q P` restores the anticommutator.
§8 then constructs the Standard Model's own b-ghost: `exists_contractingHomotopy` gives every
endomorphism of a finite-dimensional space a contracting homotopy, `smQuartet` is the resulting
quartet of `smBrstCharge`, and `smBghost`/`smPhysProj` are its `bGhost`/`physProj` fields.
§9 characterises the range of the constructed projector instead of identifying it:
`range V = ker Q ⊓ ker P` (`range_physProjOf`), the harmonic representatives, and for the SM
`range smPhysProj ⊆ closed (smBrstCharge)`.  Identifying that range with the transverse,
ghost-parity-even subspace needs a concrete mode pairing and a ghost parity, which the
choice-based construction does not supply.  The fixing hypothesis `hEtaPhys` is therefore
replaced by the weaker and correct input: `PhysicalPositivity` follows from positivity of the
charge form on that range (`physicalPositivity_of_quartet_on_range`,
`smPhysicalPositivity_of_physForm`), not from `η (V y) = V y`.
-/
import BookProof.Sm.ChapterSmBghostFormula
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.SmQuartet BookProof.SmQuartet.BrstQuartet

#audit_axioms physProjOf
#audit_axioms bGhostOf
#audit_axioms physProjOf_apply
#audit_axioms bGhostOf_apply
#audit_axioms QP_idem
#audit_axioms physProjOf_Q
#audit_axioms physProjOf_comp_Q
#audit_axioms QP_physProjOf
#audit_axioms physProjOf_idem
#audit_axioms bGhostOf_anticomm
#audit_axioms quartetOfHomotopy
#audit_axioms physicalPositivity_of_homotopy
#audit_axioms physProjOf_commute_parity
#audit_axioms physProjOf_mem_even
#audit_axioms physicalPositivity_of_homotopy_sectors
#audit_axioms exQ_exP_exQ
#audit_axioms exP_exQ_exP
#audit_axioms exP_exQ_exP_gives_V
#audit_axioms exists_contractingHomotopy
#audit_axioms isBrst_smBrstCharge
#audit_axioms smBrstCharge_quartet_nonempty
#audit_axioms smQuartet
#audit_axioms smBghost
#audit_axioms smPhysProj
#audit_axioms smPhysicalPositivity_of_etaPhys
#audit_axioms BrstQuartet.mem_range_physProj_iff
#audit_axioms BrstQuartet.range_physProj_le_closed
#audit_axioms BrstQuartet.P_physProjOf
#audit_axioms BrstQuartet.range_physProjOf
#audit_axioms BrstQuartet.physicalPositivity_of_quartet_on_range
#audit_axioms BrstQuartet.physicalPositivity_of_homotopy_on_range
#audit_axioms smPhysProj_mem_closed
#audit_axioms smPhysicalPositivity_of_physForm
#audit_axioms BookProof.SmQuartet.spineMap
#audit_axioms BookProof.SmQuartet.spineMap_injective
#audit_axioms BookProof.SmQuartet.spineMap_surjective
#audit_axioms BookProof.SmQuartet.kerEquivOfBrst
#audit_axioms BookProof.SmQuartet.Q_kerEquivOfBrst_symm
#audit_axioms BookProof.SmQuartet.canonicalHomotopy
#audit_axioms BookProof.SmQuartet.Q_canonicalHomotopy
#audit_axioms BookProof.SmQuartet.canonicalHomotopy_QSQ
#audit_axioms BookProof.SmQuartet.canonicalHomotopy_SQS
#audit_axioms BookProof.SmQuartet.ker_canonicalHomotopy
#audit_axioms BookProof.SmQuartet.range_physProjOf_canonical
#audit_axioms BookProof.SmQuartet.quartet_canonical
#audit_axioms BookProof.SmQuartet.smBghostFormula
#audit_axioms BookProof.SmQuartet.smPhysProjFormula
#audit_axioms BookProof.SmQuartet.ker_smBghostFormula
#audit_axioms BookProof.SmQuartet.smPhysProjFormula_range
#audit_axioms BookProof.SmQuartet.BrstQuartet.range_physProjOf_disjoint
#audit_axioms BookProof.SmQuartet.BrstQuartet.closed_eq_sup_range_physProjOf
#audit_axioms BookProof.SmQuartet.BrstQuartet.finrank_range_physProjOf
#audit_axioms BookProof.SmQuartet.smPhysProj_finrank
#audit_axioms BookProof.SmQuartet.finrank_smPhysProjFormula_range
#audit_axioms BookProof.SmQuartet.smPhysProj_finrank_eq_formula
#audit_axioms BookProof.SmQuartet.smPhysMetric
#audit_axioms BookProof.SmQuartet.smPhysicalPositivity_physMetric
#audit_axioms BookProof.SmQuartet.smPhysMetric_kform_eq_norm_sq_of_mem
#audit_axioms BookProof.SmQuartet.smPhysProjFormula_le_orthogonal
#audit_axioms BookProof.SmQuartet.closed_eq_sup_range_smPhysProjFormula
#audit_axioms BookProof.SmQuartet.smPhysMetric_radical_eq_gauge
#audit_axioms BookProof.SmQuartet.smPhysMetric_descends
#audit_axioms BookProof.SmQuartet.smPhysMetric_definite
#audit_axioms BookProof.SmQuartet.smPhysMetric_representative
#audit_axioms BookProof.SmGaugeRep.embedMatter_apply_matter
#audit_axioms BookProof.SmGaugeRep.embedMatter_apply_ghost_col
#audit_axioms BookProof.SmGaugeRep.embedMatter_apply_ghost_row
#audit_axioms BookProof.SmGaugeRep.fermiBilin_embedMatter
#audit_axioms BookProof.SmGaugeRep.fermiBilin_embedMatter_diagonal
#audit_axioms BookProof.SmGaugeRep.fermiBilin_embedMatter_scalar_occ
#audit_axioms BookProof.SmGaugeRep.smGen_hyper
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_hyper_occ_ne_zero
#audit_axioms BookProof.SmQuartet.smGhostParity_not_noGhost_doublet
#audit_axioms BookProof.SmBrstGhost.ghostNumber_mul_cubic_monomial
#audit_axioms BookProof.SmBrstGhost.ghostNumber_comm_smGhostCharge
#audit_axioms BookProof.SmBrstGhost.ghostNumber_smGhostCharge_eigen
#audit_axioms BookProof.SmBrstGhost.annih_occ_self
#audit_axioms BookProof.SmBrstGhost.creat_occ_empty
#audit_axioms BookProof.SmGaugeRep.castAdd12_inj
#audit_axioms BookProof.SmGaugeRep.occ_apply_single
#audit_axioms BookProof.SmGaugeRep.creat_annih_occ_entry
#audit_axioms BookProof.SmGaugeRep.matterGen_occ_entry
#audit_axioms BookProof.SmGaugeRep.matterGen_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.smGen_weak_entry
#audit_axioms BookProof.SmGaugeRep.smGen_gluon_entry
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_weak_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_gluon_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.smGen_entry_gluon
#audit_axioms BookProof.SmGaugeRep.smGen_entry_weak
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_gluon1_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_gluon2_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_gluon3_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_gluon4_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_gluon5_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_gluon6_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_gluon7_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_weak9_occ_ne_zero
#audit_axioms BookProof.SmGaugeRep.matterGen_smGen_weak10_occ_ne_zero
