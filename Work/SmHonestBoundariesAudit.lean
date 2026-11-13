import BookProof.Sm.ChapterSmCarContinuum
import BookProof.Sm.ChapterSmGaugeConnection
import BookProof.Sm.ChapterSmBrstGhost
import BookProof.Sm.ChapterSmGaugeRepresentation
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the honest-boundary closure wave of the Standard-Model work order
(§D6b-SM of `CONSOLIDATED_PLAN.md`): the continuum CAR algebra over an infinite-dimensional
one-particle space, the gauge connection inside the covariant derivative `D`, and the
ghost/BRST sector with its concrete gauge representation.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- 1. The continuum CAR algebra.
#audit_axioms BookProof.SmCarContinuum.car_cAnn_cCre_self
#audit_axioms BookProof.SmCarContinuum.car_cAnn_cCre_of_ne
#audit_axioms BookProof.SmCarContinuum.car_cAnn_cAnn
#audit_axioms BookProof.SmCarContinuum.car_cCre_cCre
#audit_axioms BookProof.SmCarContinuum.inner_cCre_left
#audit_axioms BookProof.SmCarContinuum.inner_cAnn_left
#audit_axioms BookProof.SmCarContinuum.cCreS_single
#audit_axioms BookProof.SmCarContinuum.cCreS_add
#audit_axioms BookProof.SmCarContinuum.cCreS_smul
#audit_axioms BookProof.SmCarContinuum.norm_cCreS_le
#audit_axioms BookProof.SmCarContinuum.norm_cAnnS_le
#audit_axioms BookProof.SmCarContinuum.car_smeared
#audit_axioms BookProof.SmCarContinuum.car_cCreS_cCreS
#audit_axioms BookProof.SmCarContinuum.car_cAnnS_cAnnS
#audit_axioms BookProof.SmCarContinuum.norm_oneParticle
#audit_axioms BookProof.SmCarContinuum.norm_cCreS_eq
#audit_axioms BookProof.SmCarContinuum.car_hilbert
#audit_axioms BookProof.SmCarContinuum.car_hilbert_cre
#audit_axioms BookProof.SmCarContinuum.norm_carCre_le

-- 2. The gauge connection inside `D`.
#audit_axioms BookProof.SmGaugeConnection.conn_conjTranspose
#audit_axioms BookProof.SmGaugeConnection.covD_conjTranspose
#audit_axioms BookProof.SmGaugeConnection.covD_zero_coupling
#audit_axioms BookProof.SmGaugeConnection.covD_commutator
#audit_axioms BookProof.SmGaugeConnection.covD_commutator_abelian
#audit_axioms BookProof.SmGaugeConnection.covD_conj
#audit_axioms BookProof.SmGaugeConnection.conn_gauge_transform
#audit_axioms BookProof.SmGaugeConnection.diracGaugeMat_conjTranspose
#audit_axioms BookProof.SmGaugeConnection.diracGaugeMat_split
#audit_axioms BookProof.SmGaugeConnection.diracGaugeMat_free
#audit_axioms BookProof.SmGaugeConnection.diracGaugeField_symmetric
#audit_axioms BookProof.SmGaugeConnection.dirac_gauge_field_esa

-- 3. The ghost / BRST sector.
#audit_axioms BookProof.SmBrstGhost.smStruct_antisymm
#audit_axioms BookProof.SmBrstGhost.smStruct_jacobi
#audit_axioms BookProof.SmBrstGhost.smGhostCAR
#audit_axioms BookProof.SmBrstGhost.ghostNumber_occ
#audit_axioms BookProof.SmBrstGhost.ghostNumber_comm_ghostCre
#audit_axioms BookProof.SmBrstGhost.ghostNumber_comm_ghostAnn
#audit_axioms BookProof.SmBrstGhost.smGhostCharge_nilpotent
#audit_axioms BookProof.SmBrstGhost.brstCharge_nilpotent
#audit_axioms BookProof.SmBrstGhost.fermiBilin_lie
#audit_axioms BookProof.SmBrstGhost.matterGen_lie
#audit_axioms BookProof.SmBrstGhost.matterGen_comm_ghostCre
#audit_axioms BookProof.SmBrstGhost.matterGen_comm_ghostAnn
#audit_axioms BookProof.SmBrstGhost.smBrstCharge_nilpotent

-- 4. The concrete gauge representation.
#audit_axioms BookProof.SmGaugeRep.su2gen_closes
#audit_axioms BookProof.SmGaugeRep.smGenP_closes
#audit_axioms BookProof.SmGaugeRep.smGen_closes
#audit_axioms BookProof.SmGaugeRep.sm_brst_nilpotent_of_su3_relations
#audit_axioms BookProof.SmGaugeRep.sm_brst_nilpotent_rep
