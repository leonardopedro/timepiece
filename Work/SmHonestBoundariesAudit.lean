import BookProof.ChapterSmCarContinuum
import BookProof.ChapterSmGaugeConnection
import BookProof.ChapterSmBrstGhost
import BookProof.ChapterSmGaugeRepresentation

/-!
Axiom audit for the honest-boundary closure wave of the Standard-Model work order
(§D6b-SM of `CONSOLIDATED_PLAN.md`): the continuum CAR algebra over an infinite-dimensional
one-particle space, the gauge connection inside the covariant derivative `D`, and the
ghost/BRST sector with its concrete gauge representation.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- 1. The continuum CAR algebra.
#print axioms BookProof.SmCarContinuum.car_cAnn_cCre_self
#print axioms BookProof.SmCarContinuum.car_cAnn_cCre_of_ne
#print axioms BookProof.SmCarContinuum.car_cAnn_cAnn
#print axioms BookProof.SmCarContinuum.car_cCre_cCre
#print axioms BookProof.SmCarContinuum.inner_cCre_left
#print axioms BookProof.SmCarContinuum.inner_cAnn_left
#print axioms BookProof.SmCarContinuum.cCreS_single
#print axioms BookProof.SmCarContinuum.cCreS_add
#print axioms BookProof.SmCarContinuum.cCreS_smul
#print axioms BookProof.SmCarContinuum.norm_cCreS_le
#print axioms BookProof.SmCarContinuum.norm_cAnnS_le
#print axioms BookProof.SmCarContinuum.car_smeared
#print axioms BookProof.SmCarContinuum.car_cCreS_cCreS
#print axioms BookProof.SmCarContinuum.car_cAnnS_cAnnS
#print axioms BookProof.SmCarContinuum.norm_oneParticle
#print axioms BookProof.SmCarContinuum.norm_cCreS_eq
#print axioms BookProof.SmCarContinuum.car_hilbert
#print axioms BookProof.SmCarContinuum.car_hilbert_cre
#print axioms BookProof.SmCarContinuum.norm_carCre_le

-- 2. The gauge connection inside `D`.
#print axioms BookProof.SmGaugeConnection.conn_conjTranspose
#print axioms BookProof.SmGaugeConnection.covD_conjTranspose
#print axioms BookProof.SmGaugeConnection.covD_zero_coupling
#print axioms BookProof.SmGaugeConnection.covD_commutator
#print axioms BookProof.SmGaugeConnection.covD_commutator_abelian
#print axioms BookProof.SmGaugeConnection.covD_conj
#print axioms BookProof.SmGaugeConnection.conn_gauge_transform
#print axioms BookProof.SmGaugeConnection.diracGaugeMat_conjTranspose
#print axioms BookProof.SmGaugeConnection.diracGaugeMat_split
#print axioms BookProof.SmGaugeConnection.diracGaugeMat_free
#print axioms BookProof.SmGaugeConnection.diracGaugeField_symmetric
#print axioms BookProof.SmGaugeConnection.dirac_gauge_field_esa

-- 3. The ghost / BRST sector.
#print axioms BookProof.SmBrstGhost.smStruct_antisymm
#print axioms BookProof.SmBrstGhost.smStruct_jacobi
#print axioms BookProof.SmBrstGhost.smGhostCAR
#print axioms BookProof.SmBrstGhost.ghostNumber_occ
#print axioms BookProof.SmBrstGhost.ghostNumber_comm_ghostCre
#print axioms BookProof.SmBrstGhost.ghostNumber_comm_ghostAnn
#print axioms BookProof.SmBrstGhost.smGhostCharge_nilpotent
#print axioms BookProof.SmBrstGhost.brstCharge_nilpotent
#print axioms BookProof.SmBrstGhost.fermiBilin_lie
#print axioms BookProof.SmBrstGhost.matterGen_lie
#print axioms BookProof.SmBrstGhost.matterGen_comm_ghostCre
#print axioms BookProof.SmBrstGhost.matterGen_comm_ghostAnn
#print axioms BookProof.SmBrstGhost.smBrstCharge_nilpotent

-- 4. The concrete gauge representation.
#print axioms BookProof.SmGaugeRep.su2gen_closes
#print axioms BookProof.SmGaugeRep.smGenP_closes
#print axioms BookProof.SmGaugeRep.smGen_closes
#print axioms BookProof.SmGaugeRep.sm_brst_nilpotent_of_su3_relations
#print axioms BookProof.SmGaugeRep.sm_brst_nilpotent_rep
