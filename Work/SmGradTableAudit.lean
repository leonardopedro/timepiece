/-
Axiom audit for `BookProof.SmGradTable` (SM_ESA_COMPLETION_PLAN §53 / P4).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.  The module
supplies the per-form `pderiv` table for the 49 Standard-Model forms — the last named input of the
reverse elliptic estimate — and closes the chain into `PotSelfBound` (`exists_potSelfBound_sm`).
-/
import BookProof.Sm.ChapterSmGradTable

open BookProof.SmGradTable

#print axioms pderiv_X'
#print axioms pderiv_C_mul
#print axioms pderiv_lin_sum
#print axioms pderiv_sq_sum
#print axioms pderiv_eq
#print axioms sq_le
#print axioms disjoint_smS_smT
#print axioms smDG_notMem
#print axioms smDW_notMem
#print axioms smDB_notMem
#print axioms smDPhi_notMem
#print axioms biform_smMagG_poly
#print axioms biform_smMagW_poly
#print axioms biform_smCovD_poly
#print axioms biform_smWall_poly
#print axioms biform_form_poly
#print axioms biform_smPhi_poly
#print axioms gradBound_smPhi
#print axioms exists_potSelfBound_sm
