/-
Axiom audit for `BookProof.SmGradTable` (SM_ESA_COMPLETION_PLAN §53 / P4).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.  The module
supplies the per-form `pderiv` table for the 49 Standard-Model forms — the last named input of the
reverse elliptic estimate — closes the chain into `PotSelfBound` (`exists_potSelfBound_sm`), and
instantiates the downstream consequences (`exists_kineticSum_bound_sm` = §19's `hpoly`,
`exists_smNormalForm_norm_le` = §15's P2 relative bound) at that now-unconditional `β`.  Section 6
carries the negative result for the QYM/NS forms: `not_gradDom_weylFlat`, whose Weyl potential
`Σ Φ_j² + 1` is *not* gradient-dominated, so the normal form applies but its conclusion does not.
-/
import BookProof.Sm.ChapterSmGradTable

open BookProof.SmGradTable

#print axioms pderiv_X'
#print axioms pderiv_C_mul
#print axioms pderiv_lin_sum
#print axioms pderiv_sq_sum
#print axioms pderiv_eq
#print axioms BookProof.SmGradTable.sq_le
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
#print axioms PotSelfBound_mono
#print axioms exists_potSelfBound_sm_nonneg
#print axioms exists_kineticSum_bound_sm
#print axioms exists_smNormalForm_norm_le
#print axioms weylFlat_eq_weylPotPoly
#print axioms weylFlat_eq_flat_add
#print axioms evAt_add
#print axioms eval_weylFlat_zero
#print axioms eval_weylFlat_one
#print axioms eval_weylFlat_self
#print axioms not_gradDom_weylFlat
