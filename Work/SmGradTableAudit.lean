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
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.SmGradTable

#audit_axioms pderiv_X'
#audit_axioms pderiv_C_mul
#audit_axioms pderiv_lin_sum
#audit_axioms pderiv_sq_sum
#audit_axioms pderiv_eq
#audit_axioms BookProof.SmGradTable.sq_le
#audit_axioms disjoint_smS_smT
#audit_axioms smDG_notMem
#audit_axioms smDW_notMem
#audit_axioms smDB_notMem
#audit_axioms smDPhi_notMem
#audit_axioms biform_smMagG_poly
#audit_axioms biform_smMagW_poly
#audit_axioms biform_smCovD_poly
#audit_axioms biform_smWall_poly
#audit_axioms biform_form_poly
#audit_axioms biform_smPhi_poly
#audit_axioms gradBound_smPhi
#audit_axioms exists_potSelfBound_sm
#audit_axioms PotSelfBound_mono
#audit_axioms exists_potSelfBound_sm_nonneg
#audit_axioms exists_kineticSum_bound_sm
#audit_axioms exists_smNormalForm_norm_le
#audit_axioms weylFlat_eq_weylPotPoly
#audit_axioms weylFlat_eq_flat_add
#audit_axioms evAt_add
#audit_axioms eval_weylFlat_zero
#audit_axioms eval_weylFlat_one
#audit_axioms eval_weylFlat_self
#audit_axioms not_gradDom_weylFlat
#audit_axioms weylCoercive_eq_wsSum
#audit_axioms polyW_weylCoercive
#audit_axioms gradDom_weylCoercive
#audit_axioms gradBound_weylFlat
#audit_axioms gradDom_weylCoercive_flat
