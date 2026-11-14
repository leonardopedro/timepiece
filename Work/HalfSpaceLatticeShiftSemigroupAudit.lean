/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceLatticeShiftSemigroup`.

That module inhabits the one-sided API with a *concrete* step — `cellHalfRotate` rotates each time
half internally, so `siteHalfRotate` keeps the positive half inside itself
(`preservesPositiveTimeNat_halfRotateTranslation`), which the cyclic shift of
`HalfSpaceLatticeTranslation` cannot do.  It also proves that the step commutes with the reflection
(`siteHalfRotate_reflectCoord`, `thetaObs_obsHalfRotate`) and that the finite-volume Gibbs state is
invariant under it, so `HsHinvNat` holds there as an **equality**
(`hsHinvNat_gibbsHalfSpaceState`).  Every theorem below must rest on `propext`,
`Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceLatticeShiftSemigroup
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms isPosCell_cellHalfRotate
#audit_axioms isPosTime_siteHalfRotate_iff
#audit_axioms isPosTime_siteHalfRotate_pow_iff
#audit_axioms obsHalfRotate_add
#audit_axioms preservesPositiveTimeNat_halfRotateTranslation
#audit_axioms cellHalfRotate_flipCell
#audit_axioms siteHalfRotate_reflectCoord
#audit_axioms siteHalfRotate_pow_reflectCoord
#audit_axioms thetaObs_obsHalfRotate
#audit_axioms coordSumEquiv_siteHalfRotate
#audit_axioms coordSumEquiv_siteHalfRotate_pow
#audit_axioms configEquiv_comp_siteHalfRotate_pow
#audit_axioms configEquiv_symm_comp_siteHalfRotate_pow
#audit_axioms halfAction_comp_perm
#audit_axioms gibbsWeight_comp_perm
#audit_axioms gibbsFun_obsHalfRotate
#audit_axioms hsHinvNat_gibbsHalfSpaceState
#audit_axioms mem_constGrid
#audit_axioms isHalfRotateInvariant_constGrid
#audit_axioms hsHinvNat_constGrid
#audit_axioms constGrid_transfer_contractive
