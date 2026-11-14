/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceLatticeTranslation`.

That module builds the translation the lattice actually supplies — the cyclic cell rotation on
`Config = Fin latticeDim → ℝ`, lifted to an automorphism `obsShift k` (`k : ℤ`) of the observable
algebra — and proves that the real-parameter positive-time hypothesis is **false** for it:
`not_preservesPositiveTime_of_shift`.  Every theorem below must rest on `propext`,
`Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceLatticeTranslation
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms coordOf_siteShift
#audit_axioms cellRotate_lastPos
#audit_axioms obsShift_zero
#audit_axioms obsShift_add
#audit_axioms obsShift_mul
#audit_axioms obsShift_one
#audit_axioms obsShift_comp_neg
#audit_axioms coordOf_lastPosSite
#audit_axioms isPosTime_lastPosSite
#audit_axioms not_isPosTime_siteShift_lastPosSite
#audit_axioms coordFun_mem_positiveTime
#audit_axioms obsShift_one_not_mem_positiveTime
#audit_axioms not_preservesPositiveTime_of_shift
