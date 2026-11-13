import BookProof.ChapterComputableScarcity
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterComputableScarcity`

Run with `lake build Work.ComputableScarcityAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.ComputableScarcity.exists_code_of_computable
#audit_axioms BookProof.ComputableScarcity.countable_computable
#audit_axioms BookProof.ComputableScarcity.exists_infinitely_often_ne
#audit_axioms BookProof.ComputableScarcity.uncountable_natFun
#audit_axioms BookProof.ComputableScarcity.exists_differs_infinitely_often_from_all_computable
#audit_axioms BookProof.ComputableScarcity.exists_not_eventually_eq_computable
#audit_axioms BookProof.ComputableScarcity.exists_not_computable
