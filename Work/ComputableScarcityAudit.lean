import BookProof.ChapterComputableScarcity

/-!
# Axiom audit for `BookProof.ChapterComputableScarcity`

Run with `lake build Work.ComputableScarcityAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.ComputableScarcity.exists_code_of_computable
#print axioms BookProof.ComputableScarcity.countable_computable
#print axioms BookProof.ComputableScarcity.exists_infinitely_often_ne
#print axioms BookProof.ComputableScarcity.uncountable_natFun
#print axioms BookProof.ComputableScarcity.exists_differs_infinitely_often_from_all_computable
#print axioms BookProof.ComputableScarcity.exists_not_eventually_eq_computable
#print axioms BookProof.ComputableScarcity.exists_not_computable
