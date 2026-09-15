import BookProof.ChapterHowlandAutonomization

/-!
# Axiom audit for `BookProof.ChapterHowlandAutonomization`

Run with `lake build Work.HowlandAutonomizationAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.Howland.hasDerivAt_autonomize
#print axioms BookProof.Howland.hasDerivAt_of_autonomize
#print axioms BookProof.Howland.isPropagator_id
#print axioms BookProof.Howland.isPropagator_of_group
#print axioms BookProof.Howland.howland_zero
#print axioms BookProof.Howland.howland_add
#print axioms BookProof.Howland.howland_neg
#print axioms BookProof.Howland.howland_lintegral_normSq
