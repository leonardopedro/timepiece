import BookProof.ChapterHowlandAutonomization
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterHowlandAutonomization`

Run with `lake build Work.HowlandAutonomizationAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.Howland.hasDerivAt_autonomize
#audit_axioms BookProof.Howland.hasDerivAt_of_autonomize
#audit_axioms BookProof.Howland.isPropagator_id
#audit_axioms BookProof.Howland.isPropagator_of_group
#audit_axioms BookProof.Howland.howland_zero
#audit_axioms BookProof.Howland.howland_add
#audit_axioms BookProof.Howland.howland_neg
#audit_axioms BookProof.Howland.howland_lintegral_normSq
