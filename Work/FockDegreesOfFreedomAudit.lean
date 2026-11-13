import BookProof.ChapterFockDegreesOfFreedom
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterFockDegreesOfFreedom`

Run with `lake build Work.FockDegreesOfFreedomAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul
#audit_axioms BookProof.FockDegreesOfFreedom.NavierStokes.card_symPair
#audit_axioms BookProof.FockDegreesOfFreedom.NavierStokes.jetCard
#audit_axioms BookProof.FockDegreesOfFreedom.NavierStokes.jetCard_firstOrder
#audit_axioms BookProof.FockDegreesOfFreedom.NavierStokes.ghostRawCard_navierStokes
#audit_axioms BookProof.FockDegreesOfFreedom.YangMills3D.jetCard
#audit_axioms BookProof.FockDegreesOfFreedom.YangMills3D.ghostRawCard_yangMills3D
#audit_axioms BookProof.FockDegreesOfFreedom.YangMills4D.jetCard
#audit_axioms BookProof.FockDegreesOfFreedom.YangMills4D.ghostRawCard_yangMills4D
#audit_axioms BookProof.FockDegreesOfFreedom.Gravity.jetCard
#audit_axioms BookProof.FockDegreesOfFreedom.Gravity.ghostRawCard_gravity
