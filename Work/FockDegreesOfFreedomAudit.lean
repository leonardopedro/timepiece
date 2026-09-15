import BookProof.ChapterFockDegreesOfFreedom

/-!
# Axiom audit for `BookProof.ChapterFockDegreesOfFreedom`

Run with `lake build Work.FockDegreesOfFreedomAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.FockDegreesOfFreedom.card_ghost_eq_two_mul
#print axioms BookProof.FockDegreesOfFreedom.NavierStokes.card_symPair
#print axioms BookProof.FockDegreesOfFreedom.NavierStokes.jetCard
#print axioms BookProof.FockDegreesOfFreedom.NavierStokes.jetCard_firstOrder
#print axioms BookProof.FockDegreesOfFreedom.NavierStokes.ghostRawCard
#print axioms BookProof.FockDegreesOfFreedom.YangMills3D.jetCard
#print axioms BookProof.FockDegreesOfFreedom.YangMills3D.ghostRawCard
#print axioms BookProof.FockDegreesOfFreedom.YangMills4D.jetCard
#print axioms BookProof.FockDegreesOfFreedom.YangMills4D.ghostRawCard
#print axioms BookProof.FockDegreesOfFreedom.Gravity.jetCard
#print axioms BookProof.FockDegreesOfFreedom.Gravity.ghostRawCard
