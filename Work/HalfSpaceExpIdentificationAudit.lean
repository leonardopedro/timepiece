/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceExpIdentification`.

That module closes the gap `cftproof.md` E3 left open around `hsGenerator_eq_neg`: under the flow
hypothesis `hflow`, the abstract half-space semigroup `hsEvolCompletionFun` is *identified* with the
bounded exponential `e^{−τH}`, by Grönwall on `v' = −H v`, `v(0) = 0`.  Every theorem below must
rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceExpIdentification
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms hsEvolCompletionFun_comp_neg
#audit_axioms hasDerivWithinAt_hsEvol_flow
#audit_axioms hsEvolCompletionFun_eq_hsExpOp
#audit_axioms hsGenerator_eq_neg_exp
#audit_axioms hsExpOp_iff_flow
