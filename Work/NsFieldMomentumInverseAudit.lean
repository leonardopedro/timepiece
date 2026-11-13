import BookProof.Ns.ChapterNsFieldMomentumInverse
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit — the inverse field momentum

Every headline result of `BookProof/Ns/ChapterNsFieldMomentumInverse.lean` (item 2 of the
Navier–Stokes plan items) must rest on the standard axioms only: `propext`, `Classical.choice`,
`Quot.sound`.
-/

#audit_axioms BookProof.NsFieldMomentumInverse.volume_momSymbol_zero
#audit_axioms BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae
#audit_axioms BookProof.NsFieldMomentumInverse.momentum_kernel_trivial
#audit_axioms BookProof.NsFieldMomentumInverse.isMomInverse_unique
#audit_axioms BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp
#audit_axioms BookProof.NsFieldMomentumInverse.cut_mem_momDomain
#audit_axioms BookProof.NsFieldMomentumInverse.momDomain_dense
#audit_axioms BookProof.NsFieldMomentumInverse.isMomInverse_smul
#audit_axioms BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae
#audit_axioms BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp
