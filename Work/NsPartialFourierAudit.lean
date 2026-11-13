import BookProof.Ns.ChapterNsPartialFourier
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit — the partial (spatial-only) Fourier transform

Every headline result of `BookProof/Ns/ChapterNsPartialFourier.lean` (the remaining part of item 1 of
the Navier–Stokes plan items: the partial transform on the fibred one-particle space) must rest on
the standard axioms only: `propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.NsPartialFourier.postcompCLM_apply
#audit_axioms BookProof.NsPartialFourier.postcompCLM_lineDerivOp
#audit_axioms BookProof.NsPartialFourier.fourier_postcompCLM
#audit_axioms BookProof.NsPartialFourier.toLp_postcompCLM
#audit_axioms BookProof.NsPartialFourier.partialFourier_norm
#audit_axioms BookProof.NsPartialFourier.partialFourier_inner
#audit_axioms BookProof.NsPartialFourier.partialFourier_fibreOp
#audit_axioms BookProof.NsPartialFourier.fourier_vecMomentumOp_apply
#audit_axioms BookProof.NsPartialFourier.postcompCLM_vecMomentumOp
#audit_axioms BookProof.NsPartialFourier.nsPartialFourier_norm
#audit_axioms BookProof.NsPartialFourier.nsPartialFourier_fibreOp
#audit_axioms BookProof.NsPartialFourier.nsPartialFourier_fibreFourier
#audit_axioms BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq
