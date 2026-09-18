import BookProof.ChapterNsPartialFourier

/-!
# Axiom audit — the partial (spatial-only) Fourier transform

Every headline result of `BookProof/ChapterNsPartialFourier.lean` (the remaining part of item 1 of
the Navier–Stokes plan items: the partial transform on the fibred one-particle space) must rest on
the standard axioms only: `propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.NsPartialFourier.postcompCLM_apply
#print axioms BookProof.NsPartialFourier.postcompCLM_lineDerivOp
#print axioms BookProof.NsPartialFourier.fourier_postcompCLM
#print axioms BookProof.NsPartialFourier.toLp_postcompCLM
#print axioms BookProof.NsPartialFourier.partialFourier_norm
#print axioms BookProof.NsPartialFourier.partialFourier_inner
#print axioms BookProof.NsPartialFourier.partialFourier_fibreOp
#print axioms BookProof.NsPartialFourier.fourier_vecMomentumOp_apply
#print axioms BookProof.NsPartialFourier.postcompCLM_vecMomentumOp
#print axioms BookProof.NsPartialFourier.nsPartialFourier_norm
#print axioms BookProof.NsPartialFourier.nsPartialFourier_fibreOp
#print axioms BookProof.NsPartialFourier.nsPartialFourier_fibreFourier
#print axioms BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq
