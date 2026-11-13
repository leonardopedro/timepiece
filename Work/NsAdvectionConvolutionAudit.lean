import BookProof.ChapterNsAdvectionConvolution
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit — the convolution algebra of the advection

Every headline result of `BookProof/ChapterNsAdvectionConvolution.lean` (item 3 of the
Navier–Stokes plan items) must rest on the standard axioms only: `propext`, `Classical.choice`,
`Quot.sound`.
-/

#audit_axioms BookProof.NsAdvectionConvolution.fourier_fourier_apply
#audit_axioms BookProof.NsAdvectionConvolution.fourier_mul_eq_convolution
#audit_axioms BookProof.NsAdvectionConvolution.fourier_lineDeriv_apply
#audit_axioms BookProof.NsAdvectionConvolution.fourier_advection_convolution
#audit_axioms BookProof.NsAdvectionConvolution.fourier_advection_sum
