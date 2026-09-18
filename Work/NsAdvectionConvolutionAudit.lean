import BookProof.ChapterNsAdvectionConvolution

/-!
# Axiom audit — the convolution algebra of the advection

Every headline result of `BookProof/ChapterNsAdvectionConvolution.lean` (item 3 of the
Navier–Stokes plan items) must rest on the standard axioms only: `propext`, `Classical.choice`,
`Quot.sound`.
-/

#print axioms BookProof.NsAdvectionConvolution.fourier_fourier_apply
#print axioms BookProof.NsAdvectionConvolution.fourier_mul_eq_convolution
#print axioms BookProof.NsAdvectionConvolution.fourier_lineDeriv_apply
#print axioms BookProof.NsAdvectionConvolution.fourier_advection_convolution
#print axioms BookProof.NsAdvectionConvolution.fourier_advection_sum
