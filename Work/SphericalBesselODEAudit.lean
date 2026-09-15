import BookProof.ChapterBesselHarmonic
import BookProof.ChapterAngularMomentum
import BookProof.ChapterRadialLaplacian

/-!
Axiom audit for `BookProof.ChapterSphericalBesselODE`: the spherical Bessel
equation for every angular momentum `l`, the three-term recurrence, and the
radial eigenvalue property behind Note 68 of `book.tex` §A.5.  Every result must
report only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms BookProof.ChapterSphericalBesselODE.contDiffOn_gIter
#print axioms BookProof.ChapterSphericalBesselODE.deriv_gIter_eq
#print axioms BookProof.ChapterSphericalBesselODE.second_deriv_gIter
#print axioms BookProof.ChapterSphericalBesselODE.gIter_ode
#print axioms BookProof.ChapterSphericalBesselODE.gIter_pred_eq
#print axioms BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel
#print axioms BookProof.ChapterSphericalBesselODE.sbessel_ode
#print axioms BookProof.ChapterSphericalBesselODE.sbessel_recurrence
#print axioms BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen

/-! Radial Laplacian and the `s`-wave form of Note 68. -/

#print axioms BookProof.ChapterRadialLaplacian.laplacian_comp_normSq
#print axioms BookProof.ChapterRadialLaplacian.deriv_sqrt_comp
#print axioms BookProof.ChapterRadialLaplacian.laplacian_radial
#print axioms BookProof.ChapterRadialLaplacian.laplacian_sbessel_zero
#print axioms BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero
#print axioms BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean

/-! The angular half of Note 68. -/

#print axioms BookProof.ChapterAngularMomentum.fderiv_rotationVector
#print axioms BookProof.ChapterAngularMomentum.angularMomentum_eigen
#print axioms BookProof.ChapterAngularMomentum.circHarm_rotate
#print axioms BookProof.ChapterAngularMomentum.circHarm_abs
#print axioms BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen

/-! Product rule, radial × harmonic, and Note 68 in the sector of angular momentum `l`. -/

#print axioms BookProof.ChapterLaplacianProduct.laplacian_mul
#print axioms BookProof.ChapterLaplacianProduct.fderiv_radial
#print axioms BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic
#print axioms BookProof.ChapterLaplacianProduct.helmholtz_radial_mul_harmonic
#print axioms BookProof.ChapterBesselHarmonic.reduced_from_radial
#print axioms BookProof.ChapterBesselHarmonic.reduced_radial_sbessel
#print axioms BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic
#print axioms BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm
