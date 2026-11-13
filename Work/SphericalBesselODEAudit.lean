import BookProof.HarmonicAnalysis.ChapterBesselHarmonic
import BookProof.ChapterAngularMomentum
import BookProof.HarmonicAnalysis.ChapterRadialLaplacian
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for `BookProof.ChapterSphericalBesselODE`: the spherical Bessel
equation for every angular momentum `l`, the three-term recurrence, and the
radial eigenvalue property behind Note 68 of `book.tex` §A.5.  Every result must
report only `propext`, `Classical.choice` and `Quot.sound`.
-/

#audit_axioms BookProof.ChapterSphericalBesselODE.contDiffOn_gIter
#audit_axioms BookProof.ChapterSphericalBesselODE.deriv_gIter_eq
#audit_axioms BookProof.ChapterSphericalBesselODE.second_deriv_gIter
#audit_axioms BookProof.ChapterSphericalBesselODE.gIter_ode
#audit_axioms BookProof.ChapterSphericalBesselODE.gIter_pred_eq
#audit_axioms BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel
#audit_axioms BookProof.ChapterSphericalBesselODE.sbessel_ode
#audit_axioms BookProof.ChapterSphericalBesselODE.sbessel_recurrence
#audit_axioms BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen

/-! Radial Laplacian and the `s`-wave form of Note 68. -/

#audit_axioms BookProof.ChapterRadialLaplacian.laplacian_comp_normSq
#audit_axioms BookProof.ChapterRadialLaplacian.deriv_sqrt_comp
#audit_axioms BookProof.ChapterRadialLaplacian.laplacian_radial
#audit_axioms BookProof.ChapterRadialLaplacian.laplacian_sbessel_zero
#audit_axioms BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero
#audit_axioms BookProof.ChapterRadialLaplacian.helmholtz_sbessel_zero_euclidean

/-! The angular half of Note 68. -/

#audit_axioms BookProof.ChapterAngularMomentum.fderiv_rotationVector
#audit_axioms BookProof.ChapterAngularMomentum.angularMomentum_eigen
#audit_axioms BookProof.ChapterAngularMomentum.circHarm_rotate
#audit_axioms BookProof.ChapterAngularMomentum.circHarm_abs
#audit_axioms BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen

/-! Product rule, radial × harmonic, and Note 68 in the sector of angular momentum `l`. -/

#audit_axioms BookProof.ChapterLaplacianProduct.laplacian_mul
#audit_axioms BookProof.ChapterLaplacianProduct.fderiv_radial
#audit_axioms BookProof.ChapterLaplacianProduct.laplacian_radial_mul_harmonic
#audit_axioms BookProof.ChapterLaplacianProduct.helmholtz_radial_mul_harmonic
#audit_axioms BookProof.ChapterBesselHarmonic.reduced_from_radial
#audit_axioms BookProof.ChapterBesselHarmonic.reduced_radial_sbessel
#audit_axioms BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic
#audit_axioms BookProof.ChapterBesselHarmonic.helmholtz_sbessel_one_clm
