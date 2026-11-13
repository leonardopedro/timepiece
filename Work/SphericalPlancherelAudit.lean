import BookProof.HarmonicAnalysis.ChapterSphericalPlancherel
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for `BookProof.ChapterSphericalPlancherel`: Plancherel's theorem for
the Fourier sine transform and the resulting unitarity of the spherical
(Fourier–Bessel) transform in the sector `l = 0`.  Every result must report only
`propext`, `Classical.choice` and `Quot.sound`.
-/

#audit_axioms BookProof.ChapterSphericalPlancherel.integral_eq_zero_of_odd
#audit_axioms BookProof.ChapterSphericalPlancherel.integral_eq_two_smul_of_even
#audit_axioms BookProof.ChapterSphericalPlancherel.integral_eq_two_mul_of_even_real
#audit_axioms BookProof.ChapterSphericalPlancherel.fourier_eq_cos_sub_sin
#audit_axioms BookProof.ChapterSphericalPlancherel.fourier_odd_eq
#audit_axioms BookProof.ChapterSphericalPlancherel.sine_plancherel
#audit_axioms BookProof.ChapterSphericalPlancherel.sineKernel_plancherel
#audit_axioms BookProof.ChapterSphericalPlancherel.sphericalTransform_eq
#audit_axioms BookProof.ChapterSphericalPlancherel.spherical_plancherel
#audit_axioms BookProof.ChapterSphericalPlancherel.oddSchwartz_ne_zero
#audit_axioms BookProof.ChapterSphericalPlancherel.spherical_plancherel_bump
