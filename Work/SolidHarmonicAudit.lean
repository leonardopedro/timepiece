import BookProof.HarmonicAnalysis.ChapterNote68AllModes
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the solid-harmonic wave: Legendre polynomials from Rodrigues'
formula, the Gegenbauer coefficient recursion, the solid harmonics
`rˡ Y_{lμ}` for **all** `l` and `μ ≤ l` (harmonic, homogeneous of degree `l`,
and equal to `rˡ P_l^μ(cos θ) cos(μφ)` in spherical coordinates), and Note 68 of
`book.tex` §A.5 in every angular-momentum mode.  Every result must report only
`propext`, `Classical.choice` and `Quot.sound`.
-/

/-! Legendre polynomials and the Gegenbauer recursion. -/

#audit_axioms BookProof.ChapterLegendrePolynomial.rodrigues_step
#audit_axioms BookProof.ChapterLegendrePolynomial.legendreAux_ode
#audit_axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_ode
#audit_axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_rec
#audit_axioms BookProof.ChapterLegendrePolynomial.legendre_natDegree_le
#audit_axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_eq_zero
#audit_axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_top_ne_zero
#audit_axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_parity

/-! The analytic toolkit. -/

#audit_axioms BookProof.ChapterSolidHarmonicTools.laplacian_clmPow
#audit_axioms BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow
#audit_axioms BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow
#audit_axioms BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm
#audit_axioms BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm

/-! Solid harmonics for all `l, μ`. -/

#audit_axioms BookProof.ChapterSolidHarmonic.angular_harmonic
#audit_axioms BookProof.ChapterSolidHarmonic.angular_euler
#audit_axioms BookProof.ChapterSolidHarmonic.laplacian_angular_mul_sum
#audit_axioms BookProof.ChapterSolidHarmonic.legendre_rec_factored
#audit_axioms BookProof.ChapterSolidHarmonic.solidHarmonic_harmonic
#audit_axioms BookProof.ChapterSolidHarmonic.solidHarmonicIm_harmonic
#audit_axioms BookProof.ChapterSolidHarmonic.solidHarmonic_euler
#audit_axioms BookProof.ChapterSolidHarmonic.solidHarmonicIm_euler
#audit_axioms BookProof.ChapterSolidHarmonic.radialFactor_eval
#audit_axioms BookProof.ChapterSolidHarmonic.solidHarmonic_spherical_frames_explicit

/-! Note 68 in every mode. -/

#audit_axioms BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic
#audit_axioms BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonicIm
#audit_axioms BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic_euclidean
#audit_axioms BookProof.ChapterNote68AllModes.solidHarmonic_spherical_euclidean
