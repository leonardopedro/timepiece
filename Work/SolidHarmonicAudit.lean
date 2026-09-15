import BookProof.ChapterNote68AllModes

/-!
Axiom audit for the solid-harmonic wave: Legendre polynomials from Rodrigues'
formula, the Gegenbauer coefficient recursion, the solid harmonics
`rˡ Y_{lμ}` for **all** `l` and `μ ≤ l` (harmonic, homogeneous of degree `l`,
and equal to `rˡ P_l^μ(cos θ) cos(μφ)` in spherical coordinates), and Note 68 of
`book.tex` §A.5 in every angular-momentum mode.  Every result must report only
`propext`, `Classical.choice` and `Quot.sound`.
-/

/-! Legendre polynomials and the Gegenbauer recursion. -/

#print axioms BookProof.ChapterLegendrePolynomial.rodrigues_step
#print axioms BookProof.ChapterLegendrePolynomial.legendreAux_ode
#print axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_ode
#print axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_rec
#print axioms BookProof.ChapterLegendrePolynomial.legendre_natDegree_le
#print axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_eq_zero
#print axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_top_ne_zero
#print axioms BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_parity

/-! The analytic toolkit. -/

#print axioms BookProof.ChapterSolidHarmonicTools.laplacian_clmPow
#print axioms BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow
#print axioms BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow
#print axioms BookProof.ChapterSolidHarmonicTools.laplacian_cylTerm
#print axioms BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm

/-! Solid harmonics for all `l, μ`. -/

#print axioms BookProof.ChapterSolidHarmonic.angular_harmonic
#print axioms BookProof.ChapterSolidHarmonic.angular_euler
#print axioms BookProof.ChapterSolidHarmonic.laplacian_angular_mul_sum
#print axioms BookProof.ChapterSolidHarmonic.legendre_rec_factored
#print axioms BookProof.ChapterSolidHarmonic.solidHarmonic_harmonic
#print axioms BookProof.ChapterSolidHarmonic.solidHarmonicIm_harmonic
#print axioms BookProof.ChapterSolidHarmonic.solidHarmonic_euler
#print axioms BookProof.ChapterSolidHarmonic.solidHarmonicIm_euler
#print axioms BookProof.ChapterSolidHarmonic.radialFactor_eval
#print axioms BookProof.ChapterSolidHarmonic.solidHarmonic_spherical

/-! Note 68 in every mode. -/

#print axioms BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic
#print axioms BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonicIm
#print axioms BookProof.ChapterNote68AllModes.helmholtz_sbessel_solidHarmonic_euclidean
#print axioms BookProof.ChapterNote68AllModes.solidHarmonic_spherical_euclidean
