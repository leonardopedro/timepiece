import BookProof.ChapterYangMillsAbelianFockEsa
import BookProof.ChapterSqSumFockEsa

/-!
Axiom audit for the wave that adds the **graded band calculus of the product Hermite basis**
and its consequence: the second quantization `dΓ(H₁)` of a general real quadratic
one-particle Hamiltonian — in particular the **abelian gauge-fixed Yang–Mills Hamiltonian** —
is essentially self-adjoint on the finite-occupation core, so the Yang–Mills single-time
package holds with no diagonalizing-basis hypothesis.  Every result below must report only
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- The band calculus.
#print axioms BookProof.HermiteBand.pgLp_hpsi
#print axioms BookProof.HermiteBand.crePoly_hpsi
#print axioms BookProof.HermiteBand.annPoly_hpsi
#print axioms BookProof.HermiteBand.band_crePoly
#print axioms BookProof.HermiteBand.band_annPoly
#print axioms BookProof.HermiteBand.Band.add
#print axioms BookProof.HermiteBand.Band.smul
#print axioms BookProof.HermiteBand.Band.toBand2
#print axioms BookProof.HermiteBand.Band.comp
#print axioms BookProof.HermiteBand.IsBand1.comp
#print axioms BookProof.HermiteBand.mulXPoly_eq
#print axioms BookProof.HermiteBand.momPoly_eq
#print axioms BookProof.HermiteBand.isBand1_mulXPoly
#print axioms BookProof.HermiteBand.isBand1_momPoly
#print axioms BookProof.HermiteBand.isBand2_weylProd
#print axioms BookProof.HermiteBand.isBand2_fqQuadPoly
#print axioms BookProof.HermiteBand.isBand1_foPoly
#print axioms BookProof.HermiteBand.isBand2_fqPoly

-- The graded band gate.
#print axioms BookProof.GradedBandSchur.wRow_of_gradedBand
#print axioms BookProof.GradedBandSchur.wCol_of_gradedBand
#print axioms BookProof.GradedBandSchur.wComm_of_gradedBand
#print axioms BookProof.GradedBandSchur.dGamma_essentiallySelfAdjointOn_core_gradedBand

-- The seam and the quadratic headline.
#print axioms BookProof.QuadFockEsa.hermBasisN_apply
#print axioms BookProof.QuadFockEsa.finiteModeDomain_hermBasisN
#print axioms BookProof.QuadFockEsa.inner_hermiteMvLp_hcomb
#print axioms BookProof.QuadFockEsa.hermCol_eq_coef
#print axioms BookProof.QuadFockEsa.gradedBand_of_isBand2
#print axioms BookProof.QuadFockEsa.dGamma_hermCol_essentiallySelfAdjointOn_core
#print axioms BookProof.QuadFockEsa.dGamma_fqPoly_essentiallySelfAdjointOn_core

-- The Yang–Mills instance.
#print axioms BookProof.YmAbelianFock.ymAbelianHermOp_eq
#print axioms BookProof.YmAbelianFock.ymAbelianHermCol_eq
#print axioms BookProof.YmAbelianFock.isHermCol_ymAbelianHermCol
#print axioms BookProof.YmAbelianFock.dGamma_ymAbelian_essentiallySelfAdjointOn_core
#print axioms BookProof.YmAbelianFock.ymAbelianFock_friedrichs_extension
#print axioms BookProof.YmAbelianFock.ymAbelianFock_positiveExtension_eq_closure
#print axioms BookProof.YmAbelianFock.ymAbelianFock_timeIndependent_singleTime

-- The sum-of-squares (gravity / Navier–Stokes) instance.
#print axioms BookProof.SqSumFockEsa.dGamma_sqSum_essentiallySelfAdjointOn_core
#print axioms BookProof.SqSumFockEsa.isHermCol_hermCol_sqSum
#print axioms BookProof.SqSumFockEsa.dGamma_sqSum_stone_flow
