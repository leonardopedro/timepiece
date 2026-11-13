import BookProof.Qym.ChapterYangMillsAbelianFockEsa
import BookProof.ChapterSqSumFockEsa
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the wave that adds the **graded band calculus of the product Hermite basis**
and its consequence: the second quantization `dΓ(H₁)` of a general real quadratic
one-particle Hamiltonian — in particular the **abelian gauge-fixed Yang–Mills Hamiltonian** —
is essentially self-adjoint on the finite-occupation core, so the Yang–Mills single-time
package holds with no diagonalizing-basis hypothesis.  Every result below must report only
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- The band calculus.
#audit_axioms BookProof.HermiteBand.pgLp_hpsi
#audit_axioms BookProof.HermiteBand.crePoly_hpsi
#audit_axioms BookProof.HermiteBand.annPoly_hpsi
#audit_axioms BookProof.HermiteBand.band_crePoly
#audit_axioms BookProof.HermiteBand.band_annPoly
#audit_axioms BookProof.HermiteBand.Band.add
#audit_axioms BookProof.HermiteBand.Band.smul
#audit_axioms BookProof.HermiteBand.Band.toBand2
#audit_axioms BookProof.HermiteBand.Band.comp
#audit_axioms BookProof.HermiteBand.IsBand1.comp
#audit_axioms BookProof.HermiteBand.mulXPoly_eq
#audit_axioms BookProof.HermiteBand.momPoly_eq
#audit_axioms BookProof.HermiteBand.isBand1_mulXPoly
#audit_axioms BookProof.HermiteBand.isBand1_momPoly
#audit_axioms BookProof.HermiteBand.isBand2_weylProd
#audit_axioms BookProof.HermiteBand.isBand2_fqQuadPoly
#audit_axioms BookProof.HermiteBand.isBand1_foPoly
#audit_axioms BookProof.HermiteBand.isBand2_fqPoly

-- The graded band gate.
#audit_axioms BookProof.GradedBandSchur.wRow_of_gradedBand
#audit_axioms BookProof.GradedBandSchur.wCol_of_gradedBand
#audit_axioms BookProof.GradedBandSchur.wComm_of_gradedBand
#audit_axioms BookProof.GradedBandSchur.dGamma_essentiallySelfAdjointOn_core_gradedBand

-- The seam and the quadratic headline.
#audit_axioms BookProof.QuadFockEsa.hermBasisN_apply
#audit_axioms BookProof.QuadFockEsa.finiteModeDomain_hermBasisN
#audit_axioms BookProof.QuadFockEsa.inner_hermiteMvLp_hcomb
#audit_axioms BookProof.QuadFockEsa.hermCol_eq_coef
#audit_axioms BookProof.QuadFockEsa.gradedBand_of_isBand2
#audit_axioms BookProof.QuadFockEsa.dGamma_hermCol_essentiallySelfAdjointOn_core
#audit_axioms BookProof.QuadFockEsa.dGamma_fqPoly_essentiallySelfAdjointOn_core

-- The Yang–Mills instance.
#audit_axioms BookProof.YmAbelianFock.ymAbelianHermOp_eq
#audit_axioms BookProof.YmAbelianFock.ymAbelianHermCol_eq
#audit_axioms BookProof.YmAbelianFock.isHermCol_ymAbelianHermCol
#audit_axioms BookProof.YmAbelianFock.dGamma_ymAbelian_essentiallySelfAdjointOn_core
#audit_axioms BookProof.YmAbelianFock.ymAbelianFock_friedrichs_extension
#audit_axioms BookProof.YmAbelianFock.ymAbelianFock_positiveExtension_eq_closure
#audit_axioms BookProof.YmAbelianFock.ymAbelianFock_timeIndependent_singleTime

-- The sum-of-squares (gravity / Navier–Stokes) instance.
#audit_axioms BookProof.SqSumFockEsa.dGamma_sqSum_essentiallySelfAdjointOn_core
#audit_axioms BookProof.SqSumFockEsa.isHermCol_hermCol_sqSum
#audit_axioms BookProof.SqSumFockEsa.dGamma_sqSum_stone_flow
