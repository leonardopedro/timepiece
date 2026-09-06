import BookProof.ChapterYangMillsAbelianEsa
import BookProof.ChapterYangMillsCertificateSeam
import BookProof.ChapterNsOuterFockSingleTime
import BookProof.ChapterNavierStokesEsaConsolidation
import BookProof.ChapterNonnegSemigroup

/-!
Axiom audit for the 2026-09-04g execution wave (`CONSOLIDATED_PLAN.md`): QYM next steps 1–2
and NS next steps 1–2.  Every result below must report only `propext`, `Classical.choice`
and `Quot.sound`.
-/

-- QYM next step 1: the abelian one-particle Hamiltonian.
#print axioms BookProof.YangMillsAbelianEsa.ymAbelian_eq_fqOp
#print axioms BookProof.YangMillsAbelianEsa.ymAbelian_essentiallySelfAdjointOn_core
#print axioms BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure
#print axioms BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects
#print axioms BookProof.YangMillsAbelianEsa.ymAbelian_stone_flow

-- QYM next step 2: the certificate→theorem seam.
#print axioms BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate
#print axioms BookProof.YangMillsCertificateSeam.ym_fock_mass_gap_of_matrix_certificate
#print axioms BookProof.YangMillsCertificateSeam.example_parse
#print axioms BookProof.YangMillsCertificateSeam.example_checkBounds
#print axioms BookProof.YangMillsCertificateSeam.example_ym_fock_gap
#print axioms BookProof.YangMillsCertificateSeam.example_ym_fock_mass_gap

-- NS next step 1: the outer-Fock single-time package.
#print axioms BookProof.SqSumOuterFamily.SqFamily.truncHam_tendsto
#print axioms BookProof.SqSumOuterFamily.SqFamily.outerFamily_timeIndependent_singleTime
#print axioms BookProof.NsOuterFock.nsOuterFock_timeIndependent_singleTime
#print axioms BookProof.NsOuterFock.nsOuterFock_farisLavine_timeIndependent_singleTime

-- NS next step 2: the consolidation index.
#print axioms BookProof.NavierStokesFlow.EsaConsolidation.nsFockOfFock_esa
#print axioms BookProof.NavierStokesFlow.EsaConsolidation.nsDifferential_esa
#print axioms BookProof.NavierStokesFlow.EsaConsolidation.nsOuterFock_esa
#print axioms BookProof.NavierStokesFlow.EsaConsolidation.nsEulerian_not_esa_in_general

-- Operator thread: the contraction semigroup `e^{-tT}`.
#print axioms BookProof.NonnegSemigroup.norm_expNeg_le
#print axioms BookProof.NonnegSemigroup.norm_expNeg_sub_expNeg_le
#print axioms BookProof.NonnegSemigroup.norm_semigroupS_apply_le
#print axioms BookProof.NonnegSemigroup.semigroupS_add
#print axioms BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS
#print axioms BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le
#print axioms BookProof.NonnegSemigroup.tendsto_semigroupS_zero
