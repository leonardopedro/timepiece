import BookProof.Qym.ChapterYangMillsAbelianEsa
import BookProof.Qym.ChapterYangMillsCertificateSeam
import BookProof.Ns.ChapterNsOuterFockSingleTime
import BookProof.Ns.ChapterNavierStokesEsaConsolidation
import BookProof.ChapterNonnegSemigroup
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the 2026-09-04g execution wave (`CONSOLIDATED_PLAN.md`): QYM next steps 1–2
and NS next steps 1–2.  Every result below must report only `propext`, `Classical.choice`
and `Quot.sound`.
-/

-- QYM next step 1: the abelian one-particle Hamiltonian.
#audit_axioms BookProof.YangMillsAbelianEsa.ymAbelian_eq_fqOp
#audit_axioms BookProof.YangMillsAbelianEsa.ymAbelian_essentiallySelfAdjointOn_core
#audit_axioms BookProof.YangMillsAbelianEsa.ymAbelian_positiveExtension_eq_closure
#audit_axioms BookProof.YangMillsAbelianEsa.ymAbelian_hashimoto_selects
#audit_axioms BookProof.YangMillsAbelianEsa.ymAbelian_stone_flow

-- QYM next step 2: the certificate→theorem seam.
#audit_axioms BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate
#audit_axioms BookProof.YangMillsCertificateSeam.ym_fock_mass_gap_of_matrix_certificate
#audit_axioms BookProof.YangMillsCertificateSeam.example_parse
#audit_axioms BookProof.YangMillsCertificateSeam.example_checkBounds
#audit_axioms BookProof.YangMillsCertificateSeam.example_ym_fock_gap
#audit_axioms BookProof.YangMillsCertificateSeam.example_ym_fock_mass_gap

-- NS next step 1: the outer-Fock single-time package.
#audit_axioms BookProof.SqSumOuterFamily.SqFamily.truncHam_tendsto
#audit_axioms BookProof.SqSumOuterFamily.SqFamily.outerFamily_timeIndependent_singleTime
#audit_axioms BookProof.NsOuterFock.nsOuterFock_timeIndependent_singleTime
#audit_axioms BookProof.NsOuterFock.nsOuterFock_farisLavine_timeIndependent_singleTime

-- NS next step 2: the consolidation index.
#audit_axioms BookProof.NavierStokesFlow.EsaConsolidation.nsFockOfFock_esa
#audit_axioms BookProof.NavierStokesFlow.EsaConsolidation.nsDifferential_esa
#audit_axioms BookProof.NavierStokesFlow.EsaConsolidation.nsOuterFock_esa
#audit_axioms BookProof.NavierStokesFlow.EsaConsolidation.nsEulerian_not_esa_in_general

-- Operator thread: the contraction semigroup `e^{-tT}`.
#audit_axioms BookProof.NonnegSemigroup.norm_expNeg_le
#audit_axioms BookProof.NonnegSemigroup.norm_expNeg_sub_expNeg_le
#audit_axioms BookProof.NonnegSemigroup.norm_semigroupS_apply_le
#audit_axioms BookProof.NonnegSemigroup.semigroupS_add
#audit_axioms BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS
#audit_axioms BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le
#audit_axioms BookProof.NonnegSemigroup.tendsto_semigroupS_zero
