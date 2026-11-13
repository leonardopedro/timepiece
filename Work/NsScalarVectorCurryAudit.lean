import BookProof.Ns.ChapterNsScalarVectorCurry
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit — the scalar–vector identification `L²(V; L²(W)) ≅ L²(V × W)`

Every headline result of `BookProof/Ns/ChapterNsScalarVectorCurry.lean` (the residual of item 1 of
the Navier–Stokes plan items) must rest on the standard axioms only: `propext`,
`Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.NsScalarVectorCurry.memLp_mulProd
#audit_axioms BookProof.NsScalarVectorCurry.memLp_smulConst
#audit_axioms BookProof.NsScalarVectorCurry.inner_prodMk
#audit_axioms BookProof.NsScalarVectorCurry.inner_fibMk
#audit_axioms BookProof.NsScalarVectorCurry.inner_prodTensor_eq_inner_fibTensor
#audit_axioms BookProof.NsScalarVectorCurry.norm_prodTensor_eq_norm_fibTensor
#audit_axioms BookProof.NsScalarVectorCurry.fibMk_indicatorConstLp
#audit_axioms BookProof.NsScalarVectorCurry.simpleFunc_mem_range_fibTensor
#audit_axioms BookProof.NsScalarVectorCurry.denseRange_fibTensor
#audit_axioms BookProof.NsScalarVectorCurry.prodMk_indicatorConstLp
#audit_axioms BookProof.NsScalarVectorCurry.ae_eq_zero_of_forall_setIntegral_rect_eq_zero
#audit_axioms BookProof.NsScalarVectorCurry.denseRange_prodTensor
#audit_axioms BookProof.NsScalarVectorCurry.curryLI_fibTensor
#audit_axioms BookProof.NsScalarVectorCurry.curryLI_fibMk
#audit_axioms BookProof.NsScalarVectorCurry.curryLI_indicator_prod
#audit_axioms BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect
#audit_axioms BookProof.NsScalarVectorCurry.eLpNorm_two_sq
#audit_axioms BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq
#audit_axioms BookProof.NsScalarVectorCurry.isSliceOf_fibMk
#audit_axioms BookProof.NsScalarVectorCurry.isSliceOf_fibTensor
#audit_axioms BookProof.NsScalarVectorCurry.isSliceOf_curryLI
