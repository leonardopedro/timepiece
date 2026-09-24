import BookProof.ChapterNsScalarVectorCurry

/-!
# Axiom audit — the scalar–vector identification `L²(V; L²(W)) ≅ L²(V × W)`

Every headline result of `BookProof/ChapterNsScalarVectorCurry.lean` (the residual of item 1 of
the Navier–Stokes plan items) must rest on the standard axioms only: `propext`,
`Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.NsScalarVectorCurry.memLp_mulProd
#print axioms BookProof.NsScalarVectorCurry.memLp_smulConst
#print axioms BookProof.NsScalarVectorCurry.inner_prodMk
#print axioms BookProof.NsScalarVectorCurry.inner_fibMk
#print axioms BookProof.NsScalarVectorCurry.inner_prodTensor_eq_inner_fibTensor
#print axioms BookProof.NsScalarVectorCurry.norm_prodTensor_eq_norm_fibTensor
#print axioms BookProof.NsScalarVectorCurry.fibMk_indicatorConstLp
#print axioms BookProof.NsScalarVectorCurry.simpleFunc_mem_range_fibTensor
#print axioms BookProof.NsScalarVectorCurry.denseRange_fibTensor
#print axioms BookProof.NsScalarVectorCurry.prodMk_indicatorConstLp
#print axioms BookProof.NsScalarVectorCurry.ae_eq_zero_of_forall_setIntegral_rect_eq_zero
#print axioms BookProof.NsScalarVectorCurry.denseRange_prodTensor
#print axioms BookProof.NsScalarVectorCurry.curryLI_fibTensor
#print axioms BookProof.NsScalarVectorCurry.curryLI_fibMk
#print axioms BookProof.NsScalarVectorCurry.curryLI_indicator_prod
#print axioms BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect
#print axioms BookProof.NsScalarVectorCurry.eLpNorm_two_sq
#print axioms BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq
#print axioms BookProof.NsScalarVectorCurry.isSliceOf_fibMk
#print axioms BookProof.NsScalarVectorCurry.isSliceOf_fibTensor
#print axioms BookProof.NsScalarVectorCurry.isSliceOf_curryLI
