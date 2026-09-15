import BookProof.ChapterOdeUnitaryFlow

/-!
# Axiom audit for `BookProof.ChapterOdeUnitaryFlow`

Run with `lake build Work.OdeUnitaryFlowAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt
#print axioms BookProof.OdeUnitaryFlow.classicalSol_singular_time
#print axioms BookProof.OdeUnitaryFlow.classicalSol_tendsto_atTop
#print axioms BookProof.OdeUnitaryFlow.mob_neg_eq_classicalSol
#print axioms BookProof.OdeUnitaryFlow.measurableSet_flowDom
#print axioms BookProof.OdeUnitaryFlow.volume_compl_flowDom
#print axioms BookProof.OdeUnitaryFlow.one_sub_mul_mob
#print axioms BookProof.OdeUnitaryFlow.mob_neg_mob
#print axioms BookProof.OdeUnitaryFlow.mob_mob
#print axioms BookProof.OdeUnitaryFlow.odeKoop_add
#print axioms BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop
#print axioms BookProof.OdeUnitaryFlow.hasDerivAt_mob
#print axioms BookProof.OdeUnitaryFlow.injOn_mob
#print axioms BookProof.OdeUnitaryFlow.image_mob
#print axioms BookProof.OdeUnitaryFlow.lintegral_comp_mob
#print axioms BookProof.OdeUnitaryFlow.odeKoop_lintegral_normSq
#print axioms BookProof.OdeUnitaryFlow.odeKoop_conj_mul
#print axioms BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero
#print axioms BookProof.OdeUnitaryFlow.odeKoop_generator
#print axioms BookProof.OdeUnitaryFlow.invMap_invMap
#print axioms BookProof.OdeUnitaryFlow.invMap_mob
#print axioms BookProof.OdeUnitaryFlow.odeKoop_chartW
#print axioms BookProof.OdeUnitaryFlow.hasDerivAt_invMap
#print axioms BookProof.OdeUnitaryFlow.image_invMap
#print axioms BookProof.OdeUnitaryFlow.lintegral_comp_invMap
#print axioms BookProof.OdeUnitaryFlow.chartW_lintegral_normSq
