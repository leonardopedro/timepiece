import BookProof.Ode.ChapterOdeUnitaryFlow
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterOdeUnitaryFlow`

Run with `lake build Work.OdeUnitaryFlowAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.OdeUnitaryFlow.classicalSol_hasDerivAt
#audit_axioms BookProof.OdeUnitaryFlow.classicalSol_singular_time
#audit_axioms BookProof.OdeUnitaryFlow.classicalSol_tendsto_atTop
#audit_axioms BookProof.OdeUnitaryFlow.mob_neg_eq_classicalSol
#audit_axioms BookProof.OdeUnitaryFlow.measurableSet_flowDom
#audit_axioms BookProof.OdeUnitaryFlow.volume_compl_flowDom
#audit_axioms BookProof.OdeUnitaryFlow.one_sub_mul_mob
#audit_axioms BookProof.OdeUnitaryFlow.mob_neg_mob
#audit_axioms BookProof.OdeUnitaryFlow.mob_mob
#audit_axioms BookProof.OdeUnitaryFlow.odeKoop_add
#audit_axioms BookProof.OdeUnitaryFlow.odeKoop_neg_odeKoop
#audit_axioms BookProof.OdeUnitaryFlow.hasDerivAt_mob
#audit_axioms BookProof.OdeUnitaryFlow.injOn_mob
#audit_axioms BookProof.OdeUnitaryFlow.image_mob
#audit_axioms BookProof.OdeUnitaryFlow.lintegral_comp_mob
#audit_axioms BookProof.OdeUnitaryFlow.odeKoop_lintegral_normSq
#audit_axioms BookProof.OdeUnitaryFlow.odeKoop_conj_mul
#audit_axioms BookProof.OdeUnitaryFlow.hasDerivAt_odeKoop_zero
#audit_axioms BookProof.OdeUnitaryFlow.odeKoop_generator
#audit_axioms BookProof.OdeUnitaryFlow.invMap_invMap
#audit_axioms BookProof.OdeUnitaryFlow.invMap_mob
#audit_axioms BookProof.OdeUnitaryFlow.odeKoop_chartW
#audit_axioms BookProof.OdeUnitaryFlow.hasDerivAt_invMap
#audit_axioms BookProof.OdeUnitaryFlow.image_invMap
#audit_axioms BookProof.OdeUnitaryFlow.lintegral_comp_invMap
#audit_axioms BookProof.OdeUnitaryFlow.chartW_lintegral_normSq
