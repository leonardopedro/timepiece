import BookProof.Toolbox.ChapterResolventMinMaxLadder
import BookProof.Toolbox.ChapterResolventMinMaxEquality
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the wave that carries the Courant–Fischer ladder to an **unbounded**
non-negative self-adjoint linear relation through its resolvent
(`CONSOLIDATED_PLAN.md`, the QG next step "the min–max ladder through the resolvent").
Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Cauchy–Schwarz for a non-negative bounded form.
#audit_axioms BookProof.ResolventLadder.sq_le_mul_of_quadratic_nonneg
#audit_axioms BookProof.ResolventLadder.re_inner_symm_of_selfAdjoint
#audit_axioms BookProof.ResolventLadder.posForm_cauchy_schwarz
#audit_axioms BookProof.ResolventLadder.normSq_sq_le_rayleigh_mul

-- The resolvent at `1`.
#audit_axioms BookProof.ResolventLadder.res_mem
#audit_axioms BookProof.ResolventLadder.res_eq_of_mem
#audit_axioms BookProof.ResolventLadder.res_isSelfAdjoint
#audit_axioms BookProof.ResolventLadder.res_re_inner_nonneg
#audit_axioms BookProof.ResolventLadder.graph_unique
#audit_axioms BookProof.ResolventLadder.res_injective

-- The pointwise ladder inequality.
#audit_axioms BookProof.ResolventLadder.normSq_sq_le_rayleigh_graph
#audit_axioms BookProof.ResolventLadder.one_le_add_mul_rayleigh_of_unit
#audit_axioms BookProof.ResolventLadder.inv_sub_one_le_of_rayleigh_le

-- The ladder of a bounded operator, read from the top.
#audit_axioms BookProof.ResolventLadder.rayleighInfOn_le_maxminLevel
#audit_axioms BookProof.ResolventLadder.exists_unit_rayleigh_lt
#audit_axioms BookProof.ResolventLadder.maxminSet_zero_eq_rayleighSet
#audit_axioms BookProof.ResolventLadder.maxminLevel_zero_eq_sSup_rayleighSet
#audit_axioms BookProof.ResolventLadder.sSup_rayleighSet_eq_sSup_spectrum

-- The ladder of the relation.
#audit_axioms BookProof.ResolventLadder.graphRayleighSet_bddAbove
#audit_axioms BookProof.ResolventLadder.graphMinmaxSet_bddBelow
#audit_axioms BookProof.ResolventLadder.graphMinmaxSet_nonempty

-- The headlines.
#audit_axioms BookProof.ResolventLadder.le_graphRayleighSup
#audit_axioms BookProof.ResolventLadder.resolvent_ladder_lower
#audit_axioms BookProof.ResolventLadder.maxminLevel_zero_pos
#audit_axioms BookProof.ResolventLadder.graphMinmaxLevel_zero_eq
#audit_axioms BookProof.ResolventLadder.graphMinmaxLevel_zero_eq_sSup_spectrum
#audit_axioms BookProof.ResolventLadder.graphMinmax_gap_lower
#audit_axioms BookProof.ResolventLadder.graphMinmax_gap_pos

-- The computational side: the Galerkin levels of the resolvent.
#audit_axioms BookProof.ResolventLadder.minmaxLevel_neg
#audit_axioms BookProof.ResolventLadder.maxminLevelIn_le_maxminLevel
#audit_axioms BookProof.ResolventLadder.galerkin_maxminLevel_tendsto
#audit_axioms BookProof.ResolventLadder.galerkin_maxmin_gap_eventually_pos
#audit_axioms BookProof.ResolventLadder.graphMinmaxLevel_zero_le_of_computed

-- The reverse ladder inequality: the ladder is an equality at every rung.
#audit_axioms BookProof.ResolventLadderEq.mul_rayleigh_le_normSq_of_mem_range
#audit_axioms BookProof.ResolventLadderEq.rayleighVal_le_of_cfc_eq_zero
#audit_axioms BookProof.ResolventLadderEq.exists_unit_mem_ker_of_no_range_subspace
#audit_axioms BookProof.ResolventLadderEq.graphMinmaxLevel_le
#audit_axioms BookProof.ResolventLadderEq.graphMinmaxLevel_eq
#audit_axioms BookProof.ResolventLadderEq.graphMinmax_gap_eq
