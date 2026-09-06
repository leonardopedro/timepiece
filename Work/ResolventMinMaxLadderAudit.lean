import BookProof.ChapterResolventMinMaxLadder
import BookProof.ChapterResolventMinMaxEquality

/-!
Axiom audit for the wave that carries the Courant–Fischer ladder to an **unbounded**
non-negative self-adjoint linear relation through its resolvent
(`CONSOLIDATED_PLAN.md`, the QG next step "the min–max ladder through the resolvent").
Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Cauchy–Schwarz for a non-negative bounded form.
#print axioms BookProof.ResolventLadder.sq_le_mul_of_quadratic_nonneg
#print axioms BookProof.ResolventLadder.re_inner_symm_of_selfAdjoint
#print axioms BookProof.ResolventLadder.posForm_cauchy_schwarz
#print axioms BookProof.ResolventLadder.normSq_sq_le_rayleigh_mul

-- The resolvent at `1`.
#print axioms BookProof.ResolventLadder.res_mem
#print axioms BookProof.ResolventLadder.res_eq_of_mem
#print axioms BookProof.ResolventLadder.res_isSelfAdjoint
#print axioms BookProof.ResolventLadder.res_re_inner_nonneg
#print axioms BookProof.ResolventLadder.graph_unique
#print axioms BookProof.ResolventLadder.res_injective

-- The pointwise ladder inequality.
#print axioms BookProof.ResolventLadder.normSq_sq_le_rayleigh_graph
#print axioms BookProof.ResolventLadder.one_le_add_mul_rayleigh_of_unit
#print axioms BookProof.ResolventLadder.inv_sub_one_le_of_rayleigh_le

-- The ladder of a bounded operator, read from the top.
#print axioms BookProof.ResolventLadder.rayleighInfOn_le_maxminLevel
#print axioms BookProof.ResolventLadder.exists_unit_rayleigh_lt
#print axioms BookProof.ResolventLadder.maxminSet_zero_eq_rayleighSet
#print axioms BookProof.ResolventLadder.maxminLevel_zero_eq_sSup_rayleighSet
#print axioms BookProof.ResolventLadder.sSup_rayleighSet_eq_sSup_spectrum

-- The ladder of the relation.
#print axioms BookProof.ResolventLadder.graphRayleighSet_bddAbove
#print axioms BookProof.ResolventLadder.graphMinmaxSet_bddBelow
#print axioms BookProof.ResolventLadder.graphMinmaxSet_nonempty

-- The headlines.
#print axioms BookProof.ResolventLadder.le_graphRayleighSup
#print axioms BookProof.ResolventLadder.resolvent_ladder_lower
#print axioms BookProof.ResolventLadder.maxminLevel_zero_pos
#print axioms BookProof.ResolventLadder.graphMinmaxLevel_zero_eq
#print axioms BookProof.ResolventLadder.graphMinmaxLevel_zero_eq_sSup_spectrum
#print axioms BookProof.ResolventLadder.graphMinmax_gap_lower
#print axioms BookProof.ResolventLadder.graphMinmax_gap_pos

-- The computational side: the Galerkin levels of the resolvent.
#print axioms BookProof.ResolventLadder.minmaxLevel_neg
#print axioms BookProof.ResolventLadder.maxminLevelIn_le_maxminLevel
#print axioms BookProof.ResolventLadder.galerkin_maxminLevel_tendsto
#print axioms BookProof.ResolventLadder.galerkin_maxmin_gap_eventually_pos
#print axioms BookProof.ResolventLadder.graphMinmaxLevel_zero_le_of_computed

-- The reverse ladder inequality: the ladder is an equality at every rung.
#print axioms BookProof.ResolventLadderEq.mul_rayleigh_le_normSq_of_mem_range
#print axioms BookProof.ResolventLadderEq.rayleighVal_le_of_cfc_eq_zero
#print axioms BookProof.ResolventLadderEq.exists_unit_mem_ker_of_no_range_subspace
#print axioms BookProof.ResolventLadderEq.graphMinmaxLevel_le
#print axioms BookProof.ResolventLadderEq.graphMinmaxLevel_eq
#print axioms BookProof.ResolventLadderEq.graphMinmax_gap_eq
