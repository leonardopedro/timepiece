import BookProof.ChapterFockWeightedSchurEsa

/-!
Axiom audit for the wave that adds the **Schur gate weighted by the one-particle symbol**
(`CONSOLIDATED_PLAN.md`): the relative bound `‖dΓ(A)u‖ ≤ K‖(dΓ(w²)+1)u‖`, the commutator
estimate and essential self-adjointness of `dΓ(A)` on the finite-occupation core for an
**unbounded** one-particle operator.  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- The weighted particle number and the comparison operator on the core.
#print axioms BookProof.FockWeightedSchur.wdeg_eq_sum
#print axioms BookProof.FockWeightedSchur.ndeg_le_wdeg
#print axioms BookProof.FockWeightedSchur.wdeg_up
#print axioms BookProof.FockWeightedSchur.annA_wgt
#print axioms BookProof.FockWeightedSchur.inner_wgt_symm
#print axioms BookProof.FockWeightedSchur.re_inner_wgt
#print axioms BookProof.FockWeightedSchur.sum_wsq_normSq_annA

-- The gates.
#print axioms BookProof.FockWeightedSchur.wrow_le
#print axioms BookProof.FockWeightedSchur.wcol_le
#print axioms BookProof.FockWeightedSchur.wcomm_row_le
#print axioms BookProof.FockWeightedSchur.wcomm_col_le
#print axioms BookProof.FockWeightedSchur.wcomm_nonneg

-- The relative bound.
#print axioms BookProof.FockWeightedSchur.normSq_dGamma_le_of_sector
#print axioms BookProof.FockWeightedSchur.normSq_dGamma_le_w
#print axioms BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w

-- The commutator estimate.
#print axioms BookProof.FockWeightedSchur.im_inner_dGamma_wgt_bound
#print axioms BookProof.FockWeightedSchur.dGammaOp_commForm_bound_w

-- Essential self-adjointness and the dynamics.
#print axioms BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w
#print axioms BookProof.FockWeightedSchur.dGamma_stone_flow_w

-- Non-vacuity: the unbounded oscillator matrix.
#print axioms BookProof.FockWeightedSchur.isHermCol_oscCol
#print axioms BookProof.FockWeightedSchur.wRow_oscCol
#print axioms BookProof.FockWeightedSchur.wCol_oscCol
#print axioms BookProof.FockWeightedSchur.wComm_oscCol
#print axioms BookProof.FockWeightedSchur.oscCol_entries_unbounded
#print axioms BookProof.FockWeightedSchur.oscCol_not_schurBound
#print axioms BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core
#print axioms BookProof.FockWeightedSchur.osc_stone_flow
