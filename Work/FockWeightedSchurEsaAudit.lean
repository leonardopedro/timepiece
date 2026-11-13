import BookProof.Toolbox.ChapterFockWeightedSchurEsa
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the wave that adds the **Schur gate weighted by the one-particle symbol**
(`CONSOLIDATED_PLAN.md`): the relative bound `‖dΓ(A)u‖ ≤ K‖(dΓ(w²)+1)u‖`, the commutator
estimate and essential self-adjointness of `dΓ(A)` on the finite-occupation core for an
**unbounded** one-particle operator.  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- The weighted particle number and the comparison operator on the core.
#audit_axioms BookProof.FockWeightedSchur.wdeg_eq_sum
#audit_axioms BookProof.FockWeightedSchur.ndeg_le_wdeg
#audit_axioms BookProof.FockWeightedSchur.wdeg_up
#audit_axioms BookProof.FockWeightedSchur.annA_wgt
#audit_axioms BookProof.FockWeightedSchur.inner_wgt_symm
#audit_axioms BookProof.FockWeightedSchur.re_inner_wgt
#audit_axioms BookProof.FockWeightedSchur.sum_wsq_normSq_annA

-- The gates.
#audit_axioms BookProof.FockWeightedSchur.wrow_le
#audit_axioms BookProof.FockWeightedSchur.wcol_le
#audit_axioms BookProof.FockWeightedSchur.wcomm_row_le
#audit_axioms BookProof.FockWeightedSchur.wcomm_col_le
#audit_axioms BookProof.FockWeightedSchur.wcomm_nonneg

-- The relative bound.
#audit_axioms BookProof.FockWeightedSchur.normSq_dGamma_le_of_sector
#audit_axioms BookProof.FockWeightedSchur.normSq_dGamma_le_w
#audit_axioms BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w

-- The commutator estimate.
#audit_axioms BookProof.FockWeightedSchur.im_inner_dGamma_wgt_bound
#audit_axioms BookProof.FockWeightedSchur.dGammaOp_commForm_bound_w

-- Essential self-adjointness and the dynamics.
#audit_axioms BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w
#audit_axioms BookProof.FockWeightedSchur.dGamma_stone_flow_w

-- Non-vacuity: the unbounded oscillator matrix.
#audit_axioms BookProof.FockWeightedSchur.isHermCol_oscCol
#audit_axioms BookProof.FockWeightedSchur.wRow_oscCol
#audit_axioms BookProof.FockWeightedSchur.wCol_oscCol
#audit_axioms BookProof.FockWeightedSchur.wComm_oscCol
#audit_axioms BookProof.FockWeightedSchur.oscCol_entries_unbounded
#audit_axioms BookProof.FockWeightedSchur.oscCol_not_schurBound
#audit_axioms BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core
#audit_axioms BookProof.FockWeightedSchur.osc_stone_flow
