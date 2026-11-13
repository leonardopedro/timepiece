import BookProof.Qym.ChapterYangMillsFockFriedrichs
import BookProof.Qg.ChapterScalaronNotQuadratic
import BookProof.ChapterEsaFarisLavineIndex
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the 2026-09-12 wave:

* quantum Yang–Mills on the nested Fock space by the **direct Friedrichs extension** — the
  Hamiltonian is bounded below, so no Faris–Lavine certificate is needed — at arbitrary real
  structure constants (the quartic, non-abelian case included), with the 3D gauge fixing in
  the independent derivative coordinates, together with its unitary flow and its
  particle-number conservation;
* the obstruction that keeps the gravity Hamiltonian **with** the full exponential scalaron
  potential out of the kinetic-plus-squares class.

Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Yang–Mills: bounded below, Friedrichs, Stone, number conservation.
#audit_axioms BookProof.YmFockFriedrichs.gaussPolyN_eval
#audit_axioms BookProof.YmFockFriedrichs.ymSectorHam_symmetricOn
#audit_axioms BookProof.YmFockFriedrichs.ymSectorHam_quadForm_nonneg
#audit_axioms BookProof.YmFockFriedrichs.ymSector_friedrichs_extension
#audit_axioms BookProof.YmFockFriedrichs.ymFockCore_dense
#audit_axioms BookProof.YmFockFriedrichs.ymFockHam_symmetricOn
#audit_axioms BookProof.YmFockFriedrichs.ymFockHam_quadForm_nonneg
#audit_axioms BookProof.YmFockFriedrichs.ymFock_friedrichs_extension
#audit_axioms BookProof.YmFockFriedrichs.ymFock_stone_flow
#audit_axioms BookProof.YmFockFriedrichs.ymFockHam_number_conserving

-- The scalaron obstruction.
#audit_axioms BookProof.ScalaronNotQuadratic.starobinskyV_le_plateau
#audit_axioms BookProof.ScalaronNotQuadratic.starobinskyV_pos
#audit_axioms BookProof.ScalaronNotQuadratic.starobinskyV_not_quadratic
#audit_axioms BookProof.ScalaronNotQuadratic.starobinskyPot_not_quadratic
#audit_axioms BookProof.ScalaronNotQuadratic.starobinskyPot_not_sum_of_squares

-- The index entries.
#audit_axioms BookProof.EsaFarisLavineIndex.ym_fock_bddBelow
#audit_axioms BookProof.EsaFarisLavineIndex.ym_fock_friedrichs
#audit_axioms BookProof.EsaFarisLavineIndex.ym_fock_stone_flow
