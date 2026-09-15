import BookProof.ChapterYangMillsFockFriedrichs
import BookProof.ChapterScalaronNotQuadratic
import BookProof.ChapterEsaFarisLavineIndex

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
#print axioms BookProof.YmFockFriedrichs.gaussPolyN_eval
#print axioms BookProof.YmFockFriedrichs.ymSectorHam_symmetricOn
#print axioms BookProof.YmFockFriedrichs.ymSectorHam_quadForm_nonneg
#print axioms BookProof.YmFockFriedrichs.ymSector_friedrichs_extension
#print axioms BookProof.YmFockFriedrichs.ymFockCore_dense
#print axioms BookProof.YmFockFriedrichs.ymFockHam_symmetricOn
#print axioms BookProof.YmFockFriedrichs.ymFockHam_quadForm_nonneg
#print axioms BookProof.YmFockFriedrichs.ymFock_friedrichs_extension
#print axioms BookProof.YmFockFriedrichs.ymFock_stone_flow
#print axioms BookProof.YmFockFriedrichs.ymFockHam_number_conserving

-- The scalaron obstruction.
#print axioms BookProof.ScalaronNotQuadratic.starobinskyV_le_plateau
#print axioms BookProof.ScalaronNotQuadratic.starobinskyV_pos
#print axioms BookProof.ScalaronNotQuadratic.starobinskyV_not_quadratic
#print axioms BookProof.ScalaronNotQuadratic.starobinskyPot_not_quadratic
#print axioms BookProof.ScalaronNotQuadratic.starobinskyPot_not_sum_of_squares

-- The index entries.
#print axioms BookProof.EsaFarisLavineIndex.ym_fock_bddBelow
#print axioms BookProof.EsaFarisLavineIndex.ym_fock_friedrichs
#print axioms BookProof.EsaFarisLavineIndex.ym_fock_stone_flow
