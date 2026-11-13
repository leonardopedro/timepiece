/-
Axiom audit for §47.5 of `BookProof.SmQuartet` — the physical projector constructed from the
b-ghost (`SM_ESA_COMPLETION_PLAN` §50).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
The construction removes `V` as an assumption: it is computed from `P` by
`physProjOf Q P = 1 − (QP + PQ) + Q P² Q`, and `bGhostOf Q P` restores the anticommutator.
It does **not** construct the Standard Model's own b-ghost, so `PhysicalPositivity` for
`smBrstCharge` stays a hypothesis.
-/
import BookProof.Sm.ChapterSmQuartet

open BookProof.SmQuartet BookProof.SmQuartet.BrstQuartet

#print axioms physProjOf
#print axioms bGhostOf
#print axioms physProjOf_apply
#print axioms bGhostOf_apply
#print axioms QP_idem
#print axioms physProjOf_Q
#print axioms physProjOf_comp_Q
#print axioms QP_physProjOf
#print axioms physProjOf_idem
#print axioms bGhostOf_anticomm
#print axioms quartetOfHomotopy
#print axioms physicalPositivity_of_homotopy
#print axioms physProjOf_commute_parity
#print axioms physProjOf_mem_even
#print axioms physicalPositivity_of_homotopy_sectors
#print axioms exQ_exP_exQ
#print axioms exP_exQ_exP
#print axioms exP_exQ_exP_gives_V
