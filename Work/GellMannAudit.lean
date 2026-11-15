/-
Axiom audit for `BookProof.ChapterGellMann` and the su(3) trace lemmas of
`BookProof.Qym.ChapterYangMillsSU3` (SM_ESA_COMPLETION_PLAN §81).

§81 evaluates the gluon first-slot trace `Σ_y f_{ybc}` for the trace-orthonormal Gell-Mann generators:
it does not vanish, and the mechanism is the commutator trace `−2i·tr((S T_b − T_b S) T_c)`.
Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.ChapterGellMann
import BookProof.Qym.ChapterYangMillsSU3
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.ChapterGellMann
open BookProof.YangMillsSU3

#audit_axioms sum_f_eq_trace_commutator
#audit_axioms sum_f_eq_zero_of_sum_gen_eq_zero
#audit_axioms su3genSum
#audit_axioms su3genSum_eq
#audit_axioms su3genSum_ne_zero
#audit_axioms su3gen_firstSlot_zero_one
#audit_axioms su3gen_firstSlot_zero_two
#audit_axioms su3gen_firstSlot_zero_three
#audit_axioms su3gen_firstSlot_zero_seven
#audit_axioms su3gen_firstSlot_four_seven
#audit_axioms su3gen_firstSlot_ne_zero
