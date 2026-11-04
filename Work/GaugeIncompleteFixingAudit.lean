/-
`#print axioms` audit for the module formalizing the definition of a gauge
symmetry by a comprehensive but incomplete gauge fixing.  Run on demand:

```
lake build Work.GaugeIncompleteFixingAudit
```
-/
import BookProof.ChapterGaugeIncompleteFixing
import BookProof.ChapterGaugeShiftExample

open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeShiftExample

#print axioms univ_isComprehensiveGaugeFixing
#print axioms unconstrained_gauge_fixing_incomplete
#print axioms remnant_faithful
#print axioms no_gauge_invariant_point
#print axioms one_mem_physicalSubalgebra
#print axioms isPhysicalObservable_iff_factors
#print axioms physical_ext_of_comprehensive
#print axioms exists_physical_extension
#print axioms isPhysicalOperator_iff_mem_centralizer
#print axioms expectation_physical_gauge_invariant
#print axioms no_gauge_invariant_unit_vector_of_free
#print axioms shiftOp_unitary
#print axioms shiftOp_commute
#print axioms shiftOp_eq_self_iff
#print axioms no_shift_invariant_unit_vector'
#print axioms shift_gauge_fixing_incomplete
#print axioms expectation_shift_invariant
#print axioms shift_gauge_symmetry_headline
#print axioms chapterG_isUnconstrainedGaugeFixing_vacuous
