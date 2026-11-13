/-
`#audit_axioms` audit for the module formalizing the book's definition of an
*unconstrained* gauge-fixing (the gauge generators are necessarily excluded from
the commutative von Neumann algebra and impose no constraint on the full spectrum
labelled by the basis vectors), and its satisfiability.  Run on demand:

```
lake build Work.GaugeUnconstrainedSpectrumAudit
```
-/
import BookProof.ChapterGaugeUnconstrainedSpectrum
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.ChapterGaugeUnconstrainedSpectrum

#audit_axioms diagOp_mul_comm
#audit_axioms diagOp_injective
#audit_axioms permOp_basisVec
#audit_axioms diagOp_basisVec
#audit_axioms exists_eigenvalue_of_isFunctionOfSpectrum
#audit_axioms permOp_isFunctionOfSpectrum_iff
#audit_axioms constrainedSpectrum_eq_univ_of_isUnconstrained
#audit_axioms isUnconstrained_of_faithful
#audit_axioms isUnconstrained_of_movesEveryPoint
#audit_axioms shiftPerm_movesEveryPoint
#audit_axioms shift_isUnconstrainedGaugeFixing
#audit_axioms exists_isUnconstrainedGaugeFixing
#audit_axioms signRep_isNotUnconstrained
#audit_axioms signRep_constrainedSpectrum
#audit_axioms isPhysicalFunction_iff_factors
#audit_axioms shift_observableSpectrum_subsingleton
#audit_axioms shift_isPhysicalFunction_const
#audit_axioms shift_full_spectrum_vs_observable_spectrum
