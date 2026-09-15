/-
`#print axioms` audit for the module formalizing the book's definition of an
*unconstrained* gauge-fixing (the gauge generators are necessarily excluded from
the commutative von Neumann algebra and impose no constraint on the full spectrum
labelled by the basis vectors), and its satisfiability.  Run on demand:

```
lake build Work.GaugeUnconstrainedSpectrumAudit
```
-/
import BookProof.ChapterGaugeUnconstrainedSpectrum

open BookProof.ChapterGaugeUnconstrainedSpectrum

#print axioms diagOp_mul_comm
#print axioms diagOp_injective
#print axioms permOp_basisVec
#print axioms diagOp_basisVec
#print axioms exists_eigenvalue_of_isFunctionOfSpectrum
#print axioms permOp_isFunctionOfSpectrum_iff
#print axioms constrainedSpectrum_eq_univ_of_isUnconstrained
#print axioms isUnconstrained_of_faithful
#print axioms isUnconstrained_of_movesEveryPoint
#print axioms shiftPerm_movesEveryPoint
#print axioms shift_isUnconstrainedGaugeFixing
#print axioms exists_isUnconstrainedGaugeFixing
#print axioms signRep_isNotUnconstrained
#print axioms signRep_constrainedSpectrum
#print axioms isPhysicalFunction_iff_factors
#print axioms shift_observableSpectrum_subsingleton
#print axioms shift_isPhysicalFunction_const
#print axioms shift_full_spectrum_vs_observable_spectrum
