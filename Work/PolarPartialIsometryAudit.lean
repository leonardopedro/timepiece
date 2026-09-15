import BookProof.ChapterPolarPartialIsometry

/-!
# Axiom audit for `BookProof.ChapterPolarPartialIsometry`

Run with `lake build Work.PolarPartialIsometryAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.PolarPartialIsometry.initSpace
#print axioms BookProof.PolarPartialIsometry.isClosed_initSpace
#print axioms BookProof.PolarPartialIsometry.range_le_initSpace
#print axioms BookProof.PolarPartialIsometry.preIsom
#print axioms BookProof.PolarPartialIsometry.preIsom_apply
#print axioms BookProof.PolarPartialIsometry.norm_preIsom
#print axioms BookProof.PolarPartialIsometry.preIsomL
#print axioms BookProof.PolarPartialIsometry.inclL
#print axioms BookProof.PolarPartialIsometry.isometry_inclL
#print axioms BookProof.PolarPartialIsometry.isUniformInducing_inclL
#print axioms BookProof.PolarPartialIsometry.denseRange_inclL
#print axioms BookProof.PolarPartialIsometry.polarIsom
#print axioms BookProof.PolarPartialIsometry.polarIsom_apply_of_mem
#print axioms BookProof.PolarPartialIsometry.polarIsom_apply_range
#print axioms BookProof.PolarPartialIsometry.norm_extend
#print axioms BookProof.PolarPartialIsometry.norm_polarIsom_of_mem
#print axioms BookProof.PolarPartialIsometry.polarIsom_eq_zero_of_mem_orthogonal
#print axioms BookProof.PolarPartialIsometry.norm_polarIsom
#print axioms BookProof.PolarPartialIsometry.inner_eq_of_norm_eq_clm
#print axioms BookProof.PolarPartialIsometry.inner_polarIsom
#print axioms BookProof.PolarPartialIsometry.adjoint_comp_polarIsom
#print axioms BookProof.PolarPartialIsometry.adjoint_polarIsom_apply
#print axioms BookProof.PolarPartialIsometry.polarIsom_mem_initSpace
#print axioms BookProof.PolarPartialIsometry.polarIsom_comp_adjoint
#print axioms BookProof.PolarPartialIsometry.polarIsom_unique
#print axioms BookProof.PolarPartialIsometry.polarU
#print axioms BookProof.PolarPartialIsometry.polarU_absOn
#print axioms BookProof.PolarPartialIsometry.adjoint_polarU_clExt
#print axioms BookProof.PolarPartialIsometry.norm_polarU
#print axioms BookProof.PolarPartialIsometry.polarU_eq_zero_of_mem_orthogonal
#print axioms BookProof.PolarPartialIsometry.adjoint_comp_polarU
#print axioms BookProof.PolarPartialIsometry.polarU_comp_adjoint
#print axioms BookProof.PolarPartialIsometry.polarU_unique
#print axioms BookProof.PolarPartialIsometry.absOn_eq_zero_iff
