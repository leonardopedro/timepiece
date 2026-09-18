import BookProof.ChapterNsCutoffUniformity

/-!
# Axiom audit — uniformity of the reduced forms under the energy cutoff

Every headline result of `BookProof/ChapterNsCutoffUniformity.lean` must rest on the standard
axioms only: `propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.NsCutoffUniformity.norm_coeff_redVisc_le
#print axioms BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le
#print axioms BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le
#print axioms BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le
#print axioms BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff
#print axioms BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le
#print axioms BookProof.NsCutoffUniformity.vars_redFormPoly_subset
