import BookProof.Ns.ChapterNsCutoffUniformity
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit — uniformity of the reduced forms under the energy cutoff

Every headline result of `BookProof/Ns/ChapterNsCutoffUniformity.lean` must rest on the standard
axioms only: `propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.NsCutoffUniformity.norm_coeff_redVisc_le
#audit_axioms BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le
#audit_axioms BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le
#audit_axioms BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le
#audit_axioms BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff
#audit_axioms BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le
#audit_axioms BookProof.NsCutoffUniformity.vars_redFormPoly_subset
