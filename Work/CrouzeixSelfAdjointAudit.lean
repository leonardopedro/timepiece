import BookProof.Sirk.ChapterCrouzeixSelfAdjoint
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for `BookProof.ChapterCrouzeixSelfAdjoint`: Crouzeix's inequality with
constant `1` for normal / self-adjoint operators, and the SIRK error bound with the
Crouzeix hypotheses discharged.  Every result must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

#audit_axioms BookProof.ChapterCrouzeixSelfAdjoint.norm_cfc_le_of_spectrum_subset
#audit_axioms BookProof.ChapterCrouzeixSelfAdjoint.norm_cfc_le_of_selfAdjoint
#audit_axioms BookProof.ChapterCrouzeixSelfAdjoint.spectrum_subset_realSegment
#audit_axioms BookProof.ChapterCrouzeixSelfAdjoint.crouzeix_realSegment_of_selfAdjoint
#audit_axioms BookProof.ChapterCrouzeixSelfAdjoint.compress_isSelfAdjoint
#audit_axioms BookProof.ChapterCrouzeixSelfAdjoint.norm_compress_le
#audit_axioms BookProof.ChapterCrouzeixSelfAdjoint.sirk_error_bound_selfAdjoint
