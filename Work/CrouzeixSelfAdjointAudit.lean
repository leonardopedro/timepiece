import BookProof.ChapterCrouzeixSelfAdjoint

/-!
Axiom audit for `BookProof.ChapterCrouzeixSelfAdjoint`: Crouzeix's inequality with
constant `1` for normal / self-adjoint operators, and the SIRK error bound with the
Crouzeix hypotheses discharged.  Every result must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

#print axioms BookProof.ChapterCrouzeixSelfAdjoint.norm_cfc_le_of_spectrum_subset
#print axioms BookProof.ChapterCrouzeixSelfAdjoint.norm_cfc_le_of_selfAdjoint
#print axioms BookProof.ChapterCrouzeixSelfAdjoint.spectrum_subset_realSegment
#print axioms BookProof.ChapterCrouzeixSelfAdjoint.crouzeix_realSegment_of_selfAdjoint
#print axioms BookProof.ChapterCrouzeixSelfAdjoint.compress_isSelfAdjoint
#print axioms BookProof.ChapterCrouzeixSelfAdjoint.norm_compress_le
#print axioms BookProof.ChapterCrouzeixSelfAdjoint.sirk_error_bound_selfAdjoint
