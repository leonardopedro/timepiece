import BookProof.ChapterSchurFiniteDimensional

/-!
Axiom audit for Lemma 20 (Schur's lemma for finite-dimensional representations, with no
normality hypothesis) and the core of Lemma 21 (the square of a commuting anti-unitary is
`±1`) of the chapter *"Real representations, CPT theorem and the relativistic position
operator"* of `book.tex`.

Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms BookProof.ChapterSchurFiniteDimensional.isSchurFull_of_irreducible_finiteDimensional
#print axioms BookProof.ChapterSchurFiniteDimensional.isSchurUnitary_of_irreducible_finiteDimensional
#print axioms BookProof.ChapterSchurFiniteDimensional.antiUnitary_sq_of_irreducible_finiteDimensional
#print axioms BookProof.ChapterSchurFiniteDimensional.isConjugation_or_sq_eq_neg_one
#print axioms BookProof.ChapterSchurFiniteDimensional.Rreal_commutant_eq_real_scalars_finiteDimensional
