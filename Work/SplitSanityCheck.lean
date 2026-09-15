import BookProof.ChapterEsaClosure
import BookProof.ChapterClosureUniqueness
import BookProof.ChapterHashimotoComplexShifts
import BookProof.ChapterFarisLavine
import BookProof.ChapterNonnegResolvent

/-!
# Sanity check for the `…Core` split

Importing the split chapters together with their cores must not produce duplicate
declarations, and every name the split moved must still resolve from the old chapter.
-/

open BookProof.FarisLavine BookProof.EsaClosure BookProof.HashimotoShiftInvert

#check @BookProof.FarisLavine.SymmetricOn
#check @BookProof.FarisLavine.EssentiallySelfAdjointOn
#check @BookProof.FarisLavine.essentiallySelfAdjointOn_of_farisLavine
#check @BookProof.FarisLavine.mulHamiltonian_essentiallySelfAdjoint
#check @BookProof.HashimotoShiftInvert.cshiftMap
#check @BookProof.HashimotoShiftInvert.cshiftMap_surjective
#check @BookProof.HashimotoShiftInvert.closed_of_selfAdjointCriterion
#check @BookProof.EsaClosure.clExt
#check @BookProof.EsaClosure.clExt_selfAdjointCriterion
#check @BookProof.EsaClosure.isSelfAdjointExtension_of_positive
#check @BookProof.EsaClosure.positiveExtension_eq_closure_of_esa
#check @BookProof.EsaClosure.hashimoto_multishift_selects_esa
