import BookProof.InducedSystems.ChapterPvmCyclicUnitary
import BookProof.InducedSystems.ChapterMackeyCocycle
import BookProof.InducedSystems.ChapterMackeyConverse
import BookProof.ChapterNumericalRangeCrouzeix
import BookProof.Sirk.ChapterSirkCrouzeixNumericalRange
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the wave that removes the two honest boundaries recorded by the Mackey and
SIRK/Crouzeix chapters:

* over a *continuous* (measure-theoretic) base only the induced direction of Mackey's
  imprimitivity theorem had been formalized, the converse being available only for a
  discrete base;
* Crouzeix's inequality for a *general non-normal* operator, with the numerical range as
  the spectral set and its larger constant, was a named hypothesis of the SIRK chapters.

Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- The spectral theorem for a cyclic projection-valued measure.
#audit_axioms BookProof.ChapterPvmCyclicUnitary.pvm_cyclic_unitary

-- A covariant unitary representation on `L²` is induced by a modulus-one cocycle, and the
-- measure is automatically quasi-invariant.
#audit_axioms BookProof.ChapterMackeyCocycle.quasiInvariant_of_covariant
#audit_axioms BookProof.ChapterMackeyCocycle.dens_eq_enorm_sq
#audit_axioms BookProof.ChapterMackeyCocycle.vmap_eq_tmap
#audit_axioms BookProof.ChapterMackeyCocycle.covariant_unitary_is_induced

-- The converse of Mackey's imprimitivity theorem over a continuous base (cyclic case).
#audit_axioms BookProof.ChapterMackeyConverse.mackey_converse_continuous

-- Crouzeix-type inequalities from the numerical range, for general non-normal operators.
#audit_axioms BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow
#audit_axioms BookProof.ChapterNumericalRangeCrouzeix.norm_le_two_mul_of_numRadiusLE
#audit_axioms BookProof.ChapterNumericalRangeCrouzeix.crouzeix_disc
#audit_axioms BookProof.ChapterNumericalRangeCrouzeix.numBallLE_iff_numRange_subset
#audit_axioms BookProof.ChapterNumericalRangeCrouzeix.crouzeix_ball

-- The SIRK error bound for a general non-normal operator, with no Crouzeix hypothesis.
#audit_axioms BookProof.ChapterSirkCrouzeixNumericalRange.numRadiusLE_compress
#audit_axioms BookProof.ChapterSirkCrouzeixNumericalRange.crouzeix_bound_of_numRadius
#audit_axioms BookProof.ChapterSirkCrouzeixNumericalRange.sirk_error_bound_numericalRange
#audit_axioms BookProof.ChapterSirkCrouzeixNumericalRange.sirk_error_bound_numericalRange_decay
#audit_axioms BookProof.ChapterSirkCrouzeixNumericalRange.numBallLE_compress
#audit_axioms BookProof.ChapterSirkCrouzeixNumericalRange.sirk_error_bound_numericalBall
