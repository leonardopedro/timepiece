import BookProof.ChapterOrthogonalSums
import BookProof.ChapterMackeyGeneralBase
import BookProof.ChapterWignerSymmetryInfinite
import BookProof.ChapterWignerOrbitClassification
import BookProof.ChapterWeylSL2Unipotent
import BookProof.ChapterMackeyQuasiInvariant
import BookProof.ChapterMackeyQuasiInvariantSigma
import BookProof.ChapterMackeyTranslation

/-!
Axiom audit for the wave that removes the four honest boundaries recorded with the
Mackey / Wigner / Weyl wave: Mackey's imprimitivity theorem over an arbitrary transitive
base (no chosen section, no finiteness), Wigner's symmetry theorem in an arbitrary complex
Hilbert space, transitivity of the Lorentz action on the spacelike shells together with
the complete orbit classification, and Weyl's complete reducibility theorem for `SL(2,ℂ)`
with the `sl₂`-triple *derived* from unipotence of the two one-parameter subgroups.
Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Unconditional sums of orthogonal families (the infinite-dimensional toolbox).
#print axioms BookProof.ChapterOrthogonalSums.norm_sum_sq_of_orthogonal
#print axioms BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq
#print axioms BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum
#print axioms BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq

-- Mackey's imprimitivity theorem over an arbitrary transitive base.
#print axioms BookProof.ChapterMackeyGeneralBase.mackey_imprimitivity_general

-- Wigner's symmetry theorem in an arbitrary complex Hilbert space.
#print axioms BookProof.ChapterWignerSymmetryInfinite.wigner_symmetry_hilbert
#print axioms BookProof.ChapterWignerSymmetryInfinite.wigner_symmetry_of_completeSpace

-- Transitivity on the spacelike shells and the complete orbit classification.
#print axioms BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike
#print axioms BookProof.ChapterWignerOrbitClassification.sameOrbit_spacelike
#print axioms BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11
#print axioms BookProof.ChapterWignerOrbitClassification.orbit_classification

-- Weyl's theorem for `SL(2,ℂ)` with the `sl₂`-triple derived from the group law.
#print axioms BookProof.ChapterWeylSL2Unipotent.dMat_factor
#print axioms BookProof.ChapterWeylSL2Unipotent.bruhat
#print axioms BookProof.ChapterWeylSL2Unipotent.dPoly_mul_C_E
#print axioms BookProof.ChapterWeylSL2Unipotent.dPoly_mul_C_F
#print axioms BookProof.ChapterWeylSL2Unipotent.cartan_mul_E
#print axioms BookProof.ChapterWeylSL2Unipotent.cartan_mul_F
#print axioms BookProof.ChapterWeylSL2Unipotent.bruhat_poly
#print axioms BookProof.ChapterWeylSL2Unipotent.cartan_eq_commutator
#print axioms BookProof.ChapterWeylSL2Unipotent.sl2_relations_of_unipotent
#print axioms BookProof.ChapterWeylSL2Unipotent.isUnipotentExp_stdRep
#print axioms BookProof.ChapterWeylSL2Unipotent.weyl_complete_reducibility_SL2_unipotent

-- Mackey's induced system of imprimitivity over a continuous base with a quasi-invariant
-- measure (the last restriction left by `ChapterMackeyGeneralBase`, whose base is discrete).
#print axioms BookProof.ChapterMackeyQuasiInvariant.lintegral_dens_mul
#print axioms BookProof.ChapterMackeyQuasiInvariant.dens_one
#print axioms BookProof.ChapterMackeyQuasiInvariant.dens_mul
#print axioms BookProof.ChapterMackeyQuasiInvariant.vmap_norm
#print axioms BookProof.ChapterMackeyQuasiInvariant.vmap_mul
#print axioms BookProof.ChapterMackeyQuasiInvariant.inducedRep
#print axioms BookProof.ChapterMackeyQuasiInvariant.proj_idem
#print axioms BookProof.ChapterMackeyQuasiInvariant.proj_symm
#print axioms BookProof.ChapterMackeyQuasiInvariant.inducedSystem_covariance
#print axioms BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous
#print axioms BookProof.ChapterMackeyQuasiInvariant.unitaryCocycle_one

-- Countable additivity of the continuous-base projection-valued measure.
#print axioms BookProof.ChapterMackeyQuasiInvariant.norm_sq_proj
#print axioms BookProof.ChapterMackeyQuasiInvariant.proj_orthogonal
#print axioms BookProof.ChapterMackeyQuasiInvariant.proj_hasSum_iUnion

-- The concrete continuous-base instance: translations and the localization observable.
#print axioms BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_translation
#print axioms BookProof.ChapterMackeyQuasiInvariant.dens_translation
#print axioms BookProof.ChapterMackeyQuasiInvariant.translation_inducedSystem
#print axioms BookProof.ChapterMackeyQuasiInvariant.position_system_R3
#print axioms BookProof.ChapterMackeyQuasiInvariant.position_pvm_countably_additive_R3
