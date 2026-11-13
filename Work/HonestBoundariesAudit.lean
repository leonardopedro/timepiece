import BookProof.InducedSystems.ChapterOrthogonalSums
import BookProof.InducedSystems.ChapterMackeyGeneralBase
import BookProof.InducedSystems.ChapterWignerSymmetryInfinite
import BookProof.WignerOrbit.ChapterWignerOrbitClassification
import BookProof.WeylSL2.ChapterWeylSL2Unipotent
import BookProof.InducedSystems.ChapterMackeyQuasiInvariant
import BookProof.InducedSystems.ChapterMackeyQuasiInvariantSigma
import BookProof.InducedSystems.ChapterMackeyTranslation
import BookProof.RoadmapAudit.AxiomAudit

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
#audit_axioms BookProof.ChapterOrthogonalSums.norm_sum_sq_of_orthogonal
#audit_axioms BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq
#audit_axioms BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum
#audit_axioms BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq

-- Mackey's imprimitivity theorem over an arbitrary transitive base.
#audit_axioms BookProof.ChapterMackeyGeneralBase.mackey_imprimitivity_general

-- Wigner's symmetry theorem in an arbitrary complex Hilbert space.
#audit_axioms BookProof.ChapterWignerSymmetryInfinite.wigner_symmetry_hilbert
#audit_axioms BookProof.ChapterWignerSymmetryInfinite.wigner_symmetry_of_completeSpace

-- Transitivity on the spacelike shells and the complete orbit classification.
#audit_axioms BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike
#audit_axioms BookProof.ChapterWignerOrbitClassification.sameOrbit_spacelike
#audit_axioms BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11
#audit_axioms BookProof.ChapterWignerOrbitClassification.orbit_classification

-- Weyl's theorem for `SL(2,ℂ)` with the `sl₂`-triple derived from the group law.
#audit_axioms BookProof.ChapterWeylSL2Unipotent.dMat_factor
#audit_axioms BookProof.ChapterWeylSL2Unipotent.bruhat
#audit_axioms BookProof.ChapterWeylSL2Unipotent.dPoly_mul_C_E
#audit_axioms BookProof.ChapterWeylSL2Unipotent.dPoly_mul_C_F
#audit_axioms BookProof.ChapterWeylSL2Unipotent.cartan_mul_E
#audit_axioms BookProof.ChapterWeylSL2Unipotent.cartan_mul_F
#audit_axioms BookProof.ChapterWeylSL2Unipotent.bruhat_poly
#audit_axioms BookProof.ChapterWeylSL2Unipotent.cartan_eq_commutator
#audit_axioms BookProof.ChapterWeylSL2Unipotent.sl2_relations_of_unipotent
#audit_axioms BookProof.ChapterWeylSL2Unipotent.isUnipotentExp_stdRep
#audit_axioms BookProof.ChapterWeylSL2Unipotent.weyl_complete_reducibility_SL2_unipotent

-- Mackey's induced system of imprimitivity over a continuous base with a quasi-invariant
-- measure (the last restriction left by `ChapterMackeyGeneralBase`, whose base is discrete).
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.lintegral_dens_mul
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.dens_one
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.dens_mul
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.vmap_norm
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.vmap_mul
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.inducedRep
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.proj_idem
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.proj_symm
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.inducedSystem_covariance
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.mackey_inducedSystem_continuous
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.unitaryCocycle_one

-- Countable additivity of the continuous-base projection-valued measure.
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.norm_sq_proj
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.proj_orthogonal
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.proj_hasSum_iUnion

-- The concrete continuous-base instance: translations and the localization observable.
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.quasiInvariant_translation
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.dens_translation
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.translation_inducedSystem
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.position_system_R3
#audit_axioms BookProof.ChapterMackeyQuasiInvariant.position_pvm_countably_additive_R3
