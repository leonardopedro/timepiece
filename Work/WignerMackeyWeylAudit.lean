import BookProof.ChapterWeylSl2
import BookProof.ChapterWeylSL2Group
import BookProof.ChapterWignerLittleGroup
import BookProof.ChapterWignerLittleGroupOrbits
import BookProof.ChapterMackeyImprimitivity
import BookProof.ChapterMackeyInducedSystem
import BookProof.ChapterWignerSymmetry
import BookProof.ChapterWignerSymmetryUniqueness

/-!
Axiom audit for the wave that discharges the remaining representation-theoretic
`EXTERNAL` inputs of the book chapter "Real representations, CPT theorem and the
relativistic position operator": **Mackey's imprimitivity theorem** (Note 33 / Note 84)
and **Wigner's little-group classification** (Definition 78 / Proposition 79 and the
massive/massless little groups `SU(2)`, `SE(2)`).
Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Wigner's little-group classification in the `SL(2,ℂ)` model.
#print axioms BookProof.ChapterWignerLittleGroup.hermOfMom_det
#print axioms BookProof.ChapterWignerLittleGroup.hermOfMom_trace
#print axioms BookProof.ChapterWignerLittleGroup.act_det_of_sl
#print axioms BookProof.ChapterWignerLittleGroup.mass_invariant
#print axioms BookProof.ChapterWignerLittleGroup.littleGroup_rest
#print axioms BookProof.ChapterWignerLittleGroup.littleGroup_null
#print axioms BookProof.ChapterWignerLittleGroup.nullElt_mul
#print axioms BookProof.ChapterWignerLittleGroup.nullTranslations_mul
#print axioms BookProof.ChapterWignerLittleGroup.nullTranslations_comm
#print axioms BookProof.ChapterWignerLittleGroup.nullElt_conj_translation
#print axioms BookProof.ChapterWignerLittleGroup.exists_boost_massive
#print axioms BookProof.ChapterWignerLittleGroup.exists_boost_null
#print axioms BookProof.ChapterWignerLittleGroup.littleGroup_conj
#print axioms BookProof.ChapterWignerLittleGroup.littleGroup_massive_conj_SU2
#print axioms BookProof.ChapterWignerLittleGroup.littleGroup_null_conj_SE2

-- Mackey's imprimitivity theorem (transitive discrete case).
#print axioms BookProof.ChapterMackeyImprimitivity.sum_norm_sq_of_orthogonal
#print axioms BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem.pvm_parseval
#print axioms BookProof.ChapterMackeyImprimitivity.mackeyMap_eq
#print axioms BookProof.ChapterMackeyImprimitivity.mackeyMap_mem_inducedSpace
#print axioms BookProof.ChapterMackeyImprimitivity.mackeyMap_norm_sq
#print axioms BookProof.ChapterMackeyImprimitivity.mackeyMap_reconstruct
#print axioms BookProof.ChapterMackeyImprimitivity.mackeyMap_injective
#print axioms BookProof.ChapterMackeyImprimitivity.mackeyMap_surjective
#print axioms BookProof.ChapterMackeyImprimitivity.cocycle_mem_stabilizer
#print axioms BookProof.ChapterMackeyImprimitivity.fibre_stabilizer_invariant
#print axioms BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_U
#print axioms BookProof.ChapterMackeyImprimitivity.mackeyMap_intertwines_pvm
#print axioms BookProof.ChapterMackeyImprimitivity.mackey_imprimitivity

-- Wigner's symmetry theorem.
#print axioms BookProof.ChapterWignerSymmetry.norm_map
#print axioms BookProof.ChapterWignerSymmetry.key_complex
#print axioms BookProof.ChapterWignerSymmetry.key_complex'
#print axioms BookProof.ChapterWignerSymmetry.modulus_add
#print axioms BookProof.ChapterWignerSymmetry.exists_zeta
#print axioms BookProof.ChapterWignerSymmetry.key_index
#print axioms BookProof.ChapterWignerSymmetry.key_consistent
#print axioms BookProof.ChapterWignerSymmetry.key_global
#print axioms BookProof.ChapterWignerSymmetry.coord_of_key
#print axioms BookProof.ChapterWignerSymmetry.wigner_coord
#print axioms BookProof.ChapterWignerSymmetry.orthonormal_imgVec
#print axioms BookProof.ChapterWignerSymmetry.wignerCoord_coordMap
#print axioms BookProof.ChapterWignerSymmetry.wigner_symmetry
#print axioms BookProof.ChapterWignerSymmetry.wigner_symmetry_of_finiteDimensional

-- The converse half of Mackey's theorem: the induced data really form a system of
-- imprimitivity, and the induced system reproduces the representation it came from.
#print axioms BookProof.ChapterMackeyInducedSystem.cocycle_one
#print axioms BookProof.ChapterMackeyInducedSystem.cocycle_mul
#print axioms BookProof.ChapterMackeyInducedSystem.indRepLin_one
#print axioms BookProof.ChapterMackeyInducedSystem.indRepLin_comp
#print axioms BookProof.ChapterMackeyInducedSystem.indRepLin_norm
#print axioms BookProof.ChapterMackeyInducedSystem.indRepHom
#print axioms BookProof.ChapterMackeyInducedSystem.indPvm
#print axioms BookProof.ChapterMackeyInducedSystem.inducedSystem
#print axioms BookProof.ChapterMackeyInducedSystem.inducedSystem_fibre
#print axioms BookProof.ChapterMackeyInducedSystem.inducedSystem_stabilizer_rep
#print axioms BookProof.ChapterMackeyInducedSystem.mackey_correspondence

-- The orbits of the action: energy sign invariance and the complete set of invariants.
#print axioms BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_injective
#print axioms BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_eq_zero_iff
#print axioms BookProof.ChapterWignerLittleGroupOrbits.posSemidef_diag2
#print axioms BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_posSemidef
#print axioms BookProof.ChapterWignerLittleGroupOrbits.act_inv_of_act
#print axioms BookProof.ChapterWignerLittleGroupOrbits.energy_nonneg_of_act
#print axioms BookProof.ChapterWignerLittleGroupOrbits.energy_pos_of_act
#print axioms BookProof.ChapterWignerLittleGroupOrbits.future_cone_invariant
#print axioms BookProof.ChapterWignerLittleGroupOrbits.orbit_iff_massSq_eq
#print axioms BookProof.ChapterWignerLittleGroupOrbits.littleGroup_zero
#print axioms BookProof.ChapterWignerLittleGroupOrbits.littleGroup_spacelike

-- Weyl's complete reducibility theorem, for `sl(2,ℂ)` and for `SL(2,ℂ)`.
#print axioms BookProof.ChapterWeylSl2.Sl2Rep.cas_comm_E
#print axioms BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight
#print axioms BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight
#print axioms BookProof.ChapterWeylSl2.Sl2Rep.codim_one
#print axioms BookProof.ChapterWeylSl2.Sl2Rep.weyl_complete_reducibility
#print axioms BookProof.ChapterWeylSL2Group.coeff_mem_of_poly_mem
#print axioms BookProof.ChapterWeylSL2Group.exists_factorization
#print axioms BookProof.ChapterWeylSL2Group.isInv_of_rho
#print axioms BookProof.ChapterWeylSL2Group.rho_mem_of_unipotent_inv
#print axioms BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2
#print axioms BookProof.ChapterWeylSL2Group.isExpOfSl2_stdRep

-- The uniqueness clause of Wigner's theorem.
#print axioms BookProof.ChapterWignerSymmetryUniqueness.eq_smul_of_forall_eigenvector
#print axioms BookProof.ChapterWignerSymmetryUniqueness.wigner_unique_unitary
#print axioms BookProof.ChapterWignerSymmetryUniqueness.antiunitary_norm_map
#print axioms BookProof.ChapterWignerSymmetryUniqueness.antiunitary_injective
#print axioms BookProof.ChapterWignerSymmetryUniqueness.wigner_unique_antiunitary
#print axioms BookProof.ChapterWignerSymmetryUniqueness.not_linear_and_antiunitary
