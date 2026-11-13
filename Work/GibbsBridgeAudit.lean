/-
Axiom audit for `BookProof.OSReconstruction.FiniteVolumeGibbsBridge`.

Every theorem below must rest on `propext`, `Classical.choice`, `Quot.sound` only.  The
construction data (`gibbsLF`, `gibbsCoord`, `gibbsU`, `gibbsBridge`, …) is data, not a theorem.
-/
import BookProof.OSReconstruction.FiniteVolumeGibbsBridge

open BookProof.OSReconstruction.TwoStateGibbs

#print axioms gibbsZ_pos
#print axioms gibbsWeight_pos
#print axioms gibbsWeight_sum
#print axioms fieldReflection_constConfig
#print axioms gibbsConfig_injective
#print axioms gibbs_osBilin
#print axioms gibbs_reflectionPositive
#print axioms gibbs_mem_radical_iff
#print axioms gibbsDelta_self
#print axioms gibbsDelta_of_ne
#print axioms gibbsLF_delta
#print axioms gibbsDelta_mul
#print axioms gibbsLF_delta_mul
#print axioms gibbs_not_multiplicative
#print axioms gibbsCoord_add
#print axioms gibbsCoord_smul
#print axioms gibbsCoord_norm_sq
#print axioms gibbsCoord_eq_zero_iff
#print axioms gibbsQuot_apply_mk
#print axioms gibbsQuot_norm
#print axioms gibbsQuot_surjective
#print axioms gibbsHphysMap_coe
#print axioms gibbsHphysMap_norm
#print axioms gibbsU_apply_coe
#print axioms gibbsU_surjective
#print axioms gibbsU_denseRange
#print axioms gibbsBridge_twoPoint
#print axioms gibbsBridge_norm
