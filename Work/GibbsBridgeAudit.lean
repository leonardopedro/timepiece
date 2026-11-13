/-
Axiom audit for `BookProof.OSReconstruction.FiniteVolumeGibbsBridge`.

Every theorem below must rest on `propext`, `Classical.choice`, `Quot.sound` only.  The
construction data (`gibbsLF`, `gibbsCoord`, `gibbsU`, `gibbsBridge`, …) is data, not a theorem.
-/
import BookProof.OSReconstruction.FiniteVolumeGibbsBridge
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction.TwoStateGibbs

#audit_axioms gibbsZ_pos
#audit_axioms gibbsWeight_pos
#audit_axioms gibbsWeight_sum
#audit_axioms fieldReflection_constConfig
#audit_axioms gibbsConfig_injective
#audit_axioms gibbs_osBilin
#audit_axioms gibbs_reflectionPositive
#audit_axioms gibbs_mem_radical_iff
#audit_axioms gibbsDelta_self
#audit_axioms gibbsDelta_of_ne
#audit_axioms gibbsLF_delta
#audit_axioms gibbsDelta_mul
#audit_axioms gibbsLF_delta_mul
#audit_axioms gibbs_not_multiplicative
#audit_axioms gibbsCoord_add
#audit_axioms gibbsCoord_smul
#audit_axioms gibbsCoord_norm_sq
#audit_axioms gibbsCoord_eq_zero_iff
#audit_axioms gibbsQuot_apply_mk
#audit_axioms gibbsQuot_norm
#audit_axioms gibbsQuot_surjective
#audit_axioms gibbsHphysMap_coe
#audit_axioms gibbsHphysMap_norm
#audit_axioms gibbsU_apply_coe
#audit_axioms gibbsU_surjective
#audit_axioms gibbsU_denseRange
#audit_axioms gibbsBridge_twoPoint
#audit_axioms gibbsBridge_norm
