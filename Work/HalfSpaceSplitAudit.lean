/-
Axiom audit for the new §8 of `BookProof.ReflectionPositivity.HalfSpaceSplit`.

`cftproof.md` item 3 leaves one bookkeeping step open after §7: rewriting the product `ν ⊗ ν` into
the `fkKernelMeasure … .map Prod.snd` shape §6 consumes.  §8 takes that step in integral form and
concludes reflection positivity of the finite-volume mass model on `Config` with no hypothesis on
the OS form.  Every theorem below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.ReflectionPositivity.HalfSpaceSplit
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.ReflectionPositivity

#audit_axioms sum_sq_split
#audit_axioms configAction_eq_split
#audit_axioms measurePreserving_configSplitEquiv
#audit_axioms splitMap_gffConfigMeasure
#audit_axioms gffHalfDensity_pos
#audit_axioms measurable_halfMassAction
#audit_axioms measurable_gffHalfDensity
#audit_axioms integral_splitMap_gffConfigMeasure
#audit_axioms gffConfigMeasure_osForm_nonneg
#audit_axioms gffConfigMeasure_isReflectionPositive
