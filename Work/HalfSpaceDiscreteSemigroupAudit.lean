/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceDiscreteSemigroup`.

That module weakens the half-space evolution API from a real-time group `T τ` to a one-sided,
`ℕ`-indexed semigroup `T n` with `T 0 = 1`, `T (m + n) = T m ∘ T n`, and the contractivity
hypothesis `HsHinvNat` on `𝔄₊`; it also embeds every old `TimeTranslation` into the new API
(`ofTimeTranslation`) and proves that `HsHinv` implies `HsHinvNat` there.  Every theorem below
must rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceDiscreteSemigroup
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms discreteTimeTranslation_zero
#audit_axioms discreteTimeTranslation_semigroup
#audit_axioms hsEvolNat_zero
#audit_axioms hsEvolNat_add
#audit_axioms hsRadical_invariantNat
#audit_axioms hsQuotMapNat_contractive
#audit_axioms hsQuotMapNat_zero
#audit_axioms hsQuotMapNat_add
#audit_axioms hsEvolNat_ofTimeTranslation
#audit_axioms hsHinvNat_of_hsHinv
