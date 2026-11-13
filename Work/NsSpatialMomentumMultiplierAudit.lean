import BookProof.Ns.ChapterNsSpatialMomentumMultiplier
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit — the Plancherel identification and the diagonal spatial derivative

Every headline result of `BookProof/Ns/ChapterNsSpatialMomentumMultiplier.lean` (part of item 1 of
the Navier–Stokes plan items: the momentum-side form of the spatial derivative) must rest on the
standard axioms only: `propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.NsSpatialMultiplier.l2Fourier_norm
#audit_axioms BookProof.NsSpatialMultiplier.l2Fourier_inner
#audit_axioms BookProof.NsSpatialMultiplier.fourier_opL2_eq_mulSymbol
#audit_axioms BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp
#audit_axioms BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp
#audit_axioms BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq
#audit_axioms BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre
#audit_axioms BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre
#audit_axioms BookProof.NsSpatialMultiplier.spatialMomentum_esa
