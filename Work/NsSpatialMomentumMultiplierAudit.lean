import BookProof.ChapterNsSpatialMomentumMultiplier

/-!
# Axiom audit — the Plancherel identification and the diagonal spatial derivative

Every headline result of `BookProof/ChapterNsSpatialMomentumMultiplier.lean` (part of item 1 of
the Navier–Stokes plan items: the momentum-side form of the spatial derivative) must rest on the
standard axioms only: `propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.NsSpatialMultiplier.l2Fourier_norm
#print axioms BookProof.NsSpatialMultiplier.l2Fourier_inner
#print axioms BookProof.NsSpatialMultiplier.fourier_opL2_eq_mulSymbol
#print axioms BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp
#print axioms BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp
#print axioms BookProof.NsSpatialMultiplier.foSymbolFn_congr_of_inner_eq
#print axioms BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre
#print axioms BookProof.NsSpatialMultiplier.euclidean_foSymbolFn_add_fibre
#print axioms BookProof.NsSpatialMultiplier.spatialMomentum_esa
