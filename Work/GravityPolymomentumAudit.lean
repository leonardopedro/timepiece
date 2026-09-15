import BookProof.ChapterGravityPolymomentum

/-!
# Axiom audit for `BookProof.ChapterGravityPolymomentum`

Run with `lake build Work.GravityPolymomentumAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial
#print axioms BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right
#print axioms BookProof.ChapterGravityPolymomentum.proj_metric
#print axioms BookProof.ChapterGravityPolymomentum.proj_polyMom
#print axioms BookProof.ChapterGravityPolymomentum.calA_eq
#print axioms BookProof.ChapterGravityPolymomentum.calP_eq
#print axioms BookProof.ChapterGravityPolymomentum.calS_eq
#print axioms BookProof.ChapterGravityPolymomentum.polyMom_contract_v
#print axioms BookProof.ChapterGravityPolymomentum.polyMom_contract_v_spatial
#print axioms BookProof.ChapterGravityPolymomentum.hamiltonian_momentum_eq_velocity
