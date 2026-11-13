import BookProof.GravityAlgebra.ChapterGravityPolymomentum
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterGravityPolymomentum`

Run with `lake build Work.GravityPolymomentumAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial
#audit_axioms BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right
#audit_axioms BookProof.ChapterGravityPolymomentum.proj_metric
#audit_axioms BookProof.ChapterGravityPolymomentum.proj_polyMom
#audit_axioms BookProof.ChapterGravityPolymomentum.calA_eq
#audit_axioms BookProof.ChapterGravityPolymomentum.calP_eq
#audit_axioms BookProof.ChapterGravityPolymomentum.calS_eq
#audit_axioms BookProof.ChapterGravityPolymomentum.polyMom_contract_v
#audit_axioms BookProof.ChapterGravityPolymomentum.polyMom_contract_v_spatial
#audit_axioms BookProof.ChapterGravityPolymomentum.hamiltonian_momentum_eq_velocity
