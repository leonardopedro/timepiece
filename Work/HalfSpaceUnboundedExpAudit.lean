/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceUnboundedExp`.

That module extends the bounded exponential of `HalfSpaceExponential` to an unbounded Hamiltonian in
the spectral/multiplier representation: the flow is `e⁻¹ ∘ e^{−τ f} ∘ e` on `Hhalf Λ`, and its
generator statement holds on the natural domain `{z | f · e z ∈ L²(ν)}`.  Every theorem below must
rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceUnboundedExp
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction
open scoped ENNReal

#audit_axioms HsMulModel.flow_apply
#audit_axioms HsMulModel.flow_zero
#audit_axioms HsMulModel.flow_comp
#audit_axioms HsMulModel.flow_contractive
#audit_axioms HsMulModel.flow_tendsto
#audit_axioms HsMulModel.e_opValue
#audit_axioms HsMulModel.opValue_congr
#audit_axioms HsMulModel.hasDerivWithinAt_flow
#audit_axioms HsMulModel.mem_domain_of_bounded
