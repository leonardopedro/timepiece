/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceMultiplierAdjoint`.

That module closes the two facts `HalfSpaceUnboundedExp` left open about the unbounded Hamiltonian
`H = −M_f`: for every measurable real `f` its natural domain `{z | f · e z ∈ L²(ν)}` is dense
(`dense_domain`), and `H` is self-adjoint (`hamiltonian_isSelfAdjoint`), via symmetry plus the
truncation argument `H† ≤ H` (`le_adjoint_hamiltonian`).  Every theorem below must rest on
`propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceMultiplierAdjoint
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction
open scoped ENNReal

#audit_axioms HsMulModel.norm_sq_eq_integral
#audit_axioms HsMulModel.abs_weight_le_one
#audit_axioms HsMulModel.abs_f_mul_weight_le_one
#audit_axioms HsMulModel.memLp_weight_mul
#audit_axioms HsMulModel.memLp_f_mul_weight_mul
#audit_axioms HsMulModel.truncFun_f_memLp
#audit_axioms HsMulModel.tendsto_truncFun_toLp
#audit_axioms HsMulModel.dense_memLp_mul_l2
#audit_axioms HsMulModel.dense_domain
#audit_axioms HsMulModel.e_hamiltonian
#audit_axioms HsMulModel.inner_hamiltonian_left
#audit_axioms HsMulModel.inner_hamiltonian_right
#audit_axioms HsMulModel.isFormalAdjoint_hamiltonian
#audit_axioms HsMulModel.mem_domain_of_mem_adjoint_domain
#audit_axioms HsMulModel.hamiltonian_adjoint_apply_eq
#audit_axioms HsMulModel.le_adjoint_hamiltonian
#audit_axioms HsMulModel.hamiltonian_isSelfAdjoint
