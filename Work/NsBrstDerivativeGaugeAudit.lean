import BookProof.Ns.ChapterNsBrstDerivativeGauge
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the BRST charge of the Navier–Stokes **derivative gauge** — the gauge fixing
of the variables that represent the spatial derivatives of the velocity field — and for its
commutator with the Navier–Stokes Hamiltonian.  Every result below must report only
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- The ghost sector and the graded state space.
#audit_axioms BookProof.NsBrstDerivativeGauge.nsGhost_car
#audit_axioms BookProof.NsBrstDerivativeGauge.nsBos_nsGh_comm
#audit_axioms BookProof.NsBrstDerivativeGauge.nsGradedGhostCar

-- The momentum conjugate to the velocity field, `π^i = ∂/∂u_i`.
#audit_axioms BookProof.NsBrstDerivativeGauge.genU_ccr_u
#audit_axioms BookProof.NsBrstDerivativeGauge.genU_ccr_x
#audit_axioms BookProof.NsBrstDerivativeGauge.genU_uField
#audit_axioms BookProof.NsBrstDerivativeGauge.genU_nsSymbol
#audit_axioms BookProof.NsBrstDerivativeGauge.genU_nsSymbol_ne_zero
#audit_axioms BookProof.NsBrstDerivativeGauge.genY_comm_genU
#audit_axioms BookProof.NsBrstDerivativeGauge.genY2_comm_genU

-- The corrected Hamiltonian differs from the one built with the space momentum.
#audit_axioms BookProof.NsBrstDerivativeGauge.nsHamAlg_one
#audit_axioms BookProof.NsBrstDerivativeGauge.nsHamAlgX_one
#audit_axioms BookProof.NsBrstDerivativeGauge.nsHamAlg_one_ne_zero
#audit_axioms BookProof.NsBrstDerivativeGauge.nsHamAlg_ne_nsHamAlgX

-- The gauge generators commute with the Hamiltonian on the bosonic factor.
#audit_axioms BookProof.NsBrstDerivativeGauge.comm_mulOp_of_apply_eq_zero
#audit_axioms BookProof.NsBrstDerivativeGauge.genY_comm_nsHamAlg
#audit_axioms BookProof.NsBrstDerivativeGauge.genY2_comm_nsHamAlg2

-- The BRST charges: nilpotency.
#audit_axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_nilpotent
#audit_axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_nilpotent

-- The headline: the correct commutator with the Hamiltonian.
#audit_axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_comm_hamiltonian
#audit_axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_comm_hamiltonian2
#audit_axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_hamiltonian_comm
#audit_axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_hamiltonian2_comm

-- Consequences: the dynamics descends to the BRST cohomology.
#audit_axioms BookProof.NsBrstDerivativeGauge.nsHamiltonian_mapsTo_ker
#audit_axioms BookProof.NsBrstDerivativeGauge.nsHamiltonian_mapsTo_range
#audit_axioms BookProof.NsBrstDerivativeGauge.nsHamiltonian2_mapsTo_ker
#audit_axioms BookProof.NsBrstDerivativeGauge.nsBrstCohomologyMap

-- Non-vacuity: the charges are not the zero operator.
#audit_axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_ne_zero
#audit_axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_ne_zero
