import BookProof.ChapterNsBrstDerivativeGauge

/-!
Axiom audit for the BRST charge of the Navier–Stokes **derivative gauge** — the gauge fixing
of the variables that represent the spatial derivatives of the velocity field — and for its
commutator with the Navier–Stokes Hamiltonian.  Every result below must report only
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- The ghost sector and the graded state space.
#print axioms BookProof.NsBrstDerivativeGauge.nsGhost_car
#print axioms BookProof.NsBrstDerivativeGauge.nsBos_nsGh_comm
#print axioms BookProof.NsBrstDerivativeGauge.nsGradedGhostCar

-- The momentum conjugate to the velocity field, `π^i = ∂/∂u_i`.
#print axioms BookProof.NsBrstDerivativeGauge.genU_ccr_u
#print axioms BookProof.NsBrstDerivativeGauge.genU_ccr_x
#print axioms BookProof.NsBrstDerivativeGauge.genU_uField
#print axioms BookProof.NsBrstDerivativeGauge.genU_nsSymbol
#print axioms BookProof.NsBrstDerivativeGauge.genU_nsSymbol_ne_zero
#print axioms BookProof.NsBrstDerivativeGauge.genY_comm_genU
#print axioms BookProof.NsBrstDerivativeGauge.genY2_comm_genU

-- The corrected Hamiltonian differs from the one built with the space momentum.
#print axioms BookProof.NsBrstDerivativeGauge.nsHamAlg_one
#print axioms BookProof.NsBrstDerivativeGauge.nsHamAlgX_one
#print axioms BookProof.NsBrstDerivativeGauge.nsHamAlg_one_ne_zero
#print axioms BookProof.NsBrstDerivativeGauge.nsHamAlg_ne_nsHamAlgX

-- The gauge generators commute with the Hamiltonian on the bosonic factor.
#print axioms BookProof.NsBrstDerivativeGauge.comm_mulOp_of_apply_eq_zero
#print axioms BookProof.NsBrstDerivativeGauge.genY_comm_nsHamAlg
#print axioms BookProof.NsBrstDerivativeGauge.genY2_comm_nsHamAlg2

-- The BRST charges: nilpotency.
#print axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_nilpotent
#print axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_nilpotent

-- The headline: the correct commutator with the Hamiltonian.
#print axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_comm_hamiltonian
#print axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_comm_hamiltonian2
#print axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_hamiltonian_comm
#print axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_hamiltonian2_comm

-- Consequences: the dynamics descends to the BRST cohomology.
#print axioms BookProof.NsBrstDerivativeGauge.nsHamiltonian_mapsTo_ker
#print axioms BookProof.NsBrstDerivativeGauge.nsHamiltonian_mapsTo_range
#print axioms BookProof.NsBrstDerivativeGauge.nsHamiltonian2_mapsTo_ker
#print axioms BookProof.NsBrstDerivativeGauge.nsBrstCohomologyMap

-- Non-vacuity: the charges are not the zero operator.
#print axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge_ne_zero
#print axioms BookProof.NsBrstDerivativeGauge.nsDerivBrstCharge2_ne_zero
