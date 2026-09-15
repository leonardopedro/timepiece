import BookProof.ChapterNavierStokesFullEulerianFock
import BookProof.ChapterNavierStokesFullLagrangianFock

/-!
Axiom audit for the full (non-linearised) Navier–Stokes Hamiltonians on the nested Fock
space, in Eulerian and in Lagrangian variables:

* the complete quadratic advection `u·∇u` (Eulerian) and the exact Piola pressure term with
  the exact `det F = 1` volume constraint (Lagrangian) — no Oseen linearisation anywhere;
* boundedness below, the Friedrichs extension on every parcel-number sector and on the whole
  nested Fock space, the Faris–Lavine statement on the outer space (`c = 0`, comparison
  operator the lifted Friedrichs extension), the unitary flow, and parcel-number
  conservation (so no lattice is involved);
* the two nonlinearity witnesses.

Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Eulerian variables, full nonlinear advection.
#print axioms BookProof.NsFullEuler.nsSectorHam_symmetricOn
#print axioms BookProof.NsFullEuler.nsSectorHam_quadForm_nonneg
#print axioms BookProof.NsFullEuler.nsSector_friedrichs_extension
#print axioms BookProof.NsFullEuler.nsFockCore_dense
#print axioms BookProof.NsFullEuler.nsFullFockHam_symmetricOn
#print axioms BookProof.NsFullEuler.nsFullFockHam_quadForm_nonneg
#print axioms BookProof.NsFullEuler.nsFullFock_friedrichs_extension
#print axioms BookProof.NsFullEuler.nsFullOuterN_esa
#print axioms BookProof.NsFullEuler.nsFullOuterN_isPositiveSelfAdjointExtension
#print axioms BookProof.NsFullEuler.nsFullFock_stone_flow
#print axioms BookProof.NsFullEuler.nsFullFockHam_number_conserving
#print axioms BookProof.NsFullEuler.nsResPoly_eval_testPt
#print axioms BookProof.NsFullEuler.nsResPoly_not_affine

-- Lagrangian variables, exact Piola pressure term and exact volume constraint.
#print axioms BookProof.NsFullLagrangian.lagSectorHam_symmetricOn
#print axioms BookProof.NsFullLagrangian.lagSectorHam_quadForm_nonneg
#print axioms BookProof.NsFullLagrangian.lagSector_friedrichs_extension
#print axioms BookProof.NsFullLagrangian.lagFockCore_dense
#print axioms BookProof.NsFullLagrangian.lagFullFockHam_symmetricOn
#print axioms BookProof.NsFullLagrangian.lagFullFockHam_quadForm_nonneg
#print axioms BookProof.NsFullLagrangian.lagFullFock_friedrichs_extension
#print axioms BookProof.NsFullLagrangian.lagFullOuterN_esa
#print axioms BookProof.NsFullLagrangian.lagFullOuterN_isPositiveSelfAdjointExtension
#print axioms BookProof.NsFullLagrangian.lagFullFock_stone_flow
#print axioms BookProof.NsFullLagrangian.lagFullFockHam_number_conserving
#print axioms BookProof.NsFullLagrangian.detPoly_eval_testPt
#print axioms BookProof.NsFullLagrangian.volumePoly_not_quadratic
