import BookProof.Ns.ChapterNavierStokesFullEulerianFock
import BookProof.Ns.ChapterNavierStokesFullLagrangianFock
import BookProof.RoadmapAudit.AxiomAudit

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
#audit_axioms BookProof.NsFullEuler.nsSectorHam_symmetricOn
#audit_axioms BookProof.NsFullEuler.nsSectorHam_quadForm_nonneg
#audit_axioms BookProof.NsFullEuler.nsSector_friedrichs_extension
#audit_axioms BookProof.NsFullEuler.nsFockCore_dense
#audit_axioms BookProof.NsFullEuler.nsFullFockHam_symmetricOn
#audit_axioms BookProof.NsFullEuler.nsFullFockHam_quadForm_nonneg
#audit_axioms BookProof.NsFullEuler.nsFullFock_friedrichs_extension
#audit_axioms BookProof.NsFullEuler.nsFullOuterN_esa
#audit_axioms BookProof.NsFullEuler.nsFullOuterN_isPositiveSelfAdjointExtension
#audit_axioms BookProof.NsFullEuler.nsFullFock_stone_flow
#audit_axioms BookProof.NsFullEuler.nsFullFockHam_number_conserving
#audit_axioms BookProof.NsFullEuler.nsResPoly_eval_testPt
#audit_axioms BookProof.NsFullEuler.nsResPoly_not_affine

-- Lagrangian variables, exact Piola pressure term and exact volume constraint.
#audit_axioms BookProof.NsFullLagrangian.lagSectorHam_symmetricOn
#audit_axioms BookProof.NsFullLagrangian.lagSectorHam_quadForm_nonneg
#audit_axioms BookProof.NsFullLagrangian.lagSector_friedrichs_extension
#audit_axioms BookProof.NsFullLagrangian.lagFockCore_dense
#audit_axioms BookProof.NsFullLagrangian.lagFullFockHam_symmetricOn
#audit_axioms BookProof.NsFullLagrangian.lagFullFockHam_quadForm_nonneg
#audit_axioms BookProof.NsFullLagrangian.lagFullFock_friedrichs_extension
#audit_axioms BookProof.NsFullLagrangian.lagFullOuterN_esa
#audit_axioms BookProof.NsFullLagrangian.lagFullOuterN_isPositiveSelfAdjointExtension
#audit_axioms BookProof.NsFullLagrangian.lagFullFock_stone_flow
#audit_axioms BookProof.NsFullLagrangian.lagFullFockHam_number_conserving
#audit_axioms BookProof.NsFullLagrangian.detPoly_eval_testPt
#audit_axioms BookProof.NsFullLagrangian.volumePoly_not_quadratic
