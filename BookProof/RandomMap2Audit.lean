import BookProof.ChapterRoadmapAudit

/-!
# RandomMap2 roadmap audit quarantine

The historical audit below referred to modules through the nonexistent
`RiemannProof.*` namespace.  The corresponding sources now live under
`RandomMap`, `UsedRoute`, and `UnusedRoute`, but their dependency chain includes
an explicitly unfinished RH strategy (`UsedRoute.EtaStrategy`).  Importing that
chain into `BookProof` would therefore make the roadmap's completed,
sorry-free target depend on unresolved RH-strength material.

The original audit is retained verbatim below as historical material rather
than silently weakening its claims.  The checked roadmap certificates are in
`BookProof.ChapterRoadmapAudit`, imported above.
-/

/-
import RiemannProof.RandomMap2Moments
import RiemannProof.RandomMap2Walk
import RiemannProof.RandomMap2InfiniteWalk
import RiemannProof.RcpRandomMapBridge
import RiemannProof.SolovayHilbert
import RiemannProof.RandomMap2RH

/-!
# RandomMap2 roadmap audit

Kernel-level audit surface for roadmap items R23 and R26.  The declarations
below intentionally cover the independently proved decoupling, moment,
infinite-walk, RCP-marginal, Solovay, and conditional RH results.  Historical
unconditional RH declarations are excluded because their dependency chain
contains the explicitly quarantined RH-strength placeholders.
-/

#print axioms outer_inner_reduces_to_head
#print axioms X_coordinate_orthogonal
#print axioms Var_X_coordinate_bound
#print axioms X_coordinate_secondMoment_eq
#print axioms RandomMap2Walk.partialEnergy_expectation_eq
#print axioms RandomMap2Walk.fullEnergy_expectation_eq
#print axioms RandomMap2Walk.meanEnergy_expectation_eq
#print axioms RandomMap2Walk.meanEnergy_expectation_bound
#print axioms RandomMap2InfiniteWalk.finite_marginals_compatible
#print axioms RandomMap2InfiniteWalk.totalEnergy_expectation_eq
#print axioms RandomMap2InfiniteWalk.integrable_totalEnergy
#print axioms RcpRandomMapBridge.rcp_stateMeasure_decoupling
#print axioms SolovayHilbert.godelian_trapdoor_sealed
#print axioms RandomMap2RH.rectangleRH_iff_zeroFreeRightHalfPlane
#print axioms RandomMap2RH.decoupled_integral_and_zeroFree_of_rectangle
#print axioms RandomMap2RH.outer_inner_reduces_to_head_generalized
#print axioms RandomMap2RH.riemann_hypothesis_bridge
-/
