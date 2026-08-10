import PnpProof.Foundations
import BookProof.PhysHSGaussian

/-!
# Part 3b: The uniform sphere measure and the Gaussian limit (promoted)

**Promoted (2026-08-09).**  The mathematical content of this module has been
promoted out of `PnpProof/` into `BookProof/PhysHSGaussian.lean` (see
`PLAN_LEAN_SPECIALIST_COHERENT.md` Part G): it is general mathematics — the
measure-theoretic, functional-analytic and hyperspherical/Gaussian backbone —
reused by the QFM/Fork thread, and `PnpProof/` must be a one-way leaf of the
dependency graph.  This file is now a thin re-export so that the P≠NP
development keeps its familiar names; **no proof lives here any more**.
-/

namespace PnpProof

export PhysHSGaussian (physHermite physHermite_zero physHermite_one physHermite_succ_succ
  gegenbauer gegenbauer_zero gegenbauer_one gegenbauer_two gegenbauer_rec gegenbauerScaled
  gegenbauerScaled_tendsto_hermite gaussianE sphereProj sphereUniform sphereProj_measurable
  sphereUniform_sphere weight_tendsto_gaussian sphereProj_equivariant
  gaussianE_rotation_invariant sphereUniform_rotation_invariant physHermite_hasDerivAt
  hermite_sq_integral hermite_normalization gegenbauerScaled_rec gegenbauerScaled_bound
  normalization_tendsto gammaMeasure normSq gaussian_concentration_sphere poincare_borel_ae)

end PnpProof
