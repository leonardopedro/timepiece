import Mathlib
import BookProof.Toolbox.PhysHSGaussian
import BookProof.EuclideanFock4D.CoreBasis

/-!
# The 4D Euclidean Mehler measure and its `O(4)` invariance

Plan: `cftproof.md`, Phase 1.2 — "Define the free Euclidean Gaussian measure `dγ₀(A)` …,
and show `mehler4D_O4_invariant`".

## What is real here

`BookProof.PhysHSGaussian` (corpus, `BookProof/Toolbox/PhysHSGaussian`) *constructs* the
Gaussian `gaussianE k` on `EuclideanSpace ℝ (Fin k)` as the image of the product standard
Gaussian under `toLp`, proves it is a probability measure (`gaussianE_isProbability`), proves
that the radial projection pushes it to the uniform measure on the radius-`√k` sphere
(`sphereUniform_sphere`), and proves rotational invariance of both the Gaussian
(`gaussianE_rotation_invariant`, via characteristic functions) and the sphere measure
(`sphereUniform_rotation_invariant`).

Phase 1.2 asks for exactly this in dimension `4`, named as the Mehler measure.  So
`mehlerMeasure4D` *is* `gaussianE 4`, and its `O(4)` invariance is the corpus theorem at
`k = 4`.  `O(4)` here is `EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)`, i.e.
linear maps preserving the inner product — which is the definition of the orthogonal group;
`liftIsometry` is the plan's name for the action of such an `R` on the measure.

## Boundary (recorded, not assumed away)

The plan describes `dγ₀(A)` on the `S^∞` sphere of the Fock layer, with the colour and
Lorentz factors.  The corpus — and hence this file — has the Gaussian on the *scalar*
layer `L²(ℝ⁴)`, and the sphere measure on the radius-`√k` sphere of `EuclideanSpace ℝ (Fin k)`.
The `S^∞` projective limit and the positive/negative-frequency decomposition need a Fock
space and a Poincaré action, neither of which exists in Mathlib nor in the corpus; they are
not claimed here.  See `CoreBasis.lean` for the index dictionary and the tensor-product
boundary.
-/

namespace BookProof.EuclideanFock4D

open MeasureTheory
open PhysHSGaussian

noncomputable section

/-- The orthogonal group `O(4)` of the Euclidean four-space: linear isometries of `ℝ⁴`.
(For a linear map, `‖Rx‖ = ‖x‖` for all `x` is equivalently `RᵀR = 1`.) -/
abbrev O4 : Type := EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)

/-- The action of `R ∈ O(4)` on the field, as used by the plan's statement. -/
def liftIsometry (R : O4) : Spacetime4D ≃ₗᵢ[ℝ] Spacetime4D := R

/-- **The 4D Euclidean (Mehler) Gaussian measure** `dγ₀` on `ℝ⁴`: the product of four
standard Gaussians, transported to `EuclideanSpace ℝ (Fin 4)`. -/
def mehlerMeasure4D : Measure Spacetime4D := gaussianE 4

/-- It is a probability measure. -/
instance instIsProbabilityMehlerMeasure4D : IsProbabilityMeasure mehlerMeasure4D := by
  unfold mehlerMeasure4D
  infer_instance

/-- **`O(4)` invariance of the 4D Mehler measure** (plan Phase 1.2). -/
theorem mehler4D_O4_invariant (R : O4) :
    Measure.map (liftIsometry R) mehlerMeasure4D = mehlerMeasure4D :=
  gaussianE_rotation_invariant 4 R

/-- The uniform measure on the radius-`2` sphere of `ℝ⁴`, i.e. `sphereUniform 4`.
This is the finite-`k` section of the plan's `S^∞` sphere measure. -/
def sphereUniform4D : Measure Spacetime4D := sphereUniform 4

/-- It is a probability measure. -/
instance instIsProbabilitySphereUniform4D : IsProbabilityMeasure sphereUniform4D := by
  unfold sphereUniform4D
  infer_instance

/-- The sphere measure lives on the sphere of radius `√4 = 2`. -/
theorem sphereUniform4D_sphere :
    sphereUniform4D {x : Spacetime4D | ‖x‖ = Real.sqrt 4} = 1 :=
  sphereUniform_sphere 4 (by norm_num)

/-- **`O(4)` invariance of the 4D sphere measure** (plan Phase 1.2, sphere version). -/
theorem sphereUniform4D_O4_invariant (R : O4) :
    Measure.map R sphereUniform4D = sphereUniform4D :=
  sphereUniform_rotation_invariant 4 R

end

end BookProof.EuclideanFock4D
