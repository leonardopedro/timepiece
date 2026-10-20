/-
prove2.me platform library module `Definitions.Def_AnosovPlugs_Hyperbolic`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_AnosovPlugs_Hyperbolic.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_AnosovPlugs_Flows

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017).
Hyperbolic invariant sets of flows on 3-manifolds (with 1-dimensional strong stable and strong
unstable bundles), and Anosov vector fields (§1.1, Definition 3.2).
-/

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold I3 ∞ M]

/-- A continuous Riemannian metric on the 3-manifold `M` (a continuously varying inner product
on the tangent spaces). -/
abbrev RiemannianMetric3 (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold I3 ∞ M] :=
  Bundle.ContinuousRiemannianMetric (EuclideanSpace ℝ (Fin 3)) (TangentSpace I3 : M → Type)

/-- The norm of a tangent vector `v ∈ T_x M` for the Riemannian metric `g`. -/
noncomputable def RiemannianMetric3.norm (g : RiemannianMetric3 M) (x : M)
    (v : TangentSpace I3 x) : ℝ :=
  Real.sqrt (g.inner x v v)

/-- `Λ` is a hyperbolic set of the vector field `X`, with one-dimensional strong stable and
strong unstable bundles: there are a continuous Riemannian metric `g`, line fields
`E^s, E^u` over `Λ` and constants `C > 0`, `λ > 0` such that for every `x ∈ Λ`:
* `T_x M = E^s(x) + ℝ·X(x) + E^u(x)` with `dim E^s(x) = dim E^u(x) = 1` (so the sum is direct
  and `X(x) ≠ 0`);
* `E^s` and `E^u` are invariant under the derivative of the time-`t` map of the flow, for all
  real `t`;
* `‖D X^t (v)‖ ≤ C e^{-λ t} ‖v‖` for `v ∈ E^s(x)`, `t ≥ 0`, and
  `‖D X^{-t} (v)‖ ≤ C e^{-λ t} ‖v‖` for `v ∈ E^u(x)`, `t ≥ 0`.
(Continuity of the splitting is not required: it is a consequence of these estimates.) -/
def IsHyperbolicSet (X : (x : M) → TangentSpace I3 x) (Λ : Set M) : Prop :=
  ∃ (g : RiemannianMetric3 M) (Es Eu : (x : M) → Submodule ℝ (TangentSpace I3 x)) (C lam : ℝ),
    0 < C ∧ 0 < lam ∧ ∀ x ∈ Λ,
      Module.finrank ℝ (Es x) = 1 ∧ Module.finrank ℝ (Eu x) = 1 ∧
      Es x ⊔ Submodule.span ℝ {X x} ⊔ Eu x = ⊤ ∧
      (∀ t : ℝ, (Es x).map (mfderiv I3 I3 (flowMap X t) x).toLinearMap = Es (flowMap X t x)) ∧
      (∀ t : ℝ, (Eu x).map (mfderiv I3 I3 (flowMap X t) x).toLinearMap = Eu (flowMap X t x)) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Es x,
        g.norm (flowMap X t x) (mfderiv I3 I3 (flowMap X t) x v)
          ≤ C * Real.exp (-lam * t) * g.norm x v) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v ∈ Eu x,
        g.norm (flowMap X (-t) x) (mfderiv I3 I3 (flowMap X (-t)) x v)
          ≤ C * Real.exp (-lam * t) * g.norm x v)

/-- `X` is an Anosov vector field on `M`: a C¹ vector field for which the whole manifold is a
hyperbolic set (intended for closed `M`, where the flow is complete). -/
def IsAnosov (X : (x : M) → TangentSpace I3 x) : Prop :=
  IsC1VectorField X ∧ IsHyperbolicSet X univ

end AnosovPlugs
