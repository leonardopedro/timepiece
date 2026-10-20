/-
prove2.me platform library module `Definitions.Def_AnosovPlugs_Flows`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_AnosovPlugs_Flows.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930.
Basic layer: C¹ vector fields on smooth 3-manifolds (possibly with boundary), their (partial)
flows, orientability, transitivity, and topological (orbital) equivalence.

All 3-manifolds are modelled on the closed half-space `EuclideanHalfSpace 3`; a closed
3-manifold is a compact one with empty boundary (`BoundarylessManifold`).
-/

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

/-- The model with corners of 3-manifolds with (possibly empty) boundary: the closed
half-space `{x ∈ ℝ³ | x₀ ≥ 0}`. -/
noncomputable abbrev I3 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 3) :=
  𝓡∂ 3

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold I3 ∞ M]

/-- `X` is a C¹ vector field: the section `x ↦ (x, X x)` of the tangent bundle is C¹. -/
def IsC1VectorField (X : (x : M) → TangentSpace I3 x) : Prop :=
  ContMDiff I3 I3.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I3 M))

/-- The orbit of `x` under `X` is defined on the whole closed time interval between `0` and `t`:
there is an integral curve `γ` of `X` with `γ 0 = x`, defined (inside `M`) on `[0, t]`
(or `[t, 0]` if `t < 0`). -/
def FlowDefined (X : (x : M) → TangentSpace I3 x) (x : M) (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ X (uIcc 0 t)

open Classical in
/-- The (partial) time-`t` map of the flow of `X`: the position at time `t` of the integral
curve of `X` through `x`, when this orbit is defined on the time interval between `0` and
`t`; by convention it is `x` otherwise. -/
noncomputable def flowMap (X : (x : M) → TangentSpace I3 x) (t : ℝ) (x : M) : M :=
  if h : FlowDefined X x t then h.choose t else x

/-- The flow of `X` is topologically transitive: some orbit is dense in `M`
(used for vector fields on closed manifolds, whose flows are complete). -/
def IsTransitiveFlow (X : (x : M) → TangentSpace I3 x) : Prop :=
  ∃ x : M, Dense (range fun t : ℝ => flowMap X t x)

/-- `M` is orientable: it admits an atlas of charts from its (smooth) maximal atlas, covering
`M`, all of whose transition maps have positive Jacobian determinant. -/
def IsOrientable (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] : Prop :=
  ∃ A : Set (OpenPartialHomeomorph M (EuclideanHalfSpace 3)),
    A ⊆ IsManifold.maximalAtlas I3 ∞ M ∧ (∀ x : M, ∃ e ∈ A, x ∈ e.source) ∧
    ∀ e ∈ A, ∀ e' ∈ A, ∀ x ∈ e.source ∩ e'.source,
      0 < LinearMap.det
        (fderivWithin ℝ (e'.extend I3 ∘ (e.extend I3).symm) (range I3) (e.extend I3 x) :
          EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))

variable {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
  [IsManifold I3 ∞ N]

/-- `h : M ≃ₜ N` is a topological (orbital) equivalence from `X` to `Y`: it maps every oriented
orbit (segment) of `X` onto an oriented orbit (segment) of `Y`. Precisely, for every `x` there
is a continuous increasing reparametrisation `τ` with `τ 0 = 0`, mapping the set of times for
which the `X`-orbit of `x` is defined onto the set of times for which the `Y`-orbit of `h x`
is defined, with `h (X^t x) = Y^{τ t} (h x)`. -/
def IsOrbitEquivalence (X : (x : M) → TangentSpace I3 x) (Y : (y : N) → TangentSpace I3 y)
    (h : M ≃ₜ N) : Prop :=
  ∀ x : M, ∃ τ : ℝ → ℝ, Continuous τ ∧ StrictMono τ ∧ τ 0 = 0 ∧
    τ '' {t | FlowDefined X x t} = {s | FlowDefined Y (h x) s} ∧
    ∀ t, FlowDefined X x t → h (flowMap X t x) = flowMap Y (τ t) (h x)

/-- `X` (on `M`) and `Y` (on `N`) are topologically equivalent. -/
def TopologicallyEquivalent (X : (x : M) → TangentSpace I3 x)
    (Y : (y : N) → TangentSpace I3 y) : Prop :=
  ∃ h : M ≃ₜ N, IsOrbitEquivalence X Y h

end AnosovPlugs
