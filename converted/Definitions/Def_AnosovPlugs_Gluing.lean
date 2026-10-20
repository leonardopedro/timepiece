/-
prove2.me platform library module `Definitions.Def_AnosovPlugs_Gluing`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_AnosovPlugs_Gluing.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_AnosovPlugs_Laminations

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017).
Glued manifolds and induced vector fields (Proposition 1.1, §1.3, Lemma 3.27), strong isotopy
(§1.3, Definition 3.28), basic pieces and combinatorial transitivity (§1.3).
-/

open scoped Manifold ContDiff Topology
open Set Filter Function

namespace AnosovPlugs

variable {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
  [IsManifold I3 ∞ U]
variable {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
  [IsManifold I3 ∞ N]

/-- `(N, Z)` is the manifold `U/φ` obtained from `U` by gluing the exit boundary of `X` to the
entrance boundary by `φ`, endowed with the vector field induced by `X`: the map `q : U → N` is
a surjective C¹ immersion identifying exactly the points `x ∈ ∂^{out} U` with `φ x`, and it
maps `X` to `Z` (`Dq_x (X x) = Z (q x)` for all `x`). -/
def IsSelfGluing (X : (x : U) → TangentSpace I3 x) (φ : U → U)
    (Z : (y : N) → TangentSpace I3 y) (q : U → N) : Prop :=
  ContMDiff I3 I3 1 q ∧ (∀ x, Injective (mfderiv I3 I3 q x)) ∧ Surjective q ∧
    (∀ x y, q x = q y ↔
      (x = y ∨ (x ∈ outBoundary X ∧ y = φ x) ∨ (y ∈ outBoundary X ∧ x = φ y))) ∧
    ∀ x, mfderiv I3 I3 q x (X x) = Z (q x)

variable {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
  [IsManifold I3 ∞ V]
variable {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
  [IsManifold I3 ∞ W]

/-- `(W, Z)` is the manifold `(U ⊔ V)/φ` obtained by gluing `T^{out} ⊆ ∂^{out} U` to
`T^{in} ⊆ ∂^{in} V` by `φ`, with the vector field induced by `X` and `Y`: `iU : U → W` and
`iV : V → W` are C¹ embeddings (topological embeddings with injective derivatives), their images
cover `W`, `iU x = iV y` exactly when `x ∈ T^{out}` and `y = φ x`, and they map `X`, `Y`
to `Z`. -/
def IsPlugGluing (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (Tout : Set U) (φ : U → V) (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W) :
    Prop :=
  ContMDiff I3 I3 1 iU ∧ ContMDiff I3 I3 1 iV ∧
    Topology.IsEmbedding iU ∧ Topology.IsEmbedding iV ∧
    (∀ x, Injective (mfderiv I3 I3 iU x)) ∧ (∀ y, Injective (mfderiv I3 I3 iV y)) ∧
    range iU ∪ range iV = univ ∧
    (∀ x y, iU x = iV y ↔ (x ∈ Tout ∧ y = φ x)) ∧
    (∀ x, mfderiv I3 I3 iU x (X x) = Z (iU x)) ∧
    (∀ y, mfderiv I3 I3 iV y (Y y) = Z (iV y))

/-- Definition 3.28: `(U, X₀, φ₀)` and `(U, X₁, φ₁)` are strongly isotopic: there is a path
`(X_t, φ_t)_{t ∈ [0,1]}` from `(X₀, φ₀)` to `(X₁, φ₁)` (the gluing maps agreeing on the exit
boundaries) such that each `(U, X_t)` is a hyperbolic plug with filling MS laminations and each
`φ_t` a strongly transverse gluing diffeomorphism for it; the path of vector fields is continuous
for the C¹ topology (the tangent maps of the sections `x ↦ X_t x` depend continuously on
`(t, v)`), and `(t, x) ↦ φ_t x` is continuous on `{(t, x) | t ∈ [0,1], x ∈ ∂^{out}_{X_t} U}`. -/
def StronglyIsotopic (X₀ : (x : U) → TangentSpace I3 x) (φ₀ : U → U)
    (X₁ : (x : U) → TangentSpace I3 x) (φ₁ : U → U) : Prop :=
  ∃ (Xt : ℝ → (x : U) → TangentSpace I3 x) (φt : ℝ → U → U),
    Xt 0 = X₀ ∧ Xt 1 = X₁ ∧ (∀ x ∈ outBoundary X₀, φt 0 x = φ₀ x) ∧
    (∀ x ∈ outBoundary X₁, φt 1 x = φ₁ x) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, IsFillingHyperbolicPlug (Xt t) ∧ IsStronglyTransverseGluing (Xt t) (φt t)) ∧
    ContinuousOn (fun p : ℝ × TangentBundle I3 U =>
        tangentMap I3 I3.tangent (fun x => (⟨x, Xt p.1 x⟩ : TangentBundle I3 U)) p.2)
      (Icc 0 1 ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × U => φt p.1 p.2) {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ outBoundary (Xt p.1)}

/-- The nonwandering set of `X`: points `x` such that for every neighbourhood `O` of `x` and
every `T`, some orbit segment of duration `t ≥ T` starts and ends in `O`. -/
def nonwanderingSet (X : (x : U) → TangentSpace I3 x) : Set U :=
  {x | ∀ O ∈ 𝓝 x, ∀ T : ℝ, ∃ t ≥ T, ∃ y ∈ O, FlowDefined X y t ∧ flowMap X t y ∈ O}

/-- A basic piece of `X`: a nonempty closed invariant subset of the nonwandering set `Ω`, open in
`Ω`, with a dense orbit (for hyperbolic plugs these are exactly the pieces of the spectral
decomposition of `Ω`). -/
def IsBasicPiece (X : (x : U) → TangentSpace I3 x) (B : Set U) : Prop :=
  B.Nonempty ∧ B ⊆ nonwanderingSet X ∧ IsClosed B ∧
    (∃ O : Set U, IsOpen O ∧ O ∩ nonwanderingSet X = B) ∧
    (∀ x ∈ B, ∀ t : ℝ, flowMap X t x ∈ B) ∧
    ∃ x ∈ B, B ⊆ closure (range fun t : ℝ => flowMap X t x)

/-- The stable set `W^s_X(B)` of `B`: points whose forward orbit is defined for all times and
accumulates only on `B` (converges to `B`). -/
def stableSetOf (X : (x : U) → TangentSpace I3 x) (B : Set U) : Set U :=
  {x | x ∈ stableSet X ∧ Tendsto (fun t : ℝ => flowMap X t x) atTop (𝓝ˢ B)}

/-- The unstable set `W^u_X(B)` of `B`. -/
def unstableSetOf (X : (x : U) → TangentSpace I3 x) (B : Set U) : Set U :=
  {x | x ∈ unstableSet X ∧ Tendsto (fun t : ℝ => flowMap X t x) atBot (𝓝ˢ B)}

/-- Edges of the oriented graph `P` of §1.3: from `B` to `B'` if `W^u_X(B)` meets `W^s_X(B')`,
or if `φ(W^u_X(B) ∩ ∂^{out} U)` meets `W^s_X(B') ∩ ∂^{in} U`. -/
def PieceEdge (X : (x : U) → TangentSpace I3 x) (φ : U → U) (B B' : Set U) : Prop :=
  IsBasicPiece X B ∧ IsBasicPiece X B' ∧
    ((unstableSetOf X B ∩ stableSetOf X B').Nonempty ∨
      (φ '' (unstableSetOf X B ∩ outBoundary X) ∩ (stableSetOf X B' ∩ inBoundary X)).Nonempty)

/-- `(U, X, φ)` is combinatorially transitive: the graph `P` is strongly connected. -/
def IsCombinatoriallyTransitive (X : (x : U) → TangentSpace I3 x) (φ : U → U) : Prop :=
  ∀ B B', IsBasicPiece X B → IsBasicPiece X B' → Relation.ReflTransGen (PieceEdge X φ) B B'

end AnosovPlugs
