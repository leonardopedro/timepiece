/-
prove2.me platform library module `Definitions.Def_HunterPDE_Semigroup_C0Semigroup`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_HunterPDE_Semigroup_C0Semigroup.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open Filter
open scoped Topology

namespace HunterPDE.Semigroup

/-- Definition 5.23 of Hunter, *Notes on PDEs* (p. 141): a one-parameter, **uniformly continuous
group** on the Banach space `X` (over `𝕜 = ℝ` or `ℂ`) is a family `{T(t) : t ∈ ℝ}` of bounded
linear operators with (1) `T(0) = I`, (2) `T(s)T(t) = T(s + t)` for all `s, t ∈ ℝ`, and
(3) `T(h) → I` uniformly, i.e. in the operator norm of `L(X)`, as `h → 0`. -/
def IsUniformlyContinuousGroup {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (T : ℝ → X →L[𝕜] X) : Prop :=
  T 0 = 1 ∧
  (∀ s t : ℝ, T s * T t = T (s + t)) ∧
  Tendsto T (𝓝 0) (𝓝 1)

/-- Definition 5.26 of Hunter, *Notes on PDEs* (p. 142): a one-parameter, **strongly continuous
(C₀) semigroup** on `X` is a family `{T(t) : t ≥ 0}` of bounded linear operators with
(1) `T(0) = I`, (2) `T(s)T(t) = T(s + t)` for all `s, t ≥ 0`, and (3) `T(h)f → f` in norm as
`h → 0⁺` for every `f ∈ X`.

The family is indexed by `t : ℝ`; only the values at `t ≥ 0` enter the definition (and every
statement built on it), so the values at negative times are immaterial. -/
def IsC0Semigroup {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (T : ℝ → X →L[𝕜] X) : Prop :=
  T 0 = 1 ∧
  (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T s * T t = T (s + t)) ∧
  (∀ f : X, Tendsto (fun h : ℝ => T h f) (𝓝[>] 0) (𝓝 f))

/-- Definition 5.26 (last sentence): a C₀ semigroup is a **contraction semigroup** if
`‖T(t)‖ ≤ 1` (operator norm) for all `t ≥ 0`. -/
def IsContractionSemigroup {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (T : ℝ → X →L[𝕜] X) : Prop :=
  IsC0Semigroup T ∧ ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1

/-- Definition 5.28 of Hunter, *Notes on PDEs* (pp. 143–144): a one-parameter, **strongly
continuous (C₀) group** on `X` is a family `{T(t) : t ∈ ℝ}` of bounded linear operators with
(1) `T(0) = I`, (2) `T(s)T(t) = T(s + t)` for all `s, t ∈ ℝ`, and (3) `T(h)f → f` in norm as
`h → 0` for every `f ∈ X`. -/
def IsC0Group {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (T : ℝ → X →L[𝕜] X) : Prop :=
  T 0 = 1 ∧
  (∀ s t : ℝ, T s * T t = T (s + t)) ∧
  (∀ f : X, Tendsto (fun h : ℝ => T h f) (𝓝 0) (𝓝 f))

/-- Definition 5.28 (last sentence): on a complex Hilbert space `H`, a C₀ group is a
**unitary group** if every `T(t)` is a unitary operator. -/
def IsUnitaryGroup {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : ℝ → H →L[ℂ] H) : Prop :=
  IsC0Group T ∧ ∀ t : ℝ, T t ∈ unitary (H →L[ℂ] H)

/-- Definition 5.30 of Hunter, *Notes on PDEs* (p. 144): the linear operator
`A : D(A) ⊂ X → X` (a partially defined linear map, `X →ₗ.[𝕜] X`) is **the generator** of the
family `T` if

1. `f ∈ D(A)` if and only if the limit `lim_{h → 0⁺} (T(h)f − f)/h` exists in the norm topology
   of `X`, and
2. for `f ∈ D(A)`, `Af` equals that limit.

Both clauses are encoded at once: for all `f, g ∈ X`, the difference quotient tends to `g` as
`h → 0⁺` if and only if `f ∈ D(A)` and `Af = g`. So `A` is the generator including its domain
(the full set where the limit exists), not a restriction of it. Only `h > 0` enters. -/
def IsGenerator {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (T : ℝ → X →L[𝕜] X) (A : X →ₗ.[𝕜] X) : Prop :=
  ∀ f g : X,
    Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • (T h f - f)) (𝓝[>] 0) (𝓝 g) ↔
      ∃ hf : f ∈ A.domain, A ⟨f, hf⟩ = g

end HunterPDE.Semigroup
