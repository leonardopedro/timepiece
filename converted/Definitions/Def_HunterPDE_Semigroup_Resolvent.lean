/-
prove2.me platform library module `Definitions.Def_HunterPDE_Semigroup_Resolvent`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_HunterPDE_Semigroup_Resolvent.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace HunterPDE.Semigroup

/-- Definition 5.34 of Hunter, *Notes on PDEs* (p. 145): a scalar `μ` is in the **resolvent set**
`ρ(A)` of the operator `A : D(A) ⊂ X → X` if `μI − A : D(A) → X` is one-to-one and onto.
(The book states the definition for closed, densely defined `A`; every statement of this mission
that uses it assumes that separately.) -/
def IsInResolventSet {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (A : X →ₗ.[𝕜] X) (μ : 𝕜) : Prop :=
  Function.Bijective (fun f : A.domain => μ • (f : X) - A f)

/-- The **resolvent** `R(μ, A) = (μI − A)⁻¹ : X → X` of Hunter, *Notes on PDEs*, Eq. (5.23)
(p. 145), as a function `X → X`: `resolvent A μ g` is the (unique, when `μ ∈ ρ(A)`) `f ∈ D(A)`
with `μf − Af = g`. It is only meaningful for `μ ∈ ρ(A)`, and every statement that uses it
assumes `IsInResolventSet A μ`. -/
noncomputable def resolvent {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (A : X →ₗ.[𝕜] X) (μ : 𝕜) (g : X) : X :=
  ((Function.invFun (fun f : A.domain => μ • (f : X) - A f) g : A.domain) : X)

/-- Definition 5.37 of Hunter, *Notes on PDEs* (p. 147), inequality (5.27): `A` is
**dissipative** if `λ‖f‖ ≤ ‖(λI − A)f‖` for every real `λ > 0` and every `f ∈ D(A)`.
(The book states the definition for closed, densely defined `A`; every statement of this mission
that uses it assumes that separately.) -/
def IsDissipative {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (A : X →ₗ.[𝕜] X) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ f : A.domain, lam * ‖(f : X)‖ ≤ ‖(lam : 𝕜) • (f : X) - A f‖

/-- Definition 5.37 of Hunter, *Notes on PDEs* (p. 147): `A` is **maximally dissipative**
(m-dissipative) if it is dissipative and the range of `λI − A` is all of `X` for **some**
real `λ > 0`. -/
def IsMDissipative {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (A : X →ₗ.[𝕜] X) : Prop :=
  IsDissipative A ∧
    ∃ lam : ℝ, 0 < lam ∧ Function.Surjective (fun f : A.domain => (lam : 𝕜) • (f : X) - A f)

end HunterPDE.Semigroup
