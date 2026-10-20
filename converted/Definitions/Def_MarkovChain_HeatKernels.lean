/-
prove2.me platform library module `Definitions.Def_MarkovChain_HeatKernels`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_MarkovChain_HeatKernels.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain

/-!
# Markov chains on a countable set: Dirichlet forms, isoperimetric profiles and heat kernels

Definitions for kernels `X → X → ℝ` on a state space `X`, taken from A. Erschler and T. Zheng,
*Growth of periodic Grigorchuk groups*, arXiv:1802.09077v2 (cited as EZ, with its page numbers),
§3 (p. 18), §5.1 (p. 24) and §7.5 (pp. 49–52). Kernel powers `Pⁿ` and transition kernels are
`DurrettProbability.stepProb` and `DurrettProbability.IsTransition`.

Functions on `X` are real valued; sums over `X` are `tsum`s. Quantities that may be infinite (the
Green function, sup norms) take values in `[0, ∞]`.
-/

open DurrettProbability
open scoped ENNReal

namespace MarkovChain

variable {X : Type*}

/-- A symmetric kernel, `J(x, y) = J(y, x)` (EZ p. 49). -/
def IsSymmetric (J : X → X → ℝ) : Prop := ∀ x y, J x y = J y x

/-- `P` is reversible with respect to `π`: `π(x)P(x, y) = π(y)P(y, x)` for all `x, y` (EZ p. 24). -/
def IsReversible (P : X → X → ℝ) (π : X → ℝ) : Prop := ∀ x y, π x * P x y = π y * P y x

/-- The Green function `G_P(x, y) = ∑_{n ≥ 0} Pⁿ(x, y)` (EZ p. 18), a value in `[0, ∞]`. -/
noncomputable def green [DecidableEq X] (P : X → X → ℝ) (x y : X) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (stepProb P n x y)

/-- The Dirichlet form `ℰ_P(f) = ½ ∑_{x,y ∈ X} (f(x) − f(y))² P(x, y) π(x)` (EZ p. 24). -/
noncomputable def dirichletForm (P : X → X → ℝ) (π : X → ℝ) (f : X → ℝ) : ℝ :=
  (1 / 2) * ∑' p : X × X, (f p.1 - f p.2) ^ 2 * P p.1 p.2 * π p.1

/-- The squared norm `‖f‖²_{ℓ²(π)} = ∑_x f(x)² π(x)` (EZ p. 24). -/
noncomputable def normSq (π : X → ℝ) (f : X → ℝ) : ℝ := ∑' x, f x ^ 2 * π x

/-- The smallest Dirichlet eigenvalue of a finite set `Ω` (EZ p. 24):
`λ₁(Ω) = inf {ℰ_P(f) : supp f ⊆ Ω, ‖f‖_{ℓ²(π)} = 1}`. -/
noncomputable def dirichletEigenvalue (P : X → X → ℝ) (π : X → ℝ) (Ω : Finset X) : ℝ :=
  sInf {e | ∃ f : X → ℝ, (∀ x ∉ Ω, f x = 0) ∧ normSq π f = 1 ∧ dirichletForm P π f = e}

/-- The `ℓ²`-isoperimetric profile (EZ p. 24): `Λ_P(v) = inf {λ₁(Ω) : π(Ω) ≤ v}`, the infimum
taken over finite non-empty sets `Ω`. -/
noncomputable def isoperimetricProfile (P : X → X → ℝ) (π : X → ℝ) (v : ℝ) : ℝ :=
  sInf {e | ∃ Ω : Finset X, Ω.Nonempty ∧ ∑ x ∈ Ω, π x ≤ v ∧ dirichletEigenvalue P π Ω = e}

/-- The size of the boundary of a finite set `Ω` with respect to `(P, π)` (EZ p. 24):
`|∂_P Ω| = ∑_{x ∈ Ω, y ∉ Ω} π(x) P(x, y)`. -/
noncomputable def boundarySize (P : X → X → ℝ) (π : X → ℝ) (Ω : Finset X) : ℝ :=
  ∑ x ∈ Ω, ∑' y : {y // y ∉ Ω}, π x * P x y

/-- The kernel `J` with the mass `1 − ∑_y J(x, y)` added at `(x, x)`; used to define
`heatKernel`. -/
noncomputable def uniformize [DecidableEq X] (J : X → X → ℝ) : X → X → ℝ :=
  fun x y => J x y + if x = y then 1 - ∑' z, J x z else 0

/-- The heat kernel `p(t, x, y)` of the jump kernel `J` (EZ pp. 49–51), defined as the series
`e^{−t} ∑_{n ≥ 0} (tⁿ / n!) Uⁿ(x, y)`, where `U = uniformize J`. -/
noncomputable def heatKernel [DecidableEq X] (J : X → X → ℝ) (t : ℝ) (x y : X) : ℝ :=
  ∑' n : ℕ, Real.exp (-t) * t ^ n / n.factorial * stepProb (uniformize J) n x y

/-- `ρ` is a metric on `X` (EZ p. 49). -/
structure IsMetric (ρ : X → X → ℝ) : Prop where
  self_eq : ∀ x, ρ x x = 0
  eq_of_eq_zero : ∀ x y, ρ x y = 0 → x = y
  symm : ∀ x y, ρ x y = ρ y x
  triangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z

/-- The part of `J` of range at most `R` (EZ p. 51): `J^R_1(x, y) = J(x, y) 1{ρ(x, y) ≤ R}`. -/
noncomputable def nearPart (J : X → X → ℝ) (ρ : X → X → ℝ) (R : ℝ) : X → X → ℝ :=
  fun x y => if ρ x y ≤ R then J x y else 0

/-- The part of `J` of range greater than `R` (EZ p. 51): `J^R_2(x, y) = J(x, y) 1{ρ(x, y) > R}`. -/
noncomputable def farPart (J : X → X → ℝ) (ρ : X → X → ℝ) (R : ℝ) : X → X → ℝ :=
  fun x y => if R < ρ x y then J x y else 0

/-- `Γ(f, f)(x) = ∑_y (f(y) − f(x))² J(x, y)` (EZ p. 52, `Γ_R(f, g)` with `g = f` and a general
kernel `J` in place of `J^R_1`), a value in `[0, ∞]`. -/
noncomputable def carreDuChamp (J : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  ∑' y, ENNReal.ofReal ((f y - f x) ^ 2 * J x y)

/-- `Λ(ψ)² = max {‖e^{−2ψ} Γ(e^ψ, e^ψ)‖_∞, ‖e^{2ψ} Γ(e^{−ψ}, e^{−ψ})‖_∞}` (EZ p. 52, `Λ_R(ψ)²`
with a general kernel `J` in place of `J^R_1`), a value in `[0, ∞]`. -/
noncomputable def daviesSq (J : X → X → ℝ) (ψ : X → ℝ) : ℝ≥0∞ :=
  max (⨆ x, ENNReal.ofReal (Real.exp (-2 * ψ x)) * carreDuChamp J (fun y => Real.exp (ψ y)) x)
    (⨆ x, ENNReal.ofReal (Real.exp (2 * ψ x)) * carreDuChamp J (fun y => Real.exp (-ψ y)) x)

/-- `‖J‖_∞ = sup_{x,y} J(x, y)` (EZ p. 51), a value in `[0, ∞]`. -/
noncomputable def supNorm (J : X → X → ℝ) : ℝ≥0∞ := ⨆ x, ⨆ y, ENNReal.ofReal (J x y)

/-- The Nash inequality with constants `C`, `δ` and exponent `β` for the kernel `J` (EZ p. 51):
`‖f‖₂^{2(1+β)} ≤ C (ℰ_J(f, f) + δ ‖f‖₂²) ‖f‖₁^{2β}` for every finitely supported `f : X → ℝ`,
the norms and the Dirichlet form taken with respect to the counting measure. -/
def SatisfiesNash (J : X → X → ℝ) (C δ β : ℝ) : Prop :=
  ∀ f : X → ℝ, (Function.support f).Finite →
    normSq (fun _ => 1) f ^ (1 + β) ≤
      C * (dirichletForm J (fun _ => 1) f + δ * normSq (fun _ => 1) f) * (∑' x, |f x|) ^ (2 * β)

end MarkovChain
