import Mathlib
import BookProof.OSReconstruction.PhysicalSpace

/-!
# The reflection is trivial on `𝔄 / 𝔑`: why OS positivity is a half-space statement

Plan: `cftproof.md`, Phase 3.2–3.3.  Phase 3.2 defines `𝔄₊`, the observables supported in
`{x₀ > 0}`, and Phase 3.3 states reflection positivity for `F ∈ 𝔄₊`:
`⟨θ(F) F⟩_a ≥ 0`.

`ReflectionPositivity.Proof` states the hypothesis over the *whole* observable algebra instead
(`IsReflectionPositive ω := ∀ F, 0 ≤ ω(θF · F)`), because that is the form the quotient
construction consumes.  This module records that the two are **not** interchangeable: for a
genuine state — the expectation of a positive measure, hence `ω(F²) ≥ 0` — full-algebra
reflection positivity forces every observable into the same class as its reflection.  The
reflection is then the identity on `ℋ`, and the reconstruction has no time direction left.
That is exactly the failure the literature avoids by restricting to `𝔄₊`, where `F` and `θF`
live in different algebras and the argument below does not apply.

## Contents

* `IsReflectionPositiveOn` — reflection positivity restricted to a set of observables (the
  physically stated form, `S = 𝔄₊`), and
  `IsReflectionPositive.isReflectionPositiveOn`: the full-algebra form implies it;
* `IsPositiveFunctional` — `ω(F²) ≥ 0`, the state condition;
* `thetaObs_sub_self` — `θ(F − θF) = −(F − θF)`, the reflection-antisymmetric part;
* **`osBilin_sub_theta_self_eq_zero`** — the OS form vanishes on the antisymmetric part;
* **`sub_theta_self_mem_radical`** — `F − θF ∈ 𝔑`;
* **`mk_thetaObs_eq_mk`** — `[θF] = [F]` in `𝔄 / 𝔑`: the reflection is the identity on the
  physical space.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity

noncomputable section

/-! ## The two forms of the hypothesis -/

/-- **Reflection positivity on a set of observables.**  The physical statement takes `S = 𝔄₊`
(`ReflectionPositivity.PositiveTimeAlgebra`); the quotient construction consumes `S = univ`
(`IsReflectionPositive`), which is strictly stronger — see `mk_thetaObs_eq_mk`. -/
def IsReflectionPositiveOn (S : Set Observable) (ω : Observable → ℝ) : Prop :=
  ∀ F ∈ S, 0 ≤ osForm ω F F

/-- The full-algebra form implies every restricted form. -/
theorem IsReflectionPositive.isReflectionPositiveOn {ω : Observable → ℝ}
    (h : IsReflectionPositive ω) (S : Set Observable) : IsReflectionPositiveOn S ω :=
  fun F _ => h F

/-- **The state condition**: `ω(F²) ≥ 0`.  The expectation of a positive measure satisfies it;
it is what makes `ω` a state on the commutative observable algebra. -/
def IsPositiveFunctional (ω : Observable → ℝ) : Prop := ∀ F : Observable, 0 ≤ ω (F * F)

/-! ## Reflection positivity on `𝔄₊` from independence of the two halves -/

/-- **The half-space hypothesis from a factorised state.**  If the state is a *product* over
`𝔄₊ × θ𝔄₊` — `ω(θF · G) = ωF · ωG` for `F, G ∈ 𝔄₊`, which is the algebraic form of the two
half-spaces being independent under the reflected measure — then the OS form is nonnegative on
`𝔄₊`:

`⟨F, F⟩ = ω(θF · F) = ωF · ωF = (ωF)² ≥ 0`.

This is the **uncorrelated** case only — white noise, where the two halves are literally
independent.  A free field with a nonzero propagator does *not* satisfy it, and the mechanism of
the physical theorem is instead momentum space: `MomentumBasis.dft_mul_eq_convolution` (a product
of fields is a convolution of their momentum transforms) and
`MomentumBasis.reflection_positivity_momentum` (the transfer-factorised reflected kernel has an
OS form that is a sum of modulus squares, `w i ≥ 0`).  This theorem is kept as the exact statement
of the independence hypothesis and is not the route to Phase 3.3.  It is stated as a hypothesis,
not instantiated: the corpus has no measure on the lattice configurations `Config → ℝ` (see
`docs/euclidean_cft_proof.md`'s boundary note), so there is no such `ω` here. -/
theorem isReflectionPositiveOn_of_factorization (ω : Observable → ℝ) (S : Set Observable)
    (hprod : ∀ F ∈ S, ∀ G ∈ S, ω (thetaObs F * G) = ω F * ω G) :
    IsReflectionPositiveOn S ω := by
  intro F hF
  rw [osForm_apply, hprod F hF F hF]
  exact mul_self_nonneg (ω F)

/-- **The physical form of the hypothesis, on `𝔄₊`**, from independence of the halves. -/
theorem isReflectionPositiveOn_positiveTimeAlgebra_of_factorization {ω : Observable → ℝ}
    (hprod : ∀ F ∈ PositiveTimeAlgebra, ∀ G ∈ PositiveTimeAlgebra,
      ω (thetaObs F * G) = ω F * ω G) :
    IsReflectionPositiveOn (PositiveTimeAlgebra : Set Observable) ω :=
  isReflectionPositiveOn_of_factorization ω _ hprod

/-! ## The antisymmetric part of an observable -/

/-- `θ` reverses the sign of the antisymmetric part `F − θF`. -/
theorem thetaObs_sub_self (F : Observable) : thetaObs (F - thetaObs F) = -(F - thetaObs F) := by
  funext x
  simp only [thetaObs_apply, Pi.sub_apply, Pi.neg_apply, fieldReflection_involutive]
  ring

/-- **The OS form vanishes on the antisymmetric part of every observable.**

`⟨G,G⟩ = ω(θG · G) = −ω(G²)` for `G = F − θF`, so positivity of `ω` on squares forces
`⟨G,G⟩ ≤ 0`, while reflection positivity forces `⟨G,G⟩ ≥ 0`. -/
theorem osBilin_sub_theta_self_eq_zero (ω : LinearFunctional)
    (hRP : IsReflectionPositive fun F => ω.toFun F)
    (hpos : IsPositiveFunctional fun F => ω.toFun F) (F : Observable) :
    osBilin ω (F - thetaObs F) (F - thetaObs F) = 0 := by
  set G : Observable := F - thetaObs F with hG
  have hanti : thetaObs G = -G := thetaObs_sub_self F
  have hmul : thetaObs G * G = -(G * G) := by
    funext x
    simp only [Pi.mul_apply, hanti, Pi.neg_apply]
    ring
  have h1 : osBilin ω G G = -ω.toFun (G * G) := by
    simp only [osBilin, osForm, hmul]
    rw [show (-(G * G) : Observable) = (-1 : ℝ) • (G * G) from by funext x; simp]
    rw [ω.map_smul]
    ring
  have hstate : 0 ≤ ω.toFun (G * G) := hpos G
  have hnonneg : 0 ≤ osBilin ω G G := hRP G
  linarith

/-- **`F − θF` lies in the radical `𝔑`** (Cauchy–Schwarz, from the vanishing on the diagonal). -/
theorem sub_theta_self_mem_radical (ω : LinearFunctional)
    (hRP : IsReflectionPositive fun F => ω.toFun F)
    (hpos : IsPositiveFunctional fun F => ω.toFun F) (F : Observable) :
    F - thetaObs F ∈ Radical ω :=
  mem_radical_of_self_eq_zero ω hRP (osBilin_sub_theta_self_eq_zero ω hRP hpos F)

/-- **The reflection is the identity on the physical space**: `[θF] = [F]` in `𝔄 / 𝔑`.

Consequence: under full-algebra reflection positivity of a state there is no non-trivial time
reflection on `ℋ = 𝔄 / 𝔑` — the twisted sector is entirely null.  The physical hypothesis is
therefore the half-space one, `IsReflectionPositiveOn 𝔄₊ ω`. -/
theorem mk_thetaObs_eq_mk (ω : LinearFunctional)
    (hRP : IsReflectionPositive fun F => ω.toFun F)
    (hpos : IsPositiveFunctional fun F => ω.toFun F) (F : Observable) :
    (Submodule.Quotient.mk (thetaObs F) : Observable ⧸ Radical ω) = Submodule.Quotient.mk F := by
  refine (Submodule.Quotient.eq (Radical ω)).mpr ?_
  simpa using (Radical ω).neg_mem (sub_theta_self_mem_radical ω hRP hpos F)

end

end BookProof.OSReconstruction
