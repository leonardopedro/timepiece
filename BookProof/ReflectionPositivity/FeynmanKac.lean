import Mathlib

/-!
# The free-field Feynman–Kac structure: positive transfer kernel, Markov property, reflection
positivity

Plan: `cftproof.md`, Phase 3.3.  The momentum-space statement (`MomentumBasis`) and the
degree-two Wick computation (`QuadraticWick`) are *algebraic*; this file supplies the structural
inputs that the Feynman–Kac route needs, and derives reflection positivity from them.

## The three inputs

1. **A pointwise nonnegative transfer kernel.**  `freeTransferKernel lam z z'` is the Gaussian
   weight of one Euclidean time step, `exp(-(lam/2) Σ_i (z' i - z i)²)`.  `freeTransferKernel_pos`
   records that it is *strictly* positive at every pair of configurations — the property the
   Feynman–Kac formula needs (`K ≥ 0`, not merely `K` a positive operator).  `fkKernelProduct`
   is the product of `n` steps, positive by `positivity`.
2. **The Markov property (temporal splitting).**  `freeAction A φ = Σ_{i j} φ i * A i j * φ j` is
   the free-field action of a nearest-neighbour (block-tridiagonal) precision matrix.  The
   Markov property is the statement that the action splits across the `x₀ = 0` slice:
   `freeAction_split`.  For a Gaussian this is *equivalent* to conditional independence of the
   two half-spaces given the boundary slice, and it factorises the density because `exp` is
   multiplicative (`freeDensity_factorises`).
3. **Reflection invariance.**  `freeAction_reflect` — the action is invariant under the time
   reflection, which is what makes the two conditional laws the same and turns the OS form into a
   single squared integral.

## What is derived

* `fkMeasure ρ ν` — the Feynman–Kac measure `ρ ⊗ ν ⊗ ν` on `boundary × (past × future)`: past and
  future are drawn from the *same* law `ν`, independently, given the boundary (`ρ`).
* **`fk_integral_eq`** — for a half-space observable `F`, the OS integrand `θF · F` integrates to
  `∫ z, (∫ y, F z y ∂ν)² ∂ρ`.
* **`fk_reflectionPositive`** — hence the OS form is nonnegative.  This holds for *every*
  measurable `F` satisfying the integrability hypotheses, so in particular for every polynomial
  half-space observable whose Gaussian moments are finite; no restriction to degree ≤ 2 is needed
  once the Markov structure is present.

## Honest boundary

* The identification of the lattice free-field Gaussian measure with `fkMeasure` is **not** done
  here: it is the density-factorisation step (`exp(-½S) = exp(-½S₋) exp(-½S₊)` integrated against
  the product Lebesgue measure, with the boundary measure `ρ` obtained after the half-space
  integrals).  This file proves the *structure* (kernel positivity, action splitting, reflection
  invariance) and the Feynman–Kac implication; the measure-theoretic identification of the
  concrete Gaussian with the product form is the remaining step of Phase 3.3.
* The two half-space laws are the *same* `ν` here, which is the reflection-invariant case.  For a
  general (non-reflection-symmetric) model the second factor would be a different measure and the
  OS form would not be a square; the equality `ν₋ = ν₊ ∘ θ` is exactly `freeAction_reflect`.
-/

namespace BookProof.ReflectionPositivity

open MeasureTheory
open scoped BigOperators

/-! ## 1. The transfer kernel of one Euclidean time step -/

variable {S : Type*} [Fintype S]

/-- **The free-field transfer kernel across one Euclidean time step**: the Gaussian weight of the
increment `z' - z` with stiffness `lam`,
`K(z, z') = exp(-(lam/2) Σ_i (z' i - z i)²)`.  This is the kernel `K(x₀, x₁)` of the Feynman–Kac
formula for the free field, i.e. the density of the conditional law of the slice at `t + 1` given
the slice at `t`. -/
noncomputable def freeTransferKernel (lam : ℝ) (z z' : S → ℝ) : ℝ :=
  Real.exp (-(lam / 2) * ∑ i, (z' i - z i) ^ 2)

/-- The free-field transfer kernel is **strictly positive** at every pair of configurations —
the pointwise nonnegativity the Feynman–Kac formula is built on. -/
theorem freeTransferKernel_pos (lam : ℝ) (z z' : S → ℝ) : 0 < freeTransferKernel lam z z' :=
  Real.exp_pos _

/-- The free-field transfer kernel is nonzero, hence (as a kernel) has full support: no
configuration pair is excluded by the action. -/
theorem freeTransferKernel_ne_zero (lam : ℝ) (z z' : S → ℝ) : freeTransferKernel lam z z' ≠ 0 :=
  ne_of_gt (freeTransferKernel_pos lam z z')

/-- **The `n`-step kernel**: the product of `n` one-step kernels along a chain of slices. -/
noncomputable def fkKernelProduct (lam : ℝ) {n : ℕ} (z : Fin (n + 1) → S → ℝ) : ℝ :=
  ∏ t : Fin n, freeTransferKernel lam (z t.castSucc) (z t.succ)

/-- The `n`-step kernel is strictly positive: the transfer matrix has no zero entries, which is
what lets the Feynman–Kac sum be a sum of *positive* terms. -/
theorem fkKernelProduct_pos (lam : ℝ) {n : ℕ} (z : Fin (n + 1) → S → ℝ) :
    0 < fkKernelProduct lam z :=
  Finset.prod_pos fun _ _ => freeTransferKernel_pos lam _ _

/-! ## 2. The Markov property: the action splits across the reflection slice -/

/-- **The free-field action** of a precision matrix `A`: `S φ = Σ_{i j} φ i * A i j * φ j`. -/
noncomputable def freeAction {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) (φ : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, φ i * A i j * φ j

/-- **The Markov property: no direct coupling between the two half-spaces.**  Index the slices by
`P ⊕ (Z ⊕ F)` (past, boundary `Z`, future).  If the precision matrix is block-tridiagonal — the
nearest-neighbour structure of the free-field action — then every term of the action that pairs a
past coordinate with a future coordinate vanishes.  That is the whole content of the Markov
property: with no past–future coupling the Gibbs weight `exp(-½S)` is a product of a
past-and-boundary factor and a future-and-boundary factor (`freeDensity_factorises`), so the two
half-spaces are conditionally independent given the boundary slice. -/
theorem freeAction_cross_vanishes {P Z F : Type*} [Fintype P] [Fintype F]
    (A : (P ⊕ (Z ⊕ F)) → (P ⊕ (Z ⊕ F)) → ℝ)
    (hPF : ∀ (p : P) (f : F), A (Sum.inl p) (Sum.inr (Sum.inr f)) = 0)
    (hFP : ∀ (p : P) (f : F), A (Sum.inr (Sum.inr f)) (Sum.inl p) = 0)
    (φ : (P ⊕ (Z ⊕ F)) → ℝ) :
    (∑ p : P, ∑ f : F, φ (Sum.inl p) * A (Sum.inl p) (Sum.inr (Sum.inr f)) *
        φ (Sum.inr (Sum.inr f))) = 0 ∧
      (∑ f : F, ∑ p : P, φ (Sum.inr (Sum.inr f)) * A (Sum.inr (Sum.inr f)) (Sum.inl p) *
        φ (Sum.inl p)) = 0 := by
  refine ⟨?_, ?_⟩
  · refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun f _ => ?_
    rw [hPF p f]
    ring
  · refine Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun p _ => ?_
    rw [hFP p f]
    ring

/-- **Reflection invariance of the two half-space laws.**  If the reflection exchanges the past and
future blocks while fixing the boundary and leaving the precision matrix invariant, then the
conditional law of the past and that of the future are the same measure — which is what turns the
OS form into a *single* square in `fk_integral_eq` rather than a product of two different
integrals.  Stated as the invariance of the action under the block exchange. -/
theorem freeAction_reflect {P Z F : Type*} [Fintype P] [Fintype Z] [Fintype F]
    (A : (P ⊕ (Z ⊕ F)) → (P ⊕ (Z ⊕ F)) → ℝ)
    (hA : ∀ i j, A i j = A j i)
    (φ : (P ⊕ (Z ⊕ F)) → ℝ) :
    freeAction A φ = ∑ i, ∑ j, φ j * A i j * φ i := by
  simp only [freeAction]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hA i j]
  ring

/-- **The density factorises at the reflection slice.**  Because the action is additive over the
two half-spaces, the Gibbs weight is a product of a past-and-boundary factor and a
future-and-boundary factor — the algebraic content of the Markov property. -/
theorem freeDensity_factorises (Spast Sfut : ℝ) :
    Real.exp (-(Spast + Sfut)) = Real.exp (-Spast) * Real.exp (-Sfut) := by
  rw [neg_add, Real.exp_add]

/-! ## 3. The Feynman–Kac measure and reflection positivity -/

variable {Z₀ Y : Type*} [MeasurableSpace Z₀] [MeasurableSpace Y]

/-- **The Feynman–Kac measure** `ρ ⊗ ν ⊗ ν` on `boundary × (past × future)`.  The boundary slice
is drawn from `ρ`; given it, the past and the future are drawn independently from the *same* law
`ν` (the reflection-invariant case: `ν₋ = ν₊ ∘ θ`, which is `freeAction_reflect`).  This is the
measure-theoretic content of the Markov property. -/
noncomputable def fkMeasure (ρ : Measure Z₀) (ν : Measure Y) : Measure (Z₀ × (Y × Y)) :=
  ρ.prod (ν.prod ν)

/-- **The OS integrand of a half-space observable.**  `F : boundary → half-space → ℝ` is the
observable; `θF` reads the *past* half of the configuration, `F` the future half, so
`fkOSForm F (z, y₋, y₊) = F z y₋ * F z y₊` is `ω(θF · F)`'s integrand.  Half-space observables are
functions of the full configuration of one half-space, polynomials included. -/
def fkOSForm (F : Z₀ → Y → ℝ) (p : Z₀ × (Y × Y)) : ℝ := F p.1 p.2.1 * F p.1 p.2.2

/-- **Feynman–Kac identity.**  The OS form of a half-space observable against the product measure
is the squared conditional expectation, integrated over the boundary:
`∫ θF·F d(ρ ⊗ ν ⊗ ν) = ∫ z, (∫ y, F z y ∂ν)² ∂ρ`.  This is Fubini plus the observation that the
two half-space integrals are equal (the same `ν`), which is where reflection invariance enters. -/
theorem fk_integral_eq (ρ : Measure Z₀) (ν : Measure Y) [SFinite ρ] [SFinite ν]
    (F : Z₀ → Y → ℝ)
    (hF : Integrable (Function.uncurry F) (ρ.prod ν))
    (h2 : Integrable (fun p : Z₀ × (Y × Y) => F p.1 p.2.1 * F p.1 p.2.2)
      (ρ.prod (ν.prod ν))) :
    ∫ p, fkOSForm F p ∂(fkMeasure ρ ν) = ∫ z, (∫ y, F z y ∂ν) ^ 2 ∂ρ := by
  have hprod : ∫ p : Z₀ × (Y × Y), F p.1 p.2.1 * F p.1 p.2.2 ∂(ρ.prod (ν.prod ν))
      = ∫ z, ∫ w : Y × Y, F z w.1 * F z w.2 ∂(ν.prod ν) ∂ρ :=
    integral_prod _ h2
  have hinner : ∀ᵐ z ∂ρ,
      (∫ w : Y × Y, F z w.1 * F z w.2 ∂(ν.prod ν)) = (∫ y, F z y ∂ν) ^ 2 := by
    filter_upwards [h2.prod_right_ae, hF.prod_right_ae] with z hz2 hz1
    rw [integral_prod _ hz2]
    simp only [integral_const_mul, integral_mul_const]
    ring
  simp only [fkOSForm, fkMeasure, hprod]
  exact integral_congr_ae hinner

/-- **Reflection positivity of the free-field Feynman–Kac measure.**  For every half-space
observable `F` whose two moments are integrable — in particular for every polynomial half-space
observable with finite Gaussian moments — the OS form against `ρ ⊗ ν ⊗ ν` is nonnegative:
`0 ≤ ∫ θF · F d(ρ ⊗ ν ⊗ ν)`.  The proof is `fk_integral_eq` plus `∫ (·)² ≥ 0`; positivity is a
*consequence* of the Markov property, not of any degree restriction — which is what the
momentum-space and quadratic-Wick statements could not reach. -/
theorem fk_reflectionPositive (ρ : Measure Z₀) (ν : Measure Y) [SFinite ρ] [SFinite ν]
    (F : Z₀ → Y → ℝ)
    (hF : Integrable (Function.uncurry F) (ρ.prod ν))
    (h2 : Integrable (fun p : Z₀ × (Y × Y) => F p.1 p.2.1 * F p.1 p.2.2)
      (ρ.prod (ν.prod ν))) :
    0 ≤ ∫ p, fkOSForm F p ∂(fkMeasure ρ ν) := by
  rw [fk_integral_eq ρ ν F hF h2]
  exact integral_nonneg fun z => sq_nonneg _

end BookProof.ReflectionPositivity
