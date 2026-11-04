import Mathlib
import BookProof.ReflectionPositivity.FeynmanKac

/-!
# The lattice Gaussian free field *is* `ρ ⊗ ν_z ⊗ ν_z`

`BookProof.ReflectionPositivity.FeynmanKac` proves the Feynman–Kac identity and reflection
positivity for the product measure `fkMeasure ρ ν = ρ.prod (ν.prod ν)` — but with a *single*
law `ν`, independent of the boundary slice.  For the free field that is not the model: the law of
a half-space *given* the reflection slice depends on the slice, `ν = ν_z` (a kernel).  Its
`Honest boundary` names precisely this gap: "the identification of the lattice Gaussian with
`fkMeasure` … is the remaining step".

This chapter closes that gap for the free field, in the kernel form the free field actually has.

## Contents

* `fkKernelMeasure ρd νd` — the Feynman–Kac form `ρ ⊗ ν_z ⊗ ν_z` on
  `boundary × (past × future)`: the boundary slice `z` is drawn with density `ρd`, and given `z`
  the past and the future are drawn *independently* from the same density `νd z`.  The dependence
  of `νd` on `z` is the only difference from `fkMeasure`, and it is exactly what the free field
  needs.
* **`fkKernel_integral_eq`** — the kernel Feynman–Kac identity
  `∫ θF·F d(ρ ⊗ ν_z ⊗ ν_z) = ∫ z, (∫ y, F z y ∂ν_z)² ∂ρ`.
* **`fkKernel_reflectionPositive`** — hence the OS form of the kernel form is nonnegative, for
  every half-space observable with integrable moments.  No degree restriction, and no hypothesis
  that `ν` be `z`-independent.
* The **lattice Gaussian free field**: `latticeGFFMeasure m` is the (unnormalised) Gibbs measure
  of the free field on `n` Euclidean time steps per half-space — `2n + 1` slices with the
  reflection slice in the middle — with the nearest-neighbour action
  `S = Σ_t Σ_i (φ(t+1)ᵢ − φ(t)ᵢ)² + (m/2) Σ_t Σ_i φ(t)ᵢ²`;
* **`latticeGFFMeasure_eq_fkKernelMeasure`** — **the identification**: the action splits at the
  reflection slice into the same half-space action on both sides plus the mass term of the slice,
  `S = h(z,y₋) + h(z,y₊) + d(z)`, so the measure is exactly `ρ ⊗ ν_z ⊗ ν_z` with
  `ρ = exp(−d)` and `ν_z = exp(−h(z,·))`;
* **`latticeGFF_reflectionPositive`** — reflection positivity of the concrete lattice free
  field, for every half-space observable with integrable moments.

## Why this is the right form for the free field

The precision matrix of the action is block-tridiagonal in the time slicing: `φ(t)` couples only
to `φ(t±1)` and to itself.  Hence no term of `S` pairs a past slice with a future slice — the
Markov property of `FeynmanKac.freeAction_cross_vanishes` — and the Gibbs density factorises,
`exp(−S) = exp(−h(z,y₋)) · exp(−h(z,y₊)) · exp(−d(z))`.  Reflection invariance of the action is
what makes the *two* factors the same function `h`, i.e. `ν₋ = ν₊ = ν_z`; without it the OS form
would be a product of two different half-space integrals and the square would be lost.

## Honest boundary

The identity is proved for the *unnormalised* Gibbs density: `latticeGFFMeasure` is
`volume.withDensity exp(−S)`, and the normalising constant `Z = ∫ exp(−S)` is not evaluated (it
cancels from both sides, and reflection positivity is invariant under a positive rescaling).  The
positivity statement therefore does not require `m > 0`; finiteness of the measure does, and is
not claimed.  Nothing here is a statement about the *interacting* Wilson measure: the split of
the action at the reflection slice is the Markov property of a *Gaussian* (nearest-neighbour)
action, and the non-Gaussian quartic term does not factorise this way.
-/

namespace BookProof.ReflectionPositivity

open MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## 1. The kernel Feynman–Kac form `ρ ⊗ ν_z ⊗ ν_z` -/

variable {Z₀ Y : Type*} [MeasureSpace Z₀] [MeasureSpace Y]
variable [SFinite (volume : Measure Z₀)] [SFinite (volume : Measure Y)]

/-- The density of `fkKernelMeasure`, as a real function:
`ρd z · νd z y₋ · νd z y₊`. -/
def fkKernelDensity (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ) (p : Z₀ × (Y × Y)) : ℝ :=
  ρd p.1 * νd p.1 p.2.1 * νd p.1 p.2.2

/-- **The kernel Feynman–Kac measure** `ρ ⊗ ν_z ⊗ ν_z` on `Z₀ × (Y × Y)`: the boundary slice `z`
first, then given it the past and the future independently from the *same* boundary-dependent
law `νd z`.  This is `fkMeasure` with `ν` replaced by a kernel, which is what the free field
requires. -/
def fkKernelMeasure (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ) : Measure (Z₀ × (Y × Y)) :=
  ((volume : Measure Z₀).prod ((volume : Measure Y).prod (volume : Measure Y))).withDensity
    (fun p => ENNReal.ofReal (fkKernelDensity ρd νd p))

theorem fkKernelMeasure_eq (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ) :
    fkKernelMeasure ρd νd
      = ((volume : Measure Z₀).prod
            ((volume : Measure Y).prod (volume : Measure Y))).withDensity
          (fun p => ENNReal.ofReal (fkKernelDensity ρd νd p)) := rfl

/-- The kernel density is nonnegative when its two factors are. -/
theorem fkKernelDensity_nonneg {ρd : Z₀ → ℝ} {νd : Z₀ → Y → ℝ}
    (hρ : ∀ z, 0 ≤ ρd z) (hν : ∀ z y, 0 ≤ νd z y) (p : Z₀ × (Y × Y)) :
    0 ≤ fkKernelDensity ρd νd p := by
  simp only [fkKernelDensity]
  exact mul_nonneg (mul_nonneg (hρ p.1) (hν p.1 p.2.1)) (hν p.1 p.2.2)

/-- **Fubini step of the kernel Feynman–Kac identity**: at a fixed boundary slice, integrating the
OS integrand against the density gives the square of the half-space integral, times the boundary
weight.  The two factors are the same function `νd z`, which is where reflection invariance
enters. -/
theorem fkKernel_inner (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ) (F : Z₀ → Y → ℝ) (z : Z₀) :
    ∫ w : Y × Y, fkKernelDensity ρd νd (z, w) * fkOSForm F (z, w)
        ∂((volume : Measure Y).prod (volume : Measure Y))
      = (∫ y, F z y * νd z y ∂(volume : Measure Y)) ^ 2 * ρd z := by
  have hstep : ∫ w : Y × Y, fkKernelDensity ρd νd (z, w) * fkOSForm F (z, w)
        ∂((volume : Measure Y).prod (volume : Measure Y))
      = ρd z * ∫ w : Y × Y, (F z w.1 * νd z w.1) * (F z w.2 * νd z w.2)
          ∂((volume : Measure Y).prod (volume : Measure Y)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [fkOSForm, fkKernelDensity]
    ring
  rw [hstep, integral_prod_mul (f := fun y => F z y * νd z y) (g := fun y => F z y * νd z y)]
  ring

/-- **The kernel Feynman–Kac identity.**  For a half-space observable `F`,
`∫ θF·F d(ρ ⊗ ν_z ⊗ ν_z) = ∫ z, (∫ y, F z y dν_z)² dρ`: the OS form of the free field is a
*single* square, integrated over the reflection slice. -/
theorem fkKernel_integral_eq (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ) (F : Z₀ → Y → ℝ)
    (hD : Measurable fun p : Z₀ × (Y × Y) => fkKernelDensity ρd νd p)
    (hρ : ∀ z, 0 ≤ ρd z) (hν : ∀ z y, 0 ≤ νd z y)
    (hint : Integrable (fun p : Z₀ × (Y × Y) => fkKernelDensity ρd νd p * fkOSForm F p)
      ((volume : Measure Z₀).prod ((volume : Measure Y).prod (volume : Measure Y)))) :
    ∫ p, fkOSForm F p ∂(fkKernelMeasure ρd νd)
      = ∫ z, (∫ y, F z y * νd z y ∂(volume : Measure Y)) ^ 2 * ρd z ∂(volume : Measure Z₀) := by
  rw [fkKernelMeasure_eq,
    integral_withDensity_eq_integral_toReal_smul (f_meas := Measurable.ennreal_ofReal hD)
      (hf_lt_top := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have htc : ∀ p : Z₀ × (Y × Y),
      (ENNReal.ofReal (fkKernelDensity ρd νd p)).toReal = fkKernelDensity ρd νd p :=
    fun p => ENNReal.toReal_ofReal (fkKernelDensity_nonneg hρ hν p)
  simp only [htc, smul_eq_mul]
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact fkKernel_inner ρd νd F z

/-- **Reflection positivity of the kernel Feynman–Kac form**: for every half-space observable
whose OS integrand is integrable, `0 ≤ ∫ θF·F d(ρ ⊗ ν_z ⊗ ν_z)`.  No degree restriction, and the
half-space law may depend on the boundary slice. -/
theorem fkKernel_reflectionPositive (ρd : Z₀ → ℝ) (νd : Z₀ → Y → ℝ) (F : Z₀ → Y → ℝ)
    (hD : Measurable fun p : Z₀ × (Y × Y) => fkKernelDensity ρd νd p)
    (hρ : ∀ z, 0 ≤ ρd z) (hν : ∀ z y, 0 ≤ νd z y)
    (hint : Integrable (fun p : Z₀ × (Y × Y) => fkKernelDensity ρd νd p * fkOSForm F p)
      ((volume : Measure Z₀).prod ((volume : Measure Y).prod (volume : Measure Y)))) :
    0 ≤ ∫ p, fkOSForm F p ∂(fkKernelMeasure ρd νd) := by
  rw [fkKernel_integral_eq ρd νd F hD hρ hν hint]
  refine integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hρ z)

/-! ## 2. The lattice Gaussian free field -/

variable {S : Type*} [Fintype S]

/-- The half-space configuration `z, y 0, …, y (n−1)` as a chain of `n + 1` Euclidean slices,
starting at the reflection slice `z`. -/
def chain {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) : Fin (n + 1) → S → ℝ :=
  fun k => Fin.cases z (fun j => y j) k

/-- **The half-space action**: the free-field action of one half-space, `n` time steps from the
reflection slice `z` inwards,
`Σ_k Σ_i (φ_{k+1} − φ_k)² + (m/2) Σ_k Σ_i φ_{k+1}²`,
with the mass term of the reflection slice itself *excluded* (it belongs to the boundary law
`ρ`, see `boundaryTerm`).  The past and the future half-space both use this same function — that
is the reflection invariance which makes the OS form a square. -/
def halfAction (m : ℝ) {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) : ℝ :=
  (∑ k : Fin n, ∑ i, (chain z y k.succ i - chain z y k.castSucc i) ^ 2)
    + (m / 2) * ∑ k : Fin n, ∑ i, (chain z y k.succ i) ^ 2

/-- **The boundary term**: the mass term of the reflection slice.  It depends on `z` only, so in
the product form it is the density of the boundary law `ρ`. -/
def boundaryTerm (m : ℝ) (z : S → ℝ) : ℝ := (m / 2) * ∑ i, (z i) ^ 2

/-- **The lattice free-field action** on `boundary × (past × future)`: the half-space action on
each side plus the boundary term.  This is the nearest-neighbour action
`Σ_t Σ_i (φ(t+1)ᵢ − φ(t)ᵢ)² + (m/2) Σ_t Σ_i φ(t)ᵢ²` of the `2n + 1` slices, split at the
reflection slice. -/
def latticeAction (m : ℝ) {n : ℕ}
    (p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) : ℝ :=
  halfAction m p.1 p.2.1 + halfAction m p.1 p.2.2 + boundaryTerm m p.1

/-- The boundary density `ρ = exp(−d)`. -/
def boundaryWeight (m : ℝ) (z : S → ℝ) : ℝ := Real.exp (-(boundaryTerm m z))

/-- The half-space kernel density `ν_z = exp(−h(z,·))`. -/
def halfWeight (m : ℝ) {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) : ℝ :=
  Real.exp (-(halfAction m z y))

/-- **The Gibbs measure of the lattice Gaussian free field** (unnormalised): the density
`exp(−S)` against the product Lebesgue measure on `boundary × (past × future)`. -/
def latticeGFFMeasure (m : ℝ) {n : ℕ} :
    Measure ((S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) :=
  ((volume : Measure (S → ℝ)).prod
      ((volume : Measure (Fin n → S → ℝ)).prod (volume : Measure (Fin n → S → ℝ)))).withDensity
    (fun p => ENNReal.ofReal (Real.exp (-(latticeAction m p))))

/-! ### Measurability of the action

The action is a sum of squares of coordinate projections: `chain z y k` is either the boundary
slice `z` or the interior slice `y j`, so every term is measurable in `(z, y)`. -/

theorem measurable_chain {n : ℕ} (k : Fin (n + 1)) :
    Measurable fun q : (S → ℝ) × (Fin n → S → ℝ) => chain q.1 q.2 k := by
  induction k using Fin.cases with
  | zero =>
    simpa [chain] using
      (measurable_fst : Measurable fun q : (S → ℝ) × (Fin n → S → ℝ) => q.1)
  | succ j =>
    simpa [chain] using
      (measurable_pi_apply j).comp
        (measurable_snd : Measurable fun q : (S → ℝ) × (Fin n → S → ℝ) => q.2)

theorem measurable_chain_apply {n : ℕ} (k : Fin (n + 1)) (i : S) :
    Measurable fun q : (S → ℝ) × (Fin n → S → ℝ) => chain q.1 q.2 k i :=
  (measurable_pi_apply i).comp (measurable_chain k)

theorem measurable_halfAction (m : ℝ) {n : ℕ} :
    Measurable fun q : (S → ℝ) × (Fin n → S → ℝ) => halfAction m q.1 q.2 := by
  unfold halfAction
  refine Measurable.add ?_ (Measurable.mul measurable_const ?_)
  · refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun i _ => ?_
    exact (((measurable_chain_apply k.succ i).sub
      (measurable_chain_apply k.castSucc i))).pow_const 2
  · refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun i _ => ?_
    exact (measurable_chain_apply k.succ i).pow_const 2

theorem measurable_boundaryTerm (m : ℝ) :
    Measurable fun z : S → ℝ => boundaryTerm m z := by
  unfold boundaryTerm
  refine Measurable.mul measurable_const ?_
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).pow_const 2

set_option maxHeartbeats 1000000 in
-- the `Pi` measurable-space unifications need more than the default budget
theorem measurable_latticeAction (m : ℝ) {n : ℕ} :
    Measurable fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
      latticeAction m p := by
  have hpair₁ : Measurable fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
      (p.1, p.2.1) := by fun_prop
  have hpair₂ : Measurable fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
      (p.1, p.2.2) := by fun_prop
  have hfst : Measurable fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) => p.1 :=
    measurable_fst
  have hb : Measurable fun z : S → ℝ => boundaryTerm m z := measurable_boundaryTerm m
  have h := ((measurable_halfAction (S := S) (n := n) m).comp hpair₁).add
    (((measurable_halfAction (S := S) (n := n) m).comp hpair₂).add (hb.comp hfst))
  unfold latticeAction
  simpa only [Function.comp_apply, add_assoc] using h

/-! ### The identification and reflection positivity -/

/-- **The density factorises at the reflection slice.**  This is the Markov property in density
form: `exp(−S) = exp(−d) · exp(−h(z,y₋)) · exp(−h(z,y₊))`, because `S` is the sum of the two
half-space actions and the boundary term, and `exp` is multiplicative. -/
theorem fkKernelDensity_lattice (m : ℝ) {n : ℕ}
    (p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) :
    fkKernelDensity (boundaryWeight m) (halfWeight (S := S) m) p
      = Real.exp (-(latticeAction m p)) := by
  simp only [fkKernelDensity, boundaryWeight, halfWeight, latticeAction, ← Real.exp_add]
  congr 1
  ring

/-- **The identification**: the lattice Gaussian free field is exactly `ρ ⊗ ν_z ⊗ ν_z` — the
boundary slice with law `ρ`, then the two half-spaces independently from the same
boundary-dependent law `ν_z`. -/
theorem latticeGFFMeasure_eq_fkKernelMeasure (m : ℝ) {n : ℕ} :
    latticeGFFMeasure (S := S) m
      = fkKernelMeasure (Z₀ := S → ℝ) (Y := Fin n → S → ℝ)
          (boundaryWeight (S := S) m) (halfWeight (S := S) m) := by
  rw [latticeGFFMeasure, fkKernelMeasure_eq]
  congr 1
  funext p
  rw [fkKernelDensity_lattice]

/-- **The Feynman–Kac identity for the lattice free field**: the OS form of a half-space
observable is the squared conditional expectation, integrated over the reflection slice. -/
theorem latticeGFF_integral_eq (m : ℝ) {n : ℕ}
    (F : (S → ℝ) → (Fin n → S → ℝ) → ℝ)
    (hint : Integrable
      (fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
        Real.exp (-(latticeAction m p)) * fkOSForm F p)
      ((volume : Measure (S → ℝ)).prod
        ((volume : Measure (Fin n → S → ℝ)).prod (volume : Measure (Fin n → S → ℝ))))) :
    ∫ p, fkOSForm F p ∂(latticeGFFMeasure (S := S) m)
      = ∫ z, (∫ y, F z y * halfWeight m z y ∂(volume : Measure (Fin n → S → ℝ))) ^ 2
          * boundaryWeight m z ∂(volume : Measure (S → ℝ)) := by
  rw [latticeGFFMeasure_eq_fkKernelMeasure]
  refine fkKernel_integral_eq (Z₀ := S → ℝ) (Y := Fin n → S → ℝ)
    (boundaryWeight (S := S) m) (halfWeight (S := S) (n := n) m) F ?_ ?_ ?_ ?_
  · have hexp : Measurable fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
        Real.exp (-(latticeAction m p)) := (measurable_latticeAction (S := S) (n := n) m).neg.exp
    simpa only [fkKernelDensity_lattice] using hexp
  · intro z
    exact (Real.exp_pos _).le
  · intro z y
    exact (Real.exp_pos _).le
  · simpa only [fkKernelDensity_lattice] using hint

/-- **Reflection positivity of the lattice Gaussian free field** (plan Phase 3.3, free field):
for every half-space observable whose OS integrand is integrable — in particular every polynomial
in the half-space configuration with finite Gaussian moments — the OS form is nonnegative. -/
theorem latticeGFF_reflectionPositive (m : ℝ) {n : ℕ}
    (F : (S → ℝ) → (Fin n → S → ℝ) → ℝ)
    (hint : Integrable
      (fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
        Real.exp (-(latticeAction m p)) * fkOSForm F p)
      ((volume : Measure (S → ℝ)).prod
        ((volume : Measure (Fin n → S → ℝ)).prod (volume : Measure (Fin n → S → ℝ))))) :
    0 ≤ ∫ p, fkOSForm F p ∂(latticeGFFMeasure (S := S) m) := by
  rw [latticeGFFMeasure_eq_fkKernelMeasure]
  refine fkKernel_reflectionPositive (Z₀ := S → ℝ) (Y := Fin n → S → ℝ)
    (boundaryWeight (S := S) m) (halfWeight (S := S) (n := n) m) F ?_ ?_ ?_ ?_
  · have hexp : Measurable fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
        Real.exp (-(latticeAction m p)) := (measurable_latticeAction (S := S) (n := n) m).neg.exp
    simpa only [fkKernelDensity_lattice] using hexp
  · intro z
    exact (Real.exp_pos _).le
  · intro z y
    exact (Real.exp_pos _).le
  · simpa only [fkKernelDensity_lattice] using hint

end

end BookProof.ReflectionPositivity
