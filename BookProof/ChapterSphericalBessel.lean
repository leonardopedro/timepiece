import Mathlib

/-!
# Chapter — Hankel–Majorana transform: the spherical Bessel functions (Rayleigh formula)

Source: `book.tex`, §A.5 subsection *"Hankel–Majorana Transform"* (line ~5805),
Definitions 65–71.  There the author builds the spherical / Hankel–Majorana
transform out of the **spherical Bessel functions of the first kind** `jₗ`,
defined (Definition 67) by the **Rayleigh formula**

`jₗ(r) = rˡ (-(1/r) d/dr)ˡ (sin r / r)`.

These special functions are **not** available in Mathlib, so this file develops
the self-contained analytic core from scratch: the Rayleigh operator, the
generating function `j₀(r) = sin r / r`, and the first closed forms together
with the recurrence that links them and the defining second-order ODE.

Formalized here:

* `rayleighOp` — the Rayleigh differential operator `T f = -(1/r) f'`;
* `sbessel` — the spherical Bessel function via the book's Rayleigh formula
  `jₗ(r) = rˡ (Tˡ (sin r / r))(r)`;
* `sj0` / `sj1` / `sj2` — the classical closed forms
  `j₀ = sin r / r`, `j₁ = sin r / r² − cos r / r`,
  `j₂ = (3/r³ − 1/r) sin r − (3/r²) cos r`;
* `deriv_sbesselBase` — the derivative of the generator `sin r / r`;
* `sbessel_zero` / `sbessel_one_eq` / `sbessel_two_eq` — the Rayleigh formula
  reproduces the three closed forms;
* `rayleigh_raise_01` — the raising relation `j₁ = −(d/dr) j₀`;
* `sj0_satisfies_ode` — `j₀` solves the `l = 0` spherical Bessel ODE
  `r² j'' + 2 r j' + r² j = 0`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterSphericalBessel

open scoped Topology

/-- The Rayleigh differential operator `T f (r) = -(1/r) · f'(r)`, used in the
book's Rayleigh formula for the spherical Bessel functions. -/
noncomputable def rayleighOp (f : ℝ → ℝ) : ℝ → ℝ := fun r => -(1 / r) * deriv f r

/-- The generating function `j₀(r) = sin r / r` of the spherical Bessel family. -/
noncomputable def sbesselBase : ℝ → ℝ := fun r => Real.sin r / r

/-- The spherical Bessel function of the first kind, defined by the book's
Rayleigh formula (Definition 67):
`jₗ(r) = rˡ (-(1/r) d/dr)ˡ (sin r / r)`. -/
noncomputable def sbessel (l : ℕ) : ℝ → ℝ :=
  fun r => r ^ l * (rayleighOp^[l] sbesselBase) r

/-- Closed form for `j₀`. -/
noncomputable def sj0 : ℝ → ℝ := fun r => Real.sin r / r

/-- Closed form for `j₁`. -/
noncomputable def sj1 : ℝ → ℝ := fun r => Real.sin r / r ^ 2 - Real.cos r / r

/-- Closed form for `j₂`. -/
noncomputable def sj2 : ℝ → ℝ :=
  fun r => (3 / r ^ 3 - 1 / r) * Real.sin r - 3 / r ^ 2 * Real.cos r

/-- The derivative of the generating function `sin r / r`. -/
theorem deriv_sbesselBase {r : ℝ} (hr : r ≠ 0) :
    deriv sbesselBase r = Real.cos r / r - Real.sin r / r ^ 2 := by
  have hd : HasDerivAt (fun x => Real.sin x / x)
      ((Real.cos r * id r - Real.sin r * 1) / id r ^ 2) r :=
    HasDerivAt.div (Real.hasDerivAt_sin r) (hasDerivAt_id r) hr
  have heq : (Real.cos r * id r - Real.sin r * 1) / id r ^ 2
      = Real.cos r / r - Real.sin r / r ^ 2 := by
    simp only [id_eq, mul_one]
    field_simp [hr]
  rw [show sbesselBase = fun x => Real.sin x / x from rfl]
  rw [HasDerivAt.deriv hd, heq]

/-- The Rayleigh formula reproduces `j₀(r) = sin r / r`. -/
theorem sbessel_zero : sbessel 0 = sj0 := by
  funext r; simp [sbessel, sbesselBase, sj0]

/-- The Rayleigh formula reproduces `j₁(r) = sin r / r² − cos r / r`. -/
theorem sbessel_one_eq {r : ℝ} (hr : r ≠ 0) : sbessel 1 r = sj1 r := by
  have hd := deriv_sbesselBase hr
  simp only [sbessel, sj1, rayleighOp, Function.iterate_one, pow_one, hd]
  field_simp; ring

/-- The Rayleigh raising relation between the first two spherical Bessel
functions: `j₁ = −(d/dr) j₀`. -/
theorem rayleigh_raise_01 {r : ℝ} (hr : r ≠ 0) : sj1 r = -deriv sj0 r := by
  have hd : deriv sj0 r = Real.cos r / r - Real.sin r / r ^ 2 := deriv_sbesselBase hr
  rw [hd, sj1]; ring

/-- The Rayleigh formula reproduces
`j₂(r) = (3/r³ − 1/r) sin r − (3/r²) cos r`. -/
theorem sbessel_two_eq {r : ℝ} (hr : r ≠ 0) : sbessel 2 r = sj2 r := by
  have hee : deriv (rayleighOp sbesselBase) r
      = deriv (fun x => -(1 / x) * (Real.cos x / x - Real.sin x / x ^ 2)) r := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx
    simp only [rayleighOp, deriv_sbesselBase hx]
  have h2 : (rayleighOp^[2] sbesselBase) r
      = -(1 / r) * deriv (rayleighOp sbesselBase) r := rfl
  have hd2 : deriv (fun x => -(1 / x) * (Real.cos x / x - Real.sin x / x ^ 2)) r
      = Real.sin r / r ^ 2 + 3 * Real.cos r / r ^ 3 - 3 * Real.sin r / r ^ 4 := by
    have hcos : HasDerivAt (fun x => Real.cos x / x)
        ((-Real.sin r * id r - Real.cos r * 1) / id r ^ 2) r :=
      HasDerivAt.div (Real.hasDerivAt_cos r) (hasDerivAt_id r) hr
    have hsq : HasDerivAt (fun x => Real.sin x / x ^ 2)
        ((Real.cos r * (r ^ 2) - Real.sin r * (2 * r ^ 1)) / (r ^ 2) ^ 2) r :=
      HasDerivAt.div (Real.hasDerivAt_sin r) (hasDerivAt_pow 2 r)
        (pow_ne_zero 2 hr)
    have hdif : HasDerivAt (fun x => Real.cos x / x - Real.sin x / x ^ 2)
        (-Real.sin r / r - 2 * Real.cos r / r ^ 2 + 2 * Real.sin r / r ^ 3) r :=
      (hcos.sub hsq).congr_deriv (by simp only [id_eq, mul_one]; field_simp [hr]; ring)
    have hinv : HasDerivAt (fun x => -(1 / x)) (1 / r ^ 2) r := by
      have h : HasDerivAt (fun x => 1 / x) ((0 * id r - 1 * 1) / id r ^ 2) r :=
        HasDerivAt.div (hasDerivAt_const r 1) (hasDerivAt_id r) hr
      have hneg := h.neg
      have heq : -((0 * id r - 1 * 1) / id r ^ 2) = 1 / r ^ 2 := by
        simp only [id_eq, zero_mul, mul_one, zero_sub, neg_div, neg_neg]
      rw [heq] at hneg
      exact hneg
    have hprod := hinv.mul hdif
    refine HasDerivAt.deriv ?_
    convert hprod using 1
    · rfl
    · rfl
    · field_simp [hr]
      ring
  rw [sbessel, h2, hee, hd2, sj2]
  field_simp [hr]
  ring

/-- `j₀(r) = sin r / r` solves the `l = 0` spherical Bessel ODE
`r² j'' + 2 r j' + r² j = 0`. -/
theorem sj0_satisfies_ode {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * deriv (deriv sj0) r + 2 * r * deriv sj0 r + r ^ 2 * sj0 r = 0 := by
  have h1 : ∀ x ≠ 0, deriv sj0 x = Real.cos x / x - Real.sin x / x ^ 2 :=
    fun x hx => deriv_sbesselBase hx
  have h2 : deriv (deriv sj0) r
      = deriv (fun x => Real.cos x / x - Real.sin x / x ^ 2) r :=
    Filter.EventuallyEq.deriv_eq
      (Filter.eventuallyEq_of_mem (isOpen_compl_singleton.mem_nhds hr) h1)
  rw [h2, h1 r hr, sj0]
  have hd : HasDerivAt (fun x => Real.cos x / x - Real.sin x / x ^ 2)
      (-Real.sin r / r - 2 * Real.cos r / r ^ 2 + 2 * Real.sin r / r ^ 3) r := by
    have hcos : HasDerivAt (fun x => Real.cos x / x)
        ((-Real.sin r * id r - Real.cos r * 1) / id r ^ 2) r :=
      HasDerivAt.div (Real.hasDerivAt_cos r) (hasDerivAt_id r) hr
    have hsq : HasDerivAt (fun x => Real.sin x / x ^ 2)
        ((Real.cos r * (r ^ 2) - Real.sin r * (2 * r ^ 1)) / (r ^ 2) ^ 2) r :=
      HasDerivAt.div (Real.hasDerivAt_sin r) (hasDerivAt_pow 2 r)
        (pow_ne_zero 2 hr)
    exact (hcos.sub hsq).congr_deriv (by simp only [id_eq, mul_one]; field_simp [hr]; ring)
  rw [HasDerivAt.deriv hd]
  field_simp [hr]
  ring

end BookProof.ChapterSphericalBessel
