import Mathlib
import BookProof.ChapterSphericalBessel

/-!
# Chapter — Hankel–Majorana transform: the next spherical Bessel function `j₃`

Source: `book.tex`, §A.5 subsection *"Hankel–Majorana Transform"* (line ~5805),
Definitions 65–71.  This file extends `BookProof.ChapterSphericalBessel`
(which established `j₀, j₁, j₂`, the Rayleigh formula, and the `l = 0` ODE) one
order further, to the spherical Bessel function of the first kind `j₃`.

Formalized here (all reusing the base module's `sbessel`, `sj1`, `sj2`, and the
Rayleigh machinery):

* `sj3` — the classical closed form
  `j₃(r) = (15/r⁴ − 6/r²) sin r − (15/r³ − 1/r) cos r`;
* `deriv_sj2` — the first derivative of the closed form `j₂`;
* `sbessel_three_eq` — the Rayleigh formula reproduces `j₃`: `sbessel 3 r = j₃ r`;
* `sbessel_recurrence_123` — the three-term recurrence
  `jₗ₋₁ + jₗ₊₁ = (2l+1)/r · jₗ` at `l = 2`: `j₁(r) + j₃(r) = (5/r) · j₂(r)`;
* `deriv_recurrence_sj2` — the differentiation law
  `d/dr jₗ = jₗ₋₁ − (l+1)/r · jₗ` at `l = 2`: `d/dr j₂ = j₁ − (3/r) · j₂`;
* `sj3_satisfies_ode` — `j₃` solves the `l = 3` spherical Bessel ODE
  `r² j'' + 2 r j' + (r² − 12) j = 0` (`l(l+1) = 12`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterSphericalBessel

open scoped Topology

/-- Closed form for `j₃`:
`j₃(r) = (15/r⁴ − 6/r²) sin r − (15/r³ − 1/r) cos r`. -/
noncomputable def sj3 : ℝ → ℝ :=
  fun r => (15 / r ^ 4 - 6 / r ^ 2) * Real.sin r - (15 / r ^ 3 - 1 / r) * Real.cos r

/-
The first derivative of the closed form `j₂`:
`d/dr j₂ = (−9/r⁴ + 4/r²) sin r + (9/r³ − 1/r) cos r`.
-/
theorem deriv_sj2 {r : ℝ} (hr : r ≠ 0) :
    deriv sj2 r =
      (-9 / r ^ 4 + 4 / r ^ 2) * Real.sin r + (9 / r ^ 3 - 1 / r) * Real.cos r := by
  unfold sj2; norm_num [ hr, Real.differentiableAt_sin, Real.differentiableAt_cos, differentiableAt_inv ] ; ring;
  grind

/-
The Rayleigh formula reproduces
`j₃(r) = (15/r⁴ − 6/r²) sin r − (15/r³ − 1/r) cos r`.
-/
theorem sbessel_three_eq {r : ℝ} (hr : r ≠ 0) : sbessel 3 r = sj3 r := by
  have h_rayleigh : (rayleighOp^[3] sbesselBase) r = - (1 / r) * (deriv (fun x => sj2 x / x ^ 2) r) := by
    have h_rayleigh : ∀ x, x ≠ 0 → (rayleighOp^[2] sbesselBase) x = sj2 x / x ^ 2 := by
      intros x hx
      have h_rayleigh : sbessel 2 x = x ^ 2 * (rayleighOp^[2] sbesselBase) x := by
        rfl;
      rw [ eq_div_iff ( pow_ne_zero 2 hx ), mul_comm, ← h_rayleigh, sbessel_two_eq hx ];
    convert congr_arg ( fun x => - ( 1 / r ) * x ) ( Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_of_mem ( isOpen_ne.mem_nhds hr ) fun x hx => h_rayleigh x hx ) using 1;
  unfold sbessel; simp_all +decide [ Function.iterate_succ_apply' ] ;
  unfold sj2 sj3; norm_num [ hr, Real.differentiableAt_sin, Real.differentiableAt_cos, differentiableAt_inv ] ; ring;
  grind

/-
The three-term recurrence `jₗ₋₁ + jₗ₊₁ = (2l+1)/r · jₗ` at `l = 2`:
`j₁(r) + j₃(r) = (5/r) · j₂(r)`.
-/
theorem sbessel_recurrence_123 {r : ℝ} (hr : r ≠ 0) :
    sj1 r + sj3 r = (5 / r) * sj2 r := by
  unfold sj1 sj2 sj3; ring;

/-
The differentiation law `d/dr jₗ = jₗ₋₁ − (l+1)/r · jₗ` at `l = 2`:
`d/dr j₂ = j₁ − (3/r) · j₂`.
-/
theorem deriv_recurrence_sj2 {r : ℝ} (hr : r ≠ 0) :
    deriv sj2 r = sj1 r - (3 / r) * sj2 r := by
  convert deriv_sj2 hr using 1 ; unfold sj1 sj2 ; ring

/-
`j₃` solves the `l = 3` spherical Bessel ODE
`r² j'' + 2 r j' + (r² − 12) j = 0` (`l(l+1) = 12`).
-/
theorem sj3_satisfies_ode {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * deriv (deriv sj3) r + 2 * r * deriv sj3 r + (r ^ 2 - 12) * sj3 r = 0 := by
  have h1 : ∀ x, x ≠ 0 → deriv sj3 x = (-60 / x ^ 5 + 27 / x ^ 3 - 1 / x) * Real.sin x + (60 / x ^ 4 - 7 / x ^ 2) * Real.cos x := by
    intro x hx; unfold sj3; norm_num [ hx, Real.differentiableAt_sin, Real.differentiableAt_cos, differentiableAt_inv ] ; ring;
    grind;
  rw [ show deriv ( deriv sj3 ) r = deriv ( fun x ↦ ( -60 / x ^ 5 + 27 / x ^ 3 - 1 / x ) * Real.sin x + ( 60 / x ^ 4 - 7 / x ^ 2 ) * Real.cos x ) r by exact Filter.EventuallyEq.deriv_eq ( by filter_upwards [ IsOpen.mem_nhds isOpen_ne hr ] with x hx using h1 x hx ) ];
  norm_num [ hr, Real.differentiableAt_sin, Real.differentiableAt_cos, differentiableAt_inv, h1 ];
  unfold sj3; ring;
  grind +splitIndPred

end BookProof.ChapterSphericalBessel