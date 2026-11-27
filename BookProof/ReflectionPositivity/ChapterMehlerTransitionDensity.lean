import Mathlib
import BookProof.MCMC.MehlerEigenfunction
import BookProof.ReflectionPositivity.FeynmanKac

/-!
# Chapter MehlerTransitionDensity — H1's closed-form kernel and Feynman–Kac bridge

`cftproof.md` H1 asks for the closed-form Mehler transition density `K_ε(x,y)` and a bridge
to `FeynmanKac.freeTransferKernel`.  The corpus has the *operator* form
`MehlerEigenfunction.mehlerOp` (`ρ x + √(1−ρ²) y` against a normalized Gaussian) and the
*lattice* kernel `freeTransferKernel lam` (`exp(−(lam/2)Σ(z'−z)²)`), but no density in closed
form.  This module supplies it:

* `mehlerKernel ρ x z = (√(π(1−ρ²)))⁻¹ exp(−(z−ρx)²/(1−ρ²))` for `ρ² < 1`;
* `mehlerKernel_pos` and `mehlerKernel_integral` — positivity and unit mass;
* `mehlerKernel_eq_freeTransferKernel` — on a one-site configuration space the exponent is
  exactly `freeTransferKernel (2/(1−ρ²))`, so the Mehler density is a normalized free
  transfer kernel with drift `ρx` and stiffness `2/(1−ρ²)`;
* `mehlerOp_eq_integral_mehlerKernel` — the density realizes the pCN operator as
  `∫ z, f z * K(x,z) dz`, by translation and scaling of the Lebesgue integral.

This is the analytic equivalence at the level of one Euclidean slice.  No `N → ∞` limit,
Markov path measure, reflection positivity of the interacting theory or cutoff removal is
proved here (H3/H7).  Axioms are `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.MehlerTransitionDensity

open BookProof.MCMC
open BookProof.ReflectionPositivity

/-- The closed-form transition density of one Mehler/pCN step at parameter `ρ` with
    `ρ² < 1`: mean `ρx`, variance `(1−ρ²)/2` in the physicists' normalization. -/
def mehlerKernel (ρ x z : ℝ) : ℝ :=
  (Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ *
    Real.exp (-(z - ρ * x) ^ 2 / (1 - ρ ^ 2))

/-- The density is strictly positive everywhere. -/
theorem mehlerKernel_pos {ρ : ℝ} (hρ : ρ ^ 2 < 1) (x z : ℝ) : 0 < mehlerKernel ρ x z := by
  have hpi : 0 < Real.pi * (1 - ρ ^ 2) := mul_pos Real.pi_pos (by linarith)
  dsimp [mehlerKernel]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.2 hpi)) (Real.exp_pos _)

/-- The Mehler density is a normalized `freeTransferKernel`: the square exponent of the
    latter at stiffness `2/(1−ρ²)` is exactly the Mehler exponent. -/
theorem mehlerKernel_eq_freeTransferKernel {ρ x z : ℝ} (hρ : ρ ^ 2 < 1) :
    mehlerKernel ρ x z =
      (Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ *
        freeTransferKernel (2 / (1 - ρ ^ 2)) (fun _ : Fin 1 => ρ * x) (fun _ : Fin 1 => z) := by
  have hden : 1 - ρ ^ 2 ≠ 0 := by linarith
  dsimp [mehlerKernel, freeTransferKernel]
  congr 1
  rw [Fin.sum_univ_one]
  field_simp [hden]

/-- At the stationary parameter `ρ = 0` the kernel is the standard Gaussian density,
    independent of the starting configuration. -/
theorem mehlerKernel_zero (x z : ℝ) :
    mehlerKernel 0 x z = (Real.sqrt Real.pi)⁻¹ * Real.exp (-(z ^ 2)) := by
  dsimp [mehlerKernel]
  norm_num

/-- The density integrates to one over the final configuration. -/
theorem mehlerKernel_integral {ρ : ℝ} (hρ : ρ ^ 2 < 1) (x : ℝ) :
    (∫ z : ℝ, mehlerKernel ρ x z) = 1 := by
  have hdenpos : 0 < 1 - ρ ^ 2 := by linarith
  have ha : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.2 hdenpos
  have htrans : (∫ z : ℝ, Real.exp (-(z - ρ * x) ^ 2 / (1 - ρ ^ 2))) =
      ∫ u : ℝ, Real.exp (-(u ^ 2) / (1 - ρ ^ 2)) := by
    let g : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / (1 - ρ ^ 2))
    have h := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume) g (-(ρ * x))
    simpa [g, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hgauss : (∫ u : ℝ, Real.exp (-(u ^ 2) / (1 - ρ ^ 2))) =
      Real.sqrt (Real.pi * (1 - ρ ^ 2)) := by
    have hb : 0 < (1 - ρ ^ 2)⁻¹ := inv_pos.mpr hdenpos
    have h := integral_gaussian ((1 - ρ ^ 2)⁻¹)
    have harg : (fun u : ℝ => Real.exp (-((1 - ρ ^ 2)⁻¹) * u ^ 2)) =
        fun u : ℝ => Real.exp (-(u ^ 2) / (1 - ρ ^ 2)) := by
      funext u
      congr 1
      field_simp [ne_of_gt hdenpos]
    rw [harg] at h
    rw [h]
    congr 1
    field_simp [ne_of_gt hdenpos]
  dsimp [mehlerKernel]
  rw [MeasureTheory.integral_const_mul]
  rw [htrans, hgauss]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (mul_pos Real.pi_pos hdenpos)))

/-- **The density realizes the pCN operator.**  The normalized Gaussian average
    `mehlerOp ρ f x` equals `∫ z, f z * mehlerKernel ρ x z dz`; the identity is translation
    and scaling of the Lebesgue integral, with the prefactors cancelling because
    `√(π(1−ρ²)) = √π · √(1−ρ²)`. -/
theorem mehlerOp_eq_integral_mehlerKernel {ρ : ℝ} (hρ : ρ ^ 2 < 1) (f : ℝ → ℝ) (x : ℝ) :
    mehlerOp ρ f x = ∫ z : ℝ, f z * mehlerKernel ρ x z := by
  have hdenpos : 0 < 1 - ρ ^ 2 := by linarith
  let a : ℝ := Real.sqrt (1 - ρ ^ 2)
  have ha : 0 < a := Real.sqrt_pos.2 hdenpos
  have ha_sq : a ^ 2 = 1 - ρ ^ 2 := by
    dsimp [a]
    exact Real.sq_sqrt (le_of_lt hdenpos)
  have hsqrt_mul : Real.sqrt (Real.pi * (1 - ρ ^ 2)) = Real.sqrt Real.pi * a := by
    rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  have htrans :
      (∫ z : ℝ, f z * Real.exp (-(z - ρ * x) ^ 2 / (1 - ρ ^ 2))) =
        ∫ u : ℝ, f (u + ρ * x) * Real.exp (-(u ^ 2) / (1 - ρ ^ 2)) := by
    let h : ℝ → ℝ := fun z => f z * Real.exp (-(z - ρ * x) ^ 2 / (1 - ρ ^ 2))
    have ht := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume) h (ρ * x)
    change (∫ u : ℝ, h (u + ρ * x)) = ∫ z : ℝ, h z at ht
    rw [← ht]
    congr 1
    funext u
    dsimp [h]
    congr 2
    ring
  have hsquare (u : ℝ) : (a * u) ^ 2 / (1 - ρ ^ 2) = u ^ 2 := by
    rw [← ha_sq]
    field_simp [ne_of_gt ha]
  have hscale :
      (∫ y : ℝ, f (a * y + ρ * x) * Real.exp (-(y ^ 2))) =
        a⁻¹ * ∫ u : ℝ, f (u + ρ * x) * Real.exp (-(u ^ 2) / (1 - ρ ^ 2)) := by
    let g : ℝ → ℝ := fun u => f (u + ρ * x) * Real.exp (-(u ^ 2) / (1 - ρ ^ 2))
    have hs := MeasureTheory.Measure.integral_comp_mul_left g a
    change (∫ u : ℝ, g (a * u)) = |a⁻¹| * ∫ z : ℝ, g z at hs
    calc
      (∫ y : ℝ, f (a * y + ρ * x) * Real.exp (-(y ^ 2))) = ∫ u : ℝ, g (a * u) := by
        congr 1
        funext u
        dsimp [g]
        rw [← hsquare u]
        ring_nf
      _ = |a⁻¹| * ∫ z : ℝ, g z := hs
      _ = a⁻¹ * ∫ u : ℝ, f (u + ρ * x) * Real.exp (-(u ^ 2) / (1 - ρ ^ 2)) := by
        rw [abs_of_pos (inv_pos.mpr ha)]
  have hpref : a * (Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ = (Real.sqrt Real.pi)⁻¹ := by
    rw [hsqrt_mul]
    field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos), ne_of_gt ha]
  have hR :
      (∫ z : ℝ, f z * mehlerKernel ρ x z) =
        (Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ *
          ∫ z : ℝ, f z * Real.exp (-(z - ρ * x) ^ 2 / (1 - ρ ^ 2)) := by
    dsimp [mehlerKernel]
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext z
    ring
  have hscale' :
      (∫ y : ℝ, f (ρ * x + a * y) * Real.exp (-(y ^ 2))) =
        a⁻¹ * ∫ u : ℝ, f (u + ρ * x) * Real.exp (-(u ^ 2) / (1 - ρ ^ 2)) := by
    simpa [add_comm] using hscale
  dsimp [mehlerOp, mehlerArg]
  change (Real.sqrt Real.pi)⁻¹ *
      (∫ y : ℝ, f (ρ * x + a * y) * Real.exp (-(y ^ 2))) =
    ∫ z : ℝ, f z * mehlerKernel ρ x z
  rw [hR, hscale', htrans]
  rw [← hpref]
  field_simp [ne_of_gt ha]

/-- Detailed balance of the Mehler kernel in its stationary Gaussian convention: with
    `γ(dx) = exp(−x²) dx` (up to normalization), `γ(dx)·k(x,y) = γ(dy)·k(y,x)` pointwise.
    The prefactor of the kernel cancels and the exponent reduces to the symmetric form
    `−(x² + y² − 2ρxy)/(1 − ρ²)`.  This is the H1 input `cftproof.md` asks for — detailed balance
    in the stationary Gaussian `γ`-convention — before any finite-mode product or domain claim. -/
theorem mehlerKernel_detailedBalance (ρ x y : ℝ) (hρ : ρ ^ 2 < 1) :
    Real.exp (-(x ^ 2)) * mehlerKernel ρ x y =
      Real.exp (-(y ^ 2)) * mehlerKernel ρ y x := by
  have hden : 1 - ρ ^ 2 ≠ 0 := by linarith
  have hexp : Real.exp (-(x ^ 2)) * Real.exp (-((y - ρ * x) ^ 2) / (1 - ρ ^ 2)) =
      Real.exp (-(y ^ 2)) * Real.exp (-((x - ρ * y) ^ 2) / (1 - ρ ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp [hden]
    ring
  dsimp [mehlerKernel]
  calc
    Real.exp (-(x ^ 2)) *
        ((Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ *
          Real.exp (-((y - ρ * x) ^ 2) / (1 - ρ ^ 2))) =
        (Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ *
          (Real.exp (-(x ^ 2)) * Real.exp (-((y - ρ * x) ^ 2) / (1 - ρ ^ 2))) := by ring
    _ = (Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ *
          (Real.exp (-(y ^ 2)) * Real.exp (-((x - ρ * y) ^ 2) / (1 - ρ ^ 2))) := by
            rw [hexp]
    _ = Real.exp (-(y ^ 2)) *
        ((Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹ *
          Real.exp (-((x - ρ * y) ^ 2) / (1 - ρ ^ 2))) := by ring

/-- The Gaussian density is stationary for the Mehler kernel: integrating its product with
    `k(x,y)` over the *starting* point gives the density at `y`.  This follows from detailed
    balance and normalization of the kernel in its second argument, not from a separate
    Gaussian integral. -/
theorem mehlerKernel_stationary (ρ y : ℝ) (hρ : ρ ^ 2 < 1) :
    (∫ x : ℝ, Real.exp (-(x ^ 2)) * mehlerKernel ρ x y) = Real.exp (-(y ^ 2)) := by
  have hpoint : ∀ x : ℝ, Real.exp (-(x ^ 2)) * mehlerKernel ρ x y =
      Real.exp (-(y ^ 2)) * mehlerKernel ρ y x := fun x => mehlerKernel_detailedBalance ρ x y hρ
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul]
  rw [mehlerKernel_integral hρ y]
  ring

end BookProof.MehlerTransitionDensity
