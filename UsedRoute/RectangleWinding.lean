import Mathlib

/-!
# Edge integrals of `(z - w)⁻¹` and the winding number of a rectangle

This file collects the elementary, `Rect`-independent computations behind the
Cauchy integral formula for rectangles used in `UsedRoute/RectangleStrategy.lean`.

The four edges of a rectangle contribute integrals of the two shapes

* horizontal: `∫ x in a..b, (x + c·i)⁻¹` with `c ≠ 0`,
* vertical:   `i · ∫ y in a..b, (d + y·i)⁻¹` with `d ≠ 0`,

and both are computed here in closed form by exhibiting an explicit primitive,
`½·log (t² + c²) ∓ i·arctan (t/c)`.  Adding the four contributions, the logarithmic
parts cancel and the arctangents add up to the total turning `2π`
(`arctan_rectangle_winding`), which is the analytic content of the winding number
of a rectangle around an interior point.
-/

open Complex

namespace RectangleWinding

/-- Primitive of `x ↦ (x + c·i)⁻¹` along a horizontal line: `½·log (x² + c²) - i·arctan (x/c)`. -/
lemma hasDerivAt_horizontalPrimitive (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (1 / 2 : ℂ) * (Real.log (x ^ 2 + c ^ 2) : ℂ)
        - I * (Real.arctan (x / c) : ℂ)) (((t : ℂ) + c * I)⁻¹) t := by
  have hpos : (0 : ℝ) < t ^ 2 + c ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + c ^ 2))
      ((2 * t) / (t ^ 2 + c ^ 2)) t := by
    have := ((hasDerivAt_pow 2 t).add_const (c ^ 2)).log (ne_of_gt hpos)
    simpa [mul_comm] using this
  have h2 : HasDerivAt (fun x : ℝ => Real.arctan (x / c))
      ((1 / c) / (1 + (t / c) ^ 2)) t := by
    have := (Real.hasDerivAt_arctan (t / c)).comp t ((hasDerivAt_id t).div_const c)
    simpa [div_eq_mul_inv, mul_comm] using this
  have H := ((h1.ofReal_comp).const_mul (1 / 2 : ℂ)).sub ((h2.ofReal_comp).const_mul I)
  convert H using 1
  have hne : ((t : ℂ) + c * I) ≠ 0 := fun h => hc (by simpa using congrArg Complex.im h)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hp : ((t : ℂ) ^ 2 + (c : ℂ) ^ 2) ≠ 0 := by
    have h : ((t ^ 2 + c ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
    push_cast at h
    exact h
  have harc : (1 / c / (1 + (t / c) ^ 2) : ℝ) = c / (t ^ 2 + c ^ 2) := by
    field_simp
    ring
  rw [inv_eq_one_div, harc]
  push_cast
  rw [div_eq_iff hne]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Primitive of `y ↦ i·(d + y·i)⁻¹` along a vertical line:
`½·log (y² + d²) + i·arctan (y/d)`. -/
lemma hasDerivAt_verticalPrimitive (d : ℝ) (hd : d ≠ 0) (t : ℝ) :
    HasDerivAt (fun y : ℝ => (1 / 2 : ℂ) * (Real.log (y ^ 2 + d ^ 2) : ℂ)
        + I * (Real.arctan (y / d) : ℂ)) (I * (((d : ℂ) + t * I)⁻¹)) t := by
  have hpos : (0 : ℝ) < t ^ 2 + d ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + d ^ 2))
      ((2 * t) / (t ^ 2 + d ^ 2)) t := by
    have := ((hasDerivAt_pow 2 t).add_const (d ^ 2)).log (ne_of_gt hpos)
    simpa [mul_comm] using this
  have h2 : HasDerivAt (fun y : ℝ => Real.arctan (y / d))
      ((1 / d) / (1 + (t / d) ^ 2)) t := by
    have := (Real.hasDerivAt_arctan (t / d)).comp t ((hasDerivAt_id t).div_const d)
    simpa [div_eq_mul_inv, mul_comm] using this
  have H := ((h1.ofReal_comp).const_mul (1 / 2 : ℂ)).add ((h2.ofReal_comp).const_mul I)
  convert H using 1
  have hne : ((d : ℂ) + t * I) ≠ 0 := fun h => hd (by simpa using congrArg Complex.re h)
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hp : ((t : ℂ) ^ 2 + (d : ℂ) ^ 2) ≠ 0 := by
    have h : ((t ^ 2 + d ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
    push_cast at h
    exact h
  have harc : (1 / d / (1 + (t / d) ^ 2) : ℝ) = d / (t ^ 2 + d ^ 2) := by
    field_simp
    ring
  rw [harc, inv_eq_one_div]
  push_cast
  rw [mul_one_div, div_eq_iff hne]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Closed form of a horizontal edge integral of `(z)⁻¹` at height `c ≠ 0`. -/
lemma integral_horizontalEdge (a b c : ℝ) (hc : c ≠ 0) :
    (∫ x in a..b, ((x : ℂ) + c * I)⁻¹)
      = ((1 / 2 : ℂ) * (Real.log (b ^ 2 + c ^ 2) : ℂ) - I * (Real.arctan (b / c) : ℂ))
        - ((1 / 2 : ℂ) * (Real.log (a ^ 2 + c ^ 2) : ℂ) - I * (Real.arctan (a / c) : ℂ)) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_horizontalPrimitive c hc x) ?_
  apply Continuous.intervalIntegrable
  refine Continuous.inv₀ (by fun_prop) (fun x h => ?_)
  exact absurd (by simpa using congrArg Complex.im h) hc

/-- Closed form of a vertical edge integral of `(z)⁻¹` at abscissa `d ≠ 0`
(with the `i` factor of the boundary integral included). -/
lemma integral_verticalEdge (a b d : ℝ) (hd : d ≠ 0) :
    I • (∫ y in a..b, ((d : ℂ) + y * I)⁻¹)
      = ((1 / 2 : ℂ) * (Real.log (b ^ 2 + d ^ 2) : ℂ) + I * (Real.arctan (b / d) : ℂ))
        - ((1 / 2 : ℂ) * (Real.log (a ^ 2 + d ^ 2) : ℂ) + I * (Real.arctan (a / d) : ℂ)) := by
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_verticalPrimitive d hd y) ?_
  apply Continuous.intervalIntegrable
  refine Continuous.mul continuous_const (Continuous.inv₀ (by fun_prop) (fun y h => ?_))
  exact absurd (by simpa using congrArg Complex.re h) hd

/-- The total turning of `(z - w)⁻¹` around a rectangle whose corners are at
`A < 0 < B` (horizontally) and `C < 0 < D` (vertically) relative to `w` is `2π`. -/
lemma arctan_rectangle_winding (A B C D : ℝ) (hA : A < 0) (hB : 0 < B) (hC : C < 0)
    (hD : 0 < D) :
    -(Real.arctan (B / C) - Real.arctan (A / C)) + (Real.arctan (B / D) - Real.arctan (A / D))
      + (Real.arctan (D / B) - Real.arctan (C / B))
      - (Real.arctan (D / A) - Real.arctan (C / A)) = 2 * Real.pi := by
  have p1 : Real.arctan (D / B) = Real.pi / 2 - Real.arctan (B / D) := by
    rw [show D / B = (B / D)⁻¹ by rw [inv_div]]
    exact Real.arctan_inv_of_pos (by positivity)
  have p2 : Real.arctan (C / A) = Real.pi / 2 - Real.arctan (A / C) := by
    rw [show C / A = (A / C)⁻¹ by rw [inv_div]]
    exact Real.arctan_inv_of_pos (div_pos_of_neg_of_neg hA hC)
  have p3 : Real.arctan (C / B) = -(Real.pi / 2) - Real.arctan (B / C) := by
    rw [show C / B = (B / C)⁻¹ by rw [inv_div]]
    exact Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hB hC)
  have p4 : Real.arctan (D / A) = -(Real.pi / 2) - Real.arctan (A / D) := by
    rw [show D / A = (A / D)⁻¹ by rw [inv_div]]
    exact Real.arctan_inv_of_neg (div_neg_of_neg_of_pos hA hD)
  rw [p1, p2, p3, p4]
  ring

/-- Recentring a horizontal edge integral of `(z - w)⁻¹` at the point `w`. -/
lemma integral_horizontalEdge_shift (a b c : ℝ) (w : ℂ) :
    (∫ x in a..b, ((x : ℂ) + (c : ℂ) * I - w)⁻¹)
      = ∫ x in (a - w.re)..(b - w.re), ((x : ℂ) + ((c - w.im : ℝ) : ℂ) * I)⁻¹ := by
  rw [← intervalIntegral.integral_comp_sub_right
    (fun u : ℝ => ((u : ℂ) + ((c - w.im : ℝ) : ℂ) * I)⁻¹) w.re]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  congr 1
  apply Complex.ext <;> simp

/-- Recentring a vertical edge integral of `(z - w)⁻¹` at the point `w`. -/
lemma integral_verticalEdge_shift (a b d : ℝ) (w : ℂ) :
    (∫ y in a..b, ((d : ℂ) + (y : ℂ) * I - w)⁻¹)
      = ∫ y in (a - w.im)..(b - w.im), (((d - w.re : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ := by
  rw [← intervalIntegral.integral_comp_sub_right
    (fun u : ℝ => (((d - w.re : ℝ) : ℂ) + (u : ℂ) * I)⁻¹) w.im]
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  congr 1
  apply Complex.ext <;> simp

end RectangleWinding
