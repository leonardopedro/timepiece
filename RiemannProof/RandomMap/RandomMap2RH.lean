import RiemannProof.SolovayHilbert

/-!
# Honest RandomMap2 reduction of the RH zero-free step

This module addresses roadmap item R7 without treating the historical
`riemann_hypothesis_rect` declaration as an established analytic input: that
declaration depends transitively on unresolved RH-strength placeholders.

Instead, the module isolates its exact analytic content as `RectangleRH`, proves
that it is equivalent to zero-freeness of zeta on the right half-plane, and
packages that conditional implication with RandomMap2's independently proved
finite-head dimensional reduction.  Thus the remaining obstacle is explicit:
the decoupled architecture reduces outer observables to finite-head integrals,
but it does not by itself prove the RH-equivalent analytic premise.
-/

open MeasureTheory ProbabilityTheory Complex
open SchoenfeldPRA

noncomputable section

namespace RandomMap2RH

/-- The analytic conclusion supplied by the two-rectangle route.  It is kept as
an explicit proposition rather than silently importing the historical theorem
whose proof still has RH-strength placeholders. -/
def RectangleRH : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- Zeta is zero-free strictly to the right of the critical line. -/
def ZeroFreeRightHalfPlane : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0

/-
The rectangle conclusion implies zero-freeness to the right of the critical
line, including the classical zero-free region `Re(s) ≥ 1`.
-/
theorem zeta_no_zeros_right_half_plane_of_rectangle
    (hrect : RectangleRH) : ZeroFreeRightHalfPlane := by
  intro s hs hζ
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 hζ
  · have hre_lt : s.re < 1 := lt_of_not_ge h1
    have hre_pos : 0 < s.re := lt_trans (by norm_num) hs
    have hre_eq := hrect s hζ hre_pos hre_lt
    linarith

/-
Conversely, right-half-plane zero-freeness implies the rectangle form of
RH, using the functional equation to reflect a hypothetical zero left of the
critical line.  Consequently, the missing R7 analytic premise is exactly
RH-strength; RandomMap2 decoupling alone cannot discharge it.
-/
theorem rectangleRH_of_zeta_no_zeros_right_half_plane
    (hzero : ZeroFreeRightHalfPlane) : RectangleRH := by
  intro s hs h_pos h_lt
  rcases lt_trichotomy s.re (1 / 2) with hre | hre | hre
  · have hsymm : riemannZeta (1 - s) = 0 := zeta_symm s h_pos h_lt hs
    have hreflect : 1 / 2 < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    exact False.elim (hzero (1 - s) hreflect hsymm)
  · exact hre
  · exact False.elim (hzero s hre hs)

/-
The exact equivalence between the proposed R7 zero-free result and the
rectangle formulation of RH.
-/
theorem rectangleRH_iff_zeroFreeRightHalfPlane :
    RectangleRH ↔ ZeroFreeRightHalfPlane := by
  exact ⟨zeta_no_zeros_right_half_plane_of_rectangle,
    rectangleRH_of_zeta_no_zeros_right_half_plane⟩

/-
Honest RandomMap2 bridge: under the explicit rectangle/RH analytic premise,
any two cylindrical outer wave-functions reduce to a finite-head integral and
zeta is zero-free to the right of the critical line.  The two conjuncts make
clear what comes from decoupling and what comes from the analytic premise.
-/
theorem decoupled_integral_and_zeroFree_of_rectangle {N : ℕ}
    {headDist : Measure (InnerHead N)} [IsProbabilityMeasure headDist]
    (hrect : RectangleRH)
    (Ψ₁ Ψ₂ : OuterWaveFunction N headDist)
    (hcyl₁ : dependsOnlyOnHead (Ψ₁ : InnerSpace N → ℂ))
    (hcyl₂ : dependsOnlyOnHead (Ψ₂ : InnerSpace N → ℂ)) :
    (∃ (g₁ g₂ : Lp ℂ 2 headDist),
      inner ℂ Ψ₁ Ψ₂ = ∫ x, g₁ x * star (g₂ x) ∂headDist) ∧
    ZeroFreeRightHalfPlane := by
  exact ⟨outer_inner_reduces_to_head Ψ₁ Ψ₂ hcyl₁ hcyl₂,
    zeta_no_zeros_right_half_plane_of_rectangle hrect⟩

end RandomMap2RH
