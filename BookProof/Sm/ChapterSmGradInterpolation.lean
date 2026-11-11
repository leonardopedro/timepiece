import Mathlib
import BookProof.Sm.ChapterSmGaussWeightedIbp

/-!
# The gradient interpolation from the weighted IBP identity, and where it stops

Work order: `SM_ESA_COMPLETION_PLAN.md` §26.

## 1. What §23 left, and what interpolation needs

§23 proved the sign identity of the cross term, `Re ⟪W u, −Δ_S u⟫ = ‖√W ∇u‖² + Re ⟪u ∇W, ∇u⟫`,
and said that closing §22's `PotSelfBound` still needs an **interpolation of `∇`** between `L²` and
the graph norm of `−Δ_S + W + 1`.  This section proves the interpolation that the identity actually
yields:

```text
∑_{j ∈ S} ‖∇_j p‖²  ≤  2 Re ⟪W p, −Δ_S p⟫  +  ∑_{j ∈ S} ‖(∂_j W) p‖²,
```

valid whenever `W ≥ 1` pointwise.  It is the exact quantitative content of the sign identity: the
weighted Dirichlet energy dominates the unweighted one (`‖∇p‖ ≤ ‖√W ∇p‖`, one factor per
coordinate), and the commutator term `Re ⟪p ∇W, ∇p⟫` is then absorbed by `2ab ≤ a² + b²` coordinate
by coordinate.

* `norm_coreD_sq_le_weighted` — one coordinate of the domination `‖∇_j p‖² ≤ ‖√W ∇_j p‖²`, from
  `W ≥ 1` and the pointwise form `eval_weighted_self_re` of §23.
* `abs_cross_le_op` — the commutator term is a Hilbert–Schmidt pairing, bounded by
  `‖(∂_j W) p‖ ‖∇_j p‖` (Cauchy–Schwarz in `L²`).
* `mul_le_half_add_sq` — the elementary `2ab ≤ a² + b²`.
* `dirichlet_le_weighted_form` — the interpolation itself, and `sm_dirichlet_le_weighted_form` at
the SM comparison, where `W ≥ 1` is `one_le_polyW_smPotPoly` for `c₀ ≥ 1`.

## 2. Why this is not `PotSelfBound`

The interpolation bounds `∇` **by** the quadratic form, which is the wrong direction for the
self-bound: `PotSelfBound` asks for `‖W p + p‖ ≤ β ‖(−Δ_S + W + 1) p‖`, i.e. for the *potentially*
degree-four term to be dominated by the form.  Two things are missing.

1. **The term `∑_j ‖(∂_j W) p‖²` is not absorbable.**  `W` has degree four, so `∂_j W` has degree
   three and `|∇W|²` has degree six, while `W` has degree four.  There is therefore **no constant**
   `C` with `|∇W(x)|² ≤ C W(x)` as `x → ∞`, which is the hypothesis every absorption of the
   commutator term needs.  The size of the gradient term is genuinely cubic in `x`, so the
   interpolation cannot be turned into a statement about `W` alone.
2. **`W` versus `Δ` is the open problem itself.**  Writing `(−Δ_S + W + 1) p = (W + 1) p − Δ_S p`,
   the self-bound is equivalent to the pure kinetic estimate `‖Δ_S p‖ ≤ c ‖(−Δ_S + W + 1) p‖`
   (proved below as `potSelfBound_of_kinetic_bound`, the converse of §22's reduction).  That is
   §19's `hpoly`, so §22's claim that the two hypotheses are "two equivalent spellings of one open
   problem" is now a theorem and not a remark, but it also means the interpolation cannot settle it:
   an estimate of `‖W p‖` by the graph norm is precisely what §19 states as open.

The honest summary is that §23 supplies the sign and this section supplies the size that the sign
affords, and the remaining step — a reverse elliptic estimate giving `‖W p‖ ≲ ‖(−Δ_S + W + 1) p‖` —
is untouched.  `PotSelfBound` therefore stays a hypothesis downstream, and nothing in this section
assumes it away.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmGradInterpolation

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds
open BookProof.SmComparisonEsa BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.SmFarisLavine
open BookProof.SmKineticElliptic BookProof.SmKineticGarding BookProof.SmGaussWeightedIbp
open BookProof.QuadratureEsa

noncomputable section

variable {d : ℕ}

/-! ## 1. The weighted Dirichlet energy dominates the unweighted one -/

/-- **One coordinate of `‖∇_j p‖ ≤ ‖√W ∇_j p‖`**: for a weight that is pointwise at least `1`, the
weighted self-pairing dominates the unweighted squared norm. -/
theorem norm_coreD_sq_le_weighted (j : Fin d) (W p : MvPolynomial (Fin d) ℂ)
    (hW : cpoly W = W) (hW1 : ∀ x : Vd d, 1 ≤ polyW W x) :
    ‖pgLp (coreD j p)‖ ^ 2
      ≤ (gaussInt (cpoly (W * coreD j p) * coreD j p)).re := by
  rw [norm_pgLp_sq]
  refine gaussInt_re_mono fun x => ?_
  rw [eval_cpoly_self_eq, eval_weighted_self_re W (coreD j p) hW x]
  have h1 : 1 ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) W).re := hW1 x
  have h2 : (0 : ℝ) ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (coreD j p)‖ ^ 2 :=
    sq_nonneg _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 h2

/-! ## 2. The commutator term is a Cauchy–Schwarz pairing -/

/-- **The commutator term is bounded by the two `L²` norms**: `|Re ⟪(∂_j W)p, ∇_j p⟫|` is at most
`‖(∂_j W) p‖ ‖∇_j p‖`, because it is the real part of an inner product in the Gaussian picture. -/
theorem abs_cross_le_op (j : Fin d) (W p : MvPolynomial (Fin d) ℂ) :
    |(gaussInt (cpoly (pderiv j W * p) * coreD j p)).re|
      ≤ ‖pgLp (pderiv j W * p)‖ * ‖pgLp (coreD j p)‖ := by
  have hinner : gaussInt (cpoly (pderiv j W * p) * coreD j p)
      = (inner ℂ (pgLp (pderiv j W * p)) (pgLp (coreD j p)) : ℂ) :=
    (QgHermiteFriedrichs.inner_pgLp_pgLp _ _).symm
  rw [hinner]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

/-- **`2 a b ≤ a² + b²`**, the form in which the commutator term is absorbed. -/
theorem mul_le_half_add_sq (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-! ## 3. The interpolation -/

/-- **The gradient interpolation**: the unweighted Dirichlet energy is bounded by the quadratic form
of the weight plus the size of the potential's gradient, with the constant `2` of the sign identity.
This is the quantitative form of §23's `Re ⟪W u, −Δ_S u⟫ = ‖√W ∇u‖² + Re ⟪u ∇W, ∇u⟫`. -/
theorem dirichlet_le_weighted_form (S : Finset (Fin d)) (W p : MvPolynomial (Fin d) ℂ)
    (hW : cpoly W = W) (hW1 : ∀ x : Vd d, 1 ≤ polyW W x) :
    ∑ j ∈ S, ‖pgLp (coreD j p)‖ ^ 2
      ≤ 2 * (inner ℂ (pgLp (W * p)) (pgLp (kinPolyS S p))).re
        + ∑ j ∈ S, ‖pgLp (pderiv j W * p)‖ ^ 2 := by
  set G : ℝ := ∑ j ∈ S, ‖pgLp (coreD j p)‖ ^ 2 with hG
  set C : ℝ := ∑ j ∈ S, ‖pgLp (pderiv j W * p)‖ ^ 2 with hC
  set B : ℝ := ∑ j ∈ S, (gaussInt (cpoly (W * coreD j p) * coreD j p)).re with hB
  set A : ℝ := ∑ j ∈ S, (gaussInt (cpoly (pderiv j W * p) * coreD j p)).re with hA
  have hE : (inner ℂ (pgLp (W * p)) (pgLp (kinPolyS S p))).re = A + B := by
    rw [inner_weighted_kinPolyS, Finset.sum_add_distrib, ← hA, ← hB]
  have hGB : G ≤ B := by
    rw [hG, hB]
    exact Finset.sum_le_sum fun j _ => norm_coreD_sq_le_weighted j W p hW hW1
  have hAabs : -A ≤ ∑ j ∈ S, |(gaussInt (cpoly (pderiv j W * p) * coreD j p)).re| := by
    rw [hA]
    exact (neg_le_abs _).trans (Finset.abs_sum_le_sum_abs _ _)
  have hAG : ∑ j ∈ S, |(gaussInt (cpoly (pderiv j W * p) * coreD j p)).re| ≤ (C + G) / 2 := by
    rw [hC, hG, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    exact (abs_cross_le_op j W p).trans (mul_le_half_add_sq _ _)
  have hmain : G ≤ 2 * (inner ℂ (pgLp (W * p)) (pgLp (kinPolyS S p))).re + C := by
    rw [hE]
    linarith
  simpa only [hG, hC] using hmain

/-! ## 4. The SM comparison -/

/-- **The interpolation at the SM comparison**: the quartic potential is at least `1` once `c₀ ≥ 1`,
so the Dirichlet energy over `smS` is bounded by the potential's quadratic form plus the cubic
gradient term. -/
theorem sm_dirichlet_le_weighted_form (P : SmParams) {c0 : ℝ} (hc0 : 1 ≤ c0)
    (p : MvPolynomial (Fin 163) ℂ) :
    ∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2
      ≤ 2 * (inner ℂ (pgLp (smPotPoly P c0 * p)) (pgLp (kinPolyS smS p))).re
        + ∑ j ∈ smS, ‖pgLp (pderiv j (smPotPoly P c0) * p)‖ ^ 2 :=
  dirichlet_le_weighted_form smS (smPotPoly P c0) p (realCoeff_smPotPoly P c0)
    (one_le_polyW_smPotPoly P hc0)

/-! ## 5. `PotSelfBound` is §19's `hpoly`: the converse of §22's reduction -/

/-- **The self-bound from the pure kinetic estimate**: if `‖Δ_S p‖ ≤ c ‖(−Δ_S + W + 1)p‖` — §19's
`hpoly` — then the potential satisfies `PotSelfBound` with `β = 1 + c`.  Together with §22's
`kineticSum_norm_le_of_pot_self_bound` this makes precise the claim that the two are equivalent
spellings of the same open problem, rather than two separate hypotheses. -/
theorem potSelfBound_of_kinetic_bound (P : SmParams) (c0 : ℝ) {c : ℝ}
    (hc : ∀ p : MvPolynomial (Fin 163) ℂ,
      ‖pgLp (kinPolyS smS p)‖
        ≤ c * ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖) :
    PotSelfBound P c0 (1 + c) := by
  intro p
  set S : L2d 163 := pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p
  set T : L2d 163 := pgLp (smPotPoly P c0 * p) + pgLp p
  have hS : S = pgLp (kinPolyS smS p) + T := by
    change pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p
      = pgLp (kinPolyS smS p) + (pgLp (smPotPoly P c0 * p) + pgLp p)
    rw [pgLp_add']
    abel
  have hdiff : T = S - pgLp (kinPolyS smS p) := by
    rw [hS]
    abel
  have h1 : ‖T‖ ≤ ‖S‖ + ‖pgLp (kinPolyS smS p)‖ := by
    rw [hdiff]
    exact norm_sub_le _ _
  have h2 : ‖pgLp (kinPolyS smS p)‖ ≤ c * ‖S‖ := hc p
  calc ‖pgLp (smPotPoly P c0 * p) + pgLp p‖ = ‖T‖ := rfl
    _ ≤ ‖S‖ + ‖pgLp (kinPolyS smS p)‖ := h1
    _ ≤ ‖S‖ + c * ‖S‖ := by linarith [h2]
    _ = (1 + c) * ‖S‖ := by ring
    _ = (1 + c) * ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖ := rfl

end

end BookProof.SmGradInterpolation
