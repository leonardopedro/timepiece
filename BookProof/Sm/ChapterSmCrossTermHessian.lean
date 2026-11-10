import Mathlib
import BookProof.Sm.ChapterSmQuarticUncertainty

/-!
# The cross term is a Hessian weight: the upper bound §23 and §26 did not have

Work order: `SM_ESA_COMPLETION_PLAN.md` §38.

## 1. What was missing

§31 proved that `PotSelfBound P c₀ 1` **is** the non-negativity of the residual

```text
R = ‖Δ_S p‖² + 2 Re ⟪−Δ_S p, W p + p⟫,
```

and §35 recorded that the sign route is one-sided: §23's identity
`Re ⟪W p, −Δ_S p⟫ = ‖√W ∇p‖² + Re ⟪p ∇W, ∇p⟫` bounds the cross term *below*
(the weighted Dirichlet energy is non-negative), whereas closing `R ≥ 0` needs a
commitment on the *commutator* term `Re ⟪p ∇W, ∇p⟫`, and §26's interpolation then
produces `GradResidual`, a comparison of a degree-six density with a second-order
norm.  §35 named the missing ingredient as an *upper* bound on `Re ⟪W p, −Δ_S p⟫`
and stated that no module of the corpus has one.

This section proves it.  The commutator term is not a gradient term at all: two
integration by parts turn it into a **Hessian weight**,

```text
2 Re ⟪Q p, −Δ_S p⟫  =  2 ∑_{j ∈ S} ∫ Q |∇_j p|²  −  ∑_{j ∈ S} ∫ (∂_j² Q) |p|²,
```

with no derivative left on `Q`.  The proof is the observation that the twisted
derivative satisfies the twisted Leibniz rule (`coreD_mul`) and is antisymmetric
(`gaussInt_coreD`), so the `∇Q · ∇p` term integrates by parts once more and the
twist cancels exactly (`commutator_cross_eq` below, per coordinate).

## 2. Why this is the right statement

The identity is **exact**, so it is simultaneously the upper and the lower bound
of the cross term: the sign identity of §23 is its inequality half
(the weighted Dirichlet energy is non-negative) and §35's missing upper bound is
obtained by dropping the weight `Q` to its infimum — for a non-negative weight
with non-negative Hessian trace the cross term is **dominated by the weighted
Dirichlet energy** (`crossTerm_upper`).

The residual of §31 then becomes, with no inequality anywhere,

```text
R = ‖Δ_S p‖² + 2 ∑_{j ∈ S} ∫ (W + 1) |∇_j p|² − ∑_{j ∈ S} ∫ (∂_j² W) |p|²,
```

so `PotSelfBound P c₀ 1` is *equivalent* to the single quadratic-form inequality
`hessForm ≤ kinetic + 2 · weightedDirichlet` (`potSelfBound_one_iff_hessForm`).
The degree-six density of §31's `GradResidual` is gone: the remaining gap compares
two **quadratic** forms, the Hessian-weighted `L²` of `p` with the graph form.
That is a genuine improvement in kind, and it is also the reason the gap survives:
it is the form-domain inclusion of §32 in a different spelling
(`hessForm_le_graph` shows the implication form-domain comparison ⟹ Hessian gap),
and it is *not* proved here.

Everything in this section is `sorry`-free and `axiom`-free.  `PotSelfBound`,
`FormDomainComparison` and the Hessian gap all remain hypotheses.
-/

namespace BookProof.SmCrossTermHessian

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds
open BookProof.SmComparisonEsa BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.SmKineticElliptic BookProof.SmKineticGarding
open BookProof.SmGaussWeightedIbp BookProof.SmGradInterpolation
open BookProof.SmReverseEllipticResidual BookProof.SmQuarticUncertainty
open BookProof.SmFormDomainComparison

noncomputable section

variable {d : ℕ}

/-! ## 1. Conjugation and the Gaussian integral -/

/-- The conjugate polynomial is a square root of unity. -/
theorem cpoly_cpoly (p : MvPolynomial (Fin d) ℂ) : cpoly (cpoly p) = p := by
  simp only [cpoly, MvPolynomial.map_map]
  rw [show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from
    RingHom.ext fun z => Complex.conj_conj z]
  exact MvPolynomial.map_id p

/-- **Conjugation commutes with the Gaussian integral** (the weight is real). -/
theorem gaussInt_cpoly (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly r) = (starRingEnd ℂ) (gaussInt r) := by
  rw [gaussInt, gaussInt, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal, conj_polyEval]

/-- Twice the real part of a Gaussian integral, as the integral of the symmetrized
polynomial. -/
theorem two_re_gaussInt (f : MvPolynomial (Fin d) ℂ) :
    2 * (gaussInt f).re = (gaussInt (f + cpoly f)).re := by
  rw [gaussInt_add, gaussInt_cpoly, Complex.add_conj]
  simp

/-! ## 2. The twisted Leibniz rule in the form the identity needs -/

/-- The twisted derivative splits a product into the ordinary derivative of the product
minus the twist: `coreD a · b + a · coreD b = ∂(ab) − x·ab`.  This is the algebraic core of
the commutator identity below. -/
theorem coreD_mul_add (j : Fin d) (a b : MvPolynomial (Fin d) ℂ) :
    coreD j a * b + a * coreD j b = pderiv j (a * b) - X j * (a * b) := by
  have hC2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = 1 := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  simp only [coreD, pderiv_mul, sub_mul, mul_sub]
  linear_combination (-(X j * a * b)) * hC2

/-! ## 3. The commutator cross term is a Hessian weight -/

/-- **The per-coordinate cross-term identity**: for a weight `Q` with real coefficients the
commutator half of `⟪Q p, −Δ p⟫` is the Hessian weight of `Q` against `|p|²`, with no
derivative left on `Q`.  Two integration by parts: the first turns `∂_j Q · ∂_j p` into
`−∂_j²Q · p`, and the twist `−x_j/2` cancels exactly between the two halves. -/
theorem commutator_cross_eq (j : Fin d) (Q p : MvPolynomial (Fin d) ℂ)
    (hQ : cpoly Q = Q) :
    2 * (gaussInt (cpoly (pderiv j Q * p) * coreD j p)).re
      = - (gaussInt (cpoly (pderiv j (pderiv j Q) * p) * p)).re := by
  set Q' := pderiv j Q with hQ'def
  have hQ' : cpoly Q' = Q' := by
    rw [hQ'def, cpoly_pderiv, hQ]
  have hQ'' : cpoly (pderiv j Q') = pderiv j Q' := by
    rw [hQ'def, cpoly_pderiv, hQ']
  set s := cpoly p * p with hsdef
  -- the symmetrized left-hand polynomial
  have hsym : cpoly (Q' * p) * coreD j p + cpoly (cpoly (Q' * p) * coreD j p)
      = Q' * (cpoly p * coreD j p + p * coreD j (cpoly p)) := by
    simp only [cpoly_mul, cpoly_coreD, cpoly_cpoly, hQ']
    ring
  have hsplit : cpoly p * coreD j p + p * coreD j (cpoly p)
      = pderiv j s - X j * s := by
    rw [hsdef]
    have h := coreD_mul_add j p (cpoly p)
    rw [mul_comm p (cpoly p)] at h
    linear_combination h
  -- the second integration by parts
  have hA : Q' * pderiv j s = pderiv j (Q' * s) - pderiv j Q' * s := by
    rw [show pderiv j (Q' * s) = pderiv j Q' * s + Q' * pderiv j s from
      MvPolynomial.pderiv_mul]
    ring
  have hGB : gaussInt (X j * (Q' * s)) = gaussInt (pderiv j (Q' * s)) :=
    (gaussInt_pderiv j (Q' * s)).symm
  have hAsplit : (gaussInt (Q' * pderiv j s)).re
      = (gaussInt (X j * (Q' * s))).re - (gaussInt (pderiv j Q' * s)).re := by
    rw [hA, gaussInt_sub, Complex.sub_re, hGB]
  have hlast : cpoly (pderiv j Q' * p) * p = pderiv j Q' * s := by
    rw [hsdef]
    simp only [cpoly_mul, hQ'']
    ring
  set A := Q' * pderiv j s with hAdef
  set B := X j * (Q' * s) with hBdef
  have hpoly : Q' * (pderiv j s - X j * s) = A - B := by
    rw [hAdef, hBdef]
    ring
  rw [two_re_gaussInt, hsym, hsplit, hpoly, gaussInt_sub, Complex.sub_re, hAsplit]
  rw [hlast]
  ring

/-! ## 4. Summing over the kinetic coordinates -/

/-- The weighted Dirichlet energy in Gaussian-integral form: `∑_{j∈S} ∫ Q |∇_j p|²`. -/
def weightedDirichlet (S : Finset (Fin d)) (Q p : MvPolynomial (Fin d) ℂ) : ℝ :=
  ∑ j ∈ S, (gaussInt (cpoly (Q * coreD j p) * coreD j p)).re

/-- The Hessian weight: `∑_{j∈S} ∫ (∂_j² Q) |p|²`. -/
def hessForm (S : Finset (Fin d)) (Q p : MvPolynomial (Fin d) ℂ) : ℝ :=
  ∑ j ∈ S, (gaussInt (cpoly (pderiv j (pderiv j Q) * p) * p)).re

/-- **The cross-term identity**: the pairing of the weighted vector `Q p` with `−Δ_S p` is
`weightedDirichlet − ½ hessForm`, exactly.  This is simultaneously the lower bound of §23
(the weighted energy is non-negative) and the upper bound §35 named as missing. -/
theorem crossTerm_eq (S : Finset (Fin d)) (Q p : MvPolynomial (Fin d) ℂ)
    (hQ : cpoly Q = Q) :
    2 * (inner ℂ (pgLp (Q * p)) (pgLp (kinPolyS S p))).re
      = 2 * weightedDirichlet S Q p - hessForm S Q p := by
  have hA : 2 * (∑ j ∈ S, (gaussInt (cpoly (pderiv j Q * p) * coreD j p)).re)
      = - ∑ j ∈ S, (gaussInt (cpoly (pderiv j (pderiv j Q) * p) * p)).re := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => commutator_cross_eq j Q p hQ
  rw [inner_weighted_kinPolyS, Finset.sum_add_distrib, mul_add, hA, weightedDirichlet,
    hessForm]
  ring

/-- **The upper bound on the cross term**: when the Hessian weight is non-negative the cross
term is dominated by the weighted Dirichlet energy.  This is the inequality §35 recorded as
absent from the corpus; it is a corollary of the exact identity, and it holds with no
hypothesis beyond the sign of the Hessian trace. -/
theorem crossTerm_upper (S : Finset (Fin d)) (Q p : MvPolynomial (Fin d) ℂ)
    (hQ : cpoly Q = Q) (hH : 0 ≤ hessForm S Q p) :
    (inner ℂ (pgLp (Q * p)) (pgLp (kinPolyS S p))).re ≤ weightedDirichlet S Q p := by
  have h := crossTerm_eq S Q p hQ
  linarith

/-! ## 5. The weighted energy is additive, and the weight `1` gives the Dirichlet energy -/

theorem weightedDirichlet_add (S : Finset (Fin d)) (Q R p : MvPolynomial (Fin d) ℂ) :
    weightedDirichlet S (Q + R) p
      = weightedDirichlet S Q p + weightedDirichlet S R p := by
  unfold weightedDirichlet
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpoly : cpoly ((Q + R) * coreD j p) * coreD j p
      = cpoly (Q * coreD j p) * coreD j p
        + cpoly (R * coreD j p) * coreD j p := by
    rw [add_mul, cpoly_add, add_mul]
  rw [hpoly, gaussInt_add, Complex.add_re]

theorem weightedDirichlet_one (S : Finset (Fin d)) (p : MvPolynomial (Fin d) ℂ) :
    weightedDirichlet S (1 : MvPolynomial (Fin d) ℂ) p
      = ∑ j ∈ S, ‖pgLp (coreD j p)‖ ^ 2 := by
  unfold weightedDirichlet
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_pgLp_sq, one_mul]

/-! ## 6. The residual of §31 in Hessian form -/

/-- **The exact residual, with the cross term replaced by its value**: the graph norm of
`−Δ_S + W + 1` minus the square of `‖(W + 1)p‖` is the kinetic energy plus twice the weighted
Dirichlet energy of `W + 1`, minus the Hessian weight of `W`.  Every step is an identity, so
this is the sharp form of §31's residual. -/
theorem residual_eq_hessForm (P : SmParams) (c0 : ℝ) (p : MvPolynomial (Fin 163) ℂ) :
    ‖pgLp (kinPolyS smS p)‖ ^ 2
        + 2 * (inner ℂ (pgLp (kinPolyS smS p))
            (pgLp (smPotPoly P c0 * p) + pgLp p)).re
      = ‖pgLp (kinPolyS smS p)‖ ^ 2
        + 2 * weightedDirichlet smS (smPotPoly P c0 + 1) p
        - hessForm smS (smPotPoly P c0) p := by
  have hreal : cpoly (smPotPoly P c0) = smPotPoly P c0 :=
    realCoeff_smPotPoly P c0
  have hcross := crossTerm_eq smS (smPotPoly P c0) p hreal
  have h1 := weightedDirichlet_add smS (smPotPoly P c0) 1 p
  have h2 := weightedDirichlet_one smS p
  rw [inner_KT_eq]
  linarith

/-- **`PotSelfBound P c₀ 1` is the Hessian gap**: the Hessian weight of the potential is
dominated by the kinetic energy plus twice the weighted Dirichlet energy of `W + 1`.  No
inequality is lost anywhere in the passage, so this is an equivalence and not a sufficient
condition. -/
theorem potSelfBound_one_iff_hessForm (P : SmParams) (c0 : ℝ) :
    PotSelfBound P c0 1
      ↔ ∀ p : MvPolynomial (Fin 163) ℂ,
          hessForm smS (smPotPoly P c0) p
            ≤ ‖pgLp (kinPolyS smS p)‖ ^ 2
              + 2 * weightedDirichlet smS (smPotPoly P c0 + 1) p := by
  rw [potSelfBound_one_iff_remainder]
  constructor
  · intro h p
    have hp := h p
    rw [residual_eq_hessForm] at hp
    linarith
  · intro h p
    rw [residual_eq_hessForm]
    have hp := h p
    linarith

/-! ## 7. The Hessian weight as the integral of the trace, and its sign -/

/-- The Hessian weight is the integral of the Hessian trace against `|p|²`. -/
theorem hessForm_eq_trace (S : Finset (Fin d)) (Q p : MvPolynomial (Fin d) ℂ)
    (hQ : cpoly Q = Q) :
    hessForm S Q p
      = (gaussInt (cpoly ((∑ j ∈ S, pderiv j (pderiv j Q)) * p) * p)).re := by
  have hQ2 : ∀ j, cpoly (pderiv j (pderiv j Q)) = pderiv j (pderiv j Q) := by
    intro j
    rw [cpoly_pderiv, cpoly_pderiv, hQ]
  have hpoly : ∑ j ∈ S, cpoly (pderiv j (pderiv j Q) * p) * p
      = cpoly ((∑ j ∈ S, pderiv j (pderiv j Q)) * p) * p := by
    rw [cpoly_mul, cpoly_sum]
    simp only [cpoly_mul, hQ2, Finset.sum_mul]
  unfold hessForm
  rw [← Complex.re_sum]
  congr 1
  rw [← gaussInt_sum, hpoly]

/-- **The Hessian weight is non-negative when the trace of the Hessian is**: the integrand is
the pointwise product of the trace with `|p|²`.  This is the only extra input the upper bound
of `crossTerm_upper` needs at the SM weight. -/
theorem hessForm_nonneg (S : Finset (Fin d)) (Q p : MvPolynomial (Fin d) ℂ)
    (hQ : cpoly Q = Q)
    (hτ : cpoly (∑ j ∈ S, pderiv j (pderiv j Q)) = ∑ j ∈ S, pderiv j (pderiv j Q))
    (hpos : ∀ x : Vd d,
      0 ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (∑ j ∈ S, pderiv j (pderiv j Q))).re) :
    0 ≤ hessForm S Q p := by
  rw [hessForm_eq_trace S Q p hQ]
  have hzero : gaussInt (0 : MvPolynomial (Fin d) ℂ) = 0 := by simp [gaussInt]
  have hmono := gaussInt_re_mono (r := (0 : MvPolynomial (Fin d) ℂ))
    (s := cpoly ((∑ j ∈ S, pderiv j (pderiv j Q)) * p) * p) fun x => ?_
  · rwa [hzero, Complex.zero_re] at hmono
  · rw [eval_weighted_self_re _ p hτ x]
    exact mul_nonneg (hpos x) (sq_nonneg _)

/-! ## 8. The upper bound at the SM weight -/

/-- **§35's missing upper bound, at the SM comparison**: whenever the trace of the Hessian of
the quartic potential is pointwise non-negative, the cross term is dominated by the weighted
Dirichlet energy.  The hypothesis is a sign of a *degree-two* polynomial — the sharpest form
the identity admits — and the corpus does not compute it. -/
theorem sm_crossTerm_upper (P : SmParams) (c0 : ℝ) (p : MvPolynomial (Fin 163) ℂ)
    (hτ : cpoly (∑ j ∈ smS, pderiv j (pderiv j (smPotPoly P c0)))
      = ∑ j ∈ smS, pderiv j (pderiv j (smPotPoly P c0)))
    (hpos : ∀ x : Vd 163,
      0 ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (∑ j ∈ smS, pderiv j (pderiv j (smPotPoly P c0)))).re) :
    2 * (inner ℂ (pgLp (smPotPoly P c0 * p)) (pgLp (kinPolyS smS p))).re
      ≤ 2 * weightedDirichlet smS (smPotPoly P c0) p := by
  have hH := hessForm_nonneg smS (smPotPoly P c0) p (realCoeff_smPotPoly P c0) hτ hpos
  have h := crossTerm_upper smS (smPotPoly P c0) p (realCoeff_smPotPoly P c0) hH
  linarith

end

end BookProof.SmCrossTermHessian
