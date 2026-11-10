import Mathlib
import BookProof.Sm.ChapterSmKineticGarding
import BookProof.ChapterGaussCoreQuadBounds

/-!
# The weighted integration-by-parts identity on the Gauss–polynomial core

Work order: `SM_ESA_COMPLETION_PLAN.md` §23.

## 1. The identity

§22 reduced the open quartic elliptic estimate to the self-bound of the potential, and named the
missing analytic tool: the sign of the cross term
`Re ⟪W u, −Δ u⟫ = ‖√W ∇u‖² + Re ⟪u ∇W, ∇u⟫`, whose first term is non-negative.  This section
supplies that identity on the Gauss–polynomial core, where everything is an integral of polynomials
against the Gaussian weight (`gaussInt`), so no analysis of square roots or gradients is needed.

The statement is the discrete form of the identity.  With `−Δ_S` realized on the core by
`kinPolyS S` and `∇` by the twisted derivative `coreD j = ∂_j − x_j/2` — the corpus's own
conventions throughout `BookProof/Toolbox/ChapterDegSchrodingerCore.lean` — one Gaussian
integration by parts gives

```text
⟪Q u, −Δ_S u⟫ = ∑_{j ∈ S} ( ‖√Q ∇_j u‖²  +  Re ⟪u ∇_j Q, ∇_j u⟫ ),
```

i.e. the weighted Dirichlet energy plus the commutator term, term by term in the coordinates of `S`.

* `gaussInt_weighted_kinPolyS` — the identity in Gaussian-integral form: the pairing of `Q u` with
  `−Δ_S u` is the sum over `j ∈ S` of the two pieces.  It follows from the corpus's integration by
  parts `gaussInt_kinPolyS` and the Leibniz rule `coreD_mul`: the weight moves inside the derivative
  and leaves exactly the two terms.
* `inner_weighted_kinPolyS` — the same identity in inner-product form, i.e. with the left-hand side
  written as `Re ⟪Q u, −Δ_S u⟫` for `u = pgLp p`.
* `eval_weighted_self_re` — pointwise, the weighted self-pairing is the weight times the squared
  modulus: `(Q q, q) ↦ Q(x)‖q(x)‖²`.
* `gaussInt_weighted_self_nonneg` / `inner_weighted_kinPolyS_dirichlet_nonneg` — hence
  `‖√Q ∇u‖² ≥ 0` whenever the weight is pointwise non-negative, which is the sign the elliptic
  argument needs.
* `inner_weighted_kinPolyS_ge` — the resulting semi-boundedness direction:
  `Re ⟪Q u, −Δ_S u⟫ ≥ ∑_{j∈S} Re ⟪u ∇_j Q, ∇_j u⟫`.
* `sm_weighted_kinetic_ibp`, `sm_weighted_kinetic_ibp_ge` — the identity at the SM comparison: the
  weight is the quartic potential `smPotPoly P c₀`, whose real coefficients make the non-negativity
  hypothesis automatic (`realCoeff_smPotPoly`).

## 2. What this does and does not prove

This is the *first* ingredient of `PotSelfBound` (§22) and nothing more.  What remains is the
interpolation of `coreD` between `L²` and the graph norm of `−Δ_S + W + 1`: the identity gives the
sign, but the estimate `‖W p + p‖ ≤ β ‖Δ_S p + W p + p‖` also needs the second term to be controlled
by the graph norm, and the corpus has no bound of that shape for a quartic weight.  The module is
therefore a step in the proof of `PotSelfBound`, not a proof of it, and `PotSelfBound` stays a
hypothesis downstream.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmGaussWeightedIbp

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds
open BookProof.SmComparisonEsa BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.SmFarisLavine
open BookProof.SmKineticElliptic BookProof.SmKineticGarding

noncomputable section

variable {d : ℕ}

/-! ## 1. The identity in Gaussian-integral form -/

/-- **The weighted integration-by-parts identity**: pairing the weighted vector `Q u` with `−Δ_S u`
gives, coordinate by coordinate, the weighted Dirichlet energy plus the commutator term in which the
derivative falls on the weight. -/
theorem gaussInt_weighted_kinPolyS (S : Finset (Fin d)) (Q p : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (Q * p) * kinPolyS S p)
      = ∑ j ∈ S, (gaussInt (cpoly (pderiv j Q * p) * coreD j p)
          + gaussInt (cpoly (Q * coreD j p) * coreD j p)) := by
  rw [gaussInt_kinPolyS]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coreD_mul, cpoly_add, add_mul, gaussInt_add]

/-! ## 2. The weighted self-pairing, pointwise -/

/-- **The weighted self-pairing is the weight times the squared modulus**, pointwise: for a weight
with real coefficients, `q ↦ (Q q, q)` evaluates to `Q(x)‖q(x)‖²`. -/
theorem eval_cpoly_self_eq (q : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly q * q)
      = ((‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 : ℝ) : ℂ) := by
  rw [MvPolynomial.eval_mul, ← conj_polyEval]
  set z := MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q with hz
  rw [Complex.sq_norm, ← Complex.normSq_eq_conj_mul_self]

/-- **The pointwise form of the weighted Dirichlet energy.** -/
theorem eval_weighted_self_re (Q q : MvPolynomial (Fin d) ℂ) (hQ : cpoly Q = Q) (x : Vd d) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly (Q * q) * q)).re
      = (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) Q).re
        * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 := by
  have hshape : cpoly (Q * q) * q = Q * (cpoly q * q) := by
    rw [cpoly_mul, hQ]
    ring
  rw [hshape, MvPolynomial.eval_mul, eval_cpoly_self_eq, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **A real-coefficient polynomial takes real values** on real points. -/
theorem eval_im_zero_of_cpoly_eq (Q : MvPolynomial (Fin d) ℂ) (hQ : cpoly Q = Q)
    (x : Vd d) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) Q).im = 0 := by
  have h : (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) Q)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) Q := by
    rw [conj_polyEval, hQ]
  exact Complex.conj_eq_iff_im.mp h

/-! ## 3. Non-negativity of the weighted Dirichlet energy -/

/-- **`‖√Q ∇q‖² ≥ 0`**: the weighted self-pairing is non-negative whenever the weight is. -/
theorem gaussInt_weighted_self_nonneg (Q q : MvPolynomial (Fin d) ℂ) (hQ : cpoly Q = Q)
    (hQ0 : ∀ x : Vd d, 0 ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) Q).re) :
    0 ≤ (gaussInt (cpoly (Q * q) * q)).re := by
  have hzero : gaussInt (0 : MvPolynomial (Fin d) ℂ) = 0 := by simp [gaussInt]
  have hmono := gaussInt_re_mono (r := (0 : MvPolynomial (Fin d) ℂ))
    (s := cpoly (Q * q) * q) fun x => ?_
  · rwa [hzero, Complex.zero_re] at hmono
  · rw [eval_weighted_self_re Q q hQ x]
    exact mul_nonneg (hQ0 x) (sq_nonneg _)

/-- **The weighted Dirichlet energy of the coordinate family is non-negative.** -/
theorem inner_weighted_kinPolyS_dirichlet_nonneg (S : Finset (Fin d))
    (Q p : MvPolynomial (Fin d) ℂ) (hQ : cpoly Q = Q)
    (hQ0 : ∀ x : Vd d, 0 ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) Q).re) :
    0 ≤ ∑ j ∈ S, (gaussInt (cpoly (Q * coreD j p) * coreD j p)).re :=
  Finset.sum_nonneg fun j _ => gaussInt_weighted_self_nonneg Q (coreD j p) hQ hQ0

/-! ## 4. The identity in inner-product form, and the sign -/

/-- **The weighted identity in inner-product form**: `Re ⟪Q u, −Δ_S u⟫` is the weighted Dirichlet
energy plus the commutator term, for `u = pgLp p`. -/
theorem inner_weighted_kinPolyS (S : Finset (Fin d)) (Q p : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp (Q * p)) (pgLp (kinPolyS S p))).re
      = ∑ j ∈ S, ((gaussInt (cpoly (pderiv j Q * p) * coreD j p)).re
          + (gaussInt (cpoly (Q * coreD j p) * coreD j p)).re) := by
  rw [QgHermiteFriedrichs.inner_pgLp_pgLp, gaussInt_weighted_kinPolyS, Complex.re_sum]
  exact Finset.sum_congr rfl fun j _ => Complex.add_re _ _

/-- **The sign of the cross term**: `Re ⟪Q u, −Δ_S u⟫` dominates the commutator term, because the
weighted Dirichlet energy it differs from is non-negative.  This is the semi-boundedness direction
that the elliptic argument uses. -/
theorem inner_weighted_kinPolyS_ge (S : Finset (Fin d)) (Q p : MvPolynomial (Fin d) ℂ)
    (hQ : cpoly Q = Q)
    (hQ0 : ∀ x : Vd d, 0 ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) Q).re) :
    ∑ j ∈ S, (gaussInt (cpoly (pderiv j Q * p) * coreD j p)).re
      ≤ (inner ℂ (pgLp (Q * p)) (pgLp (kinPolyS S p))).re := by
  rw [inner_weighted_kinPolyS, Finset.sum_add_distrib]
  have hb := inner_weighted_kinPolyS_dirichlet_nonneg S Q p hQ hQ0
  linarith

/-! ## 5. The SM comparison: the quartic potential as the weight -/

set_option maxHeartbeats 1000000 in
-- evaluating the `49` field polynomials of the potential exceeds the default budget
/-- **The quartic potential is pointwise non-negative** for `c₀ ≥ 0`. -/
theorem smPotPoly_nonneg (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (x : Vd 163) :
    0 ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (smPotPoly P c0)).re := by
  have h := polyW_smPotPoly P c0 x
  rw [polyW] at h
  rw [h]
  have h1 : (0 : ℝ) ≤ ∑ r : Fin 49, (polyW (smPhi P r) x) ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ ∑ m : Fin 40, (x (smCoord m)) ^ 2 := by positivity
  linarith

set_option maxHeartbeats 1000000 in
-- the `163`-dimensional coordinate set of the comparison exceeds the default budget
/-- **The identity at the SM comparison**: the weight is the quartic potential `smPotPoly P c₀` and
the Laplacian is the one of `smS`, so
`Re ⟪W u, −Δ_S u⟫ = ‖√W ∇u‖² + Re ⟪u ∇W, ∇u⟫` in the corpus's twisted-gradient convention. -/
theorem sm_weighted_kinetic_ibp (P : SmParams) (c0 : ℝ) (p : MvPolynomial (Fin 163) ℂ) :
    (inner ℂ (pgLp (smPotPoly P c0 * p)) (pgLp (kinPolyS smS p))).re
      = ∑ j ∈ smS, ((gaussInt (cpoly (pderiv j (smPotPoly P c0) * p) * coreD j p)).re
          + (gaussInt (cpoly (smPotPoly P c0 * coreD j p) * coreD j p)).re) :=
  inner_weighted_kinPolyS smS (smPotPoly P c0) p

set_option maxHeartbeats 1000000 in
-- the `163`-dimensional coordinate set of the comparison exceeds the default budget
/-- **The sign at the SM comparison**: the weighted Dirichlet energy of the quartic potential is
non-negative, so `Re ⟪W u, −Δ_S u⟫` dominates the commutator term.  The non-negativity of the weight
comes from `realCoeff_smPotPoly`, which is what makes the SM instance free of hypotheses. -/
theorem sm_weighted_kinetic_ibp_ge (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (p : MvPolynomial (Fin 163) ℂ) :
    ∑ j ∈ smS, (gaussInt (cpoly (pderiv j (smPotPoly P c0) * p) * coreD j p)).re
      ≤ (inner ℂ (pgLp (smPotPoly P c0 * p)) (pgLp (kinPolyS smS p))).re :=
  inner_weighted_kinPolyS_ge smS (smPotPoly P c0) p
    (realCoeff_smPotPoly P c0) (smPotPoly_nonneg P hc0)

end

end BookProof.SmGaussWeightedIbp
