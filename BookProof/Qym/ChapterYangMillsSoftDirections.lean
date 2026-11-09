import Mathlib

/-!
# S1: the magnetic split `B = B_deriv + g B_comm` and its cross term

`softmodes.md` (work package S1) splits the Weyl-gauge magnetic field into the derivative part and
the coupling term, and makes two statements about that split that can be turned into Lean without
any analysis of the concrete form:

* **N: the naive monotonicity in the coupling is false.**  One may *not* assume
  `‖B_deriv + g B_comm‖² ≥ g²‖B_comm‖²`; the cross term has a sign, and it is not controlled by the
  coupling.  `no_norm_add_smul_lower_bound` is the counterexample — it is one-dimensional and
  scalar, so the failure is not an artefact of the non-abelian structure constants.
* **U: the valid replacement.**  For `0 < ε < 1`,
  `‖X + Y‖² ≥ (1 − ε)‖X‖² − (ε⁻¹ − 1)‖Y‖²` (`norm_add_sq_ge_split`), and in the shape in which the
  plan uses it, with `Y` carrying the coupling,
  `‖X + g • Y‖² ≥ (1 − ε)‖X‖² − (ε⁻¹ − 1)g²‖Y‖²` (`norm_add_smul_sq_ge_split`).  The proof is
  Cauchy–Schwarz plus AM–GM: the cross term is at worst `−2‖X‖‖Y‖`, and `2‖X‖‖Y‖` is charged to
  `ε‖X‖² + ε⁻¹‖Y‖²`.

## What the estimate does and does not buy

The estimate is a statement about norms of *vectors*, so applying it to `q_h` requires a split of
the form at each point of configuration space — i.e. an identification of the derivative and
commutator parts of the concrete `magPoly` as two vectors, which is the plan's `C` item (the
polynomial split of `Qym/ChapterYangMillsFieldStrengthSplit.lean` gives the two pieces as
polynomials; nothing there says their squares add cross terms in this shape).  Beyond that:

* **C — the loss has to be paid.**  The term `(ε⁻¹ − 1)‖g B_comm‖²` is negative; for the estimate to
  become a coercivity statement on the magnetic slot it must be dominated by part of the reference
  form (`q_ref` of `ChapterReferenceGap.href_spectral_gap`), and that relative bound is exactly the
  `a < 1` input of `YangMillsFormClosureNonDiagonal`.  This module supplies the algebra of the
  comparison, not the domination.
* **C — localization.**  The plan asks for an IMS/localization bound paying for the partition
  gradients.  A global estimate on the whole core is not implied by a pointwise one when the field
  is cut into charts, and no IMS statement is made here.
* **B — the abelian/linearized description of a pure gauge.**  `A_i = ∂_i φ` is the abelian
  description; for `f ≠ 0` the orbit of zero is strictly larger, which the corpus already records as
  `BookProof.BrstLongitudinal.gaussVec_eq_longitudinal_add_comm` (the longitudinal plus the
  commutator piece) and `commGaugeVec_eq_zero_of_abelian` (the piece vanishes only for `f = 0`).
  Nothing in this module changes that: it works at the level of two abstract vectors `X`, `Y`, so it
  is agnostic between the abelian and non-abelian reading — which is the honest scope of a
  *norm* inequality.
-/

namespace BookProof.YangMillsSoftDirections


/-- **The cross-term estimate.**  For `0 < ε < 1` and any two vectors of a real inner product space,

`‖X + Y‖² ≥ (1 − ε)‖X‖² − (ε⁻¹ − 1)‖Y‖²`.

Cauchy–Schwarz gives `⟪X, Y⟫ ≥ −‖X‖‖Y‖`, and `2‖X‖‖Y‖ ≤ ε‖X‖² + ε⁻¹‖Y‖²` is AM–GM with the
weight `ε`: it is `ε(‖X‖ − ε⁻¹‖Y‖)² ≥ 0`.  This is the plan's "valid starting estimate": the
coefficient of `‖Y‖²` is negative, so the estimate is not a lower bound in `Y` — the loss must be
paid elsewhere. -/
theorem norm_add_sq_ge_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X Y : E} {ε : ℝ} (hε : 0 < ε) :
    (1 - ε) * ‖X‖ ^ 2 - (ε⁻¹ - 1) * ‖Y‖ ^ 2 ≤ ‖X + Y‖ ^ 2 := by
  have hnorm : ‖X + Y‖ ^ 2 = ‖X‖ ^ 2 + 2 * inner ℝ X Y + ‖Y‖ ^ 2 := norm_add_sq_real X Y
  have hcs : -(‖X‖ * ‖Y‖) ≤ inner ℝ X Y := by
    linarith [neg_abs_le (inner ℝ X Y), abs_real_inner_le_norm X Y]
  have hamgm : 2 * (‖X‖ * ‖Y‖) ≤ ε * ‖X‖ ^ 2 + ε⁻¹ * ‖Y‖ ^ 2 := by
    have hexp : ε * (‖X‖ - ε⁻¹ * ‖Y‖) ^ 2
        = ε * ‖X‖ ^ 2 - 2 * (‖X‖ * ‖Y‖) + ε⁻¹ * ‖Y‖ ^ 2 := by
      have hne : ε ≠ 0 := hε.ne'
      field_simp
      ring
    have hnn : 0 ≤ ε * (‖X‖ - ε⁻¹ * ‖Y‖) ^ 2 := mul_nonneg hε.le (sq_nonneg _)
    linarith [hexp, hnn]
  rw [hnorm]
  nlinarith [hcs, hamgm]

/-- **The estimate in the shape of the coupling split.**  With `B = B_deriv + g • B_comm` and
`0 < ε < 1`,

`‖B_deriv + g • B_comm‖² ≥ (1 − ε)‖B_deriv‖² − (ε⁻¹ − 1)g²‖B_comm‖²`.

The coupling now multiplies the *loss*, which is the point of the split: a larger `g` makes the
negative term larger, so no monotonicity in `g` can be read off this estimate (and
`no_norm_add_smul_lower_bound` shows that none holds in general). -/
theorem norm_add_smul_sq_ge_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X Y : E} {g ε : ℝ} (hε : 0 < ε) :
    (1 - ε) * ‖X‖ ^ 2 - (ε⁻¹ - 1) * g ^ 2 * ‖Y‖ ^ 2 ≤ ‖X + g • Y‖ ^ 2 := by
  have h := norm_add_sq_ge_split (X := X) (Y := g • Y) hε
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  convert h using 1
  ring

/-- **The naive coupling monotonicity is false.**  `‖B_deriv + g B_comm‖² ≥ g²‖B_comm‖²` fails
already in one dimension with scalar entries: take `X = 1`, `Y = −1`, `g = 2`.  Then
`‖X + gY‖² = 1` while `g²‖Y‖² = 4`, so the cross term has overwhelmed the coupling term.  This is
why the plan forbids the assumption instead of deriving it: the inequality is not true for the
*concrete* interaction either, and the counterexample does not use `f ≠ 0`, so non-abelianity is not
the source of the failure. -/
theorem no_norm_add_smul_lower_bound :
    ¬ ∀ (X Y : ℝ) (g : ℝ), 1 ≤ g → g ^ 2 * ‖Y‖ ^ 2 ≤ ‖X + g * Y‖ ^ 2 := by
  intro h
  have h2 := h 1 (-1) 2 (by norm_num)
  norm_num [Real.norm_eq_abs] at h2

/-- The plan's concrete choice `ε = 1/2`: `½‖X‖² − ‖Y‖² ≤ ‖X + Y‖²`.  Recorded because it is the
form in which the estimate is usable — it loses a factor one half on the derivative part and charges
the commutator part with coefficient exactly `1`. -/
theorem norm_add_sq_ge_half {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X Y : E) : (1 / 2) * ‖X‖ ^ 2 - ‖Y‖ ^ 2 ≤ ‖X + Y‖ ^ 2 := by
  have h := norm_add_sq_ge_split (X := X) (Y := Y) (ε := 1 / 2) (by norm_num)
  linarith [h]

end BookProof.YangMillsSoftDirections
