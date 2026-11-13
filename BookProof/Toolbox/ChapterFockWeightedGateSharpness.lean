/-
# Sharpness of the weighted commutator gate

The weighted Schur theory (`BookProof.FockWeightedSchur`) reduces essential self-adjointness of
`dΓ(A)` to three gates on the one-particle matrix: row, column, and commutator.  For the
Yang–Mills Hamiltonian the band calculus supplies a row support bound, a band radius in the
degree, and an entry bound `|A_{k j}| ≤ C (deg k + 1)^p`, and it is natural to ask which exponent
`p` the commutator gate can tolerate.

The answer is exactly `p = 1`, and this module proves both halves:

* `wCommBound_of_linear_entries` — if the entries grow at most like `(deg j + 1)`, uniformly in a
  band of radius `4`, then the commutator gate holds, with constant `400 C M` where `M` bounds the
  row support size.  So no extra work is needed at order `≤ 2`: the gate is *automatic* there.
* `not_wCommBound_quadratic` — a one-entry column whose entries are `(deg j + 1)^2`, supported at
  degree distance exactly `4`, satisfies the same band and support hypotheses and violates the
  gate for *every* `B`.  So the band calculus' quadratic entry bound cannot imply the gate.

The mechanism is the interplay of two rates.  Across a band of radius `4` the gate weight
`|w_j^2 − w_k^2| / (w_k w_j)` with `w_k = (deg k + 1)^2` decays like `1/deg`, so an entry growing
like `(deg + 1)^p` contributes like `deg^{p−1}`: bounded for `p = 1`, unbounded for `p = 2`.

A third lemma, `not_wCommBound_of_entry`, is the interface to the analysis: if a *single* weighted
entry exceeds `B`, the gate fails.  A concrete lower bound on one entry of `ymHermCol` would
therefore refute `WCommBound (ymW e) (ymHermCol e fabc)` outright, with no combinatorial estimate.
The corpus has no such lower bound; the expected size of the quartic magnetic entries is the
analysis of `CONSOLIDATED_PLAN.md` §2026-11-13e, not a theorem.

## What this does *not* say

`not_wCommBound_quadratic` is a statement about the *hypotheses*: it exhibits a matrix satisfying
the band and support hypotheses with quadratic entry growth that fails the gate.  It is **not** a
statement about `ymHermCol`, and the distinction matters — the Yang–Mills entry bound is an
*upper* bound, so nothing here shows the actual Yang–Mills matrix fails the gate, and no lower
bound on any of its entries is proved anywhere in the corpus.  Deciding the gate for `ymHermCol`
requires the actual Hermite-basis coefficients of the quartic magnetic square
`mulOp (magPoly)²`, which the band calculus discards by design.
-/
import Mathlib
import BookProof.Toolbox.ChapterFockWeightedSchurEsa

namespace BookProof.FockWeightedGateSharpness

open BookProof.FockWeightedSchur

/-! ## The arithmetic: the gate weight decays like `1/deg` across a band -/

/-- With `w = (deg + 1)^2`, the gate weight is at most `80 / (deg k + 1)` across a band of
radius `4`, for `deg k + 1 ≤ deg j + 1`.  The constant is not sharp; what matters is that it
decays in the degree. -/
theorem commWeight_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hba : b ≤ a + 4) :
    |(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2) ≤ 80 / a := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
  have hd0 : (0 : ℝ) ≤ b ^ 2 - a ^ 2 := by linarith
  have hs0 : (0 : ℝ) < b ^ 2 + a ^ 2 := by positivity
  have habs : |(b ^ 2) ^ 2 - (a ^ 2) ^ 2| = (b ^ 2 - a ^ 2) * (b ^ 2 + a ^ 2) := by
    have hfac : (b ^ 2) ^ 2 - (a ^ 2) ^ 2 = (b ^ 2 - a ^ 2) * (b ^ 2 + a ^ 2) := by ring
    rw [hfac, abs_of_nonneg (mul_nonneg hd0 hs0.le)]
  rw [habs, div_le_iff₀ (by positivity : (0 : ℝ) < a ^ 2 * b ^ 2)]
  have hrhs : 80 / a * (a ^ 2 * b ^ 2) = 80 * a * b ^ 2 := by
    field_simp
  rw [hrhs]
  have hone : b ^ 2 + a ^ 2 ≤ 2 * b ^ 2 := by nlinarith
  have htwo : b ^ 2 - a ^ 2 ≤ 4 * (b + a) := by
    have hfac : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
    rw [hfac]
    have hbma : 0 ≤ b - a := by linarith
    have hsum : 0 ≤ b + a := by linarith
    nlinarith
  have hprod : (b ^ 2 - a ^ 2) * (b ^ 2 + a ^ 2) ≤ (4 * (b + a)) * (2 * b ^ 2) :=
    mul_le_mul htwo hone (by positivity) (by linarith)
  calc (b ^ 2 - a ^ 2) * (b ^ 2 + a ^ 2) ≤ (4 * (b + a)) * (2 * b ^ 2) := hprod
    _ = 8 * (b + a) * b ^ 2 := by ring
    _ ≤ 8 * (6 * a) * b ^ 2 := by
        have h6 : b + a ≤ 6 * a := by linarith
        have : (0 : ℝ) ≤ 8 * b ^ 2 := by positivity
        nlinarith
    _ = 48 * a * b ^ 2 := by ring
    _ ≤ 80 * a * b ^ 2 := by
        have : (0 : ℝ) ≤ a * b ^ 2 := by positivity
        nlinarith

/-- **The gate term is bounded across a band of radius `4`** once entries grow linearly: the
degree factor `b` cancels the decaying weight. -/
theorem commTerm_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : |b - a| ≤ 4) :
    b * (|(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2)) ≤ 400 := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hsymm : |(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2)
      = |(a ^ 2) ^ 2 - (b ^ 2) ^ 2| / (b ^ 2 * a ^ 2) := by
    rw [abs_sub_comm, mul_comm (a ^ 2) (b ^ 2)]
  rcases le_total a b with h | h
  · have hratio := commWeight_le ha h (by linarith [abs_le.mp hab])
    have hb_le : b ≤ 5 * a := by linarith [abs_le.mp hab]
    have hb' : 0 ≤ b := by linarith
    have hstep : b * (80 / a) ≤ 400 := by
      rw [show b * (80 / a) = 80 * b / a by ring]
      rw [div_le_iff₀ ha0]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hratio hb', hstep]
  · have hratio := commWeight_le hb h (by linarith [abs_le.mp hab])
    rw [hsymm]
    have hstep : b * (80 / b) ≤ 400 := by
      rw [show b * (80 / b) = 80 by field_simp]
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left hratio hb0.le, hstep]

/-! ## The gate holds for linear entry growth -/

/-- **The commutator gate is automatic at order `≤ 2`.**  A matrix with row support at most `M`,
band radius `4` in the degree, and entries at most `C (deg j + 1)` satisfies the commutator gate
with `B = 400 C M` for the symbol `w_k = (deg k + 1)^2`. -/
theorem wCommBound_of_linear_entries {deg : ℕ → ℕ} {col : ℕ → (ℕ →₀ ℂ)} {C M : ℝ}
    (hC : 0 ≤ C) (hcard : ∀ k, ((col k).support.card : ℝ) ≤ M)
    (hband : ∀ k, ∀ j ∈ (col k).support, |(deg j : ℝ) - (deg k : ℝ)| ≤ 4)
    (hentry : ∀ k, ∀ j ∈ (col k).support, ‖(col k) j‖ ≤ C * ((deg j : ℝ) + 1)) :
    WCommBound (fun k => ((deg k : ℝ) + 1) ^ 2) col (400 * C * M) := by
  intro k
  simp only []
  have hterm : ∀ j ∈ (col k).support,
      ‖(col k) j‖
          * |(((deg j : ℝ) + 1) ^ 2) ^ 2 - (((deg k : ℝ) + 1) ^ 2) ^ 2|
            / (((deg k : ℝ) + 1) ^ 2 * ((deg j : ℝ) + 1) ^ 2) ≤ 400 * C := by
    intro j hj
    set a : ℝ := (deg k : ℝ) + 1 with ha_def
    set b : ℝ := (deg j : ℝ) + 1 with hb_def
    have ha1 : 1 ≤ a := by rw [ha_def]; linarith [Nat.cast_nonneg (α := ℝ) (deg k)]
    have hb1 : 1 ≤ b := by rw [hb_def]; linarith [Nat.cast_nonneg (α := ℝ) (deg j)]
    have hdist : |b - a| ≤ 4 := by
      have hb := hband k j hj
      rw [ha_def, hb_def]
      have heq : (deg j : ℝ) + 1 - ((deg k : ℝ) + 1) = (deg j : ℝ) - (deg k : ℝ) := by ring
      rw [heq]
      exact hb
    have hbound := commTerm_le ha1 hb1 hdist
    have hent := hentry k j hj
    rw [← hb_def] at hent
    have hratio : 0 ≤ |(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2) := by positivity
    have hsplit : ‖(col k) j‖ * |(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2)
        = ‖(col k) j‖ * (|(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2)) := by ring
    rw [hsplit]
    have h1 : ‖(col k) j‖ * (|(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2))
        ≤ (C * b) * (|(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2)) :=
      mul_le_mul hent le_rfl hratio (mul_nonneg hC (by linarith))
    have h2 : (C * b) * (|(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2)) ≤ C * 400 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hbound hC
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  calc ((col k).support.card : ℝ) * (400 * C)
      ≤ M * (400 * C) := mul_le_mul_of_nonneg_right (hcard k) (by positivity)
    _ = 400 * C * M := by ring

/-! ## Turning a single large entry into a refutation

The negative half above is synthetic: it exhibits a matrix satisfying the band hypotheses whose
entries are too large.  The actual Yang–Mills matrix would have to be refuted by computing one of
its entries, and the step from such a computation to `¬ WCommBound` is the following. -/

/-- **A single oversized entry refutes the gate.**  If the `(k, j)` entry of the matrix, weighted by
`|w_j² − w_k²| / (w_k w_j)`, already exceeds `B`, then the `k`-th row sum exceeds `B` and the gate
fails.  This is the interface between a concrete lower bound on a Hermite coefficient and
`¬ WCommBound`; it is the form in which an entry computation for the quartic magnetic square
would be consumed. -/
theorem not_wCommBound_of_entry {w : ℕ → ℝ} (hw : ∀ k, 0 < w k) {col : ℕ → (ℕ →₀ ℂ)} {B : ℝ}
    {k j : ℕ} (hj : j ∈ (col k).support)
    (hbig : B < ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j)) :
    ¬ WCommBound w col B := by
  intro hgate
  have hrow := hgate k
  have hnn : ∀ x ∈ (col k).support, 0 ≤ ‖(col k) x‖ * |w x ^ 2 - w k ^ 2| / (w k * w x) := by
    intro x _
    exact div_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (mul_pos (hw k) (hw x)).le
  have hle : ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j)
      ≤ ∑ x ∈ (col k).support, ‖(col k) x‖ * |w x ^ 2 - w k ^ 2| / (w k * w x) :=
    Finset.single_le_sum hnn hj
  linarith

/-! ## Quadratic entry growth breaks the gate -/

/-- The degree function of the witness: the index *is* the degree. -/
def shiftDeg (k : ℕ) : ℕ := k

/-- A column with one entry at degree distance exactly `4`, of size `(deg j + 1)^2` — the size the
band calculus permits, concentrated on a single band member. -/
noncomputable def shiftCol (k : ℕ) : ℕ →₀ ℂ :=
  Finsupp.single (k + 4) ((((k : ℝ) + 5) ^ 2 : ℝ) : ℂ)

theorem shiftCol_support (k : ℕ) : (shiftCol k).support = {k + 4} := by
  refine Finsupp.support_single_ne_zero _ ?_
  have h : ((k : ℝ) + 5) ^ 2 ≠ 0 := by positivity
  exact_mod_cast h

/-- **Quadratic entry growth defeats the commutator gate.**  The witness satisfies row support
bound `1`, band radius `4`, and the entry bound `C (deg j + 1)^2` with `C = 1`, yet its commutator
gate sum at row `k` is at least `16 (k + 1)`, which is unbounded. -/
theorem not_wCommBound_quadratic :
    ¬ ∃ B : ℝ, WCommBound (fun k => ((shiftDeg k : ℝ) + 1) ^ 2) shiftCol B := by
  rintro ⟨B, hB⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (B / 16)
  have hrow := hB k
  rw [shiftCol_support, Finset.sum_singleton] at hrow
  simp only [] at hrow
  set a : ℝ := (k : ℝ) + 1 with ha_def
  set b : ℝ := (k : ℝ) + 5 with hb_def
  have ha0 : (0 : ℝ) < a := by rw [ha_def]; positivity
  have hnorm : ‖(shiftCol k) (k + 4)‖ = b ^ 2 := by
    rw [shiftCol, Finsupp.single_eq_same]
    have hb2 : (0 : ℝ) ≤ b ^ 2 := by positivity
    have hcast : ((((k : ℝ) + 5) ^ 2 : ℝ) : ℂ) = ((b ^ 2 : ℝ) : ℂ) := by
      rw [hb_def]
    rw [hcast, Complex.norm_real]
    exact abs_of_nonneg hb2
  have hjr : ((shiftDeg (k + 4) : ℝ) + 1) = b := by
    simp only [shiftDeg]
    rw [hb_def]
    push_cast
    ring
  have hkr : ((shiftDeg k : ℝ) + 1) = a := by
    simp only [shiftDeg]
    exact ha_def.symm
  rw [hnorm, hjr, hkr] at hrow
  -- the row inequality is now `b^2 * |(b^2)^2 − (a^2)^2| / (a^2 b^2) ≤ B`
  have hval : b ^ 2 * |(b ^ 2) ^ 2 - (a ^ 2) ^ 2| / (a ^ 2 * b ^ 2) = (b ^ 4 - a ^ 4) / a ^ 2 := by
    have hpos : (0 : ℝ) < a ^ 2 * b ^ 2 := by positivity
    have hlt : a ^ 4 < b ^ 4 := by
      have hab : a < b := by rw [ha_def, hb_def]; linarith
      nlinarith
    rw [show (b ^ 2) ^ 2 = b ^ 4 by ring, show (a ^ 2) ^ 2 = a ^ 4 by ring,
      abs_of_pos (by linarith)]
    rw [show a ^ 2 * b ^ 2 = b ^ 2 * a ^ 2 by ring]
    exact mul_div_mul_left _ _ (by positivity : b ^ 2 ≠ 0)
  rw [hval] at hrow
  -- and that term grows like `16 (k + 1)`
  have hfac : b ^ 4 - a ^ 4 = 4 * (b + a) * (b ^ 2 + a ^ 2) := by
    have hb4 : b = a + 4 := by rw [ha_def, hb_def]; ring
    rw [hb4]
    ring
  have hgrow : 16 * a ≤ (b ^ 4 - a ^ 4) / a ^ 2 := by
    rw [hfac, le_div_iff₀ (by positivity : (0 : ℝ) < a ^ 2)]
    have h1 : 2 * a ≤ b + a := by rw [ha_def, hb_def]; linarith
    have h2 : 2 * a ^ 2 ≤ b ^ 2 + a ^ 2 := by
      have : a ≤ b := by rw [ha_def, hb_def]; linarith
      nlinarith
    nlinarith [h1, h2, ha0]
  have hk16 : B / 16 < a := by rw [ha_def]; linarith
  nlinarith [hrow, hgrow, hk16]

end BookProof.FockWeightedGateSharpness
