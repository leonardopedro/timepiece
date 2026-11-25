import Mathlib

/-!
# Chapter MassErrorArithmetic — the U3/U6 resolvent-to-mass arithmetic

This module implements the *conditional* arithmetic layer of `softmodes.md` U3 and
U6 step 1.  It proves no mass gap: the ordered true resolvent values `mu₀, mu₁` and
the whole-space error bound `e_R ≤ e` are hypotheses, exactly as the plan requires
("these conditional interfaces are not completed physics proofs").  What is proved
here is the arithmetic that consumes them:

* `resolvent_inv_interval` — from `|mu − muhat| ≤ e` and `0 < e < muhat`, the true
  resolvent value `mu` lies in `[1/(muhat+e), 1/(muhat−e)]`;
* `energy_interval` — the same window after the inversion `E = s(1/mu − κ)`;
* `mass_lower_bound` / `mass_lower_bound_pos` — `M ≥ s[1/(muhat₁+e) − 1/(muhat₀−e)]`,
  strictly positive when `muhat₀ − muhat₁ > 2e`;
* `level_error_bound` — `|s(1/mu − 1/muhat)| ≤ s·e/(muhat(muhat−e))`;
* `mass_error_bound` — `|M − Mhat| ≤ E_gap = δ₀ + δ₁`;
* `positive_margin` / `gapError_le` — `Mhat > E_gap` (or `> 2·E_level`) gives `M > 0`;
* the uniform-in-`m` envelope `gapError_le_uniform` at a denominator margin `u0`.

Everything is over `ℝ` and imports no physics module, so the lemmas can be applied
once the ordered spectral-count input and `e_R ≤ e` are supplied by the SIRK/Temple
chain.  Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace BookProof.ChapterMassErrorArithmetic

noncomputable section

/-- The per-level energy error `δ_i = s·e/(muhat_i(muhat_i − e))` of U3. -/
def levelError (s e muhat : ℝ) : ℝ := s * e / (muhat * (muhat - e))

/-- The total energy-error budget `E_gap = δ₀ + δ₁` of U3. -/
def gapError (s e mu0hat mu1hat : ℝ) : ℝ :=
  levelError s e mu0hat + levelError s e mu1hat

/-- The certified excitation mass `Mhat = s(muhat₁⁻¹ − muhat₀⁻¹)` of U3.
    Note `muhat₀ ≥ muhat₁`, so this quantity is positive. -/
def massHat (s mu0hat mu1hat : ℝ) : ℝ := s * (1 / mu1hat - 1 / mu0hat)

/-- The true excitation mass `M = E₁ − E₀ = s(mu₁⁻¹ − mu₀⁻¹)`; the shift `κ`
    cancels in the difference. -/
def mass (s mu0 mu1 : ℝ) : ℝ := s * (1 / mu1 - 1 / mu0)

/-- The dimension-independent energy-error envelope of U3: with a uniform
    denominator margin `u0 > e`, `Ebar_gap = 2 s e/(u0(u0 − e))`. -/
def uniformGapError (s e u0 : ℝ) : ℝ := 2 * (s * e / (u0 * (u0 - e)))

/-! ## Elementary interval arithmetic on the resolvent value -/

/-- If `|mu − muhat| ≤ e` with `0 < e < muhat`, then
    `1/(muhat + e) ≤ 1/mu ≤ 1/(muhat − e)`. -/
theorem resolvent_inv_interval {mu muhat e : ℝ} (he : 0 < e) (hehat : e < muhat)
    (hmu : |mu - muhat| ≤ e) :
    1 / (muhat + e) ≤ 1 / mu ∧ 1 / mu ≤ 1 / (muhat - e) := by
  have hepos : 0 < e := he
  have hb := abs_le.mp hmu
  have hlow : muhat - e ≤ mu := by linarith [hb.1]
  have hup : mu ≤ muhat + e := by linarith [hb.2]
  have hposlow : 0 < muhat - e := by linarith
  have hposmu : 0 < mu := lt_of_lt_of_le hposlow hlow
  constructor
  · exact one_div_le_one_div_of_le hposmu hup
  · exact one_div_le_one_div_of_le hposlow hlow

/-- The energy window `E = s(1/mu − κ)` inherits the resolvent interval when `s ≥ 0`. -/
theorem energy_interval {s κ mu muhat e : ℝ} (hs : 0 ≤ s) (he : 0 < e)
    (hehat : e < muhat) (hmu : |mu - muhat| ≤ e) :
    s * (1 / (muhat + e) - κ) ≤ s * (1 / mu - κ) ∧
      s * (1 / mu - κ) ≤ s * (1 / (muhat - e) - κ) := by
  have h := resolvent_inv_interval he hehat hmu
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith [h.1]) hs
  · exact mul_le_mul_of_nonneg_left (by linarith [h.2]) hs

/-! ## One-sided mass lower bound -/

/-- With ordered true levels and `e` below the excited resolvent value,
    `M ≥ s[1/(muhat₁ + e) − 1/(muhat₀ − e)]`.  This is U3's first display;
    the shift `κ` cancels. -/
theorem mass_lower_bound {s κ mu0 mu1 mu0hat mu1hat e : ℝ}
    (hs : 0 ≤ s) (he : 0 < e) (he1 : e < mu1hat) (hord : mu1hat ≤ mu0hat)
    (h0 : |mu0 - mu0hat| ≤ e) (h1 : |mu1 - mu1hat| ≤ e) :
    s * (1 / (mu1hat + e) - 1 / (mu0hat - e)) ≤ mass s mu0 mu1 := by
  have he0 : e < mu0hat := lt_of_lt_of_le he1 hord
  have hE1 := (energy_interval (s := s) (κ := κ) hs he he1 h1).1
  have hE0 := (energy_interval (s := s) (κ := κ) hs he he0 h0).2
  dsimp [mass]
  linarith

/-- Auxiliary separation predicate: `muhat₀ − muhat₁ > 2e`.  It is named so the
    positivity theorem below records the plan's condition in its binder. -/
def sep_gt_two_e (mu0hat mu1hat e : ℝ) : Prop := mu0hat - mu1hat > 2 * e

/-- The lower bound is strictly positive when the certified resolvent values are
    separated by more than `2e`. -/
theorem mass_lower_bound_pos {s mu0hat mu1hat e : ℝ}
    (hs : 0 < s) (he : 0 < e) (he1 : e < mu1hat)
    (hsep : sep_gt_two_e mu0hat mu1hat e) :
    0 < s * (1 / (mu1hat + e) - 1 / (mu0hat - e)) := by
  dsimp [sep_gt_two_e] at hsep
  have hpos1 : 0 < mu1hat + e := by linarith
  have hpos0 : 0 < mu0hat - e := by linarith
  have hlt : mu1hat + e < mu0hat - e := by linarith
  have hinv : 1 / (mu0hat - e) < 1 / (mu1hat + e) := by
    rw [one_div, one_div]
    exact (inv_lt_inv₀ hpos0 hpos1).2 hlt
  exact mul_pos hs (by linarith)

/-! ## Two-level error and the margin test -/

/-- The error of one inverted level is at most the level budget `δ_i`. -/
theorem level_error_bound {s mu muhat e : ℝ} (hs : 0 ≤ s) (he : 0 < e)
    (hehat : e < muhat) (hmu : |mu - muhat| ≤ e) :
    |s * (1 / mu - 1 / muhat)| ≤ levelError s e muhat := by
  have hb := abs_le.mp hmu
  have hlow : muhat - e ≤ mu := by linarith [hb.1]
  have hup : mu ≤ muhat + e := by linarith [hb.2]
  have hposlow : 0 < muhat - e := by linarith
  have hposmuhat : 0 < muhat := by linarith
  have hposmu : 0 < mu := lt_of_lt_of_le hposlow hlow
  have hinvlow : 1 / (muhat + e) ≤ 1 / mu := one_div_le_one_div_of_le hposmu hup
  have hinvup : 1 / mu ≤ 1 / (muhat - e) := one_div_le_one_div_of_le hposlow hlow
  have hid_up : 1 / (muhat - e) - 1 / muhat = e / ((muhat - e) * muhat) := by
    field_simp [ne_of_gt hposlow, ne_of_gt hposmuhat]
    ring
  have hid_low : 1 / (muhat + e) - 1 / muhat = -e / ((muhat + e) * muhat) := by
    field_simp [ne_of_gt (by linarith : 0 < muhat + e), ne_of_gt hposmuhat]
    ring
  have hdenle : (muhat - e) * muhat ≤ (muhat + e) * muhat := by nlinarith [he, hposmuhat]
  have hposden_low : 0 < (muhat - e) * muhat := mul_pos hposlow hposmuhat
  have hposden_up : 0 < (muhat + e) * muhat := mul_pos (by linarith) hposmuhat
  have heq_pos : s * (e / ((muhat - e) * muhat)) = levelError s e muhat := by
    dsimp [levelError]
    ring_nf
  have heq_neg : s * (-e / ((muhat - e) * muhat)) = -(levelError s e muhat) := by
    dsimp [levelError]
    ring_nf
  have hle_inv : 1 / mu - 1 / muhat ≤ e / ((muhat - e) * muhat) := by
    linarith [hinvup, hid_up]
  have hge_inv : -e / ((muhat + e) * muhat) ≤ 1 / mu - 1 / muhat := by
    linarith [hinvlow, hid_low]
  have hfrac_mono : e / ((muhat + e) * muhat) ≤ e / ((muhat - e) * muhat) :=
    div_le_div_of_nonneg_left (le_of_lt he) hposden_low hdenle
  have hneg_mono : -e / ((muhat - e) * muhat) ≤ -e / ((muhat + e) * muhat) := by
    rw [neg_div, neg_div]
    exact neg_le_neg hfrac_mono
  have hupper : s * (1 / mu - 1 / muhat) ≤ levelError s e muhat := by
    rw [← heq_pos]
    exact mul_le_mul_of_nonneg_left hle_inv hs
  have hlower : -(levelError s e muhat) ≤ s * (1 / mu - 1 / muhat) := by
    rw [← heq_neg]
    exact mul_le_mul_of_nonneg_left (le_trans hneg_mono hge_inv) hs
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The total mass error is at most `E_gap = δ₀ + δ₁`. -/
theorem mass_error_bound {s mu0 mu1 mu0hat mu1hat e : ℝ}
    (hs : 0 ≤ s) (he : 0 < e) (he1 : e < mu1hat) (hord : mu1hat ≤ mu0hat)
    (h0 : |mu0 - mu0hat| ≤ e) (h1 : |mu1 - mu1hat| ≤ e) :
    |mass s mu0 mu1 - massHat s mu0hat mu1hat| ≤ gapError s e mu0hat mu1hat := by
  have he0 : e < mu0hat := lt_of_lt_of_le he1 hord
  have hle0 := level_error_bound (s := s) (mu := mu0) (muhat := mu0hat) hs he he0 h0
  have hle1 := level_error_bound (s := s) (mu := mu1) (muhat := mu1hat) hs he he1 h1
  have hdecomp : mass s mu0 mu1 - massHat s mu0hat mu1hat =
      s * (1 / mu1 - 1 / mu1hat) - s * (1 / mu0 - 1 / mu0hat) := by
    dsimp [mass, massHat]
    ring
  rw [hdecomp]
  calc
    |s * (1 / mu1 - 1 / mu1hat) - s * (1 / mu0 - 1 / mu0hat)|
        ≤ |s * (1 / mu1 - 1 / mu1hat)| + |s * (1 / mu0 - 1 / mu0hat)| := by
          exact abs_sub (s * (1 / mu1 - 1 / mu1hat)) (s * (1 / mu0 - 1 / mu0hat))
    _ ≤ levelError s e mu1hat + levelError s e mu0hat := add_le_add hle1 hle0
    _ = gapError s e mu0hat mu1hat := by rw [gapError]; ring

/-- The stopping rule `Mhat > E_gap` yields a strictly positive mass. -/
theorem positive_margin {M Mhat Eg : ℝ} (hclose : |M - Mhat| ≤ Eg)
    (hmargin : Eg < Mhat) : 0 < M := by
  have hleft := (abs_le.mp hclose).1
  linarith

/-- If each level error is at most `E_level`, then `E_gap ≤ 2 E_level`, giving the
    sufficient test `Mhat > 2 E_level` of U3. -/
theorem gapError_le_two {s e mu0hat mu1hat El : ℝ}
    (h0 : levelError s e mu0hat ≤ El) (h1 : levelError s e mu1hat ≤ El) :
    gapError s e mu0hat mu1hat ≤ 2 * El := by
  dsimp [gapError]
  linarith

/-- Mass positivity from the two-level sufficient test. -/
theorem mass_pos_of_two_levels {s e mu0 mu1 mu0hat mu1hat Mhat El : ℝ}
    (hs : 0 ≤ s) (he : 0 < e) (he1 : e < mu1hat) (hord : mu1hat ≤ mu0hat)
    (h0 : |mu0 - mu0hat| ≤ e) (h1 : |mu1 - mu1hat| ≤ e)
    (hEl0 : levelError s e mu0hat ≤ El) (hEl1 : levelError s e mu1hat ≤ El)
    (hMhat : Mhat = massHat s mu0hat mu1hat) (hmargin : 2 * El < Mhat) :
    0 < mass s mu0 mu1 := by
  have hclose := mass_error_bound hs he he1 hord h0 h1
  have hEg := gapError_le_two hEl0 hEl1
  rw [hMhat] at hmargin
  exact positive_margin (le_trans hclose hEg) hmargin

/-! ## The dimension-independent energy-error envelope -/

/-- A single level error is bounded uniformly once `muhat ≥ u0 > e`. -/
theorem levelError_uniform {s muhat e u0 : ℝ} (hs : 0 ≤ s) (he : 0 < e)
    (hu0 : e < u0) (hmu : u0 ≤ muhat) :
    levelError s e muhat ≤ s * e / (u0 * (u0 - e)) := by
  have hu0pos : 0 < u0 := lt_trans he hu0
  have hdenpos : 0 < u0 * (u0 - e) := mul_pos hu0pos (by linarith)
  have hdenle : u0 * (u0 - e) ≤ muhat * (muhat - e) := by nlinarith [hmu, hu0, he]
  have hnum : 0 ≤ s * e := mul_nonneg hs (le_of_lt he)
  dsimp [levelError]
  exact div_le_div_of_nonneg_left hnum hdenpos hdenle

/-- At a uniform denominator margin `u0 ≤ muhat₁ ≤ muhat₀`, the whole two-level
    error is at most the dimension-independent `Ebar_gap`. -/
theorem gapError_uniform {s mu0hat mu1hat e u0 : ℝ}
    (hs : 0 ≤ s) (he : 0 < e) (hu0 : e < u0) (hu0le : u0 ≤ mu1hat)
    (hord : mu1hat ≤ mu0hat) :
    gapError s e mu0hat mu1hat ≤ uniformGapError s e u0 := by
  have h1 := levelError_uniform (s := s) (e := e) (u0 := u0) hs he hu0 hu0le
  have h0 := levelError_uniform (s := s) (e := e) (u0 := u0) hs he hu0
    (le_trans hu0le hord)
  dsimp [gapError, uniformGapError]
  linarith

end

end BookProof.ChapterMassErrorArithmetic
