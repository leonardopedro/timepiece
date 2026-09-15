import Mathlib
import BookProof.ChapterScalaronFiberFL

/-!
# The full scalaron potential is **not** a quadratic form — so the gravity Hamiltonian
of interest is **not** a kinetic-plus-squares operator

The `84`-coordinate jet model of the 3D gauge-fixed gravity Hamiltonian
(`BookProof.Qg3DGaugeFL`) is a *kinetic-plus-squares* operator: its potential is
`½ Σ_r L_r(x)²`, a quadratic form in the coordinates, and that identification is what lets
the abstract kinetic-plus-squares machinery apply to it.  That model carries the tetrad and
the independent coordinates for its spatial derivatives, but **no scalaron**.

The Hamiltonian this development delivers for quantum gravity — vielbein *and* scalaron with
the **full exponential Einstein-frame potential** (no Taylor expansion) *and* 3D gauge fixing
*and* the gauge fixing of the variables representing spatial derivatives — is **not** of that
shape, and this module proves it: the Starobinsky potential

`V(φ) = M⁴/(16α)·(1 − exp(−√(2/3)·φ/M))²`

is not a polynomial of degree `≤ 2` (`starobinskyV_not_quadratic`), hence the scalaron fibre
potential `φ²/4 + V(φ) + s` is not one either (`starobinskyPot_not_quadratic`), hence it is
not a half-sum of squares of linear forms (`starobinskyPot_not_sum_of_squares`).

The argument is elementary and uses only two structural features of the exponential wall: it
is non-negative on the whole line, and it is **bounded** on the plateau side `φ ≥ 0`
(`starobinskyV_le_plateau`), whereas a polynomial of degree `≤ 2` that is non-negative on the
line and bounded on a half-line is constant — and the wall is not constant
(`starobinskyV_pos`).

This is why the gravity Hamiltonian with the scalaron is proved essentially self-adjoint by
the Faris–Lavine mode machinery of `BookProof.QgVielbeinScalaronGaugeFL`, whose fibre carries
an arbitrary smooth non-negative wall, and *not* by the kinetic-plus-squares route.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ScalaronNotQuadratic

open BookProof.Starobinsky BookProof.ScalaronFiberFL

/-- On the plateau side `φ ≥ 0` the exponential wall is bounded by its asymptotic value
`M⁴/(16α)`. -/
theorem starobinskyV_le_plateau {M alpha : ℝ} (hM : 0 < M) (halpha : 0 < alpha) {phi : ℝ}
    (hphi : 0 ≤ phi) : starobinskyV M alpha phi ≤ M ^ 4 / (16 * alpha) := by
  have harg : -(Real.sqrt (2 / 3)) * phi / M = -(Real.sqrt (2 / 3) * phi / M) := by ring
  have hnn : 0 ≤ Real.sqrt (2 / 3) * phi / M := by positivity
  have h1 : Real.exp (-(Real.sqrt (2 / 3)) * phi / M) ≤ 1 := by
    rw [harg, Real.exp_le_one_iff]
    linarith
  have h2 : 0 < Real.exp (-(Real.sqrt (2 / 3)) * phi / M) := Real.exp_pos _
  have hK : 0 < M ^ 4 / (16 * alpha) := by positivity
  have hsq : (1 - Real.exp (-(Real.sqrt (2 / 3)) * phi / M)) ^ 2 ≤ 1 := by nlinarith
  have := mul_le_mul_of_nonneg_left hsq (le_of_lt hK)
  simpa [starobinskyV] using this

/-- The wall is strictly positive away from the origin: it is **not** the zero potential. -/
theorem starobinskyV_pos {M alpha : ℝ} (hM : M ≠ 0) (halpha : 0 < alpha) {phi : ℝ}
    (hphi : phi ≠ 0) : 0 < starobinskyV M alpha phi := by
  have hs : 0 < Real.sqrt (2 / 3) := Real.sqrt_pos.mpr (by norm_num)
  have harg : -(Real.sqrt (2 / 3)) * phi / M ≠ 0 := by
    have hne0 : (-(Real.sqrt (2 / 3)) * phi) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hs)) hphi
    exact div_ne_zero hne0 hM
  have hne : Real.exp (-(Real.sqrt (2 / 3)) * phi / M) ≠ 1 := by
    intro h
    exact harg ((Real.exp_eq_one_iff _).mp h)
  have hK : 0 < M ^ 4 / (16 * alpha) := by
    have : 0 < M ^ 4 := by positivity
    positivity
  have hsq : 0 < (1 - Real.exp (-(Real.sqrt (2 / 3)) * phi / M)) ^ 2 := by
    have : (1 - Real.exp (-(Real.sqrt (2 / 3)) * phi / M)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    positivity
  simpa [starobinskyV] using mul_pos hK hsq

/-- **The full exponential scalaron potential is not a polynomial of degree `≤ 2`.**

There are no reals `a, b, c` with `V(φ) = aφ² + bφ + c` for every `φ`.  In particular the
scalaron sector cannot be written as a quadratic form in the field-space coordinates, and the
gravity Hamiltonian that carries it is not a kinetic-plus-squares operator. -/
theorem starobinskyV_not_quadratic {M alpha : ℝ} (hM : 0 < M) (halpha : 0 < alpha) :
    ¬ ∃ a b c : ℝ, ∀ phi : ℝ, starobinskyV M alpha phi = a * phi ^ 2 + b * phi + c := by
  rintro ⟨a, b, c, h⟩
  have hKpos : 0 < M ^ 4 / (16 * alpha) := by positivity
  -- the constant term vanishes, because `V(0) = 0`
  have hc : c = 0 := by
    have h0 := h 0
    rw [starobinskyV_zero] at h0
    linarith [h0]
  subst hc
  -- non-negativity of the wall, transported to the polynomial
  have hnn : ∀ t : ℝ, 0 ≤ a * t ^ 2 + b * t + 0 := by
    intro t
    rw [← h t]
    exact starobinskyV_nonneg halpha t
  -- boundedness on the plateau side, transported to the polynomial
  have hbd : ∀ t : ℝ, 0 ≤ t → a * t ^ 2 + b * t + 0 ≤ M ^ 4 / (16 * alpha) := by
    intro t ht
    rw [← h t]
    exact starobinskyV_le_plateau hM halpha ht
  have hbabs : -|b| ≤ b := neg_abs_le b
  have hbabs' : b ≤ |b| := le_abs_self b
  have habs : (0 : ℝ) ≤ |b| := abs_nonneg b
  -- the leading coefficient is non-positive, by boundedness on `[0, ∞)`
  have ha_le : a ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    set t : ℝ := max 1 ((M ^ 4 / (16 * alpha) + |b| + 1) / a) with ht
    have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
    have ht2 : (M ^ 4 / (16 * alpha) + |b| + 1) / a ≤ t := le_max_right _ _
    have hat : M ^ 4 / (16 * alpha) + |b| + 1 ≤ a * t := by
      rw [div_le_iff₀ hpos] at ht2
      linarith [ht2]
    have hle := hbd t (by linarith)
    nlinarith
  -- and non-negative, by non-negativity on `(−∞, 0]`
  have ha_ge : 0 ≤ a := by
    by_contra hneg
    push_neg at hneg
    set t : ℝ := max 1 ((|b| + 1) / (-a)) with ht
    have hna : 0 < -a := by linarith
    have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
    have ht2 : (|b| + 1) / (-a) ≤ t := le_max_right _ _
    have hat : |b| + 1 ≤ (-a) * t := by
      rw [div_le_iff₀ hna] at ht2
      linarith [ht2]
    have hge := hnn t
    nlinarith
  have ha : a = 0 := le_antisymm ha_le ha_ge
  subst ha
  -- the linear coefficient vanishes too, by non-negativity on both half-lines
  have hb1 := hnn 1
  have hb2 := hnn (-1)
  have hb : b = 0 := by nlinarith
  subst hb
  -- so the wall would be identically zero, which it is not
  have hpos := starobinskyV_pos (ne_of_gt hM) halpha (phi := 1) one_ne_zero
  rw [h 1] at hpos
  norm_num at hpos

/-- The **scalaron fibre potential** `φ²/4 + V(φ) + s` of the Faris–Lavine mode model is not a
polynomial of degree `≤ 2` either: adding the oscillator term and the mode energy cannot
repair the exponential. -/
theorem starobinskyPot_not_quadratic {M alpha : ℝ} (hM : 0 < M) (halpha : 0 < alpha) (s : ℝ) :
    ¬ ∃ a b c : ℝ, ∀ phi : ℝ,
      (starobinskyWall M alpha halpha).pot s phi = a * phi ^ 2 + b * phi + c := by
  rintro ⟨a, b, c, h⟩
  refine starobinskyV_not_quadratic hM halpha ⟨a - 1 / 4, b, c - s, fun phi => ?_⟩
  have hp := h phi
  simp only [WallPot.pot, starobinskyWall] at hp
  linarith [hp]

/-- **The scalaron fibre potential is not a half-sum of squares of linear forms.**

A kinetic-plus-squares operator `½ Σ_j κ_j π_j² + ½ Σ_r L_r²` has, on each fibre, a potential
that is a half-sum of squares of *linear* forms in the coordinates.  The scalaron fibre
potential of the gravity Hamiltonian is not of that form, for any finite family of linear
forms — this is the precise obstruction that rules the kinetic-plus-squares identification
out once the full exponential potential is kept. -/
theorem starobinskyPot_not_sum_of_squares {M alpha : ℝ} (hM : 0 < M) (halpha : 0 < alpha)
    (s : ℝ) {R : Type} [Fintype R] (cf : R → ℝ) :
    ¬ ∀ phi : ℝ,
      (starobinskyWall M alpha halpha).pot s phi = 1 / 2 * ∑ r : R, (cf r * phi) ^ 2 := by
  intro h
  refine starobinskyPot_not_quadratic hM halpha s
    ⟨1 / 2 * ∑ r : R, cf r ^ 2, 0, 0, fun phi => ?_⟩
  have hsum : ∑ r : R, (cf r * phi) ^ 2 = (∑ r : R, cf r ^ 2) * phi ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [h phi, hsum]
  ring

end BookProof.ScalaronNotQuadratic
