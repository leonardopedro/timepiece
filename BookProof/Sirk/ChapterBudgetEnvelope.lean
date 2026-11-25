import Mathlib

/-!
# Chapter BudgetEnvelope — the U2 non-growth and budget-direction arithmetic

`softmodes.md` U2 asks for an *explicit* non-growth guarantee: with a nondecreasing
rational order `q_m`, the envelope `B(g,L,q_m) = 2 Cbar Dbar e^{−a q_m} + T + S + O + F`
must satisfy `B(g,L,q_m) ≤ B(g,L,q_m₀)` for every admitted `m ≥ m₀`.  It also asks that
the real shift schedule `γ_j = N − s j > 0` be admissible at every step with `q < N/s`,
and warns that a *lower* bound on `Dmin` has the wrong direction for bounding a product in
which `Dmin` multiplies.  This module proves those three arithmetic statements.

Nothing here instantiates a coupling, an operator or a numerical solve.  The constants
`Cbar, Dbar, a > 0` and the allocations `T, S, O, F` are the U2 data; the scalar rational
error itself is `ChapterSirkEndToEnd.geomMarker_error_le`.  Axioms are `propext`,
`Classical.choice`, `Quot.sound` only.
-/

noncomputable section

namespace BookProof.BudgetEnvelope

/-! ## 1. The geometric term and its non-growth -/

/-- The rational term `2 Cbar Dbar e^{−a q}` of the U2 envelope. -/
def rationalBudget (Cbar Dbar a q : ℝ) : ℝ := 2 * Cbar * Dbar * Real.exp (-a * q)

/-- The full U2 envelope at order `q`; `T, S, O, F` depend on `(g, L)` but not on the
    retained Krylov dimension `m`. -/
def errorBudget (Cbar Dbar a T S O F q : ℝ) : ℝ :=
  rationalBudget Cbar Dbar a q + T + S + O + F

/-- The rational term is non-increasing in the order when `a > 0` and the prefactor is
    nonnegative.  This is the direction U2 needs: a larger admissible order cannot make
    the certified maximum error worse. -/
theorem rationalBudget_antitone {Cbar Dbar a : ℝ} (hC : 0 ≤ Cbar) (hD : 0 ≤ Dbar)
    (ha : 0 < a) : Antitone (rationalBudget Cbar Dbar a) := by
  intro q₁ q₂ hq
  have harg : -a * q₂ ≤ -a * q₁ := by nlinarith
  have hexp : Real.exp (-a * q₂) ≤ Real.exp (-a * q₁) := Real.exp_le_exp.mpr harg
  have hpref : 0 ≤ 2 * Cbar * Dbar := by positivity
  exact mul_le_mul_of_nonneg_left hexp hpref

/-- **U2's explicit non-growth guarantee.**  If the admitted orders `q_m` form a
    nondecreasing schedule, the whole envelope at `m ≥ m₀` is at most its value at `m₀`. -/
theorem errorBudget_nonGrowth {q : ℕ → ℝ} (hqmono : Monotone q)
    {Cbar Dbar a T S O F : ℝ} (hC : 0 ≤ Cbar) (hD : 0 ≤ Dbar) (ha : 0 < a)
    {m₀ m : ℕ} (hm : m₀ ≤ m) :
    errorBudget Cbar Dbar a T S O F (q m) ≤ errorBudget Cbar Dbar a T S O F (q m₀) := by
  have h := (rationalBudget_antitone hC hD ha) (hqmono hm)
  dsimp [errorBudget]
  linarith

/-- The power-form counterpart of `rationalBudget_antitone`, matching
    `ChapterSirkEndToEnd.geomMarker_rate` (`ρ^q = e^{−a q}` with `a = −log ρ`). -/
theorem powBudget_nonGrowth {ρ Cbar Dbar : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hC : 0 ≤ Cbar) (hD : 0 ≤ Dbar) {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) :
    2 * Cbar * Dbar * ρ ^ q₂ ≤ 2 * Cbar * Dbar * ρ ^ q₁ := by
  have hp := pow_le_pow_of_le_one hρ0 hρ1 hq
  have hpref : 0 ≤ 2 * Cbar * Dbar := by positivity
  exact mul_le_mul_of_nonneg_left hp hpref

/-! ## 2. Shift-schedule admissibility -/

/-- A rational order `q < N/s` keeps every earlier shift `γ_j = N − s j` positive. -/
theorem shift_positive_of_lt_div {N s : ℝ} (hs : 0 < s) {q : ℕ}
    (hq : (q : ℝ) < N / s) : ∀ j : ℕ, j < q → 0 < N - s * j := by
  intro j hj
  have hjreal : (j : ℝ) < N / s := lt_trans (by exact_mod_cast hj) hq
  have hmul : s * (j : ℝ) < N := by nlinarith [(lt_div_iff₀ hs).mp hjreal]
  nlinarith

/-- A fixed shift budget admits only finitely many rational orders: all of them are at
    most `⌈N/s⌉₊`. -/
theorem admitted_order_le_ceil {N s : ℝ} {q : ℕ} (hq : (q : ℝ) < N / s) :
    q ≤ Nat.ceil (N / s) := by
  have hceil : N / s ≤ (Nat.ceil (N / s) : ℝ) := Nat.le_ceil _
  exact Nat.le_of_lt (by exact_mod_cast (lt_of_lt_of_le hq hceil))

/-- Finiteness of the admitted-order set, in the form U2's "fixed budget" uses. -/
theorem finite_admitted_orders (N s : ℝ) :
    Set.Finite {q : ℕ | (q : ℝ) < N / s} := by
  refine (Set.finite_Iic (Nat.ceil (N / s))).subset ?_
  intro q hq
  exact admitted_order_le_ceil hq

/-! ## 3. The direction of the `Dmin` bound -/

/-- A lower bound `d₀ ≤ Dmin` does **not** bound `2 C Dmin r` from above: for any proposed
    upper bound `E` there is an admissible `Dmin` making the product exceed it.  This is
    U2's warning that the old `inf Dmin_m > 0` has the wrong direction for `sirkBound`, in
    which `Dmin` multiplies. -/
theorem dmin_lower_bound_does_not_control {C r d₀ E : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hd₀ : 0 < d₀) :
    ¬ (∀ D : ℝ, d₀ ≤ D → 2 * C * D * r ≤ E) := by
  intro h
  have hcoef : 0 < 2 * C * r := by positivity
  let D : ℝ := max (d₀ + 1) ((E + 1) / (2 * C * r))
  have hD₀ : d₀ ≤ D := by
    have hstep : d₀ ≤ d₀ + 1 := by linarith
    exact hstep.trans (le_max_left _ _)
  have hDpos : 0 < D := lt_of_lt_of_le hd₀ hD₀
  have _ : 0 < D := hDpos
  have hD₁ : (E + 1) / (2 * C * r) ≤ D := le_max_right _ _
  have hprod : E + 1 ≤ 2 * C * D * r := by
    have hmul := mul_le_mul_of_nonneg_left hD₁ (le_of_lt hcoef)
    have hcalc : (2 * C * r) * ((E + 1) / (2 * C * r)) = E + 1 := by
      field_simp [ne_of_gt hcoef]
    nlinarith
  have hle := h D hD₀
  linarith

end BookProof.BudgetEnvelope
