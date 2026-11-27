import Mathlib
import BookProof.MCMC.GaussianPCNGap

/-!
# Chapter GaussianProductGap — the product gap and the bounded-oscillation comparison

This is packet **S1** (second module) of `pcnl.md`'s active S0–S6 work order, executing
Q2/T3.  Two independent statements are collected here.

## §1. The product gap

For the *exact* product target `π_r ⊗ μ_n` with `Φ(z,w) = Φ_r(z)`, the posterior factors and the
simultaneous product kernel acts on product Hermite modes with eigenvalues
`a_i · ρ^{j}` (the `z`-block spectrum times the complement pCN modes).  The centred operator
norm is therefore the supremum of `|a_i ρ^j|` over `(i,j) ≠ (0,0)`.  Since the constant modes
have `a_0 = 1` and `ρ⁰ = 1`, this supremum is

`max (1 − γ_r) |ρ|  =  1 − min (γ_r) (1 − |ρ|)`,

which is **independent of the complement dimension `n`**.  `prod_eigen_le` proves the numerical
supremum, `product_eigenvalue_bound` instantiates the complement factors at the Gaussian pCN
modes `|ρ|^j` (using `abs_rho_pow_le` from `GaussianPCNGap`), and
`product_gap_eq_one_sub_min` rewrites the contraction as `1 − min(γ_r, 1 − |ρ|)`.

**B:** this is the spectrum/contraction arithmetic of the product factorisation, not a new
construction of the product Hilbert basis.  The concrete Gaussian product measure and its
Hermite basis are not rebuilt here; the `z`-block spectrum `a` is an explicit input, exactly
as the plan's `γ_r` is.

## §2. T3's bounded-oscillation comparison

With `osc Φ ≤ B`, the Gibbs density ratios obey `q(y)/q(x) ≤ e^B` (`gibbs_ratio_le_exp`).  The
Dirichlet and target-variance comparisons then transfer a prior Poincaré gap `g₀` to
`(q₋/q₊) g₀`, and the density bound turns the ratio into `e^{−B}` (`gap_comparison`,
`gap_comparison_exp`).  Lazifying doubles the absolute gap, giving `½ e^{−B} g₀`
(`lazy_absolute_gap_nonneg`, `lazy_absolute_gap_le_half`).  At the pCN value `g₀ = 1 − ρ` this
is T3's `½ e^{−B}(1 − ρ)`.

**C:** the two analytic comparisons (`E_MH ≥ q₋ E₀` and `Var_π ≤ q₊ Var_μ₀`) are taken as the
named hypotheses of `gap_comparison`, matching T3's proof chain; this module proves the
algebraic transfer and the density bound, not the two form/variance comparisons themselves.
-/

namespace BookProof.MCMC.GaussianProductGap

open Filter

/-! ## §1. The product gap -/

/-- **The product eigenvalue bound.**  If the constant `z`-mode is an eigenvalue `1`, the
non-constant `z`-modes contract by `1 − γ`, and the complement modes are bounded by `ρ ≤ 1`,
then every non-constant product mode contracts by at most `max (1 − γ) ρ`. -/
theorem prod_eigen_le {ι κ : Type*} [Zero ι] [Zero κ] {a : ι → ℝ} {b : κ → ℝ} {γ ρ : ℝ}
    (ha0 : a 0 = 1) (ha : ∀ i, i ≠ 0 → |a i| ≤ 1 - γ)
    (hb1 : ∀ j, |b j| ≤ 1) (hb : ∀ j, j ≠ 0 → |b j| ≤ ρ)
    (hγ1 : γ ≤ 1) {p : ι × κ} (hp : p ≠ (0, 0)) :
    |a p.1 * b p.2| ≤ max (1 - γ) ρ := by
  rw [abs_mul]
  rcases eq_or_ne p.1 0 with hi | hi
  · rcases eq_or_ne p.2 0 with hj | hj
    · exact absurd (Prod.ext hi hj) hp
    · rw [hi, ha0, abs_one, one_mul]
      exact le_trans (hb p.2 hj) (le_max_right _ _)
  · have h1 : |a p.1| ≤ 1 - γ := ha p.1 hi
    have h2 : |b p.2| ≤ 1 := hb1 p.2
    calc |a p.1| * |b p.2| ≤ (1 - γ) * 1 := by
          exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
      _ = 1 - γ := mul_one _
      _ ≤ max (1 - γ) ρ := le_max_left _ _

/-- **The Gaussian complement instance.**  For the pCN multiplier `ρ` with `ρ² + s² = 1` and
`s ≠ 0`, the complement modes `|ρ|^j` satisfy §1's hypotheses, so the product contraction is
`max (1 − γ) |ρ|` — independent of the complement dimension. -/
theorem product_eigenvalue_bound {ρ s γ : ℝ} (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {ι : Type*} [Zero ι] {a : ι → ℝ} (ha0 : a 0 = 1)
    (ha : ∀ i, i ≠ 0 → |a i| ≤ 1 - γ) (hγ1 : γ ≤ 1) {p : ι × ℕ}
    (hp : p ≠ (0, 0)) :
    |a p.1 * |ρ| ^ p.2| ≤ max (1 - γ) |ρ| := by
  refine prod_eigen_le ha0 ha ?_ ?_ hγ1 hp
  · intro j
    rw [abs_pow, abs_abs]
    exact pow_le_one₀ (abs_nonneg ρ) (abs_rho_lt_one hρs hs).le
  · intro j hj
    rw [abs_pow, abs_abs]
    exact abs_rho_pow_le hρs hs (Nat.one_le_iff_ne_zero.mpr hj)

/-- The product contraction rewrites as `1 − min(γ, 1 − |ρ|)`: the absolute gap is
`min(γ, 1 − |ρ|)`, the plan's complement-dimension-independent value. -/
theorem product_gap_eq_one_sub_min {γ ρ : ℝ} :
    max (1 - γ) |ρ| = 1 - min γ (1 - |ρ|) := by
  rcases le_total γ (1 - |ρ|) with h | h
  · rw [min_eq_left h]
    have hle : |ρ| ≤ 1 - γ := by linarith
    rw [max_eq_left hle]
  · rw [min_eq_right h]
    have hle : 1 - γ ≤ |ρ| := by linarith
    rw [max_eq_right hle]
    ring

/-! ## §2. The bounded-oscillation comparison -/

/-- **The Gibbs density ratio.**  If the potential oscillation is at most `B`, the density
ratio of two points is at most `e^B`. -/
theorem gibbs_ratio_le_exp {Φ : Ω → ℝ} {B : ℝ} (hosc : ∀ x y, Φ x - Φ y ≤ B)
    (x y : Ω) :
    Real.exp (-Φ y) / Real.exp (-Φ x) ≤ Real.exp B := by
  rw [← Real.exp_sub]
  refine Real.exp_le_exp.mpr ?_
  have := hosc x y
  linarith

/-- **The gap transfer.**  A Dirichlet comparison `q₋ E₀ ≤ Eπ` and a variance comparison
`Vπ ≤ q₊ V₀` transfer a prior gap `g₀ V₀ ≤ E₀` to `(q₋/q₊) g₀ Vπ ≤ Eπ`.  This is T3's
Poincaré comparison chain, with the two analytic comparisons named as hypotheses. -/
theorem gap_comparison {E0 Epi V0 Vpi qminus qplus g0 : ℝ} (hqm : 0 < qminus) (hqp : 0 < qplus)
    (hg0 : 0 ≤ g0) (hE : qminus * E0 ≤ Epi) (hV : Vpi ≤ qplus * V0)
    (hG : g0 * V0 ≤ E0) :
    (qminus / qplus * g0) * Vpi ≤ Epi := by
  have h1 : Vpi * (qminus / qplus) ≤ V0 * qminus := by
    have hq : 0 ≤ qminus / qplus := le_of_lt (div_pos hqm hqp)
    calc Vpi * (qminus / qplus) ≤ (qplus * V0) * (qminus / qplus) := by
          exact mul_le_mul_of_nonneg_right hV hq
      _ = V0 * qminus := by field_simp
  have h2 : (qminus / qplus * g0) * Vpi ≤ qminus * E0 := by
    calc (qminus / qplus * g0) * Vpi = g0 * (Vpi * (qminus / qplus)) := by ring
      _ ≤ g0 * (V0 * qminus) := by
          exact mul_le_mul_of_nonneg_left h1 hg0
      _ = qminus * (g0 * V0) := by ring
      _ ≤ qminus * E0 := by
          exact mul_le_mul_of_nonneg_left hG hqm.le
  exact le_trans h2 hE

/-- **T3 with `e^{−B}`.**  If the density ratio is at most `e^B`, the transferred gap is at
least `e^{−B} g₀`: `e^{−B} g₀ Vπ ≤ Eπ`. -/
theorem gap_comparison_exp {E0 Epi V0 Vpi qminus qplus g0 B : ℝ} (hqm : 0 < qminus)
    (hqp : 0 < qplus) (hg0 : 0 ≤ g0) (hVpi : 0 ≤ Vpi) (hE : qminus * E0 ≤ Epi)
    (hV : Vpi ≤ qplus * V0) (hG : g0 * V0 ≤ E0)
    (hratio : qplus ≤ qminus * Real.exp B) :
    (Real.exp (-B) * g0) * Vpi ≤ Epi := by
  have htransfer := gap_comparison hqm hqp hg0 hE hV hG
  have hratio' : qplus / qminus ≤ Real.exp B := by
    rw [div_le_iff₀ hqm]
    linarith
  have hcoef : Real.exp (-B) * g0 ≤ qminus / qplus * g0 := by
    refine mul_le_mul_of_nonneg_right ?_ hg0
    have hpos : 0 < qplus / qminus := div_pos hqp hqm
    have hexpB : 0 < Real.exp B := Real.exp_pos B
    have hinv : (Real.exp B)⁻¹ ≤ (qplus / qminus)⁻¹ :=
      (inv_le_inv₀ hexpB hpos).mpr hratio'
    rw [Real.exp_neg, inv_div] at *
    exact hinv
  calc (Real.exp (-B) * g0) * Vpi ≤ (qminus / qplus * g0) * Vpi := by
        exact mul_le_mul_of_nonneg_right hcoef hVpi
    _ ≤ Epi := htransfer

/-- The lazy absolute-gap constant `½ e^{−B} g₀` is nonnegative. -/
theorem lazy_absolute_gap_nonneg {B g0 : ℝ} (hg0 : 0 ≤ g0) :
    0 ≤ (1 / 2) * Real.exp (-B) * g0 := by positivity

/-- At the pCN prior gap `g₀ = 1 − ρ` the lazy constant is at most `½`. -/
theorem lazy_absolute_gap_le_half {B ρ : ℝ} (hB : 0 ≤ B) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (1 / 2) * Real.exp (-B) * (1 - ρ) ≤ 1 / 2 := by
  have hexp : Real.exp (-B) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hfac : 0 ≤ 1 - ρ := by linarith
  have hfirst : (1 / 2) * Real.exp (-B) ≤ 1 / 2 := by nlinarith
  calc (1 / 2) * Real.exp (-B) * (1 - ρ) ≤ (1 / 2) * (1 - ρ) := by
        exact mul_le_mul_of_nonneg_right hfirst hfac
    _ ≤ 1 / 2 := by nlinarith

/-- T3's stated constant: with `g₀ = 1 − ρ`, the lazy absolute gap is exactly
`½ e^{−B}(1 − ρ)`. -/
theorem lazy_absolute_gap_eq (B ρ : ℝ) :
    (1 / 2) * Real.exp (-B) * (1 - ρ) = Real.exp (-B) * ((1 - ρ) / 2) := by ring

end BookProof.MCMC.GaussianProductGap
