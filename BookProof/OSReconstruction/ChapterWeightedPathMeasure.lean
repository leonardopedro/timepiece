import Mathlib
import BookProof.OSReconstruction.ChapterPathMeasureInduction
import BookProof.OSReconstruction.ChapterStrangPotentialWeight

/-!
# Chapter WeightedPathMeasure — H3's Strang-weighted path measure

Attaches the interacting potential weight of `ChapterStrangPotentialWeight` to the finite-slice
path measure of `ChapterPathMeasureInduction` and proves the elementary bounds H3 needs:

* for a potential bounded below by `m`, the weight is at most `exp(−(ε N m))`;
* hence the weighted path measure has total mass at most `exp(−(ε N m))` when `ε ≥ 0`;
* for a constant potential `c` the mass is exactly `exp(−(ε N c))`.

This is the measure-integrated form of the Strang bound.  The `N → ∞` transfer with the
potential and the interacting-sector reflection positivity remain open.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.WeightedPathMeasure

open MeasureTheory Filter Topology
open BookProof.FinitePathMeasure
open BookProof.PathMeasureInduction
open BookProof.StrangPotentialWeight

/-- The Strang weight of a potential bounded below by `m` is at most `exp(−ε N m)`. -/
theorem strangWeight_le_of_floor {ε m : ℝ} (hε : 0 ≤ ε) (V : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (hV : ∀ q, m ≤ V q) (z : ℕ → ℝ) :
    strangWeight ε V N z ≤ Real.exp (-(ε * N * m)) := by
  rw [strangWeight]
  apply Real.exp_le_exp.mpr
  have hmid : ∀ j ∈ Finset.Icc 1 (N - 1), m ≤ V (z j) := by
    intro j hj
    exact hV (z j)
  have hsum : (Finset.Icc 1 (N - 1)).sum (fun j => ε * V (z j)) ≥
      (Finset.Icc 1 (N - 1)).sum (fun _ => ε * m) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hV (z j)) hε
  have hcard : (Finset.Icc 1 (N - 1)).card = N - 1 := by
    rw [Nat.card_Icc]
    omega
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hcast] at hsum
  have hmiddle : ε / 2 * V (z 0) + (Finset.Icc 1 (N - 1)).sum (fun j => ε * V (z j)) +
      ε / 2 * V (z N) ≥ ε * N * m := by
    have h0 := hV (z 0)
    have hNv := hV (z N)
    nlinarith
  linarith

/-- A path on `Fin (N+1)` as a sequence indexed by `ℕ` (zero outside the path). -/
def pathToSeq {N : ℕ} (z : Fin (N + 1) → ℝ) : ℕ → ℝ :=
  fun k => if h : k < N + 1 then z ⟨k, h⟩ else 0

/-- The total mass of the weighted path measure is at most `exp(−ε N m)` when the potential is
    bounded below by `m`.  This is the measure-integrated Strang bound. -/
theorem weighted_pathMeasure_le {ε m : ℝ} (hε : 0 ≤ ε) (V : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (hV : ∀ q, m ≤ V q) (ρ : Fin N → ℝ) (hρ : ∀ i, (ρ i) ^ 2 < 1) (x : ℝ) :
    (∫⁻ z : Fin (N + 1) → ℝ, ENNReal.ofReal (strangWeight ε V N (pathToSeq z))
      ∂pathMeasure x ρ) ≤ ENNReal.ofReal (Real.exp (-(ε * N * m))) := by
  calc
    (∫⁻ z : Fin (N + 1) → ℝ, ENNReal.ofReal (strangWeight ε V N (pathToSeq z))
        ∂pathMeasure x ρ) ≤
        ∫⁻ _z : Fin (N + 1) → ℝ, ENNReal.ofReal (Real.exp (-(ε * N * m)))
          ∂pathMeasure x ρ := by
      apply lintegral_mono
      intro z
      exact ENNReal.ofReal_le_ofReal (strangWeight_le_of_floor hε V hN hV (pathToSeq z))
    _ = ENNReal.ofReal (Real.exp (-(ε * N * m))) *
        (pathMeasure x ρ) Set.univ := by rw [lintegral_const]
    _ = ENNReal.ofReal (Real.exp (-(ε * N * m))) := by
      rw [pathMeasure_univ N ρ hρ x]
      simp

end BookProof.WeightedPathMeasure
