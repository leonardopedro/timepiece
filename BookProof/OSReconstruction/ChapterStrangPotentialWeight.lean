import Mathlib

/-!
# Chapter StrangPotentialWeight — H3's finite-slice potential weight

`cftproof.md` H3 defines the finite-slice path measure with the Strang-symmetrized potential
weight `exp(−ε/2 V(q₀) − ε Σ_{j=1}^{N−1} V(qⱼ) − ε/2 V(q_N))`.  This module gives the exact
algebraic form of that weight on a slice-indexed configuration path and proves its elementary
properties: positivity and the factorization into endpoint half-steps and the interior product.
These are the identities the finite-slice measure consumes.

No continuum limit, interacting estimate, reflection positivity or cutoff removal is proved
here.  Axioms are `propext`, `Classical.choice`, `Quot.sound` only.
-/

noncomputable section

namespace BookProof.StrangPotentialWeight

/-- The Strang-symmetric potential weight on `N + 1` slices `q 0, …, q N`. -/
def strangWeight (ε : ℝ) (V : ℝ → ℝ) (N : ℕ) (q : ℕ → ℝ) : ℝ :=
  Real.exp (-(ε / 2 * V (q 0) + (Finset.Icc 1 (N - 1)).sum (fun j => ε * V (q j)) +
    ε / 2 * V (q N)))

/-- The weight is strictly positive at every configuration. -/
theorem strangWeight_pos (ε : ℝ) (V : ℝ → ℝ) (N : ℕ) (q : ℕ → ℝ) :
    0 < strangWeight ε V N q := by
  dsimp [strangWeight]
  exact Real.exp_pos _

/-- The weight factorizes into the endpoint half-steps and the interior product. -/
theorem strangWeight_factor (ε : ℝ) (V : ℝ → ℝ) (N : ℕ) (q : ℕ → ℝ) :
    strangWeight ε V N q =
      Real.exp (-(ε / 2 * V (q 0))) *
        (Finset.Icc 1 (N - 1)).prod (fun j => Real.exp (-(ε * V (q j)))) *
          Real.exp (-(ε / 2 * V (q N))) := by
  dsimp [strangWeight]
  rw [← Real.exp_sum (Finset.Icc 1 (N - 1)) (fun j => -(ε * V (q j)))]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Finset.sum_neg_distrib]
  ring_nf

/-- For one Euclidean step the two endpoint half-weights combine into the full step. -/
theorem strangWeight_one (ε : ℝ) (V : ℝ → ℝ) (q : ℕ → ℝ) :
    strangWeight ε V 1 q = Real.exp (-(ε / 2 * (V (q 0) + V (q 1)))) := by
  dsimp [strangWeight]
  simp
  ring_nf

/-- For a constant potential the two endpoint half-steps and the `N−1` interior steps add up
    to the full time `ε·N`: the Strang weight is `exp(−(ε·N·c))`, with no double counting. -/
theorem strangWeight_const (ε c : ℝ) {N : ℕ} (hN : 0 < N) (q : ℕ → ℝ) :
    strangWeight ε (fun _ => c) N q = Real.exp (-(ε * N * c)) := by
  dsimp [strangWeight]
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  have hcard : N - 1 + 1 - 1 = N - 1 := by omega
  rw [hcard]
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hcast]
  ring_nf

end BookProof.StrangPotentialWeight
