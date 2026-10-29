import Mathlib
import BookProof.BalabanRG.MultiscaleSpace

/-!
# Convergence of the effective actions `Ψ_N`

Plan: `cftproof.md`, Phase 2.3 — "Use Balaban's polymer bound `‖Ψ_{N+1} − Ψ_N‖ ≤ C L^{−εN}` …
Show `psiSeq_cauchy`, `psiSeq_has_limit`".

## Contents

* `summable_of_increment_bound` — a geometric bound on the increments makes the telescoping
  series summable (the estimate Phase 2.3 uses);
* `psiSeq_has_limit` — the limit exists, explicitly `Ψ_∞ = Ψ_0 + Σ_n (Ψ_{n+1} − Ψ_n)`;
* `psiSeq_cauchy` — consequently the sequence is Cauchy (redundant mathematically, but it is
  the shape the plan's Phase 2 estimate is stated in, and the shape Phase 3 consumes);
* `balaban_rg_convergence` — the assembled statement: the sequence of effective actions
  converges, with the plan's `C · r^N` decay as the hypothesis.

The analytic input (Balaban's polymer bound) is a *hypothesis*: it is a hard estimate about the
block-spin effective action, not a consequence of the bookkeeping proved in
`MultiscaleSpace`/`BlockOperator`.  What is proved is that the input is *sufficient* and that
the limit exists in the complete space `F_total`.

## Boundary

Phase 2.4 also claims a non-perturbative bound and renormalon cancellation with the explicit
constants of Balaban's papers; nothing of that is claimed here.  The `L^{−εN}` form of the
decay is carried as the abstract `r^N` with `r = L^{−ε} < 1` (the passage `r = L^{−ε}` is a
rewriting of the exponent, not a mathematical step).
-/

namespace BookProof.BalabanRG

open Filter
open scoped Topology BigOperators

noncomputable section

/-- A geometric bound on the increments of a sequence in a normed group makes the telescoping
series of increments summable. -/
theorem summable_of_increment_bound (u : ℕ → FTotal) (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (h : ∀ n : ℕ, ‖u (n + 1) - u n‖ ≤ C * r ^ n) :
    Summable fun n : ℕ => u (n + 1) - u n := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => C * r ^ n) ?_ ?_
  · exact (summable_geometric_of_lt_one hr0 hr1).mul_left C
  · intro n
    exact h n

/-- **The limit of the sequence of effective actions** (plan Phase 2.3 `psiSeq_has_limit`):
if the increments are summable, `Ψ_N` converges, with limit `Ψ_0 + Σ_n (Ψ_{n+1} − Ψ_n)`. -/
theorem psiSeq_has_limit (u : ℕ → FTotal)
    (h : Summable fun n : ℕ => u (n + 1) - u n) :
    ∃ uLim : FTotal, Tendsto u atTop (𝓝 uLim) := by
  refine ⟨u 0 + tsum (fun n : ℕ => u (n + 1) - u n), ?_⟩
  have htel : ∀ N : ℕ,
      u N = u 0 + Finset.sum (Finset.range N) (fun n : ℕ => u (n + 1) - u n) := by
    intro N
    rw [Finset.sum_range_sub (fun n : ℕ => u n) N]
    abel
  have hsum : Tendsto
      (fun N : ℕ => Finset.sum (Finset.range N) (fun n : ℕ => u (n + 1) - u n)) atTop
      (𝓝 (tsum fun n : ℕ => u (n + 1) - u n)) := h.hasSum.tendsto_sum_nat
  have hshift := hsum.const_add (u 0)
  have hfun : (fun N : ℕ =>
      u 0 + Finset.sum (Finset.range N) (fun n : ℕ => u (n + 1) - u n)) = u := by
    funext N
    exact (htel N).symm
  rwa [hfun] at hshift

/-- Weaker form: the sequence is Cauchy (plan Phase 2.3 `psiSeq_cauchy`). -/
theorem psiSeq_cauchy (u : ℕ → FTotal)
    (h : Summable fun n : ℕ => u (n + 1) - u n) : CauchySeq u := by
  obtain ⟨uLim, hu⟩ := psiSeq_has_limit u h
  exact hu.cauchySeq

/-- **Balaban's RG convergence** (plan Phase 2.3 `balaban_rg_convergence`): the effective
actions `Ψ_N = Q_{N−1} ⋯ Q_0 Ψ_0` converge whenever the increments obey the geometric
polymer bound. -/
theorem balaban_rg_convergence (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) (ψ0 : FTotal) (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ N : ℕ, ‖psiSeq Q hQ ψ0 (N + 1) - psiSeq Q hQ ψ0 N‖ ≤ C * r ^ N) :
    ∃ psiLim : FTotal, Tendsto (psiSeq Q hQ ψ0) atTop (𝓝 psiLim) :=
  psiSeq_has_limit _ (summable_of_increment_bound _ C r hC hr0 hr1 hdecay)

/-- The Cauchy form of the same statement. -/
theorem balaban_rg_cauchy (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) (ψ0 : FTotal) (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ N : ℕ, ‖psiSeq Q hQ ψ0 (N + 1) - psiSeq Q hQ ψ0 N‖ ≤ C * r ^ N) :
    CauchySeq (psiSeq Q hQ ψ0) :=
  psiSeq_cauchy _ (summable_of_increment_bound _ C r hC hr0 hr1 hdecay)

end

end BookProof.BalabanRG
