import Mathlib
import BookProof.BalabanRG.MultiscaleSpace
import BookProof.BalabanRG.BlockOperator

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

/-! ## The increment estimate for the *concrete* `Q_k` (open item 5 of the plan)

`balaban_rg_convergence` consumes `hdecay : ∀ N, ‖Ψ_{N+1} − Ψ_N‖ ≤ C · r^N`.  The plan asks for
that estimate for the block averaging of `BlockOperator.lean`, and it can be supplied — but for
a reason worth stating plainly, because it is a fact about the *model* and not a proof of
Balaban's polymer bound.

The modelled `Q_k` is `blockConst.starProjection` at every scale: the same orthogonal
projection, hence idempotent (`blockAveraging_idempotent`).  The recursion `Ψ_{N+1} = Q_N Ψ_N`
therefore acts *componentwise at each scale* as `(Q_k)^N`, which is `Q_k` for every `N ≥ 1`.
So `Ψ_N` is constant from `N = 1` on: the whole increment is the single first step, and the
geometric bound holds with `C = ‖ψ₀ − Q ψ₀‖` and any `r < 1` — the terms with `N ≥ 1` being
zero.  Convergence of `Ψ_N` is consequently unconditional in this model.

**What this does and does not say.**  It closes the *bookkeeping* half of the item: the
hypothesis `balaban_rg_convergence` consumes is satisfiable by the concrete `Q_k`, with explicit
constants, so the limit `Ψ_∞` exists as a theorem about `FTotal` rather than as an assumption.
It does **not** prove Balaban's estimate: in Balaban's construction the coarse-graining loses
information at each step (the block lattice genuinely has fewer degrees of freedom than the fine
one), so `Q_k` is *not* idempotent and the increments decay geometrically for analytic reasons —
the polymer bound.  In `MultiscaleSpace` every sector carries the same carrier
`EuclideanSpace ℝ (Fin latticeDim)` by design (see its module docstring), which is exactly what
makes `Q_k` a projection.  The genuinely geometric content of Phase 2.3 therefore remains the
input named in the boundary below; what is added here is that for the operator the corpus
actually defines, the input degenerates to a single-step estimate and nothing more is needed.
-/

variable (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))

/-- With idempotent `Q_k`, the `n`-th iterate at any scale `k` is the single application `Q_k`:
`Ψ_{n+1} k = Q_k (ψ₀ k)` for every `n`. -/
theorem psiSeq_component_eq (hQ : ∀ k, ‖Q k‖ ≤ 1)
    (hQid : ∀ k (x : Sector k), Q k (Q k x) = Q k x) (ψ0 : FTotal) (n k : ℕ) :
    psiSeq Q hQ ψ0 (n + 1) k = Q k (ψ0 k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [psiSeq_succ, rgOnTotal_apply_apply, ih, hQid]

/-- **Idempotence makes the RG iteration stabilise after one step**: `Ψ_{N+2} = Ψ_{N+1}` for
every `N`. -/
theorem psiSeq_succ_eq_of_idempotent (hQ : ∀ k, ‖Q k‖ ≤ 1)
    (hQid : ∀ k (x : Sector k), Q k (Q k x) = Q k x) (ψ0 : FTotal) (n : ℕ) :
    psiSeq Q hQ ψ0 (n + 2) = psiSeq Q hQ ψ0 (n + 1) :=
  FTotal.ext fun k =>
    (psiSeq_component_eq Q hQ hQid ψ0 (n + 1) k).trans (psiSeq_component_eq Q hQ hQid ψ0 n k).symm

/-- **The increment estimate `balaban_rg_convergence` consumes**, for idempotent `Q_k`: every
increment is bounded by `‖ψ₀ − Q ψ₀‖ · r^N`, with the `N = 0` term the whole of it and all the
rest zero. -/
theorem psiSeq_increment_bound_of_idempotent (hQ : ∀ k, ‖Q k‖ ≤ 1)
    (hQid : ∀ k (x : Sector k), Q k (Q k x) = Q k x) (ψ0 : FTotal) {r : ℝ} (hr : 0 ≤ r) :
    ∀ N : ℕ, ‖psiSeq Q hQ ψ0 (N + 1) - psiSeq Q hQ ψ0 N‖
      ≤ ‖ψ0 - rgOnTotal Q hQ ψ0‖ * r ^ N := by
  intro N
  cases N with
  | zero =>
      have h1 : psiSeq Q hQ ψ0 1 = rgOnTotal Q hQ ψ0 := rfl
      simp only [psiSeq_zero, pow_zero, mul_one, h1]
      rw [norm_sub_rev]
  | succ N =>
      rw [psiSeq_succ_eq_of_idempotent Q hQ hQid ψ0 N, sub_self, norm_zero]
      exact mul_nonneg (norm_nonneg _) (pow_nonneg hr _)

/-- **Balaban's RG convergence for the concrete block-averaging `Q_k`** (plan Phase 2.3,
open item 5): the increment hypothesis is satisfied by `blockAveraging`, with
`C = ‖ψ₀ − Q ψ₀‖` and `r = 1/2`, so the sequence of effective actions converges in `FTotal`. -/
theorem balaban_rg_convergence_blockAveraging (ψ0 : FTotal) :
    ∃ psiLim : FTotal,
      Tendsto (psiSeq blockAveraging blockAveraging_norm_le ψ0) atTop (𝓝 psiLim) :=
  balaban_rg_convergence blockAveraging blockAveraging_norm_le ψ0
    ‖ψ0 - rgOnTotal blockAveraging blockAveraging_norm_le ψ0‖ (1 / 2 : ℝ)
    (norm_nonneg _) (by norm_num) (by norm_num)
    (psiSeq_increment_bound_of_idempotent blockAveraging blockAveraging_norm_le
      blockAveraging_idempotent ψ0 (by norm_num))

end

end BookProof.BalabanRG
