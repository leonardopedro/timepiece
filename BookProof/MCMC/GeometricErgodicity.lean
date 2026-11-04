import Mathlib

/-!
# Chapter GeometricErgodicity — MCMC convergence from an operator spectral gap

Plan: `pcnl.md`, Modules 4–5.  The plan's thesis is that pCNL (pCN with a Langevin drift) is a
*linear* operator on `L²(π)`, so its geometric ergodicity is a corollary of a spectral gap
rather than a trajectory-tracking argument:

`‖P ^ m u − Π u‖ ≤ (1 − γ) ^ m ‖u − Π u‖`,  `P = P₀ + K_drift + K_reject`,

where `Π` is the rank-one projection onto the invariant state.  This chapter proves that
implication for a *bounded self-adjoint contraction*: the discrete-time (MCMC iterate) twin of
`BookProof.ChapterSirkDiffusiveDecay`'s continuous-time result
`‖e^{−tA} v‖ ≤ e^{−μt} ‖v‖` for a coercive generator.

The hypotheses are the ones the plan's Modules 1–3 supply: `P` is self-adjoint (the plan's
symmetrisation `ψ = √π f` makes the kernel self-adjoint), it fixes the invariant state `φ`
(`P φ = φ`, `‖φ‖ = 1`), and it contracts by `1 − γ` on the orthogonal complement of `φ` — the
gap of the unadjusted proposal being `1 − ρ` in the lowest Gegenbauer/Hermite mode.

## Contents

* `iterate_orthogonal_of_fixed` — a self-adjoint operator fixing `φ` maps the orthogonal
  complement of `φ` into itself;
* `norm_iterate_le_of_orthogonal` — **the gap propagates to every iterate**:
  `‖P^m w‖ ≤ (1 − γ)^m ‖w‖` for `w ⟂ φ`;
* **`norm_iterate_sub_invariant_le`** — **geometric ergodicity in `L²`**: for every `ψ`,
  `‖P^m ψ − ⟪φ, ψ⟫ φ‖ ≤ (1 − γ)^m ‖ψ − ⟪φ, ψ⟫ φ‖`;
* `tendsto_iterate` — hence `P^m ψ → ⟪φ, ψ⟫ φ`, i.e. the MCMC chain converges to its
  invariant state at a geometric rate.

## Boundary

Two inputs are hypotheses here, matching the plan's Modules 1–3:

* the self-adjointness and the gap of the *full* pCNL operator — for the unadjusted pCN step
  `P₀` the gap is `1 − ρ`, and the plan's Modules 1–2 supply the Gegenbauer/Hermite
  diagonalisation that certifies it; the perturbation `K_drift + K_reject` must be shown to
  preserve it (Module 3's finite-band hopping plus a relative bound), which is analytic input
  about the target potential, not bookkeeping;
* the passage from the `L²` bound proved here to a total-variation bound,
  `‖ν − π‖_TV ≤ ½‖dν/dπ − 1‖_{L²}`, which is the Cauchy–Schwarz/Born bound on densities and
  is not proved in this file.

Nothing in this file assumes a numerical mixing rate: `γ` is an operator gap, and the bound is
exact in `m`.
-/

noncomputable section

namespace BookProof.MCMC

open scoped InnerProductSpace
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## 1. The orthogonal complement of the invariant state -/

/-- **A self-adjoint operator fixing `φ` preserves the orthogonal complement of `φ`.** -/
theorem inner_fixed_apply_eq_zero {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) {φ w : E}
    (hfix : P φ = φ) (hw : (inner ℂ φ w : ℂ) = 0) : (inner ℂ φ (P w) : ℂ) = 0 := by
  have h1 : (inner ℂ (P w) φ : ℂ) = (inner ℂ w φ : ℂ) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hP.adjoint_eq, hfix]
  calc (inner ℂ φ (P w) : ℂ) = starRingEnd ℂ (inner ℂ (P w) φ : ℂ) := (inner_conj_symm _ _).symm
    _ = starRingEnd ℂ (inner ℂ w φ : ℂ) := by rw [h1]
    _ = (inner ℂ φ w : ℂ) := inner_conj_symm _ _
    _ = 0 := hw

omit [CompleteSpace E] in
/-- The invariant state is fixed by every iterate. -/
theorem iterate_fixed {P : E →L[ℂ] E} {φ : E} (hfix : P φ = φ) (m : ℕ) : (P ^ m) φ = φ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, hfix]

/-- All iterates stay orthogonal to `φ` on the orthogonal complement. -/
theorem iterate_orthogonal {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) {φ : E} (hfix : P φ = φ)
    {w : E} (hw : (inner ℂ φ w : ℂ) = 0) (m : ℕ) : (inner ℂ φ ((P ^ m) w) : ℂ) = 0 := by
  induction m with
  | zero => simpa using hw
  | succ m ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact inner_fixed_apply_eq_zero hP hfix ih

/-! ## 2. The gap propagates to every iterate -/

/-- **Geometric decay on the orthogonal complement of the invariant state.**  If `P` contracts
by `1 − γ` on `φᗮ`, then its `m`-th power contracts by `(1 − γ)^m` there. -/
theorem norm_iterate_le_of_orthogonal {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) {φ : E}
    (hfix : P φ = φ) {γ : ℝ} (hγ1 : γ ≤ 1)
    (hgap : ∀ w : E, (inner ℂ φ w : ℂ) = 0 → ‖P w‖ ≤ (1 - γ) * ‖w‖) :
    ∀ (m : ℕ) (w : E), (inner ℂ φ w : ℂ) = 0 → ‖(P ^ m) w‖ ≤ (1 - γ) ^ m * ‖w‖ := by
  intro m
  induction m with
  | zero => intro w _; simp
  | succ m ih =>
    intro w hw
    have horth := iterate_orthogonal hP hfix hw m
    have h1 : ‖P ((P ^ m) w)‖ ≤ (1 - γ) * ‖(P ^ m) w‖ := hgap _ horth
    have h2 := ih w hw
    have hstep : ‖(P ^ (m + 1)) w‖ = ‖P ((P ^ m) w)‖ := by
      rw [pow_succ', ContinuousLinearMap.mul_apply]
    rw [hstep]
    calc ‖P ((P ^ m) w)‖ ≤ (1 - γ) * ‖(P ^ m) w‖ := h1
      _ ≤ (1 - γ) * ((1 - γ) ^ m * ‖w‖) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = (1 - γ) ^ (m + 1) * ‖w‖ := by rw [pow_succ]; ring

/-! ## 3. Geometric ergodicity -/

/-- **Geometric ergodicity in `L²`.**  For a self-adjoint contraction `P` fixing the unit state
`φ` and contracting by `1 − γ` on `φᗮ`, every vector converges geometrically to its projection
onto `φ`, with the rate `(1 − γ)`:

`‖P^m ψ − ⟪φ, ψ⟫ φ‖ ≤ (1 − γ)^m ‖ψ − ⟪φ, ψ⟫ φ‖`.

`ψ` is the square root of an initial density, `φ` that of the invariant density `π`, and `P` the
pCNL transition operator. -/
theorem norm_iterate_sub_invariant_le {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) {φ : E}
    (hφ : ‖φ‖ = 1) (hfix : P φ = φ) {γ : ℝ} (hγ1 : γ ≤ 1)
    (hgap : ∀ w : E, (inner ℂ φ w : ℂ) = 0 → ‖P w‖ ≤ (1 - γ) * ‖w‖) (m : ℕ) (ψ : E) :
    ‖(P ^ m) ψ - (inner ℂ φ ψ : ℂ) • φ‖ ≤
      (1 - γ) ^ m * ‖ψ - (inner ℂ φ ψ : ℂ) • φ‖ := by
  set c : ℂ := inner ℂ φ ψ with hc
  set w : E := ψ - c • φ with hwdef
  have horth : (inner ℂ φ w : ℂ) = 0 := by
    rw [hwdef, inner_sub_right, inner_smul_right, hc]
    have hφφ : (inner ℂ φ φ : ℂ) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hφ]
      norm_num
    rw [hφφ, mul_one, sub_self]
  have hsplit : ψ = c • φ + w := by
    rw [hwdef]; abel
  have hiter : (P ^ m) ψ = c • φ + (P ^ m) w := by
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul, iterate_fixed hfix]
  have hgoal : c • φ + (P ^ m) w - c • φ = (P ^ m) w := by abel
  have hmain := norm_iterate_le_of_orthogonal hP hfix hγ1 hgap m w horth
  rw [hiter, hgoal]
  exact hmain

/-- **The MCMC chain converges to its invariant state.**  The `L²` bound of
`norm_iterate_sub_invariant_le` makes the iterates tend to the projection of the initial state
onto the invariant state at a geometric rate. -/
theorem tendsto_iterate {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) {φ : E} (hφ : ‖φ‖ = 1)
    (hfix : P φ = φ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hgap : ∀ w : E, (inner ℂ φ w : ℂ) = 0 → ‖P w‖ ≤ (1 - γ) * ‖w‖) (ψ : E) :
    Tendsto (fun m : ℕ => (P ^ m) ψ) atTop (𝓝 ((inner ℂ φ ψ : ℂ) • φ)) := by
  have hγle : γ ≤ 1 := hγ1
  have hbound : ∀ m : ℕ, ‖(P ^ m) ψ - (inner ℂ φ ψ : ℂ) • φ‖ ≤
      (1 - γ) ^ m * ‖ψ - (inner ℂ φ ψ : ℂ) • φ‖ :=
    fun m => norm_iterate_sub_invariant_le hP hφ hfix hγle hgap m ψ
  have hr : Tendsto (fun m : ℕ => (1 - γ) ^ m) atTop (𝓝 0) := by
    have hlt : |1 - γ| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    simpa using tendsto_pow_atTop_nhds_zero_of_abs_lt_one hlt
  have htozero : Tendsto (fun m : ℕ =>
      (P ^ m) ψ - (inner ℂ φ ψ : ℂ) • φ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) hbound ?_
    simpa using hr.mul_const ‖ψ - (inner ℂ φ ψ : ℂ) • φ‖
  have hconst : Tendsto (fun _ : ℕ => (inner ℂ φ ψ : ℂ) • φ) atTop
      (𝓝 ((inner ℂ φ ψ : ℂ) • φ)) := tendsto_const_nhds
  have := htozero.add hconst
  simpa using this

end BookProof.MCMC
