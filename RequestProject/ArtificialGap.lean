import Mathlib

/-!
# Formal checks of the mathematical claims in `cft.md`

`cft.md` asks two questions (A: can Bałaban's renormalisation group plus the Timepiece certified
spectral pipeline prove the mass gap? B: what can the artificial gap `H + μN` be used for?) and
gives two answers.  This file machine-checks the operator-theoretic statements those answers rely
on, in the setting of **bounded** operators on a complex Hilbert space `E` (needed here for the
operator exponential). The SIRK/Temple part for unbounded `H`, via the bounded shift-invert
operator `(H - σ)⁻¹`, is in `RequestProject/Unbounded.lean`. The transfer operators `e^{-τH}`
for unbounded self-adjoint `H` bounded below are constructed in
`RequestProject/HeatSemigroup.lean`, and the results here are redone for unbounded operators in
`RequestProject/UnboundedPhysics.lean`.

Part A (Temple's inequality):
* `temple_lower_bound` — the Temple lower bound `θ - η²/(β - θ) ≤ λ₀`.
* `temple_bound_degenerates` — for fixed residual `η ≠ 0`, the bound tends to `-∞` as `β ↓ θ`.

Part B (the artificial gap `H_μ = H + μN`):
* `shifted_coercive`, `shifted_resolvent_bound` — coercivity and the `1/μ` resolvent bound
  on the vacuum-orthogonal subspace.
* `heisenberg_shift_invariant` — number-preserving observables have `μ`-independent dynamics.
  The version for unbounded `H` and `N` is `heisenberg_shift_invariant_unbounded` in
  `RequestProject/HeisenbergUnbounded.lean`.
* `transfer_contraction`, `shifted_transfer_contraction` — `‖e^{-aH_μ} x‖ ≤ e^{-aμ}‖x‖`
  for `x ⊥ Ω`, `a ≥ 0`.
* `number_preserving_fixes_vacuum`, `truncated_correlation_vanishes`,
  `shifted_transfer_fixes_vacuum` — if `Ω` spans `ker N`, every number-preserving observable maps
  `Ω` to a multiple of `Ω`, so all truncated correlations of such observables **in `Ω`** vanish
  identically.

In the nested Fock space, `Ω` is the *outer* vacuum. The physical inner vacuum lies in the
one-outer-quantum sector and can be excited by number-preserving observables; that case is
treated in `RequestProject/NestedFock.lean`.
-/

open scoped InnerProductSpace
open NormedSpace

noncomputable section

namespace CftCheck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `ℚ`-algebra structure on bounded operators (needed for `exp_add_of_commute`). -/
instance instNormedAlgebraRatCLM [CompleteSpace E] : NormedAlgebra ℚ (E →L[ℂ] E) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

/-! ## Part A: Temple's inequality -/

/-- **Temple's inequality.**  Suppose the spectrum of `H` avoids the open interval `(λ₀, β)`,
expressed through the quadratic-form inequality `Re ⟪(H - β)x, (H - λ₀)x⟫ ≥ 0` for all `x`
(for self-adjoint `H` this is exactly the operator inequality `(H - λ₀)(H - β) ≥ 0`).
For a unit trial vector `ψ` with Rayleigh quotient `θ = Re ⟪ψ, Hψ⟫ < β` and residual
`η = ‖Hψ - θψ‖`, we get `θ - η²/(β - θ) ≤ λ₀`. -/
theorem temple_lower_bound (H : E →L[ℂ] E) (l₀ β : ℝ)
    (hspec : ∀ x : E, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • x, H x - (l₀ : ℂ) • x⟫_ℂ)
    (ψ : E) (hψ : ‖ψ‖ = 1) (hθ : RCLike.re ⟪ψ, H ψ⟫_ℂ < β) :
    RCLike.re ⟪ψ, H ψ⟫_ℂ
      - ‖H ψ - ((RCLike.re ⟪ψ, H ψ⟫_ℂ : ℝ) : ℂ) • ψ‖ ^ 2 / (β - RCLike.re ⟪ψ, H ψ⟫_ℂ) ≤ l₀ := by
  set θ := RCLike.re ⟪ψ, H ψ⟫_ℂ with hθdef
  have hconj : RCLike.re ⟪H ψ, ψ⟫_ℂ = θ := by
    rw [hθdef, ← inner_conj_symm, RCLike.conj_re]
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K]; simp [hψ]
  have key : ∀ (a b : ℝ), RCLike.re ⟪H ψ - (a : ℂ) • ψ, H ψ - (b : ℂ) • ψ⟫_ℂ
      = ‖H ψ‖ ^ 2 - (a + b) * θ + a * b := by
    intro a b
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, map_sub, hψψ,
      inner_self_eq_norm_sq_to_K]
    simp only [RCLike.re_to_complex] at hconj hθdef ⊢
    simp [Complex.mul_re, hconj, ← hθdef, ← Complex.ofReal_pow]
    ring
  have hη : ‖H ψ - (θ : ℂ) • ψ‖ ^ 2 = ‖H ψ‖ ^ 2 - θ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), key]; ring
  have hs := hspec ψ
  rw [key] at hs
  rw [hη]
  have hpos : 0 < β - θ := by linarith
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hpos]
  nlinarith

/-- The Temple bound collapses when the separation input `β` approaches the Rayleigh
quotient `θ`: for any fixed nonzero residual `η` the certified lower bound `θ - η²/(β - θ)`
tends to `-∞` as `β ↓ θ`. -/
theorem temple_bound_degenerates (θ η : ℝ) (hη : η ≠ 0) :
    Filter.Tendsto (fun β : ℝ => θ - η ^ 2 / (β - θ)) (nhdsWithin θ (Set.Ioi θ)) Filter.atBot := by
  have h1 : Filter.Tendsto (fun β : ℝ => β - θ) (nhdsWithin θ (Set.Ioi θ))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    have hc : Filter.Tendsto (fun β : ℝ => β - θ) (nhdsWithin θ (Set.Ioi θ)) (nhds 0) := by
      have := ((continuous_id.sub continuous_const).tendsto' θ 0 (by simp) :
        Filter.Tendsto (fun β : ℝ => β - θ) (nhds θ) (nhds 0))
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with b hb
    simpa using hb
  have h2 := tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Filter.Tendsto (fun β : ℝ => η ^ 2 / (β - θ)) (nhdsWithin θ (Set.Ioi θ))
      Filter.atTop := by
    have := h2.const_mul_atTop (show 0 < η ^ 2 by positivity)
    simpa [div_eq_mul_inv] using this
  have := Filter.tendsto_atBot_add_const_left _ θ (Filter.tendsto_neg_atTop_atBot.comp h3)
  refine this.congr (fun b => ?_)
  simp [sub_eq_add_neg]

/-! ## Part B: the artificial mass gap `H + μN` -/

/-- Coercivity of the shifted Hamiltonian on the vacuum-orthogonal subspace: if `H ≥ 0` and
`N ≥ 1` on `Ω^⊥`, then `Re ⟪x, (H + μN)x⟫ ≥ μ‖x‖²` for `x ⊥ Ω`. -/
theorem shifted_coercive (H N : E →L[ℂ] E) (Ω : E) (μ : ℝ) (hμ : 0 ≤ μ)
    (hH : ∀ x, 0 ≤ RCLike.re ⟪x, H x⟫_ℂ)
    (hN : ∀ x, ⟪Ω, x⟫_ℂ = 0 → ‖x‖ ^ 2 ≤ RCLike.re ⟪x, N x⟫_ℂ)
    (x : E) (hx : ⟪Ω, x⟫_ℂ = 0) :
    μ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, (H + (μ : ℂ) • N) x⟫_ℂ := by
  have h1 : RCLike.re ⟪x, (H + (μ : ℂ) • N) x⟫_ℂ
      = RCLike.re ⟪x, H x⟫_ℂ + μ * RCLike.re ⟪x, N x⟫_ℂ := by
    simp
  rw [h1]; nlinarith [hH x, hN x hx]

/-- Resolvent-type bound: `‖(H + μN) x‖ ≥ μ‖x‖` on the vacuum-orthogonal subspace, i.e. the
inverse of `H + μN` restricted there has norm at most `1/μ`. -/
theorem shifted_resolvent_bound (H N : E →L[ℂ] E) (Ω : E) (μ : ℝ) (hμ : 0 ≤ μ)
    (hH : ∀ x, 0 ≤ RCLike.re ⟪x, H x⟫_ℂ)
    (hN : ∀ x, ⟪Ω, x⟫_ℂ = 0 → ‖x‖ ^ 2 ≤ RCLike.re ⟪x, N x⟫_ℂ)
    (x : E) (hx : ⟪Ω, x⟫_ℂ = 0) :
    μ * ‖x‖ ≤ ‖(H + (μ : ℂ) • N) x‖ := by
  have h := shifted_coercive H N Ω μ hμ hH hN x hx
  have hcs : RCLike.re ⟪x, (H + (μ : ℂ) • N) x⟫_ℂ ≤ ‖x‖ * ‖(H + (μ : ℂ) • N) x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · nlinarith

/-- Heisenberg dynamics of a number-preserving observable do not see the shift `μN`:
if `[H, N] = 0` and `[O, N] = 0` then
`e^{it(H+μN)} O e^{-it(H+μN)} = e^{itH} O e^{-itH}`. -/
theorem heisenberg_shift_invariant [CompleteSpace E] (H N O : E →L[ℂ] E) (μ t : ℝ)
    (hHN : Commute H N) (hON : Commute O N) :
    exp ((t * Complex.I : ℂ) • (H + (μ : ℂ) • N)) * O
        * exp (-((t * Complex.I : ℂ) • (H + (μ : ℂ) • N)))
      = exp ((t * Complex.I : ℂ) • H) * O * exp (-((t * Complex.I : ℂ) • H)) := by
  set X := (t * Complex.I : ℂ) • H
  set Y := (t * Complex.I : ℂ) • ((μ : ℂ) • N)
  have hXY : Commute X Y := ((hHN.smul_right _).smul_right _).smul_left _
  have hOY : Commute O Y := (hON.smul_right _).smul_right _
  have e1 : (t * Complex.I : ℂ) • (H + (μ : ℂ) • N) = X + Y := smul_add _ _ _
  rw [e1, exp_add_of_commute hXY, neg_add_rev,
    exp_add_of_commute (hXY.neg_left.neg_right.symm)]
  have hYY : exp Y * exp (-Y) = 1 := by
    rw [← exp_add_of_commute (Commute.neg_right (Commute.refl Y)), add_neg_cancel, exp_zero]
  calc exp X * exp Y * O * (exp (-Y) * exp (-X))
      = exp X * (O * exp Y) * (exp (-Y) * exp (-X)) := by
        rw [hOY.exp_right.eq]; noncomm_ring
    _ = exp X * O * (exp Y * exp (-Y)) * exp (-X) := by noncomm_ring
    _ = _ := by rw [hYY, mul_one]

/-- Strict contraction of the Euclidean transfer operator `e^{-aA}` (`a ≥ 0`) on the
vacuum-orthogonal subspace, for a self-adjoint `A` with `AΩ = 0` that is `μ`-coercive there. -/
theorem transfer_contraction [CompleteSpace E] (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (Ω : E) (hAΩ : A Ω = 0)
    (μ : ℝ) (hcoer : ∀ x, ⟪Ω, x⟫_ℂ = 0 → μ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, A x⟫_ℂ)
    (a : ℝ) (ha : 0 ≤ a) (x : E) (hx : ⟪Ω, x⟫_ℂ = 0) :
    ‖exp ((a : ℂ) • (-A)) x‖ ≤ Real.exp (-(a * μ)) * ‖x‖ := by
  set Y : ℝ → E := fun u => exp (u • (-A)) x with hYdef
  have hsymm : ∀ v w : E, ⟪A v, w⟫_ℂ = ⟪v, A w⟫_ℂ := fun v w => hA.isSymmetric v w
  have hY : ∀ u : ℝ, HasDerivAt Y (-(A (Y u))) u := by
    intro u
    let L : (E →L[ℂ] E) →L[ℝ] E := (ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ
    have h1 := L.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) u)
    have hc : Commute (exp (u • (-A))) (-A) := ((Commute.refl (-A)).smul_left u).exp_left
    have : L (exp (u • (-A)) * (-A)) = -(A (Y u)) := by
      simp only [L, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply]
      rw [hc.eq]; simp [hYdef]
    rw [this] at h1
    exact h1
  have horth : ∀ u, ⟪Ω, Y u⟫_ℂ = 0 := by
    have hd : ∀ u : ℝ, HasDerivAt (fun u => ⟪Ω, Y u⟫_ℂ) 0 u := by
      intro u
      have := (hasDerivAt_const u Ω).inner ℂ (hY u)
      have h0 : ⟪Ω, -(A (Y u))⟫_ℂ = 0 := by
        rw [inner_neg_right, ← hsymm, hAΩ, inner_zero_left, neg_zero]
      simpa [h0] using this
    intro u
    have := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
      (fun w => (hd w).deriv) u 0
    simpa [hYdef, hx] using this
  have hnorm : ∀ u, RCLike.re ⟪Y u, Y u⟫_ℂ = ‖Y u‖ ^ 2 := fun u => by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  set f : ℝ → ℝ := fun u => Real.exp (2 * μ * u) * RCLike.re ⟪Y u, Y u⟫_ℂ with hfdef
  have hf : ∀ u, HasDerivAt f (Real.exp (2 * μ * u) * (2 * μ * RCLike.re ⟪Y u, Y u⟫_ℂ
      - 2 * RCLike.re ⟪Y u, A (Y u)⟫_ℂ)) u := by
    intro u
    have hin := (hY u).inner ℂ (hY u)
    have hre := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt u hin
    have hexp := ((hasDerivAt_id u).const_mul (2 * μ)).exp
    have := hexp.mul hre
    convert this using 1
    · funext v; simp [hfdef]
    · simp only [Complex.reCLM_apply, inner_neg_left, inner_neg_right, hsymm, Function.comp_apply,
        id, map_add, map_neg, RCLike.re_to_complex]
      have hc : (⟪Y u, A (Y u)⟫_ℂ).re = (⟪A (Y u), Y u⟫_ℂ).re := by rw [hsymm]
      rw [hc]; ring
  have hanti : Antitone f := by
    refine antitone_of_hasDerivAt_nonpos hf (fun u => ?_)
    have h1 := hcoer (Y u) (horth u)
    show _ ≤ 0
    rw [hnorm]
    have : 2 * μ * ‖Y u‖ ^ 2 - 2 * RCLike.re ⟪Y u, A (Y u)⟫_ℂ ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this
  have hle := hanti ha
  have hY0 : Y 0 = x := by simp [hYdef]
  simp only [hfdef, hnorm, hY0, mul_zero, Real.exp_zero, one_mul] at hle
  have hYa : exp ((a : ℂ) • (-A)) x = Y a := by
    simp only [hYdef]; rw [← Complex.coe_smul]
  rw [hYa]
  have key : ‖Y a‖ ^ 2 ≤ (Real.exp (-(a * μ)) * ‖x‖) ^ 2 := by
    have he : Real.exp (-(a * μ)) ^ 2 * Real.exp (2 * μ * a) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp; ring_nf
    have hpos : 0 < Real.exp (2 * μ * a) := Real.exp_pos _
    rw [mul_pow]
    nlinarith [sq_nonneg (Real.exp (-(a * μ))), sq_nonneg ‖x‖, sq_nonneg ‖Y a‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp key

/-- The transfer operator of the shifted Hamiltonian contracts by `e^{-aμ}` off the vacuum:
`‖e^{-a(H+μN)} x‖ ≤ e^{-aμ}‖x‖` for `x ⊥ Ω` and `a ≥ 0`. -/
theorem shifted_transfer_contraction [CompleteSpace E] (H N : E →L[ℂ] E) (hHsa : IsSelfAdjoint H)
    (hNsa : IsSelfAdjoint N) (Ω : E) (hHΩ : H Ω = 0) (hNΩ : N Ω = 0) (μ : ℝ) (hμ : 0 ≤ μ)
    (hH : ∀ x, 0 ≤ RCLike.re ⟪x, H x⟫_ℂ)
    (hN : ∀ x, ⟪Ω, x⟫_ℂ = 0 → ‖x‖ ^ 2 ≤ RCLike.re ⟪x, N x⟫_ℂ)
    (a : ℝ) (ha : 0 ≤ a) (x : E) (hx : ⟪Ω, x⟫_ℂ = 0) :
    ‖exp ((a : ℂ) • (-(H + (μ : ℂ) • N))) x‖ ≤ Real.exp (-(a * μ)) * ‖x‖ := by
  have hsa : IsSelfAdjoint (H + (μ : ℂ) • N) := by
    refine hHsa.add ?_
    change star _ = _
    rw [star_smul, hNsa.star_eq, Complex.star_def, Complex.conj_ofReal]
  exact transfer_contraction _ hsa Ω (by simp [hHΩ, hNΩ]) μ
    (fun y hy => shifted_coercive H N Ω μ hμ hH hN y hy) a ha x hx

/-- A number-preserving observable maps the vacuum to a multiple of itself when the
vacuum spans the kernel of `N`. -/
theorem number_preserving_fixes_vacuum (N O : E →L[ℂ] E) (Ω : E) (hNΩ : N Ω = 0)
    (hker : ∀ x, N x = 0 → ∃ c : ℂ, x = c • Ω) (hON : Commute O N) :
    ∃ c : ℂ, O Ω = c • Ω := by
  apply hker
  have := congrArg (fun T : E →L[ℂ] E => T Ω) hON.eq
  simp [hNΩ] at this
  exact this.symm

/-- **Truncated correlations in the outer vacuum vanish.**  Assume `Ω` (normalised)
spans `ker N` (in the nested Fock space: `Ω` is the outer vacuum, not the inner vacuum).  For number-preserving observables `A, B` and any operator `U` fixing the vacuum
(e.g. the transfer operator `e^{-τ(H + μN)}`, see `shifted_transfer_fixes_vacuum`), the truncated
correlation `⟪Ω, A U B Ω⟫ - ⟪Ω, AΩ⟫⟪Ω, BΩ⟫` is identically zero — it does not merely decay
like `e^{-μτ}`. -/
theorem truncated_correlation_vanishes (N A B U : E →L[ℂ] E) (Ω : E) (hΩ : ‖Ω‖ = 1)
    (hNΩ : N Ω = 0) (hker : ∀ x, N x = 0 → ∃ c : ℂ, x = c • Ω)
    (hBN : Commute B N) (hU : U Ω = Ω) :
    ⟪Ω, A (U (B Ω))⟫_ℂ - ⟪Ω, A Ω⟫_ℂ * ⟪Ω, B Ω⟫_ℂ = 0 := by
  obtain ⟨c, hc⟩ := number_preserving_fixes_vacuum N B Ω hNΩ hker hBN
  have hΩΩ : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K]; simp [hΩ]
  rw [hc, map_smul, hU, map_smul, inner_smul_right, inner_smul_right, hΩΩ]
  ring

/-- If `BΩ = 0` then `e^{zB}Ω = Ω` for every `z`. -/
theorem exp_smul_apply_of_apply_eq_zero [CompleteSpace E] (B : E →L[ℂ] E) (v : E) (hv : B v = 0) (z : ℂ) :
    exp (z • B) v = v := by
  have hd : ∀ w : ℂ, HasDerivAt (fun u : ℂ => exp (u • B) v) 0 w := by
    intro w
    have := (hasDerivAt_exp_smul_const (𝕂 := ℂ) B w).clm_apply (hasDerivAt_const w v)
    simpa [hv] using this
  have := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0
  simpa using this

/-- The shifted transfer operator fixes the vacuum, so it is an admissible `U` in
`truncated_correlation_vanishes`. -/
theorem shifted_transfer_fixes_vacuum [CompleteSpace E] (H N : E →L[ℂ] E) (Ω : E) (hHΩ : H Ω = 0)
    (hNΩ : N Ω = 0) (μ τ : ℝ) :
    exp ((τ : ℂ) • (-(H + (μ : ℂ) • N))) Ω = Ω :=
  exp_smul_apply_of_apply_eq_zero _ _ (by simp [hHΩ, hNΩ]) _

end CftCheck
