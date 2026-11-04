import RequestProject.ArtificialGap

/-!
# Claims A and B of `cft.md`, revisited for the nested Fock space

This file extends `RequestProject/ArtificialGap.lean`. Everything is about **bounded**
operators on a complex Hilbert space `E`. Unbounded versions of the claim-A theorems, and the
shift-invert form of the sector property, are in `RequestProject/Unbounded.lean`. The
semigroup statements below are redone for unbounded `H` and `N` in
`RequestProject/UnboundedPhysics.lean`.

## Claim A (Bałaban + Timepiece pipeline)

* `temple_enclosure`: with a uniform separation `β - θ ≥ c > 0` (Step 3 of answer A), the
  ground energy is enclosed in `[θ - η²/c, θ]`.
* `temple_enclosure_converges`: if the residuals go to `0` while the separation stays `≥ c`,
  the Rayleigh quotients converge to the ground energy (the "shrinking enclosure" of Step 3).
* `separation_input_is_gap`, `step3_hypothesis_implies_gap`: the separation hypothesis
  already implies that every eigenvalue above `l₀` lies at least `c` above it. So Step 3
  assumes the gap rather than deriving it.
* `second_quantized_edge`: the `dΓ` lift (Step 4) in its algebraic form — a sum of `n`
  one-particle terms, each `≥ μ`, is `≥ nμ`.

## Claim B (artificial gap `H + μN`) in the nested Fock space

The outer number operator `N` counts outer quanta. The physical (inner) Fock space sits inside
the one-outer-quantum sector `N = 1`, and the inner vacuum `ω` is a vector of that sector,
**not** the outer vacuum `Ω` (which spans `ker N`). Hence:

* `number_preserving_excites_inner_vacuum`: observables that commute with `N` **can** excite
  the inner vacuum `ω`, with nonzero truncated correlations. The earlier
  `truncated_correlation_vanishes` only concerns the outer vacuum `Ω`.
* `shifted_transfer_on_sector`, `shifted_correlation_factorizes`: on the sector `N = n` the
  shifted transfer operator is `e^{-τμn} e^{-τH}`. The whole effect of `μ` is a scalar factor.
* `shifted_normalized_correlation_invariant`: normalised correlations in any `N`-eigenstate
  (in particular in `ω`) do not depend on `μ`.
* `inner_vacuum_shifted_correlation`, `inner_vacuum_no_rate_mu_clustering`: if `ω` has an
  excitation of energy `e` inside its sector, then the normalised truncated correlation in `ω`
  equals `e^{-τe}‖φ‖²` for every `μ`. So for `μ > e` it is **not** `O(e^{-μτ})`.
* `toy_nested_model`: a concrete 3-dimensional nested model (outer vacuum, inner vacuum, one
  inner excitation) satisfies every hypothesis of the artificial-gap construction and
  realises all of the above. This shows the hypotheses are consistent.
-/

open scoped InnerProductSpace
open NormedSpace

noncomputable section

namespace CftCheck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Part A -/

/-- **Temple enclosure with a uniform separation input.**  If the spectrum avoids
`(l₀, β)`, `l₀` is a lower bound of `H` (the ground energy), and the trial state has
`β - θ ≥ c > 0`, then `θ - η²/c ≤ l₀ ≤ θ`. -/
theorem temple_enclosure (H : E →L[ℂ] E) (l₀ β c : ℝ) (hc : 0 < c)
    (hspec : ∀ x : E, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • x, H x - (l₀ : ℂ) • x⟫_ℂ)
    (hbot : ∀ x : E, l₀ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, H x⟫_ℂ)
    (ψ : E) (hψ : ‖ψ‖ = 1) (hsep : c ≤ β - RCLike.re ⟪ψ, H ψ⟫_ℂ) :
    RCLike.re ⟪ψ, H ψ⟫_ℂ - ‖H ψ - ((RCLike.re ⟪ψ, H ψ⟫_ℂ : ℝ) : ℂ) • ψ‖ ^ 2 / c ≤ l₀ ∧
      l₀ ≤ RCLike.re ⟪ψ, H ψ⟫_ℂ := by
  have hpos : 0 < β - RCLike.re ⟪ψ, H ψ⟫_ℂ := lt_of_lt_of_le hc hsep
  have ht := temple_lower_bound H l₀ β hspec ψ hψ (by linarith)
  refine ⟨le_trans ?_ ht, by simpa [hψ] using hbot ψ⟩
  gcongr

/-- **Shrinking enclosure (Step 3 of answer A).**  For trial states `ψ m` with a separation
`β - θ_m ≥ c > 0` that is uniform in `m` and residuals `η_m → 0`, the Rayleigh quotients `θ_m`
converge to the ground energy `l₀`. -/
theorem temple_enclosure_converges (H : E →L[ℂ] E) (l₀ β c : ℝ) (hc : 0 < c)
    (hspec : ∀ x : E, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • x, H x - (l₀ : ℂ) • x⟫_ℂ)
    (hbot : ∀ x : E, l₀ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, H x⟫_ℂ)
    (ψ : ℕ → E) (hψ : ∀ m, ‖ψ m‖ = 1) (hsep : ∀ m, c ≤ β - RCLike.re ⟪ψ m, H (ψ m)⟫_ℂ)
    (hres : Filter.Tendsto
      (fun m => ‖H (ψ m) - ((RCLike.re ⟪ψ m, H (ψ m)⟫_ℂ : ℝ) : ℂ) • ψ m‖) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => RCLike.re ⟪ψ m, H (ψ m)⟫_ℂ) Filter.atTop (nhds l₀) := by
  have hup : Filter.Tendsto
      (fun m => l₀ + ‖H (ψ m) - ((RCLike.re ⟪ψ m, H (ψ m)⟫_ℂ : ℝ) : ℂ) • ψ m‖ ^ 2 / c)
      Filter.atTop (nhds l₀) := by
    simpa using tendsto_const_nhds.add ((hres.pow 2).div_const c)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun m => ?_)
    (fun m => ?_)
  · exact (temple_enclosure H l₀ β c hc hspec hbot (ψ m) (hψ m) (hsep m)).2
  · have := (temple_enclosure H l₀ β c hc hspec hbot (ψ m) (hψ m) (hsep m)).1
    simp only
    linarith

/-- The separation hypothesis of Temple's inequality (the spectrum avoids `(l₀, β)`) forces every
eigenvalue `e > l₀` to satisfy `e ≥ β`. -/
theorem separation_input_is_gap (H : E →L[ℂ] E) (l₀ β : ℝ)
    (hspec : ∀ x : E, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • x, H x - (l₀ : ℂ) • x⟫_ℂ)
    (v : E) (hv : v ≠ 0) (e : ℝ) (hev : H v = (e : ℂ) • v) (he : l₀ < e) : β ≤ e := by
  have h := hspec v
  rw [hev, ← sub_smul, ← sub_smul, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K] at h
  have hn : 0 < ‖v‖ ^ 2 := by positivity
  have : RCLike.re ((starRingEnd ℂ) ((e : ℂ) - β) * (((e : ℂ) - l₀) * ((‖v‖ : ℂ) ^ 2)))
      = (e - β) * (e - l₀) * ‖v‖ ^ 2 := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.conj_ofReal, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]; ring
  have h2 : 0 ≤ (e - β) * (e - l₀) * ‖v‖ ^ 2 := by convert h using 1; exact this.symm
  by_contra hlt
  push Not at hlt
  have : (e - β) * (e - l₀) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
  nlinarith

/-- **Step 3 of answer A already contains the gap.**  If the separation input of Step 3 holds
(`β - θ ≥ c` for some trial state, with `β` the edge of the rest of the spectrum and `l₀` the
ground energy), then every eigenvalue above `l₀` lies at least `c` above it — before Temple's
inequality or any numerics is used. -/
theorem step3_hypothesis_implies_gap (H : E →L[ℂ] E) (l₀ β c : ℝ)
    (hspec : ∀ x : E, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • x, H x - (l₀ : ℂ) • x⟫_ℂ)
    (hbot : ∀ x : E, l₀ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, H x⟫_ℂ)
    (ψ : E) (hψ : ‖ψ‖ = 1) (hsep : c ≤ β - RCLike.re ⟪ψ, H ψ⟫_ℂ)
    (v : E) (hv : v ≠ 0) (e : ℝ) (hev : H v = (e : ℂ) • v) (he : l₀ < e) : c ≤ e - l₀ := by
  have h1 := separation_input_is_gap H l₀ β hspec v hv e hev he
  have h2 : l₀ ≤ RCLike.re ⟪ψ, H ψ⟫_ℂ := by simpa [hψ] using hbot ψ
  linarith

/-- **Algebraic form of the `dΓ` lift (Step 4 of answer A).**  On the `n`-particle sector,
`dΓ(h)` is a sum of `n` copies of `h` acting on the separate factors. If each summand is `≥ μ`,
the sum is `≥ nμ`. -/
theorem second_quantized_edge {ι : Type*} (s : Finset ι) (h : ι → E →L[ℂ] E) (μ : ℝ)
    (hh : ∀ i ∈ s, ∀ x : E, μ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, h i x⟫_ℂ) (x : E) :
    (s.card * μ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, (∑ i ∈ s, h i) x⟫_ℂ := by
  rw [sum_apply, inner_sum, map_sum]
  calc (s.card * μ) * ‖x‖ ^ 2 = ∑ i ∈ s, μ * ‖x‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum fun i hi => hh i hi x

/-! ## Part B -/

/-- If `Bv = cv` then `e^{zB} v = e^{zc} v`. -/
theorem exp_smul_apply_of_eigen [CompleteSpace E] (B : E →L[ℂ] E) (v : E) (c : ℂ)
    (hv : B v = c • v) (z : ℂ) : exp (z • B) v = Complex.exp (z * c) • v := by
  set f : ℂ → E := fun u => Complex.exp (-(u * c)) • exp (u • B) v with hf
  have hd : ∀ w : ℂ, HasDerivAt f 0 w := by
    intro w
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℂ) B w).clm_apply (hasDerivAt_const w v)
    have h2 : HasDerivAt (fun u : ℂ => Complex.exp (-(u * c))) (Complex.exp (-(w * c)) * -c) w := by
      have := ((hasDerivAt_id w).mul_const c).neg.cexp
      simpa using this
    have h3 := h2.smul h1
    convert h3 using 1
    simp only [mul_apply_eq_comp, hv, map_smul, map_zero, add_zero]
    rw [smul_smul, ← add_smul]
    ring_nf
    simp
  have hc := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0
  simp only [hf, zero_mul, neg_zero, Complex.exp_zero, zero_smul, exp_zero, one_smul,
    one_apply_eq_self] at hc
  calc exp (z • B) v = Complex.exp (z * c) • (Complex.exp (-(z * c)) • exp (z • B) v) := by
        rw [smul_smul, ← Complex.exp_add]; simp
    _ = _ := by rw [hc]

/-- **On a fixed outer sector the shift is a scalar.**  If `[H, N] = 0` and `Nψ = nψ`, then
`e^{-τ(H+μN)} ψ = e^{-τμn} e^{-τH} ψ`. -/
theorem shifted_transfer_on_sector [CompleteSpace E] (H N : E →L[ℂ] E) (hHN : Commute H N)
    (ψ : E) (n : ℝ) (hψ : N ψ = (n : ℂ) • ψ) (μ τ : ℝ) :
    exp ((τ : ℂ) • (-(H + (μ : ℂ) • N))) ψ
      = (Real.exp (-(τ * μ * n)) : ℂ) • exp ((τ : ℂ) • (-H)) ψ := by
  have e1 : (τ : ℂ) • (-(H + (μ : ℂ) • N)) = (τ : ℂ) • (-H) + (-((τ : ℂ) * μ)) • N := by
    rw [neg_add, smul_add, smul_neg, smul_neg, smul_smul, neg_smul]
  have hXY : Commute ((τ : ℂ) • (-H)) ((-((τ : ℂ) * μ)) • N) :=
    (hHN.neg_left.smul_left _).smul_right _
  rw [e1, exp_add_of_commute hXY, mul_apply_eq_comp,
    exp_smul_apply_of_eigen N ψ _ hψ, map_smul, Complex.ofReal_exp]
  congr 2
  push_cast; ring

/-- Every matrix element of the shifted transfer operator into the sector `N = n` factorises as
`e^{-τμn}` times the unshifted one. This covers number-changing observables such as outer
creation operators acting on the outer vacuum (`n = 1`): the `e^{-μτ}` decay is an explicit
prefactor multiplying the physical correlation `⟪χ, e^{-τH} ψ⟫`. -/
theorem shifted_correlation_factorizes [CompleteSpace E] (H N : E →L[ℂ] E) (hHN : Commute H N)
    (χ ψ : E) (n : ℝ) (hψ : N ψ = (n : ℂ) • ψ) (μ τ : ℝ) :
    ⟪χ, exp ((τ : ℂ) • (-(H + (μ : ℂ) • N))) ψ⟫_ℂ
      = (Real.exp (-(τ * μ * n)) : ℂ) * ⟪χ, exp ((τ : ℂ) • (-H)) ψ⟫_ℂ := by
  rw [shifted_transfer_on_sector H N hHN ψ n hψ μ τ, inner_smul_right]

/-- **Normalised correlations do not see `μ`.**  For `ψ` in the sector `N = n`, `B` commuting
with `N` and any `A`,
`⟪ψ, A e^{-τ(H+μN)} B ψ⟫ / ⟪ψ, e^{-τ(H+μN)} ψ⟫ = ⟪ψ, A e^{-τH} B ψ⟫ / ⟪ψ, e^{-τH} ψ⟫`. -/
theorem shifted_normalized_correlation_invariant [CompleteSpace E] (H N A B : E →L[ℂ] E)
    (hHN : Commute H N) (hBN : Commute B N) (ψ : E) (n : ℝ) (hψ : N ψ = (n : ℂ) • ψ)
    (μ τ : ℝ) :
    ⟪ψ, A (exp ((τ : ℂ) • (-(H + (μ : ℂ) • N))) (B ψ))⟫_ℂ
        / ⟪ψ, exp ((τ : ℂ) • (-(H + (μ : ℂ) • N))) ψ⟫_ℂ
      = ⟪ψ, A (exp ((τ : ℂ) • (-H)) (B ψ))⟫_ℂ / ⟪ψ, exp ((τ : ℂ) • (-H)) ψ⟫_ℂ := by
  have hBψ : N (B ψ) = (n : ℂ) • B ψ := by
    rw [← mul_apply_eq_comp, ← hBN.eq, mul_apply_eq_comp, hψ, map_smul]
  rw [shifted_transfer_on_sector H N hHN ψ n hψ μ τ,
    shifted_transfer_on_sector H N hHN (B ψ) n hBψ μ τ, map_smul, inner_smul_right,
    inner_smul_right]
  exact mul_div_mul_left _ _ (by exact_mod_cast (Real.exp_pos _).ne')

/-- The rank-one operator `x ↦ ⟪u, x⟫ • w` (Dirac notation `|w⟩⟨u|`). -/
def rankOne (u w : E) : E →L[ℂ] E := (innerSL ℂ u).smulRight w

@[simp] theorem rankOne_apply (u w x : E) : rankOne u w x = ⟪u, x⟫_ℂ • w := by
  simp [rankOne]

/-- `|w⟩⟨u|` commutes with a symmetric `N` when `u` and `w` lie in the same eigenspace. -/
theorem rankOne_commute (N : E →L[ℂ] E) (hN : ∀ x y : E, ⟪N x, y⟫_ℂ = ⟪x, N y⟫_ℂ)
    (u w : E) (k : ℝ) (hu : N u = (k : ℂ) • u) (hw : N w = (k : ℂ) • w) :
    Commute (rankOne u w) N := by
  ext x
  simp only [mul_apply_eq_comp, rankOne_apply, map_smul, hw, ← hN, hu,
    inner_smul_left, Complex.conj_ofReal, smul_smul]
  ring_nf

/-- Euclidean transfer operator `e^{-τ(H + μN)}` of the shifted Hamiltonian. -/
def shiftedTransfer [CompleteSpace E] (H N : E →L[ℂ] E) (μ τ : ℝ) : E →L[ℂ] E :=
  exp ((τ : ℂ) • (-(H + (μ : ℂ) • N)))

/-- Normalised truncated Euclidean correlation of `A`, `B` in the state `ω` for the transfer
operator `U`: `⟪ω, A U B ω⟫ / ⟪ω, U ω⟫ - ⟪ω, A ω⟫⟪ω, B ω⟫`. -/
def truncCorr (U A B : E →L[ℂ] E) (ω : E) : ℂ :=
  ⟪ω, A (U (B ω))⟫_ℂ / ⟪ω, U ω⟫_ℂ - ⟪ω, A ω⟫_ℂ * ⟪ω, B ω⟫_ℂ

/-- **Number-preserving observables can excite the inner vacuum.**  Let `ω` (the inner vacuum)
and `φ ⊥ ω`, `φ ≠ 0`, lie in the one-outer-quantum sector `N = 1`. Then `O = |φ⟩⟨ω|` and
`A = |ω⟩⟨φ|` commute with `N`, `Oω = φ` is not a multiple of `ω`, and the truncated
correlation `⟪ω, A O ω⟫ - ⟪ω, A ω⟫⟪ω, O ω⟫ = ‖φ‖² ≠ 0`. -/
theorem number_preserving_excites_inner_vacuum (N : E →L[ℂ] E)
    (hN : ∀ x y : E, ⟪N x, y⟫_ℂ = ⟪x, N y⟫_ℂ)
    (ω φ : E) (hω : N ω = ω) (hφ : N φ = φ) (horth : ⟪ω, φ⟫_ℂ = 0) (hφ0 : φ ≠ 0)
    (hω1 : ‖ω‖ = 1) :
    Commute (rankOne ω φ) N ∧ Commute (rankOne φ ω) N ∧ rankOne ω φ ω = φ ∧
      (∀ c : ℂ, rankOne ω φ ω ≠ c • ω) ∧
      ⟪ω, rankOne φ ω (rankOne ω φ ω)⟫_ℂ - ⟪ω, rankOne φ ω ω⟫_ℂ * ⟪ω, rankOne ω φ ω⟫_ℂ
        = (‖φ‖ ^ 2 : ℂ) := by
  have hω' : N ω = ((1 : ℝ) : ℂ) • ω := by simp [hω]
  have hφ' : N φ = ((1 : ℝ) : ℂ) • φ := by simp [hφ]
  have hωω : ⟪ω, ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K]; simp [hω1]
  have hφω : ⟪φ, ω⟫_ℂ = 0 := by rw [← inner_conj_symm, horth, map_zero]
  have hOω : rankOne ω φ ω = φ := by simp [hω1]
  refine ⟨rankOne_commute N hN ω φ 1 hω' hφ', rankOne_commute N hN φ ω 1 hφ' hω', hOω,
    fun c hc => hφ0 ?_, ?_⟩
  · have h := congrArg (fun x => ⟪ω, x⟫_ℂ) hc
    simp only [hOω, horth, inner_smul_right, hωω, mul_one] at h
    rw [hOω, ← h, zero_smul] at hc
    exact hc
  · rw [hOω]
    simp [hφω, inner_self_eq_norm_sq_to_K, hω1]

/-- **Inner-vacuum correlations under the shift.**  Take `ω`, `φ` in the sector `N = 1`, with
`Hω = 0` and `Hφ = eφ`. For `O = |φ⟩⟨ω|`, `A = |ω⟩⟨φ|`:
the unnormalised correlation is `e^{-τ(μ+e)}‖φ‖²`, but the normalised truncated correlation
is `e^{-τe}‖φ‖²`, independently of `μ`. -/
theorem inner_vacuum_shifted_correlation [CompleteSpace E] (H N : E →L[ℂ] E)
    (hHN : Commute H N) (ω φ : E) (hω : N ω = ω) (hφ : N φ = φ)
    (hHω : H ω = 0) (e : ℝ) (hHφ : H φ = (e : ℂ) • φ) (horth : ⟪ω, φ⟫_ℂ = 0)
    (hω1 : ‖ω‖ = 1) (μ τ : ℝ) :
    ⟪ω, rankOne φ ω (shiftedTransfer H N μ τ (rankOne ω φ ω))⟫_ℂ
        = (Real.exp (-(τ * (μ + e))) * ‖φ‖ ^ 2 : ℝ) ∧
      truncCorr (shiftedTransfer H N μ τ) (rankOne φ ω) (rankOne ω φ) ω
        = (Real.exp (-(τ * e)) * ‖φ‖ ^ 2 : ℝ) := by
  have hωω : ⟪ω, ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K]; simp [hω1]
  have hφω : ⟪φ, ω⟫_ℂ = 0 := by rw [← inner_conj_symm, horth, map_zero]
  have hOω : rankOne ω φ ω = φ := by simp [hω1]
  have hφφ : ⟪φ, φ⟫_ℂ = ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hφ' : N φ = ((1 : ℝ) : ℂ) • φ := by simp [hφ]
  have hω' : N ω = ((1 : ℝ) : ℂ) • ω := by simp [hω]
  have hUφ : shiftedTransfer H N μ τ φ
      = ((Real.exp (-(τ * μ * 1)) * Real.exp (-(τ * e)) : ℝ) : ℂ) • φ := by
    rw [shiftedTransfer, shifted_transfer_on_sector H N hHN φ 1 hφ' μ τ,
      exp_smul_apply_of_eigen (-H) φ (-(e : ℂ)) (by simp [hHφ]), smul_smul]
    congr 1
    push_cast
    ring_nf
  have hUω : shiftedTransfer H N μ τ ω = ((Real.exp (-(τ * μ * 1)) : ℝ) : ℂ) • ω := by
    rw [shiftedTransfer, shifted_transfer_on_sector H N hHN ω 1 hω' μ τ,
      exp_smul_apply_of_apply_eq_zero (-H) ω (by simp [hHω])]
  have hnum : ⟪ω, rankOne φ ω (shiftedTransfer H N μ τ (rankOne ω φ ω))⟫_ℂ
      = (Real.exp (-(τ * (μ + e))) * ‖φ‖ ^ 2 : ℝ) := by
    rw [hOω, hUφ, rankOne_apply, inner_smul_right, inner_smul_right, hωω, hφφ, mul_one,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3; ring
  refine ⟨hnum, ?_⟩
  rw [truncCorr, hnum, hUω, inner_smul_right, hωω, hOω]
  simp only [rankOne_apply, hφω, zero_smul, inner_zero_right, zero_mul, sub_zero, mul_one]
  rw [div_eq_iff (by exact_mod_cast (Real.exp_pos _).ne'), ← Complex.ofReal_mul]
  congr 1
  rw [mul_right_comm, ← Real.exp_add]
  congr 2; ring

/-- **The artificial gap does not give clustering at rate `μ` in the inner vacuum.**  In the
setting of `inner_vacuum_shifted_correlation`, if `e < μ` then the normalised truncated
correlation in `ω` is not bounded by `C e^{-μτ}` for any constant `C`. -/
theorem inner_vacuum_no_rate_mu_clustering [CompleteSpace E] (H N : E →L[ℂ] E)
    (hHN : Commute H N) (ω φ : E) (hω : N ω = ω) (hφ : N φ = φ)
    (hHω : H ω = 0) (e : ℝ) (hHφ : H φ = (e : ℂ) • φ) (horth : ⟪ω, φ⟫_ℂ = 0)
    (hω1 : ‖ω‖ = 1) (hφ0 : φ ≠ 0) (μ : ℝ) (he : e < μ) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖truncCorr (shiftedTransfer H N μ τ) (rankOne φ ω) (rankOne ω φ) ω‖
        ≤ C * Real.exp (-(μ * τ)) := by
  rintro ⟨C, hC⟩
  have hpos : 0 < ‖φ‖ ^ 2 := by positivity
  have hb : ∀ τ : ℝ, 0 ≤ τ → ‖φ‖ ^ 2 ≤ C * Real.exp (-((μ - e) * τ)) := by
    intro τ hτ
    have h := hC τ hτ
    rw [(inner_vacuum_shifted_correlation H N hHN ω φ hω hφ hHω e hHφ horth hω1 μ τ).2,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    have he' : Real.exp (-((μ - e) * τ)) = Real.exp (-(μ * τ)) * Real.exp (τ * e) := by
      rw [← Real.exp_add]; ring_nf
    have hx : Real.exp (-(τ * e)) * Real.exp (τ * e) = 1 := by
      rw [← Real.exp_add]; simp
    rw [he', ← mul_assoc]
    have := mul_le_mul_of_nonneg_right h (Real.exp_pos (τ * e)).le
    calc ‖φ‖ ^ 2 = Real.exp (-(τ * e)) * ‖φ‖ ^ 2 * Real.exp (τ * e) := by
          rw [mul_right_comm, hx, one_mul]
      _ ≤ _ := this
  have hlim : Filter.Tendsto (fun τ : ℝ => C * Real.exp (-((μ - e) * τ))) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun τ : ℝ => (μ - e) * τ) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop (sub_pos.2 he)
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
  have hle : ‖φ‖ ^ 2 ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, fun τ hτ => hb τ hτ⟩)
  linarith

/-- Basis vector of the three-dimensional toy nested model. -/
abbrev bv (i : Fin 3) : EuclideanSpace ℂ (Fin 3) := EuclideanSpace.single i 1

/-- Outer number operator of the toy nested model. -/
def toyN : EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  rankOne (bv 1) (bv 1) + rankOne (bv 2) (bv 2)

/-- Hamiltonian of the toy nested model. -/
def toyH (e : ℝ) : EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  (e : ℂ) • rankOne (bv 2) (bv 2)

/-- The toy outer number operator is symmetric. -/
theorem toyN_symm (x y : EuclideanSpace ℂ (Fin 3)) : ⟪toyN x, y⟫_ℂ = ⟪x, toyN y⟫_ℂ := by
  simp only [toyN, add_apply, rankOne_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, bv, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right]
  simp
  ring

/-- `Re⟪x, N x⟫ = |x₁|² + |x₂|²` in the toy model. -/
theorem toy_re_inner_N (x : EuclideanSpace ℂ (Fin 3)) :
    RCLike.re ⟪x, toyN x⟫_ℂ = ‖x 1‖ ^ 2 + ‖x 2‖ ^ 2 := by
  simp only [toyN, add_apply, rankOne_apply, inner_add_right,
    inner_smul_right, bv, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- `‖x‖² = |x₀|² + |x₁|² + |x₂|²` in the toy model. -/
theorem toy_norm_sq (x : EuclideanSpace ℂ (Fin 3)) :
    ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 + ‖x 2‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]

/-- **A concrete nested-Fock toy model.**  `bv 0` is the outer vacuum (no outer quanta);
`bv 1` (the inner vacuum `ω`) and `bv 2` (an inner excitation of energy `e`) span the
one-outer-quantum sector.  All the hypotheses of the artificial-gap construction hold
(`H ≥ 0`, `N ≥ 1` off the outer vacuum, the outer vacuum spans `ker N`, `[H, N] = 0`), a
number-preserving observable excites the inner vacuum, and yet for `μ > e` the normalised
truncated correlation in the inner vacuum is not `O(e^{-μτ})`. -/
theorem toy_nested_model (e μ : ℝ) (he0 : 0 ≤ e) (he : e < μ) :
    (∀ x, 0 ≤ RCLike.re ⟪x, toyH e x⟫_ℂ) ∧
    (∀ x, ⟪bv 0, x⟫_ℂ = 0 → ‖x‖ ^ 2 ≤ RCLike.re ⟪x, toyN x⟫_ℂ) ∧
    toyN (bv 0) = 0 ∧ toyH e (bv 0) = 0 ∧
    (∀ x, toyN x = 0 → ∃ c : ℂ, x = c • bv 0) ∧
    Commute (toyH e) toyN ∧
    Commute (rankOne (bv 1) (bv 2)) toyN ∧ Commute (rankOne (bv 2) (bv 1)) toyN ∧
    rankOne (bv 1) (bv 2) (bv 1) = bv 2 ∧
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖truncCorr (shiftedTransfer (toyH e) toyN μ τ) (rankOne (bv 2) (bv 1))
          (rankOne (bv 1) (bv 2)) (bv 1)‖ ≤ C * Real.exp (-(μ * τ)) := by
  have hHN : Commute (toyH e) toyN := by
    ext x : 1
    simp [toyH, toyN, bv, EuclideanSpace.inner_single_left]
  have hN1 : toyN (bv 1) = bv 1 := by simp [toyN, bv, EuclideanSpace.inner_single_left]
  have hN2 : toyN (bv 2) = bv 2 := by simp [toyN, bv, EuclideanSpace.inner_single_left]
  have hH1 : toyH e (bv 1) = 0 := by simp [toyH, bv, EuclideanSpace.inner_single_left]
  have hH2 : toyH e (bv 2) = (e : ℂ) • bv 2 := by
    simp [toyH, bv]
  have horth : ⟪bv 1, bv 2⟫_ℂ = 0 := by simp [bv, EuclideanSpace.inner_single_left]
  have hn1 : ‖bv 1‖ = 1 := by simp [bv]
  have h20 : bv 2 ≠ 0 := by simp [bv]
  have hex :=
    number_preserving_excites_inner_vacuum toyN toyN_symm (bv 1) (bv 2) hN1 hN2 horth h20 hn1
  refine ⟨fun x => ?_, fun x hx => ?_, ?_, ?_, fun x hx => ?_, hHN, hex.1, hex.2.1, hex.2.2.1,
    inner_vacuum_no_rate_mu_clustering (toyH e) toyN hHN (bv 1) (bv 2) hN1 hN2 hH1 e hH2 horth
      hn1 h20 μ he⟩
  · simp only [toyH, smul_apply, rankOne_apply, inner_smul_right, bv,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
    positivity
  · rw [toy_re_inner_N, toy_norm_sq]
    have : x 0 = 0 := by simpa [bv, EuclideanSpace.inner_single_left] using hx
    simp [this]
  · simp [toyN, bv, EuclideanSpace.inner_single_left]
  · simp [toyH, bv, EuclideanSpace.inner_single_left]
  · refine ⟨x 0, ?_⟩
    have h1 := congrArg (fun y => y 1) hx
    have h2 := congrArg (fun y => y 2) hx
    simp [toyN, bv, EuclideanSpace.inner_single_left] at h1 h2
    ext i
    fin_cases i <;> simp [bv, h1, h2]

end CftCheck
