import Mathlib

/-!
# Chapter TrotterProduct — the bounded Euclidean Lie–Trotter product formula (H2)

`cft_path.md` §3 splits the Euclidean evolution into `N` steps, replaces the exponent of a sum
by a product of exponentials, and records that the accumulated `O(ε²)` error over `N` steps is
`N ε² = T ε → 0`. This module proves that identity in the bounded case, for an arbitrary real
Banach algebra: no commutativity, no finite dimension and no self-adjointness is assumed.

## Contents

* `norm_exp_le` — `‖exp x‖ ≤ exp ‖x‖`.
* `hasSum_exp_norm` — the real exponential as `∑ (n!)⁻¹ ‖x‖ⁿ`.
* `norm_exp_sub_one_sub_id_le` — the second-order remainder of the exponential series,
  `‖exp x − 1 − x‖ ≤ ‖x‖² exp ‖x‖`; the only estimate in the proof that is not a triangle
  inequality.
* `norm_pow_sub_pow_le` — the telescoping bound `‖xⁿ − yⁿ‖ ≤ n ‖x − y‖ Mⁿ⁻¹` for `‖x‖, ‖y‖ ≤ M`.
* `trotter_product_tendsto` — the product formula itself:
  `(e^{(T/N)a} e^{(T/N)b})^N → e^{T(a+b)}` for `T ≥ 0`.
* `trotter_product_of_commute` — the commuting case, where the identity is exact at every step
  (so the theorem's content is precisely the non-commuting one).
* `trotter_heat_tendsto` — the Euclidean/heat sign, `e^{−Ta}` and `e^{−Tb}` sliced against each
  other converging to `e^{−T(a+b)}`.

## Boundary

The theorem is *bounded*: `a` and `b` are elements of a Banach algebra, so it concerns uniformly
bounded generators (matrix algebras, finite mode truncations, bounded multipliers). The
unbounded form-sum version — `h₀ ≥ 0`, `V ≥ 0` on a common core, strong convergence of
`(e^{−(T/N)h₀} e^{−(T/N)V})^N` to the semigroup of the form sum — is **not** proved here; that
is the H2 item that remains, and it is what `ChapterNonnegSemigroup`'s machinery plus a Chernoff
argument would have to supply. The symmetric Strang product `e^{−εV/2} e^{−εh₀} e^{−εV/2}` is not
covered either: the exact algebraic Strang identity lives in `ChapterSymmetricTimeStepOrdering`,
but its `O(ε²)` step estimate is not assembled here. Convergence is proved, not a stated rate:
the quantitative content is the telescoping bound `‖S_N^N − Y_N^N‖ ≤ N‖S_N − Y_N‖ e^{Tc}` together
with `‖S_N − Y_N‖ = o(T/N)` from the derivative at `0`, i.e. `T·o(1)`; no explicit `C T²/N`
constant is extracted. Midpoint/Weyl ordering for position–momentum cross-terms is untouched:
a product formula for a fixed pair `(a, b)` cannot encode an operator-ordering correction.
Nothing here constructs a path measure, identifies a marginal of `mehlerPathMeasure`, or proves
reflection positivity — those are H3's items.
-/

noncomputable section
namespace BookProof.TrotterProduct

open Filter Topology
open scoped Topology

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A]

noncomputable local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

omit [CompleteSpace A] in
/-- The exponential is bounded by the exponential of the norm. -/
lemma norm_exp_le (x : A) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hs : Summable (fun n : ℕ => ‖((n.factorial : ℝ))⁻¹ • x ^ n‖) :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x
  calc ‖∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • x ^ n‖
      ≤ ∑' n : ℕ, ‖((n.factorial : ℝ))⁻¹ • x ^ n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ * ‖x‖ ^ n := by
        refine Summable.tsum_le_tsum (fun n => ?_) hs ?_
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rcases Nat.eq_zero_or_pos n with h | h
          · subst h; simp
          · exact norm_pow_le' x h
        · simpa [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖x‖
    _ = Real.exp ‖x‖ := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
        simp [smul_eq_mul]

omit [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- The real exponential as the norm series of a Banach algebra element. -/
lemma hasSum_exp_norm (x : A) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * ‖x‖ ^ n) (Real.exp ‖x‖) := by
  have h : HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ • ‖x‖ ^ n) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' ‖x‖
  simpa [smul_eq_mul] using h

omit [NormOneClass A] in
/-- The second-order remainder of the exponential series, bounded by the whole series. -/
lemma norm_exp_sub_one_sub_id_le (x : A) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  let f : ℕ → A := fun n => ((n.factorial : ℝ))⁻¹ • x ^ n
  have hf : HasSum f (NormedSpace.exp x) := NormedSpace.exp_series_hasSum_exp' x
  have h0 : f 0 = 1 := by simp [f]
  have h1 : f 1 = x := by simp [f]
  have hshift : HasSum (fun n : ℕ => f (n + 2)) (NormedSpace.exp x - (f 0 + f 1)) := by
    refine (hasSum_nat_add_iff (f := f) 2).2 ?_
    have hsum : (∑ i ∈ Finset.range 2, f i) = f 0 + f 1 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hsum, sub_add_cancel]
    exact hf
  have hsummable : Summable (fun n : ℕ => ‖f (n + 2)‖) := by
    have hs : Summable (fun n : ℕ => ‖f n‖) :=
      NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x
    exact (summable_nat_add_iff 2).2 hs
  have heq : NormedSpace.exp x - 1 - x = ∑' n : ℕ, f (n + 2) := by
    rw [hshift.tsum_eq, h0, h1]; abel
  have hstep1 : ‖NormedSpace.exp x - 1 - x‖ ≤ ∑' n : ℕ, ‖f (n + 2)‖ := by
    rw [heq]; exact norm_tsum_le_tsum_norm hsummable
  have hterm : ∀ n : ℕ, ‖f (n + 2)‖ ≤ ‖x‖ ^ 2 * (((n.factorial : ℝ))⁻¹ * ‖x‖ ^ n) := by
    intro n
    have hfac : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) * n.factorial := by
      have e1 : (n + 2).factorial = (n + 2) * (n + 1).factorial := Nat.factorial_succ (n + 1)
      have e2 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
      rw [e1, e2]; push_cast; ring
    have hle : (((n + 2).factorial : ℝ))⁻¹ ≤ ((n.factorial : ℝ))⁻¹ := by
      rw [inv_le_inv₀ (a := ((n + 2).factorial : ℝ)) (b := (n.factorial : ℝ))
        (by positivity) (by positivity)]
      rw [hfac]
      have hge : (1:ℝ) ≤ ((n:ℝ) + 2) * ((n:ℝ) + 1) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hpos : (0:ℝ) ≤ (n.factorial : ℝ) := by positivity
      calc (n.factorial : ℝ) = 1 * (n.factorial : ℝ) := by ring
        _ ≤ (((n:ℝ) + 2) * ((n:ℝ) + 1)) * (n.factorial : ℝ) :=
            mul_le_mul_of_nonneg_right hge hpos
        _ = ((n:ℝ) + 2) * ((n:ℝ) + 1) * (n.factorial : ℝ) := by ring
    calc ‖f (n + 2)‖ = (((n + 2).factorial : ℝ))⁻¹ * ‖x ^ (n + 2)‖ := by
          simp [f, norm_smul]
      _ ≤ (((n + 2).factorial : ℝ))⁻¹ * ‖x‖ ^ (n + 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact norm_pow_le' x (by omega)
      _ ≤ ((n.factorial : ℝ))⁻¹ * ‖x‖ ^ (n + 2) := by
          refine mul_le_mul_of_nonneg_right hle (by positivity)
      _ = ‖x‖ ^ 2 * (((n.factorial : ℝ))⁻¹ * ‖x‖ ^ n) := by
          rw [pow_add]; ring
  have hstep2 : (∑' n : ℕ, ‖f (n + 2)‖) ≤
      ∑' n : ℕ, ‖x‖ ^ 2 * (((n.factorial : ℝ))⁻¹ * ‖x‖ ^ n) := by
    refine Summable.tsum_le_tsum hterm hsummable ?_
    simpa [smul_eq_mul] using
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖x‖).mul_left (‖x‖ ^ 2)
  have hstep3 : (∑' n : ℕ, ‖x‖ ^ 2 * (((n.factorial : ℝ))⁻¹ * ‖x‖ ^ n)) =
      ‖x‖ ^ 2 * Real.exp ‖x‖ := by
    rw [tsum_mul_left, (hasSum_exp_norm x).tsum_eq]
  linarith [hstep1, hstep2, hstep3]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- Telescoping bound for the difference of two powers. -/
lemma norm_pow_sub_pow_le {x y : A} {M : ℝ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M)
    (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ n * ‖x - y‖ * M ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hM0 : 0 ≤ M := (norm_nonneg x).trans hx
      have hsplit : x ^ (k + 1) - y ^ (k + 1) = x ^ k * (x - y) + (x ^ k - y ^ k) * y := by
        rw [pow_succ, pow_succ]
        noncomm_ring
      have hxpow : ‖x ^ k‖ ≤ M ^ k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp
        · exact (norm_pow_le' x h).trans (pow_le_pow_left₀ (norm_nonneg x) hx k)
      have key : ‖x ^ (k + 1) - y ^ (k + 1)‖ ≤ ((k : ℝ) + 1) * ‖x - y‖ * M ^ k := by
        calc ‖x ^ (k + 1) - y ^ (k + 1)‖
            = ‖x ^ k * (x - y) + (x ^ k - y ^ k) * y‖ := by rw [hsplit]
          _ ≤ ‖x ^ k * (x - y)‖ + ‖(x ^ k - y ^ k) * y‖ := norm_add_le _ _
          _ ≤ ‖x ^ k‖ * ‖x - y‖ + ‖x ^ k - y ^ k‖ * ‖y‖ :=
              add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ ≤ M ^ k * ‖x - y‖ + (k * ‖x - y‖ * M ^ (k - 1)) * M := by
              refine add_le_add (mul_le_mul_of_nonneg_right hxpow (norm_nonneg _)) ?_
              calc ‖x ^ k - y ^ k‖ * ‖y‖ ≤ (k * ‖x - y‖ * M ^ (k - 1)) * ‖y‖ :=
                    mul_le_mul_of_nonneg_right ih (norm_nonneg y)
                _ ≤ (k * ‖x - y‖ * M ^ (k - 1)) * M :=
                    mul_le_mul_of_nonneg_left hy (by positivity)
          _ = ((k : ℝ) + 1) * ‖x - y‖ * M ^ k := by
              rcases Nat.eq_zero_or_pos k with hk | hk
              · subst hk; ring
              · have hM : M ^ (k - 1) * M = M ^ k := by
                  rw [← pow_succ, Nat.sub_add_cancel hk]
                calc M ^ k * ‖x - y‖ + (k * ‖x - y‖ * M ^ (k - 1)) * M
                    = M ^ k * ‖x - y‖ + k * ‖x - y‖ * (M ^ (k - 1) * M) := by ring
                  _ = M ^ k * ‖x - y‖ + k * ‖x - y‖ * M ^ k := by rw [hM]
                  _ = ((k : ℝ) + 1) * ‖x - y‖ * M ^ k := by ring
      have hgoal : ((k + 1 : ℕ) : ℝ) * ‖x - y‖ * M ^ (k + 1 - 1)
          = ((k : ℝ) + 1) * ‖x - y‖ * M ^ k := by
        rw [Nat.add_sub_cancel]; push_cast; ring
      rw [hgoal]
      exact key

/-- The bounded Euclidean Lie–Trotter product formula (Trotter 1959). -/
theorem trotter_product_tendsto (a b : A) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun N : ℕ =>
        (NormedSpace.exp ((T / (N : ℝ)) • a) * NormedSpace.exp ((T / (N : ℝ)) • b)) ^ N)
      atTop (𝓝 (NormedSpace.exp (T • (a + b)))) := by
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · subst hT0
    simp only [zero_div, zero_smul, NormedSpace.exp_zero, one_mul, one_pow]
    exact tendsto_const_nhds
  set c : ℝ := ‖a‖ + ‖b‖ + ‖a + b‖ with hc
  set E : ℝ := Real.exp (T * c) with hE
  set S : ℝ → A := fun ε => NormedSpace.exp (ε • a) * NormedSpace.exp (ε • b) with hS
  set Y : ℝ → A := fun ε => NormedSpace.exp (ε • (a + b)) with hY
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hE0 : 0 < E := Real.exp_pos _
  -- one-step derivative at zero
  have hda : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • a)) a 0 := by
    simpa using hasDerivAt_exp_smul_const (x := a) (t := (0:ℝ))
  have hdb : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • b)) b 0 := by
    simpa using hasDerivAt_exp_smul_const (x := b) (t := (0:ℝ))
  have hSd : HasDerivAt S (a + b) 0 := by
    have h := hda.mul hdb
    simpa [hS, NormedSpace.exp_zero] using h
  have hYd : HasDerivAt Y (a + b) 0 := by
    simpa [hY, NormedSpace.exp_zero] using hasDerivAt_exp_smul_const (x := a + b) (t := (0:ℝ))
  have hD : HasDerivAt (fun ε : ℝ => S ε - Y ε) 0 0 := by
    have h := hSd.sub hYd
    simpa using h
  have hf0 : (fun ε : ℝ => S ε - Y ε) 0 = 0 := by
    simp [hS, hY, NormedSpace.exp_zero]
  have hslope : Tendsto (fun ε : ℝ => slope (fun ε : ℝ => S ε - Y ε) 0 ε)
      (𝓝[≠] (0:ℝ)) (𝓝 0) :=
    hasDerivAt_iff_tendsto_slope.mp hD
  have hεmem : Tendsto (fun N : ℕ => T / (N : ℝ)) atTop (𝓝[≠] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNne : (N : ℝ) ≠ 0 := by
        have : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
        positivity
      exact div_ne_zero hTpos.ne' hNne
  have hcomp : Tendsto (fun N : ℕ => slope (fun ε : ℝ => S ε - Y ε) 0 (T / (N:ℝ)))
      atTop (𝓝 0) := hslope.comp hεmem
  have hsmul : Tendsto (fun N : ℕ => T • slope (fun ε : ℝ => S ε - Y ε) 0 (T / (N:ℝ)))
      atTop (𝓝 0) := by
    simpa using hcomp.const_smul T
  have hcongr : (fun N : ℕ => T • slope (fun ε : ℝ => S ε - Y ε) 0 (T / (N:ℝ)))
      =ᶠ[atTop] (fun N : ℕ => (N : ℝ) • (S (T / (N:ℝ)) - Y (T / (N:ℝ)))) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [slope, hf0, sub_zero, smul_smul]
    have hNne : (N : ℝ) ≠ 0 := by
      have : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
      positivity
    congr 1 <;> simp
    field_simp
  have hN : Tendsto (fun N : ℕ => (N : ℝ) • (S (T / (N:ℝ)) - Y (T / (N:ℝ))))
      atTop (𝓝 0) := hsmul.congr' hcongr
  -- the norm bound for the mixed term
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖(S (T / (N:ℝ))) ^ N - (Y (T / (N:ℝ))) ^ N‖ ≤
        ‖(N : ℝ) • (S (T / (N:ℝ)) - Y (T / (N:ℝ)))‖ * E := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    set ε : ℝ := T / (N:ℝ) with hε
    have hε0 : 0 ≤ ε := div_nonneg hTpos.le hNpos.le
    have hNε : (N:ℝ) * ε = T := by
      rw [hε]; field_simp
    have hεN : ε ≤ T := by
      rw [← hNε]
      nlinarith [hε0, show (1:ℝ) ≤ (N:ℝ) by exact_mod_cast hN]
    have hexp1 : ‖NormedSpace.exp (ε • a)‖ ≤ Real.exp (ε * ‖a‖) := by
      have h := norm_exp_le (ε • a)
      rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0] at h
    have hexp2 : ‖NormedSpace.exp (ε • b)‖ ≤ Real.exp (ε * ‖b‖) := by
      have h := norm_exp_le (ε • b)
      rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0] at h
    have hexpab : ‖NormedSpace.exp (ε • (a + b))‖ ≤ Real.exp (ε * ‖a + b‖) := by
      have h := norm_exp_le (ε • (a + b))
      rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0] at h
    have hSle : ‖S ε‖ ≤ Real.exp (ε * c) := by
      have h1 : ‖S ε‖ ≤ Real.exp (ε * ‖a‖) * Real.exp (ε * ‖b‖) := by
        calc ‖S ε‖ = ‖NormedSpace.exp (ε • a) * NormedSpace.exp (ε • b)‖ := rfl
          _ ≤ ‖NormedSpace.exp (ε • a)‖ * ‖NormedSpace.exp (ε • b)‖ := norm_mul_le _ _
          _ ≤ Real.exp (ε * ‖a‖) * Real.exp (ε * ‖b‖) := by gcongr
      calc ‖S ε‖ ≤ Real.exp (ε * ‖a‖) * Real.exp (ε * ‖b‖) := h1
        _ = Real.exp (ε * ‖a‖ + ε * ‖b‖) := (Real.exp_add _ _).symm
        _ = Real.exp (ε * (‖a‖ + ‖b‖)) := by ring_nf
        _ ≤ Real.exp (ε * c) := by
            refine Real.exp_le_exp.mpr ?_
            rw [hc]
            nlinarith [hε0, norm_nonneg (a + b)]
    have hYle : ‖Y ε‖ ≤ Real.exp (ε * c) := by
      calc ‖Y ε‖ ≤ Real.exp (ε * ‖a + b‖) := hexpab
        _ ≤ Real.exp (ε * c) := by
            refine Real.exp_le_exp.mpr ?_
            rw [hc]
            nlinarith [hε0, norm_nonneg a, norm_nonneg b]
    have htelesc := norm_pow_sub_pow_le hSle hYle N
    have hM : (Real.exp (ε * c)) ^ (N - 1) ≤ E := by
      rw [hE, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have hNsub : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
        rw [Nat.cast_sub hN]; norm_num
      rw [hNsub]
      have hle : ((N:ℝ) - 1) * ε ≤ T := by
        rw [← hNε]
        nlinarith [hε0]
      calc ((N:ℝ) - 1) * (ε * c) = (((N:ℝ) - 1) * ε) * c := by ring
        _ ≤ T * c := mul_le_mul_of_nonneg_right hle hc0
    have hnsmul : ‖(N : ℝ) • (S ε - Y ε)‖ = (N:ℝ) * ‖S ε - Y ε‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hNpos.le]
    calc ‖(S ε) ^ N - (Y ε) ^ N‖
        ≤ N * ‖S ε - Y ε‖ * (Real.exp (ε * c)) ^ (N - 1) := htelesc
      _ = ‖(N : ℝ) • (S ε - Y ε)‖ * (Real.exp (ε * c)) ^ (N - 1) := by
          rw [hnsmul]
      _ ≤ ‖(N : ℝ) • (S ε - Y ε)‖ * E :=
          mul_le_mul_of_nonneg_left hM (norm_nonneg _)
  have hzero : Tendsto (fun N : ℕ =>
      ‖(N : ℝ) • (S (T / (N:ℝ)) - Y (T / (N:ℝ)))‖ * E) atTop (𝓝 0) := by
    simpa using hN.norm.mul_const E
  have hnorm : Tendsto (fun N : ℕ =>
      ‖(S (T / (N:ℝ))) ^ N - (Y (T / (N:ℝ))) ^ N‖) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun N => norm_nonneg _)) hbound hzero
  have hdiff : Tendsto (fun N : ℕ =>
      (S (T / (N:ℝ))) ^ N - (Y (T / (N:ℝ))) ^ N) atTop (𝓝 0) := by
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have hYpow : ∀ N : ℕ, 1 ≤ N → (Y (T / (N:ℝ))) ^ N = NormedSpace.exp (T • (a + b)) := by
    intro N hN
    have hNne : (N : ℝ) ≠ 0 := by
      have : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
      positivity
    have hone : Y (T / (N:ℝ)) = NormedSpace.exp ((T / (N:ℝ)) • (a + b)) := rfl
    rw [hone, ← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have h2 : (N:ℝ) * (T / (N:ℝ)) = T := by field_simp
    rw [h2]
  have hconst : Tendsto (fun N : ℕ => (Y (T / (N:ℝ))) ^ N) atTop
      (𝓝 (NormedSpace.exp (T • (a + b)))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hYpow N hN).symm
  have := hdiff.add hconst
  simpa [hS, sub_add_cancel] using this
omit [NormOneClass A] in
/-- When the two generators commute the product is exact at every step, so the limit
carries no error: the theorem's content is the non-commuting case. -/
theorem trotter_product_of_commute {a b : A} (h : Commute a b) (T : ℝ) {N : ℕ}
    (hN : 1 ≤ N) :
    (NormedSpace.exp ((T / (N : ℝ)) • a) * NormedSpace.exp ((T / (N : ℝ)) • b)) ^ N
      = NormedSpace.exp (T • (a + b)) := by
  have hcomm : Commute ((T / (N:ℝ)) • a) ((T / (N:ℝ)) • b) := (h.smul_left _).smul_right _
  have hprod : NormedSpace.exp ((T / (N:ℝ)) • a) * NormedSpace.exp ((T / (N:ℝ)) • b)
      = NormedSpace.exp ((T / (N:ℝ)) • a + (T / (N:ℝ)) • b) :=
    (NormedSpace.exp_add_of_commute hcomm).symm
  rw [hprod, ← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_add, smul_smul, smul_smul]
  have hNne : (N:ℝ) ≠ 0 := by
    have : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    positivity
  field_simp
  rw [smul_add]

/-- The Euclidean (heat-semigroup) form: the product of the two heat flows converges to
the heat flow of the sum, at the same rate. -/
theorem trotter_heat_tendsto (a b : A) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun N : ℕ =>
        (NormedSpace.exp ((-(T / (N : ℝ))) • a) *
          NormedSpace.exp ((-(T / (N : ℝ))) • b)) ^ N)
      atTop (𝓝 (NormedSpace.exp ((-T) • (a + b)))) := by
  have h := trotter_product_tendsto (-a) (-b) hT
  have h1 : ∀ N : ℕ, (-(T / (N:ℝ))) • (-a) = (T / (N:ℝ)) • a := by
    intro N; rw [neg_smul, smul_neg, neg_neg]
  have h2 : (-T) • (-a + -b) = T • (a + b) := by
    rw [← neg_add, smul_neg, neg_smul, neg_neg]
  simpa [h1, h2] using h

end BookProof.TrotterProduct
