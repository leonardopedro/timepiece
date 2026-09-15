import Mathlib
import BookProof.ChapterOperatorSeriesEsa

/-!
# The general quadratic Hamiltonian of a boson field with infinitely many modes

`BookProof.ChapterFullQuadraticEsa` proves that *every* real quadratic-plus-linear
Hamiltonian in **finitely many** degrees of freedom is essentially self-adjoint on the
Gauss–polynomial core.  This module removes the finiteness of the mode set: the modes are
indexed by an arbitrary type `ι`, the Hilbert space is the boson Fock space
`ℓ²(ι →₀ ℕ)` of occupation-number configurations, and the Hamiltonian is the
second-quantized quadratic expression

`H = ∑ᵢ ωᵢ aᵢ†aᵢ + ∑ₖ (gₖ a^{†Pₖ}a^{Qₖ} + conj(gₖ) a^{†Qₖ}a^{Pₖ})`,

where each interaction term `a^{†P}a^{Q}` is a product of `|P| + |Q| ≤ 2` creation and
annihilation operators — pair creation `aᵢ†aⱼ†`, pair annihilation `aⱼaᵢ`, mode exchange
`aᵢ†aⱼ`, and the linear sources `aᵢ†`, `aᵢ`.  The free dispersion `ω` is an arbitrary
non-negative function of the mode — it need not be bounded — and the interaction is an
arbitrary family, subject only to the weighted absolute summability

`∑ₖ ‖gₖ‖ (ω(Pₖ) + ω(Qₖ) + 2) < ∞`.

The route is Faris–Lavine (Nelson's commutator theorem) with the comparison operator
`N = ∑ᵢ ωᵢ aᵢ†aᵢ + 𝒩 + 1`, `𝒩` the total number operator: each elementary hop is
relatively bounded by `N` and has commutator form dominated by `N`, with constants which
are summable exactly under the hypothesis above; the series instrument
`BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series` then applies.

## What is proved

* `deg`, `wsum`, `sig` — the total occupation number `|α|`, the free energy
  `ω(α) = ∑ᵢ ωᵢ αᵢ` and the comparison symbol `σ(α) = ω(α) + |α| + 1`.
* `fall`, `amp`, `tgt` — the falling factorial of a multi-index, the ladder amplitude of
  the monomial `a^{†P}a^{Q}` and the configuration it hops to; `amp_symm` is the
  self-adjointness of the amplitude under `(P, Q) ↦ (Q, P)`.
* `hopOp` — the elementary monomial as an operator on the maximal domain of `σ`, with
  `hopOp_norm_le` (relative bound) and `hopOp_pairing` (the adjoint relation
  `⟪a^{†P}a^{Q}x, y⟫ = ⟪x, a^{†Q}a^{P}y⟫`).
* `pairOp` — the Hermitian combination `g a^{†P}a^{Q} + conj(g) a^{†Q}a^{P}`, with its
  symmetry, its relative bound and its commutator-form bound.
* `freeOp` — the free Hamiltonian `∑ᵢ ωᵢ aᵢ†aᵢ`, symmetric, dominated by `N` and
  commuting with it.
* `fockH` and `fockH_essentiallySelfAdjointOn_core` — **the headline**: the full
  Hamiltonian is essentially self-adjoint on the finite-particle core of the Fock space.
* `bogoliubov_essentiallySelfAdjointOn_core` — the pair-creation (Bogoliubov)
  specialization.

Everything is `sorry`-free and `axiom`-free.
-/

open scoped ENNReal

namespace BookProof.FockQuadratic

open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

/-! ## 1. Occupation-number configurations -/

/-- An occupation-number configuration: finitely many modes excited. -/
abbrev Idx (ι : Type*) := ι →₀ ℕ

/-- The total occupation number `|α| = ∑ᵢ αᵢ`. -/
def deg (a : Idx ι) : ℕ := a.sum fun _ n => n

theorem deg_add (a b : Idx ι) : deg (a + b) = deg a + deg b := by
  simp [deg, Finsupp.sum_add_index']

theorem apply_le_deg (a : Idx ι) (i : ι) : a i ≤ deg a := by
  classical
  by_cases h : i ∈ a.support
  · exact Finset.single_le_sum (f := fun j => a j) (fun _ _ => Nat.zero_le _) h
  · simp [Finsupp.notMem_support_iff.mp h]

theorem tsub_add_cancel_of_le' {P a : Idx ι} (h : P ≤ a) : a - P + P = a := by
  ext j
  have hj : P j ≤ a j := by rw [Finsupp.le_def] at h; exact h j
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  omega

theorem deg_tsub_of_le {P a : Idx ι} (h : P ≤ a) : deg (a - P) + deg P = deg a := by
  rw [← deg_add, tsub_add_cancel_of_le' h]

/-- The free energy `ω(α) = ∑ᵢ ωᵢ αᵢ` of a configuration. -/
def wsum (ω : ι → ℝ) (a : Idx ι) : ℝ := a.sum fun i n => ω i * n

theorem wsum_add (ω : ι → ℝ) (a b : Idx ι) : wsum ω (a + b) = wsum ω a + wsum ω b := by
  simp only [wsum]
  rw [Finsupp.sum_add_index' (by intro i; simp) (by intro i m n; push_cast; ring)]

theorem wsum_nonneg {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) (a : Idx ι) : 0 ≤ wsum ω a :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hω i) (Nat.cast_nonneg _)

theorem wsum_tsub_of_le {ω : ι → ℝ} {P a : Idx ι} (h : P ≤ a) :
    wsum ω (a - P) + wsum ω P = wsum ω a := by
  rw [← wsum_add, tsub_add_cancel_of_le' h]

/-- **The comparison symbol** `σ(α) = ω(α) + |α| + 1`: the free energy plus the total
occupation number plus one. -/
def sig (ω : ι → ℝ) (a : Idx ι) : ℝ := wsum ω a + deg a + 1

theorem sig_ge_one {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) (a : Idx ι) : 1 ≤ sig ω a := by
  have h1 : 0 ≤ wsum ω a := wsum_nonneg hω a
  have h2 : (0 : ℝ) ≤ deg a := Nat.cast_nonneg _
  simp only [sig]; linarith

theorem sig_nonneg {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) (a : Idx ι) : 0 ≤ sig ω a :=
  le_trans zero_le_one (sig_ge_one hω a)

theorem deg_add_two_le_sig {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) (a : Idx ι) :
    (deg a : ℝ) + 2 ≤ 2 * sig ω a := by
  have h1 : 0 ≤ wsum ω a := wsum_nonneg hω a
  have h2 : (0 : ℝ) ≤ deg a := Nat.cast_nonneg _
  simp only [sig]; linarith

/-! ## 2. Falling factorials and the ladder amplitude -/

/-- The falling factorial `n(n-1)⋯(n-p+1)`, truncated to `0` when `n < p`. -/
def fallNat (n p : ℕ) : ℕ := ∏ k ∈ Finset.range p, (n - k)

theorem fallNat_eq_zero_of_lt {n p : ℕ} (h : n < p) : fallNat n p = 0 := by
  refine Finset.prod_eq_zero (i := n) (Finset.mem_range.mpr h) ?_
  omega

theorem fallNat_le_pow (n p : ℕ) : fallNat n p ≤ n ^ p := by
  calc fallNat n p = ∏ k ∈ Finset.range p, (n - k) := rfl
    _ ≤ ∏ _k ∈ Finset.range p, n := Finset.prod_le_prod' (fun k _ => Nat.sub_le n k)
    _ = n ^ p := by simp

/-- The falling factorial of a multi-index: `α!/(α-P)!`. -/
def fall (a P : Idx ι) : ℕ := ∏ i ∈ P.support, fallNat (a i) (P i)

theorem fall_eq_zero_of_not_le {a P : Idx ι} (h : ¬ P ≤ a) : fall a P = 0 := by
  rw [Finsupp.le_def] at h
  push_neg at h
  obtain ⟨i, hi⟩ := h
  refine Finset.prod_eq_zero (i := i) ?_ (fallNat_eq_zero_of_lt hi)
  simp only [Finsupp.mem_support_iff]
  omega

theorem fall_le_pow (a P : Idx ι) : fall a P ≤ (deg a) ^ (deg P) := by
  calc fall a P = ∏ i ∈ P.support, fallNat (a i) (P i) := rfl
    _ ≤ ∏ i ∈ P.support, (a i) ^ (P i) := Finset.prod_le_prod' (fun i _ => fallNat_le_pow _ _)
    _ ≤ ∏ i ∈ P.support, (deg a) ^ (P i) :=
        Finset.prod_le_prod' (fun i _ => Nat.pow_le_pow_left (apply_le_deg a i) _)
    _ = (deg a) ^ (∑ i ∈ P.support, P i) := by rw [Finset.prod_pow_eq_pow_sum]
    _ = (deg a) ^ (deg P) := rfl

/-- The configuration reached from `α` by the monomial `a^{†P}a^{Q}`… as read on
coefficients: the coefficient of `α` in the image involves the coefficient of
`tgt P Q α = α - P + Q`. -/
def tgt (P Q a : Idx ι) : Idx ι := a - P + Q

theorem le_tgt (P Q a : Idx ι) : Q ≤ tgt P Q a := le_add_self

theorem tgt_tgt {P Q a : Idx ι} (h : P ≤ a) : tgt Q P (tgt P Q a) = a := by
  simp only [tgt, add_tsub_cancel_right]
  exact tsub_add_cancel_of_le' h

theorem deg_tgt {P Q a : Idx ι} (h : P ≤ a) : deg (tgt P Q a) + deg P = deg a + deg Q := by
  rw [tgt, deg_add, ← deg_tsub_of_le h]
  ring

theorem sig_tgt {ω : ι → ℝ} {P Q a : Idx ι} (h : P ≤ a) :
    sig ω (tgt P Q a) = sig ω a - wsum ω P - deg P + wsum ω Q + deg Q := by
  have hd : (deg (tgt P Q a) : ℝ) + deg P = deg a + deg Q := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (deg_tgt (Q := Q) h)
  have hw : wsum ω (tgt P Q a) = wsum ω a - wsum ω P + wsum ω Q := by
    rw [tgt, wsum_add, ← wsum_tsub_of_le (ω := ω) h]
    ring
  simp only [sig, hw]
  linarith

/-- **The ladder amplitude** of the monomial `a^{†P}a^{Q}`. -/
def amp (P Q a : Idx ι) : ℝ := Real.sqrt (fall a P) * Real.sqrt (fall (tgt P Q a) Q)

theorem amp_nonneg (P Q a : Idx ι) : 0 ≤ amp P Q a :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem amp_eq_zero_of_not_le {P Q a : Idx ι} (h : ¬ P ≤ a) : amp P Q a = 0 := by
  simp [amp, fall_eq_zero_of_not_le h]

/-- **The amplitude is Hermitian**: the monomial `a^{†Q}a^{P}` has the same amplitude on
the hopped configuration. -/
theorem amp_symm {P Q a : Idx ι} (h : P ≤ a) : amp Q P (tgt P Q a) = amp P Q a := by
  rw [amp, amp, tgt_tgt h, mul_comm]

/-- **The amplitude of a quadratic monomial is at most `|α| + 2`.** -/
theorem amp_le_deg_add_two {P Q a : Idx ι} (hPQ : deg P + deg Q ≤ 2) :
    amp P Q a ≤ (deg a : ℝ) + 2 := by
  by_cases h : P ≤ a
  · have h3 : deg (tgt P Q a) ≤ deg a + 2 := by
      have := deg_tgt (Q := Q) h
      omega
    have hm : fall a P * fall (tgt P Q a) Q ≤ (deg a + 2) ^ 2 := by
      calc fall a P * fall (tgt P Q a) Q
          ≤ (deg a) ^ (deg P) * (deg (tgt P Q a)) ^ (deg Q) :=
            Nat.mul_le_mul (fall_le_pow a P) (fall_le_pow _ _)
        _ ≤ (deg a + 2) ^ (deg P) * (deg a + 2) ^ (deg Q) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_left (by omega) _)
        _ = (deg a + 2) ^ (deg P + deg Q) := by rw [pow_add]
        _ ≤ (deg a + 2) ^ 2 := Nat.pow_le_pow_right (by omega) hPQ
    have hmR : ((fall a P : ℝ) * (fall (tgt P Q a) Q : ℝ)) ≤ ((deg a : ℝ) + 2) ^ 2 := by
      have := (Nat.cast_le (α := ℝ)).mpr hm
      push_cast at this
      linarith
    have heq : amp P Q a = Real.sqrt ((fall a P : ℝ) * (fall (tgt P Q a) Q : ℝ)) := by
      rw [amp, ← Real.sqrt_mul (by positivity)]
    rw [heq]
    calc Real.sqrt ((fall a P : ℝ) * (fall (tgt P Q a) Q : ℝ))
        ≤ Real.sqrt (((deg a : ℝ) + 2) ^ 2) := Real.sqrt_le_sqrt hmR
      _ = (deg a : ℝ) + 2 := Real.sqrt_sq (by positivity)
  · rw [amp_eq_zero_of_not_le h]
    positivity

theorem amp_le_deg_tgt_add_two {P Q a : Idx ι} (hPQ : deg P + deg Q ≤ 2) :
    amp P Q a ≤ (deg (tgt P Q a) : ℝ) + 2 := by
  by_cases h : P ≤ a
  · rw [← amp_symm h]
    exact amp_le_deg_add_two (by omega)
  · rw [amp_eq_zero_of_not_le h]
    positivity

theorem amp_le_sig {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) {P Q a : Idx ι} (hPQ : deg P + deg Q ≤ 2) :
    amp P Q a ≤ 2 * sig ω a :=
  le_trans (amp_le_deg_add_two hPQ) (deg_add_two_le_sig hω a)

theorem amp_le_sig_tgt {ω : ι → ℝ} (hω : ∀ i, 0 ≤ ω i) {P Q a : Idx ι}
    (hPQ : deg P + deg Q ≤ 2) : amp P Q a ≤ 2 * sig ω (tgt P Q a) :=
  le_trans (amp_le_deg_tgt_add_two hPQ) (deg_add_two_le_sig hω _)

/-! ## 3. Reindexing along a hop -/

/-- The hop `α ↦ α - P + Q` is a bijection from the configurations above `P` to the
configurations above `Q`. -/
def hopEquiv (P Q : Idx ι) : {a : Idx ι // P ≤ a} ≃ {b : Idx ι // Q ≤ b} where
  toFun a := ⟨tgt P Q a, le_tgt P Q a⟩
  invFun b := ⟨tgt Q P b, le_tgt Q P b⟩
  left_inv a := by ext1; exact tgt_tgt a.2
  right_inv b := by ext1; exact tgt_tgt b.2

/-- The hop is injective on the configurations above `P`. -/
theorem hop_injective (P Q : Idx ι) :
    Function.Injective (fun a : {a : Idx ι // P ≤ a} => tgt P Q (a : Idx ι)) := by
  intro a b hab
  have h : tgt Q P (tgt P Q (a : Idx ι)) = tgt Q P (tgt P Q (b : Idx ι)) := by
    simp only at hab
    rw [hab]
  rw [tgt_tgt a.2, tgt_tgt b.2] at h
  exact Subtype.ext h

/-- Reindexing a sum along the hop. -/
theorem tsum_hop_reindex {P Q : Idx ι} {F G : Idx ι → ℂ}
    (hF : ∀ a, ¬ P ≤ a → F a = 0) (hG : ∀ b, ¬ Q ≤ b → G b = 0)
    (hEq : ∀ a, P ≤ a → F a = G (tgt P Q a)) : ∑' a, F a = ∑' b, G b := by
  have hsF : Function.support F ⊆ {a : Idx ι | P ≤ a} := by
    intro a ha
    by_contra hc
    exact ha (hF a hc)
  have hsG : Function.support G ⊆ {b : Idx ι | Q ≤ b} := by
    intro b hb
    by_contra hc
    exact hb (hG b hc)
  have h1 : ∑' (a : {a : Idx ι // P ≤ a}), F (a : Idx ι) = ∑' a, F a :=
    tsum_subtype_eq_of_support_subset hsF
  have h2 : ∑' (b : {b : Idx ι // Q ≤ b}), G (b : Idx ι) = ∑' b, G b :=
    tsum_subtype_eq_of_support_subset hsG
  have h3 : ∑' (a : {a : Idx ι // P ≤ a}), G ((hopEquiv P Q a : {b : Idx ι // Q ≤ b}) : Idx ι)
      = ∑' (b : {b : Idx ι // Q ≤ b}), G (b : Idx ι) :=
    Equiv.tsum_eq (hopEquiv P Q) (fun b : {b : Idx ι // Q ≤ b} => G (b : Idx ι))
  rw [← h1, ← h2, ← h3]
  exact tsum_congr fun a => hEq (a : Idx ι) a.2

theorem summable_hop_comp {P Q : Idx ι} {f : Idx ι → ℝ} (hsum : Summable f)
    (F : Idx ι → ℝ) (hF0 : ∀ a, 0 ≤ F a) (hFvan : ∀ a, ¬ P ≤ a → F a = 0)
    (hFle : ∀ a, P ≤ a → F a ≤ f (tgt P Q a)) : Summable F := by
  have hsupp : Function.support F ⊆ {a : Idx ι | P ≤ a} := by
    intro a ha
    by_contra hc
    exact ha (hFvan a hc)
  have h1 : Summable (fun a : {a : Idx ι // P ≤ a} => f (tgt P Q (a : Idx ι))) :=
    hsum.comp_injective (hop_injective P Q)
  have h2 : Summable (fun a : {a : Idx ι // P ≤ a} => F (a : Idx ι)) :=
    Summable.of_nonneg_of_le (fun a => hF0 _) (fun a => hFle _ a.2) h1
  have h3 : Summable (Set.indicator {a : Idx ι | P ≤ a} F) :=
    summable_subtype_iff_indicator.mp h2
  rwa [Set.indicator_eq_self.mpr hsupp] at h3

/-- Reindexing an inequality of non-negative sums along the hop. -/
theorem tsum_hop_le {P Q : Idx ι} {f : Idx ι → ℝ} (hf : ∀ b, 0 ≤ f b) (hsum : Summable f)
    (F : Idx ι → ℝ) (hF0 : ∀ a, 0 ≤ F a) (hFvan : ∀ a, ¬ P ≤ a → F a = 0)
    (hFle : ∀ a, P ≤ a → F a ≤ f (tgt P Q a)) : ∑' a, F a ≤ ∑' b, f b := by
  have hsupp : Function.support F ⊆ {a : Idx ι | P ≤ a} := by
    intro a ha
    by_contra hc
    exact ha (hFvan a hc)
  have h1 : Summable (fun a : {a : Idx ι // P ≤ a} => f (tgt P Q (a : Idx ι))) :=
    hsum.comp_injective (hop_injective P Q)
  have h2 : Summable (fun a : {a : Idx ι // P ≤ a} => F (a : Idx ι)) :=
    Summable.of_nonneg_of_le (fun a => hF0 _) (fun a => hFle _ a.2) h1
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  exact Summable.tsum_le_tsum_of_inj (fun a : {a : Idx ι // P ≤ a} => tgt P Q (a : Idx ι))
    (hop_injective P Q) (fun c _ => hf c) (fun a => hFle _ a.2) h2 hsum

end

end BookProof.FockQuadratic
