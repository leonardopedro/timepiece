import Mathlib
import BookProof.ChapterOperatorSeriesEsa
import BookProof.ChapterFockQuadraticEsa.Part1

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
/-! ## 4. The elementary monomial as an operator -/

variable {ω : ι → ℝ}

/-- The coefficientwise action of the monomial `a^{†P}a^{Q}`. -/
def hopFun (P Q : Idx ι) (x : Idx ι → ℂ) : Idx ι → ℂ :=
  fun b => (amp P Q b : ℂ) * x (tgt P Q b)

/-- The square-summability of the coefficients of an `ℓ²` state, as a `HasSum`. -/
theorem hasSum_normSq {α : Type*} (f : L2I α) :
    HasSum (fun k => ‖(f : α → ℂ) k‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (E := fun _ : α => ℂ) (by norm_num) f
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at h
  simpa [Real.rpow_natCast] using h

/-- The pointwise bound behind every estimate of this module: the coefficient of the
monomial at `β` is at most twice the coefficient of the comparison operator at the hopped
configuration. -/
theorem hop_pointwise (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (x : maxDom (sig ω)) (a : Idx ι) :
    ‖hopFun P Q ((x : L2I (Idx ι)) : Idx ι → ℂ) a‖ ^ 2
      ≤ 4 * ‖((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q a)‖ ^ 2 := by
  have hamp : amp P Q a ≤ 2 * sig ω (tgt P Q a) := amp_le_sig_tgt hω hPQ
  have h0 : 0 ≤ amp P Q a := amp_nonneg _ _ _
  have hxy : ‖((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q a)‖
      = sig ω (tgt P Q a) * ‖((x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q a)‖ := by
    simp [diagMax_coe, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sig_nonneg hω (tgt P Q a))]
  have hnorm : ‖hopFun P Q ((x : L2I (Idx ι)) : Idx ι → ℂ) a‖
      = amp P Q a * ‖((x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q a)‖ := by
    simp [hopFun, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  rw [hnorm, hxy]
  have hx0 : 0 ≤ ‖((x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q a)‖ := norm_nonneg _
  have hs0 : 0 ≤ sig ω (tgt P Q a) := sig_nonneg hω _
  have hsq : amp P Q a ^ 2 ≤ (2 * sig ω (tgt P Q a)) ^ 2 := by nlinarith
  calc (amp P Q a * ‖((x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q a)‖) ^ 2
      = amp P Q a ^ 2 * ‖((x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q a)‖ ^ 2 := by ring
    _ ≤ (2 * sig ω (tgt P Q a)) ^ 2 * ‖((x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q a)‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = 4 * (sig ω (tgt P Q a) * ‖((x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q a)‖) ^ 2 := by ring

theorem hop_memLp (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (x : maxDom (sig ω)) :
    Memℓp (hopFun P Q ((x : L2I (Idx ι)) : Idx ι → ℂ)) 2 := by
  refine memLpTwo_of_summable_normSq ?_
  refine summable_hop_comp (P := P) (Q := Q)
    ((summable_normSq (diagMax (sig ω) x)).mul_left 4) _ (fun a => by positivity) ?_ ?_
  · intro a ha
    simp [hopFun, amp_eq_zero_of_not_le ha]
  · intro a _
    exact hop_pointwise hω hPQ x a

/-- **The elementary monomial** `a^{†P}a^{Q}` on the maximal domain of the comparison
symbol. -/
def hopOp (hω : ∀ i, 0 ≤ ω i) (P Q : Idx ι) (hPQ : deg P + deg Q ≤ 2) :
    maxDom (sig ω) →ₗ[ℂ] L2I (Idx ι) where
  toFun x := ⟨hopFun P Q ((x : L2I (Idx ι)) : Idx ι → ℂ), hop_memLp hω hPQ x⟩
  map_add' x y := by
    refine lp.ext (funext fun b => ?_)
    simp only [hopFun, lp.coeFn_add, Pi.add_apply, Submodule.coe_add]
    ring
  map_smul' r x := by
    refine lp.ext (funext fun b => ?_)
    simp only [hopFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Submodule.coe_smul]
    ring

@[simp] theorem hopOp_coe (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (x : maxDom (sig ω)) (b : Idx ι) :
    ((hopOp hω P Q hPQ x : L2I (Idx ι)) : Idx ι → ℂ) b
      = (amp P Q b : ℂ) * ((x : L2I (Idx ι)) : Idx ι → ℂ) (tgt P Q b) := rfl

/-- **The relative bound**: the monomial is dominated by the comparison operator. -/
theorem hopOp_norm_le (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (x : maxDom (sig ω)) :
    ‖(hopOp hω P Q hPQ x : L2I (Idx ι))‖ ≤ 2 * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := by
  have h1 := hasSum_normSq (hopOp hω P Q hPQ x : L2I (Idx ι))
  have h2 := hasSum_normSq (diagMax (sig ω) x : L2I (Idx ι))
  have hsq : ‖(hopOp hω P Q hPQ x : L2I (Idx ι))‖ ^ 2
      ≤ 4 * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ ^ 2 := by
    have h4 : (4 : ℝ) * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ ^ 2
        = ∑' γ, 4 * ‖((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) γ‖ ^ 2 := by
      rw [← h2.tsum_eq, tsum_mul_left]
    rw [← h1.tsum_eq, h4]
    refine tsum_hop_le (P := P) (Q := Q) (fun b => by positivity)
      ((summable_normSq (diagMax (sig ω) x)).mul_left 4) _ (fun a => by positivity) ?_ ?_
    · intro a ha
      simp [hopOp_coe, amp_eq_zero_of_not_le ha]
    · intro a _
      exact hop_pointwise hω hPQ x a
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg (hopOp hω P Q hPQ x : L2I (Idx ι)),
    norm_nonneg (diagMax (sig ω) x : L2I (Idx ι))]

/-- **The adjoint relation**: `a^{†Q}a^{P}` is the adjoint of `a^{†P}a^{Q}`. -/
theorem hopOp_pairing (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (hQP : deg Q + deg P ≤ 2) (x y : maxDom (sig ω)) :
    (inner ℂ (hopOp hω P Q hPQ x : L2I (Idx ι)) (y : L2I (Idx ι)) : ℂ)
      = inner ℂ (x : L2I (Idx ι)) (hopOp hω Q P hQP y : L2I (Idx ι)) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_hop_reindex (P := P) (Q := Q) ?_ ?_ ?_
  · intro b hb
    simp [RCLike.inner_apply, amp_eq_zero_of_not_le hb]
  · intro a ha
    simp [RCLike.inner_apply, amp_eq_zero_of_not_le ha]
  · intro a ha
    simp only [RCLike.inner_apply, hopOp_coe, map_mul, Complex.conj_ofReal]
    rw [amp_symm ha, tgt_tgt ha]
    ring

/-! ### The pairing symbol -/

/-- The scalar symbol `t(β) = amp(β) · conj(x(β - P + Q)) · x(β)` controlling both the
matrix element of the monomial and its commutator with the comparison operator. -/
def hopT (P Q : Idx ι) (x : Idx ι → ℂ) : Idx ι → ℂ :=
  fun b => (amp P Q b : ℂ) * (starRingEnd ℂ) (x (tgt P Q b)) * x b

theorem norm_hopT (P Q : Idx ι) (x : Idx ι → ℂ) (b : Idx ι) :
    ‖hopT P Q x b‖ = amp P Q b * ‖x (tgt P Q b)‖ * ‖x b‖ := by
  simp [hopT, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (amp_nonneg P Q b)]

/-- **The AM–GM step**: the ladder amplitude is dominated by the comparison symbol at the
two ends of the hop. -/
theorem amp_mul_le (hω : ∀ i, 0 ≤ ω i) {P Q : Idx ι} (hPQ : deg P + deg Q ≤ 2) (b : Idx ι)
    (p r : ℝ) :
    amp P Q b * r * p ≤ sig ω b * p ^ 2 + sig ω (tgt P Q b) * r ^ 2 := by
  have h1 : amp P Q b ≤ 2 * sig ω b := amp_le_sig hω hPQ
  have h2 : amp P Q b ≤ 2 * sig ω (tgt P Q b) := amp_le_sig_tgt hω hPQ
  have h0 : 0 ≤ amp P Q b := amp_nonneg _ _ _
  have hs1 : 0 ≤ sig ω b := sig_nonneg hω _
  have hs2 : 0 ≤ sig ω (tgt P Q b) := sig_nonneg hω _
  refine le_of_sq_le_sq ?_ (by positivity)
  have hamp : amp P Q b ^ 2 ≤ 4 * (sig ω b * sig ω (tgt P Q b)) := by nlinarith
  nlinarith [sq_nonneg (sig ω b * p ^ 2 - sig ω (tgt P Q b) * r ^ 2), sq_nonneg (p * r),
    sq_nonneg p, sq_nonneg r]

/-- The comparison symbol changes by at most `ω(P) + ω(Q) + 2` along a hop. -/
theorem abs_sig_sub_sig_tgt_le (hω : ∀ i, 0 ≤ ω i) {P Q b : Idx ι} (hPQ : deg P + deg Q ≤ 2)
    (h : P ≤ b) : |sig ω b - sig ω (tgt P Q b)| ≤ wsum ω P + wsum ω Q + 2 := by
  have hst := sig_tgt (ω := ω) (P := P) (Q := Q) h
  have h1 : (0 : ℝ) ≤ wsum ω P := wsum_nonneg hω _
  have h2 : (0 : ℝ) ≤ wsum ω Q := wsum_nonneg hω _
  have h3 : (deg P : ℝ) + (deg Q : ℝ) ≤ 2 := by
    exact_mod_cast (by exact_mod_cast hPQ : deg P + deg Q ≤ 2)
  have h4 : (0 : ℝ) ≤ (deg P : ℝ) := Nat.cast_nonneg _
  have h5 : (0 : ℝ) ≤ (deg Q : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> [linarith; linarith]

end

end BookProof.FockQuadratic
