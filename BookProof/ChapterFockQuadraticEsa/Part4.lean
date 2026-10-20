import Mathlib
import BookProof.ChapterOperatorSeriesEsa
import BookProof.ChapterFockQuadraticEsa.Part3

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
variable {ω : ι → ℝ}
/-! ## 6. The free Hamiltonian -/

/-- **The free Hamiltonian** `∑ᵢ ωᵢ aᵢ†aᵢ`: multiplication by the free energy. -/
def freeOp (hω : ∀ i, 0 ≤ ω i) : maxDom (sig ω) →ₗ[ℂ] L2I (Idx ι) where
  toFun x := ⟨fun b => (wsum ω b : ℂ) * ((x : L2I (Idx ι)) : Idx ι → ℂ) b, by
    refine memLpTwo_of_le (diagMax (sig ω) x) fun b => ?_
    have h1 : |wsum ω b| ≤ |sig ω b| := by
      rw [abs_of_nonneg (wsum_nonneg hω b), abs_of_nonneg (sig_nonneg hω b)]
      have h2 : (0 : ℝ) ≤ deg b := Nat.cast_nonneg _
      simp only [sig]; linarith
    simp only [diagMax_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)⟩
  map_add' x y := by
    refine lp.ext (funext fun b => ?_)
    simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add]
    ring
  map_smul' r x := by
    refine lp.ext (funext fun b => ?_)
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Submodule.coe_smul]
    ring

@[simp] theorem freeOp_coe (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) (b : Idx ι) :
    ((freeOp hω x : L2I (Idx ι)) : Idx ι → ℂ) b
      = (wsum ω b : ℂ) * ((x : L2I (Idx ι)) : Idx ι → ℂ) b := rfl

theorem freeOp_symmetricOn (hω : ∀ i, 0 ≤ ω i) :
    SymmetricOn (maxDom (sig ω)) (freeOp hω) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun b => ?_
  simp only [RCLike.inner_apply, freeOp_coe, map_mul, Complex.conj_ofReal]
  ring

theorem freeOp_norm_le (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) :
    ‖(freeOp hω x : L2I (Idx ι))‖ ≤ 1 * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := by
  have h1 := hasSum_normSq (freeOp hω x : L2I (Idx ι))
  have h2 := hasSum_normSq (diagMax (sig ω) x : L2I (Idx ι))
  have hpt : ∀ b : Idx ι, ‖((freeOp hω x : L2I (Idx ι)) : Idx ι → ℂ) b‖ ^ 2
      ≤ ‖((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) b‖ ^ 2 := by
    intro b
    have hb : |wsum ω b| ≤ |sig ω b| := by
      rw [abs_of_nonneg (wsum_nonneg hω b), abs_of_nonneg (sig_nonneg hω b)]
      have h3 : (0 : ℝ) ≤ deg b := Nat.cast_nonneg _
      simp only [sig]; linarith
    have hx : (0 : ℝ) ≤ ‖((x : L2I (Idx ι)) : Idx ι → ℂ) b‖ := norm_nonneg _
    simp only [freeOp_coe, diagMax_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  have hsq : ‖(freeOp hω x : L2I (Idx ι))‖ ^ 2 ≤ ‖(diagMax (sig ω) x : L2I (Idx ι))‖ ^ 2 := by
    rw [← h1.tsum_eq, ← h2.tsum_eq]
    exact Summable.tsum_le_tsum hpt h1.summable h2.summable
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg (freeOp hω x : L2I (Idx ι)),
    norm_nonneg (diagMax (sig ω) x : L2I (Idx ι))]

/-- The free Hamiltonian commutes with the comparison operator. -/
theorem freeOp_commForm (hω : ∀ i, 0 ≤ ω i) (x : maxDom (sig ω)) :
    commForm (freeOp hω) (diagMax (sig ω)) x = 0 := by
  rw [commForm_eq_neg_two_im]
  have h := lp.hasSum_inner (𝕜 := ℂ) (freeOp hω x : L2I (Idx ι))
    (diagMax (sig ω) x : L2I (Idx ι))
  have him := Complex.hasSum_im h
  have hzero : ∀ b : Idx ι,
      (inner ℂ (((freeOp hω x : L2I (Idx ι)) : Idx ι → ℂ) b)
        (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) b) : ℂ).im = 0 := by
    intro b
    have hb : (inner ℂ (((freeOp hω x : L2I (Idx ι)) : Idx ι → ℂ) b)
        (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) b) : ℂ)
        = ((wsum ω b * sig ω b : ℝ) : ℂ) *
          ((starRingEnd ℂ) (((x : L2I (Idx ι)) : Idx ι → ℂ) b)
            * ((x : L2I (Idx ι)) : Idx ι → ℂ) b) := by
      simp only [RCLike.inner_apply, freeOp_coe, diagMax_coe, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    have hcc : (starRingEnd ℂ) (((x : L2I (Idx ι)) : Idx ι → ℂ) b)
        * ((x : L2I (Idx ι)) : Idx ι → ℂ) b
        = ((Complex.normSq (((x : L2I (Idx ι)) : Idx ι → ℂ) b) : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
    rw [hb, hcc, ← Complex.ofReal_mul, Complex.ofReal_im]
  have hz : HasSum (fun _ : Idx ι => (0 : ℝ))
      ((inner ℂ (freeOp hω x : L2I (Idx ι)) (diagMax (sig ω) x : L2I (Idx ι)) : ℂ).im) := by
    simpa only [hzero] using him
  rw [hz.unique hasSum_zero]
  ring

/-! ## 7. The Hamiltonian and its essential self-adjointness -/

variable {κ : Type*}

/-- **The full Hamiltonian**: free part plus the summable family of Hermitian interaction
terms. -/
def fockH (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2)
    (hsum : Summable fun k => ‖g k‖ * (wsum ω (P k) + wsum ω (Q k) + 2)) :
    maxDom (sig ω) →ₗ[ℂ] L2I (Idx ι) :=
  freeOp hω +
    seriesOp (fun k => pairOp hω (g k) (P k) (Q k) (hPQ k)) (fun k => 4 * ‖g k‖)
      (fun k x => pairOp_norm_le hω (g k) (P k) (Q k) (hPQ k) x)
      (by
        refine Summable.of_nonneg_of_le (fun k => by positivity)
          (fun k => ?_) (hsum.mul_left 4)
        have h1 : (0 : ℝ) ≤ wsum ω (P k) := wsum_nonneg hω _
        have h2 : (0 : ℝ) ≤ wsum ω (Q k) := wsum_nonneg hω _
        have h3 : (0 : ℝ) ≤ ‖g k‖ := norm_nonneg _
        nlinarith)

/-- **Headline.**  The general quadratic Hamiltonian of a boson field with an arbitrary
mode set, an arbitrary non-negative free dispersion and an arbitrary weighted-summable
family of quadratic interaction terms is essentially self-adjoint on the finite-particle
core of the Fock space. -/
theorem fockH_essentiallySelfAdjointOn_core (hω : ∀ i, 0 ≤ ω i) (P Q : κ → Idx ι) (g : κ → ℂ)
    (hPQ : ∀ k, deg (P k) + deg (Q k) ≤ 2)
    (hsum : Summable fun k => ‖g k‖ * (wsum ω (P k) + wsum ω (Q k) + 2)) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((fockH hω P Q g hPQ hsum).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig ω)))) := by
  classical
  have hc0 : ∀ b : Idx ι, 0 ≤ sig ω b := fun b => sig_nonneg hω b
  set T : κ → (maxDom (sig ω) →ₗ[ℂ] L2I (Idx ι)) :=
    fun k => pairOp hω (g k) (P k) (Q k) (hPQ k) with hT
  set A : κ → ℝ := fun k => 4 * ‖g k‖ with hAdef
  have hnorm : ∀ (k : κ) (x : maxDom (sig ω)),
      ‖(T k x : L2I (Idx ι))‖ ≤ A k * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ :=
    fun k x => pairOp_norm_le hω (g k) (P k) (Q k) (hPQ k) x
  have hA : Summable A := by
    refine Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => ?_) (hsum.mul_left 4)
    have h1 : (0 : ℝ) ≤ wsum ω (P k) := wsum_nonneg hω _
    have h2 : (0 : ℝ) ≤ wsum ω (Q k) := wsum_nonneg hω _
    have h3 : (0 : ℝ) ≤ ‖g k‖ := norm_nonneg _
    nlinarith
  have hfock : fockH hω P Q g hPQ hsum = freeOp hω + seriesOp T A hnorm hA := rfl
  set B : κ → ℝ := fun k => 4 * ‖g k‖ * (wsum ω (P k) + wsum ω (Q k) + 2) with hBdef
  have hB0 : ∀ k, 0 ≤ B k := by
    intro k
    have h1 : (0 : ℝ) ≤ wsum ω (P k) := wsum_nonneg hω _
    have h2 : (0 : ℝ) ≤ wsum ω (Q k) := wsum_nonneg hω _
    have h3 : (0 : ℝ) ≤ ‖g k‖ := norm_nonneg _
    simp only [hBdef]
    positivity
  have hBsum : Summable B := by
    have := hsum.mul_left 4
    refine this.congr fun k => ?_
    simp only [hBdef]
    ring
  have hcomm : ∀ (k : κ) (x : maxDom (sig ω)),
      |commForm (T k) (diagMax (sig ω)) x| ≤ B k * quadForm (diagMax (sig ω)) x := by
    intro k x
    have h := pairOp_commForm_le hω (g k) (P k) (Q k) (hPQ k) x
    simpa [hBdef, hT, mul_assoc] using h
  rw [hfock]
  refine essentiallySelfAdjointOn_finiteModes_of_bounds (sig ω) hc0 _
    (1 + ∑' k, A k) (∑' k, B k) (tsum_nonneg hB0) ?_ ?_ ?_
  · intro x y
    have h1 := freeOp_symmetricOn hω x y
    have h2 := seriesOp_symmetricOn hnorm hA
      (fun k => pairOp_symmetricOn hω (g k) (P k) (Q k) (hPQ k)) x y
    simp only [LinearMap.add_apply, inner_add_left, inner_add_right, h1, h2]
  · intro x
    have h1 := freeOp_norm_le hω x
    have h2 := seriesOp_norm_le hnorm hA x
    have hn : (0 : ℝ) ≤ ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := norm_nonneg _
    have hadd : ‖((freeOp hω + seriesOp T A hnorm hA) x : L2I (Idx ι))‖
        ≤ ‖(freeOp hω x : L2I (Idx ι))‖ + ‖(seriesOp T A hnorm hA x : L2I (Idx ι))‖ := by
      simpa only [LinearMap.add_apply] using
        norm_add_le (freeOp hω x : L2I (Idx ι)) (seriesOp T A hnorm hA x : L2I (Idx ι))
    nlinarith [hadd, h1, h2]
  · intro x
    have hq : 0 ≤ quadForm (diagMax (sig ω)) x := diagMax_quadForm_nonneg (sig ω) hc0 x
    have hsplit := commForm_add (freeOp hω) (seriesOp T A hnorm hA) (diagMax (sig ω)) x
    have hfree := freeOp_commForm hω x
    have hser := seriesOp_commForm_le hnorm hA hBsum hcomm
      (fun y => diagMax_quadForm_nonneg (sig ω) hc0 y) x
    rw [hsplit, hfree, zero_add]
    exact hser


end

end BookProof.FockQuadratic
