import Mathlib
import BookProof.ChapterOperatorSeriesEsa
import BookProof.ChapterFockQuadraticEsa.Part2

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
/-! ## 5. The Hermitian interaction term -/

/-- **The Hermitian interaction term** `g a^{†P}a^{Q} + conj(g) a^{†Q}a^{P}`. -/
def pairOp (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι) (hPQ : deg P + deg Q ≤ 2) :
    maxDom (sig ω) →ₗ[ℂ] L2I (Idx ι) :=
  g • hopOp hω P Q hPQ + (starRingEnd ℂ) g • hopOp hω Q P (by omega)

theorem pairOp_symmetricOn (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι)
    (hPQ : deg P + deg Q ≤ 2) : SymmetricOn (maxDom (sig ω)) (pairOp hω g P Q hPQ) := by
  intro x y
  simp only [pairOp, LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [hopOp_pairing hω hPQ (by omega) x y, hopOp_pairing hω (by omega : deg Q + deg P ≤ 2) hPQ x y]
  simp [RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

theorem pairOp_norm_le (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι) (hPQ : deg P + deg Q ≤ 2)
    (x : maxDom (sig ω)) :
    ‖(pairOp hω g P Q hPQ x : L2I (Idx ι))‖
      ≤ (4 * ‖g‖) * ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := by
  have h1 := hopOp_norm_le hω hPQ x
  have h2 := hopOp_norm_le hω (by omega : deg Q + deg P ≤ 2) x
  have hnn : (0 : ℝ) ≤ ‖(diagMax (sig ω) x : L2I (Idx ι))‖ := norm_nonneg _
  have hcalc : ‖(pairOp hω g P Q hPQ x : L2I (Idx ι))‖
      ≤ ‖g‖ * ‖(hopOp hω P Q hPQ x : L2I (Idx ι))‖
        + ‖g‖ * ‖(hopOp hω Q P (by omega : deg Q + deg P ≤ 2) x : L2I (Idx ι))‖ := by
    simp only [pairOp, LinearMap.add_apply, LinearMap.smul_apply]
    refine le_trans (norm_add_le _ _) ?_
    simp [norm_smul]
  nlinarith [norm_nonneg g, hcalc, h1, h2]

/-- **The commutator-form bound** of the interaction term. -/
theorem pairOp_commForm_le (hω : ∀ i, 0 ≤ ω i) (g : ℂ) (P Q : Idx ι)
    (hPQ : deg P + deg Q ≤ 2) (x : maxDom (sig ω)) :
    |commForm (pairOp hω g P Q hPQ) (diagMax (sig ω)) x|
      ≤ (4 * ‖g‖ * (wsum ω P + wsum ω Q + 2)) * quadForm (diagMax (sig ω)) x := by
  classical
  have hQP : deg Q + deg P ≤ 2 := by omega
  have hc0 : ∀ b : Idx ι, 0 ≤ sig ω b := fun b => sig_nonneg hω b
  set xb : Idx ι → ℂ := ((x : L2I (Idx ι)) : Idx ι → ℂ) with hxb
  set q : ℝ := quadForm (diagMax (sig ω)) x with hqdef
  have hq0 : 0 ≤ q := diagMax_quadForm_nonneg (sig ω) hc0 x
  set W : ℝ := wsum ω P + wsum ω Q + 2 with hWdef
  have hW0 : 0 ≤ W := by
    have h1 : (0 : ℝ) ≤ wsum ω P := wsum_nonneg hω _
    have h2 : (0 : ℝ) ≤ wsum ω Q := wsum_nonneg hω _
    simp only [hWdef]; linarith
  set t : Idx ι → ℂ := hopT P Q xb with htdef
  set A : ℂ := inner ℂ (hopOp hω P Q hPQ x : L2I (Idx ι))
    (diagMax (sig ω) x : L2I (Idx ι)) with hAdef
  set B : ℂ := inner ℂ (hopOp hω Q P hQP x : L2I (Idx ι))
    (diagMax (sig ω) x : L2I (Idx ι)) with hBdef
  -- the two matrix elements as sums over the configurations above `P`
  have hA : HasSum (fun b : {b : Idx ι // P ≤ b} => (sig ω (b : Idx ι) : ℂ) * t (b : Idx ι)) A := by
    have h := lp.hasSum_inner (𝕜 := ℂ) (hopOp hω P Q hPQ x : L2I (Idx ι))
      (diagMax (sig ω) x : L2I (Idx ι))
    have hvan : ∀ b : Idx ι, b ∉ Set.range (Subtype.val : {b : Idx ι // P ≤ b} → Idx ι) →
        (inner ℂ (((hopOp hω P Q hPQ x : L2I (Idx ι)) : Idx ι → ℂ) b)
          (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) b) : ℂ) = 0 := by
      intro b hb
      have hnp : ¬ P ≤ b := fun hle => hb ⟨⟨b, hle⟩, rfl⟩
      simp [RCLike.inner_apply, amp_eq_zero_of_not_le hnp]
    have h2 := ((Subtype.coe_injective (p := fun b : Idx ι => P ≤ b)).hasSum_iff hvan).mpr h
    refine h2.congr_fun ?_
    intro b
    simp only [Function.comp_apply, RCLike.inner_apply, hopOp_coe, diagMax_coe, htdef, hopT,
      map_mul, Complex.conj_ofReal, hxb]
    ring
  have hB : HasSum (fun b : {b : Idx ι // P ≤ b} =>
      (sig ω (tgt P Q (b : Idx ι)) : ℂ) * (starRingEnd ℂ) (t (b : Idx ι))) B := by
    have h := lp.hasSum_inner (𝕜 := ℂ) (hopOp hω Q P hQP x : L2I (Idx ι))
      (diagMax (sig ω) x : L2I (Idx ι))
    have hvan : ∀ a : Idx ι,
        a ∉ Set.range (fun b : {b : Idx ι // P ≤ b} => tgt P Q (b : Idx ι)) →
        (inner ℂ (((hopOp hω Q P hQP x : L2I (Idx ι)) : Idx ι → ℂ) a)
          (((diagMax (sig ω) x : L2I (Idx ι)) : Idx ι → ℂ) a) : ℂ) = 0 := by
      intro a ha
      have hnq : ¬ Q ≤ a := fun hle => ha ⟨⟨tgt Q P a, le_tgt Q P a⟩, tgt_tgt hle⟩
      simp [RCLike.inner_apply, amp_eq_zero_of_not_le hnq]
    have h2 := ((hop_injective P Q).hasSum_iff hvan).mpr h
    refine h2.congr_fun ?_
    intro b
    simp only [Function.comp_apply, RCLike.inner_apply, hopOp_coe, diagMax_coe]
    rw [amp_symm b.2, tgt_tgt b.2]
    simp only [htdef, hopT, map_mul, Complex.conj_ofReal, Complex.conj_conj, hxb]
    ring
  -- the imaginary part of the matrix element of the Hermitian combination
  have hcomb : HasSum (fun b : {b : Idx ι // P ≤ b} =>
      (starRingEnd ℂ) g * ((sig ω (b : Idx ι) : ℂ) * t (b : Idx ι))
        + g * ((sig ω (tgt P Q (b : Idx ι)) : ℂ) * (starRingEnd ℂ) (t (b : Idx ι))))
      ((starRingEnd ℂ) g * A + g * B) := (hA.mul_left _).add (hB.mul_left _)
  set R : {b : Idx ι // P ≤ b} → ℝ := fun b =>
    (sig ω (b : Idx ι) - sig ω (tgt P Q (b : Idx ι))) * ((starRingEnd ℂ) g * t (b : Idx ι)).im
    with hRdef
  have him : HasSum R ((starRingEnd ℂ) g * A + g * B).im := by
    refine (Complex.hasSum_im hcomb).congr_fun ?_
    intro b
    set z : ℂ := (starRingEnd ℂ) g * t (b : Idx ι) with hz
    have hrw : (starRingEnd ℂ) g * ((sig ω (b : Idx ι) : ℂ) * t (b : Idx ι))
        + g * ((sig ω (tgt P Q (b : Idx ι)) : ℂ) * (starRingEnd ℂ) (t (b : Idx ι)))
        = (sig ω (b : Idx ι) : ℂ) * z + (sig ω (tgt P Q (b : Idx ι)) : ℂ) * (starRingEnd ℂ) z := by
      simp only [hz, map_mul, Complex.conj_conj]
      ring
    rw [hrw, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, Complex.conj_im, hRdef]
    ring
  -- the two halves of the comparison quadratic form
  have hquad : HasSum (fun b : Idx ι => sig ω b * ‖xb b‖ ^ 2) q :=
    diagMax_hasSum_quadForm (sig ω) x
  have hquad0 : ∀ b : Idx ι, 0 ≤ sig ω b * ‖xb b‖ ^ 2 := fun b =>
    mul_nonneg (hc0 b) (sq_nonneg _)
  have huS : Summable (fun b : {b : Idx ι // P ≤ b} =>
      sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2) :=
    hquad.summable.subtype _
  have hvS : Summable (fun b : {b : Idx ι // P ≤ b} =>
      sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) :=
    hquad.summable.comp_injective (hop_injective P Q)
  have huSle : (∑' b : {b : Idx ι // P ≤ b}, sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2) ≤ q := by
    rw [← hquad.tsum_eq]
    exact Summable.tsum_le_tsum_of_inj (Subtype.val : {b : Idx ι // P ≤ b} → Idx ι)
      Subtype.coe_injective (fun c _ => hquad0 c) (fun b => le_refl _) huS hquad.summable
  have hvSle : (∑' b : {b : Idx ι // P ≤ b},
      sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) ≤ q := by
    rw [← hquad.tsum_eq]
    exact Summable.tsum_le_tsum_of_inj (fun b : {b : Idx ι // P ≤ b} => tgt P Q (b : Idx ι))
      (hop_injective P Q) (fun c _ => hquad0 c) (fun b => le_refl _) hvS hquad.summable
  -- the pointwise bound
  have hRle : ∀ b : {b : Idx ι // P ≤ b}, |R b| ≤ (‖g‖ * W) *
      (sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2
        + sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) := by
    intro b
    have him1 : |((starRingEnd ℂ) g * t (b : Idx ι)).im| ≤ ‖g‖ * ‖t (b : Idx ι)‖ := by
      calc |((starRingEnd ℂ) g * t (b : Idx ι)).im|
          ≤ ‖(starRingEnd ℂ) g * t (b : Idx ι)‖ := Complex.abs_im_le_norm _
        _ = ‖g‖ * ‖t (b : Idx ι)‖ := by rw [norm_mul, RCLike.norm_conj]
    have hsig := abs_sig_sub_sig_tgt_le hω (P := P) (Q := Q) hPQ b.2
    have hnt : ‖t (b : Idx ι)‖
        = amp P Q (b : Idx ι) * ‖xb (tgt P Q (b : Idx ι))‖ * ‖xb (b : Idx ι)‖ := by
      rw [htdef]; exact norm_hopT P Q xb (b : Idx ι)
    have hamp := amp_mul_le hω (P := P) (Q := Q) hPQ (b : Idx ι)
      ‖xb (b : Idx ι)‖ ‖xb (tgt P Q (b : Idx ι))‖
    have hg0 : (0 : ℝ) ≤ ‖g‖ := norm_nonneg _
    have hnt0 : (0 : ℝ) ≤ ‖t (b : Idx ι)‖ := norm_nonneg _
    have habs : |R b| ≤ |sig ω (b : Idx ι) - sig ω (tgt P Q (b : Idx ι))|
        * |((starRingEnd ℂ) g * t (b : Idx ι)).im| := by
      rw [hRdef, abs_mul]
    have hstep : |sig ω (b : Idx ι) - sig ω (tgt P Q (b : Idx ι))|
        * |((starRingEnd ℂ) g * t (b : Idx ι)).im| ≤ W * (‖g‖ * ‖t (b : Idx ι)‖) := by
      refine mul_le_mul hsig him1 (abs_nonneg _) hW0
    have hfin : W * (‖g‖ * ‖t (b : Idx ι)‖) ≤ (‖g‖ * W) *
        (sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2
          + sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) := by
      rw [hnt]
      have := mul_le_mul_of_nonneg_left hamp (mul_nonneg hg0 hW0)
      nlinarith [this]
    linarith [habs, hstep, hfin]
  have habsS : Summable (fun b : {b : Idx ι // P ≤ b} => |R b|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hRle ?_
    exact (huS.add hvS).mul_left _
  have hRsum : Summable R := by
    have := habsS
    exact Summable.of_norm (by simpa [Real.norm_eq_abs] using this)
  have hbound : |((starRingEnd ℂ) g * A + g * B).im| ≤ (‖g‖ * W) * (2 * q) := by
    calc |((starRingEnd ℂ) g * A + g * B).im| = |∑' b : {b : Idx ι // P ≤ b}, R b| := by
          rw [him.tsum_eq]
      _ ≤ ∑' b : {b : Idx ι // P ≤ b}, |R b| := by
          have h := norm_tsum_le_tsum_norm (f := R) (by simpa [Real.norm_eq_abs] using habsS)
          simpa [Real.norm_eq_abs] using h
      _ ≤ ∑' b : {b : Idx ι // P ≤ b}, (‖g‖ * W) *
            (sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2
              + sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) :=
          Summable.tsum_le_tsum hRle habsS ((huS.add hvS).mul_left _)
      _ = (‖g‖ * W) * ((∑' b : {b : Idx ι // P ≤ b}, sig ω (b : Idx ι) * ‖xb (b : Idx ι)‖ ^ 2)
            + ∑' b : {b : Idx ι // P ≤ b},
              sig ω (tgt P Q (b : Idx ι)) * ‖xb (tgt P Q (b : Idx ι))‖ ^ 2) := by
          rw [(huS.add hvS).tsum_mul_left, huS.tsum_add hvS]
      _ ≤ (‖g‖ * W) * (2 * q) := by
          have hg0 : (0 : ℝ) ≤ ‖g‖ := norm_nonneg _
          have : (0 : ℝ) ≤ ‖g‖ * W := mul_nonneg hg0 hW0
          nlinarith [huSle, hvSle]
  -- assemble
  have hinner : (inner ℂ (pairOp hω g P Q hPQ x : L2I (Idx ι))
      (diagMax (sig ω) x : L2I (Idx ι)) : ℂ) = (starRingEnd ℂ) g * A + g * B := by
    simp only [pairOp, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_smul_left,
      hAdef, hBdef, Complex.conj_conj]
  rw [commForm_eq_neg_two_im, hinner, abs_mul]
  simp only [abs_neg, abs_two]
  nlinarith [hbound, hq0, norm_nonneg g, hW0]


end

end BookProof.FockQuadratic
