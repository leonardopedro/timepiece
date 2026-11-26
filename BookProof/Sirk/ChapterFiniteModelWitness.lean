import Mathlib
import BookProof.Sirk.ChapterTempleSeparationBound

/-!
# Chapter FiniteModelWitness — the count-certified `H_N` witness contract (U5, finite model)

This module packages the strongest statement the recorded `../unfer` campaign actually
supports: a **finite-model** mass-gap witness, with the cutoff `N` as an explicit field.
It composes `RitzCertificate.temple_lower_bound` with
`TempleSeparationBound.gap_of_temple_bounds`; no new estimate is introduced.

`qymG2N10Row` transcribes the emitted fixture of
`unfer/fock_sirk/tests/finite_model_witness_emission.rs`
(`fixtures/finite_model_witness/qym_g2_n10_count.ndjson`), checked by
`scripts/check-finite-model-witness`:

* `θᵒ₀ = -9.02285258839461`, `rᵒ = 1.0810843612259794e-13`,
  `θᵉ₀ = -10.244687196756285`,
* `β = -7.5819940659713465` — a rigorous `λ₂` lower bound in the R-odd sector, obtained
  by the count certificate of `fock_sirk::certificate::certify_spectrum`,
* emitted certified gap `1.2218346083616751`, equal to the exact truncated gap.

`NumericRow.temple_lower` is the Temple correction `r²/(β − θ)`; it is negligible here
because the eigenvector residual is ~1e-13.  The row's arithmetic is checked by `norm_num`,
but the operator-level hypotheses (`SpectralSeparation` for `β`, unit vector with the
recorded Rayleigh quotient and residual, `l_even ≤ θ_even`) are *fields* of
`FiniteModelWitness`: instantiating them for the concrete `H_N` matrix is work in unfer,
not asserted here.

**Boundary.** This proves a positive gap for the operator the data describes — the
truncated `H_N`, at a fixed cutoff — and says nothing about the continuum Hamiltonian,
the regulator limit, or the full-operator `StrongCouplingWitness` of U5.  Axioms:
`propext`, `Classical.choice`, `Quot.sound` only.
-/

noncomputable section

namespace BookProof.FiniteModelWitness

open BookProof.RitzCertificate BookProof.TempleSeparationBound

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The data a count-certified finite solve must supply, together with the operator-level
    hypotheses that make the Temple bound sound. -/
structure FiniteModelCert where
  /-- The coupling of the row (a `Prop`-free datum; `g = 0` is the gapless control). -/
  g : ℝ
  /-- The occupation cutoff `N`: the witness is about `H_N`, not about `H`. -/
  cutoff : ℕ
  /-- The dimension of the explicit sector matrix. -/
  dim : ℕ
  /-- The finite operator being certified. -/
  A : F →L[ℂ] F
  hA : IsSelfAdjoint A
  /-- The two sector ground energies of `A`. -/
  l_odd : ℝ
  l_even : ℝ
  /-- The odd-sector Ritz vector and its data. -/
  x : F
  hx : ‖x‖ = 1
  theta : ℝ
  htheta : rayleigh A x = theta
  r : ℝ
  hr : resid A x = r
  /-- The count-witness level `β`: the spectrum lies in `{l_odd} ∪ [β, ∞)`. -/
  beta : ℝ
  hsep : SpectralSeparation A l_odd beta
  hlt : theta < beta
  /-- Rayleigh–Ritz upper bound for the even-sector ground. -/
  theta_even : ℝ
  heven : l_even ≤ theta_even
  /-- The recorded positive rational margin below the certified lower bound. -/
  margin : ℝ
  hmargin_pos : 0 < margin
  hmargin_le : margin ≤ theta - theta_even - r ^ 2 / (beta - theta)

namespace FiniteModelCert

/-- The Temple correction charged by the row. -/
def delta {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (W : FiniteModelCert (F := F)) : ℝ := W.r ^ 2 / (W.beta - W.theta)

/-- The certified lower bound on the gap of `H_N`. -/
def certified {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (W : FiniteModelCert (F := F)) : ℝ := W.theta - W.theta_even - W.delta

/-- The Temple bound reaches the odd ground, and the variational bound reaches the even
    ground; hence the certified bound is a lower bound on the finite-model gap. -/
theorem certified_le_gap {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (W : FiniteModelCert (F := F)) :
    W.certified ≤ W.l_odd - W.l_even := by
  have htemple : rayleigh W.A W.x - resid W.A W.x ^ 2 / (W.beta - rayleigh W.A W.x) ≤
      W.l_odd := by
    exact temple_lower_bound W.hA W.hsep W.hx (by simpa [W.htheta] using W.hlt)
  have hgap := gap_of_temple_bounds htemple W.heven
  dsimp [certified, delta]
  rw [W.htheta, W.hr] at hgap
  exact hgap

/-- **Soundness of a finite-model witness:** a positive margin proves the gap of `H_N`
    is strictly positive. -/
theorem gap_pos {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (W : FiniteModelCert (F := F)) : 0 < W.l_odd - W.l_even := by
  have hle := W.certified_le_gap
  have hmargin_le : W.margin ≤ W.certified := by
    simpa [certified, delta] using W.hmargin_le
  exact lt_of_lt_of_le (lt_of_lt_of_le W.hmargin_pos hmargin_le) hle

end FiniteModelCert

/-! ## The transcribed `g = 2, N ≤ 10` row (numeric part only) -/

/-- The numbers of one row, transcribed from the emitted campaign output. -/
structure NumericRow where
  g : ℝ
  cutoff : ℕ
  dim : ℕ
  theta : ℝ
  r : ℝ
  theta_even : ℝ
  beta : ℝ
  certified_reported : ℝ

/-- `g = 2, N ≤ 10`, odd dimension 420, dense eigenvectors with count witness. -/
def qymG2N10Row : NumericRow :=
  { g := 2, cutoff := 10, dim := 420,
    theta := -9.02285258839461, r := 1.0810843612259794e-13,
    theta_even := -10.244687196756285,
    beta := -7.5819940659713465, certified_reported := 1.2218346083616751 }

/-- The Temple level clears the Ritz value: the residual ball does not reach `β`. -/
theorem qymG2N10_level : qymG2N10Row.theta < qymG2N10Row.beta := by
  norm_num [qymG2N10Row]

/-- The Temple correction is negligible at the recorded residual. -/
theorem qymG2N10_delta :
    qymG2N10Row.r ^ 2 / (qymG2N10Row.beta - qymG2N10Row.theta) < 1e-20 := by
  norm_num [qymG2N10Row]

/-- The row's arithmetic certifies a gap of about `1.221834608`; a margin of `1` fits
    strictly below the Temple lower bound.  (The emitter reports `1.221834608`, agreeing
    to its nine-decimal output precision.) -/
theorem qymG2N10_margin :
    (0 : ℝ) < 1 ∧ 1 ≤ qymG2N10Row.theta - qymG2N10Row.theta_even -
      qymG2N10Row.r ^ 2 / (qymG2N10Row.beta - qymG2N10Row.theta) := by
  constructor
  · norm_num
  · norm_num [qymG2N10Row]

/-- Strict eigenvalue count for a complete ordered list including multiplicity. -/
noncomputable def countBelow {n : ℕ} (levels : Fin n → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun i => levels i < t).card

theorem ordered_level_bracket {n : ℕ} {levels : Fin n → ℝ} (sorted : Monotone levels)
    (i : Fin n) {lo hi : ℝ} (hl : countBelow levels lo ≤ i.val)
    (hh : i.val < countBelow levels hi) : lo ≤ levels i ∧ levels i < hi := by
  constructor
  · by_contra! h
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => levels j < lo) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (sorted (Finset.mem_Iic.mp hj)).trans_lt h⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    unfold countBelow at hl
    omega
  · by_contra! h
    have hsub : Finset.univ.filter (fun j => levels j < hi) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra! hij
      exact ((sorted hij).trans_lt (Finset.mem_filter.mp hj).2).not_ge h
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    unfold countBelow at hh
    omega

/-- Combine the two reflection blocks. The four count hypotheses are the output
of the external inertia checker on the finite matrices. -/
theorem qymG2N10_ordered_gap {levels : Fin 1001 → ℝ} (sorted : Monotone levels)
    (h₀ : countBelow levels (-10.25) = 0) (h₁ : countBelow levels (-10.234375) = 1)
    (h₂ : countBelow levels (-9.03125) = 1) (h₃ : countBelow levels (-9.015625) = 2) :
    77 / 64 ≤ levels 1 - levels 0 ∧ levels 1 - levels 0 ≤ 79 / 64 := by
  have hg := ordered_level_bracket sorted 0 (lo := -10.25) (hi := -10.234375)
    (by simp [h₀]) (by simp [h₁])
  have he := ordered_level_bracket sorted 1 (lo := -9.03125) (hi := -9.015625)
    (by rw [h₂]; decide) (by rw [h₃]; decide)
  constructor <;> linarith [hg.1, hg.2, he.1, he.2]

/-- In the separate three-profile g=2 packet window, the inertia counts bound the
absolute occupied bottom. Every exact Ritz space containing the common seed has
its Rayleigh infimum between that bottom and the same seed ceiling. -/
theorem packetG2N3_uniform_ritz_margin {levels : Fin 20 → ℝ} (sorted : Monotone levels)
    (hlo : countBelow levels (1181 / 50) = 0) (hhi : countBelow levels (189 / 8) = 1)
    {full trial : Set ℝ} (hfull : IsGLB full (levels 0)) (hsub : trial ⊆ full)
    {estimate seed : ℝ} (htrial : IsGLB trial estimate) (hseed : seed ∈ trial)
    (hceiling : seed < 788 / 25) :
    1181 / 50 ≤ levels 0 ∧ levels 0 < 189 / 8 ∧
      |estimate - levels 0| < 79 / 10 ∧ 79 / 10 < levels 0 := by
  have bracket := ordered_level_bracket sorted 0 (lo := 1181 / 50) (hi := 189 / 8)
    (by simp [hlo]) (by simp [hhi])
  have above : levels 0 ≤ estimate := htrial.2 fun _ hx => hfull.1 (hsub hx)
  have below : estimate ≤ seed := htrial.1 hseed
  rw [abs_of_nonneg (sub_nonneg.mpr above)]
  exact ⟨bracket.1, bracket.2, by linarith [bracket.1], by linarith [bracket.1]⟩

end BookProof.FiniteModelWitness
