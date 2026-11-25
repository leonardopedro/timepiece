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
because the Lanczos residual is ~1e-14.  The row's arithmetic is checked by `norm_num`,
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

/-- `g = 2, N ≤ 10`, dimension 420, Lanczos 60 with count witness. -/
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

/-- The row's arithmetic certifies a gap of about `1.221834609`; a margin of `1` fits
    strictly below the Temple lower bound.  (The emitter reports `1.221834608`, agreeing
    to its nine-decimal output precision.) -/
theorem qymG2N10_margin :
    (0 : ℝ) < 1 ∧ 1 ≤ qymG2N10Row.theta - qymG2N10Row.theta_even -
      qymG2N10Row.r ^ 2 / (qymG2N10Row.beta - qymG2N10Row.theta) := by
  constructor
  · norm_num
  · norm_num [qymG2N10Row]

end BookProof.FiniteModelWitness
