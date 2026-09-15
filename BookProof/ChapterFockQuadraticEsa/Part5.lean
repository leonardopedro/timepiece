import Mathlib
import BookProof.ChapterOperatorSeriesEsa
import BookProof.ChapterFockQuadraticEsa.Part4

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
variable {κ : Type*}
/-! ## 8. The Bogoliubov specialization -/

/-- The pair-creation multi-index of the monomial `a†ₘ a†ₙ`. -/
def pairIdx (m n : ι) : Idx ι := Finsupp.single m 1 + Finsupp.single n 1

@[simp] theorem deg_single (i : ι) (k : ℕ) : deg (Finsupp.single i k) = k := by
  simp [deg, Finsupp.sum_single_index]

theorem wsum_single (ω : ι → ℝ) (i : ι) (k : ℕ) : wsum ω (Finsupp.single i k) = ω i * k := by
  simp [wsum, Finsupp.sum_single_index]

@[simp] theorem deg_pairIdx (m n : ι) : deg (pairIdx m n) = 2 := by
  rw [pairIdx, deg_add, deg_single, deg_single]

@[simp] theorem deg_idx_zero : deg (0 : Idx ι) = 0 := by simp [deg]

@[simp] theorem wsum_idx_zero (ω : ι → ℝ) : wsum ω (0 : Idx ι) = 0 := by simp [wsum]

theorem wsum_pairIdx (ω : ι → ℝ) (m n : ι) : wsum ω (pairIdx m n) = ω m + ω n := by
  rw [pairIdx, wsum_add, wsum_single, wsum_single]
  push_cast
  ring

/-- **The Bogoliubov Hamiltonian is essentially self-adjoint on the finite-particle
core.**  Pair creation and annihilation `gₖ a†ₘₖ a†ₙₖ + conj(gₖ) aₙₖ aₘₖ` on top of an
arbitrary non-negative free dispersion, subject only to `∑ₖ ‖gₖ‖(ωₘₖ + ωₙₖ + 2) < ∞`. -/
theorem bogoliubov_essentiallySelfAdjointOn_core (hω : ∀ i, 0 ≤ ω i) (m n : κ → ι) (g : κ → ℂ)
    (hsum : Summable fun k => ‖g k‖ * (ω (m k) + ω (n k) + 2)) :
    EssentiallySelfAdjointOn (lpFiniteModes (Idx ι))
      ((fockH hω (fun k => pairIdx (m k) (n k)) (fun _ => (0 : Idx ι)) g
          (fun k => by simp)
          (by
            refine hsum.congr fun k => ?_
            simp [wsum_pairIdx])).comp
        (Submodule.inclusion (finiteModes_le_maxDom (sig ω)))) :=
  fockH_essentiallySelfAdjointOn_core hω _ _ g _ _

end

end BookProof.FockQuadratic
