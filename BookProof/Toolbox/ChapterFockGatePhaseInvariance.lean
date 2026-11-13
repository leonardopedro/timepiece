/-
# Diagonal phases leave the weighted Schur gates unchanged

The weighted Schur theory (`BookProof.FockWeightedSchur`) reduces essential self-adjointness of
`dΓ(A)` to three gates on the one-particle matrix: row, column and commutator.  Each gate reads only
the *moduli* `‖A_{k j}‖` of the entries — the row gate sums them, the column gate sums them against
`1/w_k`, and the commutator gate multiplies them by the band weight `|w_j^2 − w_k^2|/(w_k w_j)`.  No
phase ever enters.

That observation is the whole content of this module: if two matrix descriptions agree entrywise up
to a factor `u_k · conj(u_j)` with `‖u_k‖ = 1`, then the three gates hold for one description
exactly when they hold for the other, with the *same* constants.

Why it matters.  An orthonormal basis that differs from another by a diagonal unitary — the
`coreBasis`-versus-`hermBasisN` situation of the Yang–Mills Fock space, where the two bases are
expected to agree up to one phase per degree level — produces matrix elements
`⟨u_k ψ_k, T (u_j ψ_j)⟩ = conj(u_k) u_j ⟨ψ_k, T ψ_j⟩`, which is exactly the relation assumed below.
So the gates, and with them essential self-adjointness, transfer across such a change of basis
without recomputation.

## Honest boundary

This module does **not** prove that `coreBasis` and `hermBasisN` are related by diagonal phases.
That is the basis bridge, and it is still an open hypothesis: it needs the vanishing of the product
Hermite coefficients of monomials below the degree (`⟨x^α, ψ_β⟩ = 0` whenever some `β_i > α_i`),
which is not in the corpus.  What is proved here is the *last* step of that bridge: once the phase
relation is available, the gates need no re-derivation.
-/

import BookProof.Toolbox.ChapterFockWeightedSchurEsa

namespace BookProof.FockGatePhaseInvariance

open BookProof.FockWeightedSchur

variable {w : ℕ → ℝ} {col col' : ℕ → (ℕ →₀ ℂ)} {K B : ℝ} {u : ℕ → ℂ}

/-! ## The phase relation -/

/-- Matrices related entrywise by a diagonal left phase and the conjugate diagonal right phase:
`col'_{k j} = u_k · conj(u_j) · col_{k j}`, the matrix form of `A ↦ D A D*`. -/
def PhaseRelated (u : ℕ → ℂ) (col col' : ℕ → (ℕ →₀ ℂ)) : Prop :=
  ∀ k j, col' k j = u k * star (u j) * col k j

/-- The phase relation is invertible: the unit modulus condition makes the two diagonal phases
undo each other. -/
theorem phaseRelated_star (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col') :
    PhaseRelated (fun k => star (u k)) col' col := by
  intro k j
  simp only []
  rw [h k j, star_star]
  have hk : star (u k) * u k = 1 := by simpa [hu k] using RCLike.conj_mul (u k)
  have hj : u j * star (u j) = 1 := by
    rw [mul_comm]
    simpa [hu j] using RCLike.conj_mul (u j)
  rw [show star (u k) * u j * (u k * star (u j) * col k j)
      = (star (u k) * u k) * (u j * star (u j)) * col k j by ring, hk, hj, one_mul, one_mul]

/-! ## The gates see only moduli -/

theorem support_phase (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col') (k : ℕ) :
    (col' k).support = (col k).support := by
  ext j
  simp only [Finsupp.mem_support_iff]
  rw [h k j]
  constructor
  · intro hz
    exact (mul_ne_zero_iff.mp hz).2
  · intro hz
    have hu0 : u k ≠ 0 := by
      intro h0
      have : ‖u k‖ = 0 := by rw [h0, norm_zero]
      rw [hu k] at this
      exact one_ne_zero this
    have huj : star (u j) ≠ 0 := by
      intro h0
      have h1 : u j = 0 := by
        have := congrArg star h0
        simpa using this
      have : ‖u j‖ = 0 := by rw [h1, norm_zero]
      rw [hu j] at this
      exact one_ne_zero this
    exact mul_ne_zero (mul_ne_zero hu0 huj) hz

theorem norm_phase (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col') (k j : ℕ) :
    ‖col' k j‖ = ‖col k j‖ := by
  rw [h k j, norm_mul, norm_mul, norm_star, hu k, hu j, one_mul, one_mul]

theorem phase_sum (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col') (k : ℕ) {S : Finset ℕ} :
    ∑ j ∈ S, ‖col' k j‖ = ∑ j ∈ S, ‖col k j‖ :=
  Finset.sum_congr rfl fun j _ => norm_phase hu h k j

/-! ## The three gates -/

theorem WRowBound.phase (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col')
    (hb : WRowBound w col K) : WRowBound w col' K := by
  intro k
  rw [support_phase hu h k]
  rw [phase_sum hu h k (S := (col k).support)]
  exact hb k

theorem WColBound.phase (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col')
    (hb : WColBound w col K) : WColBound w col' K := by
  intro k
  rw [support_phase hu h k]
  refine le_trans (le_of_eq ?_) (hb k)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_phase hu h k j]

theorem WCommBound.phase (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col')
    (hb : WCommBound w col B) : WCommBound w col' B := by
  intro k
  rw [support_phase hu h k]
  refine le_trans (le_of_eq ?_) (hb k)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_phase hu h k j]

/-! ## Both directions -/

theorem wRowBound_phase_iff (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col') :
    WRowBound w col K ↔ WRowBound w col' K :=
  ⟨fun hb => WRowBound.phase hu h hb, fun hb => WRowBound.phase (u := fun k => star (u k))
    (fun k => by rw [norm_star, hu k]) (phaseRelated_star hu h) hb⟩

theorem wColBound_phase_iff (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col') :
    WColBound w col K ↔ WColBound w col' K :=
  ⟨fun hb => WColBound.phase hu h hb, fun hb => WColBound.phase (u := fun k => star (u k))
    (fun k => by rw [norm_star, hu k]) (phaseRelated_star hu h) hb⟩

theorem wCommBound_phase_iff (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col') :
    WCommBound w col B ↔ WCommBound w col' B :=
  ⟨fun hb => WCommBound.phase hu h hb, fun hb => WCommBound.phase (u := fun k => star (u k))
    (fun k => by rw [norm_star, hu k]) (phaseRelated_star hu h) hb⟩

/-- **The gates transfer across a diagonal phase change.**  All three weighted Schur gates hold for
one matrix description if and only if they hold for a description differing from it by the diagonal
phases `u_k · conj(u_j)`, with the same constants. -/
theorem gates_phase_iff (hu : ∀ k, ‖u k‖ = 1) (h : PhaseRelated u col col') :
    (WRowBound w col K ∧ WColBound w col K ∧ WCommBound w col B) ↔
      (WRowBound w col' K ∧ WColBound w col' K ∧ WCommBound w col' B) := by
  rw [wRowBound_phase_iff hu h, wColBound_phase_iff hu h, wCommBound_phase_iff hu h]

end BookProof.FockGatePhaseInvariance
