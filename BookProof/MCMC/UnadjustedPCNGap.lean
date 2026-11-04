import Mathlib
import BookProof.ChapterReferenceGap
import BookProof.MCMC.GeometricErgodicity

/-!
# Chapter UnadjustedPCNGap — the pCN gap is independent of the dimension

Plan: `pcnl.md`, Module 1 (its *output*), joined to Modules 4–5.  The unadjusted pCN step

`v = ρ u + √(1 − ρ²) ξ`,  `ξ` white,

is the transition operator of Brownian motion on the sphere `S^{d-1}` in the `d`-mode truncation,
so by Schur's lemma it is diagonalised by the hyperspherical harmonics; on the slice observables
(functionals of one coordinate) the eigenfunctions are the **Gegenbauer** polynomials
`C_n^{(α/2)}`, with eigenvalues

`λ_n^{(d)} = ρ ^ n`,

**independent of `d`** — the observation `pcnl.md` §1.A makes and §1.B transports to the
Fock/Hermite modes `H_n/n!` (`PhysHSGaussian.gegenbauerScaled_tendsto_hermite`).

This chapter formalises what that spectrum says, on the coefficient model of the Gauss–polynomial
core that the rest of the MCMC/spectral development uses (`BookProof.ReferenceGap.CoreCoeff`): a
multi-index `n : Fin d → ℕ` collects the occupation of the `d` modes, its total degree
`N = ∑ i, nᵢ` labels the spherical-harmonic order, and the pCN eigenvalue of that mode is `ρ ^ N`,
so the `L²` weight of the mode is `ρ ^ (2N)`.

## Contents

* `natDeg`, `pcnWeight`, `pcnForm` — the mode degree, the `L²` weight `ρ^(2N)` and the pCN form
  `∑ n, ρ^(2N) ‖c n‖² = ‖P₀ c‖²` on the core;
* `pcnWeight_nonneg`, `pcnWeight_le_gap` — the weights are nonnegative, and every *excited* mode
  (degree `≥ 1`) carries at most `ρ²`, since `ρ^(2N) ≤ ρ²` for `0 ≤ ρ ≤ 1`;
* **`pcnForm_le`** — the contraction `‖P₀ c‖² ≤ ρ² ‖c‖²` on the vacuum-orthogonal sector;
* **`pcn_gap_uniform`** — the certified gap `(1 − ρ²)‖c‖² ≤ ‖c‖² − ‖P₀ c‖²`, with **no dependence
  on the number of modes `d`**: the gap of the unadjusted proposal is dimension-free, which is
  precisely why the plan can pass `d → ∞`;
* `pcn_norm_le` — the same statement for the norms, `‖P₀ c‖ ≤ ρ ‖c‖`;
* **`pcn_geometric_ergodicity`** — the transfer to `pcnl.md` Modules 4–5: an operator that
  contracts by `ρ` on the orthogonal complement of its invariant state converges geometrically at
  rate `ρ`, i.e. `BookProof.MCMC.norm_iterate_sub_invariant_le` with `γ = 1 − ρ`.

## Honest boundary

The eigenfunction identity `P₀ C_n^{(α/2)} = ρ^n C_n^{(α/2)}` — Module 1 proper — is **not**
proved here: it needs the spherical measure and the Gegenbauer addition theorem (or, in the
`α → ∞` limit, the Gaussian integral of `H_n(ρx + √(1−ρ²)ξ)/n!`), neither of which is in the
corpus.  What is proved is everything downstream of the spectrum: the weights `ρ^(2N)`, the
dimension-free gap, and its consequence for the MCMC rate.  The pCNL perturbation
`P = P₀ + K_drift + K_reject` is not treated at all; the plan's Module 3 must show it preserves
the gap, and `BookProof.MCMC.GeometricErgodicity` states the resulting bound with the gap as a
hypothesis.
-/

noncomputable section

namespace BookProof.MCMC.UnadjustedPCN

open Finset
open BookProof.ReferenceGap

variable {d : ℕ}

/-- The total degree `N = ∑ i, nᵢ` of a multi-index: the spherical-harmonic order of the mode. -/
def natDeg (n : Fin d → ℕ) : ℕ := ∑ i, n i

/-- The `L²` weight of the mode `n`: the pCN eigenvalue is `ρ ^ N`, so its squared modulus is
`ρ ^ (2N)`. -/
def pcnWeight (ρ : ℝ) (n : Fin d → ℕ) : ℝ := ρ ^ (2 * natDeg n)

/-- The pCN quadratic form on the core: `‖P₀ c‖²`, diagonal in the mode basis. -/
def pcnForm (ρ : ℝ) (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, pcnWeight ρ n * ‖c n‖ ^ 2

theorem natDeg_zero : natDeg (0 : Fin d → ℕ) = 0 := by
  simp [natDeg]

/-- A non-vacuum mode has degree at least one. -/
theorem one_le_natDeg {n : Fin d → ℕ} (hn : n ≠ 0) : 1 ≤ natDeg n := by
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h
    exact hn (funext fun j => by simpa using not_exists.mp h j)
  have : 0 < n j := Nat.pos_of_ne_zero hj
  have hle : n j ≤ natDeg n :=
    Finset.single_le_sum (s := Finset.univ) (f := fun i => n i) (fun i _ => Nat.zero_le _)
      (Finset.mem_univ j)
  omega

theorem pcnWeight_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (n : Fin d → ℕ) : 0 ≤ pcnWeight ρ n := by
  unfold pcnWeight
  positivity

/-- **Every excited mode carries at most `ρ²`**: for `0 ≤ ρ ≤ 1` and `N ≥ 1`, `ρ^(2N) ≤ ρ²`. -/
theorem pcnWeight_le_gap {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {n : Fin d → ℕ} (hn : n ≠ 0) :
    pcnWeight ρ n ≤ ρ ^ 2 := by
  unfold pcnWeight
  have hN : 1 ≤ natDeg n := one_le_natDeg hn
  have h2 : 2 ≤ 2 * natDeg n := by omega
  exact pow_le_pow_of_le_one hρ0 hρ1 h2

/-- **The unadjusted pCN step contracts by `ρ`**: on the vacuum-orthogonal sector its form is at
most `ρ²‖c‖²`. -/
theorem pcnForm_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (c : CoreCoeff d) (hc : c 0 = 0) :
    pcnForm ρ c ≤ ρ ^ 2 * coreNormSq c := by
  rw [pcnForm, coreNormSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hne : n ≠ 0 := by
    rintro rfl
    exact (Finsupp.notMem_support_iff.mpr hc) hn
  exact mul_le_mul_of_nonneg_right (pcnWeight_le_gap hρ0 hρ1 hne) (by positivity)

/-- **The gap of the unadjusted proposal is dimension-free.**  On the vacuum-orthogonal sector

`(1 − ρ²)‖c‖² ≤ ‖c‖² − ‖P₀ c‖²`,

with no dependence on the number of modes `d` — the statement `pcnl.md` §1.A records as "the
eigenvalues `λ_n^{(d)}` are completely independent of `d`", and the reason the `d → ∞` limit can be
taken. -/
theorem pcn_gap_uniform {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (c : CoreCoeff d) (hc : c 0 = 0) :
    (1 - ρ ^ 2) * coreNormSq c ≤ coreNormSq c - pcnForm ρ c := by
  have h := pcnForm_le hρ0 hρ1 c hc
  linarith

/-- The same contraction, read on the norms: `‖P₀ c‖ ≤ ρ ‖c‖`. -/
theorem pcn_norm_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (c : CoreCoeff d) (hc : c 0 = 0) :
    Real.sqrt (pcnForm ρ c) ≤ ρ * Real.sqrt (coreNormSq c) := by
  have h := pcnForm_le hρ0 hρ1 c hc
  have hρ2 : (0 : ℝ) ≤ ρ ^ 2 := sq_nonneg ρ
  have hnorm : Real.sqrt (pcnForm ρ c) ≤ Real.sqrt (ρ ^ 2 * coreNormSq c) :=
    Real.sqrt_le_sqrt h
  rwa [Real.sqrt_mul hρ2, Real.sqrt_sq hρ0] at hnorm

/-- The first excited mode is the pCN eigenvalue `ρ`: a mode of degree one has weight `ρ²`, so the
operator contracts it by `ρ` and the gap of the unadjusted proposal is `1 − ρ`. -/
theorem pcnWeight_degree_one {ρ : ℝ} {n : Fin d → ℕ} (hn : natDeg n = 1) :
    pcnWeight ρ n = ρ ^ 2 := by
  unfold pcnWeight
  rw [hn]

/-- **The pCN gap transfers to geometric ergodicity** (`pcnl.md` Modules 4–5): a bounded operator
that fixes the unit state `φ` and contracts by `ρ < 1` on its orthogonal complement drives every
iterate to the invariant state at the geometric rate `ρ^m`.  This is
`BookProof.MCMC.norm_iterate_sub_invariant_le` with the gap `γ = 1 − ρ` that `pcn_gap_uniform`
certifies. -/
theorem pcn_geometric_ergodicity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) {φ : E} (hφ : ‖φ‖ = 1)
    (hfix : P φ = φ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hgap : ∀ w : E, (inner ℂ φ w : ℂ) = 0 → ‖P w‖ ≤ ρ * ‖w‖) (m : ℕ) (ψ : E) :
    ‖(P ^ m) ψ - (inner ℂ φ ψ : ℂ) • φ‖ ≤
      ρ ^ m * ‖ψ - (inner ℂ φ ψ : ℂ) • φ‖ := by
  have h := BookProof.MCMC.norm_iterate_sub_invariant_le hP hφ hfix (γ := 1 - ρ)
    (by linarith) (fun w hw => by simpa using hgap w hw) m ψ
  rwa [show 1 - (1 - ρ) = ρ from by ring] at h

end BookProof.MCMC.UnadjustedPCN
