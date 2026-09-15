import Mathlib
import BookProof.ChapterFockSchurEsa
import BookProof.ChapterFockWeightedSchurEsa.Part2

/-!
# `dΓ(A)` for an **unbounded** one-particle operator: the Schur gate weighted by the
# one-particle symbol

`BookProof.ChapterFockSchurEsa` proves the number bound `‖dΓ(A)u‖ ≤ K‖𝒩u‖` and essential
self-adjointness of `dΓ(A)` on the finite-occupation core under the **unweighted Schur
gate** `∑_j |A_{kj}| ≤ K` — a gate that forces the one-particle operator `A` to be
*bounded*.  The recorded next step was `dΓ` of an **unbounded** one-particle operator,
through "a Schur gate weighted by the one-particle symbol".  That is what this module
supplies.

Fix a **weight** `w : ℕ → ℝ` with `w k ≥ 1` — the one-particle symbol — and let

```text
𝒩_w = dΓ(diag (w²)),      σ(α) = ∑_k w_k² α_k + 1
```

be the weighted number operator and its symbol.  The gate is

```text
(row)   ∀ k, ∑_j |A_{kj}| ≤ K w_k,
(col)   ∀ j, ∑_k |A_{jk}| / w_k ≤ K,
(comm)  ∀ k, ∑_j |A_{kj}| · |w_j² − w_k²| / (w_k w_j) ≤ B.
```

For `w ≡ 1` this is the unweighted Schur gate with a vanishing commutator gate, so the
present statement contains the bounded one; but the row gate now allows the rows of `A`
to *grow* like the symbol, and the witness of section 7 — the one-particle matrix
`A_{k,k+1} = A_{k+1,k} = √(k+1)`, the position operator of a harmonic oscillator — is
genuinely unbounded and covered.

## What is proved

* `wdeg`, `wSym`, `wgt` — the weighted particle number `∑_k w_k² α_k`, the comparison
  symbol `σ = wdeg + 1` and the associated diagonal operator on the core.
* `annA_wgt` — the commutation relation `a_j 𝒩_w = (𝒩_w + w_j²) a_j`, the only algebraic
  input of the commutator estimate.
* `sum_wsq_normSq_annA` — `∑_k w_k² ‖a_k u‖² = ⟪u, 𝒩_w u⟫`, the weighted form of the
  identity behind the number bound.
* **`norm_dGamma_le_w`** — the relative bound `‖dΓ(A)u‖ ≤ K‖σ u‖` on the core, proved
  sector by sector: `dΓ(A)` conserves the particle number, so on the `n`-particle sector
  the weighted Schur test gives `‖dΓ(A)u‖² ≤ K² n ⟪u, 𝒩_w u⟫`, and `n ≤ wdeg` because
  `w ≥ 1`.
* **`dGammaOp_commForm_bound_w`** — the commutator estimate
  `|⟪u, i[dΓ(A), σ]u⟫| ≤ B⟪u, σ u⟫`: the part of `⟪dΓ(A)u, σu⟫` that survives conjugation
  is `∑_{k,j} conj(A_{kj})(w_j² − w_k²)⟪a_k u, a_j u⟫`, which the commutator gate controls
  by the same Schur test.
* **`dGamma_essentiallySelfAdjointOn_core_w`** — the headline: `dΓ(A)` is essentially
  self-adjoint on the finite-occupation core, and `dGamma_stone_flow_w` — its unitary
  group.
* `oscCol`, `isHermCol_oscCol`, `wRow_oscCol`, `wCol_oscCol`, `wComm_oscCol`,
  **`oscCol_not_schurBound`**, `oscCol_entry_atTop`, **`osc_essentiallySelfAdjointOn_core`**
  — the non-vacuity witness: an *unbounded* one-particle matrix (no unweighted Schur bound
  holds, and its entries tend to infinity) whose second quantization is covered.

## Honest boundary

The one-particle matrix must still be Hermitian and column-finite; what is removed is its
boundedness.  The three gates are conditions on the matrix *relative to the chosen symbol*
`w`; nothing here chooses `w` for a given Hamiltonian.  Everything is `sorry`-free and
`axiom`-free.
-/

namespace BookProof.FockWeightedSchur

open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}
/-! ## 8. Non-vacuity: an unbounded one-particle operator -/

/-- `√a ≤ a` for `a ≥ 1`. -/
theorem sqrt_le_of_one_le {a : ℝ} (h : 1 ≤ a) : Real.sqrt a ≤ a := by
  have h0 : (0:ℝ) ≤ a := le_trans zero_le_one h
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg a, sq_nonneg (Real.sqrt a - 1)]

/-- The one-particle matrix `A_{k,k+1} = A_{k+1,k} = √(k+1)`, presented by its columns: the
position operator of a harmonic oscillator in the occupation basis.  It is Hermitian,
column-finite and **unbounded**. -/
def oscCol (k : ℕ) : ℕ →₀ ℂ :=
  if k = 0 then Finsupp.single 1 ((Real.sqrt 1 : ℝ) : ℂ)
  else Finsupp.single (k + 1) ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ)
      + Finsupp.single (k - 1) ((Real.sqrt (k : ℝ) : ℝ) : ℂ)

/-- The one-particle symbol `w_k = k + 1`. -/
def oscW (k : ℕ) : ℝ := (k : ℝ) + 1

theorem oscW_ge_one (k : ℕ) : 1 ≤ oscW k := by
  have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [oscW]; linarith

theorem oscW_pos (k : ℕ) : 0 < oscW k := lt_of_lt_of_le zero_lt_one (oscW_ge_one k)

theorem oscCol_apply (k j : ℕ) : (oscCol k) j =
    if j = k + 1 then ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ)
    else if k = j + 1 then ((Real.sqrt (k : ℝ) : ℝ) : ℂ) else 0 := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [oscCol, if_pos rfl, Finsupp.single_apply]
    by_cases h : j = 0 + 1
    · rw [if_pos (by omega : (1:ℕ) = j), if_pos h]
      norm_num
    · rw [if_neg (by omega : ¬((1:ℕ) = j)), if_neg h, if_neg (by omega)]
  · rw [oscCol, if_neg (by omega), Finsupp.add_apply, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases h1 : j = k + 1
    · rw [if_pos (by omega : k + 1 = j), if_neg (by omega : ¬(k - 1 = j)), if_pos h1]
      simp
    · by_cases h2 : k = j + 1
      · rw [if_neg (by omega : ¬(k + 1 = j)), if_pos (by omega : k - 1 = j), if_neg h1,
          if_pos h2]
        simp
      · rw [if_neg (by omega : ¬(k + 1 = j)), if_neg (by omega : ¬(k - 1 = j)), if_neg h1,
          if_neg h2]
        simp

theorem norm_oscCol_apply (k j : ℕ) : ‖(oscCol k) j‖ =
    if j = k + 1 then Real.sqrt ((k : ℝ) + 1)
    else if k = j + 1 then Real.sqrt (k : ℝ) else 0 := by
  rw [oscCol_apply]
  by_cases h1 : j = k + 1
  · rw [if_pos h1, if_pos h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  · by_cases h2 : k = j + 1
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, norm_zero]

theorem isHermCol_oscCol : IsHermCol oscCol := by
  intro j k
  rw [oscCol_apply, oscCol_apply]
  by_cases h1 : k = j + 1
  · have h2 : ¬(j = k + 1) := by omega
    rw [if_pos h1, if_neg h2, if_pos h1, Complex.conj_ofReal]
    have : ((k : ℝ)) = (j : ℝ) + 1 := by rw [h1]; push_cast; ring
    rw [this]
  · by_cases h2 : j = k + 1
    · rw [if_neg h1, if_pos h2, if_pos h2, Complex.conj_ofReal]
      have : ((j : ℝ)) = (k : ℝ) + 1 := by rw [h2]; push_cast; ring
      rw [this]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
      simp

theorem support_oscCol_subset (k : ℕ) : (oscCol k).support ⊆ {k + 1, k - 1} := by
  classical
  intro j hj
  have hne : (oscCol k) j ≠ 0 := Finsupp.mem_support_iff.mp hj
  rw [oscCol_apply] at hne
  by_cases h1 : j = k + 1
  · simp [h1]
  · by_cases h2 : k = j + 1
    · have : j = k - 1 := by omega
      simp [this]
    · rw [if_neg h1, if_neg h2] at hne
      exact absurd rfl hne

/-- A sum over a set of at most two modes, from a uniform bound on the terms. -/
theorem sum_pair_le {f : ℕ → ℝ} {S : Finset ℕ} {a b : ℕ} {C : ℝ} (hS : S ⊆ {a, b})
    (hf : ∀ j, 0 ≤ f j) (hC : ∀ j, f j ≤ C) (hC0 : 0 ≤ C) : ∑ j ∈ S, f j ≤ 2 * C := by
  classical
  have hcard : ((({a, b} : Finset ℕ)).card : ℝ) ≤ 2 := by
    have : (({a, b} : Finset ℕ)).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    exact_mod_cast this
  calc ∑ j ∈ S, f j ≤ ∑ j ∈ ({a, b} : Finset ℕ), f j :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun j _ _ => hf j
    _ ≤ ∑ _j ∈ ({a, b} : Finset ℕ), C := Finset.sum_le_sum fun j _ => hC j
    _ ≤ 2 * C := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        nlinarith [hC0, hcard]

/-- Every entry of a column is bounded by the symbol at its **row** index. -/
theorem norm_oscCol_le (k j : ℕ) : ‖(oscCol k) j‖ ≤ oscW k := by
  rw [norm_oscCol_apply]
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  by_cases h1 : j = k + 1
  · rw [if_pos h1]
    have := sqrt_le_of_one_le (a := (k : ℝ) + 1) (by linarith)
    simpa [oscW] using this
  · by_cases h2 : k = j + 1
    · rw [if_neg h1, if_pos h2]
      have hk1 : (1:ℝ) ≤ (k : ℝ) := by
        have : (1:ℕ) ≤ k := by omega
        exact_mod_cast this
      have := sqrt_le_of_one_le hk1
      simp only [oscW]; linarith
    · rw [if_neg h1, if_neg h2]
      simp only [oscW]; linarith

/-- Every entry of a column is bounded by the symbol at its **column** index. -/
theorem norm_oscCol_le_col (j k : ℕ) : ‖(oscCol j) k‖ ≤ oscW k := by
  rw [norm_oscCol_apply]
  have hj0 : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  by_cases h1 : k = j + 1
  · rw [if_pos h1]
    have hkj : (k : ℝ) = (j : ℝ) + 1 := by rw [h1]; push_cast; ring
    have := sqrt_le_of_one_le (a := (j : ℝ) + 1) (by linarith)
    simp only [oscW]; linarith
  · by_cases h2 : j = k + 1
    · rw [if_neg h1, if_pos h2]
      have hjk : (j : ℝ) = (k : ℝ) + 1 := by rw [h2]; push_cast; ring
      have := sqrt_le_of_one_le (a := (j : ℝ)) (by rw [hjk]; linarith)
      simp only [oscW]; linarith
    · rw [if_neg h1, if_neg h2]
      simp only [oscW]; linarith

theorem wRow_oscCol : WRowBound oscW oscCol 2 := by
  intro k
  exact sum_pair_le (support_oscCol_subset k) (fun j => norm_nonneg _)
    (fun j => norm_oscCol_le k j) (le_of_lt (oscW_pos k))

theorem wCol_oscCol : WColBound oscW oscCol 2 := by
  intro j
  have h := sum_pair_le (f := fun k => ‖(oscCol j) k‖ / oscW k) (C := 1)
    (support_oscCol_subset j) (fun k => div_nonneg (norm_nonneg _) (oscW_pos k).le)
    (fun k => by
      rw [div_le_one (oscW_pos k)]
      exact norm_oscCol_le_col j k) zero_le_one
  simpa using h

/-- The commutator terms of the oscillator matrix are bounded by `2`. -/
theorem oscComm_term_le (k j : ℕ) :
    ‖(oscCol k) j‖ * |oscW j ^ 2 - oscW k ^ 2| / (oscW k * oscW j) ≤ 2 := by
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hj0 : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hwk : 0 < oscW k := oscW_pos k
  have hwj : 0 < oscW j := oscW_pos j
  rw [div_le_iff₀ (mul_pos hwk hwj), norm_oscCol_apply]
  by_cases h1 : j = k + 1
  · rw [if_pos h1]
    have hj : oscW j = (k : ℝ) + 2 := by
      simp only [oscW, h1]; push_cast; ring
    have hkk : oscW k = (k : ℝ) + 1 := rfl
    have habs : |oscW j ^ 2 - oscW k ^ 2| = 2 * (k : ℝ) + 3 := by
      rw [hj, hkk, abs_of_nonneg (by nlinarith)]
      ring
    rw [habs, hj, hkk]
    have hs : Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 :=
      sqrt_le_of_one_le (by linarith)
    have hs0 : 0 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
    nlinarith [hs, hs0]
  · by_cases h2 : k = j + 1
    · rw [if_neg h1, if_pos h2]
      have hk1 : (1:ℝ) ≤ (k : ℝ) := by
        have : (1:ℕ) ≤ k := by omega
        exact_mod_cast this
      have hjk : (j : ℝ) = (k : ℝ) - 1 := by
        have : (k : ℝ) = (j : ℝ) + 1 := by rw [h2]; push_cast; ring
        linarith
      have hj : oscW j = (k : ℝ) := by simp only [oscW, hjk]; ring
      have hkk : oscW k = (k : ℝ) + 1 := rfl
      have habs : |oscW j ^ 2 - oscW k ^ 2| = 2 * (k : ℝ) + 1 := by
        rw [hj, hkk, abs_of_nonpos (by nlinarith)]
        ring
      rw [habs, hj, hkk]
      have hs : Real.sqrt (k : ℝ) ≤ (k : ℝ) := sqrt_le_of_one_le hk1
      have hs0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      nlinarith [hs, hs0]
    · rw [if_neg h1, if_neg h2]
      have : 0 < oscW k * oscW j := mul_pos hwk hwj
      nlinarith

theorem wComm_oscCol : WCommBound oscW oscCol 4 := by
  intro k
  have h := sum_pair_le
    (f := fun j => ‖(oscCol k) j‖ * |oscW j ^ 2 - oscW k ^ 2| / (oscW k * oscW j)) (C := 2)
    (support_oscCol_subset k)
    (fun j => by
      have : 0 < oscW k * oscW j := mul_pos (oscW_pos k) (oscW_pos j)
      positivity)
    (fun j => oscComm_term_le k j) (by norm_num)
  exact le_trans h (by norm_num)

/-- The entries of the oscillator matrix are **unbounded**: the one-particle operator it
defines is not bounded, so the unweighted Schur gate of `ChapterFockSchurEsa` cannot
apply. -/
theorem oscCol_entries_unbounded (C : ℝ) : ∃ k : ℕ, C ≤ ‖(oscCol k) (k + 1)‖ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2)
  refine ⟨n, ?_⟩
  rw [norm_oscCol_apply, if_pos rfl]
  by_cases hC : C ≤ 0
  · exact le_trans hC (Real.sqrt_nonneg _)
  · have hC : 0 < C := lt_of_not_ge hC
    have h1 : C ^ 2 < (n : ℝ) + 1 := by linarith
    have h2 : Real.sqrt (C ^ 2) < Real.sqrt ((n : ℝ) + 1) := by
      exact Real.sqrt_lt_sqrt (sq_nonneg C) h1
    rw [Real.sqrt_sq hC.le] at h2
    exact h2.le

/-- The oscillator matrix satisfies **no** unweighted Schur bound. -/
theorem oscCol_not_schurBound (K : ℝ) : ¬ SchurBound oscCol K := by
  classical
  intro hK
  obtain ⟨k, hk⟩ := oscCol_entries_unbounded (K + 1)
  have hmem : k + 1 ∈ (oscCol k).support := by
    refine Finsupp.mem_support_iff.mpr fun hc => ?_
    rw [show ‖(oscCol k) (k+1)‖ = 0 from by rw [hc]; simp] at hk
    have h0 : (0:ℝ) ≤ K := by
      have := hK k
      have hnn : (0:ℝ) ≤ ∑ j ∈ (oscCol k).support, ‖(oscCol k) j‖ :=
        Finset.sum_nonneg fun j _ => norm_nonneg _
      linarith
    linarith
  have hsingle : ‖(oscCol k) (k + 1)‖ ≤ ∑ j ∈ (oscCol k).support, ‖(oscCol k) j‖ :=
    Finset.single_le_sum (f := fun j => ‖(oscCol k) j‖) (fun j _ => norm_nonneg _) hmem
  have := hK k
  linarith

/-- **The second quantization of an unbounded one-particle operator is essentially
self-adjoint on the finite-occupation core.** -/
theorem osc_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp oscCol) :=
  dGamma_essentiallySelfAdjointOn_core_w (w := oscW) (K := 2) (B := 4) oscW_ge_one
    isHermCol_oscCol wRow_oscCol wCol_oscCol (by norm_num) wComm_oscCol

/-- **Its unitary group.** -/
theorem osc_stone_flow :
    ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)),
      IsSelfAdjointExtension (dGammaOp oscCol) T.op ∧ IsStoneFlow T U :=
  dGamma_stone_flow_w (w := oscW) (K := 2) (B := 4) oscW_ge_one isHermCol_oscCol
    wRow_oscCol wCol_oscCol (by norm_num) wComm_oscCol

end

end BookProof.FockWeightedSchur
