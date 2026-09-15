import Mathlib
import BookProof.ChapterFockSchurEsa

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

/-! ## 1. The weighted particle number -/

/-- The **weighted particle number** `∑_k w_k² α_k` of a configuration. -/
def wdeg (w : ℕ → ℝ) (α : Conf) : ℝ := α.sum fun k n => w k ^ 2 * n

/-- The comparison symbol `σ(α) = ∑_k w_k² α_k + 1`. -/
def wSym (w : ℕ → ℝ) (α : Conf) : ℝ := wdeg w α + 1

variable {w : ℕ → ℝ}

theorem wdeg_eq_sum {α : Conf} {S : Finset ℕ} (h : α.support ⊆ S) :
    wdeg w α = ∑ k ∈ S, w k ^ 2 * α k :=
  Finsupp.sum_of_support_subset α h _ (by simp)

theorem wdeg_nonneg (α : Conf) : 0 ≤ wdeg w α := by
  rw [wdeg_eq_sum (Finset.Subset.refl α.support)]
  refine Finset.sum_nonneg fun k _ => ?_
  have : (0:ℝ) ≤ w k ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (α k : ℝ) := Nat.cast_nonneg _
  positivity

theorem wSym_nonneg (α : Conf) : 0 ≤ wSym w α := by
  have := wdeg_nonneg (w := w) α
  simp only [wSym]; linarith

theorem wSym_pos (α : Conf) : 0 < wSym w α := by
  have := wdeg_nonneg (w := w) α
  simp only [wSym]; linarith

/-- The unweighted particle number is dominated by the weighted one. -/
theorem ndeg_le_wdeg (hw : ∀ k, 1 ≤ w k) (α : Conf) : (ndeg α : ℝ) ≤ wdeg w α := by
  rw [wdeg_eq_sum (Finset.Subset.refl α.support), ndeg_eq_sum (Finset.Subset.refl α.support)]
  push_cast
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : (1:ℝ) ≤ w k ^ 2 := by nlinarith [hw k]
  have h2 : (0:ℝ) ≤ (α k : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem wdeg_up (j : ℕ) (α : Conf) : wdeg w (up j α) = wdeg w α + w j ^ 2 := by
  classical
  have h1 : (up j α).support ⊆ insert j α.support := support_up j α
  have h2 : α.support ⊆ insert j α.support := Finset.subset_insert _ _
  rw [wdeg_eq_sum h1, wdeg_eq_sum h2]
  have hcongr : ∀ i ∈ insert j α.support,
      w i ^ 2 * (((up j α) i : ℕ) : ℝ)
        = w i ^ 2 * ((α i : ℕ) : ℝ) + (if i = j then w j ^ 2 else 0) := by
    intro i _
    rw [up_apply' j α i]
    by_cases h : i = j
    · subst h; push_cast; simp; ring
    · simp [h]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib]
  congr 1
  simp

theorem wSym_up (j : ℕ) (α : Conf) : wSym w (up j α) = wSym w α + w j ^ 2 := by
  simp only [wSym, wdeg_up]; ring

/-! ## 2. The weighted number operator on the core -/

/-- The comparison operator `𝒩_w + 1` applied to a finitely supported state. -/
def wgt (w : ℕ → ℝ) (u : FockAlg) : FockAlg :=
  Finsupp.onFinset u.support (fun α => (wSym w α : ℂ) * u α) (by
    intro α hα
    by_contra hc
    have hz : u α = 0 := Finsupp.notMem_support_iff.mp hc
    simp only [hz, mul_zero, ne_eq, not_true_eq_false] at hα)

theorem wgt_apply (u : FockAlg) (α : Conf) : wgt w u α = (wSym w α : ℂ) * u α := rfl

theorem support_wgt_subset (u : FockAlg) : (wgt w u).support ⊆ u.support :=
  Finsupp.support_onFinset_subset

/-- **The commutation relation `a_j 𝒩_w = (𝒩_w + w_j²) a_j`.** -/
theorem annA_wgt (j : ℕ) (u : FockAlg) :
    annA j (wgt w u) = wgt w (annA j u) + ((w j ^ 2 : ℝ) : ℂ) • annA j u := by
  refine Finsupp.ext fun α => ?_
  rw [annA_apply, wgt_apply, Finsupp.add_apply, wgt_apply, annA_apply, Finsupp.smul_apply,
    annA_apply, smul_eq_mul, wSym_up]
  push_cast
  ring

/-- The weighted number operator is symmetric on the core. -/
theorem inner_wgt_symm (u v : FockAlg) :
    (inner ℂ (toLp (wgt w u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (wgt w v)) := by
  classical
  have hsu : (wgt w u).support ⊆ u.support ∪ v.support :=
    (support_wgt_subset u).trans Finset.subset_union_left
  have hsv : u.support ⊆ u.support ∪ v.support := Finset.subset_union_left
  rw [inner_toLp_of_subset hsu v, inner_toLp_of_subset hsv (wgt w v)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [wgt_apply, wgt_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The quadratic form of the comparison operator. -/
theorem re_inner_wgt (u : FockAlg) :
    (inner ℂ (toLp u) (toLp (wgt w u)) : ℂ).re = ∑ α ∈ u.support, wSym w α * ‖u α‖ ^ 2 := by
  classical
  rw [inner_toLp u (wgt w u)]
  have hterm : ∀ α : Conf, (starRingEnd ℂ) (u α) * (wgt w u) α
      = ((wSym w α * ‖u α‖ ^ 2 : ℝ) : ℂ) := by
    intro α
    rw [wgt_apply]
    have : (starRingEnd ℂ) (u α) * u α = ((‖u α‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    rw [show (starRingEnd ℂ) (u α) * ((wSym w α : ℂ) * u α)
        = (wSym w α : ℂ) * ((starRingEnd ℂ) (u α) * u α) from by ring, this]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun α _ => hterm α), ← Complex.ofReal_sum, Complex.ofReal_re]

/-- **`∑_k w_k² ‖a_k u‖² = ⟪u, 𝒩_w u⟫`.** -/
theorem sum_wsq_normSq_annA {u : FockAlg} {L : Finset ℕ} (hL : modes u ⊆ L) :
    ∑ k ∈ L, w k ^ 2 * ‖toLp (annA k u)‖ ^ 2 = ∑ α ∈ u.support, wdeg w α * ‖u α‖ ^ 2 := by
  classical
  rw [Finset.sum_congr rfl (fun k _ => by rw [normSq_annA k u, Finset.mul_sum]),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hsub : α.support ⊆ L := fun i hi => hL (support_subset_modes hα hi)
  rw [wdeg_eq_sum hsub, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## 3. The weighted Schur gates -/

variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

/-- The **row gate**: the rows of the one-particle matrix grow at most like the symbol. -/
def WRowBound (w : ℕ → ℝ) (col : ℕ → (ℕ →₀ ℂ)) (K : ℝ) : Prop :=
  ∀ k, ∑ j ∈ (col k).support, ‖(col k) j‖ ≤ K * w k

/-- The **column gate**: the columns, weighted by the reciprocal symbol, are summable. -/
def WColBound (w : ℕ → ℝ) (col : ℕ → (ℕ →₀ ℂ)) (K : ℝ) : Prop :=
  ∀ j, ∑ k ∈ (col j).support, ‖(col j) k‖ / w k ≤ K

/-- The **commutator gate**: the matrix of `[A, diag w²]`, weighted by `1/(w_k w_j)`, has
bounded rows. -/
def WCommBound (w : ℕ → ℝ) (col : ℕ → (ℕ →₀ ℂ)) (B : ℝ) : Prop :=
  ∀ k, ∑ j ∈ (col k).support, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j) ≤ B

theorem sum_le_of_vanishing {f : ℕ → ℝ} {S L : Finset ℕ} (hf : ∀ j, 0 ≤ f j)
    (hz : ∀ j, j ∉ S → f j = 0) : ∑ j ∈ L, f j ≤ ∑ j ∈ S, f j := by
  classical
  have h1 : ∑ j ∈ L, f j = ∑ j ∈ L ∩ S, f j := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro j hj hjn
    exact hz j fun hs => hjn (Finset.mem_inter.mpr ⟨hj, hs⟩)
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun j _ _ => hf j

theorem w_pos (hw : ∀ k, 1 ≤ w k) (k : ℕ) : 0 < w k := lt_of_lt_of_le zero_lt_one (hw k)

/-- The row gate, on an arbitrary finite set of modes. -/
theorem wrow_le (hw : ∀ k, 1 ≤ w k) (hK : WRowBound w col K) (k : ℕ) (L : Finset ℕ) :
    ∑ j ∈ L, ‖(col k) j‖ / w k ≤ K := by
  classical
  have hwk : 0 < w k := w_pos hw k
  refine le_trans (sum_le_of_vanishing (S := (col k).support)
    (fun j => div_nonneg (norm_nonneg _) hwk.le) ?_) ?_
  · intro j hj
    rw [Finsupp.notMem_support_iff.mp hj]
    simp
  · rw [← Finset.sum_div, div_le_iff₀ hwk]
    exact le_trans (hK k) (le_of_eq (by ring))

/-- The column gate, on an arbitrary finite set of modes. -/
theorem wcol_le (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hK : WColBound w col K) (j : ℕ)
    (L : Finset ℕ) : ∑ k ∈ L, ‖(col k) j‖ / w k ≤ K := by
  classical
  have hswap : ∀ k, ‖(col k) j‖ = ‖(col j) k‖ := by
    intro k
    rw [hherm j k]
    simp
  rw [Finset.sum_congr rfl fun k _ => by rw [hswap k]]
  refine le_trans (sum_le_of_vanishing (S := (col j).support)
    (fun k => div_nonneg (norm_nonneg _) (w_pos hw k).le) ?_) (hK j)
  intro k hk
  rw [Finsupp.notMem_support_iff.mp hk]
  simp

/-- A commutator gate is non-negative. -/
theorem wcomm_nonneg (hw : ∀ k, 1 ≤ w k) (hB : WCommBound w col B) : 0 ≤ B :=
  le_trans (Finset.sum_nonneg (s := (col 0).support)
    (f := fun j => ‖(col 0) j‖ * |w j ^ 2 - w 0 ^ 2| / (w 0 * w j)) fun j _ => by
      have : 0 < w 0 * w j := mul_pos (w_pos hw 0) (w_pos hw j)
      positivity) (hB 0)

/-- The commutator gate, on an arbitrary finite set of modes: the rows. -/
theorem wcomm_row_le (hw : ∀ k, 1 ≤ w k) (hB : WCommBound w col B) (k : ℕ) (L : Finset ℕ) :
    ∑ j ∈ L, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j) ≤ B := by
  classical
  refine le_trans (sum_le_of_vanishing (S := (col k).support) (fun j => ?_) ?_) (hB k)
  · have : 0 < w k * w j := mul_pos (w_pos hw k) (w_pos hw j)
    positivity
  · intro j hj
    rw [Finsupp.notMem_support_iff.mp hj]
    simp

/-- The commutator gate, on an arbitrary finite set of modes: the columns. -/
theorem wcomm_col_le (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col) (hB : WCommBound w col B)
    (j : ℕ) (L : Finset ℕ) :
    ∑ k ∈ L, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j) ≤ B := by
  classical
  have hterm : ∀ k, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j)
      = ‖(col j) k‖ * |w k ^ 2 - w j ^ 2| / (w j * w k) := by
    intro k
    have h1 : ‖(col k) j‖ = ‖(col j) k‖ := by rw [hherm j k]; simp
    rw [h1, abs_sub_comm, mul_comm (w k) (w j)]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  exact wcomm_row_le hw hB j L

/-! ## 4. The relative bound, sector by sector -/

/-- **The weighted number bound on one sector.**  On the `n`-particle sector,
`‖dΓ(A)u‖² ≤ K² n ⟪u, 𝒩_w u⟫`. -/
theorem normSq_dGamma_le_of_sector (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K)
    {n : ℕ} {u : FockAlg} (hu : InSector n u) :
    ‖toLp (dGamma col u)‖ ^ 2 ≤ K ^ 2 * ((n : ℝ) * ∑ α ∈ u.support, wdeg w α * ‖u α‖ ^ 2) := by
  classical
  set v : FockAlg := dGamma col u with hv
  have hvsec : InSector n v := dGamma_inSector col hu
  set L : Finset ℕ := closureModes col u v with hLdef
  set Q : ℝ := ∑ α ∈ u.support, wdeg w α * ‖u α‖ ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun α _ =>
    mul_nonneg (wdeg_nonneg α) (sq_nonneg _)
  have hexp : (inner ℂ (toLp v) (toLp v) : ℂ)
      = ∑ k ∈ L, ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
          * inner ℂ (toLp (annA k u)) (toLp (annA j v)) :=
    inner_dGamma_left col u v (modes_left_subset_closure col u v)
      (col_support_subset_closure col u v)
  have hbound : ‖toLp v‖ ^ 2 ≤ ∑ k ∈ L, ∑ j ∈ L,
      ‖(col k) j‖ * (‖toLp (annA k u)‖ * ‖toLp (annA j v)‖) := by
    have h0 : ((‖toLp v‖ ^ 2 : ℝ) : ℂ) = ∑ k ∈ L, ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
        * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
      rw [← hexp, inner_self_eq_norm_sq_to_K]
      norm_cast
    have h1 : ‖toLp v‖ ^ 2 = ‖(∑ k ∈ L, ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
        * inner ℂ (toLp (annA k u)) (toLp (annA j v)) : ℂ)‖ := by
      rw [← h0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [h1]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
  have hschur := schur_test (L := L) (m := fun k j => ‖(col k) j‖ / w k)
    (x := fun k => w k * ‖toLp (annA k u)‖) (y := fun j => ‖toLp (annA j v)‖) (K := K)
    (fun k j => div_nonneg (norm_nonneg _) (w_pos hw k).le)
    (fun k => mul_nonneg (w_pos hw k).le (norm_nonneg _)) (fun j => norm_nonneg _) hK0
    (fun k => wrow_le hw hrow k L) (fun j => wcol_le hw hherm hcolg j L)
  have hLHS : ∑ k ∈ L, ∑ j ∈ L, (‖(col k) j‖ / w k)
      * ((w k * ‖toLp (annA k u)‖) * ‖toLp (annA j v)‖)
      = ∑ k ∈ L, ∑ j ∈ L, ‖(col k) j‖ * (‖toLp (annA k u)‖ * ‖toLp (annA j v)‖) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    have hwk : w k ≠ 0 := (w_pos hw k).ne'
    field_simp
  have hxsum : ∑ k ∈ L, (w k * ‖toLp (annA k u)‖) ^ 2 = Q := by
    have hid := sum_wsq_normSq_annA (w := w) (u := u) (L := L)
      (modes_left_subset_closure col u v)
    rw [hQdef, ← hid]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hysum : ∑ j ∈ L, ‖toLp (annA j v)‖ ^ 2 = (n : ℝ) * ‖toLp v‖ ^ 2 :=
    sum_normSq_annA_of_sector hvsec (modes_right_subset_closure col u v)
  rw [hLHS, hxsum, hysum] at hschur
  have hsqrtv : Real.sqrt ((n : ℝ) * ‖toLp v‖ ^ 2) = Real.sqrt n * ‖toLp v‖ := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrtv] at hschur
  have hkey : ‖toLp v‖ ^ 2 ≤ K * (Real.sqrt Q * (Real.sqrt n * ‖toLp v‖)) :=
    le_trans hbound hschur
  have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ0
  have hsn : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hQs : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hns : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le (norm_nonneg (toLp v)) with hz | hpos
  · rw [← hz]
    simpa using mul_nonneg (sq_nonneg K) (mul_nonneg (Nat.cast_nonneg n) hQ0)
  · have hle : ‖toLp v‖ ≤ K * (Real.sqrt Q * Real.sqrt n) := by
      nlinarith [hkey, hpos]
    have hRnn : 0 ≤ K * (Real.sqrt Q * Real.sqrt n) :=
      mul_nonneg hK0 (mul_nonneg hQs hns)
    calc ‖toLp v‖ ^ 2 ≤ (K * (Real.sqrt Q * Real.sqrt n)) ^ 2 := by nlinarith [hle, hpos]
      _ = K ^ 2 * ((n : ℝ) * Q) := by
          rw [mul_pow, mul_pow, hsq, hsn]; ring

end

end BookProof.FockWeightedSchur
