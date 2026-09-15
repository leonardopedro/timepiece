import Mathlib
import BookProof.ChapterFockSchurEsa
import BookProof.ChapterFockWeightedSchurEsa.Part1

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
/-! ## 5. The relative bound on the core -/

/-- **The weighted number bound.**  `‖dΓ(A)u‖ ≤ K‖σ u‖` on the finite-occupation core, with
`σ(α) = ∑_k w_k² α_k + 1`. -/
theorem normSq_dGamma_le_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) (u : FockAlg) :
    ‖toLp (dGamma col u)‖ ^ 2 ≤ K ^ 2 * ∑ α ∈ u.support, wSym w α ^ 2 * ‖u α‖ ^ 2 := by
  classical
  set D : Finset ℕ := u.support.image ndeg with hD
  have hsplit : dGamma col u = ∑ n ∈ D, dGamma col (sectorPart n u) := by
    conv_lhs => rw [← sum_sectorPart u]
    rw [map_sum]
  have hsec : ∀ n ∈ D, InSector n (dGamma col (sectorPart n u)) := fun n _ =>
    dGamma_inSector col (sectorPart_inSector n u)
  rw [hsplit, normSq_sum_of_sectors _ hsec]
  have hterm : ∀ n ∈ D, ‖toLp (dGamma col (sectorPart n u))‖ ^ 2
      ≤ K ^ 2 * ∑ α ∈ u.support.filter (fun α => ndeg α = n), wSym w α ^ 2 * ‖u α‖ ^ 2 := by
    intro n _
    set F : Finset Conf := u.support.filter (fun α => ndeg α = n) with hF
    have hsub : (sectorPart n u).support ⊆ F := by
      rw [sectorPart, Finsupp.support_filter]
    have h1 : ∑ α ∈ (sectorPart n u).support, wdeg w α * ‖(sectorPart n u) α‖ ^ 2
        = ∑ α ∈ F, wdeg w α * ‖u α‖ ^ 2 := by
      rw [Finset.sum_subset hsub (fun α _ hα => by
        rw [Finsupp.notMem_support_iff.mp hα]; simp)]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [sectorPart_apply, if_pos (Finset.mem_filter.mp hα).2]
    have hbase := normSq_dGamma_le_of_sector hw hherm hrow hcolg hK0
      (sectorPart_inSector n u)
    rw [h1] at hbase
    refine le_trans hbase ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun α hα => ?_
    have hn : ndeg α = n := (Finset.mem_filter.mp hα).2
    have h2 : ((n : ℝ)) ≤ wdeg w α := by
      rw [← hn]; exact ndeg_le_wdeg hw α
    have h3 : (0:ℝ) ≤ wdeg w α := wdeg_nonneg α
    have h4 : (n : ℝ) * wdeg w α ≤ wSym w α ^ 2 := by
      have : wSym w α = wdeg w α + 1 := rfl
      nlinarith
    have h5 : (0:ℝ) ≤ ‖u α‖ ^ 2 := sq_nonneg _
    calc (n : ℝ) * (wdeg w α * ‖u α‖ ^ 2) = ((n : ℝ) * wdeg w α) * ‖u α‖ ^ 2 := by ring
      _ ≤ wSym w α ^ 2 * ‖u α‖ ^ 2 := mul_le_mul_of_nonneg_right h4 h5
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (sq_nonneg K)
  exact Finset.sum_fiberwise_of_maps_to (fun α hα => Finset.mem_image_of_mem ndeg hα) _

/-! ## 6. The commutator estimate -/

/-- **The commutator estimate.**  `|⟪u, i[dΓ(A), σ]u⟫| ≤ B⟪u, σu⟫` on the core: the part of
`⟪dΓ(A)u, σu⟫` that survives conjugation is
`∑_{k,j} conj(A_{kj})(w_j² − w_k²)⟪a_k u, a_j u⟫`. -/
theorem im_inner_dGamma_wgt_bound (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hBg : WCommBound w col B) (u : FockAlg) :
    |(-2 : ℝ) * (inner ℂ (toLp (dGamma col u)) (toLp (wgt w u)) : ℂ).im|
      ≤ B * (inner ℂ (toLp u) (toLp (wgt w u)) : ℂ).re := by
  classical
  set N : FockAlg := wgt w u with hNdef
  set L : Finset ℕ := closureModes col u N with hLdef
  set z : ℂ := inner ℂ (toLp (dGamma col u)) (toLp N) with hzdef
  set f : ℕ → ℕ → ℂ := fun k j => (starRingEnd ℂ) ((col k) j)
    * inner ℂ (toLp (annA k u)) (toLp (wgt w (annA j u))) with hfdef
  set g : ℕ → ℕ → ℂ := fun k j => (starRingEnd ℂ) ((col k) j) * ((w j ^ 2 : ℝ) : ℂ)
    * inner ℂ (toLp (annA k u)) (toLp (annA j u)) with hgdef
  set p : ℕ → ℕ → ℂ := fun k j => (starRingEnd ℂ) ((col k) j) * ((w k ^ 2 : ℝ) : ℂ)
    * inner ℂ (toLp (annA k u)) (toLp (annA j u)) with hpdef
  have hexp : z = ∑ k ∈ L, ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
      * inner ℂ (toLp (annA k u)) (toLp (annA j N)) :=
    inner_dGamma_left col u N (modes_left_subset_closure col u N)
      (col_support_subset_closure col u N)
  have hterm : ∀ k j, (starRingEnd ℂ) ((col k) j)
      * (inner ℂ (toLp (annA k u)) (toLp (annA j N)) : ℂ) = f k j + g k j := by
    intro k j
    have hsplit : toLp (annA j N)
        = toLp (wgt w (annA j u)) + ((w j ^ 2 : ℝ) : ℂ) • toLp (annA j u) := by
      rw [hNdef, annA_wgt j u, ← toLpL_apply, map_add, map_smul, toLpL_apply, toLpL_apply]
    rw [hsplit, inner_add_right, inner_smul_right, hfdef, hgdef]
    ring
  set P : ℂ := ∑ k ∈ L, ∑ j ∈ L, f k j with hPdef
  set Q : ℂ := ∑ k ∈ L, ∑ j ∈ L, g k j with hQdef
  set R : ℂ := ∑ k ∈ L, ∑ j ∈ L, p k j with hRdef
  have hzPQ : z = P + Q := by
    rw [hexp, Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hterm k j)),
      hPdef, hQdef]
    simp only [Finset.sum_add_distrib]
  have hconjf : ∀ k j, (starRingEnd ℂ) (f k j) = f j k := by
    intro k j
    have h1 : (starRingEnd ℂ) ((starRingEnd ℂ) ((col k) j)) = (col k) j := by simp
    have h2 : (starRingEnd ℂ) (inner ℂ (toLp (annA k u)) (toLp (wgt w (annA j u))) : ℂ)
        = inner ℂ (toLp (wgt w (annA j u))) (toLp (annA k u)) := inner_conj_symm _ _
    have h3 : (inner ℂ (toLp (wgt w (annA j u))) (toLp (annA k u)) : ℂ)
        = inner ℂ (toLp (annA j u)) (toLp (wgt w (annA k u))) := inner_wgt_symm _ _
    have h4 : (starRingEnd ℂ) ((col j) k) = (col k) j := by rw [hherm j k]; simp
    simp only [hfdef]
    rw [map_mul, h1, h2, h3, h4]
  have hconjg : ∀ k j, (starRingEnd ℂ) (g k j) = p j k := by
    intro k j
    have h1 : (starRingEnd ℂ) ((starRingEnd ℂ) ((col k) j)) = (col k) j := by simp
    have h2 : (starRingEnd ℂ) (inner ℂ (toLp (annA k u)) (toLp (annA j u)) : ℂ)
        = inner ℂ (toLp (annA j u)) (toLp (annA k u)) := inner_conj_symm _ _
    have h4 : (starRingEnd ℂ) ((col j) k) = (col k) j := by rw [hherm j k]; simp
    simp only [hgdef, hpdef]
    rw [map_mul, map_mul, h1, Complex.conj_ofReal, h2, h4]
  have hconjP : (starRingEnd ℂ) P = P := by
    simp only [hPdef, map_sum]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hconjf k j))]
    exact Finset.sum_comm
  have hconjQ : (starRingEnd ℂ) Q = R := by
    simp only [hQdef, hRdef, map_sum]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hconjg k j))]
    exact Finset.sum_comm
  have hdiff : z - (starRingEnd ℂ) z = Q - R := by
    rw [hzPQ, map_add, hconjP, hconjQ]
    ring
  have hQR : Q - R = ∑ k ∈ L, ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
      * ((w j ^ 2 - w k ^ 2 : ℝ) : ℂ) * inner ℂ (toLp (annA k u)) (toLp (annA j u)) := by
    rw [hQdef, hRdef, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hgdef, hpdef]
    push_cast
    ring
  -- the Schur estimate of the surviving term
  set x : ℕ → ℝ := fun k => ‖toLp (annA k u)‖ with hxdef
  have hnorm : ‖Q - R‖ ≤ ∑ k ∈ L, ∑ j ∈ L,
      (‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j)) * ((w k * x k) * (w j * x j)) := by
    rw [hQR]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    have hwk : w k ≠ 0 := (w_pos hw k).ne'
    have hwj : w j ≠ 0 := (w_pos hw j).ne'
    have hstep : ‖(starRingEnd ℂ) ((col k) j) * ((w j ^ 2 - w k ^ 2 : ℝ) : ℂ)
        * inner ℂ (toLp (annA k u)) (toLp (annA j u))‖
        ≤ ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| * (x k * x j) := by
      rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _)
        (mul_nonneg (norm_nonneg _) (abs_nonneg _))
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  have hB0 : 0 ≤ B := wcomm_nonneg hw hBg
  have hschur := schur_test (L := L)
    (m := fun k j => ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j))
    (x := fun k => w k * x k) (y := fun j => w j * x j) (K := B)
    (fun k j => by
      have : 0 < w k * w j := mul_pos (w_pos hw k) (w_pos hw j)
      positivity)
    (fun k => mul_nonneg (w_pos hw k).le (norm_nonneg _))
    (fun j => mul_nonneg (w_pos hw j).le (norm_nonneg _)) hB0
    (fun k => wcomm_row_le hw hBg k L) (fun j => wcomm_col_le hw hherm hBg j L)
  set S : ℝ := ∑ k ∈ L, (w k * x k) ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsqrtS : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS0
  rw [hsqrtS] at hschur
  have hSval : S = ∑ α ∈ u.support, wdeg w α * ‖u α‖ ^ 2 := by
    have hid := sum_wsq_normSq_annA (w := w) (u := u) (L := L)
      (modes_left_subset_closure col u N)
    rw [hSdef, ← hid]
    exact Finset.sum_congr rfl fun k _ => by rw [hxdef]; ring
  have hSle : S ≤ (inner ℂ (toLp u) (toLp N) : ℂ).re := by
    rw [hSval, hNdef, re_inner_wgt]
    refine Finset.sum_le_sum fun α _ => ?_
    have : wdeg w α ≤ wSym w α := by simp only [wSym]; linarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have habs : |(-2 : ℝ) * z.im| = ‖z - (starRingEnd ℂ) z‖ := by
    rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_mul]
    norm_num
  calc |(-2 : ℝ) * z.im| = ‖Q - R‖ := by rw [habs, hdiff]
    _ ≤ ∑ k ∈ L, ∑ j ∈ L, (‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j))
          * ((w k * x k) * (w j * x j)) := hnorm
    _ ≤ B * S := hschur
    _ ≤ B * (inner ℂ (toLp u) (toLp N) : ℂ).re := mul_le_mul_of_nonneg_left hSle hB0

/-! ## 7. Essential self-adjointness on the finite-occupation core -/

theorem diagMax_wSym_eq (x : lpFiniteModes Conf) :
    (diagMax (wSym w) (inclC (wSym w) x) : Fock) = toLp (wgt w (fockEquiv.symm x)) := by
  refine lp.ext (funext fun α => ?_)
  rw [diagMax_coe]
  have hx : ((x : Fock) : Conf → ℂ) α = (fockEquiv.symm x) α := by
    rw [coe_fockEquiv_symm x]
    rfl
  rw [inclC_coe, hx]
  rfl

theorem normSq_toLp_wgt (u : FockAlg) :
    ‖toLp (wgt w u)‖ ^ 2 = ∑ α ∈ u.support, wSym w α ^ 2 * ‖u α‖ ^ 2 := by
  rw [normSq_toLp_of_subset (support_wgt_subset u)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [wgt_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The relative bound against the weighted comparison operator, on the core. -/
theorem dGammaOp_coreRelBound_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) :
    CoreRelBound (wSym w) (dGammaOp col) K := by
  intro x
  set u : FockAlg := fockEquiv.symm x with hu
  rw [coe_dGammaOp col x, diagMax_wSym_eq x]
  have hsq : ‖toLp (dGamma col u)‖ ^ 2 ≤ (K * ‖toLp (wgt w u)‖) ^ 2 := by
    rw [mul_pow, normSq_toLp_wgt]
    exact normSq_dGamma_le_w hw hherm hrow hcolg hK0 u
  have hR : 0 ≤ K * ‖toLp (wgt w u)‖ := mul_nonneg hK0 (norm_nonneg _)
  have hL : 0 ≤ ‖toLp (dGamma col u)‖ := norm_nonneg _
  nlinarith [hsq, hR, hL]

/-- The commutator bound on the core, in the form the Faris–Lavine instrument asks for. -/
theorem dGammaOp_commForm_bound_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hBg : WCommBound w col B) (x : lpFiniteModes Conf) :
    |(-2 : ℝ) * (inner ℂ (dGammaOp col x)
        ((diagMax (wSym w) (inclC (wSym w) x) : Fock)) : ℂ).im|
      ≤ B * (inner ℂ ((x : Fock)) ((diagMax (wSym w) (inclC (wSym w) x) : Fock)) : ℂ).re := by
  rw [coe_dGammaOp col x, diagMax_wSym_eq x, coe_fockEquiv_symm x]
  exact im_inner_dGamma_wgt_bound hw hherm hBg _

/-- **The headline.**  The second quantization of a Hermitian, column-finite one-particle
matrix satisfying the Schur gates *weighted by the one-particle symbol* `w` — the row gate
`∑_j |A_{kj}| ≤ K w_k`, the column gate `∑_k |A_{jk}|/w_k ≤ K` and the commutator gate
`∑_j |A_{kj}||w_j² − w_k²|/(w_k w_j) ≤ B` — is essentially self-adjoint on the
finite-occupation core of the Fock space.  The one-particle operator need not be
bounded. -/
theorem dGamma_essentiallySelfAdjointOn_core_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K)
    (hBg : WCommBound w col B) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp col) :=
  essentiallySelfAdjointOn_finiteModes_of_core_bounds (wSym w) (fun α => wSym_nonneg α)
    (dGammaOp col) K B (wcomm_nonneg hw hBg) (fun u v => dGammaOp_symmetricOn hherm u v)
    (dGammaOp_coreRelBound_w hw hherm hrow hcolg hK0) (dGammaOp_commForm_bound_w hw hherm hBg)

/-- **The dynamics.**  The unique self-adjoint realization of `dΓ(A)` generates a complete
unitary group. -/
theorem dGamma_stone_flow_w (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K)
    (hBg : WCommBound w col B) :
    ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)),
      IsSelfAdjointExtension (dGammaOp col) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ finiteOccupation_dense (dGammaOp_symmetricOn hherm)
    (dGamma_essentiallySelfAdjointOn_core_w hw hherm hrow hcolg hK0 hBg)

end

end BookProof.FockWeightedSchur
