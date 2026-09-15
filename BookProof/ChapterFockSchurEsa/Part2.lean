import Mathlib
import BookProof.ChapterFockSecondQuantization
import BookProof.ChapterCoreBoundsEsa
import BookProof.ChapterStoneBridge
import BookProof.ChapterEsaClosure
import BookProof.ChapterFockSchurEsa.Part1

/-!
# `dΓ(A)` for a Schur-class one-particle matrix: the number bound and essential
# self-adjointness on the finite-occupation core

`BookProof.ChapterFockDifferingBasesEsa` proves essential self-adjointness of a second
quantized Hamiltonian under the **unweighted `ℓ¹` gate** `∑ₖ ‖gₖ‖ < ∞` on its matrix
elements — a genuine restriction: a one-particle operator as simple as the
nearest-neighbour hopping `A_{jk} = 1` for `|j − k| = 1` has infinitely many entries of
modulus one and is not covered.

The gate that the physics actually asks for is the **Schur bound**

```text
∀ k, ∑_j |⟪e_j, A e_k⟫| ≤ K,
```

the classical criterion for boundedness of the one-particle operator `A`.  This module
proves that under that gate alone the second quantization `dΓ(A)` of
`BookProof.ChapterFockSecondQuantization` obeys the **number bound**

```text
‖dΓ(A) u‖ ≤ K ‖𝒩 u‖
```

on the finite-occupation core, that it **conserves the particle number** exactly, and
that it is therefore essentially self-adjoint there — with no diagonalizing basis and no
summability of the entries.

## What is proved

* `ndeg`, `numSym`, `InSector` — the particle number of a configuration, the comparison
  symbol `σ(α) = |α| + 1` and the sectors of the Fock space.
* `annA_inSector`, `creA_inSector`, `dGamma_inSector` — the ladder operators shift the
  sector by one, so `dΓ(A)` **preserves** it: second quantization conserves the particle
  number.
* `sum_normSq_annA` — `∑ₖ ‖a_k u‖² = ⟪u, 𝒩u⟫`, the identity behind the number bound.
* `schur_test` — the elementary (finite) Schur test `∑_{k,j} |A_{kj}| x_k y_j ≤ K‖x‖‖y‖`.
* **`norm_dGamma_le_of_sector`** — on the `n`-particle sector, `‖dΓ(A)u‖ ≤ K n ‖u‖`.
* **`norm_dGamma_le`** — hence `‖dΓ(A)u‖ ≤ K‖𝒩u‖` on the whole core, by orthogonality of
  the sectors.
* **`dGamma_essentiallySelfAdjointOn_core`** — the headline: for a Hermitian
  column-finite matrix with a Schur bound, `dΓ(A)` is essentially self-adjoint on the
  finite-occupation core, through
  `BookProof.CoreBounds.essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm`.
* `dGamma_stone_flow`, `dGamma_positiveExtension_eq_closure` — the unique self-adjoint
  realization, its unitary group (Stone), and — for a positive matrix — the identification
  of the Friedrichs extension with the closure.
* `hopCol`, `isHermCol_hopCol`, `schurBound_hopCol`, `hopCol_not_summable`,
  **`hop_essentiallySelfAdjointOn_core`** — non-vacuity: the nearest-neighbour hopping
  matrix satisfies the Schur gate with `K = 2` while its entries are *not* summable, so
  the statement is strictly outside the `ℓ¹` gate of `ChapterFockDifferingBasesEsa`.

## Honest boundary

The one-particle matrix must be **column-finite** (each `A e_k` a finite combination of
basis states) — that is what makes `dΓ(A)` map the finite-occupation core into itself —
and Hermitian, and it must satisfy the Schur bound, which forces `A` itself to be
*bounded*.  Nothing here covers an unbounded one-particle operator: for those the number
operator is not a comparison operator and `dΓ` needs a different gate.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.FockSchur

open BookProof.FockSecondQuantization BookProof.CoreBounds
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.YangMillsFriedrichs

noncomputable section

variable {col : ℕ → (ℕ →₀ ℂ)} {K : ℝ}
/-! ## 5. Sector decomposition and the number bound on the core -/

/-- The part of a state in the `n`-particle sector. -/
def sectorPart (n : ℕ) (u : FockAlg) : FockAlg := u.filter fun α => ndeg α = n

theorem sectorPart_inSector (n : ℕ) (u : FockAlg) : InSector n (sectorPart n u) := by
  classical
  intro α hα
  rw [sectorPart, Finsupp.support_filter] at hα
  exact (Finset.mem_filter.mp hα).2

theorem sectorPart_apply (n : ℕ) (u : FockAlg) (α : Conf) :
    sectorPart n u α = if ndeg α = n then u α else 0 := by
  classical
  simp [sectorPart, Finsupp.filter_apply]

theorem sum_sectorPart (u : FockAlg) :
    ∑ n ∈ u.support.image ndeg, sectorPart n u = u := by
  classical
  refine Finsupp.ext fun α => ?_
  rw [Finset.sum_apply']
  have hterm : ∀ n ∈ u.support.image ndeg,
      sectorPart n u α = if ndeg α = n then u α else 0 := fun n _ => sectorPart_apply n u α
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  by_cases hu : α ∈ u.support
  · rw [if_pos (Finset.mem_image_of_mem ndeg hu)]
  · rw [Finsupp.notMem_support_iff.mp hu]
    simp

/-- States of pairwise different sectors add in norm squared. -/
theorem normSq_sum_of_sectors {D : Finset ℕ} (f : ℕ → FockAlg)
    (hf : ∀ n ∈ D, InSector n (f n)) :
    ‖toLp (∑ n ∈ D, f n)‖ ^ 2 = ∑ n ∈ D, ‖toLp (f n)‖ ^ 2 := by
  classical
  have hmap : toLp (∑ n ∈ D, f n) = ∑ n ∈ D, toLp (f n) := by
    rw [← toLpL_apply, map_sum]
    rfl
  have hinner : (inner ℂ (toLp (∑ n ∈ D, f n)) (toLp (∑ n ∈ D, f n)) : ℂ)
      = ∑ n ∈ D, ∑ m ∈ D, (inner ℂ (toLp (f n)) (toLp (f m)) : ℂ) := by
    rw [hmap, sum_inner]
    exact Finset.sum_congr rfl fun n _ => inner_sum _ _ _
  have hdiag : ∀ n ∈ D, ∑ m ∈ D, (inner ℂ (toLp (f n)) (toLp (f m)) : ℂ)
      = ((‖toLp (f n)‖ ^ 2 : ℝ) : ℂ) := by
    intro n hn
    rw [Finset.sum_eq_single n]
    · rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    · intro m hm hmn
      exact inner_toLp_eq_zero_of_ne_sector (hf n hn) (hf m hm) (Ne.symm hmn)
    · intro hcon
      exact absurd hn hcon
  rw [Finset.sum_congr rfl hdiag] at hinner
  have hlhs : (inner ℂ (toLp (∑ n ∈ D, f n)) (toLp (∑ n ∈ D, f n)) : ℂ)
      = ((‖toLp (∑ n ∈ D, f n)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hlhs, ← Complex.ofReal_sum] at hinner
  exact_mod_cast hinner

/-- **The number bound.**  `‖dΓ(A)u‖ ≤ K‖𝒩u‖` on the finite-occupation core. -/
theorem norm_dGamma_le (hK : SchurBound col K) (hherm : IsHermCol col) (hK0 : 0 ≤ K)
    (u : FockAlg) :
    ‖toLp (dGamma col u)‖ ^ 2 ≤ K ^ 2 * ∑ α ∈ u.support, ((ndeg α : ℝ)) ^ 2 * ‖u α‖ ^ 2 := by
  classical
  set D : Finset ℕ := u.support.image ndeg with hD
  have hsplit : dGamma col u = ∑ n ∈ D, dGamma col (sectorPart n u) := by
    conv_lhs => rw [← sum_sectorPart u]
    rw [map_sum]
  have hsec : ∀ n ∈ D, InSector n (dGamma col (sectorPart n u)) := fun n _ =>
    dGamma_inSector col (sectorPart_inSector n u)
  rw [hsplit, normSq_sum_of_sectors _ hsec]
  have hterm : ∀ n ∈ D, ‖toLp (dGamma col (sectorPart n u))‖ ^ 2
      ≤ K ^ 2 * ((n : ℝ) ^ 2 * ‖toLp (sectorPart n u)‖ ^ 2) := by
    intro n _
    have h := norm_dGamma_le_of_sector hK hherm hK0 (sectorPart_inSector n u)
    have h0 : 0 ≤ ‖toLp (dGamma col (sectorPart n u))‖ := norm_nonneg _
    have h1 : 0 ≤ ‖toLp (sectorPart n u)‖ := norm_nonneg _
    nlinarith [h, h0, h1]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (sq_nonneg K)
  have hnorm : ∀ n : ℕ, ‖toLp (sectorPart n u)‖ ^ 2
      = ∑ α ∈ u.support.filter (fun α => ndeg α = n), ‖u α‖ ^ 2 := by
    intro n
    have hsub : (sectorPart n u).support ⊆ u.support.filter (fun α => ndeg α = n) := by
      rw [sectorPart, Finsupp.support_filter]
    rw [normSq_toLp_of_subset hsub]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [sectorPart_apply, if_pos (Finset.mem_filter.mp hα).2]
  calc ∑ n ∈ D, (n : ℝ) ^ 2 * ‖toLp (sectorPart n u)‖ ^ 2
      = ∑ n ∈ D, ∑ α ∈ u.support.filter (fun α => ndeg α = n),
          ((ndeg α : ℝ)) ^ 2 * ‖u α‖ ^ 2 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hnorm n, Finset.mul_sum]
        exact Finset.sum_congr rfl fun α hα => by rw [(Finset.mem_filter.mp hα).2]
    _ = ∑ α ∈ u.support, ((ndeg α : ℝ)) ^ 2 * ‖u α‖ ^ 2 :=
        Finset.sum_fiberwise_of_maps_to (fun α hα => Finset.mem_image_of_mem ndeg hα) _

/-! ## 6. Essential self-adjointness on the finite-occupation core -/

/-- The comparison operator `𝒩 + 1` applied to a finitely supported state. -/
def numWeight (u : FockAlg) : FockAlg :=
  Finsupp.onFinset u.support (fun α => (numSym α : ℂ) * u α) (by
    intro α hα
    by_contra hc
    have hz : u α = 0 := Finsupp.notMem_support_iff.mp hc
    simp only [hz, mul_zero, ne_eq, not_true_eq_false] at hα)

theorem numWeight_apply (u : FockAlg) (α : Conf) :
    numWeight u α = (numSym α : ℂ) * u α := rfl

theorem diagMax_numSym_eq (x : lpFiniteModes Conf) :
    (diagMax numSym (inclC numSym x) : Fock) = toLp (numWeight (fockEquiv.symm x)) := by
  refine lp.ext (funext fun α => ?_)
  rw [diagMax_coe]
  have hx : ((x : Fock) : Conf → ℂ) α = (fockEquiv.symm x) α := by
    rw [coe_fockEquiv_symm x]
    rfl
  rw [inclC_coe, hx]
  rfl

/-- The relative bound against the comparison operator, on the core. -/
theorem dGammaOp_coreRelBound (hK : SchurBound col K) (hherm : IsHermCol col) (hK0 : 0 ≤ K) :
    CoreRelBound numSym (dGammaOp col) K := by
  classical
  intro x
  set u : FockAlg := fockEquiv.symm x with hu
  have h1 : (dGammaOp col x : Fock) = toLp (dGamma col u) := coe_dGammaOp col x
  have h2 : (diagMax numSym (inclC numSym x) : Fock) = toLp (numWeight u) :=
    diagMax_numSym_eq x
  have hsupp : (numWeight u).support ⊆ u.support := Finsupp.support_onFinset_subset
  have hN : ‖toLp (numWeight u)‖ ^ 2 = ∑ α ∈ u.support, (numSym α) ^ 2 * ‖u α‖ ^ 2 := by
    rw [normSq_toLp_of_subset hsupp]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [numWeight_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  have hmono : ∑ α ∈ u.support, ((ndeg α : ℝ)) ^ 2 * ‖u α‖ ^ 2
      ≤ ∑ α ∈ u.support, (numSym α) ^ 2 * ‖u α‖ ^ 2 := by
    refine Finset.sum_le_sum fun α _ => ?_
    have h0 : (0:ℝ) ≤ (ndeg α : ℝ) := Nat.cast_nonneg _
    have hle : (ndeg α : ℝ) ≤ numSym α := by simp only [numSym]; linarith
    have hsq : ((ndeg α : ℝ)) ^ 2 ≤ (numSym α) ^ 2 := by nlinarith [h0, hle]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖u α‖)
  have hbound := norm_dGamma_le hK hherm hK0 u
  have hsq : ‖toLp (dGamma col u)‖ ^ 2 ≤ (K * ‖toLp (numWeight u)‖) ^ 2 := by
    rw [mul_pow, hN]
    refine le_trans hbound ?_
    exact mul_le_mul_of_nonneg_left hmono (sq_nonneg K)
  have hR : 0 ≤ K * ‖toLp (numWeight u)‖ := mul_nonneg hK0 (norm_nonneg _)
  have hL : 0 ≤ ‖toLp (dGamma col u)‖ := norm_nonneg _
  rw [h1, h2]
  nlinarith [hsq, hR, hL]

/-- **The commutator form vanishes**: `dΓ(A)` conserves the particle number. -/
theorem dGammaOp_commForm_zero (hherm : IsHermCol col) (x : lpFiniteModes Conf) :
    (inner ℂ (dGammaOp col x) ((diagMax numSym (inclC numSym x) : Fock)) : ℂ).im = 0 := by
  classical
  set w : FockAlg := fockEquiv.symm x with hw
  rw [coe_dGammaOp col x, diagMax_numSym_eq x]
  set D : Finset ℕ := w.support.image ndeg with hD
  have hnum : numWeight w = ∑ n ∈ D, ((n : ℂ) + 1) • sectorPart n w := by
    refine Finsupp.ext fun α => ?_
    rw [numWeight_apply, Finset.sum_apply']
    have hterm : ∀ n ∈ D, (((n : ℂ) + 1) • sectorPart n w) α
        = if ndeg α = n then ((ndeg α : ℂ) + 1) * w α else 0 := by
      intro n _
      rw [Finsupp.smul_apply, sectorPart_apply, smul_eq_mul]
      by_cases h : ndeg α = n
      · rw [if_pos h, if_pos h, h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    by_cases hα : α ∈ w.support
    · rw [if_pos (Finset.mem_image_of_mem ndeg hα)]
      simp only [numSym]
      push_cast
      ring
    · rw [Finsupp.notMem_support_iff.mp hα]
      simp
  have hXsum : toLp (dGamma col w) = ∑ n ∈ D, toLp (dGamma col (sectorPart n w)) := by
    conv_lhs => rw [← sum_sectorPart w]
    rw [map_sum, ← toLpL_apply, map_sum]
    rfl
  have hNsum : toLp (numWeight w) = ∑ n ∈ D, ((n : ℂ) + 1) • toLp (sectorPart n w) := by
    rw [hnum, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [map_smul, toLpL_apply]
  rw [hXsum, hNsum, sum_inner]
  have hterm : ∀ n ∈ D, (inner ℂ (toLp (dGamma col (sectorPart n w)))
        (∑ m ∈ D, ((m : ℂ) + 1) • toLp (sectorPart m w)) : ℂ)
      = ((n : ℂ) + 1)
        * inner ℂ (toLp (dGamma col (sectorPart n w))) (toLp (sectorPart n w)) := by
    intro n hn
    rw [inner_sum, Finset.sum_eq_single n]
    · rw [inner_smul_right]
    · intro m hm hmn
      rw [inner_smul_right,
        inner_toLp_eq_zero_of_ne_sector (dGamma_inSector col (sectorPart_inSector n w))
          (sectorPart_inSector m w) (Ne.symm hmn), mul_zero]
    · intro hcon
      exact absurd hn hcon
  rw [Finset.sum_congr rfl hterm, Complex.im_sum]
  refine Finset.sum_eq_zero fun n _ => ?_
  have hre : (inner ℂ (toLp (dGamma col (sectorPart n w))) (toLp (sectorPart n w)) : ℂ).im
      = 0 := by
    have hsymm := inner_dGamma_symm hherm (sectorPart n w) (sectorPart n w)
    have hconj := inner_conj_symm (𝕜 := ℂ) (toLp (sectorPart n w))
      (toLp (dGamma col (sectorPart n w)))
    have hz : (starRingEnd ℂ) (inner ℂ (toLp (dGamma col (sectorPart n w)))
        (toLp (sectorPart n w)) : ℂ)
        = inner ℂ (toLp (dGamma col (sectorPart n w))) (toLp (sectorPart n w)) := by
      rw [hconj, ← hsymm]
    exact Complex.conj_eq_iff_im.mp hz
  simp [Complex.mul_im, hre]

/-- **The headline.**  The second quantization of a Hermitian, column-finite one-particle
matrix satisfying the Schur bound `∑_j |A_{jk}| ≤ K` is essentially self-adjoint on the
finite-occupation core of the Fock space.  No basis diagonalizes `A`, and the entries need
not be summable. -/
theorem dGamma_essentiallySelfAdjointOn_core (hK : SchurBound col K) (hherm : IsHermCol col)
    (hK0 : 0 ≤ K) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp col) := by
  refine essentiallySelfAdjointOn_finiteModes_of_core_bounds_comm numSym numSym_nonneg
    (dGammaOp col) K ?_ (dGammaOp_coreRelBound hK hherm hK0) (dGammaOp_commForm_zero hherm)
  intro u v
  exact dGammaOp_symmetricOn hherm u v

/-! ## 7. Non-vacuity: nearest-neighbour hopping -/

/-- The **nearest-neighbour hopping** matrix `A_{jk} = 1` for `|j − k| = 1`, presented by
its columns. -/
def hopCol (k : ℕ) : ℕ →₀ ℂ :=
  if k = 0 then Finsupp.single 1 (1 : ℂ)
  else Finsupp.single (k + 1) (1 : ℂ) + Finsupp.single (k - 1) (1 : ℂ)

theorem hopCol_apply (k j : ℕ) : (hopCol k) j = if j = k + 1 ∨ k = j + 1 then 1 else 0 := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hcond : (j = 0 + 1 ∨ 0 = j + 1) ↔ (1 = j) := by omega
    rw [hopCol, if_pos rfl, Finsupp.single_apply, if_congr hcond rfl rfl]
  · have hcond : (j = k + 1 ∨ k = j + 1) ↔ (k + 1 = j ∨ k - 1 = j) := by omega
    rw [hopCol, if_neg (by omega), Finsupp.add_apply, Finsupp.single_apply,
      Finsupp.single_apply, if_congr hcond rfl rfl]
    by_cases h1 : k + 1 = j
    · have h2 : ¬ (k - 1 = j) := by omega
      simp [h1, h2]
    · by_cases h2 : k - 1 = j
      · simp [h1, h2]
      · simp [h1, h2]

theorem isHermCol_hopCol : IsHermCol hopCol := by
  intro j k
  rw [hopCol_apply, hopCol_apply]
  by_cases h : k = j + 1 ∨ j = k + 1
  · have h' : j = k + 1 ∨ k = j + 1 := h.symm
    simp [h, h']
  · have h' : ¬ (j = k + 1 ∨ k = j + 1) := fun hc => h hc.symm
    simp [h, h']

theorem support_hopCol_subset (k : ℕ) : (hopCol k).support ⊆ {k + 1, k - 1} := by
  classical
  intro j hj
  have hne : (hopCol k) j ≠ 0 := Finsupp.mem_support_iff.mp hj
  rw [hopCol_apply] at hne
  by_cases h : j = k + 1 ∨ k = j + 1
  · rcases h with h | h
    · simp [h]
    · have : j = k - 1 := by omega
      simp [this]
  · rw [if_neg h] at hne
    exact absurd rfl hne

theorem schurBound_hopCol : SchurBound hopCol 2 := by
  classical
  intro k
  have hle : ∀ j, ‖(hopCol k) j‖ ≤ 1 := by
    intro j
    rw [hopCol_apply]
    by_cases h : j = k + 1 ∨ k = j + 1 <;> simp [h]
  calc ∑ j ∈ (hopCol k).support, ‖(hopCol k) j‖
      ≤ ∑ j ∈ ({k + 1, k - 1} : Finset ℕ), ‖(hopCol k) j‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (support_hopCol_subset k)
          (fun j _ _ => norm_nonneg _)
    _ ≤ ∑ _j ∈ ({k + 1, k - 1} : Finset ℕ), (1:ℝ) := Finset.sum_le_sum fun j _ => hle j
    _ ≤ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        have : (({k + 1, k - 1} : Finset ℕ)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans
          (by simp)
        exact_mod_cast this

/-- The entries of the hopping matrix are **not** summable: the gate of
`ChapterFockDifferingBasesEsa` does not cover it. -/
theorem hopCol_not_summable : ¬ Summable fun k : ℕ => ‖(hopCol k) (k + 1)‖ := by
  intro hsum
  have hone : ∀ k : ℕ, ‖(hopCol k) (k + 1)‖ = 1 := by
    intro k
    rw [hopCol_apply, if_pos (Or.inl rfl)]
    simp
  have h := hsum.tendsto_atTop_zero
  simp only [hone] at h
  have h3 := tendsto_nhds_unique h (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop))
  norm_num at h3

/-- **The hopping Hamiltonian is essentially self-adjoint on the finite-occupation
core.** -/
theorem hop_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp hopCol) :=
  dGamma_essentiallySelfAdjointOn_core schurBound_hopCol isHermCol_hopCol (by norm_num)

/-! ## 8. The unique self-adjoint realization and its unitary group -/

/-- **The second-quantized dynamics.**  A Schur-class Hermitian one-particle matrix gives a
second quantization with a unique self-adjoint realization, and that realization generates a
complete unitary group (Stone). -/
theorem dGamma_stone_flow (hK : SchurBound col K) (hherm : IsHermCol col) (hK0 : 0 ≤ K) :
    ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)),
      IsSelfAdjointExtension (dGammaOp col) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ finiteOccupation_dense (dGammaOp_symmetricOn hherm)
    (dGamma_essentiallySelfAdjointOn_core hK hherm hK0)

/-- **For a positive Schur-class matrix the Friedrichs extension of `dΓ(A)` is the
closure**: there is nothing to select. -/
theorem dGamma_positiveExtension_eq_closure (hK : SchurBound col K) (hherm : IsHermCol col)
    (hK0 : 0 ≤ K) {Dom : Submodule ℂ Fock} {A : Dom →ₗ[ℂ] Fock}
    (hA : IsPositiveSelfAdjointExtension (dGammaOp col) A) :
    Dom = clDom (dGammaOp col) ∧
      ∀ (x : Fock) (h : x ∈ Dom) (h' : x ∈ clDom (dGammaOp col)),
        A ⟨x, h⟩ = clExt (dGammaOp col) finiteOccupation_dense
          (dGammaOp_symmetricOn hherm) ⟨x, h'⟩ :=
  positiveExtension_eq_closure_of_esa finiteOccupation_dense (dGammaOp_symmetricOn hherm)
    (dGamma_essentiallySelfAdjointOn_core hK hherm hK0) hA

/-- **The unitary group of the hopping Hamiltonian.** -/
theorem hop_stone_flow :
    ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)),
      IsSelfAdjointExtension (dGammaOp hopCol) T.op ∧ IsStoneFlow T U :=
  dGamma_stone_flow schurBound_hopCol isHermCol_hopCol (by norm_num)

end

end BookProof.FockSchur
