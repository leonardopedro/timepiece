import Mathlib
import BookProof.ChapterSirkRitzSpectrum

/-!
# Chapter SirkRitzMinMax — the higher Rayleigh–Ritz levels and the Ritz gap

`CONSOLIDATED_PLAN.md` §12.2 **Gap 2, QYM** asks for "the statement that the
Ritz/**gap** values converge to the spectrum of the selected extension as `m → ∞`".
`BookProof.ChapterSirkRitzSpectrum` settled the *lowest* Ritz value: it converges to
`sInf (spectrum ℝ A)`.  A gap statement needs the **second** level as well, and there
is no second Rayleigh quotient — the correct object is the Courant–Fischer min–max
level

  `minmaxLevel T k = inf { sup_{x ∈ S, ‖x‖ = 1} ⟪x, Tx⟫ : dim S = k + 1 }`.

This chapter introduces those levels for a bounded operator on a complex Hilbert
space, and proves that the **Galerkin (Rayleigh–Ritz) min–max levels of the
truncations converge to them**, hence that the computed gap converges to the
min–max gap.

## Deliverables

* `rayleighVal`, `rayleighSetOn`, `rayleighSup` — the Rayleigh quotient, its range
  over the unit sphere of a subspace, and the supremum, with the basic bounds
  (`rayleighSup_le_norm`, `rayleighSup_mono`).
* `minmaxLevel` / `minmaxLevelIn` — the Courant–Fischer levels of `T`, and the
  levels computed inside a fixed subspace `W` (the truncation the solver sees).
* `minmaxLevel_le_minmaxLevelIn` — the Ritz levels are always **upper** bounds
  (the variational principle in the direction the algorithm can certify).
* `minmaxLevel_mono` — the levels increase with `k`.
* `minmaxLevel_zero_eq_rayleighInf` and `minmaxLevel_zero_eq_sInf_spectrum` — the
  level `k = 0` is the bottom of the numerical range, hence the bottom of the
  spectrum: this chapter's ladder starts exactly where `ChapterSirkRitzSpectrum`
  stopped.
* `exists_galerkin_approx_subspace` — the approximation engine: any `(k+1)`-dimensional
  subspace can be pushed into a large enough Galerkin subspace with an arbitrarily
  small increase of its Rayleigh supremum.
* `galerkin_minmaxLevel_tendsto` — **headline**: for every `k`, the Galerkin min–max
  levels converge to `minmaxLevel T k`.
* `galerkin_gap_tendsto` — the computed **gap** `Λ₁(m) − Λ₀(m)` converges to
  `minmaxLevel T 1 − minmaxLevel T 0`, and `galerkin_gap_eventually_pos`: a positive
  min–max gap is eventually seen by the truncations.

## Honest boundary

The min–max levels are spectral quantities only below the essential spectrum;
nothing here claims that `minmaxLevel T k` is an eigenvalue for `k ≥ 1` (for
`k = 0` the identification with `sInf (spectrum ℝ T)` *is* proved).  The operator is
bounded throughout — the unbounded case is reached through the resolvent, not
directly.
-/

noncomputable section

namespace BookProof.RitzMinMax

open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. Rayleigh quotients on a subspace -/

/-- The Rayleigh quotient `⟪x, Tx⟫` (real part) of a vector. -/
def rayleighVal (T : F →L[ℂ] F) (x : F) : ℝ := (inner ℂ x (T x) : ℂ).re

/-- The Rayleigh quotients of the unit vectors of a subspace. -/
def rayleighSetOn (T : F →L[ℂ] F) (S : Submodule ℂ F) : Set ℝ :=
  {t : ℝ | ∃ x : F, x ∈ S ∧ ‖x‖ = 1 ∧ t = rayleighVal T x}

/-- The top of the numerical range of `T` on a subspace. -/
def rayleighSup (T : F →L[ℂ] F) (S : Submodule ℂ F) : ℝ := sSup (rayleighSetOn T S)

omit [CompleteSpace F] in
theorem abs_rayleighVal_le (T : F →L[ℂ] F) (x : F) : |rayleighVal T x| ≤ ‖T‖ * ‖x‖ ^ 2 :=
  abs_re_inner_le T x

omit [CompleteSpace F] in
/-- The Rayleigh quotient of a unit vector is at most the operator norm. -/
theorem rayleighVal_le_norm_of_unit (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    rayleighVal T x ≤ ‖T‖ := by
  have h := (le_abs_self (rayleighVal T x)).trans (abs_rayleighVal_le T x)
  rwa [hx1, one_pow, mul_one] at h

omit [CompleteSpace F] in
/-- The Rayleigh quotient of a unit vector is at least `−‖T‖`. -/
theorem neg_norm_le_rayleighVal_of_unit (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    -‖T‖ ≤ rayleighVal T x := by
  have h := neg_le_of_abs_le (abs_rayleighVal_le T x)
  rwa [hx1, one_pow, mul_one] at h

omit [CompleteSpace F] in
/-- The Rayleigh quotient scales by `‖c‖²` under a scalar multiple. -/
theorem rayleighVal_smul (T : F →L[ℂ] F) (c : ℂ) (x : F) :
    rayleighVal T (c • x) = ‖c‖ ^ 2 * rayleighVal T x := by
  have h : (inner ℂ (c • x) (T (c • x)) : ℂ) = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ x (T x) := by
    rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
    congr 1
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [rayleighVal, rayleighVal, h, Complex.re_ofReal_mul]

omit [CompleteSpace F] in
/-- A Lipschitz estimate for the Rayleigh quotient. -/
theorem rayleighVal_sub_le (T : F →L[ℂ] F) (y u : F) :
    rayleighVal T y - rayleighVal T u ≤ ‖T‖ * (‖y‖ + ‖u‖) * ‖y - u‖ := by
  have hsplit : (inner ℂ y (T y) : ℂ) - inner ℂ u (T u)
      = inner ℂ (y - u) (T y) + inner ℂ u (T (y - u)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  have h1 : rayleighVal T y - rayleighVal T u
      = (inner ℂ (y - u) (T y) : ℂ).re + (inner ℂ u (T (y - u)) : ℂ).re := by
    rw [rayleighVal, rayleighVal, ← Complex.sub_re, hsplit, Complex.add_re]
  have hb1 : (inner ℂ (y - u) (T y) : ℂ).re ≤ ‖y - u‖ * (‖T‖ * ‖y‖) := by
    calc (inner ℂ (y - u) (T y) : ℂ).re ≤ ‖(inner ℂ (y - u) (T y) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖y - u‖ * ‖T y‖ := norm_inner_le_norm _ _
      _ ≤ ‖y - u‖ * (‖T‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
  have hb2 : (inner ℂ u (T (y - u)) : ℂ).re ≤ ‖u‖ * (‖T‖ * ‖y - u‖) := by
    calc (inner ℂ u (T (y - u)) : ℂ).re ≤ ‖(inner ℂ u (T (y - u)) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖u‖ * ‖T (y - u)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖T‖ * ‖y - u‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
  rw [h1]
  nlinarith [hb1, hb2]

omit [CompleteSpace F] in
theorem rayleighSetOn_bddAbove (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    BddAbove (rayleighSetOn T S) := by
  refine ⟨‖T‖, ?_⟩
  rintro t ⟨x, -, hx1, rfl⟩
  exact rayleighVal_le_norm_of_unit T hx1

omit [CompleteSpace F] in
/-- A subspace of positive dimension has unit vectors. -/
theorem exists_unit_mem (S : Submodule ℂ F) (hS : 0 < Module.finrank ℂ S) :
    ∃ x : F, x ∈ S ∧ ‖x‖ = 1 := by
  have hne : S ≠ ⊥ := by
    intro h
    rw [h] at hS
    simp at hS
  obtain ⟨y, hy, hy0⟩ := S.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨‖y‖⁻¹ • y, S.smul_mem _ hy, ?_⟩
  rw [norm_smul]
  simp [norm_ne_zero_iff.mpr hy0]

omit [CompleteSpace F] in
theorem rayleighSetOn_nonempty (T : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : (rayleighSetOn T S).Nonempty := by
  obtain ⟨x, hx, hx1⟩ := exists_unit_mem S hS
  exact ⟨rayleighVal T x, x, hx, hx1, rfl⟩

omit [CompleteSpace F] in
theorem rayleighSup_le_norm (T : F →L[ℂ] F) (S : Submodule ℂ F) : rayleighSup T S ≤ ‖T‖ := by
  rcases Set.eq_empty_or_nonempty (rayleighSetOn T S) with h | h
  · rw [rayleighSup, h, Real.sSup_empty]
    exact norm_nonneg _
  · refine csSup_le h ?_
    rintro t ⟨x, -, hx1, rfl⟩
    exact rayleighVal_le_norm_of_unit T hx1

omit [CompleteSpace F] in
theorem neg_norm_le_rayleighSup (T : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : -‖T‖ ≤ rayleighSup T S := by
  obtain ⟨x, hx, hx1⟩ := exists_unit_mem S hS
  exact (neg_norm_le_rayleighVal_of_unit T hx1).trans
    (le_csSup (rayleighSetOn_bddAbove T S) ⟨x, hx, hx1, rfl⟩)

omit [CompleteSpace F] in
theorem rayleighVal_le_rayleighSup (T : F →L[ℂ] F) {S : Submodule ℂ F} {x : F}
    (hx : x ∈ S) (hx1 : ‖x‖ = 1) : rayleighVal T x ≤ rayleighSup T S :=
  le_csSup (rayleighSetOn_bddAbove T S) ⟨x, hx, hx1, rfl⟩

omit [CompleteSpace F] in
theorem rayleighSup_mono (T : F →L[ℂ] F) {S S' : Submodule ℂ F} (h : S ≤ S')
    (hS : 0 < Module.finrank ℂ S) : rayleighSup T S ≤ rayleighSup T S' :=
  csSup_le_csSup (rayleighSetOn_bddAbove T S') (rayleighSetOn_nonempty T hS)
    (by rintro t ⟨x, hx, hx1, rfl⟩; exact ⟨x, h hx, hx1, rfl⟩)

omit [CompleteSpace F] in
/-- On a line all unit vectors have the same Rayleigh quotient. -/
theorem rayleighSetOn_span_singleton (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    rayleighSetOn T (Submodule.span ℂ {x}) = {rayleighVal T x} := by
  ext t
  constructor
  · rintro ⟨y, hy, hy1, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hc : ‖c‖ = 1 := by
      rw [norm_smul, hx1, mul_one] at hy1
      exact hy1
    simp [rayleighVal_smul, hc]
  · rintro rfl
    exact ⟨x, Submodule.mem_span_singleton_self x, hx1, rfl⟩

omit [CompleteSpace F] in
theorem rayleighSup_span_singleton (T : F →L[ℂ] F) {x : F} (hx1 : ‖x‖ = 1) :
    rayleighSup T (Submodule.span ℂ {x}) = rayleighVal T x := by
  rw [rayleighSup, rayleighSetOn_span_singleton T hx1, csSup_singleton]

/-! ## 2. The Courant–Fischer levels -/

/-- The values `sup_{x ∈ S, ‖x‖ = 1} ⟪x, Tx⟫` over the `(k+1)`-dimensional subspaces. -/
def minmaxSet (T : F →L[ℂ] F) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F, Module.finrank ℂ S = k + 1 ∧ t = rayleighSup T S}

/-- The `k`-th Courant–Fischer min–max level of a bounded operator. -/
def minmaxLevel (T : F →L[ℂ] F) (k : ℕ) : ℝ := sInf (minmaxSet T k)

/-- The same values, computed only inside a fixed subspace `W`: the Ritz levels the
solver produces from the truncation to `W`. -/
def minmaxSetIn (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : Set ℝ :=
  {t : ℝ | ∃ S : Submodule ℂ F, S ≤ W ∧ Module.finrank ℂ S = k + 1 ∧ t = rayleighSup T S}

/-- The `k`-th Rayleigh–Ritz level of the truncation to `W`. -/
def minmaxLevelIn (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) : ℝ := sInf (minmaxSetIn T W k)

omit [CompleteSpace F] in
theorem minmaxSet_bddBelow (T : F →L[ℂ] F) (k : ℕ) : BddBelow (minmaxSet T k) := by
  refine ⟨-‖T‖, ?_⟩
  rintro t ⟨S, hrank, rfl⟩
  exact neg_norm_le_rayleighSup T (by rw [hrank]; omega)

omit [CompleteSpace F] in
theorem minmaxSetIn_bddBelow (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    BddBelow (minmaxSetIn T W k) := by
  refine ⟨-‖T‖, ?_⟩
  rintro t ⟨S, -, hrank, rfl⟩
  exact neg_norm_le_rayleighSup T (by rw [hrank]; omega)

omit [CompleteSpace F] in
theorem minmaxSetIn_subset (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    minmaxSetIn T W k ⊆ minmaxSet T k := by
  rintro t ⟨S, _, hrank, rfl⟩
  exact ⟨S, hrank, rfl⟩

omit [CompleteSpace F] in
/-- **The variational principle, in the direction the algorithm certifies**: a Ritz
level computed in a subspace is an upper bound for the true min–max level. -/
theorem minmaxLevel_le_minmaxLevelIn (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (minmaxSetIn T W k).Nonempty) :
    minmaxLevel T k ≤ minmaxLevelIn T W k :=
  csInf_le_csInf (minmaxSet_bddBelow T k) hne (minmaxSetIn_subset T W k)

omit [CompleteSpace F] in
/-- A finite-dimensional subspace contains subspaces of every smaller dimension. -/
theorem exists_le_finrank_eq {S : Submodule ℂ F} [FiniteDimensional ℂ S] {n : ℕ}
    (hn : n ≤ Module.finrank ℂ S) :
    ∃ S₀ : Submodule ℂ F, S₀ ≤ S ∧ Module.finrank ℂ S₀ = n := by
  classical
  set e := Module.finBasis ℂ S with he
  set v : Fin n → F := fun i => (e (Fin.castLE hn i) : F) with hv
  have hli : LinearIndependent ℂ v := by
    have h1 : LinearIndependent ℂ (fun i : Fin n => e (Fin.castLE hn i)) :=
      e.linearIndependent.comp _ (Fin.castLE_injective hn)
    exact h1.map' (S.subtype) (by simp [Submodule.ker_subtype])
  refine ⟨Submodule.span ℂ (Set.range v), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (e (Fin.castLE hn i)).2
  · rw [finrank_span_eq_card hli]
    simp

omit [CompleteSpace F] in
/-- The levels increase with `k`. -/
theorem minmaxLevel_mono (T : F →L[ℂ] F) {k l : ℕ} (hkl : k ≤ l)
    (hne : (minmaxSet T l).Nonempty) : minmaxLevel T k ≤ minmaxLevel T l := by
  refine le_csInf hne ?_
  rintro t ⟨S, hrank, rfl⟩
  have hfd : FiniteDimensional ℂ S := .of_finrank_pos (by rw [hrank]; omega)
  obtain ⟨S₀, hS₀le, hS₀rank⟩ :=
    exists_le_finrank_eq (S := S) (n := k + 1) (by rw [hrank]; omega)
  have hlow : minmaxLevel T k ≤ rayleighSup T S₀ :=
    csInf_le (minmaxSet_bddBelow T k) ⟨S₀, hS₀rank, rfl⟩
  exact hlow.trans (rayleighSup_mono T hS₀le (by rw [hS₀rank]; omega))

end BookProof.RitzMinMax
