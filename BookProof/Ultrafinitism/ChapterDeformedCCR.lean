import BookProof.Ultrafinitism.ChapterKrawtchoukTail
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Chapter DeformedCCR — Bounded Finite-Horizon Ladder Algebra

In the infinite-dimensional continuous theory, the canonical commutation relation
`[a, a†] = I` cannot be realized by bounded operators (the Wintner–Wielandt
theorem, `ChapterCcrNoBounded`).  On the strictly finite Krawtchouk space of
degree horizon `M`, the ladder coefficients acquire the exact finite-horizon factor
`√(1 - n / M)` from `ChapterKrawtchoukTail.krawtchouk_one_mul_succ`.

Consequently:
* Creation halts automatically at the degree horizon `M` (`creOp_top`).
* The operators `creOp M`, `annOp M`, `posOp M` are explicitly bounded
  (`creOp_norm_sq_le`, `annOp_norm_sq_le`).
* They satisfy the deformed CCR `[a_M, a_M†] = I - (2 / M) N̂` (`deformed_ccr`),
  whose trace vanishes identically (`trace_deformed_ccr_eq_zero`), dissolving the
  Wintner–Wielandt obstruction.
* On feasible grades `k ≤ d ≪ M`, the CCR defect is bounded by `2d / M`
  (`deformed_ccr_defect_bound`).
-/

namespace BookProof.Ultrafinitism.ChapterDeformedCCR

open scoped BigOperators

/-- Standard inner product on the `(M + 1)`-dimensional Krawtchouk degree space. -/
def finDot {M : ℕ} (u v : Fin (M + 1) → ℝ) : ℝ :=
  ∑ k : Fin (M + 1), u k * v k

theorem finDot_symm {M : ℕ} (u v : Fin (M + 1) → ℝ) :
    finDot u v = finDot v u := by
  refine Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem finDot_self_nonneg {M : ℕ} (v : Fin (M + 1) → ℝ) :
    0 ≤ finDot v v :=
  Finset.sum_nonneg fun k _ => mul_self_nonneg (v k)

/-- The finite-horizon Krawtchouk ladder coefficient `√((n + 1)(1 - n / M))`. -/
noncomputable def ladderCoeff (M n : ℕ) : ℝ :=
  Real.sqrt (((n + 1 : ℕ) : ℝ) * (1 - (n : ℝ) / (M : ℝ)))

theorem ladderCoeff_nonneg (M n : ℕ) : 0 ≤ ladderCoeff M n :=
  Real.sqrt_nonneg _

theorem ladderCoeff_sq {M n : ℕ} (hM : 0 < M) (hn : n ≤ M) :
    ladderCoeff M n ^ 2 = ((n + 1 : ℕ) : ℝ) * (1 - (n : ℝ) / (M : ℝ)) := by
  unfold ladderCoeff
  refine Real.sq_sqrt ?_
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hnle : (n : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hn
  have h1 : (n : ℝ) / (M : ℝ) ≤ 1 := (div_le_one hMpos).mpr hnle
  exact mul_nonneg (by positivity) (sub_nonneg.mpr h1)

theorem ladderCoeff_top (M : ℕ) (hM : 0 < M) : ladderCoeff M M = 0 := by
  have hMne : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  simp [ladderCoeff, hMne]

/-- Exact algebraic bridge between `ladderCoeff M n` and the integer Krawtchouk
normalization `Nat.choose M n` of `ChapterKrawtchoukTail`. -/
theorem ladderCoeff_matches_krawtchouk {M n : ℕ} (hM : 0 < M) (hn : n < M) :
    ladderCoeff M n ^ 2 * ((M : ℝ) * (Nat.choose M n : ℝ)) =
      ((n + 1 : ℕ) : ℝ) ^ 2 * (Nat.choose M (n + 1) : ℝ) := by
  rw [ladderCoeff_sq hM hn.le]
  have hMne : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  have hch : Nat.choose M (n + 1) * (n + 1) = Nat.choose M n * (M - n) :=
    Nat.choose_succ_right_eq M n
  have hchR : (Nat.choose M (n + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) =
      (Nat.choose M n : ℝ) * ((M : ℝ) - (n : ℝ)) := by
    have h1 : ((Nat.choose M (n + 1) * (n + 1) : ℕ) : ℝ) =
        ((Nat.choose M n * (M - n) : ℕ) : ℝ) := by exact_mod_cast hch
    push_cast at h1
    simpa [Nat.cast_sub hn.le] using h1
  calc (((n + 1 : ℕ) : ℝ) * (1 - (n : ℝ) / (M : ℝ))) * ((M : ℝ) * (Nat.choose M n : ℝ))
      = ((n + 1 : ℕ) : ℝ) * ((Nat.choose M n : ℝ) * ((M : ℝ) - (n : ℝ))) := by
        field_simp [hMne]
    _ = ((n + 1 : ℕ) : ℝ) * ((Nat.choose M (n + 1) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
        rw [← hchR]
    _ = ((n + 1 : ℕ) : ℝ) ^ 2 * (Nat.choose M (n + 1) : ℝ) := by ring

/-! ## Bounded ladder operators on `Fin (M + 1) → ℝ` -/

/-- Bounded creation operator on the `(M + 1)`-dimensional Krawtchouk space. -/
noncomputable def creOp (M : ℕ) (v : Fin (M + 1) → ℝ) : Fin (M + 1) → ℝ :=
  fun k => if h : (k : ℕ) = 0 then 0 else
    ladderCoeff M ((k : ℕ) - 1) * v ⟨(k : ℕ) - 1, by omega⟩

/-- Bounded annihilation operator on the `(M + 1)`-dimensional Krawtchouk space. -/
noncomputable def annOp (M : ℕ) (v : Fin (M + 1) → ℝ) : Fin (M + 1) → ℝ :=
  fun k => if h : (k : ℕ) < M then
    ladderCoeff M k * v ⟨(k : ℕ) + 1, by omega⟩ else 0

/-- Number operator `N̂` on the Krawtchouk degree space. -/
def numOp (M : ℕ) (v : Fin (M + 1) → ℝ) : Fin (M + 1) → ℝ :=
  fun k => (k : ℝ) * v k

/-- Symmetric position / field quadrature operator `a_M† + a_M`. -/
noncomputable def posOp (M : ℕ) (v : Fin (M + 1) → ℝ) : Fin (M + 1) → ℝ :=
  fun k => creOp M v k + annOp M v k

/-- The vacuum state `|0⟩` is annihilated by `annOp M`. -/
theorem annOp_vac (M : ℕ) :
    annOp M (Pi.single ⟨0, Nat.succ_pos M⟩ 1) = 0 := by
  ext k
  unfold annOp
  split_ifs with hk
  · have hne : (⟨(k : ℕ) + 1, by omega⟩ : Fin (M + 1)) ≠ ⟨0, Nat.succ_pos M⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp
  · rfl

/-- Creation automatically halts at the top degree horizon `|M⟩`. -/
theorem creOp_top (M : ℕ) :
    creOp M (Pi.single ⟨M, Nat.lt_succ_self M⟩ 1) = 0 := by
  ext k
  unfold creOp
  split_ifs with hk
  · rfl
  · have hne : (⟨(k : ℕ) - 1, by omega⟩ : Fin (M + 1)) ≠ ⟨M, Nat.lt_succ_self M⟩ := by
      intro h
      have hval : (k : ℕ) - 1 = M := by
        simpa using congrArg Fin.val h
      omega
    simp [hne]

private theorem creOp_zero {M : ℕ} (u : Fin (M + 1) → ℝ) :
    creOp M u 0 = 0 := by
  unfold creOp
  exact dif_pos rfl

private theorem annOp_last {M : ℕ} (v : Fin (M + 1) → ℝ) :
    annOp M v (Fin.last M) = 0 := by
  unfold annOp
  exact dif_neg (lt_irrefl M)

private theorem creOp_succ {M : ℕ} (u : Fin (M + 1) → ℝ) (j : Fin M) :
    creOp M u (Fin.succ j) = ladderCoeff M j * u (Fin.castSucc j) := by
  have hne : ((Fin.succ j : Fin (M + 1)) : ℕ) ≠ 0 := by simp
  unfold creOp
  rw [dif_neg hne]
  congr 1

private theorem annOp_castSucc {M : ℕ} (v : Fin (M + 1) → ℝ) (j : Fin M) :
    annOp M v (Fin.castSucc j) = ladderCoeff M j * v (Fin.succ j) := by
  have hlt : ((Fin.castSucc j : Fin (M + 1)) : ℕ) < M := j.isLt
  unfold annOp
  rw [dif_pos hlt]
  rfl

/-- Exact adjointness `⟨a_M† u, v⟩ = ⟨u, a_M v⟩`. -/
theorem dot_creOp_eq_dot_annOp (M : ℕ) (u v : Fin (M + 1) → ℝ) :
    finDot (creOp M u) v = finDot u (annOp M v) := by
  unfold finDot
  have hL : (∑ k : Fin (M + 1), creOp M u k * v k) =
      ∑ j : Fin M, ladderCoeff M j * u (Fin.castSucc j) * v (Fin.succ j) := by
    rw [Fin.sum_univ_succ, creOp_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [creOp_succ]
  have hR : (∑ k : Fin (M + 1), u k * annOp M v k) =
      ∑ j : Fin M, ladderCoeff M j * u (Fin.castSucc j) * v (Fin.succ j) := by
    rw [Fin.sum_univ_castSucc, annOp_last, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [annOp_castSucc]
    ring
  rw [hL, hR]

theorem dot_posOp_symm (M : ℕ) (u v : Fin (M + 1) → ℝ) :
    finDot (posOp M u) v = finDot u (posOp M v) := by
  have h1 : finDot (posOp M u) v = finDot (creOp M u) v + finDot (annOp M u) v := by
    simp [finDot, posOp, add_mul, Finset.sum_add_distrib]
  have h2 : finDot u (posOp M v) = finDot u (creOp M v) + finDot u (annOp M v) := by
    simp [finDot, posOp, mul_add, Finset.sum_add_distrib]
  rw [h1, h2, dot_creOp_eq_dot_annOp M u v, finDot_symm (annOp M u) v,
    ← dot_creOp_eq_dot_annOp M v u, finDot_symm (creOp M v) u, add_comm]

private theorem annOp_creOp_apply_of_lt {M : ℕ} (v : Fin (M + 1) → ℝ)
    {k : Fin (M + 1)} (hk : (k : ℕ) < M) :
    annOp M (creOp M v) k = ladderCoeff M k ^ 2 * v k := by
  have hk' : k = Fin.castSucc ⟨(k : ℕ), hk⟩ := Fin.ext rfl
  rw [hk', annOp_castSucc, creOp_succ]
  simp only [Fin.val_castSucc]
  rw [← hk', sq]
  ring

private theorem creOp_annOp_apply_of_ne_zero {M : ℕ} (v : Fin (M + 1) → ℝ)
    {k : Fin (M + 1)} (hk0 : (k : ℕ) ≠ 0) :
    creOp M (annOp M v) k = ladderCoeff M ((k : ℕ) - 1) ^ 2 * v k := by
  have hk1M : (k : ℕ) - 1 < M := by omega
  have hk' : k = Fin.succ ⟨(k : ℕ) - 1, hk1M⟩ := Fin.ext (by simp; omega)
  rw [hk', creOp_succ, annOp_castSucc]
  simp only [Fin.val_succ]
  have hsub : (k : ℕ) - 1 + 1 - 1 = (k : ℕ) - 1 := by omega
  rw [hsub, ← hk', sq]
  ring

/-- **Deformed CCR:** `[a_M, a_M†] = I - (2 / M) N̂` on the finite Krawtchouk space. -/
theorem deformed_ccr {M : ℕ} (hM : 0 < M) (v : Fin (M + 1) → ℝ) (k : Fin (M + 1)) :
    annOp M (creOp M v) k - creOp M (annOp M v) k =
      (1 - 2 * (k : ℝ) / (M : ℝ)) * v k := by
  have hMne : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  by_cases hk0 : (k : ℕ) = 0
  · have hkM : (k : ℕ) < M := by omega
    have hcre0 : creOp M (annOp M v) k = 0 := by simp [creOp, hk0]
    rw [annOp_creOp_apply_of_lt v hkM, hcre0, ladderCoeff_sq hM hkM.le, hk0]
    simp
  · by_cases hkM : (k : ℕ) < M
    · have hk1M : (k : ℕ) - 1 < M := by omega
      rw [annOp_creOp_apply_of_lt v hkM, creOp_annOp_apply_of_ne_zero v hk0,
        ladderCoeff_sq hM hkM.le, ladderCoeff_sq hM hk1M.le]
      have hsub : (((k : ℕ) - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk0), Nat.cast_one]
      have hsucc : (((k : ℕ) - 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by
        have : (k : ℕ) - 1 + 1 = (k : ℕ) := by omega
        rw [this]
      rw [Nat.cast_add, Nat.cast_one, hsucc, hsub]
      field_simp [hMne]
      ring
    · have hk_eq : (k : ℕ) = M := by omega
      have hann : annOp M (creOp M v) k = 0 := by simp [annOp, hkM]
      have hk1M : (k : ℕ) - 1 < M := by omega
      rw [hann, creOp_annOp_apply_of_ne_zero v hk0, ladderCoeff_sq hM hk1M.le]
      have hsub : (((k : ℕ) - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk0), Nat.cast_one]
      have hsucc : (((k : ℕ) - 1 + 1 : ℕ) : ℝ) = (k : ℝ) := by
        have : (k : ℕ) - 1 + 1 = (k : ℕ) := by omega
        rw [this]
      rw [hsucc, hsub, hk_eq]
      field_simp [hMne]
      ring

/-- **Resolution of the Wintner–Wielandt obstruction:** the trace of the deformed CCR
`I - (2 / M) N̂` vanishes identically on `Fin (M + 1) → ℝ`. -/
theorem trace_deformed_ccr_eq_zero {M : ℕ} (hM : 0 < M) :
    (∑ k : Fin (M + 1), (1 - 2 * (k : ℝ) / (M : ℝ))) = 0 := by
  have hMne : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  have hrev : (∑ k : Fin (M + 1), (k : ℝ)) =
      ∑ k : Fin (M + 1), ((Fin.rev k : Fin (M + 1)) : ℝ) :=
    (Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)).symm
  have hsum2 : 2 * (∑ k : Fin (M + 1), (k : ℝ)) = (M : ℝ) * ((M : ℝ) + 1) := by
    have hpair : (∑ k : Fin (M + 1), (k : ℝ)) +
        ∑ k : Fin (M + 1), ((Fin.rev k : Fin (M + 1)) : ℝ) =
        ∑ _k : Fin (M + 1), (M : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fin.val_rev]
      have hk : (k : ℕ) + (M + 1 - ((k : ℕ) + 1)) = M := by omega
      exact_mod_cast hk
    rw [← hrev] at hpair
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one] at hpair
    linarith
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ _k : Fin (M + 1), (1 : ℝ)) = (M : ℝ) + 1 := by
    simp [Nat.cast_add, Nat.cast_one]
  have h2 : (∑ k : Fin (M + 1), 2 * (k : ℝ) / (M : ℝ)) =
      (2 * ∑ k : Fin (M + 1), (k : ℝ)) / (M : ℝ) := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [h1, h2, hsum2]
  field_simp [hMne]
  ring

/-- On feasible grades `k ≤ d`, the CCR defect `|[a_M, a_M†] v - v|` is `O(d / M)`. -/
theorem deformed_ccr_defect_bound {M d : ℕ} (hM : 0 < M) (v : Fin (M + 1) → ℝ)
    (k : Fin (M + 1)) (hk : (k : ℕ) ≤ d) :
    |(annOp M (creOp M v) k - creOp M (annOp M v) k) - v k| ≤
      (2 * (d : ℝ) / (M : ℝ)) * |v k| := by
  rw [deformed_ccr hM v k]
  have hdiff : (1 - 2 * (k : ℝ) / (M : ℝ)) * v k - v k =
      -(2 * (k : ℝ) / (M : ℝ)) * v k := by ring
  rw [hdiff, abs_mul, abs_neg]
  have hk0 : 0 ≤ 2 * (k : ℝ) / (M : ℝ) := by positivity
  rw [abs_of_nonneg hk0]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hkR : (k : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hk
  have hMpos : (0 : ℝ) ≤ (M : ℝ) := by positivity
  exact div_le_div_of_nonneg_right (by linarith) hMpos

/-- Explicit boundedness of `creOp M` on the finite Krawtchouk space. -/
theorem creOp_norm_sq_le {M : ℕ} (hM : 0 < M) (v : Fin (M + 1) → ℝ) :
    finDot (creOp M v) (creOp M v) ≤ ((M + 1 : ℕ) : ℝ) * finDot v v := by
  unfold finDot
  rw [Fin.sum_univ_succ]
  simp only [creOp, Fin.val_zero, ↓reduceDIte, mul_zero, zero_add]
  have hle : (∑ j : Fin M, (if h : ((Fin.succ j : Fin (M + 1)) : ℕ) = 0 then 0 else
      ladderCoeff M (((Fin.succ j : Fin (M + 1)) : ℕ) - 1) *
        v ⟨((Fin.succ j : Fin (M + 1)) : ℕ) - 1, by omega⟩) *
      (if h : ((Fin.succ j : Fin (M + 1)) : ℕ) = 0 then 0 else
        ladderCoeff M (((Fin.succ j : Fin (M + 1)) : ℕ) - 1) *
          v ⟨((Fin.succ j : Fin (M + 1)) : ℕ) - 1, by omega⟩)) ≤
      ∑ j : Fin M, ((M + 1 : ℕ) : ℝ) * (v (Fin.castSucc j) * v (Fin.castSucc j)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [Fin.val_succ, add_eq_zero, one_ne_zero, and_false, ↓reduceDIte,
      Nat.add_sub_cancel]
    have heq : (ladderCoeff M j * v ⟨j, by omega⟩) * (ladderCoeff M j * v ⟨j, by omega⟩) =
        ladderCoeff M j ^ 2 * (v (Fin.castSucc j) * v (Fin.castSucc j)) := by
      change (ladderCoeff M j * v (Fin.castSucc j)) *
        (ladderCoeff M j * v (Fin.castSucc j)) = _
      ring
    rw [heq, ladderCoeff_sq hM j.isLt.le]
    refine mul_le_mul_of_nonneg_right ?_ (mul_self_nonneg _)
    have hj1 : ((j + 1 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : (j : ℕ) + 1 ≤ M + 1)
    have hfac : 1 - (j : ℝ) / (M : ℝ) ≤ 1 := by
      have : 0 ≤ (j : ℝ) / (M : ℝ) := by positivity
      linarith
    have hfac0 : 0 ≤ 1 - (j : ℝ) / (M : ℝ) := by
      have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
      have hjle : (j : ℝ) ≤ (M : ℝ) := by exact_mod_cast j.isLt.le
      linarith [(div_le_one hMpos).mpr hjle]
    nlinarith
  refine hle.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

/-- Explicit boundedness of `annOp M` on the finite Krawtchouk space. -/
theorem annOp_norm_sq_le {M : ℕ} (hM : 0 < M) (v : Fin (M + 1) → ℝ) :
    finDot (annOp M v) (annOp M v) ≤ ((M + 1 : ℕ) : ℝ) * finDot v v := by
  unfold finDot
  rw [Fin.sum_univ_castSucc]
  have hlast : annOp M v (Fin.last M) * annOp M v (Fin.last M) = 0 := by
    simp [annOp]
  rw [hlast, add_zero]
  have hle : (∑ j : Fin M, annOp M v (Fin.castSucc j) * annOp M v (Fin.castSucc j)) ≤
      ∑ j : Fin M, ((M + 1 : ℕ) : ℝ) * (v (Fin.succ j) * v (Fin.succ j)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [annOp_castSucc]
    have heq : (ladderCoeff M j * v (Fin.succ j)) *
        (ladderCoeff M j * v (Fin.succ j)) =
        ladderCoeff M j ^ 2 * (v (Fin.succ j) * v (Fin.succ j)) := by ring
    rw [heq, ladderCoeff_sq hM j.isLt.le]
    refine mul_le_mul_of_nonneg_right ?_ (mul_self_nonneg _)
    have hj1 : ((j + 1 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : (j : ℕ) + 1 ≤ M + 1)
    have hfac : 1 - (j : ℝ) / (M : ℝ) ≤ 1 := by
      have : 0 ≤ (j : ℝ) / (M : ℝ) := by positivity
      linarith
    nlinarith
  refine hle.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (mul_self_nonneg _)

end BookProof.Ultrafinitism.ChapterDeformedCCR
