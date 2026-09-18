import Mathlib
import BookProof.ChapterNsFourierElimination

/-!
# Uniformity of the reduced forms under the energy cutoff

The first of the two residual obligations of item 4 of the Navier–Stokes plan items of
`CONSOLIDATED_PLAN.md` (§5.4(1) of `DESIGN_COMPARISON_N_20260915.md`): after the Fourier
elimination the reduced constraint forms carry the mode coefficients `i k_j` and `−|k|²`, and
under the energy cutoff `|k_j| ≤ Λ` they must be bounded by `O(Λ)` **uniformly in the parcel
number `n`** — that uniformity is what makes the `ℓ²`-lift of the sector Hamiltonians possible,
and it is why the cutoff is load-bearing rather than cosmetic.

What is proved here about the reduced family `redFormPoly` of
`BookProof.ChapterNsFourierElimination`:

* `norm_coeff_redVisc_le`, `norm_coeff_redAdvectPoly_le`, `norm_coeff_redMomentumPoly_le` and the
  headline `norm_coeff_redFormPoly_le` — **every coefficient of every reduced form of every parcel
  is bounded by `cutoffBound nu Λ = 1 + 3Λ + 3|ν|Λ²`** as soon as `|k_j| ≤ Λ`.  The bound does not
  depend on the parcel number `n`, on the parcel `p`, on which of the seven forms is taken, or on
  the monomial: it is `O(Λ)` in exactly the sense the obligation asks for (and `O(Λ²)` through the
  viscous coefficient `ν|k|²`);
* `totalDegree_redFormPoly_le` — the reduced forms are of degree at most two, again uniformly;
* `vars_redFormPoly_subset` — **parcel locality**: a reduced form involves only the six
  coordinates of its own parcel.  With the fixed number `7` of forms per parcel this is the
  sparsity that makes the row/column (Schur) data of the sector Hamiltonians independent of `n`;
* `norm_coeff_redFormPoly_unbounded_of_no_cutoff` — the cutoff is **necessary**: without it the
  coefficients of the reduced family are unbounded, since the advection coefficient is `k_j`
  itself.

**What this does and does not settle.**  It settles the coefficient half of the uniformity
obligation — the data entering the Schur bounds are `O(Λ)` and parcel local, uniformly in `n`.
The operator-level relative bound `‖H_n x‖ ≤ K ‖(N_n + 1) x‖` with `K` independent of `n` is not
proved here; on the landed route it is not needed either, because the comparison actually used is
the lifted Friedrichs extension of the reduced Hamiltonian itself
(`BookProof.NsFullEuler.nsRedFullOuterN_esa`), for which the Faris–Lavine commutator constant is
`c = 0`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsCutoffUniformity

open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

/-! ## 1. Coefficient bounds for one monomial -/

variable {ι : Type*}

theorem norm_coeff_X_le (a : ι) (m : ι →₀ ℕ) : ‖coeff m (X a : MvPolynomial ι ℂ)‖ ≤ 1 := by
  classical
  rw [coeff_X']
  split <;> simp

theorem norm_coeff_C_mul_X_le (c : ℂ) (a : ι) (m : ι →₀ ℕ) :
    ‖coeff m (C c * X a : MvPolynomial ι ℂ)‖ ≤ ‖c‖ := by
  classical
  rw [coeff_C_mul, norm_mul, coeff_X']
  split <;> simp

theorem norm_coeff_C_mul_X_mul_X_le (c : ℂ) (a b : ι) (m : ι →₀ ℕ) :
    ‖coeff m (C c * (X a * X b) : MvPolynomial ι ℂ)‖ ≤ ‖c‖ := by
  classical
  have hx : (X a * X b : MvPolynomial ι ℂ)
      = monomial (Finsupp.single a 1 + Finsupp.single b 1) 1 := by
    rw [X, X, monomial_mul, one_mul]
  rw [hx, coeff_C_mul, norm_mul, coeff_monomial]
  split <;> simp

/-! ## 2. The cutoff bound -/

/-- The uniform bound on the coefficients of the reduced forms under the cutoff `|k_j| ≤ Λ`. -/
def cutoffBound (nu Λ : ℝ) : ℝ := 1 + 3 * Λ + 3 * |nu| * Λ ^ 2

theorem cutoffBound_nonneg (nu : ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) : 0 ≤ cutoffBound nu Λ := by
  unfold cutoffBound
  positivity

/-- Under the cutoff the viscous coefficient `ν |k|²` is bounded by `3 |ν| Λ²`. -/
theorem abs_visc_coeff_le {nu Λ : ℝ} {k : Fin 3 → ℝ} (hΛ : 0 ≤ Λ) (hk : ∀ j, |k j| ≤ Λ) :
    |nu * ∑ j : Fin 3, (k j) ^ 2| ≤ 3 * |nu| * Λ ^ 2 := by
  have hsum : ∑ j : Fin 3, (k j) ^ 2 ≤ 3 * Λ ^ 2 := by
    have hbound : ∀ j : Fin 3, (k j) ^ 2 ≤ Λ ^ 2 := by
      intro j
      have := hk j
      nlinarith [abs_nonneg (k j), sq_abs (k j)]
    calc ∑ j : Fin 3, (k j) ^ 2 ≤ ∑ _j : Fin 3, Λ ^ 2 := Finset.sum_le_sum fun j _ => hbound j
      _ = 3 * Λ ^ 2 := by simp [Finset.sum_const]
  have hnonneg : 0 ≤ ∑ j : Fin 3, (k j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [abs_mul, abs_of_nonneg hnonneg]
  calc |nu| * ∑ j : Fin 3, (k j) ^ 2 ≤ |nu| * (3 * Λ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsum (abs_nonneg nu)
    _ = 3 * |nu| * Λ ^ 2 := by ring

/-! ## 3. The coefficient bounds of the reduced forms -/

/-- The real residual form has coefficients bounded by `1 + 3|ν|Λ²`. -/
theorem norm_coeff_redVisc_le (nu : ℝ) {Λ : ℝ} {k : Fin 3 → ℝ} (hΛ : 0 ≤ Λ)
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (i : Fin 3) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redVisc nu k n p i)‖ ≤ 1 + 3 * |nu| * Λ ^ 2 := by
  rw [redVisc, coeff_add]
  refine (norm_add_le _ _).trans ?_
  gcongr
  · exact norm_coeff_X_le _ _
  · refine (norm_coeff_C_mul_X_le _ _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_visc_coeff_le hΛ hk

/-- The advection form has coefficients bounded by `3Λ`. -/
theorem norm_coeff_redAdvectPoly_le {Λ : ℝ} {k : Fin 3 → ℝ}
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (i : Fin 3) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redAdvectPoly k n p i)‖ ≤ 3 * Λ := by
  rw [redAdvectPoly, coeff_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin 3, ‖coeff m (C ((k j : ℝ) : ℂ) * (X (ruIdx p j) * X (ruIdx p i)))‖
      ≤ ∑ _j : Fin 3, Λ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (norm_coeff_C_mul_X_mul_X_le _ _ _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hk j
    _ = 3 * Λ := by simp [Finset.sum_const]

/-- The eliminated incompressibility has coefficients bounded by `3Λ`. -/
theorem norm_coeff_redMomentumPoly_le {Λ : ℝ} {k : Fin 3 → ℝ}
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redMomentumPoly k n p)‖ ≤ 3 * Λ := by
  rw [redMomentumPoly, coeff_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin 3, ‖coeff m (C ((k j : ℝ) : ℂ) * X (ruIdx p j))‖
      ≤ ∑ _j : Fin 3, Λ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (norm_coeff_C_mul_X_le _ _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hk j
    _ = 3 * Λ := by simp [Finset.sum_const]

/-- **The uniformity of the reduced family under the energy cutoff.**  Every coefficient of every
one of the seven reduced forms of every parcel is bounded by `1 + 3Λ + 3|ν|Λ²` once the momenta
obey the cutoff `|k_j| ≤ Λ` — a bound independent of the parcel number `n`, of the parcel and of
the form. -/
theorem norm_coeff_redFormPoly_le (nu : ℝ) {Λ : ℝ} {k : Fin 3 → ℝ} (hΛ : 0 ≤ Λ)
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (r : Fin 7) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redFormPoly nu k n p r)‖ ≤ cutoffBound nu Λ := by
  have hvisc : (0 : ℝ) ≤ 3 * |nu| * Λ ^ 2 := by positivity
  have hlam : (0 : ℝ) ≤ 3 * Λ := by positivity
  rw [redFormPoly]
  split
  · refine (norm_coeff_redVisc_le nu hΛ hk p _ m).trans ?_
    unfold cutoffBound
    linarith
  · split
    · refine (norm_coeff_redAdvectPoly_le hk p _ m).trans ?_
      unfold cutoffBound
      linarith
    · refine (norm_coeff_redMomentumPoly_le hk p m).trans ?_
      unfold cutoffBound
      linarith

/-- **The cutoff is necessary.**  Without it the coefficients of the reduced family are unbounded:
the coefficient of the eliminated incompressibility form is the momentum itself. -/
theorem norm_coeff_redFormPoly_unbounded_of_no_cutoff (nu : ℝ) (C₀ : ℝ) :
    ∃ (k : Fin 3 → ℝ) (m : Fin (1 * 6) →₀ ℕ) (p : Fin 1) (r : Fin 7),
      C₀ < ‖coeff m (redFormPoly nu k 1 p r)‖ := by
  obtain ⟨t, ht⟩ := exists_gt (max C₀ 0)
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_right C₀ 0) ht
  refine ⟨fun j => if j = 0 then t else 0, Finsupp.single (ruIdx (0 : Fin 1) 0) 1, 0,
    divIdx7, ?_⟩
  rw [redFormPoly_div, redMomentumPoly, coeff_sum]
  have hval : ∀ j : Fin 3,
      coeff (Finsupp.single (ruIdx (0 : Fin 1) 0) 1)
        (C (((if j = 0 then t else 0 : ℝ)) : ℂ) * X (ruIdx (0 : Fin 1) j))
        = if j = 0 then (t : ℂ) else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [coeff_C_mul, coeff_X']
      simp
    · rw [coeff_C_mul]
      simp [hj]
  rw [Finset.sum_congr rfl fun j _ => hval j, Finset.sum_ite_eq' Finset.univ (0 : Fin 3)
    (fun _ => (t : ℂ))]
  simp only [Finset.mem_univ, if_true, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  exact lt_of_le_of_lt (le_max_left C₀ 0) ht

/-! ## 4. Degree and parcel locality -/

section Degree

variable (nu : ℝ) (k : Fin 3 → ℝ)

private theorem totalDegree_C_mul_X_le (c : ℂ) (a : Fin (n * 6)) :
    (C c * X a : MvPolynomial (Fin (n * 6)) ℂ).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]
  norm_num

private theorem totalDegree_C_mul_X_mul_X_le (c : ℂ) (a b : Fin (n * 6)) :
    (C c * (X a * X b) : MvPolynomial (Fin (n * 6)) ℂ).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  have hab : (X a * X b : MvPolynomial (Fin (n * 6)) ℂ).totalDegree ≤ 2 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_X]
  rw [totalDegree_C]
  simpa using hab

/-- The reduced forms have degree at most two, uniformly in the parcel number. -/
theorem totalDegree_redFormPoly_le (p : Fin n) (r : Fin 7) :
    (redFormPoly nu k n p r).totalDegree ≤ 2 := by
  rw [redFormPoly]
  split
  · refine (totalDegree_add _ _).trans ?_
    refine max_le ?_ (totalDegree_C_mul_X_le _ _)
    rw [totalDegree_X]
    norm_num
  · split
    · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
      exact totalDegree_C_mul_X_mul_X_le _ _ _
    · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
      exact totalDegree_C_mul_X_le _ _

end Degree

/-- **Parcel locality.**  A reduced form involves only the six coordinates of its own parcel; with
the fixed number of forms per parcel this makes the sparsity data of the sector Hamiltonians
independent of the parcel number. -/
theorem vars_redFormPoly_subset (nu : ℝ) (k : Fin 3 → ℝ) (p : Fin n) (r : Fin 7) :
    (redFormPoly nu k n p r).vars ⊆ Finset.image (redIdx p) Finset.univ := by
  classical
  have hmemU : ∀ i : Fin 3, ruIdx p i ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) :=
    fun i => Finset.mem_image.2 ⟨ruIdx6 i, Finset.mem_univ _, rfl⟩
  have hmemQ : ∀ i : Fin 3, rqIdx p i ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) :=
    fun i => Finset.mem_image.2 ⟨rqIdx6 i, Finset.mem_univ _, rfl⟩
  have hX : ∀ a : Fin (n * 6), a ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) →
      (X a : MvPolynomial (Fin (n * 6)) ℂ).vars ⊆ Finset.image (redIdx p) Finset.univ := by
    intro a ha
    rw [vars_X]
    exact Finset.singleton_subset_iff.2 ha
  have hCX : ∀ (c : ℂ) (a : Fin (n * 6)),
      a ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) →
      (C c * X a : MvPolynomial (Fin (n * 6)) ℂ).vars
        ⊆ Finset.image (redIdx p) Finset.univ := by
    intro c a ha
    refine (vars_mul _ _).trans (Finset.union_subset ?_ (hX a ha))
    simp [vars_C]
  have hCXX : ∀ (c : ℂ) (a b : Fin (n * 6)),
      a ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) →
      b ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) →
      (C c * (X a * X b) : MvPolynomial (Fin (n * 6)) ℂ).vars
        ⊆ Finset.image (redIdx p) Finset.univ := by
    intro c a b ha hb
    refine (vars_mul _ _).trans (Finset.union_subset ?_ ?_)
    · simp [vars_C]
    · exact (vars_mul _ _).trans (Finset.union_subset (hX a ha) (hX b hb))
  rw [redFormPoly]
  split
  · exact (vars_add_subset _ _).trans
      (Finset.union_subset (hX _ (hmemQ _)) (hCX _ _ (hmemU _)))
  · split
    · refine (vars_sum_subset _ _).trans (Finset.biUnion_subset.2 fun j _ => ?_)
      exact hCXX _ _ _ (hmemU _) (hmemU _)
    · refine (vars_sum_subset _ _).trans (Finset.biUnion_subset.2 fun j _ => ?_)
      exact hCX _ _ (hmemU _)

end

end BookProof.NsCutoffUniformity
