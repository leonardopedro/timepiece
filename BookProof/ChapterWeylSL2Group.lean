import Mathlib
import BookProof.ChapterWeylSl2

/-!
# From `sl(2,ℂ)` to `SL(2,ℂ)`: Weyl's theorem for group representations

`BookProof.ChapterWeylSl2` proves Weyl's complete-reducibility theorem for the Lie algebra
`sl(2,ℂ)`.  This file transports it to representations of the **group** `SL(2,ℂ)` that are
differentiable in the sense that the two unipotent one-parameter subgroups

`u₊(t) = !![1, t; 0, 1]`,  `u₋(t) = !![1, 0; t, 1]`

act by the exponentials of the raising and lowering operators `E`, `F` of an `sl₂`-triple
(`IsExpOfSl2`).  Every finite-dimensional holomorphic representation of `SL(2,ℂ)` is of this
form, with the `sl₂`-triple being the differential of the representation.

The two ingredients are:

* `coeff_mem_of_poly_mem` — if all values of a polynomial curve `t ↦ ∑ tᵏ cₖ` lie in a
  subspace `W`, then so do all its coefficients (proved by pushing to `V ⧸ W` and using that
  a polynomial over `ℂ` vanishing identically is zero).  This turns invariance under the
  one-parameter groups into invariance under `E` and `F`.
* `exists_factorization` — every element of `SL(2,ℂ)` is a product of four elementary
  (unipotent) matrices, so invariance under `u₊` and `u₋` gives invariance under the whole
  group.

The conclusion is `weyl_complete_reducibility_SL2`: every invariant subspace of such a
representation has an invariant complement.  `rho_mem_of_unipotent_inv` is the group-level
half (invariance under the two unipotent subgroups already gives invariance under the whole
group), and `isInv_of_rho` the Lie-algebra half.

Finally `stdRep`, `stdSl2` and `isExpOfSl2_stdRep` exhibit the defining representation of
`SL(2,ℂ)` on `ℂ²` as an instance of the hypothesis, so the theorem is not vacuous.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterWeylSL2Group

open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-! ### Coefficients of a polynomial curve inside a subspace -/

/-- If every value of the polynomial curve `t ↦ ∑_{k<N} tᵏ • cₖ` lies in the subspace `W`,
then every coefficient `cₖ` lies in `W`. -/
theorem coeff_mem_of_poly_mem {W : Submodule ℂ V} {N : ℕ} {c : ℕ → V}
    (h : ∀ t : ℂ, ∑ k ∈ Finset.range N, t ^ k • c k ∈ W) {k : ℕ} (hk : k < N) : c k ∈ W := by
  by_contra hcon
  have hq : W.mkQ (c k) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hcon
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one ℂ hq
  set mu : V →ₗ[ℂ] ℂ := lam ∘ₗ W.mkQ with hmu
  have hmuW : ∀ x ∈ W, mu x = 0 := by
    intro x hx
    have : W.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hmu]
    simp [this]
  have hmuk : mu (c k) = 1 := hlam
  set P : Polynomial ℂ :=
    ∑ j ∈ Finset.range N, Polynomial.C (mu (c j)) * Polynomial.X ^ j with hP
  have hPeval : ∀ t : ℂ, P.eval t = 0 := by
    intro t
    have h1 : P.eval t = ∑ j ∈ Finset.range N, mu (c j) * t ^ j := by
      rw [hP, Polynomial.eval_finset_sum]
      exact Finset.sum_congr rfl fun j _ => by simp
    have h2 : ∑ j ∈ Finset.range N, mu (c j) * t ^ j
        = mu (∑ j ∈ Finset.range N, t ^ j • c j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
    rw [h1, h2, hmuW _ (h t)]
  have hP0 : P = 0 := Polynomial.funext fun t => by rw [hPeval t, Polynomial.eval_zero]
  have hcoeff : P.coeff k = mu (c k) := by
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Polynomial.coeff_X_pow, Ne.symm hj]
    · intro hk'
      exact absurd (Finset.mem_range.mpr hk) hk'
  rw [hP0, Polynomial.coeff_zero, hmuk] at hcoeff
  exact zero_ne_one hcoeff

/-! ### The unipotent one-parameter subgroups of `SL(2,ℂ)` -/

/-- The upper unipotent matrix `!![1, t; 0, 1]`. -/
def uPlus (t : ℂ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The lower unipotent matrix `!![1, 0; t, 1]`. -/
def uMinus (t : ℂ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem uPlus_coe (t : ℂ) : (uPlus t : Matrix (Fin 2) (Fin 2) ℂ) = !![1, t; 0, 1] := rfl

@[simp] theorem uMinus_coe (t : ℂ) : (uMinus t : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; t, 1] := rfl

/-- Every element of `SL(2,ℂ)` is a product of four elementary unipotent matrices. -/
theorem exists_factorization (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    ∃ x y z w : ℂ, g = uPlus x * uMinus y * uPlus z * uMinus w := by
  have key : ∀ h : Matrix.SpecialLinearGroup (Fin 2) ℂ, (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 →
      h = uPlus (((h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 - 1) / (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
          uMinus ((h : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
          uPlus (((h : Matrix (Fin 2) (Fin 2) ℂ) 1 1 - 1) / (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
          uMinus 0 := by
    intro h hc
    have hdet : (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (h : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        - (h : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
      have := h.2
      rwa [Matrix.det_fin_two] at this
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.SpecialLinearGroup.coe_mul, uPlus, uMinus, Matrix.mul_apply,
      Fin.sum_univ_two]
    all_goals field_simp
    all_goals try ring1
    all_goals linear_combination -hdet
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0
  · exact ⟨_, _, _, _, key g hc⟩
  · push_neg at hc
    set h := g * uMinus 1 with hh
    have hhc : (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 := by
      have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
          - (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
        have := g.2
        rwa [Matrix.det_fin_two] at this
      rw [hc, mul_zero, sub_zero] at hdet
      have h11 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hdet
        exact zero_ne_one hdet
      have : (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
        simp [hh, Matrix.SpecialLinearGroup.coe_mul, uMinus, Matrix.mul_apply, Fin.sum_univ_two,
          hc]
      rw [this]
      exact h11
    obtain ⟨x, y, z, w, hfac⟩ : ∃ x y z w : ℂ, h = uPlus x * uMinus y * uPlus z * uMinus w :=
      ⟨_, _, _, _, key h hhc⟩
    refine ⟨x, y, z, w - 1, ?_⟩
    have hinv : uMinus w * uMinus (-1) = uMinus (w - 1) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, uMinus, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hg : g = h * uMinus (-1) := by
      rw [hh, mul_assoc]
      have : uMinus 1 * uMinus (-1) = 1 := by
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.SpecialLinearGroup.coe_mul, uMinus, Matrix.mul_apply, Fin.sum_univ_two]
      rw [this, mul_one]
    rw [hg, hfac, mul_assoc, mul_assoc, ← mul_assoc (uPlus z), ← hinv]
    simp [mul_assoc]

/-! ### Representations that exponentiate an `sl₂`-triple -/

/-- A representation of `SL(2,ℂ)` **exponentiates** the `sl₂`-triple `R` (whose raising and
lowering operators are nilpotent of order at most `N`) when the two unipotent one-parameter
subgroups act by the exponential series of `E` and `F`.  This is exactly what the
differential of a finite-dimensional holomorphic representation of `SL(2,ℂ)` provides. -/
structure IsExpOfSl2 (rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)
    (R : Sl2Rep V) (N : ℕ) : Prop where
  /-- Two terms of the exponential series are needed to see the generator. -/
  two_le : 2 ≤ N
  /-- The upper unipotent subgroup acts by `exp (t E)`. -/
  expE : ∀ t : ℂ, rho (uPlus t) = ∑ k ∈ Finset.range N, (t ^ k / (Nat.factorial k : ℂ)) • R.E ^ k
  /-- The lower unipotent subgroup acts by `exp (t F)`. -/
  expF : ∀ t : ℂ, rho (uMinus t) = ∑ k ∈ Finset.range N, (t ^ k / (Nat.factorial k : ℂ)) • R.F ^ k

variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

theorem pow_mem_of_mem {W : Submodule ℂ V} {a : Module.End ℂ V} (ha : ∀ x ∈ W, a x ∈ W)
    {v : V} (hv : v ∈ W) (k : ℕ) : (a ^ k) v ∈ W := by
  induction k with
  | zero => simpa using hv
  | succ k ih => rw [Sl2Rep.pow_succ_apply]; exact ha _ ih

/-- An `sl₂`-invariant subspace is invariant under the unipotent one-parameter subgroups. -/
theorem rho_mem_of_isInv (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V} (hW : R.IsInv W) :
    ∀ t : ℂ, (∀ v ∈ W, rho (uPlus t) v ∈ W) ∧ (∀ v ∈ W, rho (uMinus t) v ∈ W) := by
  intro t
  constructor
  · intro v hv
    rw [h.expE t]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (pow_mem_of_mem hW.1 hv k)
  · intro v hv
    rw [h.expF t]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (pow_mem_of_mem hW.2.1 hv k)

/-- A subspace invariant under the unipotent one-parameter subgroups is `sl₂`-invariant. -/
theorem isInv_of_rho (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V}
    (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W)
    (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinus t) v ∈ W) : R.IsInv W := by
  have key : ∀ a : Module.End ℂ V,
      (∀ t : ℂ, ∀ v ∈ W,
        (∑ k ∈ Finset.range N, (t ^ k / (Nat.factorial k : ℂ)) • a ^ k) v ∈ W) →
      ∀ v ∈ W, a v ∈ W := by
    intro a ha v hv
    have hpoly : ∀ t : ℂ,
        ∑ k ∈ Finset.range N, t ^ k • (((Nat.factorial k : ℂ)⁻¹) • (a ^ k) v) ∈ W := by
      intro t
      have h1 := ha t v hv
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply] at h1
      have heq : ∀ k : ℕ, t ^ k • (((Nat.factorial k : ℂ)⁻¹) • (a ^ k) v)
          = (t ^ k / (Nat.factorial k : ℂ)) • (a ^ k) v := fun k => by
        rw [smul_smul, div_eq_mul_inv]
      simpa only [heq] using h1
    have h1 : (((Nat.factorial 1 : ℂ))⁻¹) • (a ^ 1) v ∈ W :=
      coeff_mem_of_poly_mem hpoly (lt_of_lt_of_le one_lt_two h.two_le)
    simpa using h1
  have hE : ∀ v ∈ W, R.E v ∈ W := key R.E (fun t => by rw [← h.expE t]; exact hplus t)
  have hF : ∀ v ∈ W, R.F v ∈ W := key R.F (fun t => by rw [← h.expF t]; exact hminus t)
  refine ⟨hE, hF, fun v hv => ?_⟩
  have hH : R.H v = R.E (R.F v) - R.F (R.E v) := by
    have hv' := congrArg (fun T : Module.End ℂ V => T v) R.hef
    simpa using hv'.symm
  rw [hH]
  exact Submodule.sub_mem _ (hE _ (hF _ hv)) (hF _ (hE _ hv))

/-! ### From the unipotent subgroups to the whole group -/

/-- A subspace invariant under the two unipotent one-parameter subgroups is invariant under
all of `SL(2,ℂ)`, because every element is a product of four unipotent matrices. -/
theorem rho_mem_of_unipotent_inv {W : Submodule ℂ V}
    (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W)
    (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinus t) v ∈ W)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) : ∀ v ∈ W, rho g v ∈ W := by
  obtain ⟨x, y, z, w, hg⟩ := exists_factorization g
  intro v hv
  have happ : rho g v = rho (uPlus x) (rho (uMinus y) (rho (uPlus z) (rho (uMinus w) v))) := by
    rw [hg]
    simp [map_mul, Module.End.mul_apply]
  rw [happ]
  exact hplus _ _ (hminus _ _ (hplus _ _ (hminus _ _ hv)))

/-! ### Weyl's theorem for `SL(2,ℂ)` -/

/-- **Weyl's complete reducibility theorem for `SL(2,ℂ)`** (`book.tex`, Note 23).  Let `rho`
be a finite-dimensional representation of `SL(2,ℂ)` on a complex vector space `V` which
exponentiates an `sl₂`-triple (the differential of the representation).  Then every
invariant subspace `W` has an invariant complement, so `V` is completely reducible. -/
theorem weyl_complete_reducibility_SL2 [FiniteDimensional ℂ V]
    (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V}
    (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ W, rho g v ∈ W) :
    ∃ U : Submodule ℂ V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ U, rho g v ∈ U) ∧ IsCompl W U := by
  have hWinv : R.IsInv W :=
    isInv_of_rho h (fun t => hW (uPlus t)) (fun t => hW (uMinus t))
  obtain ⟨U, hUinv, hcompl⟩ := Sl2Rep.weyl_complete_reducibility R W hWinv
  refine ⟨U, fun g => ?_, hcompl⟩
  exact rho_mem_of_unipotent_inv (fun t => (rho_mem_of_isInv h hUinv t).1)
    (fun t => (rho_mem_of_isInv h hUinv t).2) g

/-! ### The hypothesis is satisfiable: the defining representation -/

/-- The raising matrix of `sl(2,ℂ)`. -/
def eMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The lowering matrix of `sl(2,ℂ)`. -/
def fMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The Cartan matrix of `sl(2,ℂ)`. -/
def hMat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The defining representation of `SL(2,ℂ)` on `ℂ²`. -/
def stdRep : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    ext v i
    simp
  map_mul' g h := by
    ext v i
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_apply]

/-- The `sl₂`-triple of the defining representation. -/
def stdSl2 : Sl2Rep (Fin 2 → ℂ) where
  E := Matrix.toLin' eMat
  F := Matrix.toLin' fMat
  H := Matrix.toLin' hMat
  he := by
    have hm : hMat * eMat - eMat * hMat = eMat + eMat := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hMat, eMat]
    have hL := congrArg Matrix.toLin' hm
    rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul, map_add] at hL
    rw [two_nsmul]
    exact hL
  hf := by
    have hm : hMat * fMat - fMat * hMat = -(fMat + fMat) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hMat, fMat]
      ring1
    have hL := congrArg Matrix.toLin' hm
    rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul, map_neg, map_add] at hL
    rw [two_nsmul]
    exact hL
  hef := by
    have hm : eMat * fMat - fMat * eMat = hMat := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hMat, eMat, fMat]
    have hL := congrArg Matrix.toLin' hm
    rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul] at hL
    exact hL

/-- The defining representation exponentiates its `sl₂`-triple, so the hypothesis of
`weyl_complete_reducibility_SL2` is satisfiable. -/
theorem isExpOfSl2_stdRep : IsExpOfSl2 stdRep stdSl2 2 where
  two_le := le_rfl
  expE t := by
    have hsum : (∑ k ∈ Finset.range 2, (t ^ k / (Nat.factorial k : ℂ)) • stdSl2.E ^ k)
        = 1 + t • stdSl2.E := by
      simp [Finset.sum_range_succ]
    have hmat : ((uPlus t : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 + t • eMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [uPlus, eMat]
    rw [hsum]
    change Matrix.toLin' ((uPlus t : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 + t • Matrix.toLin' eMat
    rw [hmat, map_add, map_smul, Matrix.toLin'_one]
    rfl
  expF t := by
    have hsum : (∑ k ∈ Finset.range 2, (t ^ k / (Nat.factorial k : ℂ)) • stdSl2.F ^ k)
        = 1 + t • stdSl2.F := by
      simp [Finset.sum_range_succ]
    have hmat : ((uMinus t : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 + t • fMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [uMinus, fMat]
    rw [hsum]
    change Matrix.toLin' ((uMinus t : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 + t • Matrix.toLin' fMat
    rw [hmat, map_add, map_smul, Matrix.toLin'_one]
    rfl

end BookProof.ChapterWeylSL2Group
