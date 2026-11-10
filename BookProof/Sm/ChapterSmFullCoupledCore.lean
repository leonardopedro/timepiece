import Mathlib
import BookProof.Sm.ChapterSmFullMatterHamiltonian
import BookProof.Sm.ChapterSmFullComparisonEsa
import BookProof.Sm.ChapterSmFarisLavine

/-!
# P3 remainder — the coupled comparison `N_SM ⊗ I` and the Faris–Lavine data

Work order: `SM_ESA_COMPLETION_PLAN.md` §4 **P3** (remainder) and §4 **P4**.  The scalar half of
P3 — the comparison operator `N_SM = −Δ_S + W`, its identification with
`2h_B + Σ_m q_m² + Σⱼ(πⱼ² + xⱼ²) + c`, its symmetry, positivity, dense core and essential
self-adjointness — is `BookProof.Sm.ChapterSmFullComparisonEsa`.  This module carries that scalar
comparison to the **coupled** space `SmCoupledSpace` of P2, and supplies the Faris–Lavine
machinery the normal form of P2 is measured against.

## What is built

1. **The coupled tensor** `coupledOp T M`: the internal factor `M` acts on the occupation
   components and `T` acts on each of them.  P2's `smTensorCore` takes a bosonic factor that maps
   the Gauss–polynomial core **to itself**; the comparison operators (`smFullComparison`,
   `smFlN`, `smHamiltonian`) have codomain `L²`, so `coupledOp` is the version of the elementary
   tensor that accepts them.  For `M = 1` it is literally `T ⊗ I`.
2. **Symmetry, the quadratic form and positivity** of `T ⊗ I` on the common core
   (`coupledOp_symmetricOn`, `coupledOp_one_quadForm`, `coupledOp_one_quadForm_nonneg`): the
   coupled quadratic form is the sum of the componentwise ones.
3. **The coupled comparison operator** `smCoupledComparison P c` — the Friedrichs `Comparison`
   of `N_SM ⊗ I` on `SmCoupledCore`, together with its extension property.  This is the
   `Comparison` datum of `BookProof.QgOuterFockCoreFL` for the coupled space.
4. **The transfer of both Faris–Lavine inequalities** from the 163-mode space to the coupled
   space: the relative bound `coupledOp_one_norm_le` (with the internal matrices entering only
   through the Frobenius-type sum `pairSum`) and the commutator-form bound
   `coupledOp_one_commForm_le`.  Both are proved for an *arbitrary* scalar pair `(H, N)`
   satisfying the same inequalities, so they are reused by every ledger term.
5. **The coupled `CoreData` package and essential self-adjointness**: for the coupled
   Hamiltonian `h ⊗ I` against the coupled comparison `N ⊗ I`, with the constants of the scalar
   theory, and hence `smCoupledHamiltonian_esa`.

## Honest boundary

The relative bound is transferred for a **diagonal** internal factor: `h ⊗ I` against
`N ⊗ I`, and more generally any `T ⊗ M` against `N ⊗ I` through `pairSum M`.  The full normal
form of P2 is a sum of tensors with *non-scalar* coefficient matrices; its relative bound follows
from the same engine **term by term**, and what is still missing is the scalar relative bound of
the individual families `πⱼ`, `πⱼ²`, `uⱼ` against `N` (only the combination `h` against `N` is
proved, in `BookProof.Sm.ChapterSmFarisLavine`).  Nothing here assumes that bound, and nothing
here assumes the desired conclusion: the comparison operator is the Friedrichs extension, so its
surjectivity is by construction.
-/

namespace BookProof.SmFullCoupledCore

open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.FriedrichsExtension
open BookProof.SmHamiltonian BookProof.SmFullMatter BookProof.SmFullComparisonEsa
open BookProof.QgOuterFockCoreFL BookProof.QgOuterFockFL BookProof.SmFarisLavine

noncomputable section

/-! ## 1. The elementary tensor with an `L²`-valued bosonic factor -/

/-- **The elementary tensor `T ⊗ M`** for a bosonic factor with codomain `L²`: the internal
matrix acts on the occupation components and `T` on each of them. -/
def coupledFun (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) (f : SmCoupledCore) : SmCoupledSpace :=
  WithLp.toLp 2 (fun A => ∑ B, M A B • T (coreComp f B))

set_option maxHeartbeats 1000000 in
-- linearity has to push through `WithLp`/`PiLp` and the finite internal sum, which exceeds the
-- default heartbeat budget
/-- The elementary tensor `T ⊗ M` as a linear map out of the common core. -/
def coupledOp (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) : SmCoupledCore →ₗ[ℂ] SmCoupledSpace where
  toFun := coupledFun T M
  map_add' f g := by
    refine WithLp.ofLp_injective 2 (funext fun A => ?_)
    simp only [coupledFun, WithLp.ofLp_toLp, PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun B _ => by rw [coreComp_add, map_add, smul_add]
  map_smul' c f := by
    refine WithLp.ofLp_injective 2 (funext fun A => ?_)
    simp only [coupledFun, WithLp.ofLp_toLp, PiLp.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun B _ => by rw [coreComp_smul, map_smul, smul_comm]

/-- **The action of the coupled tensor**: the `A`-th component is `Σ_B M A B • (T f_B)`. -/
@[simp] theorem coupledOp_apply (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) (f : SmCoupledCore)
    (A : Finset (Fin 96)) :
    (coupledOp T M f).ofLp A = ∑ B, M A B • T (coreComp f B) := by
  have h : coupledOp T M f = coupledFun T M f := rfl
  rw [h, coupledFun, WithLp.ofLp_toLp]

/-- The internal identity matrix summed against a family: only the diagonal term survives. -/
theorem sum_one_smul (v : Finset (Fin 96) → L2d 163) (A : Finset (Fin 96)) :
    (∑ B, (1 : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) A B • v B) = v A := by
  rw [Finset.sum_eq_single A]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply, if_neg (fun h : A = b => hb h.symm), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ A) h

/-- **`T ⊗ I` componentwise**: the `A`-th component of `T ⊗ I` is `T` applied to the `A`-th
component. -/
@[simp] theorem coupledOp_one_apply (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (f : SmCoupledCore) (A : Finset (Fin 96)) :
    (coupledOp T 1 f).ofLp A = T (coreComp f A) := by
  rw [coupledOp_apply, sum_one_smul]

/-- The identity matrix is Hermitian — the coefficient hypothesis of symmetry, for `M = 1`. -/
theorem matrix_one_star (A B : Finset (Fin 96)) :
    star ((1 : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) A B)
      = (1 : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) B A := by
  by_cases h : A = B
  · subst h
    simp
  · rw [Matrix.one_apply, Matrix.one_apply, if_neg h, if_neg (fun hb => h hb.symm)]
    simp

set_option maxHeartbeats 1000000 in
-- the double internal sum and the two inner products need more `isDefEq` work than the default
-- heartbeat budget allows
/-- **Each coupled tensor is symmetric on the common core** when the bosonic factor is symmetric
on the Gauss–polynomial core and the internal matrix is Hermitian. -/
theorem coupledOp_symmetricOn (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (hT : SymmetricOn (polyGaussCore (d := 163)) T) (hM : ∀ A B, star (M A B) = M B A) :
    SymmetricOn SmCoupledCore (coupledOp T M) := by
  intro f g
  have hL : (inner ℂ (coupledOp T M f) (g : SmCoupledSpace) : ℂ) =
      ∑ A, ∑ B, star (M A B) * inner ℂ (T (coreComp f B))
        ((g : SmCoupledSpace).ofLp A) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [coupledOp_apply, sum_inner]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [inner_smul_left, starRingEnd_apply]
  have hR : (inner ℂ (f : SmCoupledSpace) (coupledOp T M g) : ℂ) =
      ∑ A, ∑ B, M A B * inner ℂ ((f : SmCoupledSpace).ofLp A) (T (coreComp g B)) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [coupledOp_apply, inner_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [inner_smul_right]
  rw [hL, hR]
  have hstep : ∀ A B, inner ℂ (T (coreComp f B)) ((g : SmCoupledSpace).ofLp A)
      = inner ℂ ((f : SmCoupledSpace).ofLp B) (T (coreComp g A)) := by
    intro A B
    exact hT (coreComp f B) (coreComp g A)
  calc (∑ A, ∑ B, star (M A B) * inner ℂ (T (coreComp f B)) ((g : SmCoupledSpace).ofLp A))
      = ∑ A, ∑ B, star (M A B) * inner ℂ ((f : SmCoupledSpace).ofLp B)
          (T (coreComp g A)) := by
        exact Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => by rw [hstep A B]
    _ = ∑ A, ∑ B, M A B * inner ℂ ((f : SmCoupledSpace).ofLp A) (T (coreComp g B)) :=
        star_transpose_sum M (fun A B => inner ℂ ((f : SmCoupledSpace).ofLp A)
          (T (coreComp g B))) hM

/-- **The quadratic form of `T ⊗ I` is the sum of the componentwise forms.** -/
theorem coupledOp_one_quadForm (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (f : SmCoupledCore) :
    quadForm (coupledOp T 1) f = ∑ A, quadForm T (coreComp f A) := by
  have hinner : (inner ℂ (f : SmCoupledSpace) (coupledOp T 1 f) : ℂ)
      = ∑ A, inner ℂ ((coreComp f A : polyGaussCore (d := 163)) : L2d 163)
          (T (coreComp f A)) := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun A _ => by rw [coupledOp_one_apply, coe_coreComp]
  rw [quadForm, hinner, Complex.re_sum]
  exact Finset.sum_congr rfl fun A _ => rfl

/-- **`T ⊗ I` is positive** as soon as `T` is. -/
theorem coupledOp_one_quadForm_nonneg (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (hpos : ∀ x : polyGaussCore (d := 163), 0 ≤ quadForm T x) (f : SmCoupledCore) :
    0 ≤ quadForm (coupledOp T 1) f := by
  rw [coupledOp_one_quadForm]
  exact Finset.sum_nonneg fun A _ => hpos (coreComp f A)

/-! ## 2. The coupled comparison operator `N_SM ⊗ I` -/

/-- **The coupled comparison operator** `N_SM ⊗ I` on the common core. -/
def smCoupledFullComparison (P : SmParams) (c : ℝ) : SmCoupledCore →ₗ[ℂ] SmCoupledSpace :=
  coupledOp (smFullComparison P c) 1

/-- `N_SM ⊗ I` is symmetric on the common core. -/
theorem smCoupledFullComparison_symmetricOn (P : SmParams) (c : ℝ) :
    SymmetricOn SmCoupledCore (smCoupledFullComparison P c) :=
  coupledOp_symmetricOn _ _ (smFullComparison_symmetricOn P c) matrix_one_star

/-- **`N_SM ⊗ I` is positive** on the common core, for `c ≥ 0`. -/
theorem smCoupledFullComparison_quadForm_nonneg (P : SmParams) {c : ℝ} (hc : 0 ≤ c)
    (f : SmCoupledCore) : 0 ≤ quadForm (smCoupledFullComparison P c) f :=
  coupledOp_one_quadForm_nonneg _ (smFullComparison_quadForm_nonneg P hc) f

/-- **The coupled comparison as a positive symmetric operator**, the input of the Friedrichs
construction. -/
def smCoupledFullPosSymOp (P : SmParams) {c : ℝ} (hc : 0 ≤ c) : PosSymOp SmCoupledSpace where
  dom := SmCoupledCore
  op := smCoupledFullComparison P c
  sym := smCoupledFullComparison_symmetricOn P c
  pos := smCoupledFullComparison_quadForm_nonneg P hc

/-- **The Faris–Lavine comparison operator of the coupled space**: the Friedrichs extension of
`N_SM ⊗ I`, for which the shift by `1` is onto by construction. -/
def smCoupledFullComparisonComparison (P : SmParams) {c : ℝ} (hc : 0 ≤ c) :
    Comparison SmCoupledSpace :=
  friedrichsComparison (smCoupledFullPosSymOp P hc) coupledCore_dense

/-- The coupled comparison agrees with `N_SM ⊗ I` on the common core. -/
theorem smCoupledFullComparisonComparison_extends (P : SmParams) {c : ℝ} (hc : 0 ≤ c)
    (f : SmCoupledCore) :
    ∃ h : (f : SmCoupledSpace) ∈ (smCoupledFullComparisonComparison P hc).dom,
      (smCoupledFullComparisonComparison P hc).op ⟨(f : SmCoupledSpace), h⟩
        = smCoupledFullComparison P c f :=
  friedrichsComparison_extends (smCoupledFullPosSymOp P hc) coupledCore_dense f

/-! ## 3. Norm and commutator-form transfer to the coupled space -/

/-- **The Frobenius square sum of an internal coefficient matrix**: the only way a coefficient
matrix enters the coupled relative bound. -/
def pairSum (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) : ℝ :=
  ∑ A, ∑ B, ‖M A B‖ ^ 2

/-- The Frobenius square sum is non-negative. -/
theorem pairSum_nonneg (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) : 0 ≤ pairSum M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- **Cauchy–Schwarz for one internal row**: a finite complex linear combination of `L²` vectors
is bounded by the product of the `ℓ²` norms. -/
theorem norm_sum_smul_sq_le (c : Finset (Fin 96) → ℂ) (v : Finset (Fin 96) → L2d 163) :
    ‖∑ B, c B • v B‖ ^ 2 ≤ (∑ B, ‖c B‖ ^ 2) * ∑ B, ‖v B‖ ^ 2 := by
  have h1 : ‖∑ B, c B • v B‖ ≤ ∑ B, ‖c B‖ * ‖v B‖ := by
    calc ‖∑ B, c B • v B‖ ≤ ∑ B, ‖c B • v B‖ := norm_sum_le _ _
      _ = ∑ B, ‖c B‖ * ‖v B‖ := by simp only [norm_smul]
  have h2 : (∑ B, ‖c B‖ * ‖v B‖) ^ 2 ≤ (∑ B, ‖c B‖ ^ 2) * ∑ B, ‖v B‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : (0 : ℝ) ≤ ‖∑ B, c B • v B‖ := norm_nonneg _
  have h4 : (0 : ℝ) ≤ ∑ B, ‖c B‖ * ‖v B‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [h1, h2, h3, h4]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
-- the componentwise norm sum has to be reassembled through `PiLp`/`WithLp`, and the `ℓ²` norm
-- identity of the coupled space is itself a deep unfold
/-- **The coupled tensor norm bound**: `‖T ⊗ M f‖²` is at most `pairSum M` times the sum of the
squared componentwise norms. -/
theorem coupledOp_norm_sq_le (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) (f : SmCoupledCore) :
    ‖coupledOp T M f‖ ^ 2
      ≤ pairSum M * ∑ B, ‖T (coreComp f B)‖ ^ 2 := by
  set S : ℝ := ∑ B, ‖T (coreComp f B)‖ ^ 2 with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  calc ‖coupledOp T M f‖ ^ 2
      = ∑ A, ‖(coupledOp T M f).ofLp A‖ ^ 2 := coupledSpace_norm_sq _
    _ = ∑ A, ‖∑ B, M A B • T (coreComp f B)‖ ^ 2 := by
        exact Finset.sum_congr rfl fun A _ => by rw [coupledOp_apply]
    _ ≤ ∑ A, (∑ B, ‖M A B‖ ^ 2) * S :=
        Finset.sum_le_sum fun A _ => norm_sum_smul_sq_le (fun B => M A B)
          (fun B => T (coreComp f B))
    _ = pairSum M * S := by rw [pairSum, Finset.sum_mul]

/-- The shift `(T ⊗ I) + 1` componentwise. -/
theorem coupledOp_one_add_apply (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (f : SmCoupledCore) (A : Finset (Fin 96)) :
    (coupledOp T 1 f + (f : SmCoupledSpace)).ofLp A
      = T (coreComp f A) + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163) := by
  rw [PiLp.add_apply, coupledOp_one_apply, coe_coreComp]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
-- the componentwise norm sum has to be reassembled through `PiLp`/`WithLp`, and the `ℓ²` norm
-- identity of the coupled space is itself a deep unfold
/-- **The `ℓ²` norm of the shifted comparison**: the square of the norm is the sum over the
internal components of the squared scalar shifts. -/
theorem coupledOp_one_add_norm_sq (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (f : SmCoupledCore) :
    ‖coupledOp T 1 f + (f : SmCoupledSpace)‖ ^ 2
      = ∑ A, ‖T (coreComp f A)
          + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by
  rw [coupledSpace_norm_sq]
  exact Finset.sum_congr rfl fun A _ => by rw [coupledOp_one_add_apply]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
-- squaring the Cauchy–Schwarz bound, matching it with the `ℓ²` shift norm of the coupled space
-- and converting between norms and their squares all exceed the default elaboration budget
/-- **The relative bound transfers to the coupled space.**  If the scalar factor obeys
`‖T x‖ ≤ c‖(N+1)x‖` then the coupled tensor obeys the same inequality with the internal matrix
entering only through `√(pairSum M)`. -/
theorem coupledOp_norm_le (T N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ x : polyGaussCore (d := 163), ‖T x‖
      ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (f : SmCoupledCore) :
    ‖coupledOp T M f‖
      ≤ c * Real.sqrt (pairSum M) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by
  have hcomp : ∑ B, ‖T (coreComp f B)‖ ^ 2
      ≤ c ^ 2 * ∑ B, ‖N (coreComp f B)
          + ((coreComp f B : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun B _ => ?_
    have h1 := hb (coreComp f B)
    have h2 : ‖T (coreComp f B)‖ * ‖T (coreComp f B)‖
        ≤ (c * ‖N (coreComp f B)
            + ((coreComp f B : polyGaussCore (d := 163)) : L2d 163)‖)
          * (c * ‖N (coreComp f B)
            + ((coreComp f B : polyGaussCore (d := 163)) : L2d 163)‖) :=
      mul_self_le_mul_self (norm_nonneg _) h1
    nlinarith [h2]
  have hmain : ‖coupledOp T M f‖ ^ 2
      ≤ pairSum M * (c ^ 2 * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2) := by
    calc ‖coupledOp T M f‖ ^ 2
        ≤ pairSum M * ∑ B, ‖T (coreComp f B)‖ ^ 2 := coupledOp_norm_sq_le T M f
      _ ≤ pairSum M * (c ^ 2 * ∑ B, ‖N (coreComp f B)
            + ((coreComp f B : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcomp (pairSum_nonneg M)
      _ = pairSum M * (c ^ 2 * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2) := by
          rw [coupledOp_one_add_norm_sq]
  set r : ℝ := c * Real.sqrt (pairSum M) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ with hr
  have hr2 : r ^ 2 = pairSum M * (c ^ 2 * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2) := by
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (pairSum_nonneg M)]
    ring
  have hsq : ‖coupledOp T M f‖ ^ 2 ≤ r ^ 2 := by rw [hr2]; exact hmain
  have habs : ‖coupledOp T M f‖ = |‖coupledOp T M f‖| := (abs_of_nonneg (norm_nonneg _)).symm
  rw [habs]
  exact (sq_le_sq.mp hsq).trans (le_of_eq (abs_of_nonneg (by rw [hr]; positivity)))

/-- **The commutator form of `T ⊗ I` is the sum of the componentwise commutator forms.** -/
theorem coupledOp_one_commForm (H N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (f : SmCoupledCore) :
    commForm (coupledOp H 1) (coupledOp N 1) f = ∑ A, commForm H N (coreComp f A) := by
  have hinner : (inner ℂ (coupledOp H 1 f) (coupledOp N 1 f) : ℂ)
      = ∑ A, inner ℂ (H (coreComp f A)) (N (coreComp f A)) := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun A _ => by rw [coupledOp_one_apply, coupledOp_one_apply]
  rw [commForm_eq, hinner, Complex.im_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => (commForm_eq H N (coreComp f A)).symm

/-- **The commutator-form bound transfers to the coupled space**, with the same constant and the
coupled quadratic form. -/
theorem coupledOp_one_commForm_le (H N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c : ℝ}
    (hb : ∀ x : polyGaussCore (d := 163), |commForm H N x| ≤ c * quadForm N x)
    (f : SmCoupledCore) :
    |commForm (coupledOp H 1) (coupledOp N 1) f| ≤ c * quadForm (coupledOp N 1) f := by
  rw [coupledOp_one_commForm, coupledOp_one_quadForm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun A _ => hb (coreComp f A)

/-! ## 4. The Faris–Lavine package of the coupled comparison `N = 2h + Σ q² + c₀` -/

/-- **The coupled comparison operator** `N ⊗ I` for `N = 2h + Σ_m q_m² + c₀`. -/
def smCoupledFl (P : SmParams) (c0 : ℝ) : SmCoupledCore →ₗ[ℂ] SmCoupledSpace :=
  coupledOp (smFlN P c0) 1

/-- `N ⊗ I` is symmetric on the common core. -/
theorem smCoupledFl_symmetricOn (P : SmParams) (c0 : ℝ) :
    SymmetricOn SmCoupledCore (smCoupledFl P c0) :=
  coupledOp_symmetricOn _ _ (smFlN_symmetricOn P c0) matrix_one_star

/-- `N ⊗ I` is positive on the common core. -/
theorem smCoupledFl_quadForm_nonneg (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (f : SmCoupledCore) : 0 ≤ quadForm (smCoupledFl P c0) f :=
  coupledOp_one_quadForm_nonneg _ (smFlN_quadForm_nonneg P hc0) f

/-- The coupled comparison as a positive symmetric operator. -/
def smCoupledFlPosSymOp (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) : PosSymOp SmCoupledSpace where
  dom := SmCoupledCore
  op := smCoupledFl P c0
  sym := smCoupledFl_symmetricOn P c0
  pos := smCoupledFl_quadForm_nonneg P hc0

/-- **The Faris–Lavine comparison operator of the coupled space.** -/
def smCoupledFlComparison (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) : Comparison SmCoupledSpace :=
  friedrichsComparison (smCoupledFlPosSymOp P hc0) coupledCore_dense

/-- The coupled comparison of the Faris–Lavine pair agrees with `N ⊗ I` on the common core. -/
theorem smCoupledFlComparison_extends (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (f : SmCoupledCore) :
    ∃ h : (f : SmCoupledSpace) ∈ (smCoupledFlComparison P hc0).dom,
      (smCoupledFlComparison P hc0).op ⟨(f : SmCoupledSpace), h⟩ = smCoupledFl P c0 f :=
  friedrichsComparison_extends (smCoupledFlPosSymOp P hc0) coupledCore_dense f

/-- **The coupled Hamiltonian** `h ⊗ I` on the common core. -/
def smCoupledHamiltonian (P : SmParams) : SmCoupledCore →ₗ[ℂ] SmCoupledSpace :=
  coupledOp (smHamiltonian P) 1

/-- **The relative bound of the coupled Hamiltonian**: `‖h ⊗ I f‖ ≤ K‖(N ⊗ I + 1)f‖` with the
constant `K = √(pairSum 1) = 1` inherited from the scalar bound `sm_norm_le_shift`. -/
theorem smCoupledHamiltonian_norm_le (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (f : SmCoupledCore) :
    ‖smCoupledHamiltonian P f‖
      ≤ Real.sqrt (pairSum (1 : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ))
        * ‖smCoupledFl P c0 f + (f : SmCoupledSpace)‖ := by
  have h := coupledOp_norm_le (smHamiltonian P) (smFlN P c0) 1 zero_le_one
    (fun x => sm_norm_le_shift P hc0 x) f
  simpa only [one_mul, smCoupledHamiltonian, smCoupledFl] using h

/-- **The Faris–Lavine data of the coupled Standard-Model operator**, given that the common core
is a graph core of the coupled comparison. -/
def smCoupledCoreData (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hgc : IsGraphCore (smCoupledFlComparison P hc0) SmCoupledCore) :
    CoreData SmCoupledSpace where
  C := smCoupledFlComparison P hc0
  C₀ := SmCoupledCore
  gc := hgc
  H₀ := smCoupledHamiltonian P
  K := Real.sqrt (pairSum (1 : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ))
  hK := Real.sqrt_nonneg _
  rel := by
    intro p
    obtain ⟨h, hx⟩ := smCoupledFlComparison_extends P hc0 p
    have hpt : (smCoupledFlComparison P hc0).op
        ⟨(p : SmCoupledSpace), hgc.le p.2⟩ = smCoupledFl P c0 p := hx
    rw [hpt]
    exact smCoupledHamiltonian_norm_le P hc0 p

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
-- the coupled tensor is unified against the fields of `CoreData` and against the two transferred
-- inequalities, which exceeds the default elaboration budget
/-- **The coupled Standard-Model Hamiltonian `h ⊗ I` is essentially self-adjoint on the common
core, given the graph-core property of the coupled comparison operator.**  Both Faris–Lavine
inequalities are transferred from the `163`-mode theory with their absolute constants, so the only
input is the graph-core property itself. -/
theorem smCoupledHamiltonian_esa (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hgc : IsGraphCore (smCoupledFlComparison P hc0) SmCoupledCore) :
    EssentiallySelfAdjointOn SmCoupledCore (smCoupledHamiltonian P) := by
  refine CoreData.esa_core (smCoupledCoreData P hc0 hgc)
    (coupledOp_symmetricOn _ _ (smHamiltonian_symmetricOn P) matrix_one_star)
    zero_le_one fun p => ?_
  obtain ⟨h, hx⟩ := smCoupledFlComparison_extends P hc0 p
  have hcoreN : (smCoupledCoreData P hc0 hgc).coreN p = smCoupledFl P c0 p := hx
  have h1 : commForm (smCoupledCoreData P hc0 hgc).H₀ (smCoupledCoreData P hc0 hgc).coreN p
      = commForm (smCoupledHamiltonian P) (smCoupledFl P c0) p :=
    commForm_congr _ _ _ _ _ _ rfl hcoreN
  have h2 : quadForm (smCoupledCoreData P hc0 hgc).coreN p = quadForm (smCoupledFl P c0) p :=
    quadForm_congr _ _ _ _ rfl hcoreN
  rw [h1, h2]
  exact coupledOp_one_commForm_le (smHamiltonian P) (smFlN P c0)
    (fun x => sm_commForm_le P hc0 x) p

/-! ## 5. The relative bound of the full normal form

The normal form of P2 is a finite sum of elementary tensors `smTensorCore T M` whose bosonic
factors map the Gauss–polynomial core **to itself**.  Such a tensor is the `L²`-valued tensor of
§1 with the subtype-composed factor, so the transfer engine applies unchanged; the normal form
then inherits the relative bound from the triangle inequality, with the explicit constant below.
What the statement still needs as input is the relative bound of the individual families against
`N` — the scalar analysis of `πⱼ`, `πⱼ²` and `uⱼ`, of which the corpus proves the combination
`h` (`sm_norm_le_shift`). -/

/-- P2's elementary tensor is the `L²`-valued elementary tensor of §1 with the subtype-composed
bosonic factor. -/
theorem smTensorCore_eq_coupledOp
    (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) (f : SmCoupledCore) :
    smTensorCore T M f = coupledOp ((polyGaussCore (d := 163)).subtype.comp T) M f := by
  refine WithLp.ofLp_injective 2 (funext fun A => ?_)
  rw [smTensorCore_apply, coupledOp_apply]
  exact Finset.sum_congr rfl fun B _ => by
    rw [tensorComp, tensorCompOf, LinearMap.comp_apply]

/-- **The relative bound of an elementary tensor of the normal form**, transferred from its
bosonic factor. -/
theorem smTensorCore_norm_le (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ x : polyGaussCore (d := 163), ‖((T x : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (f : SmCoupledCore) :
    ‖smTensorCore T M f‖
      ≤ c * Real.sqrt (pairSum M) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by
  rw [smTensorCore_eq_coupledOp]
  exact coupledOp_norm_le ((polyGaussCore (d := 163)).subtype.comp T) N M hc hb f

/-- The constant of the relative bound of the normal form: the sum over the three families of the
`√(pairSum)` of the coefficient matrices, plus the `1 ⊗ M₀` term. -/
def normalFormConst (D : SmNormalFormData) : ℝ :=
  (∑ j : Fin 163, Real.sqrt (pairSum (D.mom j)))
    + (∑ j : Fin 163, Real.sqrt (pairSum (D.kinetic j)))
    + (∑ j : Fin 163, Real.sqrt (pairSum (D.coord j)))
    + Real.sqrt (pairSum D.mass)

/-- The normal-form constant is non-negative. -/
theorem normalFormConst_nonneg (D : SmNormalFormData) : 0 ≤ normalFormConst D := by
  rw [normalFormConst]
  have h1 : (0 : ℝ) ≤ ∑ j : Fin 163, Real.sqrt (pairSum (D.mom j)) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ j : Fin 163, Real.sqrt (pairSum (D.kinetic j)) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ j : Fin 163, Real.sqrt (pairSum (D.coord j)) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have h4 : (0 : ℝ) ≤ Real.sqrt (pairSum D.mass) := Real.sqrt_nonneg _
  linarith

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
-- the normal form is a sum of three `Finset` sums of elementary tensors; distributing the
-- application over the sums and applying the triangle inequality needs a larger budget
/-- **The relative bound of the full normal form**: if each bosonic family satisfies
`‖Tⱼ x‖ ≤ c‖(N+1)x‖` on the common core, then

`‖h_SM f‖ ≤ c · normalFormConst D · ‖(N ⊗ I + 1) f‖`

for every coupled core vector `f`.  The estimate is the term-by-term transfer of §1 and the
triangle inequality; no property of the normal form beyond its shape is used. -/
theorem smNormalForm_norm_le (D : SmNormalFormData)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c : ℝ} (hc : 0 ≤ c)
    (hmom : ∀ (j : Fin 163) (x : polyGaussCore (d := 163)),
      ‖((smMom j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hkin : ∀ (j : Fin 163) (x : polyGaussCore (d := 163)),
      ‖((smKinetic j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hcoord : ∀ (j : Fin 163) (x : polyGaussCore (d := 163)),
      ‖((smPos j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hmass : ∀ x : polyGaussCore (d := 163), ‖((x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (f : SmCoupledCore) :
    ‖smNormalForm D f‖
      ≤ c * normalFormConst D * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by
  set R : ℝ := ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ with hR
  have hRnn : 0 ≤ R := by rw [hR]; exact norm_nonneg _
  have hfam : ∀ (T : Fin 163 → polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
      (M : Fin 163 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ),
      (∀ (j : Fin 163) (x : polyGaussCore (d := 163)),
        ‖((T j x : polyGaussCore (d := 163)) : L2d 163)‖
          ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖) →
      ‖(∑ j : Fin 163, smTensorCore (T j) (M j)) f‖
        ≤ c * (∑ j : Fin 163, Real.sqrt (pairSum (M j))) * R := by
    intro T M hb
    have h1 : ‖(∑ j : Fin 163, smTensorCore (T j) (M j)) f‖
        ≤ ∑ j : Fin 163, ‖smTensorCore (T j) (M j) f‖ := by
      rw [LinearMap.sum_apply]
      exact norm_sum_le _ _
    have h2 : ∑ j : Fin 163, ‖smTensorCore (T j) (M j) f‖
        ≤ ∑ j : Fin 163, c * Real.sqrt (pairSum (M j)) * R :=
      Finset.sum_le_sum fun j _ => smTensorCore_norm_le (T j) N (M j) hc (hb j) f
    refine (h1.trans h2).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hA := hfam smMom D.mom hmom
  have hB := hfam smKinetic D.kinetic hkin
  have hC := hfam smPos D.coord hcoord
  have hE : ‖smTensorCore LinearMap.id D.mass f‖
      ≤ c * Real.sqrt (pairSum D.mass) * R := by
    have h := smTensorCore_norm_le LinearMap.id N D.mass hc hmass f
    simpa only [LinearMap.id_coe, LinearMap.id_apply] using h
  have hshape : ‖smNormalForm D f‖
      ≤ ‖(∑ j : Fin 163, smTensorCore (smMom j) (D.mom j)) f‖
        + ‖(∑ j : Fin 163, smTensorCore (smKinetic j) (D.kinetic j)) f‖
        + ‖(∑ j : Fin 163, smTensorCore (smPos j) (D.coord j)) f‖
        + ‖smTensorCore LinearMap.id D.mass f‖ := by
    have h4 : ∀ (a b d e : SmCoupledSpace),
        ‖a + b + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖d‖ + ‖e‖ := by
      intro a b d e
      have h1 := norm_add_le (a + b + d) e
      have h2 := norm_add_le (a + b) d
      have h3 := norm_add_le a b
      linarith
    exact h4 _ _ _ _
  set s1 : ℝ := ∑ j : Fin 163, Real.sqrt (pairSum (D.mom j)) with hs1
  set s2 : ℝ := ∑ j : Fin 163, Real.sqrt (pairSum (D.kinetic j)) with hs2
  set s3 : ℝ := ∑ j : Fin 163, Real.sqrt (pairSum (D.coord j)) with hs3
  set s4 : ℝ := Real.sqrt (pairSum D.mass) with hs4
  have hA' : ‖(∑ j : Fin 163, smTensorCore (smMom j) (D.mom j)) f‖ ≤ c * s1 * R := by
    rw [hs1]; exact hA
  have hB' : ‖(∑ j : Fin 163, smTensorCore (smKinetic j) (D.kinetic j)) f‖ ≤ c * s2 * R := by
    rw [hs2]; exact hB
  have hC' : ‖(∑ j : Fin 163, smTensorCore (smPos j) (D.coord j)) f‖ ≤ c * s3 * R := by
    rw [hs3]; exact hC
  have hE' : ‖smTensorCore LinearMap.id D.mass f‖ ≤ c * s4 * R := by
    rw [hs4]; exact hE
  have hconst : normalFormConst D = ((s1 + s2) + s3) + s4 := by
    rw [normalFormConst, ← hs1, ← hs2, ← hs3, ← hs4]
  rw [hconst]
  have hsum : ‖(∑ j : Fin 163, smTensorCore (smMom j) (D.mom j)) f‖
        + ‖(∑ j : Fin 163, smTensorCore (smKinetic j) (D.kinetic j)) f‖
        + ‖(∑ j : Fin 163, smTensorCore (smPos j) (D.coord j)) f‖
        + ‖smTensorCore LinearMap.id D.mass f‖
      ≤ c * (((s1 + s2) + s3) + s4) * R := by
    have hdist : c * (((s1 + s2) + s3) + s4) * R
        = c * s1 * R + c * s2 * R + c * s3 * R + c * s4 * R := by ring
    rw [hdist]
    linarith
  linarith [hshape, hsum]


end

end BookProof.SmFullCoupledCore
