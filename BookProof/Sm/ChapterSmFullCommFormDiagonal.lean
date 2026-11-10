import Mathlib
import BookProof.Sm.ChapterSmFullNormalFormBounds

/-!
# The commutator form: support-restricted data, the canonical placement, diagonal coefficients

Work order: `SM_ESA_COMPLETION_PLAN.md` §17.

## 1. The support-restricted commutator bound

§16's `smNormalForm_commForm_le` requires the scalar relative bound at **every** index of the
three bosonic families.  A normal form whose derivative families vanish — the P1 dictionary of
`SmInternalData.toNormalForm` — cannot supply them, and §15's `smNormalForm_norm_le_support`
already records the right form of the hypothesis: the family bound is needed only where the
coefficient matrix does not vanish.  The same restriction is put here on the commutator bound,
through the engine `abs_commForm_le_of_norm_le`: a relative bound `‖H f‖ ≤ C ‖(N ⊗ 1 + 1) f‖`
together with `‖(N ⊗ 1) f‖ ≤ 2 ‖(N ⊗ 1 + 1) f‖` gives
`|commForm H (N ⊗ 1) f| ≤ 4 C ‖(N ⊗ 1 + 1) f‖ ^ 2`.

## 2. The canonical P1 data

`SmInternalData.toNormalForm_commForm_le` is the commutator bound of the P1 dictionary, and
`SmInternalData.canonical_toNormalForm_commForm_le` instantiates it at the canonical placement of
§16, so that **no** family hypothesis and no placement hypothesis remains: every input is
discharged by `smPos_smCoord_norm_le_shift`, `norm_le_norm_shift` and `smCanonicalPos_harmonic`.

## 3. Diagonal coefficient matrices

The barrier of §16 — a general coefficient matrix pairs `T f_B` with `N f_A`, so only the product
of the two norms survives — disappears for a **diagonal** matrix: `T ⊗ diag d` pairs `T f_A` with
`N f_A` componentwise, and the scalar quadratic-form bound `|commForm T N y| ≤ c quadForm N y`
then sums to the quadratic-form level,

```text
|commForm (T ⊗ diag d) (N ⊗ 1) f| ≤ c (Σ_A d_A) quadForm (N ⊗ 1) f,
```

with no graph-norm-squared factor left.  The specialization to the canonical operator `h` is
`smHamiltonian_diagonal_commForm_le`, with `sm_commForm_le` as the scalar input.

## 4. The elliptic step

What is **not** here is the elliptic (Gårding) estimate for the kinetic sum,
`‖(Σₘ πₘ²) x‖ ≤ c ‖N x + x‖`, which §16's `smKinetic_norm_le_shift` takes as its hypothesis.  It
is not a formal consequence of the quadratic-form bounds the corpus proves
(`smPi_sq_le_quadForm_smFlN`): it is Kato relative boundedness of the second-order part with
respect to `N`, and its proof needs an interpolation (Gårding) inequality.  The corpus's
second-order norm bounds — e.g. `norm_kinPoly_le_shiftNorm`,
`‖pgLp (kinPoly p)‖ ≤ 3 ‖pgLp (harmP p) + pgLp p‖` — are for the **twisted** derivative
`coreD = ∂ − x / 2` of the oscillator picture, in which `kinPoly` is the Gaussian Laplacian; the SM
momenta are **plain** derivatives `∂`, and converting by `∂ = coreD + x / 2` costs one power of the
graph norm per factor.  The gap is therefore recorded rather than hidden: everything below is
conditional on nothing, but the elliptic estimate itself remains the named input of `hkin`.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullCommFormDiagonal

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.QgOuterFockFL
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmFullFamilyBounds BookProof.SmMatter BookProof.YangMillsHermite
open BookProof.SmFullNormalFormBounds

noncomputable section

/-! ## 1. The commutator bound from a relative norm bound -/

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The commutator form from a relative bound.**  If `H` obeys `‖H f‖ ≤ C ‖(N ⊗ 1 + 1) f‖` and
the comparison is positive, then `|commForm H (N ⊗ 1) f|` is bounded by `4 C` times the square of
the shifted graph norm.  This is the engine of §16's `smNormalForm_commForm_le`, separated so that
any relative bound — in particular a support-restricted one — can be fed into it. -/
theorem abs_commForm_le_of_norm_le (H : SmCoupledCore →ₗ[ℂ] SmCoupledSpace)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (hpos : ∀ x : polyGaussCore (d := 163), 0 ≤ quadForm N x)
    {C : ℝ} (hC : 0 ≤ C)
    (hnorm : ∀ f : SmCoupledCore,
      ‖H f‖ ≤ C * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖)
    (f : SmCoupledCore) :
    |commForm H (coupledOp N 1) f|
      ≤ 4 * C * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
  have hN := coupledOp_self_norm_le N hpos f
  have hcf : |commForm H (coupledOp N 1) f| ≤ 2 * ‖H f‖ * ‖coupledOp N 1 f‖ := by
    rw [commForm_eq, abs_mul, abs_neg]
    have h1 : |(2 : ℝ)| * |(inner ℂ (H f) (coupledOp N 1 f) : ℂ).im|
        ≤ 2 * ‖(inner ℂ (H f) (coupledOp N 1 f) : ℂ)‖ := by
      rw [abs_two]
      nlinarith [Complex.abs_im_le_norm (inner ℂ (H f) (coupledOp N 1 f))]
    refine h1.trans ?_
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (H f) (coupledOp N 1 f)
    linarith
  have hprod : ‖H f‖ * ‖coupledOp N 1 f‖
      ≤ (C * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖)
        * (2 * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖) :=
    mul_le_mul (hnorm f) hN (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
  nlinarith [hcf, hprod, hC, sq_nonneg ‖coupledOp N 1 f + (f : SmCoupledSpace)‖,
    norm_nonneg (H f)]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications and the `PiLp` norm expansion exceed the default budgets
/-- **The support-restricted commutator bound of the full normal form.**  Identical to §16's
`smNormalForm_commForm_le`, except that each family bound is required only on a finite index set
outside of which the coefficient matrix vanishes — the form in which the P1 dictionary, whose
derivative families are zero, can actually use it. -/
theorem smNormalForm_commForm_le_support (D : SmNormalFormData)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c : ℝ} (hc : 0 ≤ c)
    (hpos : ∀ x : polyGaussCore (d := 163), 0 ≤ quadForm N x)
    (Smom Skin Scoord : Finset (Fin 163))
    (hSmom : ∀ j ∉ Smom, D.mom j = 0) (hSkin : ∀ j ∉ Skin, D.kinetic j = 0)
    (hScoord : ∀ j ∉ Scoord, D.coord j = 0)
    (hmom : ∀ j ∈ Smom, ∀ x : polyGaussCore (d := 163),
      ‖((smMom j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hkin : ∀ j ∈ Skin, ∀ x : polyGaussCore (d := 163),
      ‖((smKinetic j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hcoord : ∀ j ∈ Scoord, ∀ x : polyGaussCore (d := 163),
      ‖((smPos j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hmass : ∀ x : polyGaussCore (d := 163), ‖((x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (f : SmCoupledCore) :
    |commForm (smNormalForm D) (coupledOp N 1) f|
      ≤ 4 * c * normalFormConst D * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
  have hC : (0 : ℝ) ≤ c * normalFormConst D := mul_nonneg hc (normalFormConst_nonneg D)
  have hmain := abs_commForm_le_of_norm_le (smNormalForm D) N hpos hC
    (fun f => smNormalForm_norm_le_support D N hc Smom Skin Scoord hSmom hSkin hScoord
      hmom hkin hcoord hmass f) f
  calc |commForm (smNormalForm D) (coupledOp N 1) f|
      ≤ 4 * (c * normalFormConst D) * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2 := hmain
    _ = 4 * c * normalFormConst D * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
        rw [mul_assoc 4 c (normalFormConst D)]

/-! ## 2. The canonical P1 data -/

/-- **The commutator bound of the P1 Yukawa dictionary.**  The derivative families are zero and
only the four Higgs coordinates carry a coefficient matrix, so §17's support-restricted bound
applies with `c = 1` on the support `univ.image D.pos`; the placement hypothesis `hpos` is the one
of `SmInternalData.toNormalForm_norm_le`. -/
theorem SmInternalData.toNormalForm_commForm_le (D : SmInternalData) (P : SmParams) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (f : SmCoupledCore) :
    |commForm (smNormalForm D.toNormalForm) (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * 1 * normalFormConst D.toNormalForm
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
  refine smNormalForm_commForm_le_support D.toNormalForm (smFlN P c0) (by norm_num)
    (smFlN_quadForm_nonneg P hc0) ∅ ∅ (Finset.univ.image D.pos) ?_ ?_ ?_ ?_ ?_ ?_ ?_ f
  · intro j _
    rfl
  · intro j _
    rfl
  · intro j hj
    change (∑ a : Fin 4,
      if D.pos a = j then fockMatrix (matterBilin (D.higgs a)) else 0) = 0
    refine Finset.sum_eq_zero fun a _ => ?_
    refine if_neg fun h => hj ?_
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, h⟩
  · intro j hj x
    exact absurd hj (by simp)
  · intro j hj x
    exact absurd hj (by simp)
  · intro j hj x
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hj
    obtain ⟨m, hm⟩ := hpos a
    rw [← ha, hm]
    exact smPos_smCoord_norm_le_shift P hc0 m x
  · intro x
    simpa only [one_mul] using
      (norm_le_norm_shift (smFlN P c0) (smFlN_quadForm_nonneg P hc0) x)

/-- **The commutator bound of the P1 normal form at the canonical placement — with no hypothesis
left.**  The placement is harmonic by construction (`smCanonicalPos_harmonic`), so
`SmInternalData.toNormalForm_commForm_le` applies with every input discharged. -/
theorem SmInternalData.canonical_toNormalForm_commForm_le
    (higgs : Fin 4 → Matrix SmMatterIndex SmMatterIndex ℂ)
    (higgsHermitian : ∀ a : Fin 4, (higgs a).conjTranspose = higgs a)
    (mass : Matrix SmMatterIndex SmMatterIndex ℂ) (massHermitian : mass.conjTranspose = mass)
    (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (f : SmCoupledCore) :
    |commForm
        (smNormalForm
          (SmInternalData.canonical higgs higgsHermitian mass massHermitian).toNormalForm)
        (coupledOp (smFlN P c0) 1) f|
      ≤ 4 * 1 * normalFormConst
          (SmInternalData.canonical higgs higgsHermitian mass massHermitian).toNormalForm
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ ^ 2 :=
  SmInternalData.toNormalForm_commForm_le _ P hc0 smCanonicalPos_harmonic f

/-! ## 3. Diagonal coefficient matrices -/

set_option maxHeartbeats 1000000 in
-- the double internal sum and the two inner products need more `isDefEq` work than the default
-- heartbeat budget allows
/-- **A diagonal coefficient matrix pairs a single component**: the `A`-th component of
`T ⊗ diag d` is `d_A • T f_A`. -/
theorem coupledOp_diagonal_apply (T : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (d : Finset (Fin 96) → ℝ) (f : SmCoupledCore) (A : Finset (Fin 96)) :
    (coupledOp T (Matrix.diagonal fun A => (d A : ℂ)) f).ofLp A
      = (d A : ℂ) • T (coreComp f A) := by
  rw [coupledOp_apply, Finset.sum_eq_single A]
  · rw [Matrix.diagonal_apply, if_pos rfl]
  · intro b _ hb
    rw [Matrix.diagonal_apply, if_neg (Ne.symm hb), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ A) h

set_option maxHeartbeats 1000000 in
-- the double internal sum and the two inner products need more `isDefEq` work than the default
-- heartbeat budget allows
/-- **The commutator form of a diagonal coefficient matrix is the sum of the scalar forms.**  This
is the identity behind §17's quadratic-form-level bound: with a diagonal matrix, no component of
`T f` is paired with the comparison of a *different* component. -/
theorem coupledOp_diagonal_commForm_eq (T N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (d : Finset (Fin 96) → ℝ) (f : SmCoupledCore) :
    commForm (coupledOp T (Matrix.diagonal fun A => (d A : ℂ))) (coupledOp N 1) f
      = ∑ A, d A * commForm T N (coreComp f A) := by
  have hinner : (inner ℂ ((coupledOp T (Matrix.diagonal fun A => (d A : ℂ))) f)
      (coupledOp N 1 f) : ℂ)
      = ∑ A, (d A : ℂ) * inner ℂ (T (coreComp f A)) (N (coreComp f A)) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [coupledOp_diagonal_apply, coupledOp_one_apply, inner_smul_left]
    simp
  rw [commForm_eq, hinner, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [commForm_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

set_option maxHeartbeats 1000000 in
-- the componentwise sums and their rearrangement exceed the default heartbeat budget
/-- **The commutator bound at the quadratic-form level for a diagonal coefficient matrix.**  Given
the scalar quadratic-form bound `|commForm T N y| ≤ c quadForm N y` and a non-negative diagonal,
the commutator form of `T ⊗ diag d` against `N ⊗ 1` is bounded by `c (Σ_A d_A)` times the
quadratic form of the coupled comparison — no shifted-graph-norm-squared factor remains. -/
theorem coupledOp_diagonal_commForm_le (T N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ y : polyGaussCore (d := 163), |commForm T N y| ≤ c * quadForm N y)
    (hposN : ∀ y : polyGaussCore (d := 163), 0 ≤ quadForm N y)
    (d : Finset (Fin 96) → ℝ) (hdiag : ∀ A, 0 ≤ d A) (f : SmCoupledCore) :
    |commForm (coupledOp T (Matrix.diagonal fun A => (d A : ℂ))) (coupledOp N 1) f|
      ≤ c * (∑ A, d A) * quadForm (coupledOp N 1) f := by
  have hsingle : ∀ A : Finset (Fin 96),
      quadForm N (coreComp f A) ≤ ∑ B, quadForm N (coreComp f B) := fun A =>
    Finset.single_le_sum (f := fun B => quadForm N (coreComp f B))
      (fun B _ => hposN (coreComp f B)) (Finset.mem_univ A)
  rw [coupledOp_diagonal_commForm_eq]
  calc |∑ A, d A * commForm T N (coreComp f A)|
      ≤ ∑ A, |d A * commForm T N (coreComp f A)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ A, d A * |commForm T N (coreComp f A)| := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [abs_mul, abs_of_nonneg (hdiag A)]
    _ ≤ ∑ A, d A * (c * quadForm N (coreComp f A)) :=
        Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hT (coreComp f A)) (hdiag A)
    _ = c * ∑ A, d A * quadForm N (coreComp f A) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun A _ => by ring
    _ ≤ c * ((∑ A, d A) * ∑ A, quadForm N (coreComp f A)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        calc ∑ A, d A * quadForm N (coreComp f A)
            ≤ ∑ A, d A * ∑ B, quadForm N (coreComp f B) :=
              Finset.sum_le_sum fun A _ =>
                mul_le_mul_of_nonneg_left (hsingle A) (hdiag A)
          _ = (∑ A, d A) * ∑ B, quadForm N (coreComp f B) := by rw [Finset.sum_mul]
    _ = c * (∑ A, d A) * quadForm (coupledOp N 1) f := by
        rw [coupledOp_one_quadForm]
        ring

/-- **The diagonal commutator bound for the canonical operator `h`.**  The scalar input is
`sm_commForm_le`, so the constant is `1` and the bound is exactly at the quadratic-form level of
the SM comparison. -/
theorem smHamiltonian_diagonal_commForm_le (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (d : Finset (Fin 96) → ℝ) (hdiag : ∀ A, 0 ≤ d A) (f : SmCoupledCore) :
    |commForm (coupledOp (smHamiltonian P) (Matrix.diagonal fun A => (d A : ℂ)))
        (coupledOp (smFlN P c0) 1) f|
      ≤ 1 * (∑ A, d A) * quadForm (coupledOp (smFlN P c0) 1) f :=
  coupledOp_diagonal_commForm_le (smHamiltonian P) (smFlN P c0) (by norm_num)
    (sm_commForm_le P hc0) (smFlN_quadForm_nonneg P hc0) d hdiag f

end

end BookProof.SmFullCommFormDiagonal
