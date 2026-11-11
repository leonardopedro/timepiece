import Mathlib
import BookProof.Sm.ChapterSmFullCoupledCore
import BookProof.Sm.ChapterSmFullYukawaCoeffs

/-!
# Per-family relative bounds for the comparison operator `N = 2h + Σ q² + c₀`

Work order: `SM_ESA_COMPLETION_PLAN.md` §14 (what P4 still needs).  `smNormalForm_norm_le` of
`BookProof.SmFullCoupledCore` reduces the relative bound of the full normal form to a
**per-family scalar bound**: for each bosonic factor `Tⱼ`,

```text
‖Tⱼ x‖ ≤ c ‖N x + x‖    for all `x` in the Gauss–polynomial core.
```

The corpus proves that bound for the *combination* `h` (`sm_norm_le_shift`, constant `1`).
This module proves it for the individual families:

* `smPi_norm_le_shift` — the momentum family `πⱼ = −i∂ⱼ`, in the `40` momentum-carrying
  coordinates;
* `smMomField_norm_le_shift` (and `smPos_smCoord_norm_le_shift`) — the coordinate family `uⱼ`,
  in the same `40` coordinates (the ones the harmonic part `Σ_m q_m²` of `N` controls);
* `smField_norm_le_shift` — the `49` field polynomials `Ψ_r` of the Hamiltonian.

All three hold with the absolute constant `1`, for every choice of couplings.

The mechanism is one identity: the quadratic form of the comparison operator dominates the
family, and a positive quadratic form is bounded by the square of the shifted graph norm,
`quadForm N x ≤ ½‖N x + x‖²` (`quadForm_le_half_norm_add_sq`).  No spectral information about
`N` is used.

## Honest boundary

* The second-order family `πⱼ² = −∂ⱼ²` (`smKinetic`) is **not** covered.  Bounding it needs the
  quadratic form of `N` at `πⱼ x`, i.e. a second-order estimate rather than a first-order one;
  `quadForm (smFlN P c₀)` contains exactly one power of `πⱼ²`, so the argument used here does not
  apply.  This is the remaining input of `smNormalForm_norm_le` for the P2 normal form.
* The coordinate family is bounded only in the `40` harmonic coordinates.  For a coordinate `uⱼ`
  outside them the comparison operator `N` carries no `uⱼ²` term, so no such bound can hold
  from the quadratic form alone.
* Consequently `smNormalForm_norm_le_support` (below) allows the coefficient matrices to vanish
  outside a finite index set — which is exactly the shape of the P1 data
  (`SmInternalData.toNormalForm`: zero derivative families, four Higgs coordinates).  The result
  `SmInternalData.toNormalForm_norm_le` is the relative bound of the P1 Yukawa normal form, and
  it is **conditional** on those four coordinates being harmonic ones (`hpos`).

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullFamilyBounds

open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.FriedrichsExtension
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.QgOuterFockFL
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmMatter

noncomputable section

/-! ## 1. A positive quadratic form is bounded by the shifted graph norm -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- **A positive quadratic form is bounded by the square of the shifted graph norm.**  For a
symmetric `A` with non-negative quadratic form, `⟪x, A x⟫ ≤ ½‖A x + x‖²`: the cross term of the
shift is the quadratic form itself, hence non-negative, and the remaining two squares are the
ones bounded by Cauchy–Schwarz. -/
theorem quadForm_le_half_norm_add_sq (A : D →ₗ[ℂ] F) (hsym : SymmetricOn D A)
    (hnn : ∀ x : D, 0 ≤ quadForm A x) (x : D) :
    quadForm A x ≤ 1 / 2 * ‖A x + (x : F)‖ ^ 2 := by
  have hself : quadForm A x = (inner ℂ (A x) (x : F) : ℂ).re := by
    rw [quadForm, hsym x x]
  have h1 : quadForm A x ≤ ‖A x‖ * ‖(x : F)‖ := by
    rw [hself]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ‖A x‖ ^ 2 + ‖(x : F)‖ ^ 2 ≤ ‖A x + (x : F)‖ ^ 2 := by
    rw [norm_add_sq_re, ← hself]
    nlinarith [hnn x]
  nlinarith [h1, h2, norm_nonneg (A x), norm_nonneg (x : F),
    sq_nonneg (‖A x‖ - ‖(x : F)‖)]

/-- **The per-family relative bound, from a quadratic-form domination.**  If `‖T x‖² ≤ 2 ⟪x, N x⟫`
for a symmetric positive `N`, then `‖T x‖ ≤ 1 · ‖N x + x‖`. -/
theorem norm_le_shift_of_sq_le_quadForm (A : D →ₗ[ℂ] F) (hsym : SymmetricOn D A)
    (hnn : ∀ x : D, 0 ≤ quadForm A x) (T : D →ₗ[ℂ] F)
    (hT : ∀ x : D, ‖T x‖ ^ 2 ≤ 2 * quadForm A x) (x : D) :
    ‖T x‖ ≤ 1 * ‖A x + (x : F)‖ := by
  have hq := quadForm_le_half_norm_add_sq A hsym hnn x
  have hsq : ‖T x‖ ^ 2 ≤ ‖A x + (x : F)‖ ^ 2 := by nlinarith [hT x]
  have h := (sq_le_sq).mp hsq
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h
  rw [one_mul]
  exact h

end Abstract

/-! ## 2. The quadratic form of `N` dominates each family -/

/-- The momentum family is dominated by the quadratic form of the comparison operator. -/
theorem smPi_sq_le_quadForm_smFlN (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (m : Fin 40)
    (x : polyGaussCore (d := 163)) :
    ‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
      ≤ 2 * quadForm (smFlN P c0) x := by
  have hsingle := Finset.single_le_sum
    (f := fun m : Fin 40 => ‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ m)
  have hF : (0 : ℝ) ≤ ∑ r : Fin 49,
      ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hQ := smQL_quadForm_nonneg x
  have hx : (0 : ℝ) ≤ ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by positivity
  have hshift := smFlN_quadForm P c0 x
  have hH := smHamiltonian_quadForm P x
  nlinarith [hsingle, hF, hQ, hx, hshift, hH, mul_nonneg hc0 hx]

/-- The harmonic coordinate family `u_{q_m}` is dominated by the quadratic form of `N`. -/
theorem smMomField_sq_le_quadForm_smFlN (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (m : Fin 40) (x : polyGaussCore (d := 163)) :
    ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
      ≤ 2 * quadForm (smFlN P c0) x := by
  have hQf := smQL_quadForm x
  have hsingle := Finset.single_le_sum
    (f := fun m : Fin 40 => ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ m)
  have hF : (0 : ℝ) ≤ ∑ r : Fin 49,
      ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hx : (0 : ℝ) ≤ ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by positivity
  have hshift := smFlN_quadForm P c0 x
  have hH := smHamiltonian_quadForm P x
  have hHnn := smHamiltonian_quadForm_nonneg P x
  nlinarith [hsingle, hF, hQf, hx, hshift, hH, hHnn, mul_nonneg hc0 hx]

/-- Each field polynomial is dominated by the quadratic form of `N`. -/
theorem smField_sq_le_quadForm_smFlN (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (r : Fin 49)
    (x : polyGaussCore (d := 163)) :
    ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
      ≤ 2 * quadForm (smFlN P c0) x := by
  have hsingle := Finset.single_le_sum
    (f := fun r : Fin 49 => ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ r)
  have hK : (0 : ℝ) ≤ ∑ m : Fin 40,
      ‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hQ := smQL_quadForm_nonneg x
  have hx : (0 : ℝ) ≤ ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by positivity
  have hshift := smFlN_quadForm P c0 x
  have hH := smHamiltonian_quadForm P x
  nlinarith [hsingle, hK, hQ, hx, hshift, hH, mul_nonneg hc0 hx]

/-! ## 3. The relative bounds with constant `1` -/

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The momentum family satisfies the relative bound with constant `1`.** -/
theorem smPi_norm_le_shift (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (m : Fin 40)
    (x : polyGaussCore (d := 163)) :
    ‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ 1 * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ :=
  norm_le_shift_of_sq_le_quadForm (smFlN P c0) (smFlN_symmetricOn P c0)
    (smFlN_quadForm_nonneg P hc0)
    ((polyGaussCore (d := 163)).subtype.comp (smPi m))
    (fun x => by
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply]
        using smPi_sq_le_quadForm_smFlN P hc0 m x) x

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The harmonic coordinate family satisfies the relative bound with constant `1`.** -/
theorem smMomField_norm_le_shift (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (m : Fin 40)
    (x : polyGaussCore (d := 163)) :
    ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ 1 * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ :=
  norm_le_shift_of_sq_le_quadForm (smFlN P c0) (smFlN_symmetricOn P c0)
    (smFlN_quadForm_nonneg P hc0)
    ((polyGaussCore (d := 163)).subtype.comp (smMomField m))
    (fun x => by
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply]
        using smMomField_sq_le_quadForm_smFlN P hc0 m x) x

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- The coordinate family, in the form of the P2 normal form: `smPos` at a harmonic
coordinate is the coordinate multiplication `smMomField`. -/
theorem smPos_smCoord_norm_le_shift (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (m : Fin 40)
    (x : polyGaussCore (d := 163)) :
    ‖((smPos (smCoord m) x : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ 1 * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ :=
  smMomField_norm_le_shift P hc0 m x

set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **Each field polynomial satisfies the relative bound with constant `1`.** -/
theorem smField_norm_le_shift (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (r : Fin 49)
    (x : polyGaussCore (d := 163)) :
    ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ 1 * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ :=
  norm_le_shift_of_sq_le_quadForm (smFlN P c0) (smFlN_symmetricOn P c0)
    (smFlN_quadForm_nonneg P hc0)
    ((polyGaussCore (d := 163)).subtype.comp (smField P r))
    (fun x => by
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply]
        using smField_sq_le_quadForm_smFlN P hc0 r x) x

/-! ## 4. The relative bound of a normal form supported on finitely many indices -/

/-- The elementary tensor with a zero coefficient matrix vanishes. -/
theorem smTensorCore_zero (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163)) :
    smTensorCore T (0 : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) = 0 := by
  refine LinearMap.ext fun f => ?_
  refine WithLp.ofLp_injective 2 (funext fun A => ?_)
  simp only [smTensorCore_apply, Matrix.zero_apply, zero_smul, Finset.sum_const_zero,
    LinearMap.zero_apply]
  simp

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications and the `PiLp` core exceed the default budgets
/-- **The relative bound of the full normal form, with each family supported on a finite index
set.**  The per-family scalar bounds are required only where the coefficient matrix does not
vanish, which is what makes the statement usable for data whose derivative families are zero. -/
theorem smNormalForm_norm_le_support (D : SmNormalFormData)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c : ℝ} (hc : 0 ≤ c)
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
    ‖smNormalForm D f‖
      ≤ c * normalFormConst D * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by
  set R : ℝ := ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ with hR
  have hRnn : 0 ≤ R := by rw [hR]; exact norm_nonneg _
  have hfam : ∀ (T : Fin 163 → polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
      (M : Fin 163 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) (S : Finset (Fin 163)),
      (∀ j ∉ S, M j = 0) →
      (∀ j ∈ S, ∀ x : polyGaussCore (d := 163),
        ‖((T j x : polyGaussCore (d := 163)) : L2d 163)‖
          ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖) →
      ‖(∑ j : Fin 163, smTensorCore (T j) (M j)) f‖
        ≤ c * (∑ j : Fin 163, Real.sqrt (pairSum (M j))) * R := by
    intro T M S hS hb
    have h1 : ‖(∑ j : Fin 163, smTensorCore (T j) (M j)) f‖
        ≤ ∑ j : Fin 163, ‖smTensorCore (T j) (M j) f‖ := by
      rw [LinearMap.sum_apply]
      exact norm_sum_le _ _
    have h2 : ∑ j : Fin 163, ‖smTensorCore (T j) (M j) f‖
        ≤ ∑ j : Fin 163, c * Real.sqrt (pairSum (M j)) * R := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hj : j ∈ S
      · exact smTensorCore_norm_le (T j) N (M j) hc (hb j hj) f
      · rw [hS j hj, smTensorCore_zero, LinearMap.zero_apply, norm_zero]
        have := pairSum_nonneg (M j)
        positivity
    refine (h1.trans h2).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hA := hfam smMom D.mom Smom hSmom hmom
  have hB := hfam smKinetic D.kinetic Skin hSkin hkin
  have hC := hfam smPos D.coord Scoord hScoord hcoord
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

/-! ## 5. The relative bound of the P1 Yukawa normal form -/

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The relative bound of the P1 data.**  The normal form of the P1 Yukawa dictionary — the four
second-quantized Higgs generators in the coordinate family, the Yukawa insertion in the mass
slot, and nothing in the derivative families — obeys

```text
‖h_P1 f‖ ≤ 1 · normalFormConst D · ‖(N ⊗ I + 1) f‖,
```

for `N = 2h + Σ q² + c₀` with `c₀ ≥ 0`, provided the four coordinates the Higgs couples to are
harmonic ones (`hpos`).  The constant is the one of `smNormalForm_norm_le`, with `c = 1` supplied
by `smPos_smCoord_norm_le_shift` and by `norm_le_norm_shift` for the mass slot; the derivative
families contribute nothing because their coefficient matrices are zero. -/
theorem SmInternalData.toNormalForm_norm_le (D : SmInternalData) (P : SmParams) {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hpos : ∀ a : Fin 4, ∃ m : Fin 40, D.pos a = smCoord m)
    (f : SmCoupledCore) :
    ‖smNormalForm D.toNormalForm f‖
      ≤ 1 * normalFormConst D.toNormalForm
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ := by
  refine smNormalForm_norm_le_support D.toNormalForm (smFlN P c0) (by norm_num)
    ∅ ∅ (Finset.univ.image D.pos) ?_ ?_ ?_ ?_ ?_ ?_ ?_ f
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

end

end BookProof.SmFullFamilyBounds
