import Mathlib
import BookProof.Sm.ChapterSmFullFamilyBounds

/-!
# The commutator form of the full normal form, and the canonical Higgs placement

Work order: `SM_ESA_COMPLETION_PLAN.md` §16.  Two follow-ups to §15, plus the second-order
family.

## 1. The commutator form with general coefficient matrices

`coupledOp_one_commForm_le` (`BookProof.SmFullCoupledCore`) bounds the commutator form of
`h ⊗ I` against `N ⊗ I`, i.e. of a **scalar** factor coupled with the identity matrix.  Here the
factor is the full normal form `Σⱼ Tⱼ ⊗ Mⱼ`, whose coefficient matrices `Mⱼ` are arbitrary.

The mechanism is
`commForm_eq H N x = −2 Im ⟪H x, N x⟫`, so
`|commForm H (N ⊗ 1) f| ≤ 2 ‖H f‖ ‖(N ⊗ 1) f‖`; `smNormalForm_norm_le` supplies the first factor
and `coupledOp_self_norm_le` the second (`‖(N ⊗ 1) f‖ ≤ 2‖((N ⊗ 1) + 1) f‖`, from
`norm_le_norm_shift` componentwise).  The result,
`smNormalForm_commForm_le`, has both sides at the level of the *shifted graph norm squared*.
That is not an artefact of the proof: unlike the scalar case, where the imaginary part of a
single inner product `⟪T x, N x⟫` is bounded by the quadratic form of `N`, the components of a
general coefficient matrix pair `T f_B` with `N f_A`, so no `quadForm`-level bound is available —
only the product of the two norms.

## 2. The canonical Higgs placement

`SmInternalData.pos` is *data*: which of the `163` oscillator coordinates carries the `a`-th real
Higgs component.  §15's relative bound for the P1 normal form needed `hpos` (`D.pos a` is one of
the `40` harmonic coordinates `smCoord`).  `SmInternalData.canonical` fixes the placement — the
`a`-th Higgs on `smCoord ⟨a⟩` — and `smCanonicalPos_harmonic` then holds by `rfl`, so
`SmInternalData.canonical_toNormalForm_norm_le` is the relative bound with **no** unproved
hypothesis about the placement.  What remains is a modelling statement, not a proof obligation:
the physics fixes *that* the four Higgs modes are coordinate modes, and this is the canonical
choice among the harmonic ones.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFullNormalFormBounds

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.QgOuterFockFL
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmFullFamilyBounds BookProof.SmMatter BookProof.YangMillsHermite

noncomputable section

/-! ## 1. The commutator form of the full normal form -/

/-- **The comparison operator is bounded by its own shift**: `‖(N ⊗ 1) f‖ ≤ 2‖((N ⊗ 1) + 1)f‖`,
from `‖x‖ ≤ ‖N x + x‖` componentwise. -/
theorem coupledOp_self_norm_le (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163)
    (hpos : ∀ x : polyGaussCore (d := 163), 0 ≤ quadForm N x) (f : SmCoupledCore) :
    ‖coupledOp N 1 f‖ ≤ 2 * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by
  have hsq : ‖coupledOp N 1 f‖ ^ 2
      ≤ (2 * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖) ^ 2 := by
    rw [coupledSpace_norm_sq, mul_pow, coupledOp_one_add_norm_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun A _ => ?_
    rw [coupledOp_one_apply]
    have h1 := norm_le_norm_shift N hpos (coreComp f A)
    have h2 : ‖N (coreComp f A)‖ ≤ ‖N (coreComp f A)
        + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163)‖
        + ‖((coreComp f A : polyGaussCore (d := 163)) : L2d 163)‖ := by
      simpa using norm_sub_le (N (coreComp f A)
        + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163))
        (((coreComp f A : polyGaussCore (d := 163)) : L2d 163))
    have h5 : ‖N (coreComp f A)‖ ≤ 2 * ‖N (coreComp f A)
        + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163)‖ := by linarith
    have h6 : (2 : ℝ) ^ 2 * ‖N (coreComp f A)
        + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
        = (2 * ‖N (coreComp f A)
          + ((coreComp f A : polyGaussCore (d := 163)) : L2d 163)‖) ^ 2 := by ring
    rw [h6]
    exact pow_le_pow_left₀ (norm_nonneg _) h5 2
  have h7 : (0 : ℝ) ≤ 2 * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ :=
    mul_nonneg (by norm_num) (norm_nonneg _)
  have := (sq_le_sq).mp hsq
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg h7] at this
  exact this

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
-- the `L²`-coercion unifications and the `PiLp` norm expansion exceed the default budgets
/-- **The commutator form of the full normal form with general coefficient matrices.**  Given the
per-family scalar relative bounds of `smNormalForm_norm_le` (and positivity of the comparison's
quadratic form), the commutator form of `Σⱼ Tⱼ ⊗ Mⱼ` against `N ⊗ 1` is bounded by the shifted
graph norm squared, with the internal matrices entering only through `normalFormConst`. -/
theorem smNormalForm_commForm_le (D : SmNormalFormData)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c : ℝ} (hc : 0 ≤ c)
    (hpos : ∀ x : polyGaussCore (d := 163), 0 ≤ quadForm N x)
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
    |commForm (smNormalForm D) (coupledOp N 1) f|
      ≤ 4 * c * normalFormConst D * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ ^ 2 := by
  have hnf := smNormalForm_norm_le D N hc hmom hkin hcoord hmass f
  have hN := coupledOp_self_norm_le N hpos f
  have hcf : |commForm (smNormalForm D) (coupledOp N 1) f|
      ≤ 2 * ‖smNormalForm D f‖ * ‖coupledOp N 1 f‖ := by
    rw [commForm_eq, abs_mul, abs_neg]
    have h1 : |(2 : ℝ)| * |(inner ℂ (smNormalForm D f) (coupledOp N 1 f) : ℂ).im|
        ≤ 2 * ‖(inner ℂ (smNormalForm D f) (coupledOp N 1 f) : ℂ)‖ := by
      rw [abs_two]
      nlinarith [Complex.abs_im_le_norm (inner ℂ (smNormalForm D f) (coupledOp N 1 f))]
    refine h1.trans ?_
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (smNormalForm D f) (coupledOp N 1 f)
    linarith
  have hcn : (0 : ℝ) ≤ c * normalFormConst D :=
    mul_nonneg hc (normalFormConst_nonneg D)
  have hprod : ‖smNormalForm D f‖ * ‖coupledOp N 1 f‖
      ≤ (c * normalFormConst D * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖)
        * (2 * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖) :=
    mul_le_mul hnf hN (norm_nonneg _) (mul_nonneg hcn (norm_nonneg _))
  nlinarith [hcf, hprod, hcn, sq_nonneg ‖coupledOp N 1 f + (f : SmCoupledSpace)‖,
    norm_nonneg (smNormalForm D f)]

/-! ## 2. The canonical Higgs placement -/

/-- **The canonical placement of the four real Higgs components**: the `a`-th component sits on
the `a`-th harmonic coordinate `smCoord ⟨a⟩`. -/
def smCanonicalPos (a : Fin 4) : Fin 163 :=
  smCoord ⟨a.val, lt_of_lt_of_le a.isLt (by norm_num)⟩

/-- The canonical placement is harmonic, by construction: this is §15's `hpos`, discharged. -/
theorem smCanonicalPos_harmonic (a : Fin 4) : ∃ m : Fin 40, smCanonicalPos a = smCoord m :=
  ⟨_, rfl⟩

/-- **The P1 internal data at the canonical placement.**  The placement of the Higgs components is
the only part of `SmInternalData` this constructor fixes; the Higgs and Yukawa matrices are the
physical ones, together with their Hermiticity. -/
def SmInternalData.canonical (higgs : Fin 4 → Matrix SmMatterIndex SmMatterIndex ℂ)
    (higgsHermitian : ∀ a : Fin 4, (higgs a).conjTranspose = higgs a)
    (mass : Matrix SmMatterIndex SmMatterIndex ℂ) (massHermitian : mass.conjTranspose = mass) :
    SmInternalData where
  pos := smCanonicalPos
  higgs := higgs
  higgsHermitian := higgsHermitian
  mass := mass
  massHermitian := massHermitian

/-- **The relative bound of the P1 normal form at the canonical placement — with no hypothesis
left.**  Every hypothesis of `SmInternalData.toNormalForm_norm_le` is discharged: the placement
is harmonic by construction (`smCanonicalPos_harmonic`). -/
theorem SmInternalData.canonical_toNormalForm_norm_le
    (higgs : Fin 4 → Matrix SmMatterIndex SmMatterIndex ℂ)
    (higgsHermitian : ∀ a : Fin 4, (higgs a).conjTranspose = higgs a)
    (mass : Matrix SmMatterIndex SmMatterIndex ℂ) (massHermitian : mass.conjTranspose = mass)
    (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) (f : SmCoupledCore) :
    ‖smNormalForm (SmInternalData.canonical higgs higgsHermitian mass massHermitian).toNormalForm
        f‖
      ≤ 1 * normalFormConst
          (SmInternalData.canonical higgs higgsHermitian mass massHermitian).toNormalForm
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ :=
  SmInternalData.toNormalForm_norm_le _ P hc0 smCanonicalPos_harmonic f

/-! ## 3. The second-order family: `πⱼ²` is dominated by the kinetic energy -/

/-- `∂_i (X_k)` as a polynomial, in the form needed to commute derivatives. -/
theorem pderiv_X_eq {d : ℕ} (i k : Fin d) :
    MvPolynomial.pderiv i (MvPolynomial.X k : MvPolynomial (Fin d) ℂ)
      = if i = k then (1 : MvPolynomial (Fin d) ℂ) else 0 := by
  rw [MvPolynomial.pderiv_X]
  by_cases h : i = k
  · subst h
    simp
  · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]

/-- **Partial derivatives commute**: not in Mathlib, and the reason the momentum operators of
`πⱼ²` commute at all. -/
theorem pderiv_pderiv_comm {d : ℕ} (i j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p)
      = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
      simp only [pderiv_X_eq i k, pderiv_X_eq j k]
      rw [map_add, map_add]
      simp only [MvPolynomial.pderiv_mul, pderiv_X_eq i k, pderiv_X_eq j k, hp]
      split_ifs <;> simp_all

/-- **The momentum operators commute**: `[π_m, π_{m'}] = 0`.  The polynomial factor `∂_j − ½x_j`
commutes with `∂_k − ½x_k` by `pderiv_pderiv_comm`, and the transport `CoreRep.op` is an algebra
map. -/
theorem derOp_comp_comm {d : ℕ} (j k : Fin d) :
    (derOp j).comp (derOp k) = (derOp k).comp (derOp j) := by
  by_cases hjk : j = k
  · subst hjk; rfl
  refine LinearMap.ext fun p => ?_
  have hXk : MvPolynomial.pderiv j ((MvPolynomial.X k : MvPolynomial (Fin d) ℂ) * p)
      = (MvPolynomial.X k : MvPolynomial (Fin d) ℂ) * MvPolynomial.pderiv j p := by
    rw [MvPolynomial.pderiv_mul, pderiv_X_eq j k, if_neg hjk]
    ring
  have hXj : MvPolynomial.pderiv k ((MvPolynomial.X j : MvPolynomial (Fin d) ℂ) * p)
      = (MvPolynomial.X j : MvPolynomial (Fin d) ℂ) * MvPolynomial.pderiv k p := by
    rw [MvPolynomial.pderiv_mul, pderiv_X_eq k j, if_neg (Ne.symm hjk)]
    ring
  rw [LinearMap.comp_apply, LinearMap.comp_apply, derOp_apply, derOp_apply, derOp_apply,
    derOp_apply, map_sub, Derivation.map_smul, map_sub, Derivation.map_smul, hXk, hXj,
    pderiv_pderiv_comm j k]
  simp only [Algebra.smul_def]
  ring

/-- **`CoreRep.op` is multiplicative**: transporting a composite is the composite of the
transports. -/
theorem CoreRep.op_comp {d : ℕ} {D : Submodule ℂ (L2d d)} (Φ : CoreRep d D)
    (S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    Φ.op (S.comp T) = (Φ.op S).comp (Φ.op T) := by
  refine LinearMap.ext fun x => ?_
  simp only [CoreRep.op_apply, LinearMap.comp_apply, LinearEquiv.symm_apply_apply]

/-- The momentum operators of the core commute. -/
theorem momOp_comp_comm {d : ℕ} (j k : Fin d) :
    (momOp j).comp (momOp k) = (momOp k).comp (momOp j) := by
  simp only [momOp, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, derOp_comp_comm]

/-- **The momentum family `π` of the Standard Model one-particle Hamiltonian commutes.** -/
theorem smPi_comp_comm (m m' : Fin 40) :
    (smPi m).comp (smPi m') = (smPi m').comp (smPi m) := by
  rw [smPi, smPi, ← CoreRep.op_comp, ← CoreRep.op_comp, momOp_comp_comm]

/-- **A commuting family of symmetric operators is dominated, in norm, by the sum of its
squares.**  For pairwise commuting symmetric `Tⱼ`,

```text
‖Tᵢ (Tᵢ x)‖ ≤ ‖(Σⱼ Tⱼ ∘ Tⱼ) x‖,
```

because the squared norm of the sum expands into `Σⱼₖ ‖Tⱼ(Tₖ x)‖²`, all terms non-negative, and
the diagonal term `j = k = i` is `‖Tᵢ(Tᵢ x)‖²`. -/
theorem sq_norm_comp_le_sum {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {ι : Type*} [Fintype ι] (T : ι → F →ₗ[ℂ] F)
    (hsym : ∀ i, ∀ u v : F, inner ℂ (T i u) v = inner ℂ u (T i v))
    (hcomm : ∀ i k, (T i).comp (T k) = (T k).comp (T i)) (i : ι) (x : F) :
    ‖T i (T i x)‖ ≤ ‖(∑ k, (T k).comp (T k)) x‖ := by
  have key : ∀ k l : ι, (inner ℂ (T k (T k x)) (T l (T l x)) : ℂ)
      = ((‖T k (T l x)‖ ^ 2 : ℝ) : ℂ) := by
    intro k l
    have e1 : inner ℂ (T k (T k x)) (T l (T l x)) = inner ℂ (T l (T k (T k x))) (T l x) :=
      (hsym l (T k (T k x)) (T l x)).symm
    have e2 : T l (T k (T k x)) = T k (T l (T k x)) :=
      LinearMap.congr_fun (hcomm l k) (T k x)
    have e3 : inner ℂ (T k (T l (T k x))) (T l x) = inner ℂ (T l (T k x)) (T k (T l x)) :=
      hsym k (T l (T k x)) (T l x)
    have e4 : T k (T l x) = T l (T k x) := LinearMap.congr_fun (hcomm k l) x
    calc (inner ℂ (T k (T k x)) (T l (T l x)) : ℂ)
        = (inner ℂ (T l (T k (T k x))) (T l x) : ℂ) := e1
      _ = (inner ℂ (T k (T l (T k x))) (T l x) : ℂ) := by rw [e2]
      _ = (inner ℂ (T l (T k x)) (T k (T l x)) : ℂ) := e3
      _ = (inner ℂ (T k (T l x)) (T k (T l x)) : ℂ) := by rw [e4]
      _ = ((‖T k (T l x)‖ ^ 2 : ℝ) : ℂ) := by
          rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
          exact_mod_cast rfl
  have hnorm : ‖(∑ k, (T k).comp (T k)) x‖ ^ 2 = ∑ k, ∑ l, ‖T k (T l x)‖ ^ 2 := by
    have hSx : (∑ k, (T k).comp (T k)) x = ∑ k, T k (T k x) := by
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    have hsq : ((inner ℂ (∑ k, T k (T k x)) (∑ k, T k (T k x)) : ℂ)).re
        = ‖∑ k, T k (T k x)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
      exact Complex.ofReal_re _
    rw [hSx, ← hsq, sum_inner, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sum, Complex.re_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [key k l, Complex.ofReal_re]
  have hsingle := Finset.single_le_sum
    (f := fun k => ∑ l, ‖T k (T l x)‖ ^ 2) (fun k _ => Finset.sum_nonneg fun l _ => by positivity)
    (Finset.mem_univ i)
  have hdiag : ∑ l, ‖T i (T l x)‖ ^ 2 ≥ ‖T i (T i x)‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖T i (T l x)‖ ^ 2) (fun l _ => by positivity)
      (Finset.mem_univ i)
  have hsqrt : ‖T i (T i x)‖ ^ 2 ≤ ‖(∑ k, (T k).comp (T k)) x‖ ^ 2 := by
    rw [hnorm]
    exact hdiag.trans hsingle
  have h := (sq_le_sq).mp hsqrt
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h

/-- The spatial momentum index carrying the `m`-th member of the `40`-momentum family. -/
def smMomCoordFin (m : Fin 40) : Fin 163 := smMomCoord (smMomFin.symm m)

/-- **`π²` is the kinetic factor** at the corresponding coordinate: the second-order kinetic
operator of §15's `hkin` is a square of a member of the momentum family. -/
theorem smKinetic_eq_smPi_comp (m : Fin 40) :
    smKinetic (smMomCoordFin m) = (smPi m).comp (smPi m) := rfl

set_option maxHeartbeats 1000000 in
-- Heartbeats: the inherited inner-product instance on the 163-coordinate core.
/-- The symmetry hypothesis of `sq_norm_comp_le_sum`, transported from the ambient space to the
Gauss–polynomial core. -/
theorem smPi_inner_symmetric (m : Fin 40) (u v : polyGaussCore (d := 163)) :
    inner ℂ (smPi m u) v = inner ℂ u (smPi m v) := by
  have h := smPi_symmetricOn m u v
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.coe_inner] using h

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Heartbeats and recursion depth: the sum of 40 composites over the 163-coordinate core.
/-- **Every member of the `40`-momentum family satisfies the second-order bound against its own
family sum**: `‖πₘ²x‖ ≤ ‖(Σₘ πₘ²)x‖`.  Pairwise commutation and symmetry turn the squared norm of
the sum into the double sum `Σₘₖ ‖πₘπₖx‖²`, of which `‖πₘ²x‖²` is the diagonal term. -/
theorem smPi_sq_norm_le_kineticSum (m : Fin 40) (x : polyGaussCore (d := 163)) :
    ‖((smPi m (smPi m x) : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ ‖(((∑ m' : Fin 40, smPi m' (smPi m' x)) : polyGaussCore (d := 163)) : L2d 163)‖ := by
  have h := sq_norm_comp_le_sum (F := polyGaussCore (d := 163)) smPi smPi_inner_symmetric
    smPi_comp_comm m x
  calc ‖((smPi m (smPi m x) : polyGaussCore (d := 163)) : L2d 163)‖
      = ‖smPi m (smPi m x)‖ := (Submodule.coe_norm _).symm
    _ ≤ ‖(∑ k : Fin 40, (smPi k).comp (smPi k)) x‖ := h
    _ = ‖(((∑ k : Fin 40, (smPi k).comp (smPi k)) x : polyGaussCore (d := 163)) : L2d 163)‖ :=
        Submodule.coe_norm ((∑ k : Fin 40, (smPi k).comp (smPi k)) x)

/-- **The second-order per-family bound for the kinetic factor, reduced to the comparison
operator.**  If the kinetic energy sum satisfies the relative bound

```text
‖(Σₘ πₘ²)x‖ ≤ c ‖N x + x‖,
```

then so does every single `smKinetic j` at a momentum coordinate, with the same constant `c`.  This
is the hypothesis `hkin` of `smNormalForm_norm_le` in the `40` momentum directions; the remaining
input is the elliptic (Gårding) estimate for the kinetic sum, not a property of the individual
momenta. -/
theorem smKinetic_norm_le_shift (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c : ℝ}
    (hKin : ∀ x : polyGaussCore (d := 163),
      ‖(((∑ m' : Fin 40, smPi m' (smPi m' x)) : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (m : Fin 40) (x : polyGaussCore (d := 163)) :
    ‖((smKinetic (smMomCoordFin m) x : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ := by
  rw [smKinetic_eq_smPi_comp]
  exact (smPi_sq_norm_le_kineticSum m x).trans (hKin x)

end

end BookProof.SmFullNormalFormBounds
