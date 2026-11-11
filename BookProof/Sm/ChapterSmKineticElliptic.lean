import Mathlib
import BookProof.Sm.ChapterSmFullNormalFormBounds
import BookProof.Sm.ChapterSmComparisonEsa

/-!
# The kinetic sum as a plain Laplacian, and the interpolation half of the elliptic estimate

Work order: `SM_ESA_COMPLETION_PLAN.md` §19.

## 1. The kinetic sum *is* the plain Laplacian, in the function picture

§17's §4 recorded the elliptic step as blocked by a mismatch of derivatives: the SM momenta were
said to be plain derivatives while the corpus's second-order bounds were for the twisted
`coreD = ∂ − x/2` of the oscillator picture, so that converting would cost a power of the graph
norm per factor.  **That reading is wrong, and this module fixes it.**  `coreD` is the twisted
derivative on *polynomials*, but `kinPoly p = −Σ_j coreD_j (coreD_j p)` is the plain Laplacian of
the *function* `pgFun p = p · e^{−‖x‖²/4}`: `lapCS_pgFun` states `Δ_S (pgFun p) = pgFun (kinPolyS S
p)`.  Since `momOp j = (−i) • coreD j` and `(−i)² = −1`, `smPi m` transported is exactly
`−∂²` in the function picture, and the kinetic sum of the SM is the plain partial Laplacian
`kinPolyS smS`:

```text
Σ_m π_m (π_m x)  =  ⟨pgLp (kinPolyS smS p)⟩      for  x = ⟨pgLp p⟩.
```

So the corpus's `norm_kinPoly_le_shiftNorm` **is** the plain-derivative analogue, and the SM's
kinetic sum can be bounded against a *harmonic* comparison exactly as there.  What blocks the SM
is not the derivative but the potential: the SM comparison `N = −Δ_{smS} + W` carries the
quartic `W = Σ_r Φ_r² + Σ_m q_m² + c₀`, while `norm_sq_harmPoly_mul_le` — the uncertainty-bound
step behind `norm_kinPoly_le_shiftNorm` — controls the *quadratic* `harmPoly` against the
oscillator's own graph norm.  `kineticSum_norm_le_of_poly` therefore isolates the whole analytic
content of §16's `hkin` in **one polynomial inequality** `hpoly`, of exactly the shape
`norm_kinPoly_le_shiftNorm` but with the SM's comparison on the right:

```text
‖pgLp (kinPolyS smS p)‖ ≤ c ‖pgLp (kinPolyS smS p + smPotPoly P c₀ * p) + pgLp p‖.
```

That inequality is the named gap of this module, not a consequence of anything here.

## 2. The interpolation half: second order implies first order

What *is* proved here is the half of a Gårding interpolation argument that the corpus was missing
entirely, and it is the classical mechanism by which a bound on a *square* gives a bound on the
operator itself (Caccioppoli/Young interpolation):

```text
‖T x‖² = ⟪T²x, x⟫ ≤ ‖T²x‖ ‖x‖,      and        2ab ≤ εa² + b²/ε  (ε > 0).
```

`sq_norm_le_norm_comp_mul_norm` is the first identity for a core-symmetric `T`, and
`sq_norm_le_of_comp_self_eps` is the ε-form that trades a second-order term against a
zeroth-order one — the Gårding interpolation in its abstract form.  Fed with the kinetic-sum
estimate, it gives `smMom_norm_le_shift_of_kineticSum`: **the momentum families need no relative
bound of their own**.  Consequently `smNormalForm_norm_le_of_kineticSum` proves §15's second-order
family bound with the hypothesis `hmom` removed — the momentum slot now only records *where*
`D.mom` is supported — so the whole P2 relative bound rests on the single elliptic input.

## 3. The honest boundary

For a potential `W` of degree four, applying the ε-form needs `‖W²x‖` dominated by `‖N x + x‖`,
which is the same statement as the elliptic estimate itself: there is no circular shortcut, and
none is taken here.  §19's gap is `hpoly` above; everything else in the SM chain is proved.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmKineticElliptic

open MeasureTheory MvPolynomial
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.DegSchrodinger BookProof.DegKatoEsa BookProof.HermiteGraphApprox
open BookProof.SmOneParticle BookProof.SmHamiltonian BookProof.SmFarisLavine
open BookProof.SmComparisonEsa BookProof.SmFullFamilyBounds BookProof.SmFullNormalFormBounds
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmMatter BookProof.QgOuterFockFL

noncomputable section

/-! ## 1. The transport and the kinetic sum -/

/-- **The pointwise action of the SM momentum on the polynomial picture**: `π_m` transported is
`−i ∂` of the polynomial, hence `π_m²` is the plain second derivative. -/
theorem smPi_apply_pgLp_core (m : Fin 40) (p : MvPolynomial (Fin 163) ℂ) :
    smPi m ⟨pgLp p, pgLp_mem_core p⟩ = ⟨pgLp (momOp (smCoord m) p), pgLp_mem_core _⟩ := by
  rw [show smPi m = (coreRepPoly 163).op (momOp (smCoord m)) from rfl, op_pgLp]

/-- The same action read in the ambient space. -/
theorem smPi_apply_pgLp (m : Fin 40) (p : MvPolynomial (Fin 163) ℂ) :
    ((smPi m ⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := 163)) : L2d 163)
      = pgLp (momOp (smCoord m) p) := by
  rw [smPi_apply_pgLp_core]

set_option maxHeartbeats 1000000 in
-- the 40-fold transport of the momentum family and its reassembly exceed the default budget
/-- **The SM kinetic sum is the plain partial Laplacian** `−Δ_{smS}` in the function picture:
`Σ_m π_m (π_m x) = ⟨pgLp (kinPolyS smS p)⟩` for `x = ⟨pgLp p⟩`.  This is the identification
`sum_momOp_eq_kinPolyS` at the level of the core. -/
theorem kineticSum_apply_pgLp (p : MvPolynomial (Fin 163) ℂ) :
    (∑ m : Fin 40, smPi m (smPi m ⟨pgLp p, pgLp_mem_core p⟩))
      = ⟨pgLp (kinPolyS smS p), pgLp_mem_core _⟩ := by
  have hterm : ∀ m : Fin 40,
      ((smPi m (smPi m ⟨pgLp p, pgLp_mem_core p⟩) : polyGaussCore (d := 163)) : L2d 163)
        = pgLp (momOp (smCoord m) (momOp (smCoord m) p)) := by
    intro m
    rw [smPi_apply_pgLp_core, smPi_apply_pgLp_core]
  have hsum : ∀ (n : ℕ) (f : Fin n → MvPolynomial (Fin 163) ℂ),
      (∑ i : Fin n, pgLp (f i)) = pgLp (∑ i : Fin n, f i) := by
    intro n f
    rw [← HermiteProductCore.pgMap_apply, map_sum]
    rfl
  refine Subtype.ext ?_
  rw [Submodule.coe_sum, Finset.sum_congr rfl fun m _ => hterm m, hsum,
    sum_momOp_eq_kinPolyS]

/-- **The norm of the kinetic sum** is the `L²` norm of the partial Laplacian. -/
theorem kineticSum_norm_pgLp (p : MvPolynomial (Fin 163) ℂ) :
    ‖(((∑ m : Fin 40, smPi m (smPi m ⟨pgLp p, pgLp_mem_core p⟩)
      : polyGaussCore (d := 163)) : L2d 163))‖ = ‖pgLp (kinPolyS smS p)‖ := by
  rw [kineticSum_apply_pgLp]

/-- **The comparison operator of the SM in the polynomial picture**:
`N = −Δ_{smS} + Σ_r Φ_r² + Σ_m q_m² + c₀`, with no derivative left on the potential. -/
theorem smFlN_apply_pgLp (P : SmParams) (c0 : ℝ) (p : MvPolynomial (Fin 163) ℂ) :
    smFlN P c0 ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (kinPolyS smS p + smPotPoly P c0 * p) := by
  rw [smFlN_eq_hamCoreS P c0, hamCoreS_pgLp, hamPolyS,
    potLp_polyW (realCoeff_smPotPoly P c0)]
  rw [← HermiteProductCore.pgMap_apply, ← HermiteProductCore.pgMap_apply, ← map_add]
  rfl

/-- **The elliptic estimate of the kinetic sum, reduced to one polynomial inequality.**  The
inequality `hpoly` is `norm_kinPoly_le_shiftNorm`'s shape with the SM comparison in place of the
oscillator: same plain Laplacian on the left, the SM's quartic potential on the right.  It is the
single analytic input of §16's `hkin`; nothing else is assumed. -/
theorem kineticSum_norm_le_of_poly (P : SmParams) (c0 : ℝ) {c : ℝ}
    (hpoly : ∀ p : MvPolynomial (Fin 163) ℂ,
      ‖pgLp (kinPolyS smS p)‖
        ≤ c * ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖)
    (x : polyGaussCore (d := 163)) :
    ‖(((∑ m : Fin 40, smPi m (smPi m x)) : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ c * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ := by
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  rw [kineticSum_norm_pgLp, smFlN_apply_pgLp]
  exact hpoly p

/-! ## 2. Interpolation: a bound on the square gives a bound on the operator -/

set_option maxHeartbeats 1000000 in
-- the inner-product coercions of the 163-dimensional core exceed the default budget
/-- **The interpolation identity `‖T x‖² = ⟪T²x, x⟫ ≤ ‖T²x‖ ‖x‖`** for a core-symmetric `T`.
This is the mechanism by which a second-order relative bound controls the first-order operator
(the Caccioppoli/Young step of a Gårding interpolation), and it needs nothing but symmetry. -/
theorem sq_norm_le_norm_comp_mul_norm
    (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (hT : SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp T)) (x : polyGaussCore (d := 163)) :
    ‖((T x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
      ≤ ‖((T (T x) : polyGaussCore (d := 163)) : L2d 163)‖
        * ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ := by
  have hsym : inner ℂ (((T (T x) : polyGaussCore (d := 163)) : L2d 163))
      ((x : polyGaussCore (d := 163)) : L2d 163)
      = inner ℂ (((T x : polyGaussCore (d := 163)) : L2d 163))
        (((T x : polyGaussCore (d := 163)) : L2d 163)) := hT (T x) x
  have hsq : (inner ℂ (((T x : polyGaussCore (d := 163)) : L2d 163))
      (((T x : polyGaussCore (d := 163)) : L2d 163))).re
      = ‖((T x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    exact Complex.ofReal_re _
  calc ‖((T x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
      = (inner ℂ (((T (T x) : polyGaussCore (d := 163)) : L2d 163))
          ((x : polyGaussCore (d := 163)) : L2d 163)).re := by rw [hsym, hsq]
    _ ≤ ‖(inner ℂ (((T (T x) : polyGaussCore (d := 163)) : L2d 163))
          ((x : polyGaussCore (d := 163)) : L2d 163))‖ := Complex.re_le_norm _
    _ ≤ ‖((T (T x) : polyGaussCore (d := 163)) : L2d 163)‖
          * ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ := norm_inner_le_norm _ _

set_option maxHeartbeats 1000000 in
-- the real coercions of the core norms exceed the default heartbeat budget
/-- **The ε-form of the interpolation, i.e. Young's inequality applied to it**:
`‖T x‖² ≤ ε ‖T²x‖² + (4ε)⁻¹ ‖x‖²`.  This is the Gårding interpolation in the form that trades a
second-order term against a zeroth-order one with an arbitrarily small coefficient. -/
theorem sq_norm_le_of_comp_self_eps
    (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (hT : SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp T)) {eps : ℝ} (heps : 0 < eps)
    (x : polyGaussCore (d := 163)) :
    ‖((T x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
      ≤ eps * ‖((T (T x) : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
        + (1 / (4 * eps)) * ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by
  have h := sq_norm_le_norm_comp_mul_norm T hT x
  set a : ℝ := ‖((T (T x) : polyGaussCore (d := 163)) : L2d 163)‖ with ha
  set b : ℝ := ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hsq : (0 : ℝ) ≤ (2 * eps * a - b) ^ 2 := sq_nonneg _
  have hfac : (eps * a ^ 2 + (1 / (4 * eps)) * b ^ 2) * (4 * eps)
      = 4 * eps ^ 2 * a ^ 2 + b ^ 2 := by
    field_simp
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 4 * eps)
  rw [hfac]
  have hmul : ‖((T x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 * (4 * eps)
      ≤ (a * b) * (4 * eps) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [ha, hb]
    exact h
  refine hmul.trans ?_
  nlinarith [hsq]

/-! ## 3. The first-order families from the kinetic-sum estimate -/

/-- Every `c ≥ 1` dominates its own square root. -/
theorem sqrt_le_self_of_one_le {c : ℝ} (hc : 1 ≤ c) : Real.sqrt c ≤ c := by
  have h0 : 0 ≤ c := le_trans (by norm_num) hc
  have h1 : Real.sqrt c ^ 2 = c := Real.sq_sqrt h0
  have h2 : c ≤ c ^ 2 := by nlinarith
  nlinarith [Real.sqrt_nonneg c]

set_option maxHeartbeats 1000000 in
-- the inner-product coercions of the 163-dimensional core exceed the default budget
/-- **The momentum family is bounded by the kinetic-sum estimate alone.**  `‖π_m x‖² ≤
‖π_m² x‖ ‖x‖` and both factors are dominated by the shifted graph norm, so the first-order
momentum needs no relative bound of its own — the interpolation half of the elliptic step. -/
theorem smMom_norm_le_shift_of_kineticSum (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c : ℝ}
    (hc : 0 ≤ c) (hpos : ∀ x : polyGaussCore (d := 163), 0 ≤ quadForm N x)
    (hKin : ∀ x : polyGaussCore (d := 163),
      ‖(((∑ m' : Fin 40, smPi m' (smPi m' x)) : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (m : Fin 40) (x : polyGaussCore (d := 163)) :
    ‖((smMom (smMomCoordFin m) x : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ Real.sqrt c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ := by
  set g : ℝ := ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ with hg
  have hg0 : 0 ≤ g := norm_nonneg _
  have hx : ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ≤ g := norm_le_norm_shift N hpos x
  have h2 : ‖((smKinetic (smMomCoordFin m) x : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ c * g := smKinetic_norm_le_shift N hKin m x
  have h1 := sq_norm_le_norm_comp_mul_norm (smMom (smMomCoordFin m))
    (smMom_symmetricOn _) x
  have hcomp : ((smMom (smMomCoordFin m) (smMom (smMomCoordFin m) x)
      : polyGaussCore (d := 163)) : L2d 163)
      = ((smKinetic (smMomCoordFin m) x : polyGaussCore (d := 163)) : L2d 163) := rfl
  rw [hcomp] at h1
  have hkey : ‖((smMom (smMomCoordFin m) x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
      ≤ (Real.sqrt c * g) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc]
    have hprod : ‖((smKinetic (smMomCoordFin m) x : polyGaussCore (d := 163)) : L2d 163)‖
        * ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ≤ (c * g) * g :=
      mul_le_mul h2 hx (norm_nonneg _) (mul_nonneg hc hg0)
    calc ‖((smMom (smMomCoordFin m) x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
        ≤ ‖((smKinetic (smMomCoordFin m) x : polyGaussCore (d := 163)) : L2d 163)‖
            * ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ := h1
      _ ≤ (c * g) * g := hprod
      _ = c * g ^ 2 := by ring
  have hnonneg : (0 : ℝ) ≤ Real.sqrt c * g := mul_nonneg (Real.sqrt_nonneg _) hg0
  have := (sq_le_sq).mp hkey
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hnonneg] at this

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
-- the support reindexing and the `PiLp` norm expansion exceed the default budgets
/-- **The second-order family bound with the momentum hypothesis removed.**  §15's
`smNormalForm_norm_le_support` needs a relative bound for every momentum slot; by
`smMom_norm_le_shift_of_kineticSum` the slots occupied by the `40` momentum coordinates inherit
one from the kinetic-sum estimate, so only the *support* of `D.mom` has to be recorded.  The
constant passes from `√c` to `c` because `c ≥ 1`. -/
theorem smNormalForm_norm_le_of_kineticSum (D : SmNormalFormData)
    (N : polyGaussCore (d := 163) →ₗ[ℂ] L2d 163) {c : ℝ} (hc : 1 ≤ c)
    (hpos : ∀ x : polyGaussCore (d := 163), 0 ≤ quadForm N x)
    (hKin : ∀ x : polyGaussCore (d := 163),
      ‖(((∑ m' : Fin 40, smPi m' (smPi m' x)) : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hSmom : ∀ j ∉ Finset.image smMomCoordFin Finset.univ, D.mom j = 0)
    (Skin Scoord : Finset (Fin 163))
    (hSkin : ∀ j ∉ Skin, D.kinetic j = 0) (hScoord : ∀ j ∉ Scoord, D.coord j = 0)
    (hkin : ∀ j ∈ Skin, ∀ x : polyGaussCore (d := 163),
      ‖((smKinetic j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hcoord : ∀ j ∈ Scoord, ∀ x : polyGaussCore (d := 163),
      ‖((smPos j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hmass : ∀ x : polyGaussCore (d := 163),
      ‖((x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ c * ‖N x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (f : SmCoupledCore) :
    ‖smNormalForm D f‖
      ≤ c * normalFormConst D * ‖coupledOp N 1 f + (f : SmCoupledSpace)‖ := by
  have hc0 : (0 : ℝ) ≤ c := le_trans (by norm_num) hc
  refine smNormalForm_norm_le_support D N hc0 (Finset.image smMomCoordFin Finset.univ)
    Skin Scoord hSmom hSkin hScoord ?_ hkin hcoord hmass f
  intro j hj x
  obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hj
  refine (smMom_norm_le_shift_of_kineticSum N hc0 hpos hKin m x).trans ?_
  exact mul_le_mul_of_nonneg_right (sqrt_le_self_of_one_le hc) (norm_nonneg _)

end

end BookProof.SmKineticElliptic
