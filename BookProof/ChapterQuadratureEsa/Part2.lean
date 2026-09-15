import Mathlib
import BookProof.ChapterHermiteRelativeBound
import BookProof.ChapterNavierStokesSignFlip
import BookProof.ChapterStoneBridge
import BookProof.ChapterQuadratureEsa.Part1

/-!
# The quadrature operator `∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` on the Hermite core

`BookProof.ChapterHermiteRelativeBound` proves that the first-order operator
`B = ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` (`foOp b b'`) is symmetric on the Gauss–polynomial
(product Hermite) core of `L²(ℝᵈ)`, and that `H_c + B` is essentially self-adjoint
whenever the quadratic part `H_c` is *elliptic*.  The shifted-core modules
(`ChapterShiftedQuadraticEsa`, `ChapterShiftedQuadraticMatrixEsa`,
`ChapterShiftedQuadraticDegenerate`) remove the sign and the invertibility
conditions by completing the square, but need a classical equilibrium — which does
not exist in a kernel direction carrying both a linear potential `bᵢxᵢ` and a
momentum term `b'ᵢπᵢ`.  There the operator has no quadratic part at all, and the
two routes used elsewhere both fail: it has no `L²` eigenvector (so the
Hermite-eigenbasis argument does not see it) and it is not constant-coefficient
(so the Fourier-multiplier argument does not see it either).
`BookProof.ChapterMixedLinearEsa` settles that operator on the **Schwartz** core, by
a quadratic gauge.  This module settles it on the **Gauss–polynomial core** — the
core the whole quadratic family lives on — by the metaplectic rotation, which on
that core is nothing but a phase.

## What is proved

* `fourier_eq_zero_of_moments`, `ae_eq_zero_of_moments'` — **a moment lemma without
  an `L²` hypothesis**: a function all of whose exponentially weighted moments are
  finite and all of whose polynomial moments vanish is zero almost everywhere.
  This strengthens `BookProof.HermiteProductCore.ae_eq_zero_of_moments`, which
  needs the function to be a Gaussian times an `L²` function, and is what lets the
  deficiency equation of a *multiplication* operator be treated on the
  Gauss–polynomial core (there the natural function is `e^{-‖x‖²/4}(ℓ − z)u`, which
  is not of that shape);
* `foOp_pos_deficiencyTrivialAt`, `foOp_pos_essentiallySelfAdjoint` — multiplication
  by the real linear function `x ↦ ⟪x, b⟫` is essentially self-adjoint on the core;
* `phaseBasis`, `phaseU`, `phaseU_hermiteMvLp` — **the instrument**: a unimodular
  multiplier on a Hilbert basis is a unitary of the space, sending each basis vector
  to its phase multiple;
* `posL_hermiteCore`, `momL_hermiteCore`, `foOp_hermiteCore` — the ladder form of the
  canonical pair on the product Hermite basis: the quadrature raises the `i`-th
  excitation number with amplitude `wᵢ = bᵢ + ib'ᵢ/2` and lowers it with `conj wᵢ`;
* `phaseU_foOp_hermiteCore` — the phase unitary rotates the canonical pair: it carries
  `foOp r 0` onto `foOp b b'` when `ζᵢ = wᵢ/|wᵢ|`, `rᵢ = |wᵢ|`.  This is the metaplectic
  rotation `e^{iθ·N}`, realized diagonally on the Hermite basis;
* HEADLINE `foOp_essentiallySelfAdjoint` — for **arbitrary** real coefficients
  `b, b'` the quadrature `∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝᵈ)`, and `foOp_stone_flow` turns that into a
  complete unitary flow.

A reusable by-product is `linearMap_ext_of_span`: two linear maps out of a submodule
spanned by a family agree as soon as they agree on that family.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.QuadratureEsa

open MeasureTheory MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.YangMillsHermite
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

variable {d : ℕ}
/-! ### The core vector carried by a product Hermite function -/

/-- The normalized product Hermite function `ψ_α`, as an element of the core. -/
noncomputable def hermiteCore (a : Fin d →₀ ℕ) : polyGaussCore (d := d) :=
  coreEquiv (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a)

@[simp] theorem hermiteCore_coe (a : Fin d →₀ ℕ) :
    ((hermiteCore a : polyGaussCore (d := d)) : L2d d) = hermiteMvLp a := by
  rw [hermiteCore, coreEquiv_coe, pgLp_smul, hermiteMvLp]

theorem hermiteCore_eq (a : Fin d →₀ ℕ) (h : hermiteMvLp (d := d) a ∈ polyGaussCore (d := d)) :
    (⟨hermiteMvLp a, h⟩ : polyGaussCore (d := d)) = hermiteCore a :=
  Subtype.ext (hermiteCore_coe a).symm

/-! ### The canonical pair in terms of the ladder operators -/

theorem pgLp_add' (p q : MvPolynomial (Fin d) ℂ) : pgLp (p + q) = pgLp p + pgLp q :=
  map_add (pgMap (d := d)) p q

theorem pgLp_sub' (p q : MvPolynomial (Fin d) ℂ) : pgLp (p - q) = pgLp p - pgLp q :=
  map_sub (pgMap (d := d)) p q

/-- `xᵢ = aᵢ + a†ᵢ`, on polynomial coordinates. -/
theorem mulXPoly_eq_cre_add_ann (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulXPoly i p = crePoly i p + annPoly i p := by
  simp

/-- `πᵢ = (i/2)(a†ᵢ − aᵢ)`, on polynomial coordinates. -/
theorem momPoly_eq_cre_sub_ann (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = (Complex.I / 2) • (crePoly i p - annPoly i p) := by
  simp only [momPoly_apply, crePoly_apply, annPoly_apply, ← MvPolynomial.smul_eq_C_mul]
  module

theorem posL_coe (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    posL i (coreEquiv p) = pgLp (mulXPoly i p) := coreOp_coe _ p

theorem momL_coe (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momL i (coreEquiv p) = pgLp (momPoly i p) := coreOp_coe _ p

/-- **The position operator on a product Hermite function**: `xᵢψ_α = √(αᵢ+1)ψ_{α+eᵢ} +
√αᵢ ψ_{α−eᵢ}`. -/
theorem posL_hermiteCore (i : Fin d) (a : Fin d →₀ ℕ) :
    posL i (hermiteCore a)
      = ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (a + Finsupp.single i 1)
        + ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (a - Finsupp.single i 1) := by
  rw [hermiteCore, posL_coe, map_smul, mulXPoly_eq_cre_add_ann, smul_add, pgLp_add', pgLp_smul,
    pgLp_smul, crePoly_hermiteMvLp, annPoly_hermiteMvLp]

/-- **The momentum operator on a product Hermite function**: `πᵢψ_α =
(i/2)(√(αᵢ+1)ψ_{α+eᵢ} − √αᵢ ψ_{α−eᵢ})`. -/
theorem momL_hermiteCore (i : Fin d) (a : Fin d →₀ ℕ) :
    momL i (hermiteCore a)
      = (Complex.I / 2) •
          (((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (a + Finsupp.single i 1)
            - ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (a - Finsupp.single i 1)) := by
  rw [hermiteCore, momL_coe, map_smul, momPoly_eq_cre_sub_ann, smul_comm, smul_sub, pgLp_smul,
    pgLp_sub', pgLp_smul, pgLp_smul, crePoly_hermiteMvLp, annPoly_hermiteMvLp]

/-! ### The complex amplitude of a quadrature -/

/-- The complex amplitude `wᵢ = bᵢ + i b'ᵢ/2` of the quadrature `bᵢxᵢ + b'ᵢπᵢ`: it is the
coefficient with which the quadrature raises the `i`-th excitation number. -/
noncomputable def foAmp (b b' : Fin d → ℝ) (i : Fin d) : ℂ :=
  ((b i : ℝ) : ℂ) + Complex.I * ((b' i : ℝ) : ℂ) / 2

theorem foAmp_real (r : Fin d → ℝ) (i : Fin d) : foAmp r 0 i = ((r i : ℝ) : ℂ) := by
  simp [foAmp]

theorem conj_foAmp (b b' : Fin d → ℝ) (i : Fin d) :
    (starRingEnd ℂ) (foAmp b b' i) = ((b i : ℝ) : ℂ) - Complex.I * ((b' i : ℝ) : ℂ) / 2 := by
  simp only [foAmp, map_add, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- **The quadrature on a product Hermite function.** -/
theorem foOp_hermiteCore (b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    foOp b b' (hermiteCore a)
      = ∑ i, ((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ))
                • hermiteMvLp (a + Finsupp.single i 1)
              + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ))
                • hermiteMvLp (a - Finsupp.single i 1)) := by
  rw [foOp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [posL_hermiteCore, momL_hermiteCore, conj_foAmp, foAmp]
  module

/-- The modulus of the amplitude: the coefficient of the rotated, purely positional,
quadrature. -/
noncomputable def foMod (b b' : Fin d → ℝ) (i : Fin d) : ℝ := ‖foAmp b b' i‖

/-- The phase of the amplitude (set to `1` in a direction where the quadrature is absent). -/
noncomputable def foPhase (b b' : Fin d → ℝ) (i : Fin d) : ℂ :=
  if foAmp b b' i = 0 then 1 else foAmp b b' i / ((foMod b b' i : ℝ) : ℂ)

theorem norm_foPhase (b b' : Fin d → ℝ) (i : Fin d) : ‖foPhase b b' i‖ = 1 := by
  rw [foPhase]
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, foMod, abs_norm,
      div_self (norm_ne_zero_iff.mpr h)]

/-- **Polar decomposition of the amplitude**: `wᵢ = |wᵢ| ζᵢ`. -/
theorem foMod_mul_foPhase (b b' : Fin d → ℝ) (i : Fin d) :
    ((foMod b b' i : ℝ) : ℂ) * foPhase b b' i = foAmp b b' i := by
  rw [foPhase]
  split_ifs with h
  · rw [h, mul_one]
    simp [foMod, h]
  · have hne : ((foMod b b' i : ℝ) : ℂ) ≠ 0 := by
      simpa [foMod, Complex.ofReal_eq_zero] using h
    field_simp

/-- The conjugate polar identity `|wᵢ| = conj(wᵢ) ζᵢ`, which is what makes the *lowering*
coefficient rotate the right way. -/
theorem foMod_eq_conj_mul_foPhase (b b' : Fin d → ℝ) (i : Fin d) :
    ((foMod b b' i : ℝ) : ℂ) = (starRingEnd ℂ) (foAmp b b' i) * foPhase b b' i := by
  have hpolar := foMod_mul_foPhase b b' i
  have hconj := congrArg (starRingEnd ℂ) hpolar
  rw [map_mul, Complex.conj_ofReal] at hconj
  calc ((foMod b b' i : ℝ) : ℂ)
      = ((foMod b b' i : ℝ) : ℂ) * ((starRingEnd ℂ) (foPhase b b' i) * foPhase b b' i) := by
        rw [conj_mul_self_of_norm_one (norm_foPhase b b' i), mul_one]
    _ = (starRingEnd ℂ) (foAmp b b' i) * foPhase b b' i := by
        rw [← mul_assoc, hconj]

/-! ### The diagonal phase unitary -/

/-- The multi-index power `ζ^α = ∏ᵢ ζᵢ^{αᵢ}`. -/
noncomputable def phasePow (zeta : Fin d → ℂ) (a : Fin d →₀ ℕ) : ℂ := ∏ i, zeta i ^ (a i)

theorem norm_phasePow (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) (a : Fin d →₀ ℕ) :
    ‖phasePow zeta a‖ = 1 := by
  rw [phasePow, norm_prod]
  exact Finset.prod_eq_one fun i _ => by rw [norm_pow, hzn i, one_pow]

theorem phasePow_ne_zero (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) (a : Fin d →₀ ℕ) :
    phasePow zeta a ≠ 0 := by
  intro h
  have := norm_phasePow zeta hzn a
  rw [h] at this
  simp at this

theorem phasePow_add_single (zeta : Fin d → ℂ) (i : Fin d) (a : Fin d →₀ ℕ) :
    phasePow zeta (a + Finsupp.single i 1) = phasePow zeta a * zeta i := by
  classical
  have h : ∀ j : Fin d, zeta j ^ ((a + Finsupp.single i 1 : Fin d →₀ ℕ) j)
      = zeta j ^ (a j) * (if j = i then zeta i else 1) := by
    intro j
    have hj : ((a + Finsupp.single i 1 : Fin d →₀ ℕ) j) = a j + (if j = i then 1 else 0) := by
      simp [Finsupp.single_apply, eq_comm]
    rw [hj, pow_add]
    split_ifs with hji
    · rw [hji, pow_one]
    · rw [pow_zero]
  rw [phasePow, phasePow, Finset.prod_congr rfl fun j _ => h j, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i (fun _ => zeta i)]
  simp

theorem phasePow_sub_single (zeta : Fin d → ℂ) {i : Fin d} {a : Fin d →₀ ℕ} (ha : 0 < a i) :
    phasePow zeta (a - Finsupp.single i 1) * zeta i = phasePow zeta a := by
  classical
  have h : ∀ j : Fin d, zeta j ^ ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j)
      * (if j = i then zeta i else 1) = zeta j ^ (a j) := by
    intro j
    have hj : ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j) = a j - (if j = i then 1 else 0) := by
      simp [Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]
    rw [hj]
    split_ifs with hji
    · subst hji
      rw [← pow_succ]
      congr 1
      omega
    · rw [mul_one, Nat.sub_zero]
  rw [phasePow, phasePow, ← Finset.prod_congr rfl fun j _ => h j, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i (fun _ => zeta i)]
  simp

/-- The phase-rotated product Hermite family `ζ^α ψ_α`. -/
noncomputable def phaseFamily (zeta : Fin d → ℂ) (a : Fin d →₀ ℕ) : L2d d :=
  phasePow zeta a • hermiteMvLp a

theorem orthonormal_phaseFamily (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) :
    Orthonormal ℂ (phaseFamily (d := d) zeta) := by
  classical
  rw [orthonormal_iff_ite]
  intro a c
  rw [phaseFamily, phaseFamily, inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp (orthonormal_hermiteMvLp (d := d)) a c]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, mul_one, conj_mul_self_of_norm_one (norm_phasePow zeta hzn a)]
  · rw [if_neg hac, mul_zero, mul_zero]

theorem span_phaseFamily (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) :
    Submodule.span ℂ (Set.range (phaseFamily (d := d) zeta)) = polyGaussCore (d := d) := by
  rw [← span_hermiteMvLp]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hrw : hermiteMvLp (d := d) a = (phasePow zeta a)⁻¹ • phaseFamily zeta a := by
      rw [phaseFamily, smul_smul, inv_mul_cancel₀ (phasePow_ne_zero zeta hzn a), one_smul]
    change hermiteMvLp (d := d) a ∈ Submodule.span ℂ (Set.range (phaseFamily (d := d) zeta))
    rw [hrw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- The phase-rotated product Hermite functions are again a Hilbert basis. -/
noncomputable def phaseBasis (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) :
    HilbertBasis (Fin d →₀ ℕ) ℂ (L2d d) :=
  HilbertBasis.mk (orthonormal_phaseFamily zeta hzn)
    (by
      rw [span_phaseFamily zeta hzn]
      have hd := polyGaussCore_dense (d := d)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])

/-- **The phase unitary**: the unitary of `L²(ℝᵈ)` which multiplies the `α`-th product
Hermite function by `ζ^α`.  For `ζᵢ = e^{iθᵢ}` this is the metaplectic rotation
`e^{iθ·N}` generated by the number operators. -/
noncomputable def phaseU (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) : L2d d ≃ₗᵢ[ℂ] L2d d :=
  (hermiteMvBasis (d := d)).repr.trans (phaseBasis zeta hzn).repr.symm

theorem phaseU_hermiteMvLp (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) (a : Fin d →₀ ℕ) :
    phaseU zeta hzn (hermiteMvLp (d := d) a) = phasePow zeta a • hermiteMvLp a := by
  classical
  have h1 : (hermiteMvBasis (d := d)).repr (hermiteMvLp a) = lp.single 2 a 1 := by
    rw [← hermiteMvBasis_apply]
    exact HilbertBasis.repr_self _ a
  have h2 : (phaseBasis (d := d) zeta hzn).repr.symm (lp.single 2 a 1)
      = phaseFamily (d := d) zeta a := by
    rw [HilbertBasis.repr_symm_single, phaseBasis, HilbertBasis.coe_mk]
  rw [phaseU, LinearIsometryEquiv.trans_apply, h1, h2, phaseFamily]

theorem phaseU_mem_core (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1)
    (v : polyGaussCore (d := d)) :
    phaseU zeta hzn (v : L2d d) ∈ polyGaussCore (d := d) := by
  have main : ∀ y : L2d d, y ∈ Submodule.span ℂ (Set.range (hermiteMvLp (d := d))) →
      phaseU zeta hzn y ∈ polyGaussCore (d := d) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        rw [phaseU_hermiteMvLp]
        exact Submodule.smul_mem _ _ (hermiteMvLp_mem_core a)
    | zero => simp
    | add z w _ _ ihz ihw =>
        rw [map_add]
        exact Submodule.add_mem _ ihz ihw
    | smul r z _ ih =>
        rw [map_smul]
        exact Submodule.smul_mem _ _ ih
  exact main (v : L2d d) (by rw [span_hermiteMvLp]; exact v.2)

/-- The phase unitary, as an operator of the core. -/
noncomputable def phaseCore (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) :
    polyGaussCore (d := d) →ₗ[ℂ] polyGaussCore (d := d) where
  toFun v := ⟨phaseU zeta hzn (v : L2d d), phaseU_mem_core zeta hzn v⟩
  map_add' u v := Subtype.ext (by simp)
  map_smul' c v := Subtype.ext (by simp)

@[simp] theorem phaseCore_coe (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1)
    (v : polyGaussCore (d := d)) :
    ((phaseCore zeta hzn v : polyGaussCore (d := d)) : L2d d) = phaseU zeta hzn (v : L2d d) := rfl

/-! ### The rotation of the quadrature -/

set_option maxHeartbeats 1600000 in
-- the core coercions make the elaboration of this one identity expensive
/-- **The phase unitary rotates the quadrature**: on a product Hermite function it carries
the positional quadrature `∑ᵢ|wᵢ|xᵢ` onto `∑ᵢ(bᵢxᵢ + b'ᵢπᵢ)`. -/
theorem phaseU_foOp_hermiteCore (b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    phaseU (foPhase b b') (norm_foPhase b b') (foOp (foMod b b') 0 (hermiteCore a))
      = foOp b b' (phaseCore (foPhase b b') (norm_foPhase b b') (hermiteCore a)) := by
  classical
  have hpc : phaseCore (foPhase b b') (norm_foPhase b b') (hermiteCore a)
      = phasePow (foPhase b b') a • hermiteCore a := by
    refine Subtype.ext ?_
    rw [phaseCore_coe, hermiteCore_coe, phaseU_hermiteMvLp, Submodule.coe_smul, hermiteCore_coe]
  rw [hpc, map_smul, foOp_hermiteCore, foOp_hermiteCore, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_smul, map_smul, phaseU_hermiteMvLp, phaseU_hermiteMvLp, smul_add,
    smul_smul, smul_smul, smul_smul, smul_smul, foAmp_real, Complex.conj_ofReal]
  have hup : ((foMod b b' i : ℝ) : ℂ) * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ)
      * phasePow (foPhase b b') (a + Finsupp.single i 1)
      = phasePow (foPhase b b') a * (foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ)) := by
    rw [phasePow_add_single, ← foMod_mul_foPhase b b' i]
    ring
  have hdown : ((foMod b b' i : ℝ) : ℂ) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ)
      * phasePow (foPhase b b') (a - Finsupp.single i 1)
      = phasePow (foPhase b b') a
        * ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ)) := by
    rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
    · have hs : ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) = 0 := by
        rw [h0]
        simp
      rw [hs]
      ring
    · rw [← phasePow_sub_single (foPhase b b') hpos]
      rw [foMod_eq_conj_mul_foPhase b b' i]
      ring
  rw [hup, hdown]

/-- **HEADLINE.**  For arbitrary real coefficients `b, b'` the quadrature
`∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially self-adjoint on the Gauss–polynomial (product Hermite)
core of `L²(ℝᵈ)`. -/
theorem foOp_essentiallySelfAdjoint (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (foOp b b') := by
  refine BookProof.NavierStokesFlow.SignFlip.essentiallySelfAdjointOn_of_intertwine
    (phaseU (foPhase b b') (norm_foPhase b b')) (foOp (foMod b b') 0) (foOp b b')
    (phaseU_mem_core _ _) ?_ (foOp_pos_essentiallySelfAdjoint (foMod b b'))
  have hEq :
      ((phaseU (foPhase b b') (norm_foPhase b b')).toLinearEquiv.toLinearMap
          ∘ₗ foOp (foMod b b') 0)
        = (foOp b b' ∘ₗ phaseCore (foPhase b b') (norm_foPhase b b')) := by
    refine linearMap_ext_of_span (hermiteMvLp (d := d)) span_hermiteMvLp hermiteMvLp_mem_core
      _ _ fun a => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hermiteCore_eq]
    exact phaseU_foOp_hermiteCore b b' a
  intro v
  exact congrArg (fun F : polyGaussCore (d := d) →ₗ[ℂ] L2d d => F v) hEq

/-- **The quadrature generates a complete unitary flow.**  Stone's theorem applied to the
closure of `∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`. -/
theorem foOp_stone_flow (b b' : Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (foOp b b') T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense (foOp_symmetric b b')
    (foOp_essentiallySelfAdjoint b b')

end BookProof.QuadratureEsa
