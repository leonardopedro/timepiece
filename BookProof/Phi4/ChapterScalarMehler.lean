import BookProof.Sm.ChapterSmFockEsa
import BookProof.Toolbox.ChapterFockStatisticsCompletion
import BookProof.Toolbox.ChapterEsaClosure
import BookProof.Toolbox.ChapterHermiteProductBasis

/-!
# A real scalar quartic on the Mehler core

A single outer quantum carries all the inner coordinates. The scalar model `jetModel`
acts on continuous field and jet variables. Its Mehler indices enumerate Hermite functions.
`siteModel` is a separate lattice comparison whose gradient uses periodic differences
when instantiated with `periodicNext`. Both reuse the bosonic SM closure and outer lift.
-/
namespace BookProof.Phi4

open MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsHermite
open BookProof.YangMillsFriedrichs BookProof.YangMillsNonAbelianEsa
open BookProof.FriedrichsExtension BookProof.TensorCore BookProof.SecondQuantizationCore
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.ChapterStoneResolvent

noncomputable section

structure Parameters where
  coupling : ℝ
  coupling_pos : 0 < coupling
  vev : ℝ
  vev_pos : 0 < vev

/-- A scalar Mehler Hamiltonian in the half-sum-of-squares normalization. -/
structure Model (d k r : ℕ) where
  momentum : Fin k → Fin d
  distinct : Function.Injective momentum
  form : Fin r → MvPolynomial (Fin d) ℂ
  real_form : ∀ j, RealCoeff (form j)

def wall {d : ℕ} (s : Fin d) (scale offset : ℝ) : MvPolynomial (Fin d) ℂ :=
  (scale : ℂ) • (X s * X s - C (offset : ℂ))

theorem real_wall {d : ℕ} (s : Fin d) (scale offset : ℝ) : RealCoeff (wall s scale offset) :=
  RealCoeff.smul (SmHamiltonian.RealCoeff.sub' ((realCoeff_X s).mul (realCoeff_X s))
    (SmHamiltonian.realCoeff_C_real offset))

/-- Unit-volume local model. Coordinate zero is the scalar, the other three are jets. -/
def jetModel (p : Parameters) : Model 4 1 4 where
  momentum := fun _ => 0
  distinct := fun _ _ _ => Subsingleton.elim _ _
  form := Fin.cases (wall 0 (Real.sqrt (p.coupling / 2)) (p.vev ^ 2)) (fun i => X i.succ)
  real_form := Fin.cases (real_wall ..) (fun i => realCoeff_X i.succ)

/-- Four forms per site: the wall, followed by the three forward links. -/
def siteForm {m : ℕ} (next : Fin m → Fin 3 → Fin m) (p : Parameters) (a : ℝ)
    (site : Fin m) : Fin 4 → MvPolynomial (Fin m) ℂ :=
  Fin.cases (wall site (Real.sqrt (p.coupling / (2 * a ^ 3))) (a ^ 3 * p.vev ^ 2))
    (fun r => ((a⁻¹ : ℝ) : ℂ) • (X (next site r) - X site))

def siteModel {m : ℕ} (next : Fin m → Fin 3 → Fin m) (p : Parameters)
    (a : ℝ) (_ha : 0 < a) : Model m m (m * 4) where
  momentum := id
  distinct := Function.injective_id
  form := fun j => let ij := finProdFinEquiv.symm j; siteForm next p a ij.1 ij.2
  real_form := by
    intro j
    let ij : Fin m × Fin 4 := finProdFinEquiv.symm j
    change RealCoeff (siteForm next p a ij.1 ij.2)
    exact Fin.cases (motive := fun i => RealCoeff (siteForm next p a ij.1 i))
      (real_wall ..) (fun _ => RealCoeff.smul
        (SmHamiltonian.RealCoeff.sub' (realCoeff_X _) (realCoeff_X _))) ij.2

/-- A rectangular periodic cell with nonempty sides of lengths nx+1, ny+1, nz+1. -/
def periodicNext (nx ny nz : ℕ) (site : Fin ((nx+1) * ((ny+1) * (nz+1)))) (r : Fin 3) :
    Fin ((nx+1) * ((ny+1) * (nz+1))) :=
  let (x, yz) := finProdFinEquiv.symm site
  let (y, z) := finProdFinEquiv.symm yz
  let pack := fun x' y' z' => finProdFinEquiv (x', finProdFinEquiv (y', z'))
  ![pack (x+1) y z, pack x (y+1) z, pack x y (z+1)] r

theorem site_wall_energy (p : Parameters) {a : ℝ} (ha : 0 < a) (q : ℝ) :
    (Real.sqrt (p.coupling / (2 * a^3)) * (q^2 - a^3 * p.vev^2))^2 / 2 =
      p.coupling / (4 * a^3) * (q^2 - a^3 * p.vev^2)^2 := by
  have hp := p.coupling_pos
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

namespace Model

variable {d k r : ℕ} (M : Model d k r)

def innerHam := weylPoly M.momentum M.form

/-- Column action before any occupation projection. Both applications of each ladder word
take place on the polynomial core. -/
theorem innerHam_pgLp (p : MvPolynomial (Fin d) ℂ) :
    M.innerHam ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (((1/2 : ℝ) : ℂ) •
      ((∑ i, momOp (M.momentum i) (momOp (M.momentum i) p)) +
        ∑ j, M.form j * (M.form j * p))) := by
  simp only [innerHam, weylPoly, weylOp_apply, op_pgLp_d, mulOp_apply]
  change _ = pgMap _
  rw [map_smul, map_add, map_sum, map_sum]
  rfl

private theorem mom_sym (i : Fin k) :
    SymmetricOn polyGaussCore (polyGaussCore.subtype.comp
      ((coreRepPoly d).op (momOp (M.momentum i)))) :=
  (coreRepPoly d).symmetricOn_op (momOp_polySym _)

private theorem field_sym (i : Fin r) :
    SymmetricOn polyGaussCore (polyGaussCore.subtype.comp
      ((coreRepPoly d).op (mulOp (M.form i)))) :=
  (coreRepPoly d).symmetricOn_op (mulOp_polySym (M.real_form i))

theorem symmetric : SymmetricOn polyGaussCore M.innerHam :=
  weylOpDom_symmetricOn M.mom_sym M.field_sym

theorem nonneg (x : polyGaussCore (d := d)) : 0 ≤ quadForm M.innerHam x :=
  weylOpDom_quadForm_nonneg M.mom_sym M.field_sym x

theorem inner_esa : EssentiallySelfAdjointOn polyGaussCore M.innerHam :=
  weylPoly_esa M.distinct M.real_form

theorem positive_extension :
    ∃ (D : Submodule ℂ (L2d d)) (A : D →ₗ[ℂ] L2d d), IsPositiveSelfAdjointExtension M.innerHam A :=
  friedrichs_extension_exists_of_complete_explicit
    ⟨polyGaussCore, M.innerHam, M.symmetric, M.nonneg⟩ polyGaussCore_dense

open EsaClosure HashimotoShiftInvert HermiteGalerkin Filter Topology FockStatistics

theorem closure_nonneg (x : clDom M.innerHam) :
    0 ≤ quadForm (clExt M.innerHam polyGaussCore_dense M.symmetric) x := by
  obtain ⟨D, A, hA⟩ := M.positive_extension
  obtain ⟨hD, hval⟩ := positiveExtension_eq_closure_of_esa polyGaussCore_dense M.symmetric
    M.inner_esa hA
  have hx : (x : L2d d) ∈ D := hD.symm ▸ x.property
  have h := hA.2.2.1 ⟨x, hx⟩
  simpa only [quadForm, hval x hx x.property] using h

theorem inner_flow :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension M.innerHam T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense M.symmetric M.inner_esa

/-- Actual complex-shift resolvents of the scalar extension, rational Krylov denominator
identity and strong convergence of compressions of those resolvents on the Mehler core basis. -/
theorem mehler_sirk (e : ℕ ≃ (Fin d →₀ ℕ)) (z : ℕ → ℂ) (hz : ∀ j, (z j).im ≠ 0) :
    ∃ (D : Submodule ℂ (L2d d)) (A : D →ₗ[ℂ] L2d d) (R : ℕ → L2d d →L[ℂ] L2d d),
      IsSelfAdjointExtension M.innerHam A ∧ (∀ j, IsShiftInvertC A (z j) (R j)) ∧
      (∀ j, ‖R j‖ ≤ |(z j).im|⁻¹) ∧
      (∀ m v n, sirkDen (R m) (fun i => z m - z i) n (rkVec R v n) = (R m ^ n) v) ∧
      (∀ j u, Tendsto (fun n => galerkinCompression (R j) (coreBasis e) n u)
        atTop (nhds (R j u))) := by
  obtain ⟨D, A, R, hext, hR, hnorm, _, _, _, _, hden, hlim, _⟩ :=
    hashimoto_multishift_selects_esa (coreBasis e) M.innerHam polyGaussCore_dense M.symmetric
      M.inner_esa z hz
  exact ⟨D, A, R, hext, hR, hnorm, hden, hlim⟩

/-- The Hilbert direct sum of completed *symmetric* tensor sectors. -/
def outerHam := hbosonicFockOp (L2dSpace d) polyGaussCore M.innerHam

theorem outer_esa : EssentiallySelfAdjointOn _ M.outerHam :=
  hbosonicFock_esa (Hs := L2dSpace d) M.innerHam polyGaussCore_dense M.symmetric M.inner_esa

end Model

open HermiteProductBasis

theorem coordinate_ladders {d : ℕ} (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulOp (X j) p = crePoly j p + annPoly j p := by
  simp

theorem momentum_ladders {d : ℕ} (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j p = (Complex.I / 2) • (crePoly j p - annPoly j p) := by
  simp only [momOp_apply, crePoly_apply, annPoly_apply, smul_eq_C_mul]
  apply MvPolynomial.funext
  intro y
  simp
  ring

/-- On the common polynomial core this gives i times the identity for equal sites
and zero for distinct sites. -/
theorem coordinate_momentum_commutator {d : ℕ} (i j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulOp (X i) (momOp j p) - momOp j (mulOp (X i) p) =
      (if i = j then Complex.I else 0) • p := by
  simp only [mulOp_apply, momOp_apply, Derivation.leibniz, smul_eq_mul, smul_eq_C_mul]
  by_cases h : i = j
  · subst i
    simp
    ring
  · simp [h, pderiv_X_of_ne h]
    ring

def unitCell : Model 1 1 (1*4) :=
  siteModel (periodicNext 0 0 0) ⟨1, by norm_num, 1, by norm_num⟩ 1 (by norm_num)

/-- The three periodic differences in the single cell vanish. The remaining squared form
is one half of (x²−1)² before the overall factor 1/2 in h. -/
private theorem unitCell_forms (p : MvPolynomial (Fin 1) ℂ) :
    ∑ j, unitCell.form j * (unitCell.form j * p) =
      C (1/2 : ℂ) * (X 0 ^ 2 - 1)^2 * p := by
  have hs : (Real.sqrt (1/2) : ℂ)^2 = 1/2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  let x : MvPolynomial (Fin 1) ℂ := X 0
  let t := C (Real.sqrt (1/2) : ℂ) * (x*x-1)
  have hw : unitCell.form 0 = t := by
    change wall (0 : Fin 1) _ _ = _
    simp [wall, t, x, smul_eq_C_mul]
  have hz (i : Fin 3) : unitCell.form i.succ = 0 := by
    have hnext (j : Fin 3) : periodicNext 0 0 0 0 j = 0 :=
      Fin.eq_zero _
    fin_cases i <;> change ((_ : ℝ) : ℂ) • (X (periodicNext 0 0 0 0 _) - X 0) = 0 <;>
      rw [hnext, sub_self, smul_zero]
  change (∑ j : Fin 4, _) = _
  rw [Fin.sum_univ_succ, hw]
  simp only [hz, zero_mul, Finset.sum_const_zero, add_zero]
  dsimp [t, x]
  apply MvPolynomial.funext
  intro y
  simp only [map_mul, map_sub, map_one, map_pow, eval_C, eval_X]
  linear_combination (y 0 * y 0 - 1)^2 * eval y p * hs

/-- Full one-site vacuum column in the unnormalized probabilists' Hermite basis.
The three summands are He₀, He₂ and He₄ with their measured coefficients. -/
theorem unitCell_vacuum_column :
    unitCell.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ =
      pgLp (C (5/8 : ℂ) + C (7/8 : ℂ) * (X 0 ^ 2 - 1)
        + C (1/4 : ℂ) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3)) := by
  rw [Model.innerHam_pgLp, unitCell_forms, Fin.sum_univ_one]
  congr 1
  change _ • (momOp 0 (momOp 0 1) + _) = _
  rw [momOp_momOp_d]
  simp [QgHermiteFriedrichs.coreD, smul_eq_C_mul, Derivation.leibniz]
  apply MvPolynomial.funext
  intro y
  simp
  ring

/-- Squared full residual of the normalized vacuum column in the rank-one window.
The factors 2! and 4! convert the probabilists’ Hermites to normalized coefficients. -/
theorem vacuum_residual_squared :
    (7/8 : ℝ)^2 * Nat.factorial 2 + (1/4 : ℝ)^2 * Nat.factorial 4 = 97/32 := by
  norm_num [Nat.factorial]

/-- Exact inverse compression in the one-column occupation window. -/
theorem vacuum_window_generator (γ : ℝ) :
    (γ : ℂ) - ((1 / ((γ : ℂ) + Complex.I * (5/8)))⁻¹) = -Complex.I * (5/8) := by
  simp only [one_div, inv_inv]
  ring

/-- Under orthonormal two-site mixing the local quartic contains a mixed term. -/
theorem two_site_vertex (u w : ℝ) :
    ((u+w) / Real.sqrt 2)^4 + ((u-w) / Real.sqrt 2)^4 =
      (u^4 + 6*u^2*w^2 + w^4)/2 := by
  have hs : (Real.sqrt 2)^4 = 4 := by
    rw [show (4 : ℕ) = 2*2 by decide, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [div_pow, div_pow, hs]
  ring

end
end BookProof.Phi4
