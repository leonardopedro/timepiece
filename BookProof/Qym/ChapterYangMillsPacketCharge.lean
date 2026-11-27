import BookProof.Qym.ChapterYangMillsHermite

/-! # The projected Gauss charge on finite Mehler packet amplitudes

For orthonormal real field packets the classical Gauss tangent has a translation
(the projection of the gradient of the gauge parameter) and a linear colour action.
The Weyl prescription below takes the projected coefficients as inputs. All polynomial
degrees share the same dense domain in amplitude space.
-/

namespace BookProof.YangMillsPacketCharge

open MvPolynomial BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.FarisLavine

noncomputable section

variable {d : ℕ}

abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℂ

/-- Component of the affine Gauss tangent in orthonormal packet coordinates. -/
def tangent (t : Fin d → ℝ) (m : Fin d → Fin d → ℝ) (j : Fin d) : Poly d :=
  C (t j : ℂ) + ∑ k, (m j k : ℂ) • X k

theorem tangent_real (t : Fin d → ℝ) (m : Fin d → Fin d → ℝ) (j : Fin d) :
    RealCoeff (tangent t m j) :=
  RealCoeff.add (by simp [RealCoeff]) (RealCoeff.sum fun k _ => (realCoeff_X k).smul)

/-- Sum of Weyl-ordered tangent times momentum on the polynomial factor. -/
def charge (t : Fin d → ℝ) (m : Fin d → Fin d → ℝ) : Module.End ℂ (Poly d) :=
  ∑ j, weylProd (mulOp (tangent t m j)) (momOp j)

private theorem polySym_sum {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ (Poly d))
    (h : ∀ i ∈ s, PolySym (f i)) : PolySym (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PolySym]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih (fun k hk => h k (by simp [hk])))

theorem charge_polySym (t : Fin d → ℝ) (m : Fin d → Fin d → ℝ) : PolySym (charge t m) :=
  polySym_sum _ _ fun j _ =>
    weylProd_polySym (mulOp_polySym (tangent_real t m j)) (momOp_polySym j)

/-- All projected charges preserve the common polynomial-Gaussian core and act
symmetrically in its ambient Hilbert space. -/
theorem charge_dense_symmetric (t : Fin d → ℝ) (m : Fin d → Fin d → ℝ) :
    Dense ((polyGaussCore (d := d)) : Set (L2d d)) ∧
    SymmetricOn polyGaussCore
      (polyGaussCore.subtype.comp ((coreRepPoly d).op (charge t m))) :=
  ⟨polyGaussCore_dense, (coreRepPoly d).symmetricOn_op (charge_polySym t m)⟩

private theorem momentum_product (j : Fin d) (f p : Poly d) :
    momOp j (f * p) = f * momOp j p + (-Complex.I) • (pderiv j f * p) := by
  simp only [momOp_apply, pderiv_mul, smul_eq_C_mul]
  ring

private theorem weyl_product (j : Fin d) (b f p : Poly d) :
    weylProd (mulOp b) (momOp j) (f * p) =
      f * weylProd (mulOp b) (momOp j) p + (-Complex.I) • (b * pderiv j f * p) := by
  simp only [weylProd, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    mulOp_apply]
  rw [mul_left_comm b f p, momentum_product j f p, momentum_product j f (b * p)]
  simp only [smul_eq_C_mul]
  push_cast
  have half : C (1 / 2 : ℂ) * (2 : Poly d) = 1 := by
    rw [show (2 : Poly d) = C (2 : ℂ) from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  linear_combination (b * C (-Complex.I) * pderiv j f * p) * half

/-- Commuting the charge with a coordinate reads back exactly the projected
Gauss tangent, including its inhomogeneous part. -/
theorem charge_coordinate (t : Fin d → ℝ) (m : Fin d → Fin d → ℝ) (k : Fin d) (p : Poly d) :
    charge t m (X k * p) - X k * charge t m p = (-Complex.I) • (tangent t m k * p) := by
  classical
  simp only [charge, LinearMap.sum_apply, weyl_product, Finset.sum_add_distrib, Finset.mul_sum,
    add_sub_cancel_left]
  simp [pderiv_X, Pi.single_apply, mul_ite, ite_mul]

/-- Weyl ordering contributes half the divergence. The Gaussian contributes
the term proportional to the packet coordinate, even for the constant polynomial. -/
private theorem weyl_vacuum (b : Poly d) (j : Fin d) :
    weylProd (mulOp b) (momOp j) 1 =
      (Complex.I / 2) • (X j * b - pderiv j b) := by
  simp only [weylProd, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    mulOp_apply, momOp_apply, pderiv_one, mul_one, zero_sub, smul_eq_C_mul]
  push_cast
  have half : C (1 / 2 : ℂ) * (2 : Poly d) = 1 := by
    rw [show (2 : Poly d) = C (2 : ℂ) from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  rw [show Complex.I / 2 = (1 / 2 : ℂ) * Complex.I by ring, map_mul, map_neg]
  linear_combination (C (1/2 : ℂ) * C Complex.I * X j * b) * half

private theorem tangent_deriv (t : Fin d → ℝ) (m : Fin d → Fin d → ℝ) (j : Fin d) :
    pderiv j (tangent t m j) = C (m j j : ℂ) := by
  classical
  simp [tangent, pderiv_X, Pi.single_apply,
    smul_eq_C_mul]

/-- Antisymmetry cancels every quadratic contribution in the Gaussian weight. -/
private theorem skew_quadratic (m : Fin d → Fin d → ℝ) (hm : ∀ j k, m j k = -m k j) :
    (∑ j, ∑ k, (C (m j k : ℂ) : Poly d) * X j * X k) = 0 := by
  let q : Poly d := ∑ j, ∑ k, C (m j k : ℂ) * X j * X k
  have h : q = -q := by
    unfold q
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    rw [hm j k, Complex.ofReal_neg, map_neg]
    ring
  exact CharZero.eq_neg_self_iff.mp h

/-- The inner Mehler vacuum is killed by rotations. A projected translation creates
a first-degree excitation. The outer Fock vacuum is a separate vector. -/
theorem charge_vacuum (t : Fin d → ℝ) (m : Fin d → Fin d → ℝ)
    (hm : ∀ j k, m j k = -m k j) :
    charge t m 1 = (Complex.I / 2) • (∑ j, C (t j : ℂ) * X j) := by
  classical
  have hd (j : Fin d) : m j j = 0 := by linarith [hm j j]
  simp only [charge, LinearMap.sum_apply, weyl_vacuum, tangent_deriv, hd, Complex.ofReal_zero,
    map_zero, sub_zero, ← Finset.smul_sum]
  congr 1
  simp only [tangent, mul_add, Finset.mul_sum, smul_eq_C_mul, Finset.sum_add_distrib]
  simp_rw [show ∀ j k : Fin d, X j * (C (m j k : ℂ) * X k) =
    C (m j k : ℂ) * X j * X k by intros; ring]
  rw [skew_quadratic m hm, add_zero]
  apply Finset.sum_congr rfl
  intros
  ring

section SchwartzCoefficients

open MeasureTheory SchwartzMap LineDeriv

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Profile := 𝓢(Space, ℝ)
abbrev Packets (d colours : ℕ) := Fin d → Fin 3 → Fin colours → Profile

private def product (u v : Profile) : Profile :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) u v

/-- L² pairing with the gradient of a local gauge parameter in physical space. -/
def translation {colours : ℕ} (e : Packets d colours) (ω : Fin colours → Profile)
    (j : Fin d) : ℝ :=
  ∑ l, ∑ a, ∫ x, product (e j l a) (∂_{EuclideanSpace.single l (1 : ℝ)} (ω a)) x

private def overlap (u v w : Profile) : ℝ := ∫ x, product (product u v) w x

private theorem overlap_swap (u v w : Profile) : overlap u v w = overlap v u w := by
  unfold overlap
  apply integral_congr_ae
  filter_upwards with x
  change u x * v x * w x = v x * u x * w x
  ring

/-- Continuous field overlaps. With orthonormal packets these are the entries of
the orthogonal compression of A ↦ g[A,ω]. Every integrand is a Schwartz function. -/
def rotation {n : ℕ} (e : Packets d n) (ω : Fin n → Profile) (g : ℝ)
    (f : Fin n → Fin n → Fin n → ℝ) (j k : Fin d) : ℝ :=
  ∑ l, ∑ a, ∑ b, ∑ c, g * f a b c * overlap (e j l a) (e k l b) (ω c)

theorem rotation_skew {n : ℕ} (e : Packets d n) (ω : Fin n → Profile) (g : ℝ)
    (f : Fin n → Fin n → Fin n → ℝ) (hf : ∀ a b c, f a b c = -f b a c)
    (j k : Fin d) : rotation e ω g f j k = -rotation e ω g f k j := by
  unfold rotation
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  rw [hf a b c, overlap_swap (e j l a)]
  ring

/-- A local charge acting on the Gaussian responds only to the projected gradient. -/
theorem local_charge_vacuum {n : ℕ} (e : Packets d n) (ω : Fin n → Profile) (g : ℝ)
    (f : Fin n → Fin n → Fin n → ℝ) (hf : ∀ a b c, f a b c = -f b a c) :
    charge (translation e ω) (rotation e ω g f) 1 =
      (Complex.I / 2) • (∑ j, C (translation e ω j : ℂ) * X j) :=
  charge_vacuum _ _ (rotation_skew e ω g f hf)

/-- Gauge test obtained by multiplying the spatial packet by a linear coordinate. -/
def matchedParameter (a : Space →L[ℝ] ℝ) (f : Profile) : Profile :=
  smulLeftCLM ℝ a f

private theorem matched_apply (a : Space →L[ℝ] ℝ) (f : Profile) (x : Space) :
    matchedParameter a f x = a x * f x :=
  smulLeftCLM_apply_apply (by fun_prop) f x

/-- Integration by parts prices the gauge gradient on the raw field amplitude:
the linear coordinate contributes half its slope times the packet metric. -/
theorem matched_gradient (a : Space →L[ℝ] ℝ) (f : Profile) (v : Space) :
    (∫ x, f x * ∂_{v} (matchedParameter a f) x) = a v * (∫ x, f x ^ 2) / 2 := by
  let w := matchedParameter a f
  have hw : (w : Space → ℝ) = fun x => a x * f x := funext (matched_apply a f)
  have hd (x : Space) : ∂_{v} w x = a v * f x + a x * ∂_{v} f x := by
    rw [lineDerivOp_apply_eq_fderiv, hw]
    change fderiv ℝ ((a : Space → ℝ) * (f : Space → ℝ)) x v = _
    rw [(a.hasFDerivAt.mul (f.hasFDerivAt x)).fderiv]
    simp [lineDerivOp_apply_eq_fderiv, add_comm, mul_comm]
  have hip := integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) f w v
  have hi : Integrable (fun x => f x * ∂_{v} w x) := (product f (∂_{v} w)).integrable
  have hj : Integrable (fun x => ∂_{v} f x * w x) := (product (∂_{v} f) w).integrable
  have hdiff : (∫ x, f x * ∂_{v} w x) - (∫ x, ∂_{v} f x * w x) = a v * ∫ x, f x ^ 2 := by
    rw [← integral_sub hi hj, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [hd, matched_apply]
    ring
  change (∫ x, f x * ∂_{v} w x) = _
  linarith

/-- For f(x/L) and the parameter (x₁/L)f(x/L), division by the raw metric
gives a translation of half a squeezed standard deviation at every width. -/
theorem matched_standardized_shift (a : Space →L[ℝ] ℝ) (f : Profile) (v : Space)
    {L : ℝ} (hL : 0 < L) (ha : a v = 1 / L) (hm : (∫ x, f x ^ 2) ≠ 0) :
    L * (∫ x, f x * ∂_{v} (matchedParameter a f) x) / (∫ x, f x ^ 2) = 1 / 2 := by
  rw [matched_gradient, ha]
  field_simp

/-- Divergence-free spatial packets have zero projected Gauss translation for every
Schwartz gauge test. This uses physical-space derivatives of the fixed profiles. -/
theorem transverse_translation {n : ℕ} (e : Packets d n) (ω : Fin n → Profile)
    (j : Fin d) (hdiv : ∀ a x, ∑ l : Fin 3, ∂_{EuclideanSpace.single l (1 : ℝ)} (e j l a) x = 0) :
    translation e ω j = 0 := by
  unfold translation
  change (∑ l, ∑ a, ∫ x, e j l a x * ∂_{EuclideanSpace.single l (1 : ℝ)} (ω a) x) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  simp_rw [integral_mul_lineDerivOp_right_eq_neg_left, Finset.sum_neg_distrib]
  apply neg_eq_zero.mpr
  rw [← integral_finset_sum]
  · simp_rw [← Finset.sum_mul, hdiv, zero_mul, integral_zero]
  · intro l _
    exact (product (∂_{EuclideanSpace.single l (1 : ℝ)} (e j l a)) (ω a)).integrable

/-- For transverse packets in orthonormal coordinates every local projected charge
kills the inner Gaussian. Equal rescaling of all amplitudes preserves this conclusion. -/
theorem transverse_charge_vacuum {n : ℕ} (e : Packets d n) (ω : Fin n → Profile) (g : ℝ)
    (f : Fin n → Fin n → Fin n → ℝ) (hf : ∀ a b c, f a b c = -f b a c)
    (hd : ∀ j a x, ∑ l : Fin 3, ∂_{EuclideanSpace.single l (1 : ℝ)} (e j l a) x = 0) :
    charge (translation e ω) (rotation e ω g f) 1 = 0 := by
  rw [local_charge_vacuum e ω g f hf]
  simp [fun j => transverse_translation e ω j (hd j)]

end SchwartzCoefficients

section Ward

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem sym_on_pg {S : Module.End ℂ (Poly d)} (h : PolySym S) (p q : Poly d) :
    inner ℂ (pgLp (S p)) (pgLp q) = inner ℂ (pgLp p) (pgLp (S q)) := by
  simpa only [inner_pgLp_pgLp] using h p q

/-- The weak Ward identity on the actual Mehler polynomial core when the
selected amplitude has no linear rotation component. -/
theorem constant_row_ward (t : Fin d → ℝ) (m : Fin d → Fin d → ℝ) (j : Fin d)
    (hm : ∀ k, m j k = 0) (p : Poly d) :
    inner ℂ (pgLp (X j * p)) (pgLp (charge t m p)) -
      inner ℂ (pgLp (charge t m p)) (pgLp (X j * p)) =
        Complex.I * (t j : ℂ) * (‖pgLp p‖ : ℂ)^2 := by
  have hx := sym_on_pg (mulOp_polySym (realCoeff_X j)) p (charge t m p)
  simp only [mulOp_apply] at hx
  rw [hx, sym_on_pg (charge_polySym t m), ← inner_sub_right]
  simp only [← pgMap_apply, ← map_sub]
  have hc := charge_coordinate t m j p
  simp only [tangent, hm, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, add_zero] at hc
  rw [← neg_sub, hc, map_neg, map_smul, ← smul_eq_C_mul, map_smul, pgMap_apply]
  simp [inner_smul_right, mul_assoc]
  change inner ℂ (pgLp p) ((t j : ℂ) • pgLp p) = _
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  push_cast

/-- The weak commutator costs twice the product of the centered coordinate norm
and the charge norm. Its form only uses first actions on the trial vector. -/
theorem weak_charge_bound (qψ gψ : H) :
    ‖inner ℂ qψ gψ - inner ℂ gψ qψ‖ ≤ 2 * ‖qψ‖ * ‖gψ‖ := by
  calc
    _ ≤ ‖inner ℂ qψ gψ‖ + ‖inner ℂ gψ qψ‖ := norm_sub_le _ _
    _ ≤ ‖qψ‖ * ‖gψ‖ + ‖gψ‖ * ‖qψ‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = _ := by ring

/-- A normalized trial with amplitude deviation 1/L and commutator i/(2L)
has a charge residual bounded below uniformly in L. -/
theorem squeezed_charge_floor (qψ gψ : H) {L : ℝ} (hL : 0 < L)
    (hs : ‖qψ‖ = 1 / L)
    (hw : inner ℂ qψ gψ - inner ℂ gψ qψ = ((1 / (2 * L) : ℝ) : ℂ) * Complex.I) :
    1 / 4 ≤ ‖gψ‖ := by
  have h := weak_charge_bound qψ gψ
  rw [hw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), hs] at h
  field_simp [hL.ne'] at h
  nlinarith

end Ward

/-- A probability marginal with finite first moment cannot be invariant under
a nonzero translation. This tests a regular unreduced amplitude in any proposed lift. -/
theorem translated_marginal_ne (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : MeasureTheory.Integrable (fun x : ℝ => x) μ) {b : ℝ} (hb : b ≠ 0) :
    μ.map (· + b) ≠ μ := by
  intro h
  have he := congrArg (fun ν : MeasureTheory.Measure ℝ => ∫ x, x ∂ν) h
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop),
    MeasureTheory.integral_add hμ (MeasureTheory.integrable_const b)] at he
  simp only [MeasureTheory.integral_const, MeasureTheory.measureReal_univ_eq_one,
    smul_eq_mul, one_mul] at he
  exact hb (by linarith)

/-- A finite displacement by half a standard deviation changes the marginal
of the standardized amplitude. It can be tested without an operator domain. -/
theorem matched_marginal_changes :
    (ProbabilityTheory.gaussianReal 0 1).map (· + (1 / 2 : ℝ)) ≠
      ProbabilityTheory.gaussianReal 0 1 := by
  rw [ProbabilityTheory.gaussianReal_map_add_const]
  simp [ProbabilityTheory.gaussianReal_ext_iff]

/-- At gauge time 2π the standardized amplitude shifts by π. Its bounded
characteristic-function test at frequency one changes by a width-independent amount. -/
theorem matched_characteristic_difference :
    ‖MeasureTheory.charFun ((ProbabilityTheory.gaussianReal 0 1).map (· + Real.pi)) 1 -
      MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) 1‖ =
        2 * Real.exp (-(1 / 2 : ℝ)) := by
  rw [ProbabilityTheory.gaussianReal_map_add_const]
  simp only [zero_add, ProbabilityTheory.charFun_gaussianReal, Complex.ofReal_one, one_mul,
    one_pow, NNReal.coe_one, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [sub_eq_add_neg ((Real.pi : ℂ) * Complex.I) _, Complex.exp_add, Complex.exp_pi_mul_I]
  rw [show ∀ z : ℂ, -1 * z - z = -(2 * z) by intro z; ring]
  simp [Complex.norm_exp]

end
end BookProof.YangMillsPacketCharge
