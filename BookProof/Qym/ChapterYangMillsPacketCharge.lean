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

end SchwartzCoefficients

end
end BookProof.YangMillsPacketCharge
