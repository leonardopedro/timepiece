import BookProof.Phi4.ChapterScalarMehler

/-!
# The periodic two-site scalar operator in uniform and staggered modes

The `2 x 1 x 1` periodic grid has two oriented links along its active axis and no
link along the two singleton axes. Rotating the site coordinates,

`u = (x₀ + x₁)/√2`,  `w = (x₀ − x₁)/√2`,

turns the link into `2 w²/a²` and the two local walls into the mixed quartic
`u⁴/8 + 3u²w²/4 + w⁴/8 − …`. This chapter proves the rotation on every polynomial,
identifies the full inner Hamiltonian with the mode operator, and evaluates its
three exact fixture columns in the unnormalized product Hermites.
-/
namespace BookProof.Phi4

open MvPolynomial BookProof.YangMillsHermite BookProof.HermiteProductCore

noncomputable section

/-- The normalization of the orthogonal two-site mode change. -/
def rot : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem rot_sq : rot * rot = (1 / 2 : ℂ) := by
  rw [rot, ← mul_inv]
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [h]
  norm_num

/-- Uniform and staggered coordinates `u = (x₀+x₁)/√2`, `w = (x₀−x₁)/√2`. -/
def fromModes : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval ![C rot * (X 0 + X 1), C rot * (X 0 - X 1)]

@[simp] theorem fromModes_X_zero :
    fromModes (X 0) = C rot * (X 0 + X 1 : MvPolynomial (Fin 2) ℂ) := by
  simp [fromModes]

@[simp] theorem fromModes_X_one :
    fromModes (X 1) = C rot * (X 0 - X 1 : MvPolynomial (Fin 2) ℂ) := by
  simp [fromModes]

@[simp] theorem fromModes_C (c : ℂ) : fromModes (C c) = (C c : MvPolynomial (Fin 2) ℂ) := by
  simp [fromModes]

theorem fromModes_deriv_zero (p : MvPolynomial (Fin 2) ℂ) :
    pderiv 0 (fromModes p) = fromModes (rot • (pderiv 0 p + pderiv 1 p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    rw [← map_add]
    congr 1
    module
  | mul_X p n hp =>
    fin_cases n
    · simp [Fin.zero_eta, fromModes_X_zero, map_mul, pderiv_mul, pderiv_X,
        pderiv_C, map_add, map_sub, map_smul, smul_eq_C_mul, hp]
      ring_nf
    · simp [Fin.mk_one, fromModes_X_one, map_mul, pderiv_mul, pderiv_X,
        pderiv_C, map_add, map_sub, map_smul, smul_eq_C_mul, hp]
      ring_nf

theorem fromModes_deriv_one (p : MvPolynomial (Fin 2) ℂ) :
    pderiv 1 (fromModes p) = fromModes (rot • (pderiv 0 p - pderiv 1 p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    rw [← map_add]
    congr 1
    module
  | mul_X p n hp =>
    fin_cases n
    · simp [Fin.zero_eta, fromModes_X_zero, map_mul, pderiv_mul, pderiv_X,
        pderiv_C, map_add, map_sub, map_smul, smul_eq_C_mul, hp]
      ring_nf
    · simp [Fin.mk_one, fromModes_X_one, map_mul, pderiv_mul, pderiv_X,
        pderiv_C, map_add, map_sub, map_smul, smul_eq_C_mul, hp]
      ring_nf

theorem fromModes_mode_u :
    fromModes (rot • (X 0 + X 1)) = (X 0 : MvPolynomial (Fin 2) ℂ) := by
  rw [map_smul, map_add, fromModes_X_zero, fromModes_X_one, smul_eq_C_mul]
  apply MvPolynomial.funext
  intro x
  simp
  linear_combination (2 * x 0) * rot_sq

theorem fromModes_mode_w :
    fromModes (rot • (X 0 - X 1)) = (X 1 : MvPolynomial (Fin 2) ℂ) := by
  rw [map_smul, map_sub, fromModes_X_zero, fromModes_X_one, smul_eq_C_mul]
  apply MvPolynomial.funext
  intro x
  simp
  linear_combination (2 * x 1) * rot_sq

theorem mul_fromModes_zero (p : MvPolynomial (Fin 2) ℂ) :
    (X 0 : MvPolynomial (Fin 2) ℂ) * fromModes p =
      fromModes (rot • (X 0 + X 1) * p) := by
  nth_rewrite 1 [← fromModes_mode_u]
  rw [← map_mul]

theorem mul_fromModes_one (p : MvPolynomial (Fin 2) ℂ) :
    (X 1 : MvPolynomial (Fin 2) ℂ) * fromModes p =
      fromModes (rot • (X 0 - X 1) * p) := by
  nth_rewrite 1 [← fromModes_mode_w]
  rw [← map_mul]

theorem fromModes_derOp_zero (p : MvPolynomial (Fin 2) ℂ) :
    derOp (0 : Fin 2) (fromModes p) =
      fromModes (rot • (derOp (0 : Fin 2) p + derOp (1 : Fin 2) p)) := by
  rw [derOp_apply, fromModes_deriv_zero, mul_fromModes_zero]
  conv_lhs => rw [← map_smul, ← map_sub]
  congr 1
  simp only [derOp_apply, smul_eq_C_mul, mul_add, mul_sub]
  ring

theorem fromModes_derOp_one (p : MvPolynomial (Fin 2) ℂ) :
    derOp (1 : Fin 2) (fromModes p) =
      fromModes (rot • (derOp (0 : Fin 2) p - derOp (1 : Fin 2) p)) := by
  rw [derOp_apply, fromModes_deriv_one, mul_fromModes_one]
  conv_lhs => rw [← map_smul, ← map_sub]
  congr 1
  simp only [derOp_apply, smul_eq_C_mul, mul_add, mul_sub]
  ring

theorem fromModes_momOp_zero (p : MvPolynomial (Fin 2) ℂ) :
    momOp (0 : Fin 2) (fromModes p) =
      fromModes (rot • (momOp (0 : Fin 2) p + momOp (1 : Fin 2) p)) := by
  rw [momOp, LinearMap.smul_apply, fromModes_derOp_zero]
  conv_rhs =>
    simp only [momOp, LinearMap.smul_apply]
    rw [
      show rot • ((-Complex.I) • (derOp (0 : Fin 2) p) +
          (-Complex.I) • (derOp (1 : Fin 2) p)) =
        (-Complex.I) • (rot • (derOp (0 : Fin 2) p + derOp (1 : Fin 2) p)) by module]
  conv_rhs => rw [map_smul]

theorem fromModes_momOp_one (p : MvPolynomial (Fin 2) ℂ) :
    momOp (1 : Fin 2) (fromModes p) =
      fromModes (rot • (momOp (0 : Fin 2) p - momOp (1 : Fin 2) p)) := by
  rw [momOp, LinearMap.smul_apply, fromModes_derOp_one]
  conv_rhs =>
    simp only [momOp, LinearMap.smul_apply]
    rw [
      show rot • ((-Complex.I) • (derOp (0 : Fin 2) p) -
          (-Complex.I) • (derOp (1 : Fin 2) p)) =
        (-Complex.I) • (rot • (derOp (0 : Fin 2) p - derOp (1 : Fin 2) p)) by module]
  conv_rhs => rw [map_smul]

/-- The kinetic energy is invariant under the orthogonal mode change. -/
theorem fromModes_kinetic (p : MvPolynomial (Fin 2) ℂ) :
    (∑ i : Fin 2, momOp i (momOp i (fromModes p))) =
      fromModes (∑ i : Fin 2, momOp i (momOp i p)) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  set q0 := rot • (momOp (0 : Fin 2) p + momOp (1 : Fin 2) p) with hq0
  set q1 := rot • (momOp (0 : Fin 2) p - momOp (1 : Fin 2) p) with hq1
  have h0 : momOp (0 : Fin 2) (fromModes p) = fromModes q0 := fromModes_momOp_zero p
  have h1 : momOp (1 : Fin 2) (fromModes p) = fromModes q1 := fromModes_momOp_one p
  rw [h0, h1, fromModes_momOp_zero q0, fromModes_momOp_one q1, ← map_add]
  congr 1
  simp only [q0, q1, map_add, map_sub, map_smul, smul_sub, smul_add, smul_smul]
  rw [rot_sq]
  module

/-- The actual `2 x 1 x 1` periodic site model at unit side lengths. -/
def twoSite (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a) :
    Model 2 2 8 :=
  siteModel (periodicNext 1 0 0) ⟨lam, hlam, v, hv⟩ a ha

@[simp] theorem periodicNext_00 :
    periodicNext 1 0 0 (0 : Fin 2) (0 : Fin 3) = 1 := by decide

@[simp] theorem periodicNext_01 :
    periodicNext 1 0 0 (0 : Fin 2) (1 : Fin 3) = 0 := by decide

@[simp] theorem periodicNext_02 :
    periodicNext 1 0 0 (0 : Fin 2) (2 : Fin 3) = 0 := by decide

@[simp] theorem periodicNext_10 :
    periodicNext 1 0 0 (1 : Fin 2) (0 : Fin 3) = 0 := by decide

@[simp] theorem periodicNext_11 :
    periodicNext 1 0 0 (1 : Fin 2) (1 : Fin 3) = 1 := by decide

@[simp] theorem periodicNext_12 :
    periodicNext 1 0 0 (1 : Fin 2) (2 : Fin 3) = 1 := by decide

@[simp] theorem twoSite_momentum (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v)
    (ha : 0 < a) : (twoSite lam v a hlam hv ha).momentum = id := rfl

/-- The site form sum: two walls and the two oriented active links. -/
theorem twoSite_forms (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a)
    (p : MvPolynomial (Fin 2) ℂ) :
    ∑ j, (twoSite lam v a hlam hv ha).form j *
      ((twoSite lam v a hlam hv ha).form j * p) =
      ((lam / (2 * a^3) : ℝ) : ℂ) •
        ((X 0 ^ 2 - C ((a^3 * v^2 : ℝ) : ℂ)) *
          ((X 0 ^ 2 - C ((a^3 * v^2 : ℝ) : ℂ)) * p) +
         (X 1 ^ 2 - C ((a^3 * v^2 : ℝ) : ℂ)) *
          ((X 1 ^ 2 - C ((a^3 * v^2 : ℝ) : ℂ)) * p)) +
      ((2 / a^2 : ℝ) : ℂ) • ((X 0 - X 1) * ((X 0 - X 1) * p)) := by
  conv_lhs =>
    rw [← (finProdFinEquiv (m := 2) (n := 4)).sum_comp]
    rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_two]
  simp [Fin.sum_univ_succ, twoSite, siteModel, siteForm,
    Equiv.symm_apply_apply, wall, smul_eq_C_mul]
  ring_nf
  simp only [← map_pow, ← Complex.ofReal_pow]
  rw [Real.sq_sqrt (by positivity)]
  push_cast
  apply MvPolynomial.funext
  intro x
  simp
  field_simp
  ring

/-- The site potential after the mode rotation, including the mixed vertex. -/
def modePotential (lam v a : ℝ) (p : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  ((lam / (4 * a ^ 3) : ℝ) : ℂ) •
    ((X 0 ^ 2 + X 1 ^ 2 - C ((2 * a ^ 3 * v ^ 2 : ℝ) : ℂ)) *
      ((X 0 ^ 2 + X 1 ^ 2 - C ((2 * a ^ 3 * v ^ 2 : ℝ) : ℂ)) * p))
    + ((lam / a ^ 3 : ℝ) : ℂ) • ((X 0 * X 1) * ((X 0 * X 1) * p))
    + ((4 / a ^ 2 : ℝ) : ℂ) • (X 1 * (X 1 * p))

/-- Under the rotation the site form sum is the mode potential. -/
theorem twoSite_forms_modes (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a)
    (p : MvPolynomial (Fin 2) ℂ) :
    ∑ j, (twoSite lam v a hlam hv ha).form j *
      ((twoSite lam v a hlam hv ha).form j * fromModes p) =
      fromModes (modePotential lam v a p) := by
  rw [twoSite_forms]
  conv_rhs =>
    simp only [modePotential, map_add, map_mul, map_sub, map_pow, map_smul,
      fromModes_X_zero, fromModes_X_one, fromModes_C, smul_eq_C_mul]
  apply MvPolynomial.funext
  intro x
  simp
  ring_nf
  have hrot2 : rot ^ 2 = (1 / 2 : ℂ) := by rw [sq, rot_sq]
  have hrot4 : rot ^ 4 = (1 / 4 : ℂ) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hrot2]
    norm_num
  rw [hrot2, hrot4]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [ha']
  ring

/-- The full mode action: half the kinetic sum plus the mode potential. -/
def modeHam (lam v a : ℝ) (p : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  ((1 / 2 : ℝ) : ℂ) •
    ((∑ i : Fin 2, momOp i (momOp i p)) + modePotential lam v a p)

/-- The full `2 x 1 x 1` inner Hamiltonian on the rotated core. -/
theorem twoSite_action (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a)
    (p : MvPolynomial (Fin 2) ℂ) :
    ((1 / 2 : ℝ) : ℂ) • ((∑ i : Fin 2, momOp i (momOp i (fromModes p))) +
      (∑ j, (twoSite lam v a hlam hv ha).form j *
        ((twoSite lam v a hlam hv ha).form j * fromModes p))) =
      fromModes (modeHam lam v a p) := by
  rw [fromModes_kinetic, twoSite_forms_modes, ← map_add, ← map_smul]
  rfl

/-- Binding of the two-site calculation to the actual site operator. -/
theorem twoSite_innerHam (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a)
    (p : MvPolynomial (Fin 2) ℂ) :
    (twoSite lam v a hlam hv ha).innerHam
        ⟨pgLp (fromModes p), pgLp_mem_core (fromModes p)⟩ =
      pgLp (fromModes (modeHam lam v a p)) := by
  rw [Model.innerHam_pgLp]
  simp only [twoSite_momentum, id_eq]
  rw [twoSite_action]

/-- Unnormalized probabilists' Hermites `He₀ … He₆` in mode `i`. -/
def modeHe : ℕ → Fin 2 → MvPolynomial (Fin 2) ℂ
  | 0, _ => 1
  | 1, i => X i
  | 2, i => X i ^ 2 - 1
  | 3, i => X i ^ 3 - 3 * X i
  | 4, i => X i ^ 4 - 6 * X i ^ 2 + 3
  | 5, i => X i ^ 5 - 10 * X i ^ 3 + 15 * X i
  | 6, i => X i ^ 6 - 15 * X i ^ 4 + 45 * X i ^ 2 - 15
  | _, _ => 0

/-- Fixture column `(0,0)`: the Gaussian seed. -/
theorem twoSite_column_00 :
    modeHam 1 1 1 (modeHe 0 0 * modeHe 0 1) =
      (13/4 : ℂ) • (modeHe 0 0 * modeHe 0 1) +
      (23/8 : ℂ) • (modeHe 0 0 * modeHe 2 1) +
      (1/8 : ℂ) • (modeHe 0 0 * modeHe 4 1) +
      (7/8 : ℂ) • (modeHe 2 0 * modeHe 0 1) +
      (3/4 : ℂ) • (modeHe 2 0 * modeHe 2 1) +
      (1/8 : ℂ) • (modeHe 4 0 * modeHe 0 1) := by
  simp [modeHam, modePotential, modeHe, momOp_apply, pderiv_C,
    Derivation.map_natCast, Complex.I_sq]
  apply MvPolynomial.funext
  intro x
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Fixture column `(2,0)`: the uniform-mode excitation. -/
theorem twoSite_column_20 :
    modeHam 1 1 1 (modeHe 2 0 * modeHe 0 1) =
      (7/4 : ℂ) • (modeHe 0 0 * modeHe 0 1) +
      (3/2 : ℂ) • (modeHe 0 0 * modeHe 2 1) +
      (37/4 : ℂ) • (modeHe 2 0 * modeHe 0 1) +
      (47/8 : ℂ) • (modeHe 2 0 * modeHe 2 1) +
      (1/8 : ℂ) • (modeHe 2 0 * modeHe 4 1) +
      (15/8 : ℂ) • (modeHe 4 0 * modeHe 0 1) +
      (3/4 : ℂ) • (modeHe 4 0 * modeHe 2 1) +
      (1/8 : ℂ) • (modeHe 6 0 * modeHe 0 1) := by
  simp [modeHam, modePotential, modeHe, momOp_apply, pderiv_C,
    Derivation.map_natCast, Complex.I_sq]
  rw [show (2 : MvPolynomial (Fin 2) ℂ) = C 2 from rfl, pderiv_C]
  apply MvPolynomial.funext
  intro x
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Fixture column `(0,2)`: the staggered-mode excitation. -/
theorem twoSite_column_02 :
    modeHam 1 1 1 (modeHe 0 0 * modeHe 2 1) =
      (23/4 : ℂ) • (modeHe 0 0 * modeHe 0 1) +
      (69/4 : ℂ) • (modeHe 0 0 * modeHe 2 1) +
      (31/8 : ℂ) • (modeHe 0 0 * modeHe 4 1) +
      (1/8 : ℂ) • (modeHe 0 0 * modeHe 6 1) +
      (3/2 : ℂ) • (modeHe 2 0 * modeHe 0 1) +
      (31/8 : ℂ) • (modeHe 2 0 * modeHe 2 1) +
      (3/4 : ℂ) • (modeHe 2 0 * modeHe 4 1) +
      (1/8 : ℂ) • (modeHe 4 0 * modeHe 2 1) := by
  simp [modeHam, modePotential, modeHe, momOp_apply, pderiv_C,
    Derivation.map_natCast, Complex.I_sq]
  rw [show (2 : MvPolynomial (Fin 2) ℂ) = C 2 from rfl, pderiv_C]
  apply MvPolynomial.funext
  intro x
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

end
end BookProof.Phi4
