import BookProof.Phi4.ChapterScalarTwoSite
import BookProof.ChapterQuadraticRotationEsa

/-!
# An exact two-site rank-two Hashimoto calculation

The three columns are in unnormalized product Hermites. Rational complex numbers
keep every finite identity decidable in the kernel. The Hermite Gram matrix enters
both the dual used in the compression and the norm of the discarded action.
-/
namespace BookProof.Phi4.RankTwo

abbrev QI := QuadraticAlgebra ℚ (-1) 0
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) QI
private def q (x : ℚ) : QI := ⟨x, 0⟩
private def ii : QI := ⟨0, 1⟩

/-- Retained rows first, then all other modes reached by one full action. -/
def modes : Fin 10 → ℕ × ℕ :=
  ![(0,0), (2,0), (0,2), (0,4), (0,6), (2,2), (2,4), (4,0), (4,2), (6,0)]

def fullColumns : Mat 10 3 := !![
    q (13/4), q (7/4), q (23/4);
    q (7/8), q (37/4), q (3/2);
    q (23/8), q (3/2), q (69/4);
    q (1/8), 0, q (31/8);
    0, 0, q (1/8);
    q (3/4), q (47/8), q (31/8);
    0, q (1/8), q (3/4);
    q (1/8), q (15/8), 0;
    0, q (3/4), q (1/8);
    0, q (1/8), 0]

private def retained (i : Fin 3) : Fin 10 := i.castLE (by decide)

noncomputable def modeTerm (i : Fin 10) := modeHe (modes i).1 0 * modeHe (modes i).2 1

/-- All ten rows are the full polynomial action on each retained mode. -/
theorem fullColumns_action (j : Fin 3) :
    modeHam 1 1 1 (modeTerm (retained j)) =
      ∑ i, ((fullColumns i j).re : ℂ) • modeTerm i := by
  fin_cases j
  · change modeHam 1 1 1 (modeHe 0 0 * modeHe 0 1) = _
    rw [twoSite_column_00]
    norm_num [Fin.sum_univ_succ, modeTerm, modes, fullColumns, q]
    abel
  · change modeHam 1 1 1 (modeHe 2 0 * modeHe 0 1) = _
    rw [twoSite_column_20]
    norm_num [Fin.sum_univ_succ, modeTerm, modes, fullColumns, q]
    abel
  · change modeHam 1 1 1 (modeHe 0 0 * modeHe 2 1) = _
    rw [twoSite_column_02]
    norm_num [Fin.sum_univ_succ, modeTerm, modes, fullColumns, q]
    abel

/-- The same coefficient array applied inside the two-site operator on the site Gaussian core. -/
theorem site_columns (j : Fin 3) :
    (twoSite 1 1 1 (by norm_num) (by norm_num) (by norm_num)).innerHam
      ⟨HermiteProductCore.pgLp (fromModes (modeTerm (retained j))),
        HermiteProductCore.pgLp_mem_core _⟩ =
      HermiteProductCore.pgLp (fromModes (∑ i, ((fullColumns i j).re : ℂ) • modeTerm i)) := by
  rw [twoSite_innerHam, fullColumns_action]

def hWin : Mat 3 3 := fullColumns.submatrix retained id

def metric : Mat 3 3 := Matrix.diagonal ![1, 2, 2]

def fullMetric : Mat 10 10 := Matrix.diagonal fun i =>
  q ((modes i).1.factorial * (modes i).2.factorial)

def inclusion : Mat 10 3 := fun i j => if i = retained j then 1 else 0

def shifted (γ : ℕ) : Mat 3 3 := γ • (1 : Mat 3 3) + ii • hWin

def basis : Mat 3 2 := !![
    1, ⟨37913768/237801325, -16436754/237801325⟩;
    0, ⟨-102704/9512053, 869/9512053⟩;
    0, ⟨-6355248/237801325, 895469/237801325⟩]

def generator : Mat 2 2 := !![
    ⟨-1975087311464981/387678327400657, -7803020777077170/387678327400657⟩, -1;
    ⟨-36582638530574935/3101426619205256, 39094647255223290/387678327400657⟩, 5]

private def res3 : Mat 3 3 := !![
    ⟨92129784/437912353, -64884570/437912353⟩,
    ⟨-13906464/437912353, 5240226/437912353⟩,
    ⟨-32208672/437912353, 15571010/437912353⟩;
    ⟨-6953232/437912353, 2620113/437912353⟩,
    ⟨15301428/437912353, -43357945/437912353⟩,
    ⟨469188/437912353, 2978483/437912353⟩;
    ⟨-16104336/437912353, 7785505/437912353⟩,
    ⟨469188/437912353, 2978483/437912353⟩,
    ⟨9938100/437912353, -26512025/437912353⟩]

def dual : Mat 2 3 := !![
    1, ⟨1027165/502353, -435020/502353⟩, ⟨895951/167451, -741260/502353⟩;
    0, ⟨-6419000/502353, -108625/1004706⟩, ⟨-5296040/167451, -4477345/1004706⟩]

private def gramInv : Mat 2 2 := !![
    q (9478442/502353), ⟨-47392210/502353, 4565765/111634⟩;
    ⟨-47392210/502353, -4565765/111634⟩, q (1189006625/2009412)]

def defectGram : Mat 2 2 := !![
    q (1227243135860099/387678327400657), ⟨-93714912/237801325, -55971003/475602650⟩;
    ⟨-93714912/237801325, 55971003/475602650⟩, q (53022439/237801325)]

def gram : Mat 2 2 := basis.conjTranspose * metric * basis

/-- The actual compressed bounded resolvent, using the physical left inverse of the basis. -/
def bounded : Mat 2 2 := dual * res3 * basis

theorem window_hermitian : hWin.conjTranspose * metric = metric * hWin := by decide +kernel

theorem shift_five_seed : (shifted 5).mulVec (fun i => basis i 1) = fun i => basis i 0 := by
  decide +kernel

theorem basis_second_column :
    (fun i => basis i 1) = ((shifted 5)⁻¹).mulVec (fun i => basis i 0) := by
  have h : IsUnit (shifted 5).det := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨-205184/237801325, -81248/237801325⟩, ?_⟩
    rw [Matrix.det_fin_three]
    decide +kernel
  rw [← shift_five_seed, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]

theorem shift_three_inverse : shifted 3 * res3 = 1 := by decide +kernel

theorem gram_inverse : gram * gramInv = 1 := by decide +kernel

theorem physical_dual : gramInv * basis.conjTranspose * metric = dual := by decide +kernel

theorem dual_basis : dual * basis = 1 := by decide +kernel

theorem compressed_inverse : bounded * (3 • (1 : Mat 2 2) - generator) = 1 := by
  decide +kernel

/-- The generator is obtained by inverting the compressed resolvent. -/
theorem hashimoto_generator :
    3 • (1 : Mat 2 2) - (gram⁻¹ * basis.conjTranspose * metric * (shifted 3)⁻¹ * basis)⁻¹ =
      generator := by
  rw [Matrix.inv_eq_right_inv gram_inverse, physical_dual,
    Matrix.inv_eq_right_inv shift_three_inverse, ← bounded,
    Matrix.inv_eq_right_inv compressed_inverse]
  abel

theorem differs_from_projected_h :
    generator ≠ (-ii) • (dual * hWin * basis) := by decide +kernel

def leak : Mat 3 2 := res3 * basis * (3 • (1 : Mat 2 2) - generator) - basis

/-- Dissipation of the reduced evolution in its own Gram metric. -/
theorem dissipation :
    generator.conjTranspose * gram + gram * generator =
      -(6 • (leak.conjTranspose * metric * leak)) := by decide +kernel

def defect : Mat 10 2 := ii • (inclusion * basis * generator) - fullColumns * basis

theorem full_defect_gram : defect.conjTranspose * fullMetric * defect = defectGram := by
  decide +kernel

/-- Squared Hilbert–Schmidt norm with the physical Gram matrices in both spaces. -/
theorem full_defect_hs_squared :
    Matrix.trace (gram⁻¹ * (defect.conjTranspose * fullMetric * defect)) =
      q (66577730826550897732871 / 259668494406269661228) := by
  rw [Matrix.inv_eq_right_inv gram_inverse, full_defect_gram]
  decide +kernel

/-- The discarded Hermite rows and the rational compression error inside the
window are orthogonal. Both are evaluated on the same two rational columns. -/
theorem defect_split :
    let inside := inclusion * inclusion.transpose * defect
    let tail := defect - inside
    let A := inside.conjTranspose * fullMetric * inside
    let B := tail.conjTranspose * fullMetric * tail
    A + B = defectGram ∧
      (A 0 0).re = 64208153658128/387678327400657 ∧ (B 0 0).re = 3 ∧
      (Matrix.trace (gramInv * A)).re = 608593260375654076576/194751370804702245921 ∧
      (Matrix.trace (gramInv * B)).re = 508924037/2009412 := by decide +kernel

private def normSq {n : ℕ} (W : Mat n n) (v : Fin n → QI) : ℚ :=
  (∑ i, star (v i) * (W.mulVec v i)).re

private def seed : Fin 2 → QI := ![1, 0]
private def speed := generator.mulVec seed
private def transverse : Fin 3 → QI :=
  let w := basis.mulVec speed
  ![0, w 1, w 2]

/-- In units of the Gaussian norm, these squared bounds control the short-time
integral of the full defect and the component orthogonal to the seed. -/
theorem orbit_rates :
    (defectGram 0 0).re ≤ (178/100 : ℚ)^2 ∧
    (Matrix.trace (gramInv * defectGram)).re ≤ (1602/100 : ℚ)^2 ∧
    normSq gram speed ≤ (529/100 : ℚ)^2 ∧
    normSq gram (generator.mulVec speed) ≤ (8851/100 : ℚ)^2 ∧
    (417/100 : ℚ)^2 ≤ normSq metric transverse := by decide +kernel

/-- The full seed variance uses all ten output rows; the shift is its mean 13/4. -/
theorem seed_variance :
    normSq fullMetric (fun i => fullColumns i 0 - q (13/4) * inclusion i 0) = 337/16 := by
  decide +kernel

open MvPolynomial HermiteProductCore HermiteProductBasis HermiteCore QuadraticRotation
noncomputable section

private def rotation : Matrix (Fin 2) (Fin 2) ℝ :=
  let a := (Real.sqrt 2)⁻¹
  !![a, a; a, -a]

private theorem orthogonal : rotation.transpose * rotation = 1 := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1/2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.mul_apply, Fin.sum_univ_two, h, Matrix.one_apply]

private theorem rotate_polynomial : fromModes = rotPoly rotation := by
  ext i
  fin_cases i <;>
    simp [rotPoly_X, rotation, rot, Fin.sum_univ_two, fromModes_X_zero, fromModes_X_one] <;> ring

theorem rotation_preserves_inner (p q : MvPolynomial (Fin 2) ℂ) :
    inner ℂ (pgLp (fromModes p)) (pgLp (fromModes q)) = inner ℂ (pgLp p) (pgLp q) := by
  rw [rotate_polynomial]
  exact inner_pgLp_rotPoly orthogonal p q

private theorem modeHe_factor (i : Fin 2) (n : ℕ) (hn : n ≤ 6) :
    modeHe n i = hermiteFactor i n := by
  have step (m : ℕ) (hm : m < 6) :
      modeHe (m+1) i = X i * modeHe m i - (m : ℂ) • modeHe (m-1) i := by
    interval_cases m <;> norm_num [modeHe, smul_eq_C_mul, map_ofNat] <;> ring
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact (hermiteFactor_zero i).symm
    | succ m =>
      rw [step m (by omega), ih m (by omega) (by omega), ih (m-1) (by omega) (by omega),
        hermiteFactor_X_mul]
      abel


private def exponent (a : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a.1, a.2]

private theorem productHe {a : ℕ × ℕ} (ha : a.1 ≤ 6 ∧ a.2 ≤ 6) :
    modeHe a.1 0 * modeHe a.2 1 = hermiteMv (exponent a) := by
  simp [hermiteMv, exponent, Fin.prod_univ_two, modeHe_factor _ _ ha.1,
    modeHe_factor _ _ ha.2]

theorem rotated_mode_inner (i j : Fin 10) :
    inner ℂ (pgLp (fromModes (modeHe (modes i).1 0 * modeHe (modes i).2 1)))
      (pgLp (fromModes (modeHe (modes j).1 0 * modeHe (modes j).2 1))) =
      ((fullMetric i j).re : ℂ) * ((Real.sqrt (2*Real.pi) : ℝ) : ℂ)^2 := by
  have hdeg : ∀ n, (modes n).1 ≤ 6 ∧ (modes n).2 ≤ 6 := by decide +kernel
  have hinj : Function.Injective modes := by decide +kernel
  rw [rotation_preserves_inner, productHe (hdeg i), productHe (hdeg j), inner_pgLp_hermiteMv]
  by_cases hij : i = j
  · subst j
    simp [fullMetric, q, exponent, Fin.prod_univ_two, hermiteInner_eq]
    ring
  · have hne : modes i ≠ modes j := fun h => hij (hinj h)
    rcases not_and_or.mp (fun h : (modes i).1 = (modes j).1 ∧ (modes i).2 = (modes j).2 =>
      hne (Prod.ext h.1 h.2)) with h | h <;>
      simp [fullMetric, hij, h, exponent, Fin.prod_univ_two, hermiteInner_eq]

/-- Reconstruct a physical site-space vector from any ten complex mode coefficients. -/
def synthesize (c : Fin 10 → ℂ) : L2d 2 :=
  ∑ i, c i • pgLp (fromModes (modeTerm i))

theorem synthesis_inner (a b : Fin 10 → ℂ) :
    inner ℂ (synthesize a) (synthesize b) =
      (∑ i, ∑ j, (starRingEnd ℂ) (a i) * ((fullMetric i j).re : ℂ) * b j) *
        ((Real.sqrt (2*Real.pi) : ℝ) : ℂ)^2 := by
  simp only [synthesize, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    modeTerm, rotated_mode_inner, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end

end BookProof.Phi4.RankTwo
