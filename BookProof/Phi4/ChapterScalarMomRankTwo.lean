import BookProof.Phi4.ChapterScalarMomentum

/-!
# Exact `S₃`-symmetric rank-two Hashimoto–SIRK certificate

Continuous model `unitMomCont` on `L²(ℝ³_k × ℝ_φ)`.  The eleven rows
`fullColumns` are the exact polynomial action of `unitMomCont.innerHam` on the
`S₃`-symmetric modes of §2.2, in the unnormalized product-Hermite basis.  The
Hermite Gram weights are `fullMetric`.

The rational matrices below are transcribed from
`../unfer/docs/fixtures/phi4_momentum_mehler.json` (schema
`phi4-momentum-cont-exact/v1`).  Every finite identity is checked in the kernel
with `decide +kernel`; no floating-point value enters the certificate.
-/

namespace BookProof.Phi4.MomRankTwo

abbrev QI := QuadraticAlgebra ℚ (-1) 0
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) QI

private def q (x : ℚ) : QI := ⟨x, 0⟩
private def ii : QI := ⟨0, 1⟩

/-- Exact 11×3 action table (rows: modes, columns: retained inputs). -/
def fullColumns : Mat 11 3 := !![
    ⟨17/8, 0⟩, ⟨19/4, 0⟩, ⟨3, 0⟩;
    ⟨19/8, 0⟩, ⟨125/8, 0⟩, ⟨3, 0⟩;
    ⟨1/2, 0⟩, ⟨1, 0⟩, ⟨33/8, 0⟩;
    ⟨1/2, 0⟩, ⟨5/2, 0⟩, ⟨35/8, 0⟩;
    ⟨1/4, 0⟩, ⟨35/8, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨1/4, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨1/2, 0⟩, ⟨1/4, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1/2, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1/2, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]

/-- Hermite Gram weights of the eleven modes. -/
def fullMetric : Mat 11 11 :=
  Matrix.diagonal ![1, 2, 6, 12, 24, 720, 144, 72, 12, 144, 24]

/-- The three-dimensional retained window. -/
private def retained (i : Fin 3) : Fin 11 := i.castLE (by decide)

def hWin : Mat 3 3 := fullColumns.submatrix retained id

/-- The Hermite metric on the retained window. -/
def metric : Mat 3 3 := Matrix.diagonal ![1, 2, 6]

/-- Orthonormalized two-column Krylov basis. -/
def basis : Mat 3 2 := !![
    ⟨1, 0⟩, ⟨110324118400/1172304151961, -16502148984/1172304151961⟩;
    ⟨0, 0⟩, ⟨-12949530880/1172304151961, -5177637112/1172304151961⟩;
    ⟨0, 0⟩, ⟨-2635663360/1172304151961, -3134041696/1172304151961⟩]

/-- Exact inverse `(5I + i h_win)⁻¹`. -/
def res5 : Mat 3 3 := !![
    ⟨15355083200/86641347161, -3985592184/86641347161⟩,
      ⟨-4366362880/86641347161, -9853424/86641347161⟩,
      ⟨-4662958080/86641347161, -2746291776/86641347161⟩;
    ⟨-2183181440/86641347161, -4926712/86641347161⟩,
      ⟨2340900800/86641347161, -4882994520/86641347161⟩,
      ⟨-1791490560/86641347161, 1383348096/86641347161⟩;
    ⟨-777159680/86641347161, -457715296/86641347161⟩,
      ⟨-597163520/86641347161, 461116032/86641347161⟩,
      ⟨10716608320/86641347161, -8016607944/86641347161⟩]

/-- Physical left inverse of the basis. -/
def dual : Mat 2 3 := !![
    ⟨1, 0⟩, ⟨17902823/3262873, -10461680/3262873⟩,
      ⟨9558852/3262873, -15564480/3262873⟩;
    ⟨0, 0⟩, ⟨-202336420/3262873, 647204639/26102984⟩,
      ⟨-123546720/3262873, 293816409/6525746⟩]

/-- Inverse of the physical Gram matrix `Vᴴ W V`. -/
def gramInv : Mat 2 2 := !![
    ⟨172381435/6525746, 0⟩, ⟨-861907175/3262873, 2062768623/52205968⟩;
    ⟨-861907175/3262873, -2062768623/52205968⟩,
      ⟨1172304151961/417647744, 0⟩]

/-- Hashimoto generator at the two shifts `(10, 5)`. -/
def generator : Mat 2 2 := !![
    ⟨-410510624514736810/35842864921428721,
        -2164067412169955831/143371459685714884⟩, ⟨-1, 0⟩;
    ⟨225295123360348302293/2293943354971438144,
        10976144245761583075/71685729842857442⟩, ⟨10, 0⟩]

/-- Gram matrix of the full unprojected defect. -/
def defectGram : Mat 2 2 := !![
    ⟨376129126840276773/71685729842857442, 0⟩,
      ⟨-106895779200/1172304151961, -370105795818/1172304151961⟩;
    ⟨-106895779200/1172304151961, 370105795818/1172304151961⟩,
      ⟨62155170072/1172304151961, 0⟩]

/-- Physical Gram matrix of the two-column basis. -/
def gram : Mat 2 2 := basis.conjTranspose * metric * basis

/-- The compressed bounded resolvent `V⁺ R₅ V`. -/
def bounded : Mat 2 2 := dual * res5 * basis

/-- The leak `L = R₅ V B⁻¹ − V`. -/
def leak : Mat 3 2 := !![
    ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨-80267614831008/35842864921428721, -1202410014600960/35842864921428721⟩, ⟨0, 0⟩;
    ⟨-563507635626408/35842864921428721, 1246603278254400/35842864921428721⟩, ⟨0, 0⟩]

/-- Full unprojected defect `D = i V G − H V` on the eleven modes. -/
def defect : Mat 11 2 := !![
    ⟨-2071794077326512/35842864921428721, -1971637734591360/35842864921428721⟩, ⟨0, 0⟩;
    ⟨-8956754461618524/35842864921428721, -14646508569221760/35842864921428721⟩, ⟨0, 0⟩;
    ⟨3828279779482059/35842864921428721, 6757366686330480/35842864921428721⟩, ⟨0, 0⟩;
    ⟨-1/2, 0⟩, ⟨-11257204800/1172304151961, 34906599692/1172304151961⟩;
    ⟨-1/4, 0⟩, ⟨29073168000/1172304151961, 26777699611/1172304151961⟩;
    ⟨0, 0⟩, ⟨3237382720/1172304151961, 1294409278/1172304151961⟩;
    ⟨0, 0⟩, ⟨7133681280/1172304151961, 3372328980/1172304151961⟩;
    ⟨0, 0⟩, ⟨1317831680/1172304151961, 1567020848/1172304151961⟩;
    ⟨0, 0⟩, ⟨2635663360/1172304151961, 3134041696/1172304151961⟩;
    ⟨0, 0⟩, ⟨1317831680/1172304151961, 1567020848/1172304151961⟩;
    ⟨0, 0⟩, ⟨2635663360/1172304151961, 3134041696/1172304151961⟩]

/-- The retained window is Hermitian for the Hermite metric. -/
theorem window_hermitian : hWin.conjTranspose * metric = metric * hWin := by
  decide +kernel

/-- The fixture's `gramInv` is the inverse of the physical Gram matrix. -/
theorem gram_inverse : gram * gramInv = 1 := by
  decide +kernel

/-- The physical left inverse is `V⁺ = W₂⁻¹ Vᴴ W`. -/
theorem physical_dual : gramInv * basis.conjTranspose * metric = dual := by
  decide +kernel

/-- `V⁺ V = 1`. -/
theorem dual_basis : dual * basis = 1 := by
  decide +kernel

/-- `R₅` is the inverse of `5I + i h_win`. -/
theorem res5_inverse : res5 * (5 • (1 : Mat 3 3) + ii • hWin) = 1 := by
  decide +kernel

/-- The compressed resolvent inverts `5I − G`. -/
theorem compressed_inverse : bounded * (5 • (1 : Mat 2 2) - generator) = 1 := by
  decide +kernel

/-- The generator is obtained by inverting the compressed resolvent. -/
theorem hashimoto_generator :
    5 • (1 : Mat 2 2) -
        (gramInv * basis.conjTranspose * metric * res5 * basis)⁻¹ = generator := by
  have hM : gramInv * basis.conjTranspose * metric * res5 * basis = bounded := by
    rw [physical_dual]
    rfl
  rw [hM]
  have hinv : bounded⁻¹ = 5 • (1 : Mat 2 2) - generator :=
    Matrix.inv_eq_right_inv compressed_inverse
  rw [hinv]
  abel


/-- **Exact dissipation** of the reduced Hashimoto evolution. -/
theorem dissipation :
    generator.conjTranspose * gram + gram * generator =
      -(10 • (leak.conjTranspose * metric * leak)) := by
  decide +kernel

/-- The Hashimoto generator is not the projected Hamiltonian. -/
theorem differs_from_projected_h :
    generator ≠ (-ii) • (dual * hWin * basis) := by
  decide +kernel

/-- The full defect Gram matrix. -/
theorem full_defect_gram : defect.conjTranspose * fullMetric * defect = defectGram := by
  decide +kernel

/-- Squared Hilbert–Schmidt norm of the full defect. -/
theorem full_defect_hs_squared :
    Matrix.trace (gramInv * (defect.conjTranspose * fullMetric * defect)) =
      q (581287352664920203420194051 / 1871211459116430322806928) := by
  rw [full_defect_gram]
  decide +kernel

/-- The seed variance over all eleven rows is `553/32`. -/
theorem seed_variance :
    (∑ i, star (fullColumns i 0 - q (17/8) * (if i = 0 then 1 else 0)) *
      (fullMetric.mulVec (fun j => fullColumns j 0 - q (17/8) * (if j = 0 then 1 else 0)) i)).re
        = 553/32 := by
  decide +kernel


/-! ## The eleven continuous `S₃`-symmetric modes -/

open MvPolynomial

/-- `He₂(φ) = φ² − 1`. -/
noncomputable def he2 : MvPolynomial (Fin 4) ℂ := X 0 ^ 2 - 1

/-- `He₄(φ) = φ⁴ − 6φ² + 3`. -/
noncomputable def he4 : MvPolynomial (Fin 4) ℂ := X 0 ^ 4 - 6 * X 0 ^ 2 + 3

/-- `He₆(φ) = φ⁶ − 15φ⁴ + 45φ² − 15`. -/
noncomputable def he6 : MvPolynomial (Fin 4) ℂ :=
  X 0 ^ 6 - 15 * X 0 ^ 4 + 45 * X 0 ^ 2 - 15

/-- `K₂ = |k|² − 3 = k₁² + k₂² + k₃² − 3`. -/
noncomputable def k2 : MvPolynomial (Fin 4) ℂ := X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 - 3

/-- `K₄ = Σᵢ (kᵢ⁴ − 6kᵢ²) + 9`. -/
noncomputable def k4 : MvPolynomial (Fin 4) ℂ :=
  (X 1 ^ 4 - 6 * X 1 ^ 2) + (X 2 ^ 4 - 6 * X 2 ^ 2) +
    (X 3 ^ 4 - 6 * X 3 ^ 2) + 9

/-- `K₂₂ = Σᵢ<ⱼ (kᵢ² − 1)(kⱼ² − 1)`. -/
noncomputable def k22 : MvPolynomial (Fin 4) ℂ :=
  (X 1 ^ 2 - 1) * (X 2 ^ 2 - 1) + (X 1 ^ 2 - 1) * (X 3 ^ 2 - 1) +
    (X 2 ^ 2 - 1) * (X 3 ^ 2 - 1)

/-- The eleven modes in the order of `phi4_momentum_mehler.json`. -/
noncomputable def contMode : Fin 11 → MvPolynomial (Fin 4) ℂ :=
  ![1, he2, k2, he2 * k2, he4, he6, he4 * k2, k4, k22, he2 * k4, he2 * k22]

end BookProof.Phi4.MomRankTwo

namespace BookProof.Phi4.MomRankTwo

/-! ## The three retained `fullColumns` actions -/

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis BookProof.HermiteCore
open BookProof.YangMillsNonAbelianEsa BookProof.YangMillsHermite
open BookProof.YangMillsFriedrichs BookProof.FarisLavine
open scoped InnerProductSpace

noncomputable section

private noncomputable def cc (x : ℚ) : MvPolynomial (Fin 4) ℂ := C (x : ℂ)

@[simp] private theorem pderiv_two (j : Fin 4) :
    (pderiv j) (2 : MvPolynomial (Fin 4) ℂ) = 0 := by
  change (pderiv j) (Nat.cast 2) = 0
  exact Derivation.map_natCast _ 2

@[simp] private theorem pderiv_three (j : Fin 4) :
    (pderiv j) (3 : MvPolynomial (Fin 4) ℂ) = 0 := by
  change (pderiv j) (Nat.cast 3) = 0
  exact Derivation.map_natCast _ 3

private noncomputable def col0 : MvPolynomial (Fin 4) ℂ :=
  cc (17/8) + cc (19/8) * (X 0 ^ 2 - 1) + cc (1/4) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3) +
    cc (1/2) * ((X 1 ^ 2 - 1) + (X 2 ^ 2 - 1) + (X 3 ^ 2 - 1)) +
    cc (1/2) * (X 0 ^ 2 - 1) * ((X 1 ^ 2 - 1) + (X 2 ^ 2 - 1) + (X 3 ^ 2 - 1))

private noncomputable def col1 : MvPolynomial (Fin 4) ℂ :=
  cc (19/4) + cc (125/8) * (X 0 ^ 2 - 1) +
    cc 1 * (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 - 3) +
    cc (5/2) * (X 0 ^ 2 - 1) * (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 - 3) +
    cc (35/8) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3) +
    cc (1/4) * (X 0 ^ 6 - 15 * X 0 ^ 4 + 45 * X 0 ^ 2 - 15) +
    cc (1/2) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3) * (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 - 3)

private noncomputable def col2 : MvPolynomial (Fin 4) ℂ :=
  cc 3 + cc 3 * (X 0 ^ 2 - 1) + cc (33/8) * (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 - 3) +
    cc (35/8) * (X 0 ^ 2 - 1) * (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 - 3) +
    cc (1/4) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3) * (X 1 ^ 2 + X 2 ^ 2 + X 3 ^ 2 - 3) +
    cc (1/2) * ((X 1 ^ 4 - 6 * X 1 ^ 2) + (X 2 ^ 4 - 6 * X 2 ^ 2) +
      (X 3 ^ 4 - 6 * X 3 ^ 2) + 9) +
    cc 1 * ((X 1 ^ 2 - 1) * (X 2 ^ 2 - 1) + (X 1 ^ 2 - 1) * (X 3 ^ 2 - 1) +
      (X 2 ^ 2 - 1) * (X 3 ^ 2 - 1)) +
    cc (1/2) * (X 0 ^ 2 - 1) * ((X 1 ^ 4 - 6 * X 1 ^ 2) + (X 2 ^ 4 - 6 * X 2 ^ 2) +
      (X 3 ^ 4 - 6 * X 3 ^ 2) + 9) +
    cc 1 * (X 0 ^ 2 - 1) * ((X 1 ^ 2 - 1) * (X 2 ^ 2 - 1) +
      (X 1 ^ 2 - 1) * (X 3 ^ 2 - 1) + (X 2 ^ 2 - 1) * (X 3 ^ 2 - 1))

private noncomputable def fullColumnPoly : Fin 3 → MvPolynomial (Fin 4) ℂ :=
  ![col0, col1, col2]

private theorem cont_fullColumns_action_apply (j : Fin 3) :
    unitMomCont.innerHam ⟨pgLp (contMode (retained j)), pgLp_mem_core _⟩ =
      pgLp (fullColumnPoly j) := by
  fin_cases j
  · rw [Model.innerHam_pgLp, unitMomCont_forms, Fin.sum_univ_one]
    congr 1
    have hmom : unitMomCont.momentum 0 = (0 : Fin 4) := rfl
    rw [hmom, momOp_momOp_d]
    simp [fullColumnPoly, col0, cc, contMode, retained, QgHermiteFriedrichs.coreD,
      smul_eq_C_mul, Derivation.leibniz, MvPolynomial.pderiv_X]
    apply MvPolynomial.funext
    intro x
    simp
    ring
  · rw [Model.innerHam_pgLp, unitMomCont_forms, Fin.sum_univ_one]
    congr 1
    have hmom : unitMomCont.momentum 0 = (0 : Fin 4) := rfl
    rw [hmom, momOp_momOp_d]
    simp [fullColumnPoly, col1, cc, contMode, he2, retained, QgHermiteFriedrichs.coreD,
      smul_eq_C_mul, Derivation.leibniz, MvPolynomial.pderiv_X]
    apply MvPolynomial.funext
    intro x
    simp
    ring
  · rw [Model.innerHam_pgLp, unitMomCont_forms, Fin.sum_univ_one]
    congr 1
    have hmom : unitMomCont.momentum 0 = (0 : Fin 4) := rfl
    rw [hmom, momOp_momOp_d]
    simp [fullColumnPoly, col2, cc, contMode, k2, retained, QgHermiteFriedrichs.coreD,
      smul_eq_C_mul, Derivation.leibniz, MvPolynomial.pderiv_X]
    apply MvPolynomial.funext
    intro x
    simp
    ring

private theorem fullColumnPoly_eq (j : Fin 3) :
    (∑ k : Fin 11, C ((fullColumns k j).re : ℂ) * contMode k) = fullColumnPoly j := by
  fin_cases j
  · simp [fullColumns, contMode, fullColumnPoly, col0, Fin.sum_univ_succ,
      he2, he4, he6, k2, k4, k22, cc]
    ring
  · simp [fullColumns, contMode, fullColumnPoly, col1, Fin.sum_univ_succ,
      he2, he4, he6, k2, k4, k22, cc]
    ring
  · simp [fullColumns, contMode, fullColumnPoly, col2, Fin.sum_univ_succ,
      he2, he4, he6, k2, k4, k22, cc]
    ring

/-- The exact action of `unitMomCont.innerHam` on each of the three retained
`fullColumns` inputs, expanded in the eleven modes. -/
theorem cont_fullColumns_action (j : Fin 3) :
    unitMomCont.innerHam ⟨pgLp (contMode (retained j)), pgLp_mem_core _⟩ =
      pgLp (∑ k : Fin 11, C ((fullColumns k j).re : ℂ) * contMode k) := by
  rw [fullColumnPoly_eq j]
  exact cont_fullColumns_action_apply j


/-! ## The Hermite Gram of the eleven modes -/

private def e (i : Fin 4) (n : ℕ) : Fin 4 →₀ ℕ := Finsupp.single i n

private theorem hf2 (i : Fin 4) : hermiteFactor i 2 = X i ^ 2 - 1 := by
  simp [hermiteFactor, hermiteCx, Polynomial.hermite_succ, Polynomial.hermite_zero]
  ring

private theorem hf4 (i : Fin 4) : hermiteFactor i 4 = X i ^ 4 - 6 * X i ^ 2 + 3 := by
  simp [hermiteFactor, hermiteCx, Polynomial.hermite_succ, Polynomial.hermite_zero]
  ring

private theorem hf6 (i : Fin 4) :
    hermiteFactor i 6 = X i ^ 6 - 15 * X i ^ 4 + 45 * X i ^ 2 - 15 := by
  simp [hermiteFactor, hermiteCx, Polynomial.hermite_succ, Polynomial.hermite_zero]
  ring

noncomputable def termList : Fin 11 → List (Fin 4 →₀ ℕ) := ![
  [0],
  [e 0 2],
  [e 1 2, e 2 2, e 3 2],
  [e 0 2 + e 1 2, e 0 2 + e 2 2, e 0 2 + e 3 2],
  [e 0 4],
  [e 0 6],
  [e 0 4 + e 1 2, e 0 4 + e 2 2, e 0 4 + e 3 2],
  [e 1 4, e 2 4, e 3 4],
  [e 1 2 + e 2 2, e 1 2 + e 3 2, e 2 2 + e 3 2],
  [e 0 2 + e 1 4, e 0 2 + e 2 4, e 0 2 + e 3 4],
  [e 0 2 + e 1 2 + e 2 2, e 0 2 + e 1 2 + e 3 2, e 0 2 + e 2 2 + e 3 2]]

noncomputable def modeSum (l : List (Fin 4 →₀ ℕ)) : MvPolynomial (Fin 4) ℂ :=
  (l.map hermiteMv).sum


private theorem pgLp_zero : pgLp (d := 4) (0 : MvPolynomial (Fin 4) ℂ) = 0 :=
  (pgMap (d := 4)).map_zero

private theorem pgMap_modeSum (l : List (Fin 4 →₀ ℕ)) :
    pgMap (modeSum l) = (l.map fun a => pgMap (hermiteMv a)).sum := by
  induction l with
  | nil => simpa [modeSum] using pgLp_zero
  | cons a l ih =>
      rw [show modeSum (a :: l) = hermiteMv a + modeSum l by simp [modeSum, List.sum_cons]]
      rw [map_add, ih]
      rfl

private theorem inner_hermiteMv_eq (a b : Fin 4 →₀ ℕ) :
    inner ℂ (pgLp (hermiteMv a)) (pgLp (hermiteMv b)) =
      if a = b then ((∏ i, ((hermiteInner (a i) (a i) : ℝ) : ℂ))) else 0 := by
  rw [inner_pgLp_hermiteMv]
  by_cases h : a = b
  · subst h
    simp only [if_true]
    push_cast
    rfl
  · rw [if_neg h]
    have hex : ∃ i, a i ≠ b i := by
      by_contra hc
      push_neg at hc
      exact h (Finsupp.ext hc)
    obtain ⟨i, hi⟩ := hex
    have h0 : (∏ j, hermiteInner (a j) (b j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hermiteInner_eq, if_neg hi])
    rw [h0]
    simp

private theorem inner_single_modeSum (x : L2d 4) (m : List (Fin 4 →₀ ℕ)) :
    inner ℂ x (pgMap (modeSum m)) =
      (m.map fun b => inner ℂ x (pgMap (hermiteMv b))).sum := by
  induction m with
  | nil => rw [show modeSum ([] : List (Fin 4 →₀ ℕ)) = 0 by simp [modeSum],
        show pgMap (0 : MvPolynomial (Fin 4) ℂ) = 0 from (pgMap (d := 4)).map_zero]; simp
  | cons b m ih =>
      rw [show modeSum (b :: m) = hermiteMv b + modeSum m by simp [modeSum, List.sum_cons]]
      rw [map_add, inner_add_right, ih]
      simp [List.sum_cons]

private theorem inner_modeSum (l m : List (Fin 4 →₀ ℕ)) :
    inner ℂ (pgMap (modeSum l)) (pgMap (modeSum m)) =
      (l.map fun a => (m.map fun b =>
        inner ℂ (pgMap (hermiteMv a)) (pgMap (hermiteMv b))).sum).sum := by
  induction l with
  | nil => simp [modeSum, pgLp_zero]
  | cons a l ih =>
      rw [show modeSum (a :: l) = hermiteMv a + modeSum l by simp [modeSum, List.sum_cons]]
      rw [map_add, inner_add_left, ih, inner_single_modeSum]
      simp [List.sum_cons]

@[simp] private theorem qi_re_one : (1 : QI).re = (1 : ℚ) := rfl

@[simp] private theorem qi_re_ofNat (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : QI).re = (OfNat.ofNat n : ℚ) := rfl

private theorem contMode_eq (i : Fin 11) : contMode i = modeSum (termList i) := by
  fin_cases i <;>
    simp [contMode, he2, he4, he6, k2, k4, k22, termList, modeSum, e, hermiteMv,
      Fin.prod_univ_four, hermiteFactor_zero, hf2, hf4, hf6] <;> ring_nf

set_option maxHeartbeats 4000000 in
theorem contMode_inner (i j : Fin 11) :
    inner ℂ (pgLp (contMode i)) (pgLp (contMode j)) =
      ((fullMetric i j).re : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ 4 := by
  rw [contMode_eq i, contMode_eq j, ← HermiteProductCore.pgMap_apply,
    ← HermiteProductCore.pgMap_apply]
  rw [inner_modeSum]
  fin_cases i <;> fin_cases j <;>
    simp +decide [termList, e, inner_hermiteMv_eq, hermiteInner_eq, fullMetric,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne, Fin.prod_univ_four, QuadraticAlgebra.re_one,
      QuadraticAlgebra.re_ofNat] <;> ring_nf

/-- The Gram matrix in the probability-normalized Gaussian measure.  The raw
`L²` pairing carries the common factor `(√(2π))⁴`, recorded in `contMode_inner`. -/
theorem contMode_inner_normalized (i j : Fin 11) :
    inner ℂ (pgLp (contMode i)) (pgLp (contMode j)) /
        ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ 4 = ((fullMetric i j).re : ℂ) := by
  rw [contMode_inner]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hs4 : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ 4 ≠ 0 := pow_ne_zero 4 hs
  field_simp [hs4]

/-! ## Synthesis of an arbitrary eleven-mode coefficient vector -/

/-- Reconstruct a physical vector from eleven complex mode coefficients. -/
noncomputable def synthesize (c : Fin 11 → ℂ) : L2d 4 :=
  ∑ i, c i • pgLp (contMode i)

/-- The Gram identity for an arbitrary eleven-mode superposition. -/
theorem synthesis_inner (a b : Fin 11 → ℂ) :
    inner ℂ (synthesize a) (synthesize b) =
      (∑ i, ∑ j, (starRingEnd ℂ) (a i) * ((fullMetric i j).re : ℂ) * b j) *
        ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ 4 := by
  simp only [synthesize, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    contMode_inner, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end

end BookProof.Phi4.MomRankTwo
