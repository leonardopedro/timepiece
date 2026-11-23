import BookProof.Phi4.ChapterScalarMehler

/-!
# The continuous-coordinate λφ⁴ vacuum column

The independent-jet model has one field coordinate and three jet coordinates.
At unit width and unit parameters this file computes the full action on the
Mehler Gaussian, keeping the quartic field mode and the three quadratic jet
modes. The residual weights are the factorial weights used by the one-site
rank-one estimate.
-/

namespace BookProof.Phi4

open MvPolynomial HermiteProductCore HermiteProductBasis

noncomputable section

/-- The continuous-coordinate jet model at unit width and unit parameters. -/
def unitJet : Model 4 1 4 :=
  jetModel ⟨1, by norm_num, 1, by norm_num⟩

/-- The form sum splits into the double-well wall in the field coordinate and
one quadratic potential in each of the three jet coordinates. -/
theorem jet_forms (p : MvPolynomial (Fin 4) ℂ) :
    ∑ j, unitJet.form j * (unitJet.form j * p) =
      C (1 / 2 : ℂ) * (X 0 ^ 2 - 1) * ((X 0 ^ 2 - 1) * p) +
        X 1 * (X 1 * p) + X 2 * (X 2 * p) + X 3 * (X 3 * p) := by
  have hw : unitJet.form 0 =
      C (Real.sqrt (1 / 2) : ℂ) * (X 0 * X 0 - 1) := by
    change wall 0 _ _ = _
    simp [wall, smul_eq_C_mul]
  have h1 : unitJet.form 1 = (X 1 : MvPolynomial (Fin 4) ℂ) := by
    change (jetModel ⟨1, by norm_num, 1, by norm_num⟩).form (1 : Fin 4) = _
    rfl
  have h2 : unitJet.form 2 = (X 2 : MvPolynomial (Fin 4) ℂ) := by
    change (jetModel ⟨1, by norm_num, 1, by norm_num⟩).form (2 : Fin 4) = _
    rfl
  have h3 : unitJet.form 3 = (X 3 : MvPolynomial (Fin 4) ℂ) := by
    change (jetModel ⟨1, by norm_num, 1, by norm_num⟩).form (3 : Fin 4) = _
    rfl
  rw [Fin.sum_univ_four, hw, h1, h2, h3]
  ring_nf
  simp only [← map_pow, ← Complex.ofReal_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  push_cast
  apply MvPolynomial.funext
  intro x
  simp
  ring

/-- The full action on the unnormalized Gaussian, in the unnormalized product
Hermites. The constant is 17/8, the field coefficients are 7/8 and 1/4, and
each jet coefficient is 1/2. -/
theorem unitJet_vacuum_column :
    unitJet.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ =
      pgLp (C (17 / 8 : ℂ) + C (7 / 8 : ℂ) * (X 0 ^ 2 - 1) +
        C (1 / 4 : ℂ) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3) +
        C (1 / 2 : ℂ) * (X 1 ^ 2 - 1) +
        C (1 / 2 : ℂ) * (X 2 ^ 2 - 1) +
        C (1 / 2 : ℂ) * (X 3 ^ 2 - 1)) := by
  rw [Model.innerHam_pgLp, jet_forms, Fin.sum_univ_one]
  congr 1
  have hmom : unitJet.momentum 0 = (0 : Fin 4) := rfl
  rw [hmom, BookProof.YangMillsNonAbelianEsa.momOp_momOp_d]
  simp [QgHermiteFriedrichs.coreD, smul_eq_C_mul, Derivation.leibniz]
  apply MvPolynomial.funext
  intro x
  simp
  ring

/-- Factorial-weighted squared residual of the jet vacuum column. The factors
2! and 4! are the squared norms of the unnormalized Hermites; the final factor
3 is the number of independent jet directions. -/
theorem jet_variance_weights :
    (7 / 8 : ℝ)^2 * Nat.factorial 2 + (1 / 4 : ℝ)^2 * Nat.factorial 4 +
      3 * ((1 / 2 : ℝ)^2 * Nat.factorial 2) = 145 / 32 := by
  norm_num [Nat.factorial]

end

end BookProof.Phi4
