import Mathlib
import BookProof.Sm.ChapterSmFullYukawaData
import BookProof.Sm.ChapterSmFullMatterHamiltonian

/-!
# The P1 Yukawa dictionary in the occupation-basis coefficient matrices

Work order: `SM_ESA_COMPLETION_PLAN.md` §4 **P1** → **P2**.  P2's normal form

```text
h_SM = Σⱼ πⱼ ⊗ Aⱼ + Σⱼ πⱼ² ⊗ Bⱼ + Σⱼ uⱼ ⊗ Jⱼ + 1 ⊗ M₀
```

carries internal coefficient *matrices*; P1 supplies the internal *operators* — the four real
Higgs components `yukawaPair (higgsGen a) Y` and the hermitianized mass/Yukawa insertion.  This
module reads those operators in the occupation basis of the matter Fock space, which is exactly
what the normal form needs, and proves the two structural hypotheses of P2,
`HermitianCoeffs` and `ParityGradedCoeffs`, hold for the result.

## What is built

* `fockBasis`, `fockMatrix` — the occupation basis `|S⟩` and the matrix of an internal operator
  in it, `fockMatrix A S T = ⟪|S⟩, A |T⟩⟫`;
* **`fockMatrix_star`** — a symmetric internal operator has a Hermitian coefficient matrix;
* **`fockMatrix_parity`** — an internal operator commuting with fermion parity has a
  parity-graded coefficient matrix (`fockSign S * M S T = M S T * fockSign T`);
* `SmInternalData` — the internal data of the P1 dictionary (the position of each real Higgs
  component among the 163 oscillator coordinates, the four second-quantized Higgs generators, the
  mass/Yukawa insertion, and their Hermiticity);
* `SmInternalData.toNormalForm` — the resulting `SmNormalFormData`: the coordinate family carries
  the Higgs generators, the mass slot the Yukawa insertion, and the two bosonic families of
  derivatives carry no internal matrix;
* **`SmInternalData.toNormalForm_hermitian`** and **`toNormalForm_parity`** — P2's
  `HermitianCoeffs` and `ParityGradedCoeffs`, derived from
  `matterBilin_symmetric`/`matterBilin_parity` and the P1 Hermiticity lemmas, so P2's
  `smNormalForm_symmetricOn` and `smNormalForm_parity` apply to the P1 data;
* **`toNormalForm_coord_null`/`toNormalForm_kinetic_null`** — the two derivative families are the
  zero matrices: the internal factor carries no derivative, which is the "no added kinetic
  derivatives" clause of the plan.

## Boundary

The map from the four real Higgs components to coordinates of `ℝ¹⁶³` is carried as the data
`pos : Fin 4 → Fin 163`; nothing here asserts that `pos` is injective or that the `163`
coordinates are exhausted, and no mass value is computed from the P1 couplings — the statement is
structural: *the P1 dictionary satisfies P2's hypotheses in the occupation basis*.
-/

namespace BookProof.SmFullYukawaCoeffs

open BookProof.SmCar BookProof.SmFullMatter BookProof.SmMatter BookProof.SmFullYukawa
open BookProof.SmGaugeRep BookProof.FarisLavine

noncomputable section

/-! ## 1. The occupation basis and the matrix of an internal operator -/

/-- **The occupation-basis vector** `|S⟩`. -/
def fockBasis (S : Finset (Fin 96)) : MatterFock :=
  WithLp.toLp 2 (fun T => if T = S then (1 : ℂ) else 0)

@[simp] theorem fockBasis_self (S : Finset (Fin 96)) : fockBasis S S = 1 := by
  simp [fockBasis]

theorem fockBasis_of_ne {S T : Finset (Fin 96)} (h : T ≠ S) : fockBasis S T = 0 := by
  simp [fockBasis, h]

/-- **The coefficient matrix of an internal operator in the occupation basis.** -/
def fockMatrix (A : MatterFock →ₗ[ℂ] MatterFock) :
    Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ :=
  fun S T => A (fockBasis T) S

/-- The matrix entries are the matrix elements in the occupation basis. -/
theorem fockMatrix_eq_inner (A : MatterFock →ₗ[ℂ] MatterFock) (S T : Finset (Fin 96)) :
    fockMatrix A S T = (inner ℂ (fockBasis S) (A (fockBasis T)) : ℂ) := by
  rw [inner_eq_sum, Finset.sum_eq_single S]
  · simp [fockMatrix]
  · intro b _ hb
    rw [fockBasis_of_ne hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ S) h

set_option maxRecDepth 4000 in
-- the `PiLp` inner product and its conjugation symmetry are deep unfolds
/-- **A symmetric internal operator has a Hermitian coefficient matrix.** -/
theorem fockMatrix_star (A : MatterFock →ₗ[ℂ] MatterFock)
    (hA : ∀ ψ φ : MatterFock, (inner ℂ (A ψ) φ : ℂ) = inner ℂ ψ (A φ))
    (S T : Finset (Fin 96)) :
    star (fockMatrix A S T) = fockMatrix A T S := by
  rw [fockMatrix_eq_inner, fockMatrix_eq_inner]
  have hconj : star (inner ℂ (fockBasis S) (A (fockBasis T)) : ℂ)
      = (inner ℂ (A (fockBasis T)) (fockBasis S) : ℂ) := by
    rw [Complex.star_def, ← inner_conj_symm (A (fockBasis T)) (fockBasis S)]
  rw [hconj, hA (fockBasis T) (fockBasis S)]

/-! ## 2. Parity grading of the coefficient matrix -/

/-- Parity acts on the occupation basis by the sign. -/
theorem fockBasis_parity (S : Finset (Fin 96)) :
    fockParity (fockBasis S) = fockSign S • fockBasis S := by
  refine WithLp.ofLp_injective 2 (funext fun T => ?_)
  by_cases h : T = S
  · subst h
    simp [fockParity_apply, fockBasis, PiLp.smul_apply]
  · rw [fockParity_apply, fockBasis_of_ne h, PiLp.smul_apply, fockBasis_of_ne h, smul_zero,
      mul_zero]

/-- **An internal operator commuting with parity has a parity-graded coefficient matrix.** -/
theorem fockMatrix_parity (A : MatterFock →ₗ[ℂ] MatterFock)
    (hA : fockParity ∘ₗ A = A ∘ₗ fockParity) (S T : Finset (Fin 96)) :
    fockSign S * fockMatrix A S T = fockMatrix A S T * fockSign T := by
  have hfun := LinearMap.congr_fun hA (fockBasis T)
  simp only [LinearMap.comp_apply] at hfun
  have h1 : (fockParity (A (fockBasis T))) S = fockSign S * fockMatrix A S T := by
    rw [fockParity_apply, fockMatrix]
  have h2 : (A (fockParity (fockBasis T))) S = fockSign T * fockMatrix A S T := by
    rw [fockBasis_parity, map_smul, PiLp.smul_apply, fockMatrix, smul_eq_mul]
  have hpar : fockSign S * fockMatrix A S T = fockSign T * fockMatrix A S T := by
    rw [← h1, hfun]
    exact h2
  by_cases hs : fockSign S = fockSign T
  · rw [hs, mul_comm]
  · have hz : fockMatrix A S T = 0 := by
      have hne : fockSign S - fockSign T ≠ 0 := sub_ne_zero.mpr hs
      have h0 : (fockSign S - fockSign T) * fockMatrix A S T = 0 := by
        rw [sub_mul, hpar, sub_self]
      exact (mul_eq_zero.mp h0).resolve_left hne
    rw [hz, mul_zero, zero_mul]

/-- A finite sum of Hermitian matrices is Hermitian, entrywise. -/
theorem matrix_sum_hermitian {ι : Type*} [Fintype ι]
    (M : ι → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (h : ∀ (i : ι) (S T : Finset (Fin 96)), star (M i S T) = M i T S)
    (S T : Finset (Fin 96)) :
    star ((∑ i, M i) S T) = (∑ i, M i) T S := by
  rw [Finset.sum_apply, Finset.sum_apply, star_sum, Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => h i S T

/-- A finite sum of parity-graded matrices is parity-graded, entrywise. -/
theorem matrix_sum_parity {ι : Type*} [Fintype ι]
    (M : ι → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (h : ∀ (i : ι) (S T : Finset (Fin 96)), fockSign S * M i S T = M i S T * fockSign T)
    (S T : Finset (Fin 96)) :
    fockSign S * (∑ i, M i) S T = (∑ i, M i) S T * fockSign T := by
  rw [Finset.sum_apply, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => h i S T

/-! ## 3. The P1 internal data and the normal form it produces -/

/-- **The internal data of the P1 Yukawa dictionary**: where each real Higgs component sits among
the `163` oscillator coordinates, the four second-quantized Higgs generators, the second-quantized
mass/Yukawa insertion, and the Hermiticity of all five. -/
structure SmInternalData where
  /-- the oscillator coordinate of the `a`-th real Higgs component -/
  pos : Fin 4 → Fin 163
  /-- the second-quantized `a`-th Higgs generator `yukawaPair (higgsGen a) Y` -/
  higgs : Fin 4 → Matrix SmMatterIndex SmMatterIndex ℂ
  /-- the second-quantized mass/Yukawa insertion -/
  mass : Matrix SmMatterIndex SmMatterIndex ℂ
  /-- the Higgs generators are Hermitian -/
  higgsHermitian : ∀ a : Fin 4, (higgs a).conjTranspose = higgs a
  /-- the Yukawa insertion is Hermitian -/
  massHermitian : mass.conjTranspose = mass

/-- **The normal-form data of the P1 dictionary**: the four real Higgs components are coordinate
terms, the Yukawa insertion is the constant term, and no internal matrix accompanies a bosonic
derivative. -/
def SmInternalData.toNormalForm (D : SmInternalData) : SmNormalFormData where
  mom := fun _ => 0
  kinetic := fun _ => 0
  coord := fun j =>
    ∑ a : Fin 4, if D.pos a = j then fockMatrix (matterBilin (D.higgs a)) else 0
  mass := fockMatrix (matterBilin D.mass)

/-- The two derivative families of the P1 dictionary are the zero matrices. -/
theorem SmInternalData.toNormalForm_mom_null (D : SmInternalData) (j : Fin 163) :
    D.toNormalForm.mom j = 0 := rfl

theorem SmInternalData.toNormalForm_kinetic_null (D : SmInternalData) (j : Fin 163) :
    D.toNormalForm.kinetic j = 0 := rfl

/-- **P2's `HermitianCoeffs` holds for the P1 dictionary**, by `matterBilin_symmetric` and the P1
Hermiticity lemmas, read in the occupation basis with `fockMatrix_star`. -/
theorem SmInternalData.toNormalForm_hermitian (D : SmInternalData) :
    HermitianCoeffs D.toNormalForm := by
  have hgen : ∀ a : Fin 4,
      ∀ S T : Finset (Fin 96),
        star (fockMatrix (matterBilin (D.higgs a)) S T)
          = fockMatrix (matterBilin (D.higgs a)) T S :=
    fun a => fockMatrix_star _ (matterBilin_symmetric (D.higgsHermitian a))
  refine ⟨fun j S T => ?_, fun j S T => ?_, fun j S T => ?_, fun S T => ?_⟩
  · simp [SmInternalData.toNormalForm]
  · simp [SmInternalData.toNormalForm]
  · exact matrix_sum_hermitian
      (fun a => if D.pos a = j then fockMatrix (matterBilin (D.higgs a)) else 0)
      (fun a S T => by
        dsimp only
        by_cases h : D.pos a = j
        · rw [if_pos h]
          exact hgen a S T
        · rw [if_neg h]
          simp) S T
  · exact fockMatrix_star _ (matterBilin_symmetric D.massHermitian) S T

/-- **P2's `ParityGradedCoeffs` holds for the P1 dictionary**, by `matterBilin_parity` and
`fockMatrix_parity`. -/
theorem SmInternalData.toNormalForm_parity (D : SmInternalData) :
    ParityGradedCoeffs D.toNormalForm := by
  have hgen : ∀ a : Fin 4,
      ∀ S T : Finset (Fin 96),
        fockSign S * fockMatrix (matterBilin (D.higgs a)) S T
          = fockMatrix (matterBilin (D.higgs a)) S T * fockSign T :=
    fun a => fockMatrix_parity _ (matterBilin_parity (D.higgs a))
  refine ⟨fun j S T => ?_, fun j S T => ?_, fun j S T => ?_, fun S T => ?_⟩
  · simp [SmInternalData.toNormalForm]
  · simp [SmInternalData.toNormalForm]
  · exact matrix_sum_parity
      (fun a => if D.pos a = j then fockMatrix (matterBilin (D.higgs a)) else 0)
      (fun a S T => by
        dsimp only
        by_cases h : D.pos a = j
        · rw [if_pos h]
          exact hgen a S T
        · rw [if_neg h]
          simp) S T
  · exact fockMatrix_parity _ (matterBilin_parity D.mass) S T

/-- **The normal form built from the P1 Yukawa dictionary is symmetric on the common core.** -/
theorem SmInternalData.toNormalForm_symmetricOn (D : SmInternalData) :
    SymmetricOn SmCoupledCore (smNormalForm D.toNormalForm) :=
  smNormalForm_symmetricOn D.toNormalForm D.toNormalForm_hermitian

end

end BookProof.SmFullYukawaCoeffs
