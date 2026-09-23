import Mathlib
import BookProof.ChapterSmBrstGhost

/-!
# A concrete Standard-Model gauge representation, and a fully instantiated BRST charge

`BookProof.ChapterSmBrstGhost` proves that the Standard-Model BRST charge

```
Ω = Σ_a c^a G_a − ½ Σ f_{abc} c^a c^b b_c ,     G_a = −i dΓ(T_a)
```

is nilpotent *whenever* the twelve matter generators `T_a` close with the structure
constants `smStruct f₃` of `su(3) ⊕ su(2) ⊕ u(1)`.  This module removes the last hypothesis
that is a statement about a representation rather than about the Lie algebra: it builds a
**concrete** family of twelve generators — one coloured weak doublet, i.e. the internal
space `ℂ³ ⊗ ℂ²` of a quark multiplet at one plane-wave momentum, with hypercharge `y` —
and proves that it closes with exactly those structure constants.

## What is proved

* `pauli`, `su2gen` — the Pauli matrices and the `su(2)` generators `τ_k / 2`, with
  **`su2gen_closes`**: `[τ_j/2, τ_k/2] = i ε_{jkl} τ_l/2`, i.e. they close with the
  Levi-Civita structure constants `su2Struct` of `BookProof.ChapterSmBrstGhost`.
* `smGenP` — the twelve generators on the internal space `ℂ³ ⊗ ℂ²`: the eight gluon
  directions `T_a ⊗ 1`, the three weak directions `1 ⊗ τ_k/2` and the hypercharge `y·1`;
  **`smGenP_closes`** — they close with `sumStruct f₃ (sumStruct su2Struct u1Struct)`, the
  direct-sum structure constants (a bracket never leaves its summand, the colour and weak
  factors commute, and the hypercharge is central).
* `smGen` — the same twelve generators on the six matter modes `Fin 6 ≃ Fin 3 × Fin 2`, with
  **`smGen_closes`**: `ClosesWithStructureConstants (smGen S₃ y) (smStruct f₃)`.
* **`sm_brst_nilpotent_rep`** — the Standard-Model BRST charge of this concrete multiplet,
  on the eighteen-mode Fock space (six matter modes and twelve ghosts), squares to zero.
  Its only remaining inputs are the two defining relations of the `su(3)` generators
  themselves (`TraceOrthonormal`, `ClosesWithStructureConstants`), from which the
  antisymmetry and the Jacobi identity of `f₃` are *derived*, through
  `BookProof.YangMillsSU3.structureConstant_antisymm_swap` and
  `BookProof.YangMillsSU3.structureConstant_jacobi`.
* `sm_brst_nilpotent_of_su3_relations` — the same reduction of the hypotheses for an
  arbitrary matter representation.

## Honest boundary

The multiplet is one coloured weak doublet at one momentum: the mode set is finite, as in
`BookProof.ChapterSmBrstGhost`.  The `su(3)` generators enter through their two defining
relations rather than through the explicit Gell-Mann table, and nothing is claimed about the
size of the BRST cohomology.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmGaugeRep

open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.SmBrstGhost

noncomputable section

/-! ## 1. The `su(2)` generators -/

/-- The three Pauli matrices. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- The `su(2)` generators in the physics normalization, `τ_k / 2`. -/
def su2gen (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • pauli k

/-- **The weak generators close with the Levi-Civita structure constants**:
`[τ_j/2, τ_k/2] = i ε_{jkl} τ_l/2`. -/
theorem su2gen_closes : ClosesWithStructureConstants su2gen su2Struct := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    (rw [Fin.sum_univ_three]
     ext i j
     fin_cases i <;> fin_cases j <;>
       norm_num +decide [su2gen, pauli, su2Struct, epsZ, Matrix.mul_apply, Fin.sum_univ_two,
         Matrix.one_apply, Complex.ext_iff, Matrix.smul_apply, Matrix.cons_val_two,
         Matrix.tail_cons, Matrix.head_cons])

/-! ## 2. The twelve generators on the internal space `ℂ³ ⊗ ℂ²` -/

variable {S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

/-- The Kronecker product distributes over a difference in its left factor. -/
theorem sub_kronecker (A B : Matrix (Fin 3) (Fin 3) ℂ) (C : Matrix (Fin 2) (Fin 2) ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext i j; simp [Matrix.kroneckerMap_apply, sub_mul]

/-- The Kronecker product distributes over a difference in its right factor. -/
theorem kronecker_sub (C : Matrix (Fin 3) (Fin 3) ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    C ⊗ₖ (A - B) = C ⊗ₖ A - C ⊗ₖ B := by
  ext i j; simp [Matrix.kroneckerMap_apply, mul_sub]

/-- The Kronecker product distributes over a finite sum in its left factor. -/
theorem sum_kronecker_left {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, (A i ⊗ₖ B) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_kronecker, ih]

/-- The Kronecker product distributes over a finite sum in its right factor. -/
theorem kronecker_sum_right {ι : Type*} (s : Finset ι) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, (A ⊗ₖ B i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.kronecker_add, ih]

/-- **The twelve Standard-Model generators on the internal space of one coloured weak
doublet**: `T_a ⊗ 1` in the eight gluon directions, `1 ⊗ τ_k/2` in the three weak
directions, and the central hypercharge `y·1`. -/
def smGenP (S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (y : ℝ) :
    (Fin 8 ⊕ (Fin 3 ⊕ Fin 1)) → Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ
  | Sum.inl a => S3 a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | Sum.inr (Sum.inl k) => (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ su2gen k
  | Sum.inr (Sum.inr _) => ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)

/-- The hypercharge generator is central. -/
theorem smGenP_hyp_comm (y : ℝ) (M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) * M
      = M * ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- The colour and weak factors commute. -/
theorem smGenP_col_iso_comm (A : Matrix (Fin 3) (Fin 3) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ B)
      = ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- **The concrete generators close with the direct-sum structure constants of
`su(3) ⊕ su(2) ⊕ u(1)`.** -/
theorem smGenP_closes (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ)
    (A B : Fin 8 ⊕ (Fin 3 ⊕ Fin 1)) :
    smGenP S3 y A * smGenP S3 y B - smGenP S3 y B * smGenP S3 y A
      = Complex.I • ∑ C, ((sumStruct f3 (sumStruct su2Struct u1Struct) A B C : ℝ) : ℂ)
          • smGenP S3 y C := by
  revert A B
  have hzero : ∀ A B : Fin 8 ⊕ (Fin 3 ⊕ Fin 1),
      smGenP S3 y A * smGenP S3 y B - smGenP S3 y B * smGenP S3 y A = 0 →
      (∀ D, sumStruct f3 (sumStruct su2Struct u1Struct) A B D = 0) →
      smGenP S3 y A * smGenP S3 y B - smGenP S3 y B * smGenP S3 y A
        = Complex.I • ∑ D, ((sumStruct f3 (sumStruct su2Struct u1Struct) A B D : ℝ) : ℂ)
            • smGenP S3 y D := by
    intro A B h0 hf
    rw [h0]
    refine (smul_eq_zero_of_right _ ?_).symm
    refine Finset.sum_eq_zero fun D _ => ?_
    rw [hf D]
    simp
  intro A B
  rcases A with a | (k | u) <;> rcases B with b | (l | v)
  · -- colour / colour
    have hcomm : smGenP S3 y (Sum.inl a) * smGenP S3 y (Sum.inl b)
        - smGenP S3 y (Sum.inl b) * smGenP S3 y (Sum.inl a)
        = (S3 a * S3 b - S3 b * S3 a) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [smGenP, ← Matrix.mul_kronecker_mul, Matrix.one_mul, sub_kronecker]
    rw [hcomm, hS3 a b, Matrix.smul_kronecker, sum_kronecker_left]
    congr 1
    rw [Fintype.sum_sum_type]
    have h2 : ∑ D : Fin 3 ⊕ Fin 1,
        ((sumStruct f3 (sumStruct su2Struct u1Struct) (Sum.inl a) (Sum.inl b)
          (Sum.inr D) : ℝ) : ℂ) • smGenP S3 y (Sum.inr D) = 0 := by
      refine Finset.sum_eq_zero fun D _ => ?_
      rcases D with D | D <;> simp [sumStruct]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_kronecker]
    rfl
  · -- colour / weak
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact smGenP_col_iso_comm _ _
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- colour / hypercharge
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact (smGenP_hyp_comm y _).symm
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- weak / colour
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact (smGenP_col_iso_comm _ _).symm
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- weak / weak
    have hcomm : smGenP S3 y (Sum.inr (Sum.inl k)) * smGenP S3 y (Sum.inr (Sum.inl l))
        - smGenP S3 y (Sum.inr (Sum.inl l)) * smGenP S3 y (Sum.inr (Sum.inl k))
        = (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ (su2gen k * su2gen l - su2gen l * su2gen k) := by
      simp only [smGenP, ← Matrix.mul_kronecker_mul, Matrix.one_mul, kronecker_sub]
    rw [hcomm, su2gen_closes k l, Matrix.kronecker_smul, kronecker_sum_right]
    congr 1
    rw [Fintype.sum_sum_type]
    have h1 : ∑ D : Fin 8,
        ((sumStruct f3 (sumStruct su2Struct u1Struct) (Sum.inr (Sum.inl k))
          (Sum.inr (Sum.inl l)) (Sum.inl D) : ℝ) : ℂ) • smGenP S3 y (Sum.inl D) = 0 :=
      Finset.sum_eq_zero fun D _ => by simp [sumStruct]
    rw [h1, zero_add, Fintype.sum_sum_type]
    have h2 : ∑ D : Fin 1,
        ((sumStruct f3 (sumStruct su2Struct u1Struct) (Sum.inr (Sum.inl k))
          (Sum.inr (Sum.inl l)) (Sum.inr (Sum.inr D)) : ℝ) : ℂ)
          • smGenP S3 y (Sum.inr (Sum.inr D)) = 0 :=
      Finset.sum_eq_zero fun D _ => by simp [sumStruct]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.kronecker_smul]
    rfl
  · -- weak / hypercharge
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact (smGenP_hyp_comm y _).symm
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- hypercharge / colour
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact smGenP_hyp_comm y _
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- hypercharge / weak
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact smGenP_hyp_comm y _
    · intro D; rcases D with D | (D | D) <;> rfl
  · -- hypercharge / hypercharge
    refine hzero _ _ ?_ ?_
    · rw [sub_eq_zero]
      exact smGenP_hyp_comm y _
    · intro D; rcases D with D | (D | D) <;> rfl

/-! ## 3. The generators on the six matter modes -/

/-- The colour–isospin mode labelling: the `3 × 2 = 6` modes of one coloured weak doublet at
one plane-wave momentum. -/
def internalEquiv : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv

/-- The matrix algebra of the internal space, transported to the six matter modes. -/
def toModes : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ ≃ₐ[ℂ] Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ internalEquiv

/-- **The twelve Standard-Model generators on the six matter modes.** -/
def smGen (S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (y : ℝ) (a : Fin 12) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  toModes (smGenP S3 y (smIdxEquiv a))

/-- **The concrete Standard-Model generators close with `smStruct f₃`** — the hypothesis the
BRST construction of `BookProof.ChapterSmBrstGhost` needs. -/
theorem smGen_closes (hS3 : ClosesWithStructureConstants S3 f3) (y : ℝ) :
    ClosesWithStructureConstants (smGen S3 y) (smStruct f3) := by
  intro a b
  have hP := smGenP_closes hS3 y (smIdxEquiv a) (smIdxEquiv b)
  have hmap : smGen S3 y a * smGen S3 y b - smGen S3 y b * smGen S3 y a
      = toModes (smGenP S3 y (smIdxEquiv a) * smGenP S3 y (smIdxEquiv b)
        - smGenP S3 y (smIdxEquiv b) * smGenP S3 y (smIdxEquiv a)) := by
    rw [map_sub, map_mul, map_mul]
    rfl
  rw [hmap, hP, map_smul, map_sum]
  refine congrArg (fun M => Complex.I • M) ?_
  refine (Fintype.sum_equiv smIdxEquiv
    (fun c => ((smStruct f3 a b c : ℝ) : ℂ) • smGen S3 y c)
    (fun C => toModes (((sumStruct f3 (sumStruct su2Struct u1Struct) (smIdxEquiv a)
        (smIdxEquiv b) C : ℝ) : ℂ) • smGenP S3 y C))
    (fun c => by simp only [smGen, map_smul]; rfl)).symm

/-! ## 4. The fully instantiated BRST charge -/

/-- **Nilpotency of the Standard-Model BRST charge from the defining relations of the gauge
algebra alone.**  For any matter representation of the twelve generators, the antisymmetry
and the Jacobi identity of the `su(3)` structure constants — the two remaining hypotheses of
`BookProof.SmBrstGhost.smBrstCharge_nilpotent` — follow from trace-orthonormality and
closure of the `su(3)` generators. -/
theorem sm_brst_nilpotent_of_su3_relations {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    (hS3 : TraceOrthonormal S3) (hf3 : ClosesWithStructureConstants S3 f3)
    (hT : ClosesWithStructureConstants T (smStruct f3)) :
    smBrstCharge m T f3 * smBrstCharge m T f3 = 0 :=
  smBrstCharge_nilpotent hT (structureConstant_antisymm_swap hS3 hf3)
    (structureConstant_jacobi hS3 hf3)

/-- **The Standard-Model BRST charge of one coloured weak doublet is nilpotent.**  On the
eighteen-mode fermionic Fock space — six matter modes (colour ⊗ weak isospin) and the twelve
ghosts of `su(3) ⊕ su(2) ⊕ u(1)` — the charge
`Ω = Σ_a c^a G_a − ½ Σ f_{abc} c^a c^b b_c` built from the concrete Gauss-law generators
`G_a = −i dΓ(T_a)` satisfies `Ω² = 0`.  The only inputs are the two defining relations of
the `su(3)` generators. -/
theorem sm_brst_nilpotent_rep (hS3 : TraceOrthonormal S3)
    (hf3 : ClosesWithStructureConstants S3 f3) (y : ℝ) :
    smBrstCharge 6 (smGen S3 y) f3 * smBrstCharge 6 (smGen S3 y) f3 = 0 :=
  sm_brst_nilpotent_of_su3_relations hS3 hf3 (smGen_closes hf3 y)

end

end BookProof.SmGaugeRep
