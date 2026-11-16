import Mathlib
import BookProof.Sm.ChapterParity
import BookProof.Sm.ChapterSmBrstGhost

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

open BookProof.SmCar

/-! ## 5. What one generator does to a ghost-free state

`ChapterSmQuartet` §20 reduces the ghost-parity no-ghost condition to a single matrix entry: the
charge kills a ghost-free state iff every Gauss generator does.  This section supplies that entry at
the doublet, so the refutation is a theorem about `smGen` rather than a hypothesis about it.

The work is in evaluating `G_a` on an occupation state.  `fermiBilin (embedMatter m M)` only sees the
matter block (`fermiBilin_embedMatter`), so on a state occupying one matter mode it is that column of
`M` (`fermiBilin_embedMatter_diagonal`); for the hypercharge generator, which is a multiple of the
identity, the column is the state itself.  Hence `G_11 (occ {0}) = −i y · occ {0}`, nonzero exactly
when the hypercharge is.  That is `matterGen_smGen_hyper_occ_ne_zero` — the matrix entry §20 asks
for, at the model's own representation. -/

/-- The matter block of `embedMatter` reads off the entries of `M` on the matter modes, which are
`Fin.castAdd 12 i`. -/
theorem embedMatter_apply_matter {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    embedMatter m M (Fin.castAdd 12 i) (Fin.castAdd 12 j) = M i j := by
  simp [embedMatter, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks,
    finSumFinEquiv]

/-- The matter block is zero in a ghost column. -/
theorem embedMatter_apply_ghost_col {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i : Fin (m + 12))
    (b : Fin 12) : embedMatter m M i (Fin.natAdd m b) = 0 :=
  embedMatter_col_ghost m M b i

/-- The matter block is zero in a ghost row. -/
theorem embedMatter_apply_ghost_row {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (j : Fin (m + 12))
    (b : Fin 12) : embedMatter m M (Fin.natAdd m b) j = 0 :=
  embedMatter_row_ghost m M b j

/-- **`dΓ` of an embedded matter matrix only touches the matter modes.**  Reindexing the two mode
sums by `Fin m ⊕ Fin 12` leaves the matter block, and the ghost rows and columns of that block are
zero. -/
theorem fermiBilin_embedMatter {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (ψ : FermiFock (m + 12)) :
    fermiBilin (embedMatter m M) ψ
      = ∑ i : Fin m, ∑ j : Fin m,
          M i j • creat (Fin.castAdd 12 i) (annih (Fin.castAdd 12 j) ψ) := by
  rw [fermiBilin_apply]
  have hsplit : ∀ F : Fin (m + 12) → FermiFock (m + 12),
      (∑ i : Fin (m + 12), F i) = ∑ u : Fin m ⊕ Fin 12, F (finSumFinEquiv u) := by
    intro F
    exact (Fintype.sum_equiv finSumFinEquiv _ _ (fun _ => rfl)).symm
  simp only [hsplit, Fintype.sum_sum_type, finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right, embedMatter_apply_ghost_col,
    embedMatter_apply_ghost_row, zero_smul, Finset.sum_const_zero, add_zero,
    embedMatter_apply_matter]

/-- For a diagonal one-particle matrix the embedded second quantization is the sum of the matter
occupation numbers, weighted by the diagonal entries. -/
theorem fermiBilin_embedMatter_diagonal {m : ℕ} (e : Fin m → ℂ) (ψ : FermiFock (m + 12)) :
    fermiBilin (embedMatter m (Matrix.diagonal e)) ψ
      = ∑ i : Fin m, e i • creat (Fin.castAdd 12 i) (annih (Fin.castAdd 12 i) ψ) := by
  rw [fermiBilin_embedMatter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **On a single occupied matter mode the embedded second quantization is the column of `M`.**  For
`M` a multiple of the identity the column is the state itself. -/
theorem fermiBilin_embedMatter_scalar_occ {m : ℕ} (y : ℂ) (i₀ : Fin m) :
    fermiBilin (embedMatter m (y • (1 : Matrix (Fin m) (Fin m) ℂ)))
        (occ ({Fin.castAdd 12 i₀} : Finset (Fin (m + 12))))
      = y • occ ({Fin.castAdd 12 i₀} : Finset (Fin (m + 12))) := by
  rw [Matrix.smul_one_eq_diagonal, fermiBilin_embedMatter_diagonal]
  rw [Finset.sum_eq_single i₀]
  · rw [occupation_occ, if_pos (Finset.mem_singleton_self _)]
  · intro b _ hb
    have hne : Fin.castAdd 12 b ≠ Fin.castAdd 12 i₀ := by
      intro hh
      exact hb (Fin.ext (by simpa using congrArg Fin.val hh))
    rw [occupation_occ, if_neg (by simpa using hne), smul_zero]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

/-- The hypercharge generator of the doublet is `y` times the identity on the six matter modes. -/
theorem smGen_hyper (S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (y : ℝ) :
    smGen S3 y 11 = ((y : ℂ)) • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  unfold smGen
  have hidx : smIdxEquiv 11 = Sum.inr (Sum.inr 0) := by decide
  rw [hidx]
  show toModes (smGenP S3 y (Sum.inr (Sum.inr 0))) = ((y : ℂ)) • 1
  rw [show smGenP S3 y (Sum.inr (Sum.inr 0))
      = ((y : ℂ)) • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) from rfl]
  rw [map_smul, map_one]

/-- **The hypercharge Gauss generator does not kill the ghost-free state `occ {0}`** at the
doublet, whenever the hypercharge is nonzero.  This is the single matrix entry that §20's refutation
needs, at the model's own representation. -/
theorem matterGen_smGen_hyper_occ_ne_zero (S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) {y : ℝ}
    (hy : (y : ℂ) ≠ 0) :
    matterGen 6 (smGen S3 y) 11
        (occ ({Fin.castAdd 12 (0 : Fin 6)} : Finset (Fin (6 + 12)))) ≠ 0 := by
  have hval : matterGen 6 (smGen S3 y) 11
      (occ ({Fin.castAdd 12 (0 : Fin 6)} : Finset (Fin (6 + 12))))
      = ((-Complex.I) * (y : ℂ)) •
        occ ({Fin.castAdd 12 (0 : Fin 6)} : Finset (Fin (6 + 12))) := by
    rw [matterGen, smGen_hyper, LinearMap.smul_apply,
      fermiBilin_embedMatter_scalar_occ (y := (y : ℂ)) (i₀ := (0 : Fin 6)), smul_smul]
  rw [hval]
  intro hzero
  have hnorm : ‖((-Complex.I) * (y : ℂ)) •
      occ ({Fin.castAdd 12 (0 : Fin 6)} : Finset (Fin (6 + 12)))‖ = ‖(y : ℂ)‖ := by
    rw [norm_smul]
    have hI : ‖(-Complex.I * (y : ℂ))‖ = ‖(y : ℂ)‖ := by
      rw [norm_mul]
      simp
    have hocc : ‖occ ({Fin.castAdd 12 (0 : Fin 6)} : Finset (Fin (6 + 12)))‖ = 1 := by
      simp [occ, EuclideanSpace.norm_single]
    rw [hI, hocc, mul_one]
  rw [hzero, norm_zero] at hnorm
  exact hy (norm_eq_zero.mp hnorm.symm)

/-! ## 6. The weak and gluon generators on a ghost-free state

§5 settled the hypercharge direction, the one place where the Gauss generator is a multiple of the
identity and the column of `M` is the state itself.  The remaining eleven directions are not
central, so on one occupied matter mode `G_a` is the *column* of `M` and lands in another mode: the
entry
is `−i M i₀ j₀`, where the state occupies the matter mode `j₀` and the entry is read in the
matter mode `i₀`.  That is `matterGen_occ_entry`, and it is nonzero whenever the matrix entry is.

The two computations at the model's own representation are then `smGen_weak_entry` — the first weak
generator `1 ⊗ τ₁/2` carries `1/2` from the mode of colour zero and isospin zero to its isospin
partner — and `smGen_gluon_entry` — the first Gell-Mann generator `λ¹ ⊗ 1` carries `1` from the
mode of colour zero to colour one.  Both are nonzero, so `Ω` does not kill the ghost-free state
`occ {0}` in those directions either; together with §5 that closes all twelve.
-/

/-- Injectivity of `Fin.castAdd 12`, in both directions. -/
theorem castAdd12_inj {m : ℕ} {i j : Fin m} : Fin.castAdd 12 i = Fin.castAdd 12 j ↔ i = j := by
  constructor
  · intro h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro h
    rw [h]

/-- An occupation basis vector reads off one matter mode. -/
theorem occ_apply_single {m : ℕ} (i i₀ : Fin m) :
    (occ ({Fin.castAdd 12 i} : Finset (Fin (m + 12))))
        ({Fin.castAdd 12 i₀} : Finset (Fin (m + 12))) = if i = i₀ then 1 else 0 := by
  rw [occ, EuclideanSpace.single_apply]
  by_cases h : i = i₀
  · subst h
    simp
  · have hne : ({Fin.castAdd 12 i} : Finset (Fin (m + 12))) ≠ {Fin.castAdd 12 i₀} := by
      intro hh
      exact h (castAdd12_inj.mp (Finset.singleton_inj.mp hh))
    rw [if_neg (Ne.symm hne), if_neg h]

/-- **One `creat`–`annih` pair on a one-mode state.**  The pair fills the mode `i₀` exactly when it
annihilates the mode `j₀` and creates it back, and the two Jordan–Wigner signs cancel. -/
theorem creat_annih_occ_entry {N : ℕ} (i j i₀ j₀ : Fin N) :
    (creat i (annih j (occ ({j₀} : Finset (Fin N))))) ({i₀} : Finset (Fin N))
      = if i = i₀ ∧ j = j₀ then 1 else 0 := by
  by_cases hi : i = i₀
  · subst hi
    by_cases hj : j = j₀
    · subst hj
      rw [annih_occ_self, creat_occ_empty, if_pos ⟨rfl, rfl⟩, occ, EuclideanSpace.single_apply,
        if_pos rfl]
    · rw [if_neg (by simp [hj]), creat_apply, if_pos (Finset.mem_singleton_self i),
        Finset.erase_singleton, annih_apply, if_neg (Finset.notMem_empty j)]
      simp [occ, EuclideanSpace.single_apply, hj]
  · rw [if_neg (by simp [hi]), creat_apply, if_neg (by simp [hi])]

/-- **The Gauss generator on a one-mode matter state is the column of `M`.**  Evaluating
`G_a = −i dΓ(T_a)` on `occ {j₀}` at the one-mode state `occ {i₀}` leaves the matrix entry
`T_a i₀ j₀`: the only surviving `creat`–`annih` pair is the diagonal one. -/
theorem matterGen_occ_entry {m : ℕ} (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ) (a : Fin 12)
    (i₀ j₀ : Fin m) :
    (matterGen m T a (occ ({Fin.castAdd 12 j₀} : Finset (Fin (m + 12)))))
        ({Fin.castAdd 12 i₀} : Finset (Fin (m + 12))) = (-Complex.I) * T a i₀ j₀ := by
  rw [matterGen, LinearMap.smul_apply, smul_apply_fock, fermiBilin_embedMatter]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, smul_apply_fock, creat_annih_occ_entry,
    castAdd12_inj]
  congr 1
  rw [Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single j₀]
    · rw [if_pos ⟨rfl, rfl⟩, mul_one]
    · intro b _ hb
      rw [if_neg (fun hh => hb hh.2), mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  · intro b _ hb
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (fun hh => hb hh.1), mul_zero]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

/-- **A nonzero matrix entry means the generator does not kill the state.** -/
theorem matterGen_occ_ne_zero {m : ℕ} (T : Fin 12 → Matrix (Fin m) (Fin m) ℂ)
    (a : Fin 12) {i₀ j₀ : Fin m} (h : T a i₀ j₀ ≠ 0) :
    matterGen m T a (occ ({Fin.castAdd 12 j₀} : Finset (Fin (m + 12)))) ≠ 0 := by
  intro hzero
  have hentry := matterGen_occ_entry T a i₀ j₀
  rw [hzero] at hentry
  have h0 : (-Complex.I) * T a i₀ j₀ = 0 := hentry.symm
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Complex.I_ne_zero (neg_eq_zero.mp h1)
  · exact h h1

/-- **The first weak generator moves the state to its isospin partner.**  `smGen … 8 = 1 ⊗ τ₁/2`
carries the mode of colour zero and isospin zero to its isospin partner with coefficient `1/2`. -/
theorem smGen_weak_entry (S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (y : ℝ) :
    smGen S3 y 8 (1 : Fin 6) (0 : Fin 6) = 1 / 2 := by
  unfold smGen
  have hidx : smIdxEquiv 8 = Sum.inr (Sum.inl 0) := by decide
  rw [hidx]
  change toModes (smGenP S3 y (Sum.inr (Sum.inl 0))) 1 0 = 1 / 2
  rw [toModes, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have h0 : internalEquiv.symm (0 : Fin 6) = ((0, 0) : Fin 3 × Fin 2) := by decide
  have h1 : internalEquiv.symm (1 : Fin 6) = ((0, 1) : Fin 3 × Fin 2) := by decide
  rw [h0, h1]
  simp [smGenP, su2gen, pauli, Matrix.kroneckerMap_apply]

/-- **The first gluon generator moves the state to the next colour.**  `smGen … 0 = λ¹ ⊗ 1` carries
the mode of colour zero to colour one, isospin unchanged, with coefficient `1`. -/
theorem smGen_gluon_entry (y : ℝ) :
    smGen BookProof.ChapterParity.gellMann y 0 (2 : Fin 6) (0 : Fin 6) = 1 := by
  unfold smGen
  have hidx : smIdxEquiv 0 = Sum.inl 0 := by decide
  rw [hidx]
  change toModes (smGenP BookProof.ChapterParity.gellMann y (Sum.inl 0)) 2 0 = 1
  rw [toModes, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have h0 : internalEquiv.symm (0 : Fin 6) = ((0, 0) : Fin 3 × Fin 2) := by decide
  have h2 : internalEquiv.symm (2 : Fin 6) = ((1, 0) : Fin 3 × Fin 2) := by decide
  rw [h0, h2]
  simp [smGenP, BookProof.ChapterParity.gellMann, Matrix.kroneckerMap_apply]

/-- **The weak Gauss generator does not kill the ghost-free state `occ {0}`**, for any colour
matrix `S3` and any hypercharge: only the weak factor enters. -/
theorem matterGen_smGen_weak_occ_ne_zero (S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ)
    (y : ℝ) :
    matterGen 6 (smGen S3 y) 8
        (occ ({Fin.castAdd 12 (0 : Fin 6)} : Finset (Fin (6 + 12)))) ≠ 0 :=
  matterGen_occ_ne_zero (smGen S3 y) 8 (i₀ := (1 : Fin 6)) (j₀ := (0 : Fin 6))
    (by rw [smGen_weak_entry]; norm_num)

/-- **The first gluon Gauss generator does not kill the ghost-free state `occ {0}`** at the
Gell-Mann representation. -/
theorem matterGen_smGen_gluon_occ_ne_zero (y : ℝ) :
    matterGen 6 (smGen BookProof.ChapterParity.gellMann y) 0
        (occ ({Fin.castAdd 12 (0 : Fin 6)} : Finset (Fin (6 + 12)))) ≠ 0 :=
  matterGen_occ_ne_zero (smGen BookProof.ChapterParity.gellMann y) 0
    (i₀ := (2 : Fin 6)) (j₀ := (0 : Fin 6))
    (by rw [smGen_gluon_entry]; norm_num)

end

end BookProof.SmGaugeRep
