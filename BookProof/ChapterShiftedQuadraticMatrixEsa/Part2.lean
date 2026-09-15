import Mathlib
import BookProof.ChapterShiftedQuadraticEsa
import BookProof.ChapterQuadraticRotationEsa
import BookProof.ChapterShiftedQuadraticMatrixEsa.Part1

/-!
# The indefinite quadratic Hamiltonian **with cross terms** and an unbounded
first-order perturbation

`BookProof.ChapterQuadraticRotationPerturbed` proves that for a **positive definite** real
symmetric matrix `A` and arbitrary real `b, b'` the operator
`H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`, `H_A = ∑_{k,l} A_{kl}(π_kπ_l + x_kx_l/4)`, is essentially
self-adjoint on the Gauss–polynomial core; positive definiteness is used exactly once, to
produce the relative bound, and the indefinite case was the recorded boundary.
`BookProof.ChapterShiftedQuadraticEsa` removes the sign condition for **diagonal** weights,
by completing the square on a translated, modulated core.

This module combines the two: for **every** real symmetric **invertible** `A` — no sign
condition, so the signature may be elliptic, hyperbolic or anything in between — and
arbitrary real `b, b'`, the operator

`H = ∑_{k,l} A_{kl}(π_kπ_l + x_kx_l/4) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`,  `πᵢ = −i∂/∂xᵢ`,

is symmetric and essentially self-adjoint on the translated, modulated Gauss–polynomial
core `D_{a,k}` of `BookProof.ChapterShiftedHermiteCore`, where `a = −2A⁻¹b` and
`k = −A⁻¹b'/2` are the classical equilibrium position and momentum.

The mechanism is again completing the square, now in matrix form:

`∑_{p,q} A_{pq}((π_p + k_p)(π_q + k_q) + (x_p + a_p)(x_q + a_q)/4)
   + ∑ᵢ (bᵢ(xᵢ + aᵢ) + b'ᵢ(πᵢ + kᵢ)) = H_A + const`

as soon as `A a = −2b` and `A k = −b'/2`, and `H_A` is diagonal on the *rotated* Hermite
polynomials, so the *translated, modulated, rotated* Hermite functions are an orthonormal
total family of eigenvectors of `H` in `D_{a,k}`.  No relative bound and no domination is
used; the only hypothesis is invertibility of `A`, which is exactly what is needed to
solve for the classical equilibrium.

## What is proved

* `quadPolyMatT`, `foTPoly`, `shiftedHMatPoly` — the Hamiltonian in the polynomial
  coordinates of the translated, modulated frame;
* `quadPolyMatT_apply_expand` — the expansion of the quadratic part into `H_A`, a
  first-order part and a constant;
* `shiftedHMatPoly_eq_quadPolyMat` — **completing the square** in matrix form;
* `hermiteTRLp`, `orthonormal_hermiteTRLp`, `span_hermiteTRLp`, `hermiteTRLp_total` — the
  translated, modulated, rotated product Hermite functions are an orthonormal family whose
  span is the core and which is total in `L²(ℝᵈ)`;
* `shiftedHMatOp`, `shiftedHMatOp_hermiteTRLp` — the operator and its diagonal action;
* `shiftedHMatOp_symmetric`, `shiftedHMatOp_essentiallySelfAdjoint` — **the headline**, for
  every real symmetric invertible `A` of arbitrary signature;
* `shiftedHMatOp_not_bounded`, `shiftedHMatCore_dense` — non-vacuity: the operator is
  genuinely unbounded (an invertible `A` has no zero eigenvalue) and its domain is dense;
* `shiftedHMatOp_stone_flow` — the resulting complete unitary Schrödinger flow;
* `wave_rotated_linear_essentiallySelfAdjoint` — the corollary: the rotated Minkowski
  quadratic (indefinite, with cross terms) plus an arbitrary constant external field and
  boost.

## Honest boundary

Invertibility of `A` is used exactly once, to solve `A a = −2b`, `A k = −b'/2`; if `A` is
singular and `b` has a component in the kernel the square cannot be completed (the motion
is free in that direction).  Nothing here claims a general Faris–Lavine potential.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ShiftedQuadraticMatrix

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}
/-! ## 4. The operator on the translated core, and its diagonal action -/

/-- **The inhomogeneous quadratic Hamiltonian on the translated, modulated core.** -/
def shiftedHMatOp (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (b b' : Fin d → ℝ) :
    (polyGaussCoreT a k) →ₗ[ℂ] L2d d :=
  (polyGaussCoreT a k).subtype ∘ₗ coreOpT a k (shiftedHMatPoly a k A b b')

/-- **The diagonal action** on the translated, modulated, rotated Hermite functions. -/
theorem shiftedHMatOp_hermiteTRLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2)
    (α : Fin d →₀ ℕ) (h : hermiteTRLp O a k α ∈ polyGaussCoreT a k) :
    shiftedHMatOp a k (rotConj O c) b b' ⟨_, h⟩
      = (((quadSymbol c α + matShiftConst a k b b' : ℝ)) : ℂ) • hermiteTRLp O a k α := by
  have hcoe : (⟨hermiteTRLp O a k α, h⟩ : polyGaussCoreT a k)
      = coreEquivT a k (((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • rotPoly O (hermiteMv α)) := by
    apply Subtype.ext
    rw [coreEquivT_coe, pgLpT_smul]
    rfl
  rw [hcoe]
  simp only [shiftedHMatOp, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [coreOpT_coe, map_smul, shiftedHMatPoly_eq_quadPolyMat a k hsym b b' ha hk,
    quadPolyMat_rotPoly hO, quadPoly_hermiteMv, map_smul, smul_add, smul_smul, smul_smul,
    ← add_smul, pgLpT_smul, hermiteTRLp, smul_smul]
  congr 1
  push_cast
  ring

/-! ## 5. Symmetry and essential self-adjointness -/

theorem shiftedHMatOp_rotConj_symmetric {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2) :
    SymmetricOn (polyGaussCoreT a k) (shiftedHMatOp a k (rotConj O c) b b') :=
  symmetricOn_of_diagonal (hermiteTRLp O a k) (orthonormal_hermiteTRLp hO a k)
    (fun α => quadSymbol c α + matShiftConst a k b b') (span_hermiteTRLp hO a k) _
    (fun α h => shiftedHMatOp_hermiteTRLp hO c a k b b' hsym ha hk α h)

theorem shiftedHMatOp_rotConj_deficiencyTrivialAt {O : Matrix (Fin d) (Fin d) ℝ}
    (hO : Oᵀ * O = 1) (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCoreT a k) (shiftedHMatOp a k (rotConj O c) b b') z :=
  deficiencyTrivialAt_of_diagonal (hermiteTRLp O a k)
    (fun α => quadSymbol c α + matShiftConst a k b b') (hermiteTRLp_total hO a k) _
    (hermiteTRLp_mem_coreT O a k)
    (fun α h => shiftedHMatOp_hermiteTRLp hO c a k b b' hsym ha hk α h) hz

/-- The classical equilibrium position `a = −2A⁻¹b`. -/
def matShiftVec (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) : Vd d :=
  (WithLp.toLp 2 (A⁻¹ *ᵥ fun i => -2 * b i) : Vd d)

/-- The classical equilibrium momentum `k = −A⁻¹b'/2`. -/
def matBoostVec (A : Matrix (Fin d) (Fin d) ℝ) (b' : Fin d → ℝ) : Vd d :=
  (WithLp.toLp 2 (A⁻¹ *ᵥ fun i => -(b' i) / 2) : Vd d)

theorem mulVec_matShiftVec {A : Matrix (Fin d) (Fin d) ℝ} (hdet : IsUnit A.det)
    (b : Fin d → ℝ) (i : Fin d) :
    ∑ j, A i j * (matShiftVec A b) j = -2 * b i := by
  have h : A *ᵥ (A⁻¹ *ᵥ fun j => -2 * b j) = fun j => -2 * b j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  calc ∑ j, A i j * (matShiftVec A b) j
      = (A *ᵥ (A⁻¹ *ᵥ fun j => -2 * b j)) i := rfl
    _ = -2 * b i := by rw [h]

theorem mulVec_matBoostVec {A : Matrix (Fin d) (Fin d) ℝ} (hdet : IsUnit A.det)
    (b' : Fin d → ℝ) (i : Fin d) :
    ∑ j, A i j * (matBoostVec A b') j = -(b' i) / 2 := by
  have h : A *ᵥ (A⁻¹ *ᵥ fun j => -(b' j) / 2) = fun j => -(b' j) / 2 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  calc ∑ j, A i j * (matBoostVec A b') j
      = (A *ᵥ (A⁻¹ *ᵥ fun j => -(b' j) / 2)) i := rfl
    _ = -(b' i) / 2 := by rw [h]

/-- A real symmetric matrix has symmetric entries. -/
theorem entries_symm {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (i j : Fin d) :
    A i j = A j i := by
  have h := congrFun (congrFun hA i) j
  simpa [Matrix.conjTranspose_apply] using h.symm

/-- **The headline.**  For every real symmetric **invertible** matrix `A` — of arbitrary
signature — and arbitrary real vectors `b, b'`, the inhomogeneous quadratic Hamiltonian

`H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`,  `H_A = ∑_{p,q} A_{pq}(π_pπ_q + x_px_q/4)`,

is essentially self-adjoint on the translated, modulated Gauss–polynomial core `D_{a,k}`
of `L²(ℝᵈ)`, with `a = −2A⁻¹b` and `k = −A⁻¹b'/2` the classical equilibrium. -/
theorem shiftedHMatOp_essentiallySelfAdjoint {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCoreT (matShiftVec A b) (matBoostVec A b'))
      (shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b') := by
  obtain ⟨O, hO, hAO⟩ := exists_rotConj_eigenvalues hA
  have hsym := entries_symm hA
  rw [hAO] at hsym hdet ⊢
  exact ⟨shiftedHMatOp_rotConj_deficiencyTrivialAt hO _ _ _ b b' hsym
      (mulVec_matShiftVec hdet b) (mulVec_matBoostVec hdet b') (by simp),
    shiftedHMatOp_rotConj_deficiencyTrivialAt hO _ _ _ b b' hsym
      (mulVec_matShiftVec hdet b) (mulVec_matBoostVec hdet b') (by simp)⟩

/-- The operator is symmetric on the same core. -/
theorem shiftedHMatOp_symmetric {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCoreT (matShiftVec A b) (matBoostVec A b'))
      (shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b') := by
  obtain ⟨O, hO, hAO⟩ := exists_rotConj_eigenvalues hA
  have hsym := entries_symm hA
  rw [hAO] at hsym hdet ⊢
  exact shiftedHMatOp_rotConj_symmetric hO _ _ _ b b' hsym
    (mulVec_matShiftVec hdet b) (mulVec_matBoostVec hdet b')

/-- The operator is genuinely unbounded as soon as one weight of the diagonalization is
non-zero. -/
theorem shiftedHMatOp_rotConj_not_bounded {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2)
    {i : Fin d} (hci : c i ≠ 0) :
    ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT a k,
        ‖shiftedHMatOp a k (rotConj O c) b b' f‖ ≤ C * ‖(f : L2d d)‖ := by
  classical
  rintro ⟨C, hC⟩
  set S : ℝ := ∑ j, c j * (1/2) + matShiftConst a k b b' with hS
  set K : ℝ := |S| with hK
  obtain ⟨n, hn⟩ := exists_nat_gt ((C + K) / |c i|)
  set α : Fin d →₀ ℕ := Finsupp.single i n with hα
  have hnorm : ‖hermiteTRLp (d := d) O a k α‖ = 1 :=
    (orthonormal_hermiteTRLp hO a k).norm_eq_one α
  have h := hC ⟨hermiteTRLp O a k α, hermiteTRLp_mem_coreT O a k α⟩
  rw [shiftedHMatOp_hermiteTRLp hO c a k b b' hsym ha hk α
    (hermiteTRLp_mem_coreT O a k α), norm_smul] at h
  simp only [hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  have hci' : 0 < |c i| := abs_pos.mpr hci
  have hsymb : quadSymbol c α + matShiftConst a k b b' = c i * (n : ℝ) + S := by
    rw [hα, quadSymbol_single, hS]
    ring
  have hlow : |c i| * (n : ℝ) - K ≤ |quadSymbol c α + matShiftConst a k b b'| := by
    have htri : |c i * (n : ℝ)| ≤ |c i * (n : ℝ) + S| + K := by
      have h1 := abs_add_le (c i * (n : ℝ) + S) (-S)
      rw [hK]
      simpa using h1
    have habs : |c i * (n : ℝ)| = |c i| * (n : ℝ) := by
      rw [abs_mul, Nat.abs_cast]
    rw [hsymb]
    linarith [htri, habs.symm.le, habs.le]
  have hbig : C < |c i| * (n : ℝ) - K := by
    have hmul : (C + K) < |c i| * (n : ℝ) := by
      rw [div_lt_iff₀ hci'] at hn
      linarith [hn]
    linarith
  linarith [h, hlow, hbig]

/-- The operator is genuinely unbounded whenever the space is non-trivial: an invertible
`A` has no zero eigenvalue. -/
theorem shiftedHMatOp_not_bounded {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) (i : Fin d) :
    ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT (matShiftVec A b) (matBoostVec A b'),
        ‖shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b' f‖
          ≤ C * ‖(f : L2d d)‖ := by
  obtain ⟨O, hO, hAO⟩ := exists_rotConj_eigenvalues hA
  have hsym := entries_symm hA
  have heig : hA.eigenvalues i ≠ 0 := by
    have hprod : (∏ j, hA.eigenvalues j) ≠ 0 := by
      have := hA.det_eq_prod_eigenvalues
      simp only [RCLike.ofReal_real_eq_id, id_eq] at this
      rw [← this]
      exact isUnit_iff_ne_zero.mp hdet
    exact fun h0 => hprod (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  rw [hAO] at hsym hdet ⊢
  exact shiftedHMatOp_rotConj_not_bounded hO _ _ _ b b' hsym
    (mulVec_matShiftVec hdet b) (mulVec_matBoostVec hdet b') heig

/-- The core is dense, so the statement above is a genuine essential self-adjointness
statement. -/
theorem shiftedHMatCore_dense {A : Matrix (Fin d) (Fin d) ℝ} (b b' : Fin d → ℝ) :
    Dense ((polyGaussCoreT (matShiftVec A b) (matBoostVec A b')
      : Submodule ℂ (L2d d)) : Set (L2d d)) :=
  polyGaussCoreT_dense _ _

/-- **The Hamiltonian generates a complete unitary flow.** -/
theorem shiftedHMatOp_stone_flow {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension
        (shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b') T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ (shiftedHMatCore_dense b b')
    (shiftedHMatOp_symmetric hA hdet b b')
    (shiftedHMatOp_essentiallySelfAdjoint hA hdet b b')

/-! ## 6. The rotated Minkowski corollary -/

/-- `O diag(c) Oᵀ` is symmetric. -/
theorem rotConj_isHermitian (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) :
    (rotConj O c).IsHermitian := by
  change (rotConj O c)ᴴ = rotConj O c
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, rotConj]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- The determinant of `O diag(c) Oᵀ` is `∏ c`, for orthogonal `O`. -/
theorem rotConj_det {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) :
    (rotConj O c).det = ∏ i, c i := by
  have hd : O.det * O.det = 1 := by
    have h := congrArg Matrix.det hO
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact h
  rw [rotConj_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
  linear_combination (∏ i, c i) * hd

/-- **The rotated wave operator with an indefinite quadratic potential, a constant
external field and a constant boost.**  For any orthogonal `O`, the matrix
`A = O diag(1, −1, …, −1) Oᵀ` is symmetric, indefinite and invertible, and *neither* the
kinetic form nor the potential of `H_A` is diagonal; the theorem adds to it an arbitrary
unbounded first-order term. -/
theorem wave_rotated_linear_essentiallySelfAdjoint (n : ℕ)
    {O : Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ} (hO : Oᵀ * O = 1)
    (b b' : Fin (1 + n) → ℝ) :
    EssentiallySelfAdjointOn
      (polyGaussCoreT (matShiftVec (rotConj O (minkowskiCoeff n)) b)
        (matBoostVec (rotConj O (minkowskiCoeff n)) b'))
      (shiftedHMatOp (matShiftVec (rotConj O (minkowskiCoeff n)) b)
        (matBoostVec (rotConj O (minkowskiCoeff n)) b')
        (rotConj O (minkowskiCoeff n)) b b') :=
  shiftedHMatOp_essentiallySelfAdjoint (rotConj_isHermitian O (minkowskiCoeff n))
    (by
      rw [isUnit_iff_ne_zero, rotConj_det hO]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => minkowskiCoeff_ne_zero n i) b b'

end

end BookProof.ShiftedQuadraticMatrix
