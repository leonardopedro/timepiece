import BookProof.ChapterLaplacianProduct

/-!
# Tools for solid harmonics: Laplacians of powers of linear forms and of `‖x‖²`

This module supplies the differential-calculus toolkit needed to exhibit the
solid harmonics `rˡ Y_{lμ}(θ,φ)` of `book.tex` §A.5 as *bona fide* harmonic
functions, homogeneous of degree `l`, on a three-dimensional Euclidean space.
It continues `BookProof.ChapterRadialLaplacian` and
`BookProof.ChapterLaplacianProduct`.

## Contents

* `laplacian_clmPow` / `laplacian_rclmPow` — the Laplacian of the `k`-th power
  of a (complex- resp. real-valued) continuous linear functional:
  `Δ(ψ ^ k) = k(k−1) ψ^{k−2} ∑ᵢ ψ(bᵢ)²`.  In particular a functional whose
  coordinate squares sum to zero (a *null* functional, such as `x¹ + i x²`)
  has harmonic powers — these are the top spherical harmonics;
* `laplacian_normSqPow`, `fderiv_normSqPow` — the Laplacian and the derivative
  of `x ↦ (‖x‖²)ᵐ`;
* `laplacian_sum` — the Laplacian of a finite sum;
* `laplacian_angular_mul_term` — the key computation: for an *angular* factor
  `A` (harmonic, homogeneous of degree `μ` in the sense of Euler's identity,
  and constant along the axis `e`) and the cylindrical monomial
  `⟪e,x⟫ʲ (‖x‖²)ᵐ`,
  `Δ(A · ⟪e,·⟫ʲ‖·‖^{2m}) = A · [ j(j−1)⟪e,x⟫^{j−2}(‖x‖²)ᵐ
      + (4m(m−1) + 2nm + 4jm + 4μm) ⟪e,x⟫ʲ(‖x‖²)^{m−1} ]`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterSolidHarmonicTools

open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the `k`-th power of a complex-valued linear form. -/
theorem hasFDerivAt_clmPow (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) :
    HasFDerivAt (fun y => (ψ y) ^ k) (((k : ℂ) * (ψ x) ^ (k - 1)) • (ψ : E →L[ℝ] ℂ)) x :=
  (hasDerivAt_pow k (ψ x)).comp_hasFDerivAt x ψ.hasFDerivAt

/-- The derivative of the `k`-th power of a real-valued linear form. -/
theorem hasFDerivAt_rclmPow (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) :
    HasFDerivAt (fun y => (L y) ^ k) (((k : ℝ) * (L x) ^ (k - 1)) • (L : E →L[ℝ] ℝ)) x :=
  (hasDerivAt_pow k (L x)).comp_hasFDerivAt x L.hasFDerivAt

theorem contDiff_clmPow (ψ : E →L[ℝ] ℂ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (ψ y) ^ k :=
  (ψ.contDiff (n := 2)).pow k

theorem contDiff_rclmPow (L : E →L[ℝ] ℝ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (L y) ^ k :=
  (L.contDiff (n := 2)).pow k

theorem fderiv_fderiv_clmPow (ψ : E →L[ℝ] ℂ) (k : ℕ) (x v w : E) :
    fderiv ℝ (fderiv ℝ fun y => (ψ y) ^ k) x v w
      = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k - 2) * ψ v * ψ w := by
  have hfd : (fderiv ℝ fun y : E => (ψ y) ^ k)
      = fun y => ((k : ℂ) * (ψ y) ^ (k - 1)) • (ψ : E →L[ℝ] ℂ) := by
    funext y; exact (hasFDerivAt_clmPow ψ k y).fderiv
  rw [hfd]
  have hc : HasFDerivAt (fun y : E => (k : ℂ) * (ψ y) ^ (k - 1))
      (((k : ℂ) * ((k - 1 : ℕ) : ℂ) * (ψ x) ^ (k - 1 - 1)) • (ψ : E →L[ℝ] ℂ)) x := by
    have h := (hasFDerivAt_clmPow ψ (k - 1) x).const_mul (k : ℂ)
    convert h using 1
    ext u
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [(hc.smul_const (ψ : E →L[ℝ] ℂ)).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  rcases k with _ | _ | k
  · simp
  · simp
  · push_cast; ring_nf

theorem fderiv_fderiv_rclmPow (L : E →L[ℝ] ℝ) (k : ℕ) (x v w : E) :
    fderiv ℝ (fderiv ℝ fun y => (L y) ^ k) x v w
      = (k : ℝ) * ((k : ℝ) - 1) * (L x) ^ (k - 2) * L v * L w := by
  have hfd : (fderiv ℝ fun y : E => (L y) ^ k)
      = fun y => ((k : ℝ) * (L y) ^ (k - 1)) • (L : E →L[ℝ] ℝ) := by
    funext y; exact (hasFDerivAt_rclmPow L k y).fderiv
  rw [hfd]
  have hc : HasFDerivAt (fun y : E => (k : ℝ) * (L y) ^ (k - 1))
      (((k : ℝ) * ((k - 1 : ℕ) : ℝ) * (L x) ^ (k - 1 - 1)) • (L : E →L[ℝ] ℝ)) x := by
    have h := (hasFDerivAt_rclmPow L (k - 1) x).const_mul (k : ℝ)
    convert h using 1
    ext u
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [(hc.smul_const (L : E →L[ℝ] ℝ)).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  rcases k with _ | _ | k
  · simp
  · simp
  · push_cast; ring_nf

end NormedSpace

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Laplacian of a power of a complex-valued linear form.** -/
theorem laplacian_clmPow (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) :
    (Δ fun y => (ψ y) ^ k) x
      = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k - 2)
          * ∑ i, (ψ (stdOrthonormalBasis ℝ E i)) ^ 2 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_clmPow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The Laplacian of a power of a real-valued linear form.** -/
theorem laplacian_rclmPow (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) :
    (Δ fun y => (L y) ^ k) x
      = (k : ℝ) * ((k : ℝ) - 1) * (L x) ^ (k - 2)
          * ∑ i, (L (stdOrthonormalBasis ℝ E i)) ^ 2 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_rclmPow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Parseval for one vector: `∑ᵢ ⟪e, bᵢ⟫² = ‖e‖²`. -/
theorem sum_inner_sq (e : E) :
    ∑ i, (⟪e, (stdOrthonormalBasis ℝ E) i⟫_ℝ) ^ 2 = ‖e‖ ^ 2 := by
  have h := (stdOrthonormalBasis ℝ E).sum_inner_mul_inner e e
  simp only [real_inner_comm e] at h
  simp only [sq]
  rw [h, real_inner_self_eq_norm_sq]
  ring

/-- The derivative of `x ↦ (‖x‖²)ᵐ`. -/
theorem fderiv_normSqPow (m : ℕ) (x : E) :
    fderiv ℝ (fun y : E => (‖y‖ ^ 2) ^ m) x = (2 * m * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x := by
  have hG : ContDiffAt ℝ 2 (fun q : ℝ => q ^ m) (‖x‖ ^ 2) := (contDiff_id.pow m).contDiffAt
  have h := (fderiv_comp_normSq (G := fun q : ℝ => q ^ m) hG).self_of_nhds
  have hd : deriv (fun q : ℝ => q ^ m) = fun q : ℝ => (m : ℝ) * q ^ (m - 1) := by
    funext q; simp
  rw [h, hd]
  simp only [mul_assoc]

theorem contDiff_normSqPow (m : ℕ) : ContDiff ℝ 2 fun y : E => (‖y‖ ^ 2) ^ m :=
  ((contDiff_norm_sq ℝ).pow m)

/-- **The Laplacian of `x ↦ (‖x‖²)ᵐ`**: `4m(m−1)(‖x‖²)^{m−1} + 2nm(‖x‖²)^{m−1}`. -/
theorem laplacian_normSqPow (m : ℕ) (x : E) :
    (Δ fun y : E => (‖y‖ ^ 2) ^ m) x
      = (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m) * (‖x‖ ^ 2) ^ (m - 1) := by
  have hG : ContDiffAt ℝ 2 (fun q : ℝ => q ^ m) (‖x‖ ^ 2) := (contDiff_id.pow m).contDiffAt
  have h := laplacian_comp_normSq (G := fun q : ℝ => q ^ m) (x := x) hG
  rw [h]
  have hd : deriv (fun q : ℝ => q ^ m) = fun q : ℝ => (m : ℝ) * q ^ (m - 1) := by
    funext q; simp
  rw [hd]
  have hdd : deriv (fun q : ℝ => (m : ℝ) * q ^ (m - 1))
      = fun q : ℝ => (m : ℝ) * ((m - 1 : ℕ) : ℝ) * q ^ (m - 1 - 1) := by
    funext q
    rw [deriv_const_mul _ (by fun_prop)]
    simp [mul_assoc]
  rw [hdd]
  rcases m with _ | _ | m
  · simp
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- The Laplacian of a finite sum. -/
theorem laplacian_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    (Δ fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, (Δ (f i)) x := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
      simp
  | insert a s ha ih =>
      have hfa : ContDiffAt ℝ 2 (f a) x := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x := fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)
      have hsum : ContDiffAt ℝ 2 (fun y => ∑ i ∈ s, f i y) x := by
        refine ContDiffAt.sum ?_
        intro i hi
        exact hfs i hi
      have hrw : (fun y => ∑ i ∈ insert a s, f i y)
          = (f a) + (fun y => ∑ i ∈ s, f i y) := by
        funext y
        simp [Finset.sum_insert ha]
      rw [hrw, hfa.laplacian_add hsum, ih hfs, Finset.sum_insert ha]

/-- The derivative of the cylindrical monomial `⟪e,y⟫ʲ (‖y‖²)ᵐ`. -/
theorem hasFDerivAt_cylTerm (e : E) (j m : ℕ) (x : E) :
    HasFDerivAt (fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m)
      (((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (‖x‖ ^ 2) ^ m) • innerCLM E e
        + (2 * m * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x) x := by
  have hf : HasFDerivAt (fun y : E => (⟪e, y⟫_ℝ) ^ j)
      (((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1)) • (innerCLM E e)) x :=
    hasFDerivAt_rclmPow (innerCLM E e) j x
  have hg : HasFDerivAt (fun y : E => (‖y‖ ^ 2) ^ m)
      ((2 * m * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x) x := by
    have hcd : ContDiff ℝ 2 fun y : E => (‖y‖ ^ 2) ^ m := contDiff_normSqPow m
    have hdiff : DifferentiableAt ℝ (fun y : E => (‖y‖ ^ 2) ^ m) x :=
      (hcd.differentiable (by norm_num)).differentiableAt
    rw [← fderiv_normSqPow m x]
    exact hdiff.hasFDerivAt
  have h := hf.mul hg
  convert h using 1
  ext u
  simp only [ContinuousLinearMap.add_apply, Pi.smul_apply,
    smul_eq_mul, innerCLM_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_smul]
  ring

/-- **The Laplacian of the cylindrical monomial** `⟪e,y⟫ʲ (‖y‖²)ᵐ` for a unit
vector `e`. -/
theorem laplacian_cylTerm (e : E) (he : ‖e‖ = 1) (j m : ℕ) (x : E) :
    (Δ fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x
      = (j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) * (‖x‖ ^ 2) ^ m
        + (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m + 4 * j * m)
            * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1) := by
  have hf : ContDiffAt ℝ 2 (fun y : E => (⟪e, y⟫_ℝ) ^ j) x :=
    (contDiff_rclmPow (innerCLM E e) j).contDiffAt
  have hg : ContDiffAt ℝ 2 (fun y : E => (‖y‖ ^ 2) ^ m) x := (contDiff_normSqPow m).contDiffAt
  have hprod := laplacian_mul hf hg
  have hlapf : (Δ fun y : E => (⟪e, y⟫_ℝ) ^ j) x
      = (j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) := by
    have key := laplacian_rclmPow (innerCLM E e) j x
    simp only [innerCLM_apply] at key
    rw [key, sum_inner_sq e, he]
    ring
  have hlapg := laplacian_normSqPow (E := E) m x
  have hcross : ∑ i, fderiv ℝ (fun y : E => (⟪e, y⟫_ℝ) ^ j) x ((stdOrthonormalBasis ℝ E) i)
      * fderiv ℝ (fun y : E => (‖y‖ ^ 2) ^ m) x ((stdOrthonormalBasis ℝ E) i)
      = 2 * (j : ℝ) * m * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1) := by
    have hfd := (hasFDerivAt_rclmPow (innerCLM E e) j x).fderiv
    simp only [innerCLM_apply] at hfd
    rw [hfd, fderiv_normSqPow]
    have hsum : ∑ i, ((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (2 * m * (‖x‖ ^ 2) ^ (m - 1)))
        * (⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ * (innerCLM E e) ((stdOrthonormalBasis ℝ E) i))
        = ((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (2 * m * (‖x‖ ^ 2) ^ (m - 1))) * ⟪e, x⟫_ℝ := by
      rw [← Finset.mul_sum, sum_inner_mul_apply (innerCLM E e) x]
      simp
    have hrw : ∑ i, (((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1)) • innerCLM E e) ((stdOrthonormalBasis ℝ E) i)
        * ((2 * m * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x) ((stdOrthonormalBasis ℝ E) i)
        = ∑ i, ((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (2 * m * (‖x‖ ^ 2) ^ (m - 1)))
            * (⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ
              * (innerCLM E e) ((stdOrthonormalBasis ℝ E) i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, innerCLM_apply]
      ring
    rw [hrw, hsum]
    rcases j with _ | j
    · simp
    · simp only [Nat.add_sub_cancel]
      ring
  rw [hprod, hlapf, hlapg, hcross]
  ring

/-- **The Laplacian of an angular factor times a cylindrical one.**  `A` is
assumed harmonic, homogeneous of degree `μ` (Euler's identity) and constant
along the axis `e`; `B` has gradient `α e + β x`. -/
theorem laplacian_angular_mul {A B : E → ℝ} {x : E} {α β : ℝ} {e : E} {μ : ℕ}
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hharm : (Δ A) x = 0) (heuler : fderiv ℝ A x x = μ * A x) (haxis : fderiv ℝ A x e = 0)
    (hgrad : fderiv ℝ B x = α • innerCLM E e + β • innerCLM E x) :
    (Δ fun y : E => A y * B y) x = A x * (Δ B) x + 2 * β * (μ : ℝ) * A x := by
  have hprod := laplacian_mul hA hB
  have hcross : ∑ i, fderiv ℝ A x ((stdOrthonormalBasis ℝ E) i)
      * fderiv ℝ B x ((stdOrthonormalBasis ℝ E) i)
      = α * fderiv ℝ A x e + β * fderiv ℝ A x x := by
    have he' : ∑ i, ⟪e, (stdOrthonormalBasis ℝ E) i⟫_ℝ
        * fderiv ℝ A x ((stdOrthonormalBasis ℝ E) i) = fderiv ℝ A x e :=
      sum_inner_mul_apply (fderiv ℝ A x) e
    have hx' : ∑ i, ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ
        * fderiv ℝ A x ((stdOrthonormalBasis ℝ E) i) = fderiv ℝ A x x :=
      sum_inner_mul_apply (fderiv ℝ A x) x
    have hterm : ∀ i, fderiv ℝ A x ((stdOrthonormalBasis ℝ E) i)
        * fderiv ℝ B x ((stdOrthonormalBasis ℝ E) i)
        = α * (⟪e, (stdOrthonormalBasis ℝ E) i⟫_ℝ * fderiv ℝ A x ((stdOrthonormalBasis ℝ E) i))
          + β * (⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ
            * fderiv ℝ A x ((stdOrthonormalBasis ℝ E) i)) := by
      intro i
      rw [hgrad]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        smul_eq_mul, innerCLM_apply]
      ring
    simp only [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, he', hx']
  rw [hprod, hcross, hharm, haxis, heuler]
  ring

/-- **The key computation.**  For an angular factor `A` (harmonic, homogeneous
of degree `μ`, constant along the unit axis `e`) and the cylindrical monomial
`⟪e,y⟫ʲ(‖y‖²)ᵐ`. -/
theorem laplacian_angular_mul_cylTerm {A : E → ℝ} {x : E} {e : E} (he : ‖e‖ = 1) {μ : ℕ}
    (j m : ℕ) (hA : ContDiffAt ℝ 2 A x) (hharm : (Δ A) x = 0)
    (heuler : fderiv ℝ A x x = μ * A x) (haxis : fderiv ℝ A x e = 0) :
    (Δ fun y : E => A y * ((⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m)) x
      = A x * ((j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) * (‖x‖ ^ 2) ^ m
        + (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m + 4 * j * m + 4 * μ * m)
            * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) := by
  have hB : ContDiffAt ℝ 2 (fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x :=
    ((contDiff_rclmPow (innerCLM E e) j).mul (contDiff_normSqPow m)).contDiffAt
  have hgrad : fderiv ℝ (fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x
      = ((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (‖x‖ ^ 2) ^ m) • innerCLM E e
        + (2 * m * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x :=
    (hasFDerivAt_cylTerm e j m x).fderiv
  rw [laplacian_angular_mul hA hB hharm heuler haxis hgrad, laplacian_cylTerm e he j m x]
  ring

end Inner

end BookProof.ChapterSolidHarmonicTools
