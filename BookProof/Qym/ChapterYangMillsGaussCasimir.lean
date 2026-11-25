import BookProof.ChapterBrstYmCommute
import BookProof.Qym.ChapterYangMillsHermite

/-!
# The kinetic half of `[H, Ω] = 0`: `[Σ π², 𝒢_d] = 0`

`BookProof/ChapterBrstYmCommute.lean` proves the constraint-algebra half of
`[H, Ω] = 0` for the concrete Weyl-gauge Yang–Mills Hamiltonian and BRST charge, and
names the two Casimir lemmas its Hamiltonian half consumes.  This module proves the
first of them, on the polynomial core:

* `momSq_comm` — `[Σ_{j,a} π_{ja}², 𝒢_d] = 0`, the kinetic term of
  `H = ½ Σ π² + ½ Σ B²`, for every colour `d`.

The route is the one that file records.  A gauge rotation acts on the `A`-block as the
linear colour rotation at fixed spatial index, so

* `mulOp_X_comm_deriv` — `[X_i, 𝒢_d] = −mulOp (𝒢_d X_i)`;
* `pderiv_comm_deriv` — `[∂_i, 𝒢_d] = Σ_j mulOp (∂_i v_j) ∂_j`, with `pderiv_pderiv`
  the mixed-partials identity it needs;
* `pderiv_vec_eq` / `sum_pderiv_vec_eval` evaluate `∂_i v_j` on the concrete vector
  field: only the `A`-coordinates with the *same* spatial index survive, and the
  coefficient is the structure constant;
* `derOp_comm_gauss` assembles these into the adjoint action on the deformed ladder
  generators `derOp = ∂ − ½ x`;
* `sum_sq_comm_of_adjoint` is the general cancellation: squares of a family acting in
  the adjoint representation commute with the generator, because the structure
  constants are antisymmetric.

## Boundary

`ymGauss_comm_magSq` — `[Σ B², 𝒢_d] = 0` — is **not** proved here.  It needs the field
strength to transform in the adjoint, `𝒢_d(B_{ia}) = Σ_g f_{agd} B_{ig}`, whose scalar
content is the contracted Jacobi identity
`Σ_b f_{abq} f_{bpd} + Σ_b f_{apb} f_{bqd} = Σ_e f_{aed} f_{epq}`
(a consequence of `G.jacobi` with `antisymm` and `cyclic`).  Until that lands,
`[H, Ω] = 0` itself remains open and `H` is not yet available as a gauge-invariant
observable.  Nothing here assumes it.

Everything is `sorry`-free and axiom-free beyond `propext` / `Classical.choice` /
`Quot.sound`.
-/

open MvPolynomial
open BookProof.BrstYmCommute
namespace BookProof.Qym.GaussCasimir

open BookProof.YangMillsHermite BookProof.BookBrstYangMills

variable {d : ℕ}

/-- Mixed partial derivatives commute. -/
theorem pderiv_pderiv (i j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
      rw [pderiv_monomial, pderiv_monomial, pderiv_monomial, pderiv_monomial]
      have hidx : (s - Finsupp.single j 1) - Finsupp.single i 1
          = (s - Finsupp.single i 1) - Finsupp.single j 1 := by
        ext x
        rw [Finsupp.coe_tsub, Finsupp.coe_tsub, Finsupp.coe_tsub, Finsupp.coe_tsub]
        simp only [Pi.sub_apply]
        omega
      rw [hidx]
      congr 1
      by_cases h : i = j
      · subst h
        ring
      · have h1 : ((s - Finsupp.single j 1 : Fin d →₀ ℕ) : Fin d → ℕ) i = s i := by
          rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne (a := j) (a' := i) h,
            tsub_zero]
        have h2 : ((s - Finsupp.single i 1 : Fin d →₀ ℕ) : Fin d → ℕ) j = s j := by
          rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne (a := i) (a' := j)
            (Ne.symm h), tsub_zero]
        rw [h1, h2]
        ring
  | add p q hp hq => simp only [map_add, hp, hq]

/-- `[X_i, 𝒢_d] = −mulOp (𝒢_d X_i)`, written without the sign. -/
theorem mulOp_X_comm_deriv (G : GaugeAlgebra 8) (d : Fin 8) (i : Fin 99) :
    mulOp (X i) * (ymGaussDer G d).toLinearMap + mulOp (ymGaussVec G d i)
      = (ymGaussDer G d).toLinearMap * mulOp (X i) := by
  refine LinearMap.ext fun p => ?_
  change X i * (ymGaussDer G d p) + ymGaussVec G d i * p = ymGaussDer G d (X i * p)
  rw [Derivation.leibniz, ymGaussDer_X]
  simp only [smul_eq_mul]
  ring

/-- `[∂_i, 𝒢_d] = Σ_j mulOp (∂_i v_j) ∂_j` for the vector field `v = 𝒢_d`. -/
theorem pderiv_comm_deriv (G : GaugeAlgebra 8) (d : Fin 8) (i : Fin 99) :
    (pderiv i).toLinearMap * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap * (pderiv i).toLinearMap
        + ∑ j : Fin 99, mulOp (pderiv i (ymGaussVec G d j)) * (pderiv j).toLinearMap := by
  refine LinearMap.ext fun p => ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply]
  rw [LinearMap.sum_apply]
  simp only [Module.End.mul_apply, mulOp_apply]
  calc pderiv i (ymGaussDer G d p)
      = ∑ j : Fin 99, pderiv i (ymGaussVec G d j * pderiv j p) := by
        rw [ymGaussDer_apply, map_sum]
    _ = ∑ j : Fin 99, (ymGaussVec G d j * pderiv j (pderiv i p)
            + pderiv i (ymGaussVec G d j) * pderiv j p) :=
        Finset.sum_congr rfl fun j _ => by rw [pderiv_mul, pderiv_pderiv i j p]; ring
    _ = (∑ j : Fin 99, ymGaussVec G d j * pderiv j (pderiv i p))
          + ∑ j : Fin 99, pderiv i (ymGaussVec G d j) * pderiv j p :=
        Finset.sum_add_distrib
    _ = ymGaussDer G d (pderiv i p)
          + ∑ j : Fin 99, pderiv i (ymGaussVec G d j) * pderiv j p := by
        rw [ymGaussDer_apply]


section Concretize

theorem mulOp_add' (a b : YmPoly) : mulOp (a + b) = mulOp a + mulOp b := by
  refine LinearMap.ext fun p => ?_
  rw [LinearMap.add_apply, mulOp_apply, mulOp_apply, mulOp_apply, add_mul]

/-- `mulOp` is additive in its polynomial argument. -/
theorem mulOp_sum {n : ℕ} (F : Fin n → YmPoly) :
    mulOp (∑ i, F i) = ∑ i, mulOp (F i) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [mulOp]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mulOp_add', ih]

/-- Multiplication by the constant `c` is `c` times the identity. -/
theorem mulOp_C_smul (c : ℂ) (T : Module.End ℂ YmPoly) : mulOp (C c) * T = c • T := by
  refine LinearMap.ext fun p => ?_
  rw [Module.End.mul_apply, mulOp_apply, C_mul', LinearMap.smul_apply]

/-- The derivative of one linear colour combination of `A`-coordinates. -/
theorem pderiv_linear_idxA (G : GaugeAlgebra 8) (d : Fin 8) (j0 : Fin 3) (a : Fin 8)
    (j1 : Fin 3) (b : Fin 8) :
    pderiv (idxA j0 a) (∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxA j1 g))
      = if j1 = j0 then C ((G.f b a d : ℝ) : ℂ) else (0 : YmPoly) := by
  rw [map_sum]
  have hterm : ∀ g : Fin 8,
      pderiv (idxA j0 a) (((G.f b g d : ℝ) : ℂ) • X (idxA j1 g))
        = if j1 = j0 ∧ g = a then C ((G.f b a d : ℝ) : ℂ) else (0 : YmPoly) := by
    intro g
    rw [smul_eq_C_mul, pderiv_C_mul, pderiv_X]
    by_cases h : j1 = j0 ∧ g = a
    · obtain ⟨rfl, rfl⟩ := h
      rw [Pi.single_eq_same, if_pos ⟨rfl, rfl⟩, mul_one]
    · rw [if_neg h]
      have hne : idxA j1 g ≠ idxA j0 a := by
        intro he
        exact h (Prod.ext_iff.mp (idxA_injective (a₁ := (j1, g)) (a₂ := (j0, a)) he))
      rw [Pi.single_eq_of_ne' (Ne.symm hne), mul_zero]
  rw [Finset.sum_congr rfl fun g _ => hterm g]
  by_cases h : j1 = j0
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro g _ hg
      rw [if_neg (by intro hc; exact hg hc.2)]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · rw [if_neg h, Finset.sum_eq_zero]
    intro g _
    rw [if_neg (by intro hc; exact h hc.1)]

/-- A linear combination of the jet coordinates has zero `A`-derivative. -/
theorem pderiv_linear_idxD (G : GaugeAlgebra 8) (d : Fin 8) (j0 : Fin 3) (a : Fin 8)
    (j1 k1 : Fin 3) (b : Fin 8) :
    pderiv (idxA j0 a) (∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxD j1 k1 g))
      = (0 : YmPoly) := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [smul_eq_C_mul, pderiv_C_mul, pderiv_X]
  have hne : idxA j0 a ≠ idxD j1 k1 g := idxA_ne_idxD j0 a j1 k1 g
  rw [Pi.single_eq_of_ne' hne, mul_zero]

/-- The `A`-block of the Gauss vector field, differentiated. -/
theorem blockA_pderiv (G : GaugeAlgebra 8) (d : Fin 8) (j0 : Fin 3) (a : Fin 8) (m : Fin 99) :
    pderiv (idxA j0 a)
        (∑ p : Fin 3 × Fin 8, if idxA p.1 p.2 = m then
          (∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • X (idxA p.1 g)) else 0)
      = ∑ b : Fin 8, if idxA j0 b = m then C ((G.f b a d : ℝ) : ℂ) else (0 : YmPoly) := by
  rw [map_sum]
  have hif : ∀ (c : Prop) [Decidable c] (P : YmPoly),
      pderiv (idxA j0 a) (if c then P else 0) = if c then pderiv (idxA j0 a) P else 0 := by
    intro c _ P
    by_cases hc : c <;> simp [hc]
  simp only [hif]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_eq_single j0]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [pderiv_linear_idxA]
    simp
  · intro j _ hj
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [pderiv_linear_idxA, if_neg hj]
    simp
  · intro hmem
    exact absurd (Finset.mem_univ j0) hmem

/-- The jet block of the Gauss vector field has zero `A`-derivative. -/
theorem blockD_pderiv (G : GaugeAlgebra 8) (d : Fin 8) (j0 : Fin 3) (a : Fin 8) (m : Fin 99) :
    pderiv (idxA j0 a)
        (∑ p : Fin 3 × Fin 3 × Fin 8, if idxD p.1 p.2.1 p.2.2 = m then
          (∑ g : Fin 8, ((G.f p.2.2 g d : ℝ) : ℂ) • X (idxD p.1 p.2.1 g)) else 0)
      = (0 : YmPoly) := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hm : idxD p.1 p.2.1 p.2.2 = m
  · rw [if_pos hm, pderiv_linear_idxD]
  · rw [if_neg hm]
    simp

/-- The Gauss vector field's `A`-derivative: only same-space colour rotations survive. -/
theorem pderiv_vec_eq (G : GaugeAlgebra 8) (d : Fin 8) (j0 : Fin 3) (a : Fin 8) (m : Fin 99) :
    pderiv (idxA j0 a) (ymGaussVec G d m)
      = ∑ b : Fin 8, if idxA j0 b = m then C ((G.f b a d : ℝ) : ℂ) else (0 : YmPoly) := by
  rw [ymGaussVec, map_add, blockA_pderiv, blockD_pderiv, add_zero]

/-- The `∂`-side of the commutator, summed over the `99` coordinates. -/
theorem sum_pderiv_gaussVec (G : GaugeAlgebra 8) (d : Fin 8) (j0 : Fin 3) (a : Fin 8) :
    (∑ m : Fin 99, mulOp (pderiv (idxA j0 a) (ymGaussVec G d m)) * (pderiv m).toLinearMap)
      = ∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) • (pderiv (idxA j0 b)).toLinearMap := by
  rw [Finset.sum_congr rfl fun m _ => by rw [pderiv_vec_eq]]
  rw [Finset.sum_congr rfl fun m _ => by rw [mulOp_sum]]
  rw [Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (idxA j0 b)]
  · simp [mulOp_C_smul]
  · intro m _ hm
    by_cases h : idxA j0 b = m
    · exact absurd h.symm hm
    · simp [h, mulOp]
  · intro hmem
    exact absurd (Finset.mem_univ (idxA j0 b)) hmem

/-- The same identity, evaluated at a polynomial. -/
theorem sum_pderiv_vec_eval (G : GaugeAlgebra 8) (d : Fin 8) (j0 : Fin 3) (a : Fin 8)
    (p : YmPoly) :
    (∑ m : Fin 99, pderiv (idxA j0 a) (ymGaussVec G d m) * pderiv m p)
      = ∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) • pderiv (idxA j0 b) p := by
  rw [Finset.sum_congr rfl fun m _ => by rw [pderiv_vec_eq]]
  rw [Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (idxA j0 b)]
  · rw [if_pos rfl, C_mul']
  · intro m _ hm
    by_cases h : idxA j0 b = m
    · exact absurd h.symm hm
    · simp [h]
  · intro hmem
    exact absurd (Finset.mem_univ (idxA j0 b)) hmem

/-- `[∂_{j0 a}, 𝒢_d]` at the `A`-block. -/
theorem pderiv_comm_gaussVec (G : GaugeAlgebra 8) (d : Fin 8) (j0 : Fin 3) (a : Fin 8) :
    (pderiv (idxA j0 a)).toLinearMap * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap * (pderiv (idxA j0 a)).toLinearMap
        + ∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) • (pderiv (idxA j0 b)).toLinearMap := by
  refine LinearMap.ext fun p => ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  calc pderiv (idxA j0 a) (ymGaussDer G d p)
      = ∑ m : Fin 99, pderiv (idxA j0 a) (ymGaussVec G d m * pderiv m p) := by
        rw [ymGaussDer_apply, map_sum]
    _ = ∑ m : Fin 99, (ymGaussVec G d m * pderiv m (pderiv (idxA j0 a) p)
            + pderiv (idxA j0 a) (ymGaussVec G d m) * pderiv m p) :=
        Finset.sum_congr rfl fun m _ => by
          rw [pderiv_mul, pderiv_pderiv (idxA j0 a) m p]; ring
    _ = (∑ m : Fin 99, ymGaussVec G d m * pderiv m (pderiv (idxA j0 a) p))
          + ∑ m : Fin 99, pderiv (idxA j0 a) (ymGaussVec G d m) * pderiv m p :=
        Finset.sum_add_distrib
    _ = ymGaussDer G d (pderiv (idxA j0 a) p)
          + ∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) • pderiv (idxA j0 b) p := by
        rw [sum_pderiv_vec_eval, ymGaussDer_apply]

/-- The colour-adjointness of the deformed ladder generators on the `A`-block. -/
theorem derOp_comm_gauss (G : GaugeAlgebra 8) (d : Fin 8) (j0 : Fin 3) (a : Fin 8) :
    derOp (idxA j0 a) * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap * derOp (idxA j0 a)
        + ∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) • derOp (idxA j0 b) := by
  have h1 : mulOp (X (idxA j0 a)) * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap * mulOp (X (idxA j0 a))
        + ∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) • mulOp (X (idxA j0 b)) := by
    have h := mulOp_X_comm_deriv G d (idxA j0 a)
    rw [ymGaussVec_idxA, mulOp_sum] at h
    have hsm : ∀ i : Fin 8, mulOp (((G.f a i d : ℝ) : ℂ) • X (idxA j0 i))
        = ((G.f a i d : ℝ) : ℂ) • mulOp (X (idxA j0 i)) := by
      intro i
      refine LinearMap.ext fun p => ?_
      rw [LinearMap.smul_apply, mulOp_apply, mulOp_apply, smul_eq_C_mul, mul_assoc, C_mul']
    rw [Finset.sum_congr rfl fun i _ => hsm i] at h
    have hneg : (∑ i : Fin 8, ((G.f a i d : ℝ) : ℂ) • mulOp (X (idxA j0 i)))
        = -∑ i : Fin 8, ((G.f i a d : ℝ) : ℂ) • mulOp (X (idxA j0 i)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [G.antisymm]
      push_cast
      rw [← neg_one_mul, mul_smul, neg_one_smul]
    rw [hneg] at h
    rw [← h]
    abel
  have h2 := pderiv_comm_gaussVec G d j0 a
  have hsum : (∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) •
        ((pderiv (idxA j0 b)).toLinearMap
          - ((1 / 2 : ℝ) : ℂ) • mulOp (X (idxA j0 b))))
      = (∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) • (pderiv (idxA j0 b)).toLinearMap)
        - ((1 / 2 : ℝ) : ℂ) •
            ∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) • mulOp (X (idxA j0 b)) := by
    rw [Finset.sum_congr rfl fun b _ => by rw [smul_sub]]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm]
  change (pderiv (idxA j0 a)).toLinearMap * (ymGaussDer G d).toLinearMap
      - ((1 / 2 : ℝ) : ℂ) • (mulOp (X (idxA j0 a)) * (ymGaussDer G d).toLinearMap)
      = (ymGaussDer G d).toLinearMap * ((pderiv (idxA j0 a)).toLinearMap
          - ((1 / 2 : ℝ) : ℂ) • mulOp (X (idxA j0 a)))
        + ∑ b : Fin 8, ((G.f b a d : ℝ) : ℂ) •
            ((pderiv (idxA j0 b)).toLinearMap - ((1 / 2 : ℝ) : ℂ) • mulOp (X (idxA j0 b)))
  rw [hsum, h2, h1, mul_sub, smul_add, mul_smul_comm]
  abel

/-- A sum of squares of an adjoint family commutes with the derivation. -/
theorem sum_sq_comm_of_adjoint {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℂ YmPoly)
    (D : Module.End ℂ YmPoly) (C : ι → ι → ℂ)
    (hanti : ∀ i b, C b i = -C i b)
    (h : ∀ i, T i * D = D * T i + ∑ b, C b i • T b) :
    (∑ i, T i * T i) * D = D * (∑ i, T i * T i) := by
  have hstep : ∀ i, T i * T i * D
      = D * (T i * T i) + ∑ b, C b i • (T i * T b + T b * T i) := by
    intro i
    have hTD : T i * D = D * T i + ∑ b, C b i • T b := by
      rw [h i]
    calc T i * T i * D
        = T i * (D * T i) + ∑ b, C b i • (T i * T b) := by
          rw [mul_assoc, hTD, mul_add, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun b _ => by rw [mul_smul_comm]
      _ = (D * T i) * T i + (∑ b, C b i • T b) * T i
            + ∑ b, C b i • (T i * T b) := by
          have hmid : T i * (D * T i) = (D * T i) * T i + (∑ b, C b i • T b) * T i := by
            rw [← mul_assoc, hTD, add_mul]
          rw [hmid]
      _ = D * (T i * T i) + (∑ b, C b i • (T b * T i))
            + ∑ b, C b i • (T i * T b) := by
          rw [← mul_assoc, Finset.sum_mul]
          simp only [smul_mul_assoc]
      _ = D * (T i * T i) + (∑ b, C b i • (T i * T b)
            + ∑ b, C b i • (T b * T i)) := by
          abel
      _ = D * (T i * T i) + ∑ b, C b i • (T i * T b + T b * T i) := by
          rw [← Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_congr rfl fun b _ => by rw [smul_add]
  set S := ∑ i, ∑ b, C b i • (T i * T b + T b * T i) with hSdef
  have hsym : ∀ i b, C b i • (T i * T b + T b * T i)
      = -(C i b • (T b * T i + T i * T b)) := by
    intro i b
    have hAB : T b * T i + T i * T b = T i * T b + T b * T i := by abel
    have hsc : ((-C i b : ℂ)) • (T i * T b + T b * T i)
        = -(C i b • (T i * T b + T b * T i)) := by
      rw [← neg_one_mul, mul_smul, neg_one_smul]
    conv_lhs => rw [hanti i b]
    conv_rhs => rw [hAB]
    rw [hsc]
  have hS : S = -S := by
    calc S = ∑ i, ∑ b, -(C i b • (T b * T i + T i * T b)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => hsym i b
      _ = -(∑ i, ∑ b, C i b • (T b * T i + T i * T b)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_neg_distrib]
      _ = -(∑ b, ∑ i, C i b • (T b * T i + T i * T b)) := by
          rw [Finset.sum_comm]
      _ = -S := by
          rw [hSdef]
  have h2 : S + S = 0 := by
    nth_rewrite 1 [hS]
    exact neg_add_cancel S
  have h3 : (2 : ℂ) • S = 0 := by
    rw [two_smul]
    exact h2
  have hzero : S = 0 := (smul_eq_zero.mp h3).resolve_left (by norm_num)
  have hsum : (∑ i, T i * T i * D) = (∑ i, D * (T i * T i)) + S := by
    rw [show (∑ i, T i * T i * D)
        = ∑ i, (D * (T i * T i) + ∑ b, C b i • (T i * T b + T b * T i)) from
      Finset.sum_congr rfl fun i _ => hstep i]
    rw [Finset.sum_add_distrib, hSdef]
  rw [Finset.sum_mul, Finset.mul_sum, hsum, hzero, add_zero]

/-- The colour-rotation coefficient matrix on the `A`-block. -/
def rotCoeff (G : GaugeAlgebra 8) (d : Fin 8) :
    Fin 3 × Fin 8 → Fin 3 × Fin 8 → ℂ :=
  fun p q => if p.1 = q.1 then ((G.f p.2 q.2 d : ℝ) : ℂ) else 0

/-- The coefficient matrix is antisymmetric. -/
theorem rotCoeff_anticomm (G : GaugeAlgebra 8) (d : Fin 8) (p q : Fin 3 × Fin 8) :
    rotCoeff G d q p = -rotCoeff G d p q := by
  unfold rotCoeff
  by_cases h : p.1 = q.1
  · rw [if_pos h, if_pos h.symm, G.antisymm]
    push_cast
    ring
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp

/-- The adjoint action of the constraint, in the coefficient matrix's terms. -/
theorem sum_rotCoeff (G : GaugeAlgebra 8) (d : Fin 8) (p : Fin 3 × Fin 8) :
    (∑ q : Fin 3 × Fin 8, rotCoeff G d q p • derOp (idxA q.1 q.2))
      = ∑ b : Fin 8, ((G.f b p.2 d : ℝ) : ℂ) • derOp (idxA p.1 b) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_eq_single p.1]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [rotCoeff]
  · intro j _ hj
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hjb : j = p.1
    · exact absurd hjb hj
    · simp [rotCoeff, hjb]
  · intro hmem
    exact absurd (Finset.mem_univ p.1) hmem

/-- `[Σ_{(j,b)} derOp², 𝒢_d] = 0`. -/
theorem derOpSq_comm (G : GaugeAlgebra 8) (d : Fin 8) :
    (∑ p : Fin 3 × Fin 8, derOp (idxA p.1 p.2) * derOp (idxA p.1 p.2))
        * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap
        * ∑ p : Fin 3 × Fin 8, derOp (idxA p.1 p.2) * derOp (idxA p.1 p.2) := by
  refine sum_sq_comm_of_adjoint (T := fun p : Fin 3 × Fin 8 => derOp (idxA p.1 p.2))
    (D := (ymGaussDer G d).toLinearMap) (C := rotCoeff G d) ?_ ?_
  · intro p q
    exact rotCoeff_anticomm G d p q
  · intro p
    rw [derOp_comm_gauss G d p.1 p.2, sum_rotCoeff G d p]

/-- `[Σ_{(j,b)} π², 𝒢_d] = 0` for the momenta `π = −i ∂`. -/
theorem momSq_comm (G : GaugeAlgebra 8) (d : Fin 8) :
    (∑ p : Fin 3 × Fin 8, momOp (idxA p.1 p.2) * momOp (idxA p.1 p.2))
        * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap
        * ∑ p : Fin 3 × Fin 8, momOp (idxA p.1 p.2) * momOp (idxA p.1 p.2) := by
  have hsq : ∀ p : Fin 3 × Fin 8,
      momOp (idxA p.1 p.2) * momOp (idxA p.1 p.2)
        = (-1 : ℂ) • (derOp (idxA p.1 p.2) * derOp (idxA p.1 p.2)) := by
    intro p
    rw [momOp, smul_mul_smul_comm]
    norm_num
  rw [Finset.sum_congr rfl fun p _ => hsq p, ← Finset.smul_sum]
  rw [smul_mul_assoc, mul_smul_comm, derOpSq_comm G d]

end Concretize

end BookProof.Qym.GaussCasimir
