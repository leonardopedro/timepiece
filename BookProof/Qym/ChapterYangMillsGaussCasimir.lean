import BookProof.ChapterBrstYmCommute
import BookProof.Qym.ChapterYangMillsHermite

/-!
# `[H, Ω] = 0` for the concrete Weyl-gauge Yang–Mills model

`BookProof/ChapterBrstYmCommute.lean` proves the constraint-algebra half of
`[H, Ω] = 0` for the concrete Weyl-gauge Yang–Mills Hamiltonian and BRST charge, and
names the two Casimir lemmas its Hamiltonian half consumes.  This module proves both of
them on the polynomial core and closes the commutator:

* `momSq_comm` — `[Σ_{j,a} π_{ja}², 𝒢_d] = 0`, the kinetic term of
  `H = ½ Σ π² + ½ Σ B²`, for every colour `d`;
* `magSq_comm` — `[Σ_{(i,a)} B_{ia}², 𝒢_d] = 0`, the magnetic term (second section);
* `ymOmega_comm_ymH` — `[Ω, H] = 0`, with `H = ymH`, together with the membership
  corollaries `ymH_mem_physicalStates` / `ymH_mem_exactStates`.

## The kinetic term

A gauge rotation acts on the `A`-block as the linear colour rotation at fixed spatial
index, so

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

The magnetic term is different in kind — the field strength is cubic, and its adjoint
transformation is where the Jacobi identity of the gauge algebra enters; the second
section records that development (`magJacobi` → `ymGaussDer_magPoly` → `magSq_comm`).

## Boundary

`[H, Ω] = 0` holds for the constant-multiplet model (`G.D = 0`), the same regime the
corpus's other invariance theorems carry; `BookProof/ChapterBrstYmCommute.lean`'s
"Honest boundary" explains why the `D`-part is not translation covariant in this
realization.  What is *not* proved here is the passage of `Ω` and `H` to the completed
Hilbert space — this is the algebraic identity on the polynomial core, which is the
missing hypothesis of the reduced-transfer chapters.

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

/-! ## The magnetic half, and `[H, Ω] = 0`

The deformed-ladder route above covers the kinetic term.  The magnetic term is the
field strength transforming in the adjoint, which is where the Jacobi identity enters:

* `mulOp_comm_deriv` — `[mulOp f, 𝒢_d] = −mulOp (𝒢_d f)`, the commutator of a
  multiplication operator with the derivation;
* `magJacobi` — the contracted Jacobi identity
  `Σ_g f_{agc} f_{gbd} + Σ_g f_{abg} f_{gcd} = Σ_g f_{agd} f_{gbc}`;
* `ymGaussDer_magPoly` — `𝒢_d B_{ia} = Σ_g f_{agd} B_{ig}`, the adjoint transformation of
  the field strength, assembled from the coordinate lemmas `ymGaussDer_X_idxA` /
  `ymGaussDer_X_idxD`, the cubic contraction `ymGaussDer_magCubic`, and the summation
  reordering `magPoly_adjoint_sum`;
* `magSq_comm` — `[Σ_{(i,a)} B_{ia}², 𝒢_d] = 0`, by `sum_sq_comm_of_adjoint` again, with
  the coefficient matrix `rotCoeff` read off `ymGaussDer_magPoly`;
* `ymHamPoly_comm` — `[H, 𝒢_d] = 0` for `H = ½ Σ π² + ½ Σ B²` on the polynomial core
  (`ymHamPoly`, the polynomial form of `BookProof.YangMillsHermite.ymHamiltonian`);
* `ymOmega_comm_ymH` — `[Ω, H] = 0` for the concrete Weyl-gauge model, one application of
  `brstCharge_comm_of_comm`;
* `ymH_mem_physicalStates` / `ymH_mem_exactStates` — `H` preserves the BRST-closed
  (`ymPhysicalStates`) and BRST-exact (`ymExactStates`) states, so the dynamics descends
  to the cohomology.

Everything is `sorry`-free and axiom-free beyond `propext` / `Classical.choice` /
`Quot.sound`.
-/

theorem mulOp_comm_deriv (G : GaugeAlgebra 8) (d : Fin 8) (f : YmPoly) :
    mulOp f * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap * mulOp f - mulOp (ymGaussDer G d f) := by
  refine LinearMap.ext fun p => ?_
  rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.mul_apply, mulOp_apply, mulOp_apply]
  change f * (ymGaussDer G d) p
    = (ymGaussDer G d) (f * p) - (ymGaussDer G d) f * p
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem ymGaussDer_X (G : GaugeAlgebra 8) (d : Fin 8) (m : Fin 99) :
    ymGaussDer G d (X m) = ymGaussVec G d m :=
  MvPolynomial.mkDerivation_X (R := ℂ) (ymGaussVec G d) m

theorem ymGaussDer_X_idxA (G : GaugeAlgebra 8) (d : Fin 8) (j : Fin 3) (b : Fin 8) :
    ymGaussDer G d (X (idxA j b)) = ∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxA j g) := by
  rw [ymGaussDer_X, ymGaussVec_idxA]

theorem ymGaussDer_X_idxD (G : GaugeAlgebra 8) (d : Fin 8) (j k : Fin 3) (b : Fin 8) :
    ymGaussDer G d (X (idxD j k b))
      = ∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxD j k g) := by
  rw [ymGaussDer_X, ymGaussVec_idxD]

theorem ymGaussDer_magInner (G : GaugeAlgebra 8) (d : Fin 8) (j k : Fin 3) (a : Fin 8) :
    ymGaussDer G d (X (idxD j k a) + ∑ b : Fin 8, ∑ c : Fin 8,
        ((G.f a b c : ℝ) : ℂ) • (X (idxA j b) * X (idxA k c)))
      = (∑ g : Fin 8, ((G.f a g d : ℝ) : ℂ) • X (idxD j k g))
        + ∑ b : Fin 8, ∑ c : Fin 8, ((G.f a b c : ℝ) : ℂ) •
            (ymGaussDer G d (X (idxA j b)) * X (idxA k c)
              + X (idxA j b) * ymGaussDer G d (X (idxA k c))) := by
  rw [map_add, ymGaussDer_X_idxD, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Derivation.map_smul, Derivation.leibniz]
  simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
  ring


theorem magJacobi (G : GaugeAlgebra 8) (a b c d : Fin 8) :
    (∑ g : Fin 8, G.f a g c * G.f g b d) + (∑ g : Fin 8, G.f a b g * G.f g c d)
      = ∑ g : Fin 8, G.f a g d * G.f g b c := by
  have hJ := G.jacobi a b c d
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hJ
  have h3 : (∑ e : Fin 8, G.f c a e * G.f e b d)
      = ∑ g : Fin 8, G.f a g c * G.f g b d := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [G.cyclic c a e]
  have h2 : (∑ e : Fin 8, G.f b c e * G.f e a d)
      = -(∑ e : Fin 8, G.f b c e * G.f a e d) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [G.antisymm e a d]
    ring
  have h2' : (∑ e : Fin 8, G.f b c e * G.f a e d)
      = ∑ g : Fin 8, G.f a g d * G.f g b c := by
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_comm (G.f b c e), G.cyclic b c e, G.cyclic c e b]
  rw [h3, h2, h2'] at hJ
  linarith

theorem sum_swap_idx {M : Type*} [AddCommMonoid M] (F : Fin 8 → Fin 8 → M) :
    (∑ b : Fin 8, ∑ g : Fin 8, F b g) = ∑ b : Fin 8, ∑ g : Fin 8, F g b := by
  rw [Finset.sum_comm]

theorem ymGaussDer_magCubicFirst (G : GaugeAlgebra 8) (d : Fin 8) (a : Fin 8)
    (j k : Fin 3) :
    (∑ b : Fin 8, ∑ c : Fin 8, ((G.f a b c : ℝ) : ℂ) •
        (ymGaussDer G d (X (idxA j b)) * X (idxA k c)))
      = ∑ b : Fin 8, ∑ c : Fin 8,
          ((∑ g : Fin 8, G.f a g c * G.f g b d : ℝ) : ℂ) • (X (idxA j b) * X (idxA k c)) := by
  have hcast : ∀ b c : Fin 8, ((∑ g : Fin 8, G.f a g c * G.f g b d : ℝ) : ℂ)
      = ∑ g : Fin 8, ((G.f a g c : ℝ) : ℂ) * ((G.f g b d : ℝ) : ℂ) := by
    intro b c
    push_cast
    rfl
  have hexp : ∀ b c : Fin 8, ((G.f a b c : ℝ) : ℂ) •
        (ymGaussDer G d (X (idxA j b)) * X (idxA k c))
      = ∑ g : Fin 8, (((G.f a b c : ℝ) : ℂ) * ((G.f b g d : ℝ) : ℂ)) •
          (X (idxA j g) * X (idxA k c)) := by
    intro b c
    rw [ymGaussDer_X_idxA, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_mul_assoc, smul_smul]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => hexp b c]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun c _ =>
    sum_swap_idx (fun b g => (((G.f a b c : ℝ) : ℂ) * ((G.f b g d : ℝ) : ℂ)) •
      (X (idxA j g) * X (idxA k c)))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hcast b c, Finset.sum_smul]

theorem ymGaussDer_magCubicSecond (G : GaugeAlgebra 8) (d : Fin 8) (a : Fin 8)
    (j k : Fin 3) :
    (∑ b : Fin 8, ∑ c : Fin 8, ((G.f a b c : ℝ) : ℂ) •
        (X (idxA j b) * ymGaussDer G d (X (idxA k c))))
      = ∑ b : Fin 8, ∑ c : Fin 8,
          ((∑ g : Fin 8, G.f a b g * G.f g c d : ℝ) : ℂ) • (X (idxA j b) * X (idxA k c)) := by
  have hcast : ∀ b c : Fin 8, ((∑ g : Fin 8, G.f a b g * G.f g c d : ℝ) : ℂ)
      = ∑ g : Fin 8, ((G.f a b g : ℝ) : ℂ) * ((G.f g c d : ℝ) : ℂ) := by
    intro b c
    push_cast
    rfl
  have hexp : ∀ b c : Fin 8, ((G.f a b c : ℝ) : ℂ) •
        (X (idxA j b) * ymGaussDer G d (X (idxA k c)))
      = ∑ g : Fin 8, (((G.f a b c : ℝ) : ℂ) * ((G.f c g d : ℝ) : ℂ)) •
          (X (idxA j b) * X (idxA k g)) := by
    intro b c
    rw [ymGaussDer_X_idxA, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_smul_comm, smul_smul]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => hexp b c]
  rw [Finset.sum_congr rfl fun b _ =>
    sum_swap_idx (fun c g => (((G.f a b c : ℝ) : ℂ) * ((G.f c g d : ℝ) : ℂ)) •
      (X (idxA j b) * X (idxA k g)))]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hcast b c, Finset.sum_smul]

theorem ymGaussDer_magCubic (G : GaugeAlgebra 8) (d : Fin 8) (a : Fin 8) (j k : Fin 3) :
    (∑ b : Fin 8, ∑ c : Fin 8, ((G.f a b c : ℝ) : ℂ) •
        (ymGaussDer G d (X (idxA j b)) * X (idxA k c)
          + X (idxA j b) * ymGaussDer G d (X (idxA k c))))
      = ∑ b : Fin 8, ∑ c : Fin 8,
          ((∑ g : Fin 8, G.f a g d * G.f g b c : ℝ) : ℂ) • (X (idxA j b) * X (idxA k c)) := by
  simp only [smul_add, Finset.sum_add_distrib]
  rw [ymGaussDer_magCubicFirst, ymGaussDer_magCubicSecond, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← add_smul]
  have h := magJacobi G a b c d
  rw [← Complex.ofReal_add, h]


theorem sum_rotate3 {M : Type*} [AddCommMonoid M] (F : Fin 8 → Fin 3 → Fin 3 → M) :
    (∑ g : Fin 8, ∑ j : Fin 3, ∑ k : Fin 3, F g j k)
      = ∑ j : Fin 3, ∑ k : Fin 3, ∑ g : Fin 8, F g j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

theorem sum_rotate5 {M : Type*} [AddCommMonoid M]
    (F : Fin 8 → Fin 3 → Fin 3 → Fin 8 → Fin 8 → M) :
    (∑ g : Fin 8, ∑ j : Fin 3, ∑ k : Fin 3, ∑ b : Fin 8, ∑ c : Fin 8, F g j k b c)
      = ∑ j : Fin 3, ∑ k : Fin 3, ∑ b : Fin 8, ∑ c : Fin 8, ∑ g : Fin 8, F g j k b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem magPoly_adjoint_sum (G : GaugeAlgebra 8) (d : Fin 8) (i : Fin 3) (a : Fin 8) :
    (∑ g : Fin 8, ((G.f a g d : ℝ) : ℂ) • magPoly G.f i g)
      = ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
          ((∑ g : Fin 8, ((G.f a g d : ℝ) : ℂ) • (X (idxD j k g) : YmPoly))
            + ∑ b : Fin 8, ∑ c : Fin 8,
                ((∑ g : Fin 8, G.f a g d * G.f g b c : ℝ) : ℂ) •
                  (((X (idxA j b) : YmPoly) * X (idxA k c)))) := by
  have hcast : ∀ b c : Fin 8, ((∑ g : Fin 8, G.f a g d * G.f g b c : ℝ) : ℂ)
      = ∑ g : Fin 8, ((G.f a g d : ℝ) : ℂ) * ((G.f g b c : ℝ) : ℂ) := by
    intro b c
    push_cast
    rfl
  have hD : (∑ g : Fin 8, ∑ j : Fin 3, ∑ k : Fin 3,
        (((G.f a g d : ℝ) : ℂ) * ((levi i j k : ℝ) : ℂ)) • (X (idxD j k g) : YmPoly))
      = ∑ j : Fin 3, ∑ k : Fin 3, ∑ g : Fin 8,
        (((levi i j k : ℝ) : ℂ) * ((G.f a g d : ℝ) : ℂ)) • (X (idxD j k g) : YmPoly) := by
    rw [sum_rotate3]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm]
  have hC1 : (∑ j : Fin 3, ∑ k : Fin 3, ∑ b : Fin 8, ∑ c : Fin 8,
        (((levi i j k : ℝ) : ℂ) * ((∑ g : Fin 8, G.f a g d * G.f g b c : ℝ) : ℂ))
          • (((X (idxA j b) : YmPoly) * X (idxA k c))))
      = ∑ j : Fin 3, ∑ k : Fin 3, ∑ b : Fin 8, ∑ c : Fin 8,
        (((levi i j k : ℝ) : ℂ) *
            ∑ g : Fin 8, ((G.f a g d : ℝ) : ℂ) * ((G.f g b c : ℝ) : ℂ))
          • (((X (idxA j b) : YmPoly) * X (idxA k c))) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hcast b c]
  have hC2 : (∑ j : Fin 3, ∑ k : Fin 3, ∑ b : Fin 8, ∑ c : Fin 8,
        (((levi i j k : ℝ) : ℂ) *
            ∑ g : Fin 8, ((G.f a g d : ℝ) : ℂ) * ((G.f g b c : ℝ) : ℂ))
          • (((X (idxA j b) : YmPoly) * X (idxA k c))))
      = ∑ g : Fin 8, ∑ j : Fin 3, ∑ k : Fin 3, ∑ b : Fin 8, ∑ c : Fin 8,
        (((G.f a g d : ℝ) : ℂ) * (((levi i j k : ℝ) : ℂ) * ((G.f g b c : ℝ) : ℂ)))
          • (((X (idxA j b) : YmPoly) * X (idxA k c))) := by
    simp only [Finset.mul_sum, Finset.sum_smul]
    rw [← sum_rotate5]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    congr 1
    ring
  simp only [magPoly, Finset.smul_sum, smul_add, smul_smul, Finset.sum_add_distrib]
  rw [hD, ← hC2, ← hC1]

theorem ymGaussDer_msum {n : ℕ} (G : GaugeAlgebra 8) (d : Fin 8) (F : Fin n → YmPoly) :
    ymGaussDer G d (∑ i, F i) = ∑ i, ymGaussDer G d (F i) := by
  exact map_sum (ymGaussDer G d).toLinearMap F Finset.univ

theorem ymGaussDer_magPoly_expanded (G : GaugeAlgebra 8) (d : Fin 8) (i : Fin 3) (a : Fin 8) :
    ymGaussDer G d (magPoly G.f i a)
      = ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
          ((∑ g : Fin 8, ((G.f a g d : ℝ) : ℂ) • X (idxD j k g))
            + ∑ b : Fin 8, ∑ c : Fin 8,
                ((∑ g : Fin 8, G.f a g d * G.f g b c : ℝ) : ℂ) •
                  (X (idxA j b) * X (idxA k c))) := by
  simp only [magPoly]
  rw [ymGaussDer_msum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ymGaussDer_msum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.map_smul, ymGaussDer_magInner, ymGaussDer_magCubic]

theorem ymGaussDer_magPoly (G : GaugeAlgebra 8) (d : Fin 8) (i : Fin 3) (a : Fin 8) :
    ymGaussDer G d (magPoly G.f i a)
      = ∑ g : Fin 8, ((G.f a g d : ℝ) : ℂ) • magPoly G.f i g :=
  (ymGaussDer_magPoly_expanded G d i a).trans (magPoly_adjoint_sum G d i a).symm

theorem mulOp_smul (c : ℂ) (f : YmPoly) : mulOp (c • f) = c • mulOp f := by
  refine LinearMap.ext fun p => ?_
  rw [mulOp_apply, LinearMap.smul_apply, mulOp_apply, smul_mul_assoc]

theorem mulOp_ymGaussDer_magPoly (G : GaugeAlgebra 8) (d : Fin 8) (i : Fin 3) (a : Fin 8) :
    mulOp (ymGaussDer G d (magPoly G.f i a))
      = ∑ g : Fin 8, ((G.f a g d : ℝ) : ℂ) • mulOp (magPoly G.f i g) := by
  rw [ymGaussDer_magPoly, mulOp_sum]
  exact Finset.sum_congr rfl fun g _ => mulOp_smul _ _

theorem sum_rotCoeff_mag (G : GaugeAlgebra 8) (d : Fin 8) (p : Fin 3 × Fin 8) :
    (∑ q : Fin 3 × Fin 8, rotCoeff G d q p • mulOp (magPoly G.f q.1 q.2))
      = ∑ b : Fin 8, ((G.f b p.2 d : ℝ) : ℂ) • mulOp (magPoly G.f p.1 b) := by
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

set_option maxHeartbeats 800000 in
-- keyed matching of the two adjoint lemmas on the `99`-variable field strength costs
-- far more than the default budget
theorem mulOp_magSq_adjoint (G : GaugeAlgebra 8) (d : Fin 8) (p : Fin 3 × Fin 8) :
    mulOp (magPoly G.f p.1 p.2) * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap * mulOp (magPoly G.f p.1 p.2)
        + ∑ q : Fin 3 × Fin 8, rotCoeff G d q p • mulOp (magPoly G.f q.1 q.2) := by
  have h1 : mulOp (magPoly G.f p.1 p.2) * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap * mulOp (magPoly G.f p.1 p.2)
        - mulOp (ymGaussDer G d (magPoly G.f p.1 p.2)) :=
    mulOp_comm_deriv G d (magPoly G.f p.1 p.2)
  rw [h1]
  have h2 : mulOp (ymGaussDer G d (magPoly G.f p.1 p.2))
      = ∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • mulOp (magPoly G.f p.1 g) :=
    mulOp_ymGaussDer_magPoly G d p.1 p.2
  rw [h2]
  rw [sub_eq_add_neg, sum_rotCoeff_mag, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [G.antisymm p.2 b d]
  push_cast
  have hs : (-(↑(G.f b p.2 d) : ℂ)) • mulOp (magPoly G.f p.1 b)
      = -((↑(G.f b p.2 d) : ℂ) • mulOp (magPoly G.f p.1 b)) :=
    neg_smul (↑(G.f b p.2 d) : ℂ) (mulOp (magPoly G.f p.1 b))
  rw [hs, neg_neg]

theorem magSq_comm (G : GaugeAlgebra 8) (d : Fin 8) :
    (∑ p : Fin 3 × Fin 8, mulOp (magPoly G.f p.1 p.2) * mulOp (magPoly G.f p.1 p.2))
        * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap
        * ∑ p : Fin 3 × Fin 8, mulOp (magPoly G.f p.1 p.2) * mulOp (magPoly G.f p.1 p.2) :=
  sum_sq_comm_of_adjoint (T := fun p : Fin 3 × Fin 8 => mulOp (magPoly G.f p.1 p.2))
    (D := (ymGaussDer G d).toLinearMap) (C := rotCoeff G d)
    (fun p q => rotCoeff_anticomm G d p q) (fun p => mulOp_magSq_adjoint G d p)

theorem decodeSpace_finProdFinEquiv (j : Fin 3) (a : Fin 8) :
    decodeSpace (finProdFinEquiv (j, a)) = j := by
  apply Fin.ext
  have hv : (finProdFinEquiv (j, a)).val = a.val + 8 * j.val :=
    finProdFinEquiv_apply_val (j, a)
  change (finProdFinEquiv (j, a)).val / 8 = j.val
  rw [hv]
  have := a.isLt
  omega

theorem decodeColor_finProdFinEquiv (j : Fin 3) (a : Fin 8) :
    decodeColor (finProdFinEquiv (j, a)) = a := by
  apply Fin.ext
  have hv : (finProdFinEquiv (j, a)).val = a.val + 8 * j.val :=
    finProdFinEquiv_apply_val (j, a)
  change (finProdFinEquiv (j, a)).val % 8 = a.val
  rw [hv]
  have := a.isLt
  omega

/-- The `24` field/colour pairs are the `3 × 8` spatial/colour pairs. -/
theorem sum_fin24 (F : Fin 3 → Fin 8 → Module.End ℂ YmPoly) :
    (∑ m : Fin 24, F (decodeSpace m) (decodeColor m))
      = ∑ p : Fin 3 × Fin 8, F p.1 p.2 := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m := 3) (n := 8))
    (fun m => F (decodeSpace m) (decodeColor m))]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨j, a⟩ := p
  rw [decodeSpace_finProdFinEquiv, decodeColor_finProdFinEquiv]

/-- The **Yang–Mills Hamiltonian on the polynomial core**,
`H = ½ Σ_m π_m² + ½ Σ_m B_m²` — the polynomial form of
`BookProof.YangMillsHermite.ymHamiltonian` (`weylOp`), in the positive convention. -/
noncomputable def ymHamPoly (G : GaugeAlgebra 8) : Module.End ℂ YmPoly :=
  (1 / 2 : ℂ) •
    ((∑ m : Fin 24, momOp (idxA (decodeSpace m) (decodeColor m))
        * momOp (idxA (decodeSpace m) (decodeColor m)))
      + ∑ m : Fin 24, mulOp (magPoly G.f (decodeSpace m) (decodeColor m))
          * mulOp (magPoly G.f (decodeSpace m) (decodeColor m)))

theorem ymHamPoly_eq (G : GaugeAlgebra 8) :
    ymHamPoly G
      = (1 / 2 : ℂ) •
          ((∑ p : Fin 3 × Fin 8, momOp (idxA p.1 p.2) * momOp (idxA p.1 p.2))
            + ∑ p : Fin 3 × Fin 8,
                mulOp (magPoly G.f p.1 p.2) * mulOp (magPoly G.f p.1 p.2)) := by
  unfold ymHamPoly
  rw [sum_fin24 (fun j a => momOp (idxA j a) * momOp (idxA j a)),
    sum_fin24 (fun j a => mulOp (magPoly G.f j a) * mulOp (magPoly G.f j a))]

/-- `[H, 𝒢_d] = 0` on the polynomial core, from the two Casimir lemmas. -/
theorem ymHamPoly_comm (G : GaugeAlgebra 8) (d : Fin 8) :
    ymHamPoly G * (ymGaussDer G d).toLinearMap
      = (ymGaussDer G d).toLinearMap * ymHamPoly G := by
  rw [ymHamPoly_eq, smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
    momSq_comm G d, magSq_comm G d]

/-- The Hamiltonian on the graded `99`-coordinate state space. -/
noncomputable def ymH (G : GaugeAlgebra 8) : Module.End ℂ YmBookState :=
  ymBos (ymHamPoly G)

/-- **The Hamiltonian commutes with every constraint**, `[H, 𝒢_a] = 0`. -/
theorem ymGauss_comm_ymH (G : GaugeAlgebra 8) (a : Fin 8) :
    ymGauss G a * ymH G = ymH G * ymGauss G a := by
  change ymBos (ymGaussPoly G a) * ymBos (ymHamPoly G)
    = ymBos (ymHamPoly G) * ymBos (ymGaussPoly G a)
  rw [← ymBos_mul, ← ymBos_mul]
  change ymBos ((ymGaussDer G a).toLinearMap * ymHamPoly G)
    = ymBos (ymHamPoly G * (ymGaussDer G a).toLinearMap)
  rw [ymHamPoly_comm G a]

/-- **The BRST charge commutes with the Hamiltonian**: `[Ω, H] = 0`. -/
theorem ymOmega_comm_ymH (G : GaugeAlgebra 8) :
    ymOmega G * ymH G = ymH G * ymOmega G := by
  have hGc : ∀ a : Fin 8, ymGauss G a * ymH G = ymH G * ymGauss G a :=
    ymGauss_comm_ymH G
  have hχ : ∀ a : Fin 8, ymChi a * ymH G = ymH G * ymChi a := fun a =>
    (ymBos_ymGh_comm (ymHamPoly G) (ghostCreN a)).symm
  have hβ : ∀ a : Fin 8, ymBeta a * ymH G = ymH G * ymBeta a := fun a =>
    (ymBos_ymGh_comm (ymHamPoly G) (ghostAnnN a)).symm
  have h := BookProof.BookBrstGaugeFixing.brstCharge_comm_of_comm
    (R := Module.End ℂ YmBookState) (f := G.f)
    (Gc := ymGauss G) (χ := ymChi) (β := ymBeta) hGc hχ hβ
  rw [ymOmega, smul_mul_assoc, mul_smul_comm, h]

/-- **Physical states** of the concrete Yang–Mills model: the kernel of `Ω`. -/
def ymPhysicalStates (G : GaugeAlgebra 8) : Submodule ℂ YmBookState :=
  LinearMap.ker (ymOmega G)

/-- **BRST-exact states** of the concrete Yang–Mills model: the range of `Ω`. -/
def ymExactStates (G : GaugeAlgebra 8) : Submodule ℂ YmBookState :=
  LinearMap.range (ymOmega G)

/-- The Hamiltonian preserves the physical states. -/
theorem ymH_mem_physicalStates (G : GaugeAlgebra 8) {v : YmBookState}
    (hv : v ∈ ymPhysicalStates G) : ymH G v ∈ ymPhysicalStates G := by
  change ymOmega G (ymH G v) = 0
  have hv' : ymOmega G v = 0 := hv
  have h := congrArg (fun T : Module.End ℂ YmBookState => T v) (ymOmega_comm_ymH G)
  simpa [Module.End.mul_apply, hv'] using h

/-- The Hamiltonian preserves the BRST-exact states, so `H` descends to the cohomology. -/
theorem ymH_mem_exactStates (G : GaugeAlgebra 8) {v : YmBookState}
    (hv : v ∈ ymExactStates G) : ymH G v ∈ ymExactStates G := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨ymH G w, ?_⟩
  have h := congrArg (fun T : Module.End ℂ YmBookState => T w) (ymOmega_comm_ymH G)
  simpa [Module.End.mul_apply] using h

end BookProof.Qym.GaussCasimir
