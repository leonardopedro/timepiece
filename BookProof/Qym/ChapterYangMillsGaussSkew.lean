import BookProof.Qym.ChapterYangMillsGaussCasimir

/-!
# The Gauss constraint on the completed Mehler core

`BookProof/Qym/ChapterYangMillsGaussCasimir.lean` proves `[H, 𝒢_d] = 0` on the
polynomial algebra `ℂ[X₀,…,X₉₈]`, and its docstring names the passage to the completed
Hilbert space as the remaining input of the reduced-transfer chapters.  This module takes
the *infinitesimal* half of that passage: it realises the Gauss constraint `𝒢_d` as an
operator on the dense Gauss–polynomial core of `L²(ℝ⁹⁹)` and proves the structural facts
wanted there.

## Why `𝒢_d` is skew, not symmetric

`𝒢_d` generates the residual colour rotation, so as an operator it is **skew-adjoint**:
`⟪𝒢_d x, y⟫ = −⟪x, 𝒢_d y⟫`, equivalently `i·𝒢_d` is symmetric.  That is the shape the
ghost current of `Ω = Σ_a c†_a 𝒢_a + …` needs.  The polynomial statement is `PolySkew`
below, the same adjoint pairing as `PolySym` in `ChapterYangMillsHermite`.

## The proof of skewness

`𝒢_d` is the first-order operator `Σ_m v_m ∂_m` of the *linear* vector field
`v_m = ymGaussVec G d m`.  For a general first-order operator the adjoint computation is
exact:

* `gaussInt_mul_pderiv` — one-coordinate integration by parts,
  `∫ h (∂_m f) g = ∫ x_m h f g − ∫ (∂_m h) f g − ∫ h f (∂_m g)`;
* `gaussInt_firstOrder` — summed over `m`,
  `∫ (Σ v_m ∂_m f) g = ∫ ((Σ x_m v_m) f g) − ∫ ((Σ ∂_m v_m) f g) − ∫ f (Σ v_m ∂_m g)`;
* `firstOrder_polySkew` — so a first-order operator is skew as soon as its vector field
  **kills the radius** (`Σ_m x_m v_m = 0`) and is **divergence free**
  (`Σ_m ∂_m v_m = 0`).

For the colour rotation both are the antisymmetry of the structure constants:
`Σ_m x_m v_m = Σ_{b,g} f_{bgd} x_b x_g = 0` (`sum_X_ymGaussVec`, through
`sum_antisymm_quad`), and `∂_m v_m = f_{bbd} = 0` coordinate by coordinate
(`pderiv_ymGaussVec_self`).  This is the operator-level counterpart of the two Casimir
identities: those say the *squares* of the fields commute with `𝒢_d`, this says `𝒢_d`
itself is the generator of a one-parameter family of isometries.

## What is proved here

* `PolySkew`, `gaussInt_neg`, `gaussInt_zero`, `sum_antisymm_quad`,
  `gaussInt_mul_pderiv`, `gaussInt_firstOrder`, `firstOrder_polySkew` — the general
  skew criterion for first-order operators;
* `realCoeff_ymGaussVec`, `sum_X_ymGaussVec`, `pderiv_ymGaussVec_self`,
  `sum_pderiv_ymGaussVec` — the two hypotheses, for the colour rotation;
* `ymGaussPoly_polySkew` — **`𝒢_d` is skew on the polynomial algebra**;
* `coreRep_skewOn_op` — transport to the dense core of `L²(ℝᵈ)`;
* `ymGaussPoly_skewOn_core`, `ymGaussPoly_inner_re_zero` — **`𝒢_d` is skew on the
  completed Gauss–polynomial core**, with vanishing real expectation values;
* `coreRep_op_mul` / `op_add` / `op_sum` / `op_smul` — the transport is a ring map;
* `coreRep_ham_comm_gauss`, `coreRep_ham_comm_gauss_apply` — **`H` preserves the core of
  `𝒢_d` and the two commute there**, the core form of the `DomPreserve` / `StrongCommute`
  hypotheses of `ChapterBrstReducedTransferUnbounded`.  Here `H` is the transported
  polynomial Hamiltonian `Φ.op (ymHamPoly G)`; identifying it with the analytic
  `ymHamiltonian` of `ChapterYangMillsHermite` is a further rewrite that is not carried
  out in this module.

## Boundary

* This is the core, not the closure: no closedness, essential self-adjointness or unitary
  group `e^{−itT}` is claimed for `𝒢_d` or for `H`.  The Friedrichs machinery for the
  abelian sector lives in `ChapterYangMillsGhostSector`; for `f ≠ 0` the quartic magnetic
  term is exactly the open problem recorded there.
* The ghost sector is not completed here.  `𝒢_d` is bosonic; transporting the full charge
  `Ω` needs the ghost Fock completion, which `ChapterYangMillsGhostSector` builds only for
  a *diagonal* (free) ghost Hamiltonian.
* The constant-multiplet regime `G.D = 0` is inherited from `ChapterBrstYmCommute`: the
  Gauss vector field of this realization is the colour rotation alone.
-/

open MvPolynomial

namespace BookProof.Qym.GaussSkew

open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

/-! ## Skew polynomial operators -/

/-- A polynomial-level operator is **Gauss skew** when its adjoint is its negative:
`⟪T p, q⟫ = −⟪p, T q⟫` for the Gaussian inner product. -/
def PolySkew (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) : Prop :=
  PolyAdj T (-T)

theorem gaussInt_neg (r : MvPolynomial (Fin d) ℂ) : gaussInt (-r) = -gaussInt r := by
  have h : (-r) = (-1 : ℂ) • r := by simp
  rw [h, gaussInt_smul]
  ring

theorem gaussInt_zero : gaussInt (0 : MvPolynomial (Fin d) ℂ) = 0 := by
  have h := gaussInt_smul (0 : ℂ) (1 : MvPolynomial (Fin d) ℂ)
  simpa using h

/-- An antisymmetric coefficient matrix kills the quadratic form `Σ_{b,g} c_{bg} x_b x_g`:
the operator-side form of the antisymmetry of the structure constants. -/
theorem sum_antisymm_quad {ι : Type*} [Fintype ι] (c : ι → ι → ℂ)
    (hc : ∀ b g, c b g = -c g b) (u : ι → MvPolynomial (Fin d) ℂ) :
    (∑ b, ∑ g, c b g • (u b * u g)) = 0 := by
  classical
  have hp : ∀ p : ι × ι,
      c p.1 p.2 • (u p.1 * u p.2) = -(c p.2 p.1 • (u p.2 * u p.1)) := by
    intro p
    rw [hc p.2 p.1, neg_smul, neg_neg, mul_comm (u p.1) (u p.2)]
  have key : (∑ b, ∑ g, c b g • (u b * u g))
      = -(∑ b, ∑ g, c b g • (u b * u g)) := by
    calc (∑ b, ∑ g, c b g • (u b * u g))
        = ∑ p : ι × ι, c p.1 p.2 • (u p.1 * u p.2) :=
          (Fintype.sum_prod_type (fun p : ι × ι => c p.1 p.2 • (u p.1 * u p.2))).symm
      _ = ∑ p : ι × ι, -(c p.1 p.2 • (u p.1 * u p.2)) := by
          refine Fintype.sum_equiv (Equiv.prodComm ι ι) _ _ ?_
          intro p
          exact hp p
      _ = -(∑ p : ι × ι, c p.1 p.2 • (u p.1 * u p.2)) := Finset.sum_neg_distrib _
      _ = -(∑ b, ∑ g, c b g • (u b * u g)) := by
          rw [Fintype.sum_prod_type]
  have h2 : (∑ b, ∑ g, c b g • (u b * u g)) + (∑ b, ∑ g, c b g • (u b * u g)) = 0 := by
    nth_rewrite 1 [key]
    exact neg_add_cancel _
  have h3 : (2 : ℂ) • (∑ b, ∑ g, c b g • (u b * u g)) = 0 := by
    rw [two_smul]
    exact h2
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num)

/-! ## The skew criterion for first-order operators -/

/-- The first-order operator `Σ_m v_m ∂_m`. -/
def firstOrder (v : Fin d → MvPolynomial (Fin d) ℂ) :
    Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  ∑ m, mulOp (v m) * (pderiv m).toLinearMap

theorem firstOrder_apply (v : Fin d → MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    firstOrder v p = ∑ m, v m * pderiv m p := by
  rw [firstOrder, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Module.End.mul_apply, mulOp_apply]
  rfl

/-- A first-order operator with real-coefficient vector field commutes with coefficient
conjugation. -/
theorem firstOrder_starP (v : Fin d → MvPolynomial (Fin d) ℂ)
    (hv : ∀ m, RealCoeff (v m)) (p : MvPolynomial (Fin d) ℂ) :
    starP (firstOrder v p) = firstOrder v (starP p) := by
  rw [firstOrder_apply, firstOrder_apply, starP_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [starP_mul, starP_pderiv, hv m]

/-- **One-coordinate integration by parts** for a first-order term:
`∫ h (∂_m f) g = ∫ x_m h f g − ∫ (∂_m h) f g − ∫ h f (∂_m g)`. -/
theorem gaussInt_mul_pderiv (m : Fin d) (h f g : MvPolynomial (Fin d) ℂ) :
    gaussInt (h * pderiv m f * g)
      = gaussInt (X m * (h * f * g)) - gaussInt (pderiv m h * f * g)
        - gaussInt (h * f * pderiv m g) := by
  have key := gaussInt_pderiv m (h * f * g)
  have hexp : pderiv m (h * f * g)
      = pderiv m h * f * g + h * pderiv m f * g + h * f * pderiv m g := by
    rw [pderiv_mul, pderiv_mul]
    ring
  rw [hexp, gaussInt_add, gaussInt_add] at key
  rw [← key]
  ring

/-- **The adjoint computation for a first-order operator**, summed over the coordinates. -/
theorem gaussInt_firstOrder (v : Fin d → MvPolynomial (Fin d) ℂ)
    (f g : MvPolynomial (Fin d) ℂ) :
    gaussInt (firstOrder v f * g)
      = gaussInt ((∑ m, X m * v m) * f * g)
        - gaussInt ((∑ m, pderiv m (v m)) * f * g)
        - gaussInt (f * firstOrder v g) := by
  have hA : (∑ m, X m * (v m * f * g)) = ∑ m, (X m * v m) * (f * g) :=
    Finset.sum_congr rfl fun m _ => by ring
  have hB : (∑ m, (X m * v m) * (f * g)) = (∑ m, X m * v m) * (f * g) :=
    (Finset.sum_mul _ _ _).symm
  have e1 : (∑ m, X m * (v m * f * g)) = (∑ m, X m * v m) * f * g := by
    rw [hA, hB, ← mul_assoc]
  have hC : (∑ m, pderiv m (v m) * f * g) = ∑ m, (pderiv m (v m)) * (f * g) :=
    Finset.sum_congr rfl fun m _ => by ring
  have hE : (∑ m, (pderiv m (v m)) * (f * g)) = (∑ m, pderiv m (v m)) * (f * g) :=
    (Finset.sum_mul _ _ _).symm
  have e2 : (∑ m, pderiv m (v m) * f * g) = (∑ m, pderiv m (v m)) * f * g := by
    rw [hC, hE, ← mul_assoc]
  have e3 : (∑ m, v m * f * pderiv m g) = f * firstOrder v g := by
    conv_lhs => rw [show (∑ m, v m * f * pderiv m g) = ∑ m, f * (v m * pderiv m g) from
      Finset.sum_congr rfl fun m _ => by ring]
    rw [← Finset.mul_sum, firstOrder_apply]
  calc gaussInt (firstOrder v f * g)
      = gaussInt (∑ m, (v m * pderiv m f) * g) := by
        rw [firstOrder_apply, Finset.sum_mul]
    _ = ∑ m, gaussInt ((v m * pderiv m f) * g) := gaussInt_sum _ _
    _ = ∑ m, (gaussInt (X m * (v m * f * g)) - gaussInt (pderiv m (v m) * f * g)
          - gaussInt (v m * f * pderiv m g)) :=
        Finset.sum_congr rfl fun m _ => gaussInt_mul_pderiv m (v m) f g
    _ = (∑ m, gaussInt (X m * (v m * f * g)))
          - (∑ m, gaussInt (pderiv m (v m) * f * g))
          - ∑ m, gaussInt (v m * f * pderiv m g) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = gaussInt (∑ m, X m * (v m * f * g))
          - gaussInt (∑ m, pderiv m (v m) * f * g)
          - gaussInt (∑ m, v m * f * pderiv m g) := by
        rw [← gaussInt_sum, ← gaussInt_sum, ← gaussInt_sum]
    _ = gaussInt ((∑ m, X m * v m) * f * g)
          - gaussInt ((∑ m, pderiv m (v m)) * f * g)
          - gaussInt (f * firstOrder v g) := by
        rw [e1, e2, e3]

/-- **A first-order operator is skew when its vector field kills the radius and is
divergence free.** -/
theorem firstOrder_polySkew (v : Fin d → MvPolynomial (Fin d) ℂ)
    (hv : ∀ m, RealCoeff (v m))
    (hX : ∑ m, X m * v m = 0) (hD : ∑ m, pderiv m (v m) = 0) :
    PolySkew (firstOrder v) := by
  intro p q
  have hstar := firstOrder_starP v hv p
  have h := gaussInt_firstOrder v (starP p) q
  rw [hX, hD] at h
  simp only [zero_mul, gaussInt_zero, sub_zero] at h
  rw [hstar]
  simp only [LinearMap.neg_apply, mul_neg, gaussInt_neg]
  rw [h]
  ring

/-! ## The Gauss vector field satisfies the two hypotheses -/

/-- The Gauss vector field has real coefficients. -/
theorem realCoeff_ymGaussVec (G : GaugeAlgebra 8) (d : Fin 8) (m : Fin 99) :
    RealCoeff (ymGaussVec G d m) := by
  classical
  refine RealCoeff.add (RealCoeff.sum fun p _ => ?_) (RealCoeff.sum fun p _ => ?_)
  · by_cases h : idxA p.1 p.2 = m
    · rw [if_pos h]
      exact RealCoeff.sum fun g _ => RealCoeff.smul (realCoeff_X _)
    · rw [if_neg h]
      exact starP_zero
  · by_cases h : idxD p.1 p.2.1 p.2.2 = m
    · rw [if_pos h]
      exact RealCoeff.sum fun g _ => RealCoeff.smul (realCoeff_X _)
    · rw [if_neg h]
      exact starP_zero

set_option maxHeartbeats 2000000 in
-- the `99`-coordinate `if`-sum and the two reindexings cost far more than the default budget
/-- The `A` block of the "kills the radius" identity, after collapsing the `99`-coordinate
`if`-sum onto the block. -/
theorem sum_X_gaussVec_blockA (G : GaugeAlgebra 8) (d : Fin 8) :
    (∑ m : Fin 99, X m * (∑ p : Fin 3 × Fin 8,
        if idxA p.1 p.2 = m then
          (∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • X (idxA p.1 g)) else (0 : YmPoly)))
      = ∑ j : Fin 3, ∑ b : Fin 8, ∑ g : Fin 8,
          ((G.f b g d : ℝ) : ℂ) • (X (idxA j b) * X (idxA j g)) := by
  conv_lhs =>
    arg 2
    intro m
    rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (idxA j b)]
  · rw [if_pos rfl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [mul_smul_comm]
  · intro m _ hm
    rw [if_neg (Ne.symm hm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

set_option maxHeartbeats 2000000 in
-- the jet block carries a triple product index, so the reindexing is one step longer
/-- The jet block of the "kills the radius" identity. -/
theorem sum_X_gaussVec_blockD (G : GaugeAlgebra 8) (d : Fin 8) :
    (∑ m : Fin 99, X m * (∑ p : Fin 3 × Fin 3 × Fin 8,
        if idxD p.1 p.2.1 p.2.2 = m then
          (∑ g : Fin 8, ((G.f p.2.2 g d : ℝ) : ℂ) • X (idxD p.1 p.2.1 g)) else (0 : YmPoly)))
      = ∑ j : Fin 3, ∑ k : Fin 3, ∑ b : Fin 8, ∑ g : Fin 8,
          ((G.f b g d : ℝ) : ℂ) • (X (idxD j k b) * X (idxD j k g)) := by
  conv_lhs =>
    arg 2
    intro m
    rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (idxD j k b)]
  · rw [if_pos rfl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [mul_smul_comm]
  · intro m _ hm
    rw [if_neg (Ne.symm hm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Splitting the Gauss vector field into its field and jet blocks. -/
theorem ymGaussVec_split (G : GaugeAlgebra 8) (d : Fin 8) (m : Fin 99) :
    ymGaussVec G d m
      = (∑ p : Fin 3 × Fin 8,
          if idxA p.1 p.2 = m then
            (∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • X (idxA p.1 g)) else (0 : YmPoly))
        + ∑ p : Fin 3 × Fin 3 × Fin 8,
            if idxD p.1 p.2.1 p.2.2 = m then
              (∑ g : Fin 8, ((G.f p.2.2 g d : ℝ) : ℂ) • X (idxD p.1 p.2.1 g))
            else (0 : YmPoly) :=
  rfl

/-- An antisymmetric structure-constant matrix annihilates `Σ_{b,g} f_{bgd} u_b u_g`. -/
theorem sum_antisymm_gauss (G : GaugeAlgebra 8) (d : Fin 8) (u : Fin 8 → YmPoly) :
    (∑ b : Fin 8, ∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • (u b * u g)) = 0 := by
  refine sum_antisymm_quad (d := 99) (fun b g => ((G.f b g d : ℝ) : ℂ)) ?_ u
  intro b g
  change ((G.f b g d : ℝ) : ℂ) = -((G.f g b d : ℝ) : ℂ)
  rw [G.antisymm b g d]
  push_cast
  ring

/-- The field block of the "kills the radius" identity vanishes. -/
theorem sum_X_gaussVec_blockA_zero (G : GaugeAlgebra 8) (d : Fin 8) :
    (∑ m : Fin 99, X m * (∑ p : Fin 3 × Fin 8,
        if idxA p.1 p.2 = m then
          (∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • X (idxA p.1 g)) else (0 : YmPoly))) = 0 := by
  rw [sum_X_gaussVec_blockA]
  exact Finset.sum_eq_zero fun j _ => sum_antisymm_gauss G d fun b => X (idxA j b)

/-- The jet block of the "kills the radius" identity vanishes. -/
theorem sum_X_gaussVec_blockD_zero (G : GaugeAlgebra 8) (d : Fin 8) :
    (∑ m : Fin 99, X m * (∑ p : Fin 3 × Fin 3 × Fin 8,
        if idxD p.1 p.2.1 p.2.2 = m then
          (∑ g : Fin 8, ((G.f p.2.2 g d : ℝ) : ℂ) • X (idxD p.1 p.2.1 g))
        else (0 : YmPoly))) = 0 := by
  rw [sum_X_gaussVec_blockD]
  exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ =>
    sum_antisymm_gauss G d fun b => X (idxD j k b)

set_option maxHeartbeats 2000000 in
-- the `99`-coordinate split needs more than the default budget
/-- **The Gauss vector field kills the radius**: `Σ_m x_m v_m = 0`, the antisymmetry of the
structure constants read as `Σ_{b,g} f_{bgd} x_b x_g = 0` on each block. -/
theorem sum_X_ymGaussVec (G : GaugeAlgebra 8) (d : Fin 8) :
    (∑ m : Fin 99, X m * ymGaussVec G d m) = (0 : YmPoly) := by
  have hsplit : (∑ m : Fin 99, X m * ymGaussVec G d m)
      = (∑ m : Fin 99, X m * (∑ p : Fin 3 × Fin 8,
          if idxA p.1 p.2 = m then
            (∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • X (idxA p.1 g)) else (0 : YmPoly)))
        + ∑ m : Fin 99, X m * (∑ p : Fin 3 × Fin 3 × Fin 8,
            if idxD p.1 p.2.1 p.2.2 = m then
              (∑ g : Fin 8, ((G.f p.2.2 g d : ℝ) : ℂ) • X (idxD p.1 p.2.1 g))
            else (0 : YmPoly)) := by
    conv_lhs =>
      arg 2
      intro m
      rw [ymGaussVec_split G d m, mul_add]
    rw [Finset.sum_add_distrib]
  rw [hsplit, sum_X_gaussVec_blockA_zero, sum_X_gaussVec_blockD_zero, add_zero]

/-- The jet block of the Gauss vector field, differentiated in a jet direction. -/
theorem pderiv_idxD_idxD (G : GaugeAlgebra 8) (d : Fin 8) (j0 k0 : Fin 3) (a : Fin 8)
    (j1 k1 : Fin 3) (b : Fin 8) :
    pderiv (idxD j0 k0 a) (∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxD j1 k1 g))
      = if j1 = j0 ∧ k1 = k0 then C ((G.f b a d : ℝ) : ℂ) else (0 : YmPoly) := by
  rw [map_sum]
  have hterm : ∀ g : Fin 8,
      pderiv (idxD j0 k0 a) (((G.f b g d : ℝ) : ℂ) • X (idxD j1 k1 g))
        = if j1 = j0 ∧ k1 = k0 ∧ g = a then C ((G.f b a d : ℝ) : ℂ) else (0 : YmPoly) := by
    intro g
    rw [smul_eq_C_mul, pderiv_C_mul, pderiv_X]
    by_cases h : j1 = j0 ∧ k1 = k0 ∧ g = a
    · obtain ⟨rfl, rfl, rfl⟩ := h
      rw [Pi.single_eq_same, if_pos ⟨rfl, rfl, rfl⟩, mul_one]
    · rw [if_neg h]
      have hne : idxD j1 k1 g ≠ idxD j0 k0 a := by
        intro he
        have hp := idxD_injective (a₁ := (j1, k1, g)) (a₂ := (j0, k0, a)) he
        simp only [Prod.mk.injEq] at hp
        exact h ⟨hp.1, hp.2.1, hp.2.2⟩
      rw [Pi.single_eq_of_ne' (Ne.symm hne), mul_zero]
  rw [Finset.sum_congr rfl fun g _ => hterm g]
  by_cases hj : j1 = j0
  · subst hj
    by_cases hk : k1 = k0
    · subst hk
      rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single a]
      · rw [if_pos ⟨rfl, rfl, rfl⟩]
      · intro g _ hg
        rw [if_neg (by intro hc; exact hg hc.2.2)]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    · rw [if_neg (by intro hc; exact hk hc.2), Finset.sum_eq_zero]
      intro g _
      rw [if_neg (by intro hc; exact hk hc.2.1)]
  · rw [if_neg (by intro hc; exact hj hc.1), Finset.sum_eq_zero]
    intro g _
    rw [if_neg (by intro hc; exact hj hc.1)]

/-- **The Gauss vector field is divergence free**: `∂_m v_m = 0` coordinate by
coordinate, each reading `f_{bbd} = 0`. -/
theorem pderiv_ymGaussVec_self (G : GaugeAlgebra 8) (d : Fin 8) (m : Fin 99) :
    pderiv m (ymGaussVec G d m) = 0 := by
  classical
  have hdiag : ∀ b : Fin 8, G.f b b d = 0 := by
    intro b
    have h := G.antisymm b b d
    linarith
  rcases lt_or_ge m.val 3 with h3 | h3
  · rw [ymGaussVec_x G d m h3, map_zero]
  · rcases lt_or_ge m.val 27 with h27 | h27
    · obtain ⟨j, b, rfl⟩ := idxA_surjective_val m (by omega) h27
      rw [ymGaussVec_idxA, pderiv_linear_idxA (G := G) (d := d) (j0 := j) (a := b)
        (j1 := j) (b := b), if_pos rfl]
      simp [hdiag b]
    · obtain ⟨j, k, b, rfl⟩ := idxD_surjective_val m h27
      rw [ymGaussVec_idxD, pderiv_idxD_idxD (G := G) (d := d) (j0 := j) (k0 := k) (a := b)
        (j1 := j) (k1 := k) (b := b), if_pos ⟨rfl, rfl⟩]
      simp [hdiag b]

/-- The divergence of the Gauss vector field vanishes. -/
theorem sum_pderiv_ymGaussVec (G : GaugeAlgebra 8) (d : Fin 8) :
    ∑ m : Fin 99, pderiv m (ymGaussVec G d m) = 0 :=
  Finset.sum_eq_zero fun m _ => pderiv_ymGaussVec_self G d m

/-- The Gauss derivation is the first-order operator of its vector field. -/
theorem ymGaussPoly_eq_firstOrder (G : GaugeAlgebra 8) (d : Fin 8) :
    ymGaussPoly G d = firstOrder (ymGaussVec G d) := by
  refine LinearMap.ext fun p => ?_
  rw [firstOrder_apply]
  exact ymGaussDer_apply G d p

/-- **The Gauss constraint is skew on the polynomial algebra.** -/
theorem ymGaussPoly_polySkew (G : GaugeAlgebra 8) (d : Fin 8) :
    PolySkew (ymGaussPoly G d) := by
  rw [ymGaussPoly_eq_firstOrder]
  exact firstOrder_polySkew (ymGaussVec G d) (realCoeff_ymGaussVec G d)
    (sum_X_ymGaussVec G d) (sum_pderiv_ymGaussVec G d)

/-! ## Transport to the completed core -/

section Transport

variable {D : Submodule ℂ (L2d d)}

theorem coreRep_op_add (Φ : CoreRep d D)
    (S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    Φ.op (S + T) = Φ.op S + Φ.op T :=
  map_add (Φ.equiv.conj : Module.End ℂ (MvPolynomial (Fin d) ℂ) →+ Module.End ℂ D) S T

theorem coreRep_op_mul (Φ : CoreRep d D)
    (S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    Φ.op (S * T) = Φ.op S * Φ.op T := by
  simp only [CoreRep.op, Module.End.mul_eq_comp, LinearEquiv.conj_comp]

theorem coreRep_op_sum (Φ : CoreRep d D) {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    Φ.op (∑ i ∈ s, T i) = ∑ i ∈ s, Φ.op (T i) :=
  map_sum (Φ.equiv.conj : Module.End ℂ (MvPolynomial (Fin d) ℂ) →+ Module.End ℂ D) T s

theorem coreRep_op_smul (Φ : CoreRep d D) (c : ℂ)
    (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    Φ.op (c • T) = c • Φ.op T :=
  map_smul (Φ.equiv.conj : Module.End ℂ (MvPolynomial (Fin d) ℂ) →ₗ[ℂ] Module.End ℂ D) c T

/-- **A Gauss-skew polynomial operator transports to a skew operator on the core**: its
adjoint is its negative, `⟪T x, y⟫ = −⟪x, T y⟫`. -/
theorem coreRep_skewOn_op (Φ : CoreRep d D) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hT : PolySkew T) (x y : D) :
    inner ℂ ((D.subtype.comp (Φ.op T)) x) ((y : D) : L2d d)
      = -inner ℂ ((x : D) : L2d d) ((D.subtype.comp (Φ.op T)) y) := by
  have hx : (D.subtype.comp (Φ.op T)) x = pgLp (T (Φ.equiv.symm x)) := Φ.coe_op T x
  have hy : (D.subtype.comp (Φ.op T)) y = pgLp (T (Φ.equiv.symm y)) := Φ.coe_op T y
  have hcx : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x) := Φ.coe_symm x
  have hcy : ((y : D) : L2d d) = pgLp (Φ.equiv.symm y) := Φ.coe_symm y
  rw [hx, hy, hcx, hcy, inner_pgLp_pgLp, inner_pgLp_pgLp]
  have h := hT (Φ.equiv.symm x) (Φ.equiv.symm y)
  simp only [LinearMap.neg_apply, mul_neg, gaussInt_neg] at h ⊢
  exact h

end Transport

section Core99

variable {D : Submodule ℂ (L2d 99)}

/-- **The Gauss constraint is skew on the completed Gauss–polynomial core.** -/
theorem ymGaussPoly_skewOn_core (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (x y : D) :
    inner ℂ ((D.subtype.comp (Φ.op (ymGaussPoly G d))) x) ((y : D) : L2d 99)
      = -inner ℂ ((x : D) : L2d 99) ((D.subtype.comp (Φ.op (ymGaussPoly G d))) y) :=
  coreRep_skewOn_op Φ (ymGaussPoly_polySkew G d) x y

/-- The Gauss constraint has vanishing real expectation values on the core — the
infinitesimal form of "it generates isometries". -/
theorem ymGaussPoly_inner_re_zero (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (x : D) :
    (inner ℂ ((D.subtype.comp (Φ.op (ymGaussPoly G d))) x) ((x : D) : L2d 99)).re = 0 := by
  have hskew := ymGaussPoly_skewOn_core G d Φ x x
  have hconj : inner ℂ ((x : D) : L2d 99) ((D.subtype.comp (Φ.op (ymGaussPoly G d))) x)
      = (starRingEnd ℂ)
        (inner ℂ ((D.subtype.comp (Φ.op (ymGaussPoly G d))) x) ((x : D) : L2d 99)) :=
    (inner_conj_symm _ _).symm
  rw [hconj] at hskew
  have hre := congrArg Complex.re hskew
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

/-! ## The Hamiltonian on the core -/

/-- **`H` commutes with the Gauss constraint on the core**: the transported form of
`ymHamPoly_comm`, as an identity of operators on the dense core. -/
theorem coreRep_ham_comm_gauss (G : GaugeAlgebra 8) (d : Fin 8) (Φ : CoreRep 99 D) :
    Φ.op (ymHamPoly G) * Φ.op (ymGaussPoly G d)
      = Φ.op (ymGaussPoly G d) * Φ.op (ymHamPoly G) := by
  rw [← coreRep_op_mul, ← coreRep_op_mul]
  exact congrArg Φ.op (ymHamPoly_comm G d)

/-- The pointwise form: `H` preserves the core of `𝒢_d` and the two commute there — the
core-level content of the `DomPreserve` / `StrongCommute` pair of
`ChapterBrstReducedTransferUnbounded`. -/
theorem coreRep_ham_comm_gauss_apply (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (x : D) :
    Φ.op (ymHamPoly G) (Φ.op (ymGaussPoly G d) x)
      = Φ.op (ymGaussPoly G d) (Φ.op (ymHamPoly G) x) := by
  simp only [← Module.End.mul_apply, coreRep_ham_comm_gauss]

end Core99

end

end BookProof.Qym.GaussSkew
