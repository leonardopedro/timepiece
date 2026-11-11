import BookProof.MCMC.FockLangevinOperator
import BayesianTransformer.Transformer.GlobalLipschitz

/-!
# Chapter CoeffMap — the coefficient map from the `ε`-normalized potential

Plan: `pcnl.md` §2.2 and `FockLangevinOperator` §16.  §16 turned the architecture's weight-space
bound `M_ε = 2K/ε` into the coefficient predicate `GradCoeffBound Φ (2K/ε)` and showed that the
rest of the chain (`gradSectorBound_le_of_gradCoeffBound`, `driftScale_gradSectorBound_le_eps`)
follows from it — but left the *reading* as an assumption: which coefficient family does `Φ_ε` have,
and why is its derivative's `ℓ¹` mass at most `2K/ε`?

This chapter supplies the map and closes the gap at the order the architecture bounds.

* `linCoeff F x j` — the `j`-th linear Taylor coefficient of a potential `F` at the base point `x`,
  i.e. `D F(x)[eⱼ]` for the standard basis of the weight space `EuclideanSpace ℝ (Fin d)`.  This is
  the coefficient map: it reads the first-order coefficients of the Fock expansion off the
  weight-space function.
* `linPart F x` — the linear polynomial with those coefficients (`∑ⱼ linCoeff · Xⱼ`), the potential
  the architecture's Theorem 1 controls.  `pderiv_linPart` and `coeffMass_pderiv_linPart` identify
  the model's `∂ⱼ` coefficients with `linCoeff` exactly.
* **`norm_linCoeff_le`** (`‖linCoeff‖ ≤ ‖D F(x)‖`, since `‖eⱼ‖ = 1`) and
  **`gradCoeffBound_linPart`**: any weight-space gradient bound `M` for `F` is a coefficient bound
  `GradCoeffBound (linPart F x) M` for the model's potential.  Composing with
  `BayesianTransformer.epsProj_fderiv_le` gives **`gradCoeffBound_epsProj`**: for the additive
  normalization `Ŵ = W/(‖W‖ + ε)` and `‖W‖ ≥ ε`, the coefficient bound holds with `M_ε = 2K/ε` —
  no hypothesis left.  `driftScale_linPart_le_eps_proj` then reads the architecture's constant
  into §12's drift: `B ≤ β²σ²K/ε` times the explicit level factor.
* **The units match** (`eval_pderiv_norm_le_coeffMass`): on the unit cube the model's derivative is
  at most the coefficient mass, so `GradCoeffBound Φ M` really is a sup-norm gradient bound — the
  coefficient hypothesis and `epsProj_fderiv_le`'s conclusion are statements of the same kind.

## Honest boundary

`epsProj_fderiv_le` bounds the **first** derivative of the normalized potential.  The coefficient
map above is therefore the linear one: `linPart` is the first-order Taylor polynomial, and its
coefficient bound is exactly `‖DΦ_ε‖`.  Reading higher coefficients off the same hypothesis is not
possible — a bound on `∇Φ_ε` says nothing about `D²Φ_ε` — so a general (nonlinear) `Φ_ε` would need
the corresponding higher derivative bounds, which the architecture's Theorem 1 does not supply.
This is why §16's `GradCoeffBound` is a predicate: it is the coefficient form of exactly the data
the architecture has, and here it is *derived* rather than assumed at the order where that reading
is faithful.
-/

noncomputable section

namespace BookProof.MCMC.FockLangevin

open Finset
open BookProof.ReferenceGap
open BookProof.MCMC.UnadjustedPCN

variable {d : ℕ}

/-! ## 17.1 The coefficient map -/

/-- The `j`-th linear Taylor coefficient of a potential at `x`: the coefficient map that reads the
model's `∂ⱼΦ` off a weight-space function.  The weight space is `EuclideanSpace ℝ (Fin d)`, whose
basis `eⱼ` has unit norm — the Frobenius norm of the architecture's parameter space. -/
def linCoeff (F : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) : ℂ :=
  fderiv ℝ F x (EuclideanSpace.single j 1)

/-- The linear part of a potential at `x`, as a polynomial in the model's coefficients. -/
def linPart (F : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    MvPolynomial (Fin d) ℂ :=
  ∑ j, MvPolynomial.monomial (Finsupp.single j 1) (linCoeff F x j)

theorem coeffMass_C (a : ℂ) : coeffMass (d := d) (MvPolynomial.C a) = ‖a‖ := by
  classical
  rw [coeffMass]
  by_cases ha : a = 0
  · simp [ha]
  · rw [MvPolynomial.support_C, if_neg ha, Finset.sum_singleton, MvPolynomial.coeff_C]
    simp

/-- The derivative of a single-variable monomial at exponent `1` is its coefficient. -/
theorem pderiv_monomial_single_one (j : Fin d) (a : ℂ) :
    MvPolynomial.pderiv j (MvPolynomial.monomial (Finsupp.single j 1) a) = MvPolynomial.C a := by
  rw [MvPolynomial.pderiv_monomial_single, Nat.sub_self, Finsupp.single_zero]
  simp

/-- **The coefficient map, differentiated.**  In the model `pderiv j` is exactly the coefficient
functional: the derivative of the linear part is the constant `linCoeff F x j`. -/
theorem pderiv_linPart (F : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d))
    (j : Fin d) :
    MvPolynomial.pderiv j (linPart F x) = MvPolynomial.C (linCoeff F x j) := by
  classical
  rw [linPart, map_sum]
  refine (Finset.sum_eq_single j ?_ ?_).trans (pderiv_monomial_single_one j _)
  · intro j' _ hne
    rw [MvPolynomial.pderiv_monomial]
    have hval : (Finsupp.single j' 1 : Fin d →₀ ℕ) j = 0 := by simp [hne]
    simp [hval]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem coeffMass_pderiv_linPart (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    coeffMass (MvPolynomial.pderiv j (linPart F x)) = ‖linCoeff F x j‖ := by
  rw [pderiv_linPart, coeffMass_C]

/-- The linear coefficient is at most the operator norm of the differential: `‖D F(x)[eⱼ]‖` with
`‖eⱼ‖ = 1`. -/
theorem norm_linCoeff_le (F : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d))
    (j : Fin d) : ‖linCoeff F x j‖ ≤ ‖fderiv ℝ F x‖ := by
  have h := ContinuousLinearMap.le_opNorm (fderiv ℝ F x) (EuclideanSpace.single j (1 : ℝ))
  rw [EuclideanSpace.norm_single, norm_one, mul_one] at h
  simpa [linCoeff] using h

/-- **The reading, at the linear order.**  A weight-space gradient bound `M` for the potential is a
coefficient bound for its linear part — no further hypothesis. -/
theorem gradCoeffBound_linPart (F : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d))
    {M : ℝ} (hM : ‖fderiv ℝ F x‖ ≤ M) : GradCoeffBound (linPart F x) M :=
  fun j => (coeffMass_pderiv_linPart F x j).trans_le ((norm_linCoeff_le F x j).trans hM)

theorem linPart_totalDegree_le (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) : (linPart F x).totalDegree ≤ 1 := by
  classical
  have hmono : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      (MvPolynomial.monomial (Finsupp.single j 1) (linCoeff F x j)).totalDegree ≤ 1 := by
    intro j _
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    rw [Finsupp.sum_single_index]
    · simp
    · simp
  rw [linPart]
  exact totalDegree_finset_sum_le _ _ hmono

/-- The explicit level factor of §14–§16, named once so the statements below stay legible. -/
def levelFactor (Φ : MvPolynomial (Fin d) ℂ) (N : ℕ) : ℝ :=
  (d : ℝ) * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree

theorem driftScale_le_eps_levelFactor {Φ : MvPolynomial (Fin d) ℂ} {K ε : ℝ} (hK : 0 ≤ K)
    (hε : 0 < ε) (h : GradCoeffBound Φ (2 * K / ε)) (β σ : ℝ) (N : ℕ) :
    driftScale β σ (gradSectorBound Φ N) ≤ β ^ 2 * σ ^ 2 * K / ε * levelFactor Φ N :=
  driftScale_gradSectorBound_le_eps β σ hK hε h N

/-! ## 17.2 The architecture's `M_ε = 2K/ε` as a coefficient bound -/

/-- **The reading, closed.**  For the additive normalization `Ŵ = W/(‖W‖ + ε)` and any `‖W‖ ≥ ε`,
the linear part of `g ∘ Ŵ` satisfies `GradCoeffBound (linPart (g ∘ Ŵ) W) (2K/ε)` — §16's hypothesis,
derived from `BayesianTransformer.epsProj_fderiv_le` rather than assumed. -/
theorem gradCoeffBound_epsProj {g : EuclideanSpace ℝ (Fin d) → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hg_diff : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 → DifferentiableAt ℝ g u)
    (hg_bound : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 → ‖fderiv ℝ g u‖ ≤ K)
    {ε : ℝ} (hε : 0 < ε) {w : EuclideanSpace ℝ (Fin d)} (hw : ε ≤ ‖w‖) :
    GradCoeffBound (linPart (fun v => g (BayesianTransformer.epsProj ε v)) w) (2 * K / ε) :=
  gradCoeffBound_linPart _ w
    (BayesianTransformer.epsProj_fderiv_le hK hg_diff hg_bound hε hw)

/-- **The drift constant from the architecture, with no hypothesis.**  Composing the reading with
§16 gives `B = (β²σ²/2)·M` at `M = 2K/ε`, i.e. `β²σ²K/ε` times the explicit level factor. -/
theorem driftScale_linPart_le_eps_proj {g : EuclideanSpace ℝ (Fin d) → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hg_diff : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 → DifferentiableAt ℝ g u)
    (hg_bound : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 → ‖fderiv ℝ g u‖ ≤ K)
    {ε : ℝ} (hε : 0 < ε) {w : EuclideanSpace ℝ (Fin d)} (hw : ε ≤ ‖w‖) (β σ : ℝ) (N : ℕ) :
    driftScale β σ (gradSectorBound (linPart (fun v => g (BayesianTransformer.epsProj ε v)) w) N)
      ≤ β ^ 2 * σ ^ 2 * K / ε
        * levelFactor (linPart (fun v => g (BayesianTransformer.epsProj ε v)) w) N :=
  driftScale_le_eps_levelFactor hK hε (gradCoeffBound_epsProj hK hg_diff hg_bound hε hw) β σ N

/-! ## 17.3 The units: the coefficient mass bounds the derivative on the cube -/

theorem norm_finsupp_prod_le_one {z : Fin d → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1) (m : Fin d →₀ ℕ) :
    ‖m.prod fun i e => z i ^ e‖ ≤ 1 := by
  classical
  rw [Finsupp.prod, norm_prod]
  refine Finset.prod_le_one (fun i _ => by positivity) fun i _ => ?_
  simpa [norm_pow] using pow_le_one₀ (norm_nonneg (z i)) (hz i) (n := m i)

/-- **`GradCoeffBound` is a sup-norm gradient bound.**  On the unit cube of the model's coordinates,
`‖∂ⱼΦ(z)‖` is at most the coefficient mass of `∂ⱼΦ`: the coefficient hypothesis of §16 and the
conclusion of `epsProj_fderiv_le` are statements in the same units. -/
theorem eval_pderiv_norm_le_coeffMass (Φ : MvPolynomial (Fin d) ℂ) (j : Fin d)
    {z : Fin d → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖MvPolynomial.eval z (MvPolynomial.pderiv j Φ)‖ ≤ coeffMass (MvPolynomial.pderiv j Φ) := by
  classical
  have hexp : MvPolynomial.eval z (MvPolynomial.pderiv j Φ)
      = ∑ m ∈ (MvPolynomial.pderiv j Φ).support,
          MvPolynomial.coeff m (MvPolynomial.pderiv j Φ) * m.prod fun i e => z i ^ e := by
    conv_lhs => rw [MvPolynomial.as_sum (MvPolynomial.pderiv j Φ)]
    simp only [map_sum, MvPolynomial.eval_monomial]
  rw [hexp]
  calc ‖∑ m ∈ (MvPolynomial.pderiv j Φ).support,
        MvPolynomial.coeff m (MvPolynomial.pderiv j Φ) * m.prod fun i e => z i ^ e‖
      ≤ ∑ m ∈ (MvPolynomial.pderiv j Φ).support,
          ‖MvPolynomial.coeff m (MvPolynomial.pderiv j Φ)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul]
        calc ‖MvPolynomial.coeff m (MvPolynomial.pderiv j Φ)‖ * ‖m.prod fun i e => z i ^ e‖
            ≤ ‖MvPolynomial.coeff m (MvPolynomial.pderiv j Φ)‖ * 1 :=
              mul_le_mul_of_nonneg_left (norm_finsupp_prod_le_one hz m) (norm_nonneg _)
          _ = ‖MvPolynomial.coeff m (MvPolynomial.pderiv j Φ)‖ := mul_one _
    _ = coeffMass (MvPolynomial.pderiv j Φ) := rfl

/-- Consequently a coefficient bound is a uniform derivative bound on the cube. -/
theorem eval_pderiv_norm_le_of_gradCoeffBound {Φ : MvPolynomial (Fin d) ℂ} {M : ℝ}
    (h : GradCoeffBound Φ M) (j : Fin d) {z : Fin d → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖MvPolynomial.eval z (MvPolynomial.pderiv j Φ)‖ ≤ M :=
  (eval_pderiv_norm_le_coeffMass Φ j hz).trans (h j)

end BookProof.MCMC.FockLangevin
