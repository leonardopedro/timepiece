import Mathlib
import BookProof.ChapterHermiteProductBasis
import BookProof.ChapterFullQuadraticEsa
import BookProof.ChapterHermiteBandCalculus.Part1

/-!
# The graded band calculus of the product Hermite basis: a real quadratic Hamiltonian has a
# band matrix whose entries grow like the degree

`BookProof.ChapterHermiteProductBasis` makes the product Hermite functions
`ψ_α = He_α · e^{-‖x‖²/4} / ‖·‖` an orthonormal basis of `L²(ℝᵈ)` and records the ladder
relations `a†ᵢψ_α = √(αᵢ+1) ψ_{α+eᵢ}`, `aᵢψ_α = √αᵢ ψ_{α−eᵢ}`.  This chapter turns those
relations into a **calculus of band operators**, whose purpose is the input of the weighted
Schur gate of `BookProof.ChapterFockWeightedSchurEsa`: a one-particle matrix that is
band-limited in the degree, has boundedly many entries per column, and whose entries grow
at most like `deg + 1`.

## What is proved

* `hpsi`, `pgLp_hpsi`, `hcomb` — the normalized Hermite *polynomial* `ψ_α`, its `L²` vector,
  and the finite combination `Σ_β f_β ψ_β` of Hermite states.
* `crePoly_hpsi`, `annPoly_hpsi` — the ladder relations at the level of polynomials.
* `Band T r M C g` — the band predicate: `T ψ_α` is a combination of at most `M` Hermite
  states whose degrees differ from `deg α` by at most `r`, with coefficients bounded by
  `C · g (deg α)`.  The two growths used are `g1 n = √(n+1)` (first order) and
  `g2 n = n + 1` (second order).
* `Band.add`, `Band.smul`, `Band.mono`, `Band.toBand2` — the closure properties.
* `band_crePoly`, `band_annPoly` — the ladder operators are first-order band operators with
  `M = C = 1`.
* **`Band.comp`** — the composition of two first-order band operators is a second-order one:
  `M₁M₂` entries, band `2`, and the growth `2 M₁ C₁ C₂ (deg α + 1)`; the analytic content is
  `√(deg α + 1) · √(deg γ + 1) ≤ 2 (deg α + 1)` for `|deg γ − deg α| ≤ 1`.
* `IsBand1` / `IsBand2` — the existential forms, closed under sums, scalar multiples, finite
  sums and (for `IsBand1`) composition.
* `mulXPoly_eq`, `momPoly_eq` — the coordinate and momentum operators are the ladder
  combinations `xᵢ = aᵢ† + aᵢ` and `πᵢ = (i/2)(aᵢ† − aᵢ)`, hence first-order.
* **`isBand2_fqPoly`** — the headline: the general real quadratic Hamiltonian
  `fqPoly P Q S b b'` of `BookProof.ChapterFullQuadraticEsa` — an arbitrary Weyl-ordered
  quadratic form in the coordinates and momenta, plus a first-order term — is a second-order
  band operator.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.HermiteBand

noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}
/-! ## Composition: a product of two first-order operators is second-order -/

theorem Band.comp {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {M₁ M₂ : ℕ}
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hU : Band U 1 M₂ C₂ g1) (hT : Band T 1 M₁ C₁ g1) :
    Band (U ∘ₗ T) 2 (M₁ * M₂) (2 * M₁ * C₁ * C₂) g2 := by
  classical
  intro α
  obtain ⟨f, hrep, hcard, hband, hcoef⟩ := hT α
  choose G hGrep hGcard hGband hGcoef using hU
  refine ⟨f.sum fun γ c => c • G γ, ?_, ?_, ?_, ?_⟩
  · have h1 : (U ∘ₗ T) (hpsi α) = U (hcomb f) := by rw [LinearMap.comp_apply, hrep]
    rw [h1, hcomb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, hcomb,
      show (f.sum fun γ c => c • G γ) = ∑ γ ∈ f.support, f γ • G γ from rfl, map_sum]
    exact Finset.sum_congr rfl fun γ _ => by rw [map_smul, hGrep γ, map_smul]
  · have hsub : (f.sum fun γ c => c • G γ).support ⊆ f.support.biUnion fun γ => (G γ).support := by
      refine (Finsupp.support_sum).trans ?_
      intro β hβ
      simp only [Finset.mem_biUnion] at hβ ⊢
      obtain ⟨γ, hγ, hβγ⟩ := hβ
      exact ⟨γ, hγ, Finsupp.support_smul hβγ⟩
    calc (f.sum fun γ c => c • G γ).support.card
        ≤ (f.support.biUnion fun γ => (G γ).support).card := Finset.card_le_card hsub
      _ ≤ ∑ γ ∈ f.support, (G γ).support.card := Finset.card_biUnion_le
      _ ≤ ∑ _γ ∈ f.support, M₂ := Finset.sum_le_sum fun γ _ => hGcard γ
      _ = f.support.card * M₂ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ M₁ * M₂ := Nat.mul_le_mul_right _ hcard
  · intro β hβ
    have hmem : β ∈ f.support.biUnion fun γ => (G γ).support := by
      refine (Finsupp.support_sum).trans (by
        intro β' hβ'
        simp only [Finset.mem_biUnion] at hβ' ⊢
        obtain ⟨γ, hγ, hβγ⟩ := hβ'
        exact ⟨γ, hγ, Finsupp.support_smul hβγ⟩) hβ
    simp only [Finset.mem_biUnion] at hmem
    obtain ⟨γ, hγ, hβγ⟩ := hmem
    have h1 := hGband γ β hβγ
    have h2 := hband γ hγ
    omega
  · intro β
    have happ : (f.sum fun γ c => c • G γ) β = ∑ γ ∈ f.support, f γ * (G γ) β := by
      simp only [Finsupp.sum, Finset.sum_apply', Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [happ]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ γ ∈ f.support, ‖f γ * (G γ) β‖ ≤ 2 * C₁ * C₂ * g2 α.degree := by
      intro γ hγ
      have hγdeg : ((γ.degree : ℤ) - (α.degree : ℤ)).natAbs ≤ 1 := hband γ hγ
      have hle : (γ.degree : ℝ) ≤ (α.degree : ℝ) + 1 := by
        have : (γ.degree : ℤ) ≤ (α.degree : ℤ) + 1 := by omega
        exact_mod_cast this
      have h1 : ‖f γ‖ ≤ C₁ * g1 α.degree := hcoef γ
      have h2 : ‖(G γ) β‖ ≤ C₂ * g1 γ.degree := hGcoef γ β
      have hg1a : g1 α.degree = Real.sqrt ((α.degree : ℝ) + 1) := rfl
      have hg1g : g1 γ.degree = Real.sqrt ((γ.degree : ℝ) + 1) := rfl
      have hsa : Real.sqrt ((α.degree : ℝ) + 1) ^ 2 = (α.degree : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      have hsg : Real.sqrt ((γ.degree : ℝ) + 1) ^ 2 = (γ.degree : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      have hprod : g1 α.degree * g1 γ.degree ≤ 2 * g2 α.degree := by
        rw [hg1a, hg1g, g2]
        nlinarith [Real.sqrt_nonneg ((α.degree : ℝ) + 1), Real.sqrt_nonneg ((γ.degree : ℝ) + 1),
          sq_nonneg (Real.sqrt ((α.degree : ℝ) + 1) - Real.sqrt ((γ.degree : ℝ) + 1)),
          Nat.cast_nonneg (α := ℝ) α.degree]
      calc ‖f γ * (G γ) β‖ = ‖f γ‖ * ‖(G γ) β‖ := norm_mul _ _
        _ ≤ (C₁ * g1 α.degree) * (C₂ * g1 γ.degree) := by
            exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC₁ (g1_nonneg _))
        _ = C₁ * C₂ * (g1 α.degree * g1 γ.degree) := by ring
        _ ≤ C₁ * C₂ * (2 * g2 α.degree) := by
            refine mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = 2 * C₁ * C₂ * g2 α.degree := by ring
    calc ∑ γ ∈ f.support, ‖f γ * (G γ) β‖
        ≤ ∑ _γ ∈ f.support, 2 * C₁ * C₂ * g2 α.degree := Finset.sum_le_sum hterm
      _ = f.support.card * (2 * C₁ * C₂ * g2 α.degree) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M₁ * (2 * C₁ * C₂ * g2 α.degree) := by
          have hg2 : (0:ℝ) ≤ g2 α.degree := by
            simp only [g2]
            positivity
          have hnn : (0:ℝ) ≤ 2 * C₁ * C₂ * g2 α.degree :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) hC₂) hg2
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn
      _ = 2 * M₁ * C₁ * C₂ * g2 α.degree := by ring

open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

/-- A first-order band operator. -/
def IsBand1 (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) : Prop :=
  ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ Band T 1 M C g1

/-- A second-order band operator. -/
def IsBand2 (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) : Prop :=
  ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ Band T 2 M C g2

theorem g2_nonneg (n : ℕ) : 0 ≤ g2 n := by
  simp only [g2]
  positivity

theorem IsBand1.toBand2 {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (h : IsBand1 T) : IsBand2 T := by
  obtain ⟨M, C, hC, hB⟩ := h
  exact ⟨M, C, hC, Band.toBand2 hC hB⟩

theorem IsBand1.add {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : IsBand1 T) (hS : IsBand1 S) : IsBand1 (T + S) := by
  obtain ⟨M₁, C₁, hC₁, h₁⟩ := hT
  obtain ⟨M₂, C₂, hC₂, h₂⟩ := hS
  exact ⟨M₁ + M₂, C₁ + C₂, by linarith, Band.add h₁ h₂⟩

theorem IsBand2.add {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : IsBand2 T) (hS : IsBand2 S) : IsBand2 (T + S) := by
  obtain ⟨M₁, C₁, hC₁, h₁⟩ := hT
  obtain ⟨M₂, C₂, hC₂, h₂⟩ := hS
  exact ⟨M₁ + M₂, C₁ + C₂, by linarith, Band.add h₁ h₂⟩

theorem IsBand1.smul {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (c : ℂ)
    (hT : IsBand1 T) : IsBand1 (c • T) := by
  obtain ⟨M, C, hC, h⟩ := hT
  exact ⟨M, ‖c‖ * C, mul_nonneg (norm_nonneg c) hC, Band.smul c h⟩

theorem IsBand2.smul {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (c : ℂ)
    (hT : IsBand2 T) : IsBand2 (c • T) := by
  obtain ⟨M, C, hC, h⟩ := hT
  exact ⟨M, ‖c‖ * C, mul_nonneg (norm_nonneg c) hC, Band.smul c h⟩

theorem isBand2_zero : IsBand2 (0 : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) := by
  refine ⟨0, 0, le_refl 0, fun α => ⟨0, ?_, ?_, ?_, ?_⟩⟩
  · simp [hcomb]
  · simp
  · simp
  · simp

theorem isBand1_zero : IsBand1 (0 : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) := by
  refine ⟨0, 0, le_refl 0, fun α => ⟨0, ?_, ?_, ?_, ?_⟩⟩
  · simp [hcomb]
  · simp
  · simp
  · simp

theorem IsBand1.sum {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, IsBand1 (F i)) : IsBand1 (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isBand1_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact IsBand1.add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsBand2.sum {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, IsBand2 (F i)) : IsBand2 (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isBand2_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact IsBand2.add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The composition of two first-order band operators is second-order. -/
theorem IsBand1.comp {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hU : IsBand1 U) (hT : IsBand1 T) : IsBand2 (U ∘ₗ T) := by
  obtain ⟨M₁, C₁, hC₁, h₁⟩ := hT
  obtain ⟨M₂, C₂, hC₂, h₂⟩ := hU
  refine ⟨M₁ * M₂, 2 * M₁ * C₁ * C₂, ?_, Band.comp hC₁ hC₂ h₂ h₁⟩
  have : (0:ℝ) ≤ 2 * M₁ := by positivity
  exact mul_nonneg (mul_nonneg this hC₁) hC₂

/-! ## The basic operators -/

theorem isBand1_crePoly (i : Fin d) : IsBand1 (crePoly i) :=
  ⟨1, 1, zero_le_one, band_crePoly i⟩

theorem isBand1_annPoly (i : Fin d) : IsBand1 (annPoly i) :=
  ⟨1, 1, zero_le_one, band_annPoly i⟩

theorem mulXPoly_eq (i : Fin d) :
    (mulXPoly i : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
      = crePoly i + annPoly i := by
  refine LinearMap.ext fun p => ?_
  simp [mulXPoly, crePoly, annPoly]

theorem momPoly_eq (i : Fin d) :
    (momPoly i : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
      = (Complex.I / 2) • crePoly i + (-(Complex.I / 2)) • annPoly i := by
  refine LinearMap.ext fun p => ?_
  have h1 : (C (-Complex.I) : MvPolynomial (Fin d) ℂ) * (pderiv i p - C (1/2 : ℂ) * (X i * p))
      = (-Complex.I) • (pderiv i p - (1/2 : ℂ) • (X i * p)) := by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, momPoly_apply, crePoly_apply,
    annPoly_apply, h1]
  module

theorem isBand1_mulXPoly (i : Fin d) : IsBand1 (mulXPoly i) := by
  rw [mulXPoly_eq]
  exact (isBand1_crePoly i).add (isBand1_annPoly i)

theorem isBand1_momPoly (i : Fin d) : IsBand1 (momPoly i) := by
  rw [momPoly_eq]
  exact ((isBand1_crePoly i).smul _).add ((isBand1_annPoly i).smul _)

/-! ## The quadratic Hamiltonian -/

theorem isBand2_weylProd {S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hS : IsBand1 S) (hT : IsBand1 T) :
    IsBand2 (BookProof.YangMillsHermite.weylProd S T) := by
  rw [BookProof.YangMillsHermite.weylProd]
  exact IsBand2.smul _ ((hS.comp hT).add (hT.comp hS))

theorem isBand2_fqQuadPoly (P Q S : Fin d → Fin d → ℝ) : IsBand2 (fqQuadPoly P Q S) := by
  rw [fqQuadPoly]
  refine IsBand2.sum _ _ fun i _ => IsBand2.sum _ _ fun j _ => ?_
  refine IsBand2.add (IsBand2.add ?_ ?_) ?_
  · exact IsBand2.smul _ (isBand2_weylProd (isBand1_momPoly i) (isBand1_momPoly j))
  · exact IsBand2.smul _ (isBand2_weylProd (isBand1_mulXPoly i) (isBand1_mulXPoly j))
  · exact IsBand2.smul _ (isBand2_weylProd (isBand1_mulXPoly i) (isBand1_momPoly j))

theorem isBand1_foPoly (b b' : Fin d → ℝ) : IsBand1 (BookProof.HermiteRelative.foPoly b b') := by
  rw [BookProof.HermiteRelative.foPoly]
  exact IsBand1.sum _ _ fun i _ =>
    ((isBand1_mulXPoly i).smul _).add ((isBand1_momPoly i).smul _)

/-- **The Hermite matrix of a general real quadratic Hamiltonian is graded-band.** -/
theorem isBand2_fqPoly (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    IsBand2 (fqPoly P Q S b b') := by
  rw [fqPoly]
  exact (isBand2_fqQuadPoly P Q S).add (isBand1_foPoly b b').toBand2

end

end BookProof.HermiteBand
