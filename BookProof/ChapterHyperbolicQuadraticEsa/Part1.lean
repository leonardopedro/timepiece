import Mathlib
import BookProof.ChapterNavierStokesDifferentialL2
import BookProof.ChapterWaveBoundedPotential

/-!
# The hyperbolic operator with an indefinite quadratic potential

`BookProof.ChapterStrichartzWave` proves essential self-adjointness of every
constant-coefficient operator with a real symbol — in particular of the wave operator
`□ = −∂_t² + Δ_x` — on the Schwartz core of `L²(ℝ^{1+n})`, and
`BookProof.ChapterWaveUnboundedPotential` does the same for multiplication by a real
potential of temperate growth.  Both of those are *commuting* halves: the first is a pure
Fourier multiplier, the second a pure multiplication operator.
`BookProof.ChapterHarmonicOscillatorEsa` settles the prototypical **non-commuting** mixture
in the *elliptic* normalization, `−d²/dx² + x²/4` on `L²(ℝ)`.

What was recorded as open (`STRICHARTZ_WAVE_ESA.md`, `CONSOLIDATED_PLAN.md` §9.5 and the
Lean-specialist backlog item A1) is the non-commuting mixture in the **hyperbolic**
normalization: `□ + V` with `V` in the Faris–Lavine class (bounded above by a quadratic —
the sign that the sign warning of `STRICHARTZ_WAVE_ESA.md` singles out; with the opposite
sign the operator genuinely fails to be essentially self-adjoint).  This module proves that
mixture for the quadratic potentials that are diagonal in the coordinates, by exhibiting
the joint eigenbasis: the product Hermite functions of
`BookProof.ChapterHermiteProductBasis`.

## What is proved

For an arbitrary real weight vector `c : Fin d → ℝ` — *no sign condition* — let

`H_c = ∑ᵢ cᵢ (−∂²/∂xᵢ² + xᵢ²/4)`

on the Gauss–polynomial (product Hermite) core `polyGaussCore` of `L²(ℝᵈ)`.

* `oscPoly`, `oscPoly_apply`, `oscPoly_hermiteMv` — the one-coordinate oscillator
  `−∂ᵢ² + xᵢ²/4`, written with the *canonical pair* `momPoly i = −i∂ᵢ`,
  `mulXPoly i = xᵢ·` of `BookProof.ChapterNavierStokesDifferentialL2`, is the number
  operator `aᵢ†aᵢ + ½` on the product Hermite functions;
* `quadOp`, `quadSymbol`, `quadOp_hermiteMvLp` — `H_c` on the core, and its diagonal
  action `H_c ψ_α = (∑ᵢ cᵢ(αᵢ + ½)) ψ_α`;
* `quadPoly_apply_eq_differential` — the **identification**: pointwise, `H_c` really is
  `∑ᵢ cᵢ(−∂ᵢ²f + (xᵢ²/4)f)` with Mathlib's `deriv` taken twice along the `i`-th coordinate
  line;
* `quadOp_symmetric` and `quadOp_essentiallySelfAdjoint` — **the headline**: `H_c` is
  symmetric and essentially self-adjoint on the Hermite core, for every real `c`;
* `quadOp_not_bounded`, `polyGaussCore_dense_L2'` — the operator is genuinely unbounded as
  soon as some `cᵢ ≠ 0`, and the core is dense, so the statement is not an artefact;
* `minkowskiCoeff`, `wave_indefiniteQuadratic_essentiallySelfAdjoint` and
  `minkowski_apply_eq_differential` — the case `c = (1, −1, …, −1)`: in the convention
  `□ = −∂_t² + Δ_x` of `BookProof.ChapterStrichartzWave` this is

  `□ + V`,  `V(t, x) = (t² − ‖x‖²)/4`,

  an unbounded potential which is bounded above by the quadratic `(t² + ‖x‖²)/4` — the
  Faris–Lavine sign — and which does not commute with `□`.

* `quadOp_add_boundedPotential_essentiallySelfAdjoint` and
  `quadOp_add_realBoundedPotential_essentiallySelfAdjoint` — the potential class is
  widened by the already-proved Kato–Rellich theorem: `H_c + W` is still essentially
  self-adjoint on the same core for every real, essentially bounded `W`, so the
  potential may be any *diagonal quadratic plus bounded* real function.

Two general instruments are proved on the way and are reusable:
`symmetricOn_of_diagonal` and `deficiencyTrivialAt_of_diagonal` — an operator that is
diagonal with a *real* symbol on an orthonormal family spanning its domain is symmetric,
and its deficiency spaces at non-real points vanish as soon as the family is total.

## Honest boundary

The potential is quadratic and diagonal in the coordinates (`∑ᵢ cᵢxᵢ²/4`); a general
Faris–Lavine potential bounded above by a quadratic is *not* covered — the joint
eigenbasis is what makes the argument work, and it exists only for the diagonal quadratic
family.  Nothing here claims anything for the opposite sign (the `−d²/dx² − x⁴` class,
whose deficiency indices are non-zero).
-/

namespace BookProof.HyperbolicQuadratic

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

/-! ## An instrument: operators that are diagonal on an orthonormal family -/

section Diagonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

/-- An operator which is **diagonal with a real symbol** on an orthonormal family spanning
its domain is symmetric on that domain. -/
theorem symmetricOn_of_diagonal (v : ι → E) (hv : Orthonormal ℂ v) (lam : ι → ℝ)
    {D : Submodule ℂ E} (hD : Submodule.span ℂ (Set.range v) = D)
    (T : D →ₗ[ℂ] E)
    (hT : ∀ (i : ι) (h : v i ∈ D), T ⟨v i, h⟩ = ((lam i : ℝ) : ℂ) • v i) :
    SymmetricOn D T := by
  classical
  have hvD : ∀ i, v i ∈ D := fun i => hD ▸ Submodule.subset_span ⟨i, rfl⟩
  have main : ∀ y : E, y ∈ Submodule.span ℂ (Set.range v) →
      ∀ (hy : y ∈ D) (i : ι), (inner ℂ (T ⟨v i, hvD i⟩) y : ℂ) = inner ℂ (v i) (T ⟨y, hy⟩) := by
    intro y hy0
    induction hy0 using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        intro hy i
        rw [hT i (hvD i), hT j hy, inner_smul_left, inner_smul_right,
          orthonormal_iff_ite.mp hv i j]
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
    | zero =>
        intro hy i
        have h0 : (⟨(0 : E), hy⟩ : D) = 0 := Subtype.ext rfl
        simp [h0]
    | add z w hz hw ihz ihw =>
        intro hy i
        have hzD : z ∈ D := hD ▸ hz
        have hwD : w ∈ D := hD ▸ hw
        have hadd : (⟨z + w, hy⟩ : D) = ⟨z, hzD⟩ + ⟨w, hwD⟩ := Subtype.ext rfl
        rw [hadd, map_add, inner_add_right, inner_add_right, ihz hzD i, ihw hwD i]
    | smul r z hz ih =>
        intro hy i
        have hzD : z ∈ D := hD ▸ hz
        have hsm : (⟨r • z, hy⟩ : D) = r • ⟨z, hzD⟩ := Subtype.ext rfl
        rw [hsm, map_smul, inner_smul_right, inner_smul_right, ih hzD i]
  have main2 : ∀ x : E, x ∈ Submodule.span ℂ (Set.range v) →
      ∀ (hx : x ∈ D) (y : E) (hy : y ∈ D),
        (inner ℂ (T ⟨x, hx⟩) y : ℂ) = inner ℂ x (T ⟨y, hy⟩) := by
    intro x hx0
    induction hx0 using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        intro _ y hy
        exact main y (hD ▸ hy) hy j
    | zero =>
        intro hx y hy
        have h0 : (⟨(0 : E), hx⟩ : D) = 0 := Subtype.ext rfl
        simp [h0]
    | add z w hz hw ihz ihw =>
        intro hx y hy
        have hzD : z ∈ D := hD ▸ hz
        have hwD : w ∈ D := hD ▸ hw
        have hadd : (⟨z + w, hx⟩ : D) = ⟨z, hzD⟩ + ⟨w, hwD⟩ := Subtype.ext rfl
        rw [hadd, map_add, inner_add_left, inner_add_left, ihz hzD y hy, ihw hwD y hy]
    | smul r z hz ih =>
        intro hx y hy
        have hzD : z ∈ D := hD ▸ hz
        have hsm : (⟨r • z, hx⟩ : D) = r • ⟨z, hzD⟩ := Subtype.ext rfl
        rw [hsm, map_smul, inner_smul_left, inner_smul_left, ih hzD y hy]
  intro x y
  have hx : (x : E) ∈ Submodule.span ℂ (Set.range v) := hD ▸ x.2
  simpa using main2 (x : E) hx x.2 (y : E) y.2

/-- The **deficiency spaces of a diagonal operator with a real symbol vanish** at every
non-real point, as soon as the diagonalizing family is total. -/
theorem deficiencyTrivialAt_of_diagonal (v : ι → E) (lam : ι → ℝ)
    (htot : ∀ w : E, (∀ i, (inner ℂ (v i) w : ℂ) = 0) → w = 0)
    {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) (hmem : ∀ i, v i ∈ D)
    (hT : ∀ (i : ι) (h : v i ∈ D), T ⟨v i, h⟩ = ((lam i : ℝ) : ℂ) • v i)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt D T z := by
  intro w hw
  refine htot w fun i => ?_
  have h := hw ⟨v i, hmem i⟩
  rw [hT i (hmem i), inner_smul_left, Complex.conj_ofReal] at h
  have hne : ((lam i : ℝ) : ℂ) - z ≠ 0 := by
    intro hc
    have hzi : z = ((lam i : ℝ) : ℂ) := by linear_combination -hc
    rw [hzi] at hz
    simp at hz
  have hprod : (((lam i : ℝ) : ℂ) - z) * (inner ℂ (v i) w : ℂ) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hprod).resolve_left hne

end Diagonal

variable {d : ℕ}

/-! ## The one-coordinate oscillator in the canonical pair -/

/-- The one-coordinate harmonic oscillator `−∂ᵢ² + xᵢ²/4`, written with the canonical pair
`πᵢ = −i∂ᵢ` and `xᵢ·` of `BookProof.ChapterNavierStokesDifferentialL2`: `πᵢ² + xᵢ²/4`. -/
def oscPoly (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  (momPoly i).comp (momPoly i) + (1/4 : ℂ) • ((mulXPoly i).comp (mulXPoly i))

/-- The momentum in `•`-form. -/
theorem momPoly_apply' (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = (-Complex.I) • (pderiv i p - (1/2 : ℂ) • (X i * p)) := by
  rw [momPoly_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]

/-- The square of the momentum in polynomial coordinates. -/
theorem momPoly_sq (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i (momPoly i p)
      = -(pderiv i (pderiv i p)) + (1/2 : ℂ) • p + X i * pderiv i p
        - (1/4 : ℂ) • (X i * (X i * p)) := by
  have hlei : ∀ q : MvPolynomial (Fin d) ℂ, pderiv i (X i * q) = q + X i * pderiv i q := by
    intro q
    rw [Derivation.leibniz, pderiv_X_self]
    simp [smul_eq_mul]
    ring
  set q : MvPolynomial (Fin d) ℂ := pderiv i p - (1/2 : ℂ) • (X i * p) with hq
  have h1 : momPoly i p = (-Complex.I) • q := momPoly_apply' i p
  have h2 : momPoly i ((-Complex.I) • q) = (-Complex.I) • (momPoly i q) := map_smul _ _ _
  have h3 : momPoly i q = (-Complex.I) • (pderiv i q - (1/2 : ℂ) • (X i * q)) :=
    momPoly_apply' i q
  have hdq : pderiv i q = pderiv i (pderiv i p) - (1/2 : ℂ) • (p + X i * pderiv i p) := by
    rw [hq, map_sub, Derivation.map_smul_of_tower, hlei]
  have hxq : X i * q = X i * pderiv i p - (1/2 : ℂ) • (X i * (X i * p)) := by
    rw [hq, mul_sub, mul_smul_comm]
  have hinner : pderiv i q - (1/2 : ℂ) • (X i * q)
      = pderiv i (pderiv i p) - (1/2 : ℂ) • p - X i * pderiv i p
        + (1/4 : ℂ) • (X i * (X i * p)) := by
    rw [hdq, hxq]
    module
  have hII : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by simp [Complex.I_mul_I]
  rw [h1, h2, h3, hinner, smul_smul, hII]
  module

/-- `−∂ᵢ² + xᵢ²/4 = xᵢ∂ᵢ − ∂ᵢ² + ½` in polynomial coordinates: the Gaussian weight turns the
oscillator into the number operator plus `½`. -/
theorem oscPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    oscPoly i p = X i * pderiv i p - pderiv i (pderiv i p) + (1/2 : ℂ) • p := by
  simp only [oscPoly, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    mulXPoly_apply, momPoly_sq]
  module

/-- The number operator `aᵢ†aᵢ` acts on the product Hermite polynomial by `αᵢ`. -/
theorem hermiteMv_number (i : Fin d) (a : Fin d →₀ ℕ) :
    X i * pderiv i (hermiteMv a) - pderiv i (pderiv i (hermiteMv a))
      = ((a i : ℂ)) • hermiteMv a := by
  classical
  set b : Fin d →₀ ℕ := a - Finsupp.single i 1 with hb
  have hd : pderiv i (hermiteMv a) = ((a i : ℂ)) • hermiteMv b := pderiv_hermiteMv i a
  rw [hd, mul_smul_comm, Derivation.map_smul_of_tower, ← smul_sub]
  have hcre : X i * hermiteMv b - pderiv i (hermiteMv b)
      = hermiteMv (b + Finsupp.single i 1) := by
    have h := crePoly_hermiteMv i b
    rwa [crePoly_apply] at h
  rw [hcre]
  rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
  · rw [h0]; simp
  · have hba : b + Finsupp.single i 1 = a := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [hb]; omega
      · simp [hb, hj]
    rw [hba]

/-- **The product Hermite functions diagonalize the one-coordinate oscillator**:
`(−∂ᵢ² + xᵢ²/4) ψ_α = (αᵢ + ½) ψ_α`. -/
theorem oscPoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    oscPoly i (hermiteMv a) = (((a i : ℝ) : ℂ) + 1/2) • hermiteMv a := by
  rw [oscPoly_apply, hermiteMv_number, ← add_smul]
  norm_num

/-! ## The Hamiltonian `H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` -/

/-- The weighted sum of the one-coordinate oscillators, in polynomial coordinates. -/
def quadPoly (c : Fin d → ℝ) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, ((c i : ℝ) : ℂ) • oscPoly i

/-- The symbol of `H_c` on the product Hermite function `ψ_α`. -/
def quadSymbol (c : Fin d → ℝ) (a : Fin d →₀ ℕ) : ℝ := ∑ i, c i * ((a i : ℝ) + 1/2)

theorem quadPoly_hermiteMv (c : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    quadPoly c (hermiteMv a) = ((quadSymbol c a : ℝ) : ℂ) • hermiteMv a := by
  rw [quadPoly, LinearMap.sum_apply]
  have hterm : ∀ i : Fin d, (((c i : ℝ) : ℂ) • oscPoly i) (hermiteMv a)
      = (((c i * ((a i : ℝ) + 1/2) : ℝ)) : ℂ) • hermiteMv a := by
    intro i
    rw [LinearMap.smul_apply, oscPoly_hermiteMv, smul_smul]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul]
  congr 1
  rw [quadSymbol]
  push_cast
  ring

/-- **The Hamiltonian `H_c` on the Gauss–polynomial (Hermite) core of `L²(ℝᵈ)`.** -/
def quadOp (c : Fin d → ℝ) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (quadPoly c)

theorem pgLp_hermiteMvLp (a : Fin d →₀ ℕ) :
    pgLp (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a) = hermiteMvLp a := by
  rw [pgLp_smul]; rfl

/-- **The diagonal action**: `H_c ψ_α = (∑ᵢ cᵢ(αᵢ + ½)) ψ_α`. -/
theorem quadOp_hermiteMvLp (c : Fin d → ℝ) (a : Fin d →₀ ℕ)
    (h : hermiteMvLp a ∈ polyGaussCore (d := d)) :
    quadOp c ⟨hermiteMvLp a, h⟩ = ((quadSymbol c a : ℝ) : ℂ) • hermiteMvLp a := by
  have hcoe : (⟨hermiteMvLp a, h⟩ : polyGaussCore (d := d))
      = coreEquiv (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a) := by
    apply Subtype.ext
    rw [coreEquiv_coe, pgLp_hermiteMvLp]
  rw [hcoe]
  simp only [quadOp, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [coreOp_coe, map_smul, quadPoly_hermiteMv, ← smul_assoc, smul_eq_mul, mul_comm,
    ← smul_eq_mul, smul_assoc, pgLp_smul, pgLp_hermiteMvLp]

end

end BookProof.HyperbolicQuadratic
