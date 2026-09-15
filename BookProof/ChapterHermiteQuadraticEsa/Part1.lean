import Mathlib
import BookProof.ChapterQgHermiteOscillatorEsa

/-!
# Unbounded quadratic-type perturbations on the Gauss–polynomial (Hermite) core

`CONSOLIDATED_PLAN.md` §10.6.1 target 4 asks for essential self-adjointness of the *sum*
`−Δ + V` on the Gauss–polynomial core of `L²(ℝᵈ)`.  What was available so far is
`BookProof.ChapterQgHermiteOscillatorEsa`: the harmonic (conformal-mode) Hamiltonian
`−Δ + ‖x‖²/4` is essentially self-adjoint on that core, and — by Kato–Rellich with relative
bound `0` — so is `−Δ + ‖x‖²/4 + B` for a *bounded* continuous `B`.  On the other side,
`BookProof.ChapterHermiteExpWall` shows that the exponentially growing scalaron wall is
**not** relatively bounded on this core at all, so no Kato–Rellich argument can reach it.

This module fills the gap in between: **unbounded** perturbations of quadratic type.

## The analytic input

The one quantitative fact needed is the relative bound of the harmonic potential itself with
respect to the harmonic Hamiltonian, with constant `1`:

`‖(‖x‖²/4)ψ‖² ≤ ‖(−Δ + ‖x‖²/4)ψ‖² + (d/2)‖ψ‖²`   (`norm_sq_harmPoly_mul_le`).

It comes from the anticommutator identity (`gaussInt_anticommutator`), which on the
Gauss–polynomial core is a purely algebraic computation with the twisted derivative
`coreD j = ∂ⱼ − xⱼ/2` and Gaussian integration by parts:

`⟪−Δψ, Wψ⟫ + ⟪Wψ, −Δψ⟫ = 2 ∑ⱼ ⟪∂ⱼψ, W ∂ⱼψ⟫ − (d/2)‖ψ‖²`,  `W = ‖x‖²/4`,

whose right-hand side is `≥ −(d/2)‖ψ‖²` because `W ≥ 0`.  (Classically this is
`{−Δ, W} = −ΔW + 2∑ⱼ(−∂ⱼ)W∂ⱼ` with `ΔW = d/2`.)

## What is proved

* `gaussInt_anticommutator`, `two_re_inner_kin_harm_ge`, `norm_sq_harmPoly_mul_le`,
  `norm_harmPoly_mul_le` — the relative bound of `‖x‖²/4` with respect to `−Δ + ‖x‖²/4`,
  with relative constant `1` and additive constant `√(d/2)`;
* `norm_potLp_le_of_le_harm` — the `L²` bound `‖Vψ‖ ≤ a‖Wψ‖ + b‖ψ‖` for a potential
  dominated pointwise by `a·‖x‖²/4 + b`;
* **`harmonic_add_subquadratic_essentiallySelfAdjoint`** — the headline: if `V` is
  continuous with `|V(x)| ≤ a‖x‖²/4 + b` and `a < 1`, then `−Δ + ‖x‖²/4 + V` is essentially
  self-adjoint on the Gauss–polynomial core.  The perturbation may be unbounded;
* `harmonic_add_subquadratic_stone_flow` — the self-adjoint realization and its unitary
  group, read off from essential self-adjointness;
* `quadraticGrowth_essentiallySelfAdjoint` — the criterion in growth form: a continuous
  potential `U` with `|U(x) − ‖x‖²/4| ≤ A‖x‖² + C‖x‖ + B` and `4A < 1`;
* `scaledHarmonic_essentiallySelfAdjoint` — `−Δ + λ‖x‖²/4` is essentially self-adjoint on the
  (fixed, width-one) Gauss core for every `λ ∈ (0, 2)`;
* **`confV_essentiallySelfAdjoint`** — the conformal-mode instance of §10.6.1 target 4: the
  regularized `R + αR²` conformal-mode Hamiltonian `−Δ + V₃`,
  `V₃(R_c) = −(M²/2)R_c + αR_c²`, is essentially self-adjoint on the Gauss core of `L²(ℝ)`
  for `0 < α < 1/2`, unconditionally (no finite-speed hypothesis), together with its Stone
  flow `confV_stone_flow`;
* **`sectorQuad_essentiallySelfAdjoint`** — the two-variable reduced `(R_c, φ)` sector with
  the scalaron wall replaced by a quadratic term, `V₃(R_c) + μφ²` on `L²(ℝ²)`, for
  `0 < α < 1/2` and `0 < μ < 1/2`, with `sectorQuad_stone_flow`;
  `tendsto_starobinskyV_div_sq` computes the curvature of the scalaron potential at its
  minimum, `V(φ)/φ² → M²/(24α)`, and `sectorHarmonicApprox_essentiallySelfAdjoint` is the
  sector statement at that physically natural value of `μ`, valid when `M² < 12α`.

**Honest boundary.**  The relative bound of `‖x‖²/4` against `−Δ + ‖x‖²/4` is exactly `1`, so
the Kato–Rellich window `a < 1` is the natural limit of this method: it reaches quadratic
potentials whose curvature is within a factor `2` of the width of the Gauss core (this is why
`confV_essentiallySelfAdjoint` carries `α < 1/2`; a different `α` is the same operator on a
Gauss core of a different width, which this module does not build), and every strictly
subquadratic perturbation of them.  It does not reach the exponential scalaron wall — nothing
can, on this core, by `BookProof.ChapterHermiteExpWall`.
-/

namespace BookProof.HermiteQuadraticEsa

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. Algebraic preliminaries on the core -/

/-- The gradient of the harmonic potential: `∂ⱼ(‖x‖²/4) = xⱼ/2`. -/
theorem pderiv_harmPoly (j : Fin d) :
    pderiv j (harmPoly (d := d)) = C (1 / 2 : ℂ) * X j := by
  have hC : (C (1 / 4 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = C (1 / 2 : ℂ) := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  unfold harmPoly
  rw [map_sum, Finset.sum_eq_single j]
  · rw [pderiv_C_mul, pow_two, pderiv_mul, pderiv_X_self]
    linear_combination (X j : MvPolynomial (Fin d) ℂ) * hC
  · intro k _ hk
    rw [pderiv_C_mul, pow_two, pderiv_mul, pderiv_X_of_ne hk]
    ring
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Leibniz for the twisted derivative against the harmonic potential.** -/
theorem coreD_harmPoly_mul (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    coreD j (harmPoly * p) = C (1 / 2 : ℂ) * (X j * p) + harmPoly * coreD j p := by
  unfold coreD
  rw [pderiv_mul, pderiv_harmPoly]
  ring

/-- The twisted derivative against a coordinate. -/
theorem coreD_X_mul (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    coreD j (X j * p) = p + X j * coreD j p := by
  unfold coreD
  rw [pderiv_mul, pderiv_X_self]
  ring

/-- Conjugation of coefficients is additive. -/
theorem cpoly_add (p q : MvPolynomial (Fin d) ℂ) : cpoly (p + q) = cpoly p + cpoly q := by
  simp [cpoly]

/-- The harmonic polynomial has real coefficients. -/
theorem cpoly_harmPoly : cpoly (harmPoly (d := d)) = harmPoly := by
  have hq : (starRingEnd ℂ) (1 / 4 : ℂ) = 1 / 4 := by norm_num [Complex.ext_iff]
  unfold harmPoly
  rw [cpoly_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_two, cpoly_mul, cpoly_mul, cpoly_C, cpoly_X, hq]

/-- The cross term of the anticommutator: Gaussian integration by parts against `xⱼ`. -/
theorem gaussInt_cross (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (coreD j p) * (X j * p)) + gaussInt (cpoly p * (X j * coreD j p))
      = -gaussInt (cpoly p * p) := by
  rw [gaussInt_coreD j p (X j * p), coreD_X_mul, mul_add, gaussInt_add]
  ring

/-- The Gaussian pairing of a polynomial with itself is the squared `L²` norm of the core
vector it names. -/
theorem gaussInt_self (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly r * r) = ((‖pgLp r‖ ^ 2 : ℝ) : ℂ) := by
  rw [← inner_pgLp_pgLp, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  norm_cast

/-- The harmonic quadratic form on the core is a sum of squared norms — in particular it is
a nonnegative real. -/
theorem gaussInt_harm_self (q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly q * (harmPoly * q))
      = (((∑ k : Fin d, ‖pgLp (X k * q)‖ ^ 2) / 4 : ℝ) : ℂ) := by
  have hsum : cpoly q * (harmPoly * q)
      = ∑ k : Fin d, (1 / 4 : ℂ) • (cpoly (X k * q) * (X k * q)) := by
    unfold harmPoly
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cpoly_mul, cpoly_X, smul_eq_C_mul]
    ring
  have hterm : ∀ k : Fin d, gaussInt ((1 / 4 : ℂ) • (cpoly (X k * q) * (X k * q)))
      = ((‖pgLp (X k * q)‖ ^ 2 / 4 : ℝ) : ℂ) := by
    intro k
    rw [gaussInt_smul, gaussInt_self]
    push_cast
    ring
  rw [hsum, gaussInt_sum]
  simp only [hterm]
  rw [← Complex.ofReal_sum, Finset.sum_div]

/-- **The anticommutator identity** `{−Δ, W} = −(d/2) + 2∑ⱼ(−∂ⱼ)W∂ⱼ`, in the Gaussian
pairing of the core. -/
theorem gaussInt_anticommutator (p : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (kinPoly p) * (harmPoly * p))
        + gaussInt (cpoly (harmPoly * p) * kinPoly p)
      = 2 * (∑ j : Fin d, gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)))
        - ((d : ℂ) / 2) * gaussInt (cpoly p * p) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by norm_num [Complex.ext_iff]
  have hT1 : ∀ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j (harmPoly * p))
      = (1 / 2 : ℂ) * gaussInt (cpoly (coreD j p) * (X j * p))
        + gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)) := by
    intro j
    rw [coreD_harmPoly_mul, mul_add, gaussInt_add]
    congr 1
    have hsm : cpoly (coreD j p) * (C (1 / 2 : ℂ) * (X j * p))
        = (1 / 2 : ℂ) • (cpoly (coreD j p) * (X j * p)) := by
      rw [smul_eq_C_mul]; ring
    rw [hsm, gaussInt_smul]
  have hT2 : ∀ j : Fin d, gaussInt (cpoly (coreD j (harmPoly * p)) * coreD j p)
      = (1 / 2 : ℂ) * gaussInt (cpoly p * (X j * coreD j p))
        + gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)) := by
    intro j
    rw [coreD_harmPoly_mul, cpoly_add]
    simp only [cpoly_mul, cpoly_C, cpoly_X, cpoly_harmPoly, hhalf]
    rw [add_mul, gaussInt_add]
    congr 1
    · have hsm : C (1 / 2 : ℂ) * (X j * cpoly p) * coreD j p
          = (1 / 2 : ℂ) • (cpoly p * (X j * coreD j p)) := by
        rw [smul_eq_C_mul]; ring
      rw [hsm, gaussInt_smul]
    · congr 1
      ring
  rw [gaussInt_kinPoly_left p (harmPoly * p), gaussInt_kinPoly (harmPoly * p) p]
  simp only [hT1, hT2]
  rw [← Finset.sum_add_distrib]
  have hstep : ∀ j : Fin d,
      ((1 / 2 : ℂ) * gaussInt (cpoly (coreD j p) * (X j * p))
          + gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)))
        + ((1 / 2 : ℂ) * gaussInt (cpoly p * (X j * coreD j p))
          + gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)))
      = 2 * gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p))
        - (1 / 2 : ℂ) * gaussInt (cpoly p * p) := by
    intro j
    have h := gaussInt_cross j p
    linear_combination (1 / 2 : ℂ) * h
  simp only [hstep]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ## 2. The relative bound of the harmonic potential -/

/-- The cross term in `‖(−Δ + W)ψ‖²` is bounded below by `−(d/2)‖ψ‖²`. -/
theorem two_re_inner_kin_harm_ge (p : MvPolynomial (Fin d) ℂ) :
    -((d : ℝ) / 2) * ‖pgLp p‖ ^ 2
      ≤ 2 * (inner ℂ (pgLp (kinPoly p)) (pgLp (harmPoly * p)) : ℂ).re := by
  set A : ℂ := (inner ℂ (pgLp (kinPoly p)) (pgLp (harmPoly * p)) : ℂ) with hAdef
  set R : ℝ := ∑ j : Fin d, (∑ k : Fin d, ‖pgLp (X k * coreD j p)‖ ^ 2) / 4 with hRdef
  have hR : 0 ≤ R := by
    rw [hRdef]; positivity
  have hA : A = gaussInt (cpoly (kinPoly p) * (harmPoly * p)) := inner_pgLp_pgLp _ _
  have hB : (inner ℂ (pgLp (harmPoly * p)) (pgLp (kinPoly p)) : ℂ)
      = gaussInt (cpoly (harmPoly * p) * kinPoly p) := inner_pgLp_pgLp _ _
  have hconj : gaussInt (cpoly (harmPoly * p) * kinPoly p) = (starRingEnd ℂ) A := by
    rw [← hB, hAdef, inner_conj_symm]
  have key := gaussInt_anticommutator p
  rw [← hA, hconj, Complex.add_conj, gaussInt_self] at key
  simp only [gaussInt_harm_self] at key
  have hcast :
      (2 : ℂ) * (∑ j : Fin d, (((∑ k : Fin d, ‖pgLp (X k * coreD j p)‖ ^ 2) / 4 : ℝ) : ℂ))
        - ((d : ℂ) / 2) * ((‖pgLp p‖ ^ 2 : ℝ) : ℂ)
      = (((2 * R - (d : ℝ) / 2 * ‖pgLp p‖ ^ 2 : ℝ)) : ℂ) := by
    rw [hRdef]
    push_cast
    ring
  rw [hcast] at key
  have hreal : 2 * A.re = 2 * R - (d : ℝ) / 2 * ‖pgLp p‖ ^ 2 := by exact_mod_cast key
  linarith

/-- **The harmonic potential is relatively bounded by the harmonic Hamiltonian with relative
constant `1`.** -/
theorem norm_sq_harmPoly_mul_le (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp (harmPoly * p)‖ ^ 2
      ≤ ‖pgLp (kinPoly p + harmPoly * p)‖ ^ 2 + ((d : ℝ) / 2) * ‖pgLp p‖ ^ 2 := by
  have hadd : pgLp (kinPoly p + harmPoly * p) = pgLp (kinPoly p) + pgLp (harmPoly * p) := by
    rw [← pgMap_apply, ← pgMap_apply, ← pgMap_apply, map_add]
  have hre : RCLike.re (inner ℂ (pgLp (kinPoly p)) (pgLp (harmPoly * p)) : ℂ)
      = (inner ℂ (pgLp (kinPoly p)) (pgLp (harmPoly * p)) : ℂ).re := rfl
  rw [hadd, norm_add_sq (𝕜 := ℂ), hre]
  have h := two_re_inner_kin_harm_ge p
  nlinarith [sq_nonneg ‖pgLp (kinPoly p)‖]

/-- The same bound in the form Kato–Rellich uses. -/
theorem norm_harmPoly_mul_le (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp (harmPoly * p)‖
      ≤ ‖pgLp (kinPoly p + harmPoly * p)‖ + Real.sqrt ((d : ℝ) / 2) * ‖pgLp p‖ := by
  have hs : Real.sqrt ((d : ℝ) / 2) ^ 2 = (d : ℝ) / 2 :=
    Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt ((d : ℝ) / 2) := Real.sqrt_nonneg _
  have h := norm_sq_harmPoly_mul_le p
  nlinarith [norm_nonneg (pgLp (harmPoly * p)), norm_nonneg (pgLp (kinPoly p + harmPoly * p)),
    norm_nonneg (pgLp p), mul_nonneg hs0 (norm_nonneg (pgLp p))]

/-! ## 3. Potentials dominated by the harmonic one -/

/-- A potential dominated by `a‖x‖²/4 + b` is exponentially bounded. -/
theorem expBounded_of_le_harm {V : Vd d → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b) : ExpBounded V := by
  refine ⟨a / 2 + b, 1, zero_le_one, fun x => ?_⟩
  have h := Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) 2
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hfac] at h
  have h1 : (1 : ℝ) ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg x)
  have hharm : harmW x = ‖x‖ ^ 2 / 4 := rfl
  have hVx := hV x
  rw [hharm] at hVx
  rw [one_mul]
  nlinarith

/-- The `L²` bound for a potential dominated by `a‖x‖²/4 + b`. -/
theorem norm_potLp_le_of_le_harm {V : Vd d → ℝ} (hVc : Continuous V) (hVb : ExpBounded V)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hV : ∀ x, |V x| ≤ a * harmW x + b)
    (p : MvPolynomial (Fin d) ℂ) :
    ‖potLp V hVc hVb p‖ ≤ a * ‖pgLp (harmPoly * p)‖ + b * ‖pgLp p‖ := by
  have hstep : ‖potLp V hVc hVb p‖
      ≤ ‖((a : ℝ) : ℂ) • pgLp (harmPoly * p) + ((b : ℝ) : ℂ) • pgLp p‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [potLp_coeFn V hVc hVb p,
      Lp.coeFn_add (((a : ℝ) : ℂ) • pgLp (harmPoly * p)) (((b : ℝ) : ℂ) • pgLp p),
      Lp.coeFn_smul ((a : ℝ) : ℂ) (pgLp (harmPoly * p)),
      Lp.coeFn_smul ((b : ℝ) : ℂ) (pgLp p),
      pgLp_coeFn (harmPoly * p), pgLp_coeFn p] with x h1 h2 h3 h4 h5 h6
    have hfun : pgFun (harmPoly * p) x = ((harmW x : ℝ) : ℂ) * pgFun p x := by
      simp only [pgFun, map_mul, eval_harmPoly]
      ring
    rw [h1, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6, hfun,
      smul_eq_mul, smul_eq_mul]
    have hrw : ((a : ℝ) : ℂ) * (((harmW x : ℝ) : ℂ) * pgFun p x) + ((b : ℝ) : ℂ) * pgFun p x
        = ((a * harmW x + b : ℝ) : ℂ) * pgFun p x := by
      push_cast
      ring
    rw [hrw, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hpos : 0 ≤ a * harmW x + b := by
      have : 0 ≤ harmW x := by unfold harmW; positivity
      positivity
    rw [abs_of_nonneg hpos]
    exact hV x
  refine hstep.trans ((norm_add_le _ _).trans ?_)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]

/-! ## 4. The essential self-adjointness theorem -/

/-- **Essential self-adjointness of `−Δ + ‖x‖²/4 + V` for an unbounded, quadratically
dominated perturbation.**  If `V` is continuous and `|V(x)| ≤ a‖x‖²/4 + b` with `a < 1`, the
Gauss–polynomial (Hermite) core is a core for `−Δ + ‖x‖²/4 + V`. -/
theorem harmonic_add_subquadratic_essentiallySelfAdjoint {V : Vd d → ℝ} {a b : ℝ}
    (hVc : Continuous V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b)
    (hsc : Continuous fun x => harmW x + V x) (hsb : ExpBounded fun x => harmW x + V x) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (hamCore (fun x => harmW x + V x) hsc hsb) := by
  have hVb : ExpBounded V := expBounded_of_le_harm ha hb hV
  have hs0 : (0 : ℝ) ≤ Real.sqrt ((d : ℝ) / 2) := Real.sqrt_nonneg _
  rw [hamCore_add_potential harmW V continuous_harmW expBounded_harmW hVc hVb hsc hsb]
  refine BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded
    (a := a) (b := a * Real.sqrt ((d : ℝ) / 2) + b) _ _
    harmonicCore_symmetricOn harmonicCore_essentiallySelfAdjoint
    (potCore_symmetricOn V hVc hVb) ha ha1 (by positivity) fun x => ?_
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  rw [hx, potCore_pgLp]
  have hham : (hamCore harmW continuous_harmW expBounded_harmW) ⟨pgLp p, pgLp_mem_core p⟩
      = pgLp (kinPoly p + harmPoly * p) := harmCore_pgLp p
  rw [hham]
  have h1 := norm_potLp_le_of_le_harm hVc hVb ha hb hV p
  have h2 := norm_harmPoly_mul_le p
  have hcoe : ‖((⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := d)) : L2d d)‖ = ‖pgLp p‖ := rfl
  rw [hcoe]
  nlinarith [norm_nonneg (pgLp p), norm_nonneg (pgLp (kinPoly p + harmPoly * p))]

/-- The Stone flow of `−Δ + ‖x‖²/4 + V`: essential self-adjointness on the dense core produces
a self-adjoint realization together with the unitary group it generates. -/
theorem harmonic_add_subquadratic_stone_flow {V : Vd d → ℝ} {a b : ℝ}
    (hVc : Continuous V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b)
    (hsc : Continuous fun x => harmW x + V x) (hsb : ExpBounded fun x => harmW x + V x) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (hamCore (fun x => harmW x + V x) hsc hsb) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense (hamCore_symmetricOn _ hsc hsb)
    (harmonic_add_subquadratic_essentiallySelfAdjoint hVc ha ha1 hb hV hsc hsb)

end

end BookProof.HermiteQuadraticEsa
