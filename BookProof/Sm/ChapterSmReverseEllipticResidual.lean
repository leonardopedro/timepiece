import Mathlib
import BookProof.Sm.ChapterSmGradInterpolation

/-!
# The reverse elliptic estimate: its exact residual, and what the sign route cannot reach

Work order: `SM_ESA_COMPLETION_PLAN.md` §31.

## 1. What is being attacked

`PotSelfBound P c₀ β` is `‖W p + p‖ ≤ β ‖(−Δ_S + W + 1) p‖`, and §26 proved it equivalent to §19's
`hpoly`.  Writing

```text
K = −Δ_S p,        T = W p + p,        N p = K + T,
```

the estimate is `‖T‖ ≤ β ‖K + T‖`.  This section computes the exact residual of that inequality, so
that the gap is an equation and not a slogan, and then shows what the two available tools — the sign
identity of §23 and the interpolation of §26 — can and cannot do with it.

## 2. The exact residual

`‖K + T‖² = ‖K‖² + 2 Re ⟪K, T⟫ + ‖T‖²`, so `β = 1` is **equivalent** to the non-negativity of

```text
‖K‖² + 2 Re ⟪K, T⟫.
```

Both directions are `norm_shift_sq_decomp` and `potSelfBound_one_iff_remainder`, so with
`β = 1` there is no approximation anywhere: the reverse estimate is the statement that this number
is non-negative.
The interesting content is in `Re ⟪K, T⟫`, and §23 evaluates half of it:

* `re_inner_kinPolyS_self` — `Re ⟪−Δ_S p, p⟫ = ∑_{j ∈ S} ‖∇_j p‖²` (this is §23's weighted
  identity at weight `1`; it was used implicitly in §26 and is recorded here because the residual
  needs it);
* `inner_KT_eq` — `Re ⟪K, T⟫ = Re ⟪W p, −Δ_S p⟫ + ∑_{j ∈ S} ‖∇_j p‖²`, i.e. the sign identity's left
  side plus the Dirichlet energy.

## 3. What the interpolation buys, and why `β = 1` is out of reach

§26 gives `∑_j ‖∇_j p‖² ≤ 2 Re ⟪W p, −Δ_S p⟫ + ∑_j ‖(∂_j W) p‖²`, i.e.
`2 Re ⟪W p, −Δ_S p⟫ ≥ G − C` with `G` the Dirichlet energy and `C` the gradient term.  Substituting
into the residual gives the sufficient condition

```text
C  ≤  ‖K‖² + 3 G            (GradResidual),
```

and `potSelfBound_one_of_grad_residual` proves `GradResidual → PotSelfBound P c₀ 1`.

This is the sharpest statement the sign route yields, and the module says what it is worth rather
than presenting it as a step towards the self-bound:

* the hypothesis `GradResidual` is a comparison between the **cubic** quantity
  `∑_j ‖(∂_j W) p‖²` and the **second-order** quantities `‖Δ_S p‖²`, `∑_j ‖∇_j p‖²`.  For the SM's
  quartic `W` it is a
  genuine inequality about `∇W` alone, and it is *not* a consequence of anything in the corpus;
* it is strictly stronger than `PotSelfBound P c₀ 1` (which is the exact residual, with no `2ab ≤
  a² + b²` slack), so `potSelfBound_one_of_grad_residual` is a **sufficient condition**, not an
  equivalence, and the slack it carries is exactly §26's `mul_le_half_add_sq`;
* nothing here proves `GradResidual`, and therefore nothing here proves `PotSelfBound` with any `β`.

The honest conclusion, stated as the result of the attack rather than as a plan: the reverse
estimate is *exactly* the non-negativity of `‖K‖² + 2 Re ⟪K, T⟫`; the sign identity computes
`Re ⟪K, T⟫` up to the commutator term `Re ⟪p ∇W, ∇p⟫`; and every route from there (the
interpolation, hence any amount of the `2ab ≤ a² + b²` calculus) lands on `GradResidual`, which
compares a degree-six density with a second-order norm and is therefore **not** provable by these
tools for the SM's quartic `W`.  A proof of `PotSelfBound` must compare *form domains* — the domain
of the closed form of `−Δ_S + W` with the `H²` domain — which is elliptic regularity, absent from
this corpus.  `PotSelfBound` stays a hypothesis, and `p = 1` is the first test any candidate
inequality should pass.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmReverseEllipticResidual

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds
open BookProof.SmComparisonEsa BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.SmFarisLavine BookProof.SmKineticElliptic BookProof.SmKineticGarding
open BookProof.SmGaussWeightedIbp BookProof.SmGradInterpolation BookProof.QuadratureEsa

noncomputable section

variable {d : ℕ}

/-! ## 0. Two elementary real inequalities -/

/-- `a ≤ b` for non-negative reals from `a ^ 2 ≤ b ^ 2`. -/
theorem le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  have h1 : |a| ≤ |b| := (sq_le_sq).mp h
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at h1

/-- The converse for a non-negative left-hand side. -/
theorem sq_le_sq_of_le {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  simpa [pow_two] using mul_self_le_mul_self ha h

/-! ## 1. The Dirichlet energy is the real part of `⟪−Δ_S p, p⟫` -/

/-- **§23's weighted identity at weight `1`**: the Dirichlet energy of the coordinate family is the
real part of `⟪−Δ_S p, p⟫`.  The commutator term vanishes because `∂_j 1 = 0`. -/
theorem re_inner_kinPolyS_self (S : Finset (Fin d)) (p : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp (kinPolyS S p)) (pgLp p)).re
      = ∑ j ∈ S, ‖pgLp (coreD j p)‖ ^ 2 := by
  have hzero : ∀ q : MvPolynomial (Fin d) ℂ,
      (gaussInt (cpoly (0 : MvPolynomial (Fin d) ℂ) * q)).re = 0 := by
    intro q
    simp [gaussInt, cpoly]
  have h := inner_weighted_kinPolyS S (1 : MvPolynomial (Fin d) ℂ) p
  simp only [one_mul, MvPolynomial.pderiv_one, zero_mul] at h
  have h' : (inner ℂ (pgLp p) (pgLp (kinPolyS S p))).re
      = ∑ j ∈ S, ‖pgLp (coreD j p)‖ ^ 2 := by
    rw [h]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hzero (coreD j p), zero_add, (norm_pgLp_sq (coreD j p)).symm]
  rw [show (inner ℂ (pgLp (kinPolyS S p)) (pgLp p)).re
      = (inner ℂ (pgLp p) (pgLp (kinPolyS S p))).re from inner_re_symm (𝕜 := ℂ) _ _, h']

/-! ## 2. The exact residual of the reverse estimate -/

/-- **The residual decomposition** at the SM comparison: the squared graph norm splits into the
kinetic term, the potential term, and the cross term whose sign §23 controls. -/
theorem norm_shift_sq_decomp (P : SmParams) (c0 : ℝ) (p : MvPolynomial (Fin 163) ℂ) :
    ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖ ^ 2
      = ‖pgLp (kinPolyS smS p)‖ ^ 2
        + 2 * (inner ℂ (pgLp (kinPolyS smS p))
            (pgLp (smPotPoly P c0 * p) + pgLp p)).re
        + ‖pgLp (smPotPoly P c0 * p) + pgLp p‖ ^ 2 := by
  rw [pgLp_add']
  have hassoc : pgLp (kinPolyS smS p) + pgLp (smPotPoly P c0 * p) + pgLp p
      = pgLp (kinPolyS smS p) + (pgLp (smPotPoly P c0 * p) + pgLp p) := by
    abel
  rw [hassoc, norm_add_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex]

/-- **The cross term is the sign identity plus the Dirichlet energy**: §23 computes
`Re ⟪W p, −Δ_S p⟫`, and the second term of the cross product is
`Re ⟪−Δ_S p, p⟫ = ∑_j ‖∇_j p‖²`. -/
theorem inner_KT_eq (P : SmParams) (c0 : ℝ) (p : MvPolynomial (Fin 163) ℂ) :
    (inner ℂ (pgLp (kinPolyS smS p))
        (pgLp (smPotPoly P c0 * p) + pgLp p)).re
      = (inner ℂ (pgLp (smPotPoly P c0 * p)) (pgLp (kinPolyS smS p))).re
        + ∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2 := by
  rw [inner_add_right, Complex.add_re, re_inner_kinPolyS_self]
  congr 1
  exact inner_re_symm (𝕜 := ℂ) _ _


/-! ## 3. The estimate with `β = 1` is exactly the non-negativity of the residual -/

/-- **`PotSelfBound P c₀ 1` is the non-negativity of the residual.**  No inequality of the proof is
lossy here: the two are the same statement. -/
theorem potSelfBound_one_iff_remainder (P : SmParams) (c0 : ℝ) :
    PotSelfBound P c0 1
      ↔ ∀ p : MvPolynomial (Fin 163) ℂ,
        0 ≤ ‖pgLp (kinPolyS smS p)‖ ^ 2
          + 2 * (inner ℂ (pgLp (kinPolyS smS p))
              (pgLp (smPotPoly P c0 * p) + pgLp p)).re := by
  constructor
  · intro h p
    have hle : ‖pgLp (smPotPoly P c0 * p) + pgLp p‖
        ≤ ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖ := by
      simpa using h p
    have hsq : ‖pgLp (smPotPoly P c0 * p) + pgLp p‖ ^ 2
        ≤ ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖ ^ 2 :=
      sq_le_sq_of_le (norm_nonneg _) hle
    rw [norm_shift_sq_decomp] at hsq
    linarith
  · intro h p
    have hsq : ‖pgLp (smPotPoly P c0 * p) + pgLp p‖ ^ 2
        ≤ ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖ ^ 2 := by
      rw [norm_shift_sq_decomp]
      have := h p
      linarith
    have hle := le_of_sq_le_sq (norm_nonneg (pgLp (smPotPoly P c0 * p) + pgLp p))
      (norm_nonneg (pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p)) hsq
    simpa using hle

/-! ## 4. What §26's interpolation yields: the gradient-residual condition -/

/-- **The interpolation's sufficient condition**: if the potential's cubic gradient term is
dominated by the kinetic and Dirichlet energies,

```text
∑_j ‖(∂_j W) p‖²  ≤  ‖Δ_S p‖² + 3 ∑_j ‖∇_j p‖²,
```

then the potential satisfies `PotSelfBound` with `β = 1`.  This is the sharpest constant the sign
route of §23/§26 reaches: the `2ab ≤ a² + b²` slack of `mul_le_half_add_sq` is spent in the `3`, and
the remaining hypothesis is a comparison between a degree-six density and a second-order norm that
the corpus does not prove. -/
theorem potSelfBound_one_of_grad_residual (P : SmParams) {c0 : ℝ} (hc0 : 1 ≤ c0)
    (hres : ∀ p : MvPolynomial (Fin 163) ℂ,
      ∑ j ∈ smS, ‖pgLp (pderiv j (smPotPoly P c0) * p)‖ ^ 2
        ≤ ‖pgLp (kinPolyS smS p)‖ ^ 2
          + 3 * ∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2) :
    PotSelfBound P c0 1 := by
  refine (potSelfBound_one_iff_remainder P c0).mpr ?_
  intro p
  have hbd : 3 * (∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2)
      - (∑ j ∈ smS, ‖pgLp (pderiv j (smPotPoly P c0) * p)‖ ^ 2)
      ≤ 2 * (inner ℂ (pgLp (kinPolyS smS p))
          (pgLp (smPotPoly P c0 * p) + pgLp p)).re := by
    rw [inner_KT_eq]
    have hinterp := dirichlet_le_weighted_form smS (smPotPoly P c0) p
      (realCoeff_smPotPoly P c0) (one_le_polyW_smPotPoly P hc0)
    linarith
  have hres' := hres p
  linarith

end

end BookProof.SmReverseEllipticResidual
