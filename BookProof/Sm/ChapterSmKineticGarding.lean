import Mathlib
import BookProof.Sm.ChapterSmKineticElliptic

/-!
# The quartic Gårding step: the elliptic estimate reduced to the potential's self-bound

Work order: `SM_ESA_COMPLETION_PLAN.md` §22.

## 1. What is attempted, and what came out

§19 reduced §16's `hkin` for the SM comparison to the single polynomial inequality `hpoly`

```text
‖Δ_S p‖ ≤ c ‖Δ_S p + W p + p‖,        W = Σ_r Φ_r² + Σ_m q_m² + c₀,        Δ_S = −kinPolyS smS,
```

where `kinPolyS smS p = −Δ p` is the plain partial Laplacian of the function picture (§19) and `W`
is the quartic potential.  `hpoly` is *not* proved here either, and this section records the outcome
of the attempt rather than a new hypothesis dressed as a result.

What is proved is the classical Gårding factorization, which pins the gap down to a single inequality
about `W` alone:

* `kinetic_le_shift_add_pot` — the triangle identity `‖Δ p‖ ≤ ‖Δp + Wp + p‖ + ‖Wp + p‖`: the
  kinetic term is bounded by the comparison plus the potential, so nothing but the potential stands
  between `hpoly` and the estimate.
* `kineticSum_norm_le_of_pot_self_bound` — if the potential is **self-bounded** with constant `β`,
  i.e. `‖W p + p‖ ≤ β ‖Δ_S p + W p + p‖`, then `hpoly` holds with `c = 1 + β`, and §19's
  `kineticSum_norm_le_of_poly` gives `‖Σ_m π_m² x‖ ≤ (1 + β) ‖N x + x‖`.
* `smNormalForm_norm_le_of_pot_self_bound` — the composition with §19's interpolation half: the full
  second-order family bound of §15 now rests on `PotSelfBound` **alone** (no momentum hypothesis, no
  separate kinetic-sum estimate).

## 2. Why the self-bound is the honest name of the gap

`PotSelfBound P c₀ β` is the Kato-type self-boundedness of `W` with respect to `-Δ_S + W`, and it is
the standard first step of every ellipticity proof for a polynomial potential.  Its usual proof reads
the sign of the cross term

```text
Re ⟪W u, −Δ u⟫ = ‖√W ∇u‖² + Re ⟪u ∇W, ∇u⟫,
```

the first term of which is non-negative, and then interpolates `∇` between `L²` and the graph norm.
Neither ingredient exists in this corpus:

* there is no integration-by-parts identity for a polynomial weight on the Gaussian core — the
  corpus's core lemmas are algebraic (`pgLp_add'`, `lapCS_pgFun`) or inner-product identities for
  *symmetric* operators, and `W` is a multiplication operator, not a core endomorphism;
* the one uncertainty-type bound the corpus has, `norm_sq_harmPoly_mul_le`, controls the **quadratic**
  weight `harmPoly` against the oscillator's own graph norm.  It is exactly what makes
  `norm_kinPoly_le_shiftNorm` work, and it has no quartic analogue: the quartic growth of `W` is
  never again used, in any module, except through the pointwise lower bound
  `one_le_polyW_smPotPoly`.

The pointwise lower bound is *not* enough, and this is worth recording because it is the trap the
attempt fell into first: `W ≥ 1` gives no norm comparison between `‖W p‖` and `‖Δp + Wp + p‖`.
A solution concentrating at high frequency where `W` is order one has a huge `‖Δp‖` and a moderate
`‖Wp‖`, so `‖Wp + p‖ ≤ β‖Δp + Wp + p‖` cannot come from positivity of `W`; it needs the elliptic
bootstrap itself, i.e. the very estimate being proved.  §19's `hpoly` and this section's
`PotSelfBound` are therefore two equivalent spellings of one open problem, and neither is assumed
downstream.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmKineticGarding

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.QgHermiteCore
open BookProof.YangMillsHermite BookProof.DegSchrodinger
open BookProof.SmHamiltonian BookProof.SmOneParticle BookProof.SmFarisLavine
open BookProof.SmComparisonEsa BookProof.SmFullFamilyBounds BookProof.SmFullNormalFormBounds
open BookProof.SmFullMatter BookProof.SmFullCoupledCore BookProof.SmFullYukawaCoeffs
open BookProof.SmMatter
open BookProof.SmKineticElliptic BookProof.QuadratureEsa

noncomputable section

/-! ## 1. The Gårding factorization -/

/-- **The triangle reduction**: the kinetic term is bounded by the comparison plus the potential, so
`hpoly` differs from the elliptic estimate by the potential's self-bound and nothing else. -/
theorem kinetic_le_shift_add_pot (P : SmParams) (c0 : ℝ) (p : MvPolynomial (Fin 163) ℂ) :
    ‖pgLp (kinPolyS smS p)‖
      ≤ ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖
        + ‖pgLp (smPotPoly P c0 * p) + pgLp p‖ := by
  have hsplit : pgLp (kinPolyS smS p)
      = (pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p)
        - (pgLp (smPotPoly P c0 * p) + pgLp p) := by
    rw [pgLp_add']
    abel
  rw [hsplit]
  exact norm_sub_le _ _

/-- **The self-bound of the quartic potential** — the single inequality the elliptic estimate needs:
`W` plus the identity is dominated by the full comparison `−Δ_S + W + 1` with constant `β`.  This is
the Kato-type self-boundedness whose standard proof is the sign identity of the cross term; see the
module docstring for why the corpus cannot supply it yet. -/
def PotSelfBound (P : SmParams) (c0 β : ℝ) : Prop :=
  ∀ p : MvPolynomial (Fin 163) ℂ,
    ‖pgLp (smPotPoly P c0 * p) + pgLp p‖
      ≤ β * ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖

/-- **The elliptic estimate from the potential's self-bound**: `hpoly` of §19 holds with
`c = 1 + β`. -/
theorem kineticSum_norm_le_of_pot_self_bound (P : SmParams) (c0 : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hpot : PotSelfBound P c0 β) (x : polyGaussCore (d := 163)) :
    ‖(((∑ m : Fin 40, smPi m (smPi m x)) : polyGaussCore (d := 163)) : L2d 163)‖
      ≤ (1 + β) * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ := by
  refine kineticSum_norm_le_of_poly P c0 ?_ x
  intro p
  set S : L2d 163 := pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p
  set T : L2d 163 := pgLp (smPotPoly P c0 * p) + pgLp p
  have hS : S = pgLp (kinPolyS smS p) + T := by
    show pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p
      = pgLp (kinPolyS smS p) + (pgLp (smPotPoly P c0 * p) + pgLp p)
    rw [pgLp_add']
    abel
  have h1 : ‖pgLp (kinPolyS smS p)‖ ≤ ‖S‖ + ‖T‖ := by
    have hdiff : pgLp (kinPolyS smS p) = S - T := by
      rw [hS]
      abel
    rw [hdiff]
    exact norm_sub_le _ _
  have h2 : ‖T‖ ≤ β * ‖S‖ := hpot p
  have hβS : 0 ≤ β * ‖S‖ := mul_nonneg hβ (norm_nonneg S)
  nlinarith [h1, h2, hβS, norm_nonneg S]

/-! ## 2. The composition with the interpolation half of §19 -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
-- the support reindexing and the `PiLp` norm expansion exceed the default budgets
/-- **The second-order family bound of §15 from the potential's self-bound alone.**  §19 removed the
momentum hypothesis `hmom` at the price of the kinetic-sum estimate; this removes the estimate as an
independent input, so the whole P2 relative bound for the SM rests on `PotSelfBound`. -/
theorem smNormalForm_norm_le_of_pot_self_bound (P : SmParams) (D : SmNormalFormData)
    (c0 : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hpot : PotSelfBound P c0 β)
    (hpos : ∀ x : polyGaussCore (d := 163), 0 ≤ quadForm (smFlN P c0) x)
    (hSmom : ∀ j ∉ Finset.image smMomCoordFin Finset.univ, D.mom j = 0)
    (Skin Scoord : Finset (Fin 163))
    (hSkin : ∀ j ∉ Skin, D.kinetic j = 0) (hScoord : ∀ j ∉ Scoord, D.coord j = 0)
    (hkin : ∀ j ∈ Skin, ∀ x : polyGaussCore (d := 163),
      ‖((smKinetic j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ (1 + β) * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hcoord : ∀ j ∈ Scoord, ∀ x : polyGaussCore (d := 163),
      ‖((smPos j x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ (1 + β) * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (hmass : ∀ x : polyGaussCore (d := 163),
      ‖((x : polyGaussCore (d := 163)) : L2d 163)‖
        ≤ (1 + β) * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖)
    (f : SmCoupledCore) :
    ‖smNormalForm D f‖
      ≤ (1 + β) * normalFormConst D
        * ‖coupledOp (smFlN P c0) 1 f + (f : SmCoupledSpace)‖ :=
  smNormalForm_norm_le_of_kineticSum D (smFlN P c0)
    (by linarith) hpos (fun x => kineticSum_norm_le_of_pot_self_bound P c0 hβ hpot x)
    hSmom Skin Scoord hSkin hScoord hkin hcoord hmass f

end

end BookProof.SmKineticGarding
