import Mathlib
import BookProof.Sm.ChapterSmDegenerateDoubletSharp

/-!
# Which quadratic-weight lemmas survive a weight dominated by `harmPoly`

Work order: `SM_ESA_COMPLETION_PLAN.md` §37.

## 1. The question

§33 recorded that for a quadratic weight the whole §22/§32 package is a theorem.  Which parts of it
survive for a **more general** weight `W` that is merely dominated by the harmonic potential, i.e.
`|W(x)| ≤ λ · harmW(x) + μ`?  That is the largest class in which the corpus's quadratic tool
(`norm_potLp_le_of_le_harm`) applies, so it is the right boundary to map.

## 2. The table

| lemma | status for `W` with `|W| ≤ λ harmW + μ` |
| :--- | :--- |
| lemma | status |
| :--- | :--- |
| potential bound `‖W p‖ ≤ λ' shiftNorm p` | **holds** — `norm_potLp_le_of_le_harm` gives the
  two terms, §33's `potentialBound_harm` evaluates the harmonic one |
| identity bound `‖p‖ ≤ shiftNorm p` | **holds** unconditionally — §33's `identityBound_harm` |
| self-bound `‖W p + p‖ ≤ β shiftNorm p` | **holds by composition** — `selfBound_of_potBound` |
| coercivity `‖p‖ ≤ ‖N_W p‖` | **holds** for `W ≥ 0`, by §32's argument with `W` for `smPotPoly` |
| **reverse (`H²`) estimate** | **does not follow** — see §3 |

So every *lower-order* statement survives; the one that does not is the statement about the
**comparison operator** `−Δ + W + 1` itself.

## 3. Why the reverse estimate is not in the table

The reverse estimate is `‖Δ p‖ ≤ c ‖(−Δ + W + 1) p‖`, and the domination `|W| ≤ λ harmW + μ` says
nothing about the graph norm of *that* operator: it is a bound on `W`, not a comparison between the
two graph norms.  Passing from the harmonic instance to `N_W` needs
`‖N_harm p‖ ≤ κ ‖N_W p‖`, which is a statement about the two forms, i.e. §32's named input in
another guise.  This is not a gap in the argument but a fact about what domination of a
*coefficient* can and cannot say; correspondingly the corpus's one uncertainty bound,
`norm_sq_harmPoly_mul_le`, controls `W` only when `W` is itself quadratic.

The honest summary: a potential dominated by `harmPoly` gets the self-bound and coercivity for free,
and does not get the reverse estimate.  The SM's quartic `W` is not even in this class (`W` is not
pointwise dominated by `harmPoly`, degree four against degree two), so the table's provable half
does not apply to it either.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmQuadraticWeightLemmas

open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds BookProof.QgHermiteOscillator
open BookProof.SmHarmonicReverseEstimate

noncomputable section

variable {D : ℕ}

/-! ## 1. The composition step -/

/-- **From a potential bound to a self-bound**: if the weight is bounded by the harmonic graph norm
with constant `λ`, then the weight plus the identity is bounded with `λ + 1`.  This is the only step
between the potential bound of a dominated weight and the `PotSelfBound` shape, and it holds for
*any* weight, quadratic or not — it uses no property of `W` beyond the hypothesis. -/
theorem selfBound_of_potBound (W : MvPolynomial (Fin D) ℂ) {lam : ℝ}
    (hW : ∀ p : MvPolynomial (Fin D) ℂ, ‖pgLp (W * p)‖ ≤ lam * shiftNorm p)
    (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (W * p) + pgLp p‖ ≤ (lam + 1) * shiftNorm p := by
  refine (norm_add_le _ _).trans ?_
  have h1 := hW p
  have h2 := identityBound_harm p
  nlinarith [shiftNorm_nonneg p]

end

end BookProof.SmQuadraticWeightLemmas
