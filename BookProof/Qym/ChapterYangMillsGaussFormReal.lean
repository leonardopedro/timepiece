/-
# S0: the Friedrichs form of the Gaussian operator, over `ℝ`

`ChapterYangMillsFriedrichs` states Part B (the form `⟪x, y⟫_H = ⟪x, y⟫ + ⟪x, H y⟫`, its
expansions, Cauchy–Schwarz, and `form_closable`) for a **complex** Hilbert space, because its
deficiency-space Part A is complex.  `ChapterYangMillsGaussFormReal` already restates those
constructions for `[InnerProductSpace ℝ F]`, and `ChapterYangMillsGaussForm` proves the Gaussian
operator `gaussOp` on `L²(γ dx; ℝ)` is symmetric and positive.

This module is the join: the two hypotheses `ChapterYangMillsFriedrichsReal.form_closable` consumes,
discharged for `gaussOp`, and `form_closable` itself applied to it.  No complexification is on the
path — `gaussOp` is already an operator on a real Hilbert space, so the real forms apply to it
directly.  (`ChapterYangMillsGaussFormComplex` reaches the same conclusion through the `ℂ` lift;
that route stays, since the `ℂ` operator is what the deficiency analysis will consume.)

**What is proved here.**

* `gaussOp_symmetricOn_real` — `gaussOp` is symmetric in the real form sense, from the weighted
  integration by parts `gaussOp_inner_comm`;
* `gaussOp_quadForm_nonneg_real` — positivity `0 ≤ quadForm gaussOpLinearMap x`, from
  `gaussOp_inner_self_eq` and nonnegativity of the Dirichlet form;
* `gaussOp_form_closable_real` — the form of `gaussOp` is closable: a sequence that is Cauchy for
  the form norm and tends to `0` in `L²(γ dx)` has form norm tending to `0`.

This module is a leaf: nothing imports it except `BookProof`.  The import cycle forbids the reverse
placement — `ChapterYangMillsGaussForm` already imports `ChapterYangMillsFriedrichs` (through
Mehler, Abelian, Hermite and the Friedrichs extension chapters), so the instantiation cannot live in
either chapter and be imported by the other.
-/
import BookProof.Qym.ChapterYangMillsFriedrichs
import BookProof.Qym.ChapterYangMillsGaussForm

namespace BookProof.YangMillsFriedrichsReal

open MeasureTheory BookProof.YangMillsMehlerLp BookProof.YangMillsGaussForm
  BookProof.YangMillsMehlerBridge

/-- **`gaussOp` is symmetric in the real form sense.**  This is `gaussOp_inner_comm` read as
`SymmetricOn gaussCore gaussOpLinearMap`, which is exactly the hypothesis of `form_closable`. -/
theorem gaussOp_symmetricOn_real : SymmetricOn gaussCore gaussOpLinearMap :=
  fun f g => BookProof.YangMillsGaussForm.gaussOp_inner_comm f g

/-- **`gaussOp` is positive in the real form sense.**  `quadForm gaussOpLinearMap x` is
`⟪x, gaussOp x⟫` — no real part to take over `ℝ` — so this is `gaussOp_quadForm_nonneg`. -/
theorem gaussOp_quadForm_nonneg_real (f : gaussCore) : 0 ≤ quadForm gaussOpLinearMap f :=
  BookProof.YangMillsGaussForm.gaussOp_quadForm_nonneg f

/-- **The form of `gaussOp` is closable** — `form_closable` instantiated on the real Gaussian
operator, with no complexification anywhere in the statement or proof. -/
theorem gaussOp_form_closable_real (x : ℕ → gaussCore)
    (hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      formNormSq gaussOpLinearMap (x p - x q) < ε)
    (hzero : Filter.Tendsto (fun n => ((x n : Lp ℝ 2 gaussMeasure))) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => formNormSq gaussOpLinearMap (x n)) Filter.atTop (nhds 0) :=
  form_closable gaussOp_symmetricOn_real gaussOp_quadForm_nonneg_real x hCauchy hzero

end BookProof.YangMillsFriedrichsReal
