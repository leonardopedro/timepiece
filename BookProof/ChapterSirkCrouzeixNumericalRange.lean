import Mathlib
import BookProof.ChapterH4
import BookProof.ChapterNumericalRangeCrouzeix

/-!
# The SIRK error bound for general non-normal operators, with the Crouzeix hypothesis
discharged from the numerical range

`BookProof.ChapterH4` proves the SIRK convergence headline `sirk_error_bound`
*conditionally*: the two operator-norm bounds `‖ψ(X) − r(X)‖ ≤ C·D` (eq. 14 of the source)
are **named hypotheses**, standing for Crouzeix's inequality over a convex set containing
the numerical range.  `BookProof.ChapterCrouzeixSelfAdjoint` discharges them in the
*self-adjoint* (positive shift-invert) regime, with constant `C = 1`, and records the
honest boundary that for a **general non-normal** operator — numerical range, larger
constant — the bound was still assumed.

`BookProof.ChapterNumericalRangeCrouzeix` removes that boundary analytically: for an
operator whose numerical range lies in the closed disc of radius `r` and a power series
obeying Cauchy's estimate `‖aₙ‖ ≤ M/Rⁿ` on a strictly larger disc,
`crouzeix_disc` gives `‖f(A)‖ ≤ (1 + 2r/(R − r))·M` — Crouzeix's inequality for a general
operator, from the numerical range, with an explicit larger constant.

This file plugs the two together, so that the SIRK package no longer carries a Crouzeix
hypothesis in the non-normal regime either.

## Results

* `numRadiusLE_compress` — the numerical range of the Krylov compression `V∗XV` of `X`
  lies in the same disc as that of `X`: the Crouzeix domain is inherited by the reduced
  operator, with no extra assumption beyond isometry of `V`.
* `crouzeix_bound_of_numRadius` — the Crouzeix hypothesis of `ChapterH4.sirk_error_bound`
  in the form it is used there: if `ψ(X) − r(X)` is the analytic functional calculus
  `∑ aₙ Xⁿ` of a series with `‖aₙ‖ ≤ D/Rⁿ`, and the numerical range of `X` lies in the
  disc of radius `r < R`, then `‖ψ(X) − r(X)‖ ≤ (1 + 2r/(R − r))·D`.
* **`sirk_error_bound_numericalRange`** — the SIRK error bound of
  `ChapterH4.sirk_error_bound` for a **general non-normal** operator, with **no Crouzeix
  hypothesis**: only the numerical-range bound, the Cauchy estimate for the error series,
  the isometry of the Krylov embedding and the rational-transfer identity.
* `sirk_error_bound_numericalRange_compress` — the same with the reduced operator taken to
  be the compression `V∗XV`, whose numerical-range hypothesis is then automatic.
* `sirk_error_bound_numericalRange_decay` — the eq.-(12) form, with the `e^{−hm}` decay
  factor carried over from `ChapterH4.sirk_error_bound_decay`.
* `compress_sub_const`, `numBallLE_compress`, `sirk_error_bound_numericalBall` — the same
  package for a numerical range in a disc in *general position* (centre `c`), which is the
  Crouzeix domain that `ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvertC` produces
  for a shift-invert at a non-real shift.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace

namespace BookProof.ChapterSirkCrouzeixNumericalRange

open BookProof.ChapterNumericalRangeCrouzeix

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## The Crouzeix disc is inherited by the Krylov compression -/

/-- **The numerical range of a compression is no larger.**  If `V` is isometric and the
numerical range of `X` lies in the closed disc of radius `r`, then so does the numerical
range of the compression `V∗XV`. -/
theorem numRadiusLE_compress (V : F →L[ℂ] E) {X : E →L[ℂ] E} {r : ℝ}
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hX : NumRadiusLE X r) :
    NumRadiusLE (BookProof.ChapterH4.compress V X) r := by
  intro x
  have hinner : (⟪x, (BookProof.ChapterH4.compress V X) x⟫_ℂ) = ⟪V x, X (V x)⟫_ℂ := by
    simp only [BookProof.ChapterH4.compress, ContinuousLinearMap.comp_apply]
    exact ContinuousLinearMap.adjoint_inner_right V x (X (V x))
  rw [hinner, ← hViso x]
  exact hX (V x)

/-! ## The Crouzeix hypothesis, proved from the numerical range -/

/-- **The Crouzeix operator-norm bound used by SIRK, proved.**  If the error operator
`ψ(X) − r(X)` is the analytic functional calculus of a series obeying Cauchy's estimate
`‖aₙ‖ ≤ D/Rⁿ`, and the numerical range of `X` lies in the closed disc of radius `r < R`,
then `‖ψ(X) − r(X)‖ ≤ C·D` with the explicit Crouzeix constant `C = 1 + 2r/(R − r)`. -/
theorem crouzeix_bound_of_numRadius {X psiX rX : E →L[ℂ] E} {r D R : ℝ} {a : ℕ → ℂ}
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hR : r < R) (hX : NumRadiusLE X r)
    (ha : ∀ n, ‖a n‖ ≤ D / R ^ n) (hdiff : psiX - rX = analyticFC a X) :
    ‖psiX - rX‖ ≤ (1 + 2 * r / (R - r)) * D := by
  rw [hdiff]
  exact crouzeix_disc hr hD hR hX ha

/-! ## The SIRK error bound without any Crouzeix hypothesis -/

/-- **The SIRK error bound for a general (non-normal) operator, unconditional.**  This is
`ChapterH4.sirk_error_bound` with both Crouzeix hypotheses *proved* from the numerical
range: if the numerical ranges of `X` and of the reduced operator `B` lie in the closed
disc of radius `r`, and the error function `ψ − r` is given on the strictly larger disc of
radius `R` by a power series with `‖aₙ‖ ≤ D/Rⁿ`, then the SIRK approximation error obeys
`‖φ(A)v − V ψ(B) V∗v‖ ≤ 2·(1 + 2r/(R − r))·D·‖v‖`. -/
theorem sirk_error_bound_numericalRange
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    {X : E →L[ℂ] E} {B : F →L[ℂ] F} {r D R : ℝ} {a : ℕ → ℂ}
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hR : r < R)
    (hX : NumRadiusLE X r) (hB : NumRadiusLE B r)
    (ha : ∀ n, ‖a n‖ ≤ D / R ^ n)
    (hdiffX : psiX - rX = analyticFC a X)
    (hdiffB : psiB - rB = analyticFC a B)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, rX v = V (rB (V.adjoint v)))
    (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖ ≤ 2 * (1 + 2 * r / (R - r)) * D * ‖v‖ :=
  BookProof.ChapterH4.sirk_error_bound V phiA psiX rX psiB rB (1 + 2 * r / (R - r)) D
    hphi hViso hVadj hrt
    (crouzeix_bound_of_numRadius hr hD hR hX ha hdiffX)
    (crouzeix_bound_of_numRadius hr hD hR hB ha hdiffB) v

/-- The SIRK error bound for a general operator when the reduced operator is the Krylov
compression `V∗XV`: the numerical-range hypothesis on the reduced side is then automatic
(`numRadiusLE_compress`), so the only spectral input is the numerical range of `X`. -/
theorem sirk_error_bound_numericalRange_compress
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    {X : E →L[ℂ] E} {r D R : ℝ} {a : ℕ → ℂ}
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hR : r < R)
    (hX : NumRadiusLE X r)
    (ha : ∀ n, ‖a n‖ ≤ D / R ^ n)
    (hdiffX : psiX - rX = analyticFC a X)
    (hdiffB : psiB - rB = analyticFC a (BookProof.ChapterH4.compress V X))
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, rX v = V (rB (V.adjoint v)))
    (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖ ≤ 2 * (1 + 2 * r / (R - r)) * D * ‖v‖ :=
  sirk_error_bound_numericalRange V phiA psiX rX psiB rB hr hD hR hX
    (numRadiusLE_compress V hViso hX) ha hdiffX hdiffB hphi hViso hVadj hrt v

/-- The eq.-(12) form: the unconditional general-operator SIRK bound together with the
`e^{−hm}` decay of the error size `D`. -/
theorem sirk_error_bound_numericalRange_decay
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    {X : E →L[ℂ] E} {B : F →L[ℂ] F} {r D R Dmin h m : ℝ} {a : ℕ → ℂ}
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hR : r < R)
    (hX : NumRadiusLE X r) (hB : NumRadiusLE B r)
    (ha : ∀ n, ‖a n‖ ≤ D / R ^ n)
    (hdiffX : psiX - rX = analyticFC a X)
    (hdiffB : psiB - rB = analyticFC a B)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, rX v = V (rB (V.adjoint v)))
    (hdecay : D ≤ Real.exp (-(h * m)) * Dmin)
    (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖
      ≤ 2 * (1 + 2 * r / (R - r)) * Real.exp (-(h * m)) * Dmin * ‖v‖ := by
  have hC : (0 : ℝ) ≤ 1 + 2 * r / (R - r) := by
    have hRr : (0 : ℝ) < R - r := by linarith
    positivity
  exact BookProof.ChapterH4.sirk_error_bound_decay V phiA psiX rX psiB rB
    (1 + 2 * r / (R - r)) D Dmin h m hphi hViso hVadj hrt
    (crouzeix_bound_of_numRadius hr hD hR hX ha hdiffX)
    (crouzeix_bound_of_numRadius hr hD hR hB ha hdiffB) hC hdecay v

/-! ## The same over a disc in general position -/

/-- The compression of the shifted operator is the shift of the compression, when `V` is an
isometric embedding with `V∗V = 1`. -/
theorem compress_sub_const (V : F →L[ℂ] E) (X : E →L[ℂ] E) (c : ℂ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    BookProof.ChapterH4.compress V (X - c • (1 : E →L[ℂ] E))
      = BookProof.ChapterH4.compress V X - c • (1 : F →L[ℂ] F) := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hVVx : V.adjoint (V x) = x := by
    simpa using congrArg (fun T : F →L[ℂ] F => T x) hVV
  simp only [BookProof.ChapterH4.compress, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, map_sub, map_smul, hVVx]

/-- **The Crouzeix disc in general position is inherited by the Krylov compression.** -/
theorem numBallLE_compress (V : F →L[ℂ] E) {X : E →L[ℂ] E} {c : ℂ} {r : ℝ}
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (hX : NumBallLE X c r) :
    NumBallLE (BookProof.ChapterH4.compress V X) c r := by
  have h := numRadiusLE_compress V hViso hX
  rwa [compress_sub_const V X c hVV] at h

/-- **The SIRK error bound for a general non-normal operator whose numerical range lies in
a disc in general position**, with no Crouzeix hypothesis: the error function is expanded
about the centre `c` of the disc. -/
theorem sirk_error_bound_numericalBall
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    {X : E →L[ℂ] E} {B : F →L[ℂ] F} {c : ℂ} {r D R : ℝ} {a : ℕ → ℂ}
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hR : r < R)
    (hX : NumBallLE X c r) (hB : NumBallLE B c r)
    (ha : ∀ n, ‖a n‖ ≤ D / R ^ n)
    (hdiffX : psiX - rX = analyticFC a (X - c • (1 : E →L[ℂ] E)))
    (hdiffB : psiB - rB = analyticFC a (B - c • (1 : F →L[ℂ] F)))
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hrt : ∀ v : E, rX v = V (rB (V.adjoint v)))
    (v : E) :
    ‖phiA v - V (psiB (V.adjoint v))‖ ≤ 2 * (1 + 2 * r / (R - r)) * D * ‖v‖ :=
  sirk_error_bound_numericalRange V phiA psiX rX psiB rB hr hD hR hX hB ha hdiffX hdiffB
    hphi hViso hVadj hrt v

end BookProof.ChapterSirkCrouzeixNumericalRange
