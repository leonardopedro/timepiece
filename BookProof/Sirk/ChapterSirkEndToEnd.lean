import Mathlib
import BookProof.Textbook.ChapterH4
import BookProof.Textbook.ChapterH6
import BookProof.Textbook.ChapterH7
import BookProof.Textbook.ChapterH8
import BookProof.Textbook.ChapterH9
import BookProof.Sirk.ChapterRitzCertificate

/-!
# Chapter SirkEndToEnd — the end-to-end SIRK reliability statement (assembly)

`CONSOLIDATED_PLAN.md` §12.2 **Gap 1** records that the four stages of the
SIRK/Hashimoto pipeline exist as separate modules but that *no theorem composes
them* into a single flow-approximation statement

  `‖e^{−itH} v − V_m e^{−itB_m} V_m∗ v‖ ≤ bound(m, shifts, t, spectral geometry)`,

and §12.3 names this "the highest-value, lowest-risk step: it does not touch any
physics".  This chapter is that assembly, on the generic machinery, with the
constants `C`, `Dmin`, `h` abstract.

## What is new here (as opposed to restated)

* `sirk_error_bound_at` **weakens** the compression-transfer hypothesis of
  `ChapterH4.sirk_error_bound` from "for every vector" to "at the one seed
  vector `v`".  That is what makes the composition possible at all: the rational
  transfer `r(X) v = V r(B) V∗ v` of `ChapterH4.compress_rational_transfer` is
  only available **on the range of `V`**, which is exactly where the Krylov seed
  lives.
* `sirk_end_to_end` therefore has **no `hrt` hypothesis left**: the transfer is
  discharged from the isometry, the Krylov invariance of the range and the
  invertibility of the rational denominator.  What remains conditional is only
  the pair of Crouzeix bounds and the `e^{−hm}` deformation — the two inputs the
  project has always carried as *named hypotheses with citation*, never axioms.
* `crouzeix_domain_transfer` shows that **one** Crouzeix domain serves both
  bounds: if `Σ` is convex and contains the numerical range of `X`, it contains
  the convex hull of the numerical range of every compression `B = V∗XV`
  (`ChapterH9.numRange_compress_subset`).  So `hcx1` and `hcx2` may be taken with
  the *same* `C` and the *same* `D = ‖ψ − r‖_{∞,Σ}`, which is what the informal
  argument silently uses.
* `sirk_flow_error_tendsto_zero` and `sirk_flow_error_uniform_in_time` are the
  convergence conclusions: the reduced flows converge to the exact one as the
  Krylov dimension grows, and — when the constants do not depend on the time —
  the convergence is **uniform in `t`** (the bound half of §12.2 Gap 3).
* `sirk_error_opNorm_le` and `sirk_opNorm_error_tendsto_zero` are the bound in its
  **maximum-error** form: the supremum over unit vectors gives
  `‖flow − sirkApprox V psiB‖ ≤ sirkBound C Dmin h 1 m`, and that worst-case
  error vanishes in the reduction order.  A residual certificate needs the norm
  bound, not the estimate at one seed.
* `sirk_ritz_resid_le` is the seam that makes both bounds *usable*: a reduced
  eigenpair `psiB y = μ y` with `‖y‖ = 1` reconstructs to `V y`, and its residual
  for `X` is bounded by the operator-norm error,
  `resid X (V y) ≤ ‖X − sirkApprox V psiB‖`, with **no factor 2** —
  `resid_le_norm_sub_smul` records the geometric reason (the Rayleigh quotient of
  `V y` is the best approximation of `X (V y)` by multiples of `V y`).  That turns
  `ChapterRitzCertificate.temple_lower_bound` into a certificate for the SIRK
  output, which is what `softmodes.md` S3.1 asks for.
* `sirkApprox_id`, `sirkReconstruction_isIdempotent`,
  `sirkReconstruction_isSelfAdjoint`: the reconstruction step `V ∘ V∗` *is* the
  orthogonal projection onto the retained subspace (§12.2 Gap 4a).
* `sirk_block_error_eq_correction` supplies the piece `softmodes.md` U2 says the
  block estimate still needs: `V∗ R V` is *not* `(V∗(H − z)V)⁻¹`, and the identity
  `V∗ R V − B = −B·V∗((H − z)Q R V)` says the difference is exactly the leakage,
  transported by `B`.  `sirk_block_error_le_of_inverse` reads it as the number
  `‖B‖‖(H − z)Q‖‖R P‖`, and `sirk_fullSpace_error_le_shiftInvert` puts that number
  into the §8 estimate, so no term of the composed bound refers to `V∗ R V`.
* `sirk_error_le_budget` is U2's envelope with all four allocations attached to
  proved quantities: `T = sirkTailBudget` (leakage plus tail), `O =
  sirkTransferBudget` (the compressed-inverse correction above), `S =
  sirkSolveBudget m ε = ε` — `m` columns of norm `ε/√m` have Frobenius mass `ε²`
  (`solve_columns_budget`) — and `F` the caller's rounding budget.  The
  `2 C̄ D̄ e^{−a q_m}` rational term is not claimed; it belongs to approximating
  `R_g` itself.
* `sirk_fullSpace_error_le` prices the space a generic Krylov basis leaves
  behind.  With `P = V V∗`, `Q = 1 − P` it proves
  `‖R − V B V∗‖ ≤ ‖V∗RV − B‖ + 2‖Q R P‖ + ‖Q R Q‖`, so the exact-invariance
  premise of `sirk_end_to_end` is replaced by two numbers (leakage and tail)
  rather than assumed.  `sirk_offblock_norm_eq` explains the single factor `2`:
  for self-adjoint `R` the corners `P R Q` and `Q R P` are adjoints, hence have
  equal norms — no `m`-dependent entrywise summation.

## Honest boundary

Nothing here proves Crouzeix's inequality or the `e^{−hm}` deformation; they
enter as named hypotheses exactly as in `ChapterH4`.  Nothing here instantiates
the constants for a particular Hamiltonian (§12.2 Gap 2), and nothing is claimed
about floating-point arithmetic (§12.2 Gap 6).  What is proved is the
*composition*: from the two named inputs, the isometry and the Krylov
invariance, the end-to-end bound and its convergence follow.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open Filter Topology

namespace BookProof.ChapterSirkEndToEnd

open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. The SIRK approximant and the reconstruction projection -/

/-- The **SIRK approximant** `V ψ(B) V∗`: reduce with `V∗`, propagate with the
`m × m` reduced operator `ψ(B)`, reconstruct with `V`. -/
def sirkApprox (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) : E →L[ℂ] E :=
  V.comp (psiB.comp V.adjoint)

@[simp] theorem sirkApprox_apply (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (v : E) :
    sirkApprox V psiB v = V (psiB (V.adjoint v)) := rfl

/-- The **reconstruction operator** `V ∘ V∗`. -/
def sirkReconstruction (V : F →L[ℂ] E) : E →L[ℂ] E := V.comp V.adjoint

/-- With no propagation at all the SIRK approximant is the reconstruction
operator. -/
theorem sirkApprox_id (V : F →L[ℂ] E) :
    sirkApprox V (ContinuousLinearMap.id ℂ F) = sirkReconstruction V := rfl

/-- **Reconstruction is a projection (§12.2 Gap 4a).**  For an isometric
embedding, `V ∘ V∗` is idempotent. -/
theorem sirkReconstruction_isIdempotent (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    (sirkReconstruction V).comp (sirkReconstruction V) = sirkReconstruction V := by
  ext v
  have h : V.adjoint (V (V.adjoint v)) = V.adjoint v :=
    congrArg (fun f : F →L[ℂ] F => f (V.adjoint v)) hVV
  simp [sirkReconstruction, h]

/-- **Reconstruction is self-adjoint**, so `V ∘ V∗` is the *orthogonal*
projection onto the retained subspace. -/
theorem sirkReconstruction_isSelfAdjoint (V : F →L[ℂ] E) :
    IsSelfAdjoint (sirkReconstruction V) := by
  change ContinuousLinearMap.adjoint (V.comp V.adjoint) = V.comp V.adjoint
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

/-- The SIRK approximant never amplifies more than the reduced propagator does. -/
theorem norm_sirkApprox_apply_le (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) (v : E) :
    ‖sirkApprox V psiB v‖ ≤ ‖psiB‖ * ‖v‖ := by
  rw [sirkApprox_apply, hViso]
  exact le_trans (psiB.le_opNorm _)
    (mul_le_mul_of_nonneg_left (hVadj v) (norm_nonneg _))

/-- If the reduced propagator is an isometry — the case of a Hermitian reduced
generator, `ChapterH7.generationOperator_mem_unitaryGroup` — the SIRK approximant
is a contraction, so the scheme cannot manufacture norm. -/
theorem norm_sirkApprox_apply_le_of_isometry (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hpsi : ∀ y : F, ‖psiB y‖ = ‖y‖) (v : E) :
    ‖sirkApprox V psiB v‖ ≤ ‖v‖ := by
  rw [sirkApprox_apply, hViso, hpsi]
  exact hVadj v

/-! ## 2. The pointwise Crouzeix core -/

/-- **The SIRK error bound with the transfer hypothesis at the seed only.**
`ChapterH4.sirk_error_bound` asks for `r(X) = V r(B) V∗` as an operator
identity; the rational transfer only holds on the range of `V`.  The proof uses
the identity at the single vector `v`, so this is the form that composes. -/
theorem sirk_error_bound_at
    (V : F →L[ℂ] E) (phiA psiX rX : E →L[ℂ] E) (psiB rB : F →L[ℂ] F)
    (C D : ℝ)
    (hphi : phiA = psiX)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hcx1 : ‖psiX - rX‖ ≤ C * D)
    (hcx2 : ‖psiB - rB‖ ≤ C * D)
    (v : E) (hrt : rX v = V (rB (V.adjoint v))) :
    ‖phiA v - sirkApprox V psiB v‖ ≤ 2 * C * D * ‖v‖ := by
  have hCD : 0 ≤ C * D := le_trans (norm_nonneg _) hcx2
  have key : phiA v - sirkApprox V psiB v
      = (psiX - rX) v + V ((rB - psiB) (V.adjoint v)) := by
    have h1 : V ((rB - psiB) (V.adjoint v))
        = V (rB (V.adjoint v)) - V (psiB (V.adjoint v)) := by
      rw [ContinuousLinearMap.sub_apply, map_sub]
    rw [h1, ContinuousLinearMap.sub_apply, ← hrt, hphi, sirkApprox_apply]
    abel
  rw [key]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(psiX - rX) v‖ ≤ C * D * ‖v‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right hcx1 (norm_nonneg _))
  have h2 : ‖V ((rB - psiB) (V.adjoint v))‖ ≤ C * D * ‖v‖ := by
    rw [hViso]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    exact mul_le_mul (by simpa only [norm_sub_rev] using hcx2) (hVadj v) (norm_nonneg _) hCD
  linarith

/-! ## 3. One Crouzeix domain for both bounds -/

/-- **The Crouzeix domain transfers to the compression.**  If `Σ` is convex and
contains the numerical range of `X`, it contains the convex hull of the
numerical range of the compression `B = V∗XV`.  Consequently a single Crouzeix
constant `C` and a single sup-norm `D = ‖ψ − r‖_{∞,Σ}` bound *both*
`‖ψ(X) − r(X)‖` and `‖ψ(B) − r(B)‖`, which is what `sirk_error_bound_at` needs. -/
theorem crouzeix_domain_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S)
    (hS : numRange X ⊆ S) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ S :=
  convexHull_min ((numRange_compress_subset V X hViso).trans hS) hconv

/-- The unconditional form: the numerical range of every compression sits inside
the closed disc of radius `‖X‖`, uniformly in the reduction order. -/
theorem crouzeix_domain_uniform (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) ‖X‖ :=
  crouzeix_domain_transfer V X hViso _ (convex_closedBall _ _)
    (numRange_subset_closedBall X)

/-! ## 4. The end-to-end bound -/

/-- **The end-to-end SIRK reliability bound (§12.2 Gap 1).**

`flow` is the exact propagator, assumed (`hflow`) to be the value `ψ_{k,γ}(X)` of
the shift-invert functional calculus — this is `ChapterH4.psi_shift_eq_phi`, the
spectral consistency of Definition 2.4.  `r = p/q` is the rational approximant,
`V` the isometric Krylov embedding, `B = V∗XV` the reduced generator of eq. (10),
and the reduced propagator is `psiB`.  The two Crouzeix bounds and the `e^{−hm}`
deformation are folded into `hcx1`/`hcx2` on the *common* domain of
`crouzeix_domain_transfer`.

The transfer identity `r(X)v = V r(B) V∗v` is **not** a hypothesis: it is
discharged from the isometry (`hVV`), the Krylov invariance of the range
(`hinvX`, `hinvq`) and the invertibility of the denominator (`hqXl`, `hqBr`),
via `ChapterH4.compress_rational_transfer`.

The conclusion is the eq.-(12) bound in the explicit form of
`ChapterH6.sirkBound`. -/
theorem sirk_end_to_end
    (V : F →L[ℂ] E) (X qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F) (p : Polynomial ℂ)
    (flow psiX : E →L[ℂ] E) (psiB : F →L[ℂ] F)
    (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (hinvq : ∀ x : F, ∃ y : F, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F)
    (hflow : flow = psiX)
    (hcx1 : ‖psiX - (Polynomial.aeval X p).comp qXinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - (Polynomial.aeval (compress V X) p).comp qBinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by
  have hrt : ((Polynomial.aeval X p).comp qXinv) v
      = V (((Polynomial.aeval (compress V X) p).comp qBinv) (V.adjoint v)) := by
    simpa using
      compress_rational_transfer V X qX qXinv qBinv p hVV hinvX hinvq hqXl hqBr v hv
  have := sirk_error_bound_at V flow psiX ((Polynomial.aeval X p).comp qXinv)
    psiB ((Polynomial.aeval (compress V X) p).comp qBinv)
    C (Real.exp (-(h * m)) * Dmin) hflow hViso hVadj hcx1 hcx2 v hrt
  simpa [sirkBound, mul_assoc] using this

/-! ## 5. Convergence in the reduction order, and uniformity in time -/

/-- A nonnegative error dominated by the SIRK bound tends to `0`. -/
theorem tendsto_zero_of_le_sirkBound (err : ℕ → ℝ) (C Dmin h nv : ℝ) (hh : 0 < h)
    (hnn : ∀ m, 0 ≤ err m) (hle : ∀ m, err m ≤ sirkBound C Dmin h nv m) :
    Tendsto err atTop (𝓝 0) :=
  squeeze_zero hnn hle (sirk_error_decay_exponential C Dmin h nv hh)

/-- **Convergence of the SIRK flow approximation (§12.2 Gap 1).**  If at every
reduction order `m` the end-to-end bound holds with the *same* constants, the
reduced flows converge to the exact flow at the seed. -/
theorem sirk_flow_error_tendsto_zero
    {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
    [∀ m, CompleteSpace (G m)]
    (flow : E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, G m →L[ℂ] G m)
    (C Dmin h : ℝ) (hh : 0 < h) (v : E)
    (hbound : ∀ m, ‖flow v - sirkApprox (V m) (psiB m) v‖ ≤ sirkBound C Dmin h ‖v‖ m) :
    Tendsto (fun m => ‖flow v - sirkApprox (V m) (psiB m) v‖) atTop (𝓝 0) :=
  tendsto_zero_of_le_sirkBound _ C Dmin h ‖v‖ hh (fun _ => norm_nonneg _) hbound

/-- **The SIRK bound is a bound on the maximum error, not on one seed's error.**
`sirk_end_to_end` estimates `‖flow v - sirkApprox V psiB v‖` at a single seed
`v`.  Taking the supremum over the unit sphere turns that pointwise estimate into
an operator-norm estimate on `flow - sirkApprox V psiB`: the largest error over
*every* state in the Krylov space is bounded by the same `sirkBound`, evaluated at
`nv = 1`.  This is the form a spectral certificate consumes — a residual bound
has to hold for the vector it is given, not only for the seed it was built from. -/
theorem sirk_error_opNorm_le (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (flow : E →L[ℂ] E)
    (C Dmin h : ℝ) (m : ℕ) (hC : 0 ≤ C) (hD : 0 ≤ Dmin)
    (hpoint : ∀ v : E, ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m) :
    ‖flow - sirkApprox V psiB‖ ≤ sirkBound C Dmin h 1 m := by
  have hB : 0 ≤ sirkBound C Dmin h 1 m := by
    rw [sirkBound]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
        (le_of_lt (Real.exp_pos _))) hD) (by norm_num)
  refine ContinuousLinearMap.opNorm_le_bound _ hB fun v => ?_
  rw [ContinuousLinearMap.sub_apply]
  calc ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := hpoint v
    _ = sirkBound C Dmin h 1 m * ‖v‖ := by
      simp only [sirkBound]
      ring

/-- **The maximum error tends to zero in the reduction order.**  The operator-norm
form of `sirk_flow_error_tendsto_zero`: if the end-to-end bound holds at every
order with the *same* constants, the worst-case error over the whole space — not
merely the error at the seed — vanishes like `e^{-hm}`.  A spectral certificate at
a finite order therefore only needs the same three constants the pointwise bound
already needs. -/
theorem sirk_opNorm_error_tendsto_zero
    {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
    [∀ m, CompleteSpace (G m)]
    (flow : E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, G m →L[ℂ] G m)
    (C Dmin h : ℝ) (hh : 0 < h)
    (hbound : ∀ m, ‖flow - sirkApprox (V m) (psiB m)‖ ≤ sirkBound C Dmin h 1 m) :
    Tendsto (fun m => ‖flow - sirkApprox (V m) (psiB m)‖) atTop (𝓝 0) :=
  tendsto_zero_of_le_sirkBound _ C Dmin h 1 hh (fun _ => norm_nonneg _) hbound

/-- **Uniformity in time (§12.2 Gap 3, the bound half).**  If the SIRK constants
`C`, `Dmin`, `h` can be chosen independently of the time, then the convergence of
the reduced flow to the exact flow is uniform over the whole time axis. -/
theorem sirk_flow_error_uniform_in_time
    {G : ℕ → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, InnerProductSpace ℂ (G m)]
    [∀ m, CompleteSpace (G m)]
    (flow : ℝ → E →L[ℂ] E) (V : ∀ m, G m →L[ℂ] E) (psiB : ∀ m, ℝ → G m →L[ℂ] G m)
    (C Dmin h : ℝ) (hh : 0 < h) (v : E)
    (hbound : ∀ (t : ℝ) (m : ℕ),
      ‖flow t v - sirkApprox (V m) (psiB m t) v‖ ≤ sirkBound C Dmin h ‖v‖ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ t : ℝ, ‖flow t v - sirkApprox (V m) (psiB m t) v‖ < ε := by
  have hb := sirk_error_tendsto_zero C Dmin h ‖v‖ hh hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 hb
  refine ⟨M, fun m hm t => ?_⟩
  exact lt_of_le_of_lt (hbound t m) (lt_of_abs_lt (hM m hm))


/-! ## 7. The residual seam: the operator-norm bound is a Ritz residual -/

/-- **A residual is bounded by the distance to any multiple of a unit vector.**

`RitzCertificate.resid A x` is the distance from `A x` to the *line* spanned by
`x`.  For self-adjoint `A` and `‖x‖ = 1` that distance is no larger than
`‖A x − c x‖` for **any** real `c`, even though `resid` measures against the
Rayleigh quotient of `x` rather than against `c`.  This is what lets an error
bound on `A − B` be used as an eigenvector residual: it does not matter that the
Rayleigh quotient of `x` for `A` differs from the eigenvalue `B` gives `x`. -/
theorem resid_le_norm_sub_smul {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {x : E}
    (hx : ‖x‖ = 1) (c : ℝ) :
    BookProof.RitzCertificate.resid A x ≤ ‖A x - (c : ℂ) • x‖ := by
  set th := BookProof.RitzCertificate.rayleigh A x with hth
  have hself : (inner ℂ x (A x) : ℂ) = (inner ℂ (A x) x : ℂ) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hA.adjoint_eq]
  have hz : (inner ℂ (A x) x : ℂ) = (th : ℂ) := by
    have hc : (inner ℂ (A x) x : ℂ) = (starRingEnd ℂ) (inner ℂ (A x) x : ℂ) := by
      calc (inner ℂ (A x) x : ℂ) = (inner ℂ x (A x) : ℂ) := hself.symm
        _ = (starRingEnd ℂ) (inner ℂ (A x) x : ℂ) := by
          rw [inner_conj_symm]
    have him : (inner ℂ (A x) x : ℂ).im = 0 := by
      have h := congrArg Complex.im hc
      rw [Complex.conj_im] at h
      linarith
    have hre : (((inner ℂ (A x) x : ℂ).re : ℝ) : ℂ) = (inner ℂ (A x) x : ℂ) := by
      have h := Complex.re_add_im (inner ℂ (A x) x : ℂ)
      rw [him] at h
      simpa using h
    rw [← hre, hth, BookProof.RitzCertificate.rayleigh, ← hself]
  have hsq : ∀ d : ℝ, ‖A x - (d : ℂ) • x‖ ^ 2 = ‖A x‖ ^ 2 - 2 * d * th + d ^ 2 := by
    intro d
    rw [@norm_sub_sq ℂ E _ _ _ (A x) ((d : ℂ) • x), inner_smul_right, norm_smul, hx, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, hz]
    rw [← Complex.ofReal_mul]
    simp
    ring
  have hkey : ‖A x - (th : ℂ) • x‖ ^ 2 ≤ ‖A x - (c : ℂ) • x‖ ^ 2 := by
    rw [hsq th, hsq c]
    nlinarith [sq_nonneg (c - th)]
  have h1 : 0 ≤ ‖A x - (th : ℂ) • x‖ := norm_nonneg _
  have h2 : 0 ≤ ‖A x - (c : ℂ) • x‖ := norm_nonneg _
  rw [BookProof.RitzCertificate.resid, ← hth]
  calc ‖A x - (th : ℂ) • x‖
      = Real.sqrt (‖A x - (th : ℂ) • x‖ ^ 2) := (Real.sqrt_sq h1).symm
    _ ≤ Real.sqrt (‖A x - (c : ℂ) • x‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖A x - (c : ℂ) • x‖ := Real.sqrt_sq h2

/-- **The residual seam (`sirk_ritz_resid_le`).**

A reduced eigenpair `psiB y = μ y` of the Galerkin matrix, with `y` a unit vector
and `V` isometric (`V∗ V = 1`), reconstructs to `V y`, whose `X`-Rayleigh
quotient is irrelevant: only `sirkApprox V psiB (V y) = μ (V y)` matters.  Hence

`resid X (V y) ≤ ‖X − sirkApprox V psiB‖ ≤ ε_m`,

so the *operator-norm* SIRK error of `sirk_error_opNorm_le` is a genuine Ritz
residual — the input `ChapterRitzCertificate.temple_lower_bound` consumes.  Both
inequalities are sharp in the sense that the first is an identity on the
retained subspace: no factor `2` is lost. -/
theorem sirk_ritz_resid_le (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (X : E →L[ℂ] E)
    (C Dmin h : ℝ) (m : ℕ) (mu : ℝ) (y : F)
    (hX : IsSelfAdjoint X)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (heig : psiB y = (mu : ℂ) • y) (hy : ‖V y‖ = 1)
    (hbound : ‖X - sirkApprox V psiB‖ ≤ sirkBound C Dmin h 1 m) :
    BookProof.RitzCertificate.resid X (V y) ≤ sirkBound C Dmin h 1 m := by
  have hAy : sirkApprox V psiB (V y) = (mu : ℂ) • (V y) := by
    have h1 : V.adjoint (V y) = y := by
      have h := congrArg (fun f : F →L[ℂ] F => f y) hVV
      simpa using h
    rw [sirkApprox_apply, h1, heig, map_smul]
  have hstep : ‖X (V y) - (mu : ℂ) • (V y)‖ ≤ sirkBound C Dmin h 1 m := by
    have h := ContinuousLinearMap.le_opNorm (X - sirkApprox V psiB) (V y)
    rw [hy, mul_one] at h
    refine le_trans ?_ (le_trans h hbound)
    rw [ContinuousLinearMap.sub_apply, hAy]
  exact le_trans (resid_le_norm_sub_smul hX hy mu) hstep
/-! ## 6. Non-vacuity -/

/-- **The hypothesis set of `sirk_end_to_end` is satisfiable with a nonzero
generator.**  Take the trivial rational approximant `r = X` (numerator the
polynomial `X`, denominator `1`): then the reduced propagator is the compression
itself and the end-to-end bound holds — indeed with error `0`, since on the
retained subspace the compression reproduces the generator exactly
(`ChapterH4.compress_transfer`). -/
theorem sirk_end_to_end_satisfiable
    (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : F, ∃ y : F, X (V x) = V y)
    (m : ℕ) (v : E) (hv : V (V.adjoint v) = v) :
    ‖X v - sirkApprox V (compress V X) v‖ ≤ sirkBound 1 1 1 ‖v‖ m := by
  refine sirk_end_to_end V X (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ E)
    (ContinuousLinearMap.id ℂ F) (Polynomial.X : Polynomial ℂ) X X (compress V X) 1 1 1 m
    hVV hViso hVadj hinvX (fun x => ⟨x, rfl⟩) (by ext x; simp) ?_ rfl ?_ ?_ v hv
  · have hcid : compress V (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ F := by
      ext x; simpa using congrArg (fun f : F →L[ℂ] F => f x) hVV
    rw [hcid]; ext x; simp
  · have : (Polynomial.aeval X (Polynomial.X : Polynomial ℂ) : E →L[ℂ] E).comp
        (ContinuousLinearMap.id ℂ E) = X := by ext x; simp
    rw [this, sub_self, norm_zero]
    positivity
  · have : (Polynomial.aeval (compress V X) (Polynomial.X : Polynomial ℂ) : F →L[ℂ] F).comp
        (ContinuousLinearMap.id ℂ F) = compress V X := by ext x; simp
    rw [this, sub_self, norm_zero]
    positivity


/-! ## 8. The full-space error: leakage and tail, priced rather than assumed -/

/-- The **complementary projection** `Q = 1 − V V∗`.

`softmodes.md` U2 asks for the estimate that exact Krylov invariance supplies for
free.  `Q` is the part of the ambient space the reconstruction discards, so the
two off-block pieces below are literally what invariance would have set to zero. -/
def sirkComplement (V : F →L[ℂ] E) : E →L[ℂ] E :=
  1 - sirkReconstruction V

@[simp] theorem sirkComplement_apply (V : F →L[ℂ] E) (v : E) :
    sirkComplement V v = v - sirkReconstruction V v := rfl

/-- `Q` is self-adjoint, being `1` minus the self-adjoint reconstruction. -/
theorem sirkComplement_isSelfAdjoint (V : F →L[ℂ] E) :
    IsSelfAdjoint (sirkComplement V) := by
  rw [IsSelfAdjoint, sirkComplement, star_sub, star_one,
    (sirkReconstruction_isSelfAdjoint V)]

/-- **Splitting a vector costs nothing.**  `P y + Q y = y` for `P = V V∗` and
`Q = 1 − P`: the two blocks are complementary projections. -/
theorem sirkReconstruction_add_complement (V : F →L[ℂ] E) (y : E) :
    sirkReconstruction V y + sirkComplement V y = y := by
  simp [sirkComplement]

/-- **The leakage is the tail.**  For self-adjoint `R` the two off-block corners
`P R Q` and `Q R P` are adjoints of one another, hence have equal operator norms.
This is what turns `‖P R Q‖ + ‖Q R P‖` into `2 ‖Q R P‖` — the factor `2` of the
full-space bound, rather than a separate norm for each corner. -/
theorem sirk_offblock_norm_eq (V : F →L[ℂ] E) {R : E →L[ℂ] E} (hR : IsSelfAdjoint R) :
    ‖(sirkReconstruction V).comp (R.comp (sirkComplement V))‖
      = ‖(sirkComplement V).comp (R.comp (sirkReconstruction V))‖ := by
  have hP := sirkReconstruction_isSelfAdjoint V
  have hQ := sirkComplement_isSelfAdjoint V
  have hstar : star ((sirkComplement V).comp (R.comp (sirkReconstruction V)))
      = (sirkReconstruction V).comp (R.comp (sirkComplement V)) := by
    change ContinuousLinearMap.adjoint
        ((sirkComplement V).comp (R.comp (sirkReconstruction V)))
      = (sirkReconstruction V).comp (R.comp (sirkComplement V))
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
    rw [← ContinuousLinearMap.star_eq_adjoint (sirkReconstruction V),
      ← ContinuousLinearMap.star_eq_adjoint R,
      ← ContinuousLinearMap.star_eq_adjoint (sirkComplement V), hP, hR, hQ]
    rfl
  rw [← hstar]
  simp

/-- **The full-space SIRK error, with the omitted space priced.**

For an isometric `V`, a self-adjoint `R` and any reduced `B`,

  `‖R − V B V∗‖ ≤ ‖V∗ R V − B‖ + 2 ‖Q R P‖ + ‖Q R Q‖`,

with `P = V V∗` and `Q = 1 − P`.  The first term is the reduced block error, the
middle the *leakage* (mass the retained block lets out of `ran V`) and the last
the *tail* on the omitted space.  Exact invariance of `ran V` would kill both
off-block terms; this inequality is what replaces that hypothesis — which
`sirk_end_to_end` cannot justify for a generic Krylov space — by two numbers.
No left inverse `V∗ V = 1` is assumed: the estimate is purely about the split
`x = P x + Q x` and the isometry of `V`. -/
theorem sirk_fullSpace_error_le (V : F →L[ℂ] E) (B : F →L[ℂ] F) {R : E →L[ℂ] E}
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hR : IsSelfAdjoint R) :
    ‖R - sirkApprox V B‖ ≤ ‖V.adjoint.comp (R.comp V) - B‖
      + 2 * ‖(sirkComplement V).comp (R.comp (sirkReconstruction V))‖
      + ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖ := by
  set P : E →L[ℂ] E := sirkReconstruction V with hP
  set Q : E →L[ℂ] E := sirkComplement V with hQ
  have hsplit : ∀ y : E, P y + Q y = y := fun y => by
    rw [hP, hQ]; exact sirkReconstruction_add_complement V y
  have hkey : ∀ x : E, (R - sirkApprox V B) x
      = V ((V.adjoint.comp (R.comp V) - B) (V.adjoint x))
        + P (R (Q x)) + Q (R (P x)) + Q (R (Q x)) := by
    intro x
    have hfirst : V ((V.adjoint.comp (R.comp V) - B) (V.adjoint x))
        = P (R (P x)) - V (B (V.adjoint x)) := by
      rw [ContinuousLinearMap.sub_apply, map_sub]
      simp [hP, sirkReconstruction]
    have hRx : R x = (P (R (P x)) + P (R (Q x))) + (Q (R (P x)) + Q (R (Q x))) := by
      have h1 : R x = R (P x) + R (Q x) := by rw [← map_add, hsplit]
      have h2 : R (P x) = P (R (P x)) + Q (R (P x)) := (hsplit (R (P x))).symm
      have h3 : R (Q x) = P (R (Q x)) + Q (R (Q x)) := (hsplit (R (Q x))).symm
      calc R x = R (P x) + R (Q x) := h1
        _ = (P (R (P x)) + Q (R (P x))) + (P (R (Q x)) + Q (R (Q x))) := by
          conv_lhs => rw [h2, h3]
        _ = (P (R (P x)) + P (R (Q x))) + (Q (R (P x)) + Q (R (Q x))) := by abel
    rw [ContinuousLinearMap.sub_apply, sirkApprox_apply, hfirst, hRx]
    abel
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [hkey x]
  have hblock : ‖V ((V.adjoint.comp (R.comp V) - B) (V.adjoint x))‖
      ≤ ‖V.adjoint.comp (R.comp V) - B‖ * ‖x‖ := by
    rw [hViso]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_left (hVadj x) (norm_nonneg _))
  have hleakN : ‖P.comp (R.comp Q)‖ = ‖Q.comp (R.comp P)‖ := by
    rw [hP, hQ]; exact sirk_offblock_norm_eq V hR
  have hleak : ‖P (R (Q x))‖ ≤ ‖Q.comp (R.comp P)‖ * ‖x‖ := by
    rw [← hleakN]
    exact ContinuousLinearMap.le_opNorm (P.comp (R.comp Q)) x
  have hcorner : ‖Q (R (P x))‖ ≤ ‖Q.comp (R.comp P)‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm (Q.comp (R.comp P)) x
  have htail : ‖Q (R (Q x))‖ ≤ ‖Q.comp (R.comp Q)‖ * ‖x‖ :=
    ContinuousLinearMap.le_opNorm (Q.comp (R.comp Q)) x
  have hsum : ‖V ((V.adjoint.comp (R.comp V) - B) (V.adjoint x))‖
        + ‖P (R (Q x))‖ + ‖Q (R (P x))‖ + ‖Q (R (Q x))‖
      ≤ (‖V.adjoint.comp (R.comp V) - B‖ + 2 * ‖Q.comp (R.comp P)‖
        + ‖Q.comp (R.comp Q)‖) * ‖x‖ := by
    nlinarith [hblock, hleak, hcorner, htail]
  have htri : ‖V ((V.adjoint.comp (R.comp V) - B) (V.adjoint x))
        + P (R (Q x)) + Q (R (P x)) + Q (R (Q x))‖
      ≤ ‖V ((V.adjoint.comp (R.comp V) - B) (V.adjoint x))‖
        + ‖P (R (Q x))‖ + ‖Q (R (P x))‖ + ‖Q (R (Q x))‖ := by
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    exact norm_add_le _ _
  linarith [htri, hsum]



/-! ## 9. The block term carries the finite shift-invert inverse -/

/-- `P ∘ V = V` for isometric `V`: the reconstruction fixes the retained range, so pushing
`V` through the projection changes nothing. -/
theorem sirkReconstruction_comp_self (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    (sirkReconstruction V).comp V = V := by
  ext x
  have hx : V.adjoint (V x) = x := by
    simpa using congrArg (fun f : F →L[ℂ] F => f x) hVV
  simp [sirkReconstruction, hx]

/-- `V∗ ∘ P = V∗`: the adjoint does not see the reconstruction either. -/
theorem sirk_adjoint_comp_reconstruction (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    V.adjoint.comp (sirkReconstruction V) = V.adjoint := by
  ext x
  have hx : V.adjoint (V (V.adjoint x)) = V.adjoint x := by
    simpa using congrArg (fun f : F →L[ℂ] F => f (V.adjoint x)) hVV
  simpa [sirkReconstruction] using hx

/-- **The compression correction is an identity, not an inequality.**
`ChapterShiftInvertBookkeeping.compression_ne_resolvent` exhibits the gap on a two-dimensional
witness.  Here is its general form: for `R = (H − z)⁻¹` and `B` a left inverse of the compressed
`V∗(H − z)V`,

  `V∗ R V − B = − B · V∗ ((H − z) Q R V)`,

with `Q = 1 − V V∗`.  The right-hand side is the *omitted coupling*: the exact resolvent
differs from the compressed inverse by the leakage the compression discards, transported by
`B`.  Unlike §8 this identity does need `V∗ V = 1` (to turn `T R V` into `V`), which an
isometric `V` supplies and which `sirk_end_to_end` already assumes. -/
theorem sirk_block_error_eq_correction (V : F →L[ℂ] E) (H R : E →L[ℂ] E) (z : ℂ)
    (B : F →L[ℂ] F) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hRright : (H - z • 1).comp R = ContinuousLinearMap.id ℂ E)
    (hBleft : B.comp (V.adjoint.comp ((H - z • 1).comp V)) =
      ContinuousLinearMap.id ℂ F) :
    V.adjoint.comp (R.comp V) - B
      = -(B.comp (V.adjoint.comp
        (((H - z • 1).comp (sirkComplement V)).comp (R.comp V)))) := by
  set T : E →L[ℂ] E := H - z • 1 with hT
  set P : E →L[ℂ] E := sirkReconstruction V with hP
  set Q : E →L[ℂ] E := sirkComplement V with hQ
  set X : F →L[ℂ] F := V.adjoint.comp (R.comp V) with hX
  set A : F →L[ℂ] F := V.adjoint.comp (T.comp V) with hA
  set S : F →L[ℂ] F := V.adjoint.comp ((T.comp Q).comp (R.comp V)) with hS
  have hTapply : ∀ x : E, T (R x) = x := by
    intro x
    have h := congrArg (fun f : E →L[ℂ] E => f x) hRright
    simpa [hT, ContinuousLinearMap.comp_apply] using h
  have hPQ : ∀ y : E, P y + Q y = y := by
    intro y
    rw [hP, hQ]
    exact sirkReconstruction_add_complement V y
  have hAX : A.comp X = ContinuousLinearMap.id ℂ F - S := by
    ext x
    have hsplit : P (R (V x)) + Q (R (V x)) = R (V x) := hPQ _
    have hp : P (R (V x)) = V (V.adjoint (R (V x))) := by rw [hP]; rfl
    have hAapply : A (X x) = V.adjoint (T (P (R (V x)))) := by
      simp only [hA, hX, ContinuousLinearMap.comp_apply]
      rw [hp]
    have hSapply : S x = V.adjoint (T (Q (R (V x)))) := by
      simp only [hS, ContinuousLinearMap.comp_apply]
    have hlin : T (R (V x)) = T (P (R (V x))) + T (Q (R (V x))) := by
      rw [← map_add, hsplit]
    have hVx : V.adjoint (T (R (V x))) = x := by
      rw [hTapply]
      simpa using congrArg (fun f : F →L[ℂ] F => f x) hVV
    have hsum : A (X x) + S x = x := by
      rw [hAapply, hSapply, ← map_add, ← hlin, hVx]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    exact eq_sub_iff_add_eq.mpr hsum
  have hBX : B.comp (A.comp X) = B - B.comp S := by
    rw [hAX, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
  have hleft : B.comp (A.comp X) = X := by
    rw [← ContinuousLinearMap.comp_assoc,
      show B.comp A = ContinuousLinearMap.id ℂ F from by simpa [hA, hT] using hBleft,
      ContinuousLinearMap.id_comp]
  have hXeq : X = B - B.comp S := by rw [← hleft, hBX]
  have hgoal : V.adjoint.comp (R.comp V) - B =
      -(B.comp (V.adjoint.comp ((T.comp Q).comp (R.comp V)))) := by
    rw [← hX, hXeq]
    abel
  simpa [hT, hQ, hX, hS] using hgoal

/-- **The block error is bounded by the leakage through the compressed inverse.**  Combining the
identity with the operator norms gives

  `‖V∗ R V − B‖ ≤ ‖B‖ · ‖(H − z) Q‖ · ‖R P‖`,

the quantity the SIRK error bound needs in place of `‖V∗ R V − B‖` when `B` is the finite
shift-invert inverse rather than the exact compression. -/
theorem sirk_block_error_le_of_inverse (V : F →L[ℂ] E) (H R : E →L[ℂ] E) (z : ℂ)
    (B : F →L[ℂ] F) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hRright : (H - z • 1).comp R = ContinuousLinearMap.id ℂ E)
    (hBleft : B.comp (V.adjoint.comp ((H - z • 1).comp V)) =
      ContinuousLinearMap.id ℂ F) :
    ‖V.adjoint.comp (R.comp V) - B‖
      ≤ ‖B‖ * (‖(H - z • 1).comp (sirkComplement V)‖
        * ‖R.comp (sirkReconstruction V)‖) := by
  set T : E →L[ℂ] E := H - z • 1 with hT
  set P : E →L[ℂ] E := sirkReconstruction V with hP
  set Q : E →L[ℂ] E := sirkComplement V with hQ
  have hPV : ∀ x : F, P (V x) = V x := by
    intro x
    have h := congrArg (fun f : F →L[ℂ] E => f x) (sirkReconstruction_comp_self V hVV)
    simpa [hP] using h
  have hid := sirk_block_error_eq_correction V H R z B hVV hRright hBleft
  have hbound : ∀ x : F,
      ‖((V.adjoint.comp ((T.comp Q).comp (R.comp V)))) x‖
        ≤ ‖T.comp (Q.comp (R.comp P))‖ * ‖x‖ := by
    intro x
    have hx : ((V.adjoint.comp ((T.comp Q).comp (R.comp V)))) x
        = V.adjoint (((T.comp (Q.comp (R.comp P))).comp V) x) := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [hPV x]
    rw [hx]
    calc ‖V.adjoint ((T.comp (Q.comp (R.comp P))) (V x))‖
        ≤ ‖(T.comp (Q.comp (R.comp P))) (V x)‖ := hVadj _
      _ ≤ ‖T.comp (Q.comp (R.comp P))‖ * ‖V x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖T.comp (Q.comp (R.comp P))‖ * ‖x‖ := by rw [hViso]
  have hSle : ‖V.adjoint.comp ((T.comp Q).comp (R.comp V))‖
      ≤ ‖T.comp (Q.comp (R.comp P))‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) hbound
  have hcomp : ‖T.comp (Q.comp (R.comp P))‖
      ≤ ‖T.comp Q‖ * ‖R.comp P‖ := by
    rw [← ContinuousLinearMap.comp_assoc]
    exact ContinuousLinearMap.opNorm_comp_le (T.comp Q) (R.comp P)
  have hB : ‖B.comp (V.adjoint.comp ((T.comp Q).comp (R.comp V)))‖
      ≤ ‖B‖ * ‖V.adjoint.comp ((T.comp Q).comp (R.comp V))‖ :=
    ContinuousLinearMap.opNorm_comp_le B _
  have hchain : ‖B.comp (V.adjoint.comp ((T.comp Q).comp (R.comp V)))‖
      ≤ ‖B‖ * (‖T.comp Q‖ * ‖R.comp P‖) := by
    refine le_trans hB ?_
    exact mul_le_mul_of_nonneg_left (le_trans hSle hcomp) (norm_nonneg B)
  rw [hid, norm_neg]
  simpa [hT, hP, hQ] using hchain

/-- **The composed full-space bound with the finite inverse.**  §8 prices the omitted space;
this replaces its first term by the correction of §9, so the whole estimate is stated for a
`B` that inverts the *compressed* shift `V∗(H − z)V` — the object SIRK actually builds — and
no term refers to `V∗ R V` any more. -/
theorem sirk_fullSpace_error_le_shiftInvert (V : F →L[ℂ] E) (H R : E →L[ℂ] E) (z : ℂ)
    (B : F →L[ℂ] F) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hR : IsSelfAdjoint R)
    (hRright : (H - z • 1).comp R = ContinuousLinearMap.id ℂ E)
    (hBleft : B.comp (V.adjoint.comp ((H - z • 1).comp V)) =
      ContinuousLinearMap.id ℂ F) :
    ‖R - sirkApprox V B‖ ≤ ‖B‖ * (‖(H - z • 1).comp (sirkComplement V)‖
        * ‖R.comp (sirkReconstruction V)‖)
      + 2 * ‖(sirkComplement V).comp (R.comp (sirkReconstruction V))‖
      + ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖ := by
  refine le_trans (sirk_fullSpace_error_le V B hViso hVadj hR) ?_
  have hblock := sirk_block_error_le_of_inverse V H R z B hVV hViso hVadj hRright hBleft
  linarith



/-! ## 10. U2's budget: `T`, `S`, `O`, `F` attached to the leakage and tail -/

/-- **`T` — the omitted-space allocation.**  Leakage plus tail, exactly the two off-block
norms of §8.  `softmodes.md` U2 asks that `T` bound "physical truncation and omitted-space
effects"; these are the two operator norms that §8 leaves once the block term is separated. -/
noncomputable def sirkTailBudget (V : F →L[ℂ] E) (R : E →L[ℂ] E) : ℝ :=
  2 * ‖(sirkComplement V).comp (R.comp (sirkReconstruction V))‖
    + ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖

/-- **`O` — the transfer allocation.**  The price of replacing the compression `V∗ R V` by the
finite inverse `B` of `V∗(H − z)V`: §9's correction, read as a number. -/
noncomputable def sirkTransferBudget (V : F →L[ℂ] E) (H R : E →L[ℂ] E) (z : ℂ)
    (B : F →L[ℂ] F) : ℝ :=
  ‖B‖ * (‖(H - z • 1).comp (sirkComplement V)‖ * ‖R.comp (sirkReconstruction V)‖)

/-- **`S` — the solve allocation.**  `m` solve-columns of norm `ε / √m` carry at most `ε` in
Frobenius norm, so the accumulated solve error is budgeted by a single number `ε`; keeping
`ε` fixed is what makes the budget independent of `m`. -/
def sirkSolveBudget (_m : ℕ) (ε : ℝ) : ℝ := ε

/-- The arithmetic behind `S`: `m` columns of norm `ε / √m` have squared Frobenius mass
exactly `ε²`, hence Frobenius norm `ε`.  This is why the per-column tolerance `ε / √m` is the
right one — a fixed per-column tolerance would grow with `m`. -/
theorem solve_columns_budget (m : ℕ) (hm : 0 < m) (ε : ℝ) :
    (m : ℝ) * (ε / Real.sqrt m) ^ 2 = ε ^ 2 := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsqrt : Real.sqrt (m : ℝ) ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (le_of_lt hm')]
  ring

/-- **`V ∘ B ∘ V∗` is Lipschitz in `B` with constant one.**  The simulated scheme differs from
the exact reduced inverse only through `B − Bhat`, and neither `V` nor `V∗` amplifies. -/
theorem norm_sirkApprox_sub_le (V : F →L[ℂ] E) (B Bhat : F →L[ℂ] F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) :
    ‖sirkApprox V B - sirkApprox V Bhat‖ ≤ ‖B - Bhat‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have hsub : (sirkApprox V B - sirkApprox V Bhat) x
      = V ((B - Bhat) (V.adjoint x)) := by
    simp [sirkApprox_apply, ContinuousLinearMap.sub_apply, map_sub]
  rw [hsub, hViso]
  exact le_trans (ContinuousLinearMap.le_opNorm (B - Bhat) _)
    (mul_le_mul_of_nonneg_left (hVadj x) (norm_nonneg _))

/-- **U2's envelope, with every allocation named.**

For the exact resolvent `R = (H − z)⁻¹` and a reduced `Bhat` within `S + F` of the finite
inverse `B` of `V∗(H − z)V`:

  `‖R − V Bhat V∗‖ ≤ O + T + (S + F)`,

where `O = sirkTransferBudget` (compressed-inverse correction, §9), `T = sirkTailBudget`
(leakage and tail, §8), `S = sirkSolveBudget m ε` (accumulated solves, `ε/√m` per column) and
`F` is the caller's certified rounding-and-assembly budget.  The `2 C̄ D̄ e^{−a q_m}` term of
`softmodes.md` U2 lives in the rational approximation of `R_g` and is *not* claimed here; what
this theorem does is attach the other four allocations to the same scheme, so that the envelope
of U2 is a statement about numbers that have already been proved to bound something. -/
theorem sirk_error_le_budget (V : F →L[ℂ] E) (H R : E →L[ℂ] E) (z : ℂ)
    (B Bhat : F →L[ℂ] F) (m : ℕ) (ε Fg : ℝ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hR : IsSelfAdjoint R)
    (hRright : (H - z • 1).comp R = ContinuousLinearMap.id ℂ E)
    (hBleft : B.comp (V.adjoint.comp ((H - z • 1).comp V)) =
      ContinuousLinearMap.id ℂ F)
    (hBhat : ‖B - Bhat‖ ≤ sirkSolveBudget m ε + Fg) :
    ‖R - sirkApprox V Bhat‖
      ≤ sirkTransferBudget V H R z B + sirkTailBudget V R
        + (sirkSolveBudget m ε + Fg) := by
  have hexact : ‖R - sirkApprox V B‖
      ≤ sirkTransferBudget V H R z B + sirkTailBudget V R := by
    have h := sirk_fullSpace_error_le_shiftInvert V H R z B hVV hViso hVadj hR hRright hBleft
    rw [sirkTransferBudget, sirkTailBudget]
    linarith
  have hdiff : ‖sirkApprox V B - sirkApprox V Bhat‖ ≤ ‖B - Bhat‖ :=
    norm_sirkApprox_sub_le V B Bhat hViso hVadj
  have hsplit : R - sirkApprox V Bhat
      = (R - sirkApprox V B) + (sirkApprox V B - sirkApprox V Bhat) := by abel
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  linarith


/-! ## 11. `T` from the tail and the coupling: the Schur/Gershgorin data -/

/-- **The leakage is the tail times the coupling times the finite inverse.**  Compressing the
resolvent identity `Q R (H − z) P = Q P = 0` gives

  `(Q R P) (P (H − z) P) + (Q R Q) (Q (H − z) P) = 0`,

and `V B V∗` is a right inverse of `P (H − z) P` — exactly what `B` being an inverse of the
compressed shift `V∗(H − z)V` says.  Hence `Q R P = − (Q R Q) (Q (H − z) P) (V B V∗)`, so the
leakage costs the **tail** `‖Q R Q‖`, the off-diagonal **coupling** `‖Q (H − z) P‖` and `‖B‖`.
The coupling is what a Schur row/column test bounds, the tail is what a truncation lift bounds;
neither estimate sums entries, so no factor `m` is manufactured. -/
theorem sirk_leakage_le_of_tail_coupling (V : F →L[ℂ] E) (T R : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hRleft : R.comp T = ContinuousLinearMap.id ℂ E)
    (hBright : (V.adjoint.comp (T.comp V)).comp B = ContinuousLinearMap.id ℂ F) :
    ‖(sirkComplement V).comp (R.comp (sirkReconstruction V))‖
      ≤ ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖
        * (‖(sirkComplement V).comp (T.comp (sirkReconstruction V))‖ * ‖B‖) := by
  set P : E →L[ℂ] E := sirkReconstruction V with hP
  set Q : E →L[ℂ] E := sirkComplement V with hQ
  set M : E →L[ℂ] E := V.comp (B.comp V.adjoint) with hM
  have hPQ : ∀ y : E, P y + Q y = y := fun y => by
    rw [hP, hQ]; exact sirkReconstruction_add_complement V y
  have hPV : ∀ z : F, P (V z) = V z := fun z => by
    rw [hP, sirkReconstruction, ContinuousLinearMap.comp_apply]
    have h := congrArg (fun f : F →L[ℂ] F => f z) hVV
    simpa [ContinuousLinearMap.comp_apply] using congrArg V h
  have hAB : ∀ w : F, (V.adjoint.comp (T.comp V)) (B w) = w := fun w => by
    have := congrArg (fun f : F →L[ℂ] F => f w) hBright
    simpa [ContinuousLinearMap.comp_apply] using this
  have hPT : ∀ z : F, P (T (V z)) = V ((V.adjoint.comp (T.comp V)) z) := fun z => by
    rw [hP, sirkReconstruction, ContinuousLinearMap.comp_apply]
    rfl
  have hPTPM : (P.comp (T.comp P)).comp M = P := by
    ext x
    have h1 : P (V (B (V.adjoint x))) = V (B (V.adjoint x)) := hPV _
    have h2 : P (T (V (B (V.adjoint x))))
        = V ((V.adjoint.comp (T.comp V)) (B (V.adjoint x))) := hPT _
    have h3 : (V.adjoint.comp (T.comp V)) (B (V.adjoint x)) = V.adjoint x := hAB _
    have h4 : P x = V (V.adjoint x) := by
      rw [hP, sirkReconstruction, ContinuousLinearMap.comp_apply]
    simp only [ContinuousLinearMap.comp_apply, hM]
    rw [h1, h2, h3, h4]
  have hQP : ∀ y : E, Q (P y) = 0 := fun y => by
    have h1 := hPQ (P y)
    have h2 : P (P y) = P y := by
      rw [hP]
      have hidem := sirkReconstruction_isIdempotent V hVV
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun f : E →L[ℂ] E => f y) hidem
    rw [h2] at h1
    exact add_eq_left.mp h1
  have hPPapp : ∀ y : E, P (P y) = P y := fun y => by
    have hidem := sirkReconstruction_isIdempotent V hVV
    simpa [hP, ContinuousLinearMap.comp_apply] using
      congrArg (fun f : E →L[ℂ] E => f y) hidem
  have hQdef : ∀ y : E, Q y = y - P y := fun y => by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hPQ y
  have hQP0 : ∀ y : E, P (Q y) = 0 := fun y => by
    rw [hQdef y, map_sub, hPPapp y, sub_self]
  have hQQ : ∀ y : E, Q (Q y) = Q y := fun y => by
    rw [hQdef (Q y), hQP0 y, sub_zero]
  have hkey : ∀ x : E,
      Q (R (P (P (T (P x))))) + Q (R (Q (T (P x)))) = 0 := by
    intro x
    have hzero : Q (R (T (P x))) = 0 := by
      have h1 : R (T (P x)) = P x := by
        have := congrArg (fun f : E →L[ℂ] E => f (P x)) hRleft
        simpa [ContinuousLinearMap.comp_apply] using this
      rw [h1, hQP x]
    have hsplit : T (P x) = P (T (P x)) + Q (T (P x)) := by
      exact (hPQ (T (P x))).symm
    rw [hsplit] at hzero
    simp only [map_add] at hzero
    simpa [hPPapp] using hzero
  have hPfix : ∀ x : E, Q (R (P (P x))) = Q (R (P x)) := by
    intro x
    have : P (P x) = P x := by
      rw [hP]
      have hidem := sirkReconstruction_isIdempotent V hVV
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun f : E →L[ℂ] E => f x) hidem
    rw [this]
  have hleak : ∀ x : E, Q (R (P x))
      = -(Q (R (Q ((T.comp P) (M x))))) :=
    fun x => by
      have hk := hkey (M x)
      have hMx : (P.comp (T.comp P)) (M x) = P x := by
        have := congrArg (fun f : E →L[ℂ] E => f x) hPTPM
        simpa [ContinuousLinearMap.comp_apply] using this
      have hMx' : P (T (P (M x))) = P x := by
        simpa [ContinuousLinearMap.comp_apply] using hMx
      have hMx' : P (T (P (M x))) = P x := by
        simpa [ContinuousLinearMap.comp_apply] using hMx
      have hk' : Q (R (P x)) + Q (R (Q (T (P (M x))))) = 0 := by
        simpa [hPPapp, hMx'] using hk
      simpa [ContinuousLinearMap.comp_apply] using eq_neg_of_add_eq_zero_left hk'
  -- norm bound
  have hMn : ‖M‖ ≤ ‖B‖ := by
    have h1 : ‖M‖ ≤ ‖V‖ * (‖B‖ * ‖V.adjoint‖) := by
      rw [hM]
      calc ‖V.comp (B.comp V.adjoint)‖ ≤ ‖V‖ * ‖B.comp V.adjoint‖ :=
            ContinuousLinearMap.opNorm_comp_le V _
        _ ≤ ‖V‖ * (‖B‖ * ‖V.adjoint‖) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le B V.adjoint
    have hV1 : ‖V‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [hViso]; simp
    have hVa1 : ‖V.adjoint‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
        simpa using hVadj v
    calc ‖M‖ ≤ ‖V‖ * (‖B‖ * ‖V.adjoint‖) := h1
      _ ≤ 1 * (‖B‖ * 1) := by gcongr
      _ = ‖B‖ := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  change ‖Q (R (P x))‖ ≤ ‖Q.comp (R.comp Q)‖ * (‖Q.comp (T.comp P)‖ * ‖B‖) * ‖x‖
  rw [hleak x, norm_neg]
  have h1 : ‖Q (R (Q ((T.comp P) (M x))))‖
      ≤ ‖Q.comp (R.comp Q)‖ * ‖Q ((T.comp P) (M x))‖ := by
    have heq : Q (R (Q ((T.comp P) (M x))))
        = (Q.comp (R.comp Q)) (Q ((T.comp P) (M x))) := by
      simp only [ContinuousLinearMap.comp_apply, hQQ]
    rw [heq]
    exact ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖Q ((T.comp P) (M x))‖ ≤ ‖Q.comp (T.comp P)‖ * ‖M x‖ := by
    simpa [ContinuousLinearMap.comp_apply] using
      ContinuousLinearMap.le_opNorm (Q.comp (T.comp P)) (M x)
  have h3 : ‖M x‖ ≤ ‖M‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
  have h4 : ‖M‖ * ‖x‖ ≤ ‖B‖ * ‖x‖ :=
    mul_le_mul_of_nonneg_right hMn (norm_nonneg x)
  have h5 : ‖Q ((T.comp P) (M x))‖ ≤ ‖Q.comp (T.comp P)‖ * (‖B‖ * ‖x‖) := by
    refine le_trans h2 ?_
    exact mul_le_mul_of_nonneg_left (le_trans h3 h4) (norm_nonneg _)
  have h6 : ‖Q.comp (R.comp Q)‖ * ‖Q ((T.comp P) (M x))‖
      ≤ ‖Q.comp (R.comp Q)‖ * (‖Q.comp (T.comp P)‖ * (‖B‖ * ‖x‖)) :=
    mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
  refine le_trans (le_trans h1 h6) ?_
  have hrr : ‖Q.comp (R.comp Q)‖ * (‖Q.comp (T.comp P)‖ * (‖B‖ * ‖x‖))
      = ‖Q.comp (R.comp Q)‖ * (‖Q.comp (T.comp P)‖ * ‖B‖) * ‖x‖ := by ring
  rw [hrr]

/-- **`T` is a single multiple of the tail.**  Substituting the leakage bound into
`sirkTailBudget` gives

  `T ≤ (2 ‖Q (H − z) P‖ ‖B‖ + 1) · ‖Q R Q‖`,

so the omitted-space allocation is the tail times an explicit factor built from the coupling and
the reduced inverse — no sum over basis directions, hence `m`-independent whenever those three
numbers are. -/
theorem sirkTailBudget_le_of_tail_coupling (V : F →L[ℂ] E) (T R : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hRleft : R.comp T = ContinuousLinearMap.id ℂ E)
    (hBright : (V.adjoint.comp (T.comp V)).comp B = ContinuousLinearMap.id ℂ F) :
    sirkTailBudget V R
      ≤ (2 * ‖(sirkComplement V).comp (T.comp (sirkReconstruction V))‖ * ‖B‖ + 1)
        * ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖ := by
  have hleak := sirk_leakage_le_of_tail_coupling V T R B hVV hViso hVadj hRleft hBright
  rw [sirkTailBudget]
  nlinarith [hleak, norm_nonneg ((sirkComplement V).comp (R.comp (sirkComplement V))),
    norm_nonneg ((sirkComplement V).comp (T.comp (sirkReconstruction V))), norm_nonneg B]

/-! ## 12. The scalar marker for the resolvent on the common segment -/

/-- The degree-`q` geometric marker `Σ_{j<q} (−t)^j` for `1/(1 + t)`: the explicit rational
approximant (`denominator 1`) that `softmodes.md` U2 asks for on the common segment.  It is the
polynomial SIRK would build for the scalar model `1/(1 + t)`, and its error is *exact*, not
estimated: `geomMarker_remainder` below. -/
def geomMarker (q : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range q, (-t) ^ j

/-- `geomMarker (q+1) t = geomMarker q t + (-t)^q`. -/
theorem geomMarker_succ (q : ℕ) (t : ℝ) :
    geomMarker (q + 1) t = geomMarker q t + (-t) ^ q := by
  simp [geomMarker, Finset.sum_range_succ]

/-- **The remainder is exact.**  `1/(1 + t) − Σ_{j<q} (−t)^j = (−t)^q/(1 + t)`, so the marker's
error is the next geometric term over `1 + t` — there is no approximation in this step, only the
collapse of the finite geometric series. -/
theorem geomMarker_remainder (q : ℕ) (t : ℝ) (ht : t ≠ -1) :
    1 / (1 + t) - geomMarker q t = (-t) ^ q / (1 + t) := by
  induction q with
  | zero => simp [geomMarker]
  | succ q ih =>
    rw [geomMarker_succ, sub_add_eq_sub_sub, ih, pow_succ']
    have h1 : (1 : ℝ) + t ≠ 0 := by
      intro h; apply ht; linarith
    field_simp
    ring

/-- **The scalar error on the common segment.**  For `0 ≤ t ≤ ρ`, the degree-`q` marker
approximates `1/(1 + t)` to within `ρ^q`.  With `t = x/γ` and `x ∈ [0, 1/κ]` this is the `D` of
`sirk_error_bound_at` with `C = 1`, and the `2 C D` term it feeds is `2 ρ^q`
(`geomMarker_twoCD`). -/
theorem geomMarker_error_le (q : ℕ) (t ρ : ℝ) (ht : 0 ≤ t) (htρ : t ≤ ρ) :
    |1 / (1 + t) - geomMarker q t| ≤ ρ ^ q := by
  have ht1 : t ≠ -1 := by linarith
  rw [geomMarker_remainder q t ht1, abs_div]
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have habs1 : |1 + t| = 1 + t := abs_of_pos hpos
  rw [habs1]
  have hnum : |(-t) ^ q| = t ^ q := by
    rw [abs_pow, abs_neg, abs_of_nonneg ht]
  rw [hnum]
  have hq : t ^ q ≤ ρ ^ q := pow_le_pow_left₀ ht htρ q
  rw [div_le_iff₀ hpos]
  calc t ^ q ≤ ρ ^ q := hq
    _ ≤ ρ ^ q * (1 + t) := by
        have h0 : (0 : ℝ) ≤ ρ ^ q := pow_nonneg (by linarith) q
        nlinarith

/-- The `2 C D` term of `sirk_error_bound_at` with `C = 1` and `D = ρ^q`. -/
theorem geomMarker_twoCD (q : ℕ) (t ρ : ℝ) (ht : 0 ≤ t) (htρ : t ≤ ρ) :
    2 * |1 / (1 + t) - geomMarker q t| ≤ 2 * ρ ^ q := by
  have := geomMarker_error_le q t ρ ht htρ
  linarith

/-- **The rate is exponential.**  For `0 < ρ < 1` the geometric error `ρ^q` is `e^{−a q}` with
`a = −log ρ > 0`, so `geomMarker_error_le` supplies the `D e^{−a q}` half of the envelope with
`a` explicit and `D` the tail of the geometric series. -/
theorem geomMarker_rate (ρ : ℝ) (hρ : 0 < ρ) (q : ℕ) :
    ρ ^ q = Real.exp (-((-Real.log ρ) * q)) := by
  rw [show -((-Real.log ρ) * q) = (q : ℝ) * Real.log ρ by ring]
  rw [Real.exp_nat_mul, Real.exp_log hρ]


/-! ## 13. The Fock instantiation: `T` as a function of the coupling and the gap

`softmodes.md` U2 asks for the tail number `T(g, L)` of the full-space SIRK budget to be
*computed*, not assumed.  §11 reduced `T` to two operator norms: the coupling `Q (H − z) P` and
the compressed resolvent `Q R Q`.  This section evaluates both for a Fock model whose free part
is block diagonal across the split — the situation of `H = A + g·W` with `A` preserving the
retained and discarded sectors.

* `opNorm_le_one_of_orthogonalProjection` / `norm_projection_le`: an orthogonal projection does
  not amplify.  This is what keeps a factor `‖Q‖` out of the coupling estimate.
* `fock_coupling_le`: `Q (H − z) P = g · Q W P`, because the free block `Q A P` vanishes and
  `Q P = 0`.  Hence `‖Q (H − z) P‖ ≤ ‖g‖‖W‖‖P‖` — linear in the coupling.
* `fock_tail_le`: if `H` commutes with `Q`, is coercive on the discarded block with gap `mu`, and
  the shift is `z = −lam < 0`, then `‖Q R Q‖ ≤ (mu + lam)⁻¹`.  No symmetry of `H` is used.
* `sirkTailBudget_le_fock`: the two combined, `sirkTailBudget V R ≤ (2‖g‖‖W‖‖P‖‖B‖ + 1)/(mu +
  lam)`, with no factor of the Krylov dimension `m`.

-/


theorem opNorm_le_one_of_orthogonalProjection (Q : E →L[ℂ] E)
    (hQidem : Q.comp Q = Q) (hQadj : Q.adjoint = Q) : ‖Q‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have h1 : Q (Q x) = Q x := by
    have := congrArg (fun f : E →L[ℂ] E => f x) hQidem
    simpa [ContinuousLinearMap.comp_apply] using this
  have hsq : ‖Q x‖ ^ 2 = (inner ℂ x (Q x)).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (Q x)]
    have hAI := ContinuousLinearMap.adjoint_inner_left Q x (Q x)
    rw [hQadj, h1] at hAI
    have hc : (inner ℂ x (Q x)) = (starRingEnd ℂ) (inner ℂ (Q x) x) :=
      (inner_conj_symm (𝕜 := ℂ) x (Q x)).symm
    rw [hc, Complex.conj_re, ← hAI]
    rfl
  have hle : ‖Q x‖ ^ 2 ≤ ‖x‖ * ‖Q x‖ := by
    rw [hsq]
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  nlinarith [norm_nonneg (Q x), norm_nonneg x]

/-- **The coupling of a Fock model `H = A + g·W` across a split.**  If the free part `A` does not
couple the kept space `range P` to the discarded one `range Q` (`Q A P = 0`), then the whole
off-diagonal block of the shifted generator `H − z` is the interaction alone:
`Q (H − z) P = g · Q W P`.  So the coupling number of §11 is `|g| ‖W‖ ‖P‖`: linear in the
coupling and independent of the truncation order. -/
theorem fock_coupling_le (A W P Q H : E →L[ℂ] E) (g : ℂ) (z : ℂ)
    (hP : P = ContinuousLinearMap.id ℂ E - Q) (hQidem : Q.comp Q = Q)
    (hQadj : Q.adjoint = Q)
    (hblock : Q.comp (A.comp P) = 0) (hH : H = A + g • W) :
    ‖Q.comp ((H - z • 1).comp P)‖ ≤ ‖g‖ * ‖W‖ * ‖P‖ := by
  have hQP : Q.comp P = 0 := by
    rw [hP, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id, hQidem, sub_self]
  have hkey : Q.comp ((H - z • 1).comp P) = g • (Q.comp (W.comp P)) := by
    ext x
    have h1 : Q (((H - z • 1) (P x))) = Q (H (P x)) - z • Q (P x) := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, map_sub, map_smul]
    have h2 : Q (H (P x)) = Q (A (P x)) + g • Q (W (P x)) := by
      rw [hH]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add,
        map_smul]
    have h3 : Q (A (P x)) = 0 := by
      have := congrArg (fun f : E →L[ℂ] E => f x) hblock
      simpa [ContinuousLinearMap.comp_apply] using this
    have h4 : Q (P x) = 0 := by
      have := congrArg (fun f : E →L[ℂ] E => f x) hQP
      simpa [ContinuousLinearMap.comp_apply] using this
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
    rw [h1, h2, h3, h4]
    simp
  have hQ1 : ‖Q‖ ≤ 1 := opNorm_le_one_of_orthogonalProjection Q hQidem hQadj
  rw [hkey, norm_smul]
  have h1 : ‖Q.comp (W.comp P)‖ ≤ ‖W‖ * ‖P‖ := by
    calc ‖Q.comp (W.comp P)‖ ≤ ‖Q‖ * ‖W.comp P‖ :=
          ContinuousLinearMap.opNorm_comp_le Q _
      _ ≤ 1 * (‖W‖ * ‖P‖) := by
          refine mul_le_mul hQ1 ?_ (norm_nonneg _) zero_le_one
          exact ContinuousLinearMap.opNorm_comp_le W P
      _ = ‖W‖ * ‖P‖ := one_mul _
  calc ‖g‖ * ‖Q.comp (W.comp P)‖ ≤ ‖g‖ * (‖W‖ * ‖P‖) := by gcongr
    _ = ‖g‖ * ‖W‖ * ‖P‖ := by ring

/-- The real part of `⟪Q x, Q x⟫` is `⟪x, Q x⟫`'s, for an orthogonal projection `Q`. -/
theorem re_inner_projection (Q : E →L[ℂ] E) (hQidem : Q.comp Q = Q) (hQadj : Q.adjoint = Q)
    (x : E) : (inner ℂ (Q x) (Q x)).re = (inner ℂ x (Q x)).re := by
  have h1 : Q (Q x) = Q x := by
    have := congrArg (fun f : E →L[ℂ] E => f x) hQidem
    simpa [ContinuousLinearMap.comp_apply] using this
  have hAI := ContinuousLinearMap.adjoint_inner_left Q x (Q x)
  rw [hQadj, h1] at hAI
  have hc : (inner ℂ x (Q x)) = (starRingEnd ℂ) (inner ℂ (Q x) x) :=
    (inner_conj_symm (𝕜 := ℂ) x (Q x)).symm
  rw [hc, Complex.conj_re, ← hAI]

/-- **An orthogonal projection does not amplify.**  `‖Q x‖ ≤ ‖x‖`, from
`‖Q x‖² = ⟪x, Q x⟫.re ≤ ‖x‖‖Q x‖`. -/
theorem norm_projection_le (Q : E →L[ℂ] E) (hQidem : Q.comp Q = Q) (hQadj : Q.adjoint = Q)
    (x : E) : ‖Q x‖ ≤ ‖x‖ := by
  have hsq : ‖Q x‖ ^ 2 = (inner ℂ x (Q x)).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (Q x)]
    exact re_inner_projection Q hQidem hQadj x
  have hle : ‖Q x‖ ^ 2 ≤ ‖x‖ * ‖Q x‖ := by
    rw [hsq]
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  nlinarith [norm_nonneg (Q x), norm_nonneg x]

/-- **The tail of the resolvent on the discarded block.**  If `H` preserves the splitting
(`H Q = Q H`), is coercive on it with gap `mu`, and the shift is real and negative (`z = −lam`),
then the compressed resolvent `Q R Q` is bounded by `(mu + lam)⁻¹` — the resolvent estimate on
the complement, with no symmetry assumption on `H` beyond commuting with `Q`.

**Superseded by §15.**  The commutation hypothesis here is vacuous for a SIRK split (§14);
`resolvent_tail_le_of_schur` proves the same conclusion from the coercivity of the Schur
complement of the compressed shift, with no invariance. -/
theorem fock_tail_le (Q H R : E →L[ℂ] E) (mu lam : ℝ)
    (hQidem : Q.comp Q = Q) (hQadj : Q.adjoint = Q) (hcomm : H.comp Q = Q.comp H)
    (hcoer : ∀ v : E, mu * ‖Q v‖ ^ 2 ≤ (inner ℂ (Q v) (H (Q v))).re)
    (hpos : 0 < mu + lam)
    (hinv : (H + (lam : ℂ) • 1).comp R = ContinuousLinearMap.id ℂ E) :
    ‖Q.comp (R.comp Q)‖ ≤ (mu + lam)⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  set w : E := Q x with hw
  set v : E := Q (R w) with hv
  have hQw : Q w = w := by
    rw [hw, ← ContinuousLinearMap.comp_apply, hQidem]
  have hQv : Q v = v := by
    rw [hv, ← ContinuousLinearMap.comp_apply, hQidem]
  have hHv : H v = Q (H (R w)) := by
    have := congrArg (fun f : E →L[ℂ] E => f (R w)) hcomm
    simpa [hv, ContinuousLinearMap.comp_apply] using this
  have hfix : H v + (lam : ℂ) • v = w := by
    have h1 : (H + (lam : ℂ) • 1) (R w) = w := by
      have := congrArg (fun f : E →L[ℂ] E => f w) hinv
      simpa [ContinuousLinearMap.comp_apply] using this
    have h2 : (H + (lam : ℂ) • 1) (R w) = H (R w) + (lam : ℂ) • R w := rfl
    rw [h2] at h1
    have h3 : Q (H (R w) + (lam : ℂ) • R w) = Q w := by rw [h1]
    rw [map_add, map_smul, hQw] at h3
    simpa only [← hv, hHv] using h3
  have hinner : mu * ‖v‖ ^ 2 ≤ (inner ℂ v (H v)).re := by
    have := hcoer (R w)
    simpa [hv] using this
  have hquad : (mu + lam) * ‖v‖ ^ 2 ≤ ‖v‖ * ‖x‖ := by
    have hre : (inner ℂ v (H v)).re + lam * ‖v‖ ^ 2 = (inner ℂ v w).re := by
      have h0 : (inner ℂ v (H v + (lam : ℂ) • v)).re = (inner ℂ v w).re := by rw [hfix]
      have hsq : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
      have him : (inner ℂ v v).im = 0 := inner_self_im (𝕜 := ℂ) v
      rw [inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, hsq, him, zero_mul, sub_zero] at h0
      simpa using h0
    have h1 : (mu + lam) * ‖v‖ ^ 2 ≤ (inner ℂ v w).re := by
      rw [← hre]
      nlinarith [hinner]
    have h2 : (inner ℂ v w).re ≤ ‖v‖ * ‖w‖ :=
      (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
    have h3 : ‖w‖ ≤ ‖x‖ := by
      rw [hw]
      exact norm_projection_le Q hQidem hQadj x
    nlinarith [h1, h2, h3, norm_nonneg v, norm_nonneg x, norm_nonneg w]
  have hfinal : ‖v‖ ≤ (mu + lam)⁻¹ * ‖x‖ := by
    rcases eq_or_lt_of_le (norm_nonneg v) with h0 | h0
    · rw [← h0]
      positivity
    · have hstep : (mu + lam) * ‖v‖ ≤ ‖x‖ := by
        have h1 : (mu + lam) * ‖v‖ * ‖v‖ ≤ ‖v‖ * ‖x‖ := by
          calc (mu + lam) * ‖v‖ * ‖v‖ = (mu + lam) * ‖v‖ ^ 2 := by ring
            _ ≤ ‖v‖ * ‖x‖ := hquad
        exact le_of_mul_le_mul_right (by simpa [mul_comm] using h1) h0
      calc ‖v‖ ≤ ‖x‖ / (mu + lam) := by
            rw [le_div_iff₀ hpos]
            calc ‖v‖ * (mu + lam) = (mu + lam) * ‖v‖ := by ring
              _ ≤ ‖x‖ := hstep
        _ = (mu + lam)⁻¹ * ‖x‖ := by rw [div_eq_inv_mul]
  calc ‖(Q.comp (R.comp Q)) x‖ = ‖v‖ := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hv, ← hw]
    _ ≤ (mu + lam)⁻¹ * ‖x‖ := hfinal

/-- `P = V V∗` is idempotent when `V` has orthonormal columns. -/
theorem sirkReconstruction_idem (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    (sirkReconstruction V).comp (sirkReconstruction V) = sirkReconstruction V := by
  rw [sirkReconstruction, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc V.adjoint V V.adjoint, hVV,
    ContinuousLinearMap.id_comp]

/-- The complement `Q = 1 − P` of an idempotent self-adjoint `P` is again one. -/
theorem sirkComplement_idem (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    (sirkComplement V).comp (sirkComplement V) = sirkComplement V := by
  have hP := sirkReconstruction_idem V hVV
  ext x
  have hPx : sirkReconstruction V (sirkReconstruction V x) = sirkReconstruction V x := by
    have := congrArg (fun f : E →L[ℂ] E => f x) hP
    simpa [ContinuousLinearMap.comp_apply] using this
  simp only [ContinuousLinearMap.comp_apply, sirkComplement_apply, map_sub,
    hPx]
  abel

/-- The complement is self-adjoint, in the `adjoint`-form used by the norm estimates. -/
theorem sirkComplement_adjoint_eq (V : F →L[ℂ] E) :
    (sirkComplement V).adjoint = sirkComplement V :=
  sirkComplement_isSelfAdjoint V

/-- **§13: the Fock tail budget is a concrete function of `(g, lam, mu)`.**  For a Fock model
`H = A + g·W` split by the SIRK reconstruction:
* the free part is block diagonal, so the coupling of `H − z` is the interaction alone,
  `‖Q (H − z) P‖ ≤ ‖g‖‖W‖‖P‖` (§13 coupling lemma);
* on the discarded block `H` has gap `mu` and the shift is `z = −lam`, so the compressed
  resolvent obeys `‖Q R Q‖ ≤ (mu + lam)⁻¹` (§13 tail lemma).
Feeding both into §11's `sirkTailBudget_le_of_tail_coupling` turns the abstract `T` of U2 into
`(2‖g‖‖W‖‖P‖‖B‖ + 1)(mu + lam)⁻¹`: linear in the coupling, and with no factor of the Krylov
dimension `m`.

**Superseded by §15**: `sirkTailBudget_le_fock_schur` reaches the same shape with no `hcomm`,
replacing it by the Schur complement of the compressed shift. -/
theorem sirkTailBudget_le_fock (V : F →L[ℂ] E) (A W H R : E →L[ℂ] E) (g z : ℂ)
    (mu lam : ℝ) (B : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hRleft : R.comp (H - z • 1) = ContinuousLinearMap.id ℂ E)
    (hRright : (H - z • 1).comp R = ContinuousLinearMap.id ℂ E)
    (hBright : (V.adjoint.comp ((H - z • 1).comp V)).comp B
      = ContinuousLinearMap.id ℂ F)
    (hblock : (sirkComplement V).comp (A.comp (sirkReconstruction V)) = 0)
    (hH : H = A + g • W) (hz : z = -(lam : ℂ))
    (hcomm : H.comp (sirkComplement V) = (sirkComplement V).comp H)
    (hcoer : ∀ v : E, mu * ‖(sirkComplement V) v‖ ^ 2
      ≤ (inner ℂ ((sirkComplement V) v) (H ((sirkComplement V) v))).re)
    (hpos : 0 < mu + lam) :
    sirkTailBudget V R
      ≤ (2 * (‖g‖ * ‖W‖ * ‖sirkReconstruction V‖) * ‖B‖ + 1) * (mu + lam)⁻¹ := by
  have hQidem := sirkComplement_idem V hVV
  have hQadj := sirkComplement_adjoint_eq V
  have hP : sirkReconstruction V = ContinuousLinearMap.id ℂ E - sirkComplement V := by
    ext x
    simp [sirkComplement]
  have hcoupling := fock_coupling_le A W (sirkReconstruction V) (sirkComplement V) H g z
    hP hQidem hQadj hblock hH
  have hshift : H - z • 1 = H + (lam : ℂ) • 1 := by
    rw [hz]
    simp
  have hRinv : (H + (lam : ℂ) • 1).comp R = ContinuousLinearMap.id ℂ E := by
    rw [← hshift]
    exact hRright
  have htail : ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖ ≤ (mu + lam)⁻¹ :=
    fock_tail_le (sirkComplement V) H R mu lam hQidem hQadj hcomm hcoer hpos hRinv
  have hleak := sirkTailBudget_le_of_tail_coupling V (H - z • 1) R B hVV hViso hVadj
    hRleft hBright
  have hBnn : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have htnn : (0 : ℝ) ≤ (mu + lam)⁻¹ := by positivity
  have hmono : 2 * ‖(sirkComplement V).comp ((H - z • 1).comp (sirkReconstruction V))‖
        * ‖B‖ + 1
      ≤ 2 * (‖g‖ * ‖W‖ * ‖sirkReconstruction V‖) * ‖B‖ + 1 := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoupling (by norm_num : (0 : ℝ) ≤ 2)) hBnn
    linarith
  calc sirkTailBudget V R
      ≤ (2 * ‖(sirkComplement V).comp ((H - z • 1).comp (sirkReconstruction V))‖ * ‖B‖ + 1)
          * ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖ := hleak
    _ ≤ (2 * (‖g‖ * ‖W‖ * ‖sirkReconstruction V‖) * ‖B‖ + 1) * (mu + lam)⁻¹ := by
        refine mul_le_mul hmono htail (norm_nonneg _) ?_
        have h1 : 0 ≤ ‖g‖ * ‖W‖ * ‖sirkReconstruction V‖ :=
          mul_nonneg (mul_nonneg (norm_nonneg g) (norm_nonneg W))
            (norm_nonneg (sirkReconstruction V))
        have h2 : 0 ≤ 2 * (‖g‖ * ‖W‖ * ‖sirkReconstruction V‖) * ‖B‖ :=
          mul_nonneg (mul_nonneg (by norm_num) h1) hBnn
        linarith


/-! ## 14. What the commutation hypothesis really buys, and `O` without it

§13's `sirkTailBudget_le_fock` assumed `H Q = Q H`.  That hypothesis is not merely
unproved for a SIRK split — it is *inconsistent* with a nonzero coupling term, and
`comp_shift_eq_zero_of_comm` makes this formal: `H Q = Q H` forces
`Q (H − z) P = 0`, so the §13 bound always reads
`sirkTailBudget ≤ (1)·‖Q R Q‖` and never uses `‖g‖‖W‖`.  Exactly invariant splits are
the case SIRK exists to avoid, so §13 covers only the degenerate regime; the honest
statement of what invariance gives is `sirkTailBudget_le_of_invariant_split`.

The transfer allocation needs no invariance at all.  For `H = A + g·W` the triangle
inequality gives `‖(H − z) Q‖ ≤ ‖(A − z) Q‖ + ‖g‖‖W‖` (because `‖Q‖ ≤ 1`), so with
`alpha` the free part's norm on the discarded sector,
`sirkTransferBudget_le_fock` reads `O ≤ ‖B‖ (alpha + ‖g‖‖W‖) ‖R P‖` — affine in the
coupling and valid for every split.  §15 then replaces the *tail* hypothesis as well: the
Schur complement of the compressed shift controls `‖Q R Q‖` with no commutation at all.

-/



omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] in
/-- **Exact invariance kills the coupling block.**  If `H` commutes with the discarded
projection `Q`, the off-diagonal block of the shifted generator vanishes identically:
`Q (H − z) P = 0`.  So §13's commutation hypothesis forces the coupling term of
`sirkTailBudget_le_fock` to vanish: that lemma therefore describes the *exactly* invariant
split, not the Krylov split SIRK actually uses. -/
theorem comp_shift_eq_zero_of_comm (H Q : E →L[ℂ] E) (z : ℂ)
    (hQidem : Q.comp Q = Q) (hcomm : H.comp Q = Q.comp H) :
    Q.comp ((H - z • 1).comp (ContinuousLinearMap.id ℂ E - Q)) = 0 := by
  have hQP : Q.comp (ContinuousLinearMap.id ℂ E - Q) = 0 := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id, hQidem, sub_self]
  have hA : Q.comp (H.comp (ContinuousLinearMap.id ℂ E - Q)) = 0 := by
    rw [← ContinuousLinearMap.comp_assoc, ← hcomm, ContinuousLinearMap.comp_assoc, hQP]
    simp
  have hz : Q.comp ((z : ℂ) • (ContinuousLinearMap.id ℂ E - Q)) = 0 := by
    rw [ContinuousLinearMap.comp_smul, hQP, smul_zero]
  have hstep : (H - z • 1).comp (ContinuousLinearMap.id ℂ E - Q)
      = H.comp (ContinuousLinearMap.id ℂ E - Q)
        - (z : ℂ) • (ContinuousLinearMap.id ℂ E - Q) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_sub]
  rw [hstep, ContinuousLinearMap.comp_sub, hA, hz, sub_self]

/-- **What exact invariance actually delivers.**  Under `H Q = Q H` the tail budget loses its
coupling factor: `sirkTailBudget V R ≤ ‖Q R Q‖`.  This is the only regime where §13's
commutation hypothesis is consistent with a nonzero coupling, and there the coupling is zero. -/
theorem sirkTailBudget_le_of_invariant_split (V : F →L[ℂ] E) (H R : E →L[ℂ] E) (z : ℂ)
    (B : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hQidem : (sirkComplement V).comp (sirkComplement V) = sirkComplement V)
    (hcomm : H.comp (sirkComplement V) = (sirkComplement V).comp H)
    (hRleft : R.comp (H - z • 1) = ContinuousLinearMap.id ℂ E)
    (hBright : (V.adjoint.comp ((H - z • 1).comp V)).comp B
      = ContinuousLinearMap.id ℂ F) :
    sirkTailBudget V R ≤ ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖ := by
  have hzero := comp_shift_eq_zero_of_comm H (sirkComplement V) z hQidem hcomm
  have hP : sirkReconstruction V = ContinuousLinearMap.id ℂ E - sirkComplement V := by
    ext x
    simp [sirkComplement]
  have hleak := sirkTailBudget_le_of_tail_coupling V (H - z • 1) R B hVV hViso hVadj
    hRleft hBright
  rw [hP, hzero, norm_zero] at hleak
  simpa using hleak

/-- **`O` as a function of the coupling — no invariance assumed.**  For `H = A + g·W` the
transfer allocation splits by the triangle inequality alone:
`‖(H − z) Q‖ ≤ ‖(A − z) Q‖ + ‖g‖ ‖W‖`, since `‖Q‖ ≤ 1`.  Writing `alpha` for the free part's
norm on the discarded sector, `O ≤ ‖B‖ (alpha + ‖g‖‖W‖) ‖R P‖` — affine in the coupling, and
independent of whether the split is `H`-invariant.  This is the non-vacuous counterpart of
`sirkTailBudget_le_fock`'s commutation hypothesis. -/
theorem sirkTransferBudget_le_fock (V : F →L[ℂ] E) (A W H R : E →L[ℂ] E) (g z : ℂ)
    (B : F →L[ℂ] F) (alpha : ℝ)
    (hQidem : (sirkComplement V).comp (sirkComplement V) = sirkComplement V)
    (hQadj : (sirkComplement V).adjoint = sirkComplement V)
    (hH : H = A + g • W)
    (hfree : ‖(A - z • 1).comp (sirkComplement V)‖ ≤ alpha) :
    sirkTransferBudget V H R z B
      ≤ ‖B‖ * (alpha + ‖g‖ * ‖W‖) * ‖R.comp (sirkReconstruction V)‖ := by
  have hQ1 : ‖sirkComplement V‖ ≤ 1 :=
    opNorm_le_one_of_orthogonalProjection (sirkComplement V) hQidem hQadj
  have hsplit : H - z • 1 = (A - z • 1) + g • W := by
    rw [hH]
    abel
  have hcomp : (H - z • 1).comp (sirkComplement V)
      = (A - z • 1).comp (sirkComplement V)
        + g • (W.comp (sirkComplement V)) := by
    rw [hsplit, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp]
  have hW : ‖g • (W.comp (sirkComplement V))‖ ≤ ‖g‖ * ‖W‖ := by
    rw [norm_smul]
    have h1 : ‖W.comp (sirkComplement V)‖ ≤ ‖W‖ * 1 := by
      calc ‖W.comp (sirkComplement V)‖ ≤ ‖W‖ * ‖sirkComplement V‖ :=
            ContinuousLinearMap.opNorm_comp_le W _
        _ ≤ ‖W‖ * 1 := by gcongr
    nlinarith [norm_nonneg g, norm_nonneg W]
  have hbound : ‖(H - z • 1).comp (sirkComplement V)‖ ≤ alpha + ‖g‖ * ‖W‖ := by
    rw [hcomp]
    refine (norm_add_le _ _).trans ?_
    linarith
  rw [sirkTransferBudget]
  have hRP : (0 : ℝ) ≤ ‖R.comp (sirkReconstruction V)‖ := norm_nonneg _
  have h1 : ‖(H - z • 1).comp (sirkComplement V)‖ * ‖R.comp (sirkReconstruction V)‖
      ≤ (alpha + ‖g‖ * ‖W‖) * ‖R.comp (sirkReconstruction V)‖ :=
    mul_le_mul_of_nonneg_right hbound hRP
  calc ‖B‖ * (‖(H - z • 1).comp (sirkComplement V)‖ * ‖R.comp (sirkReconstruction V)‖)
      ≤ ‖B‖ * ((alpha + ‖g‖ * ‖W‖) * ‖R.comp (sirkReconstruction V)‖) := by
        gcongr
    _ = ‖B‖ * (alpha + ‖g‖ * ‖W‖) * ‖R.comp (sirkReconstruction V)‖ := by ring

/-! ## 15. The tail bound without invariance: Schur complement of the compressed shift

§13's `fock_tail_le` assumed `H Q = Q H`, and §14 shows that hypothesis is not merely unproved:
it forces `Q (H − z) P = 0`, i.e. it is inconsistent with the nonzero coupling of a SIRK split.
The invariant-free replacement is the Schur complement of the compressed shift.  With
`P = 1 − Q`, `A = H − z` and `U` a one-sided inverse of the `P`-block `P A P` on `range P`
(`U (P A P) = P`), the block equations of `A R = 1` give

`S (Q R Q) = Q`,  `S = Q A Q − (Q A P) U (P A Q)`,

so the tail is controlled by the coercivity gap of `S` alone:

* `schur_comp_eq`: the identity above, from `A R = 1` and `U (P A P) = P` — no commutation;
* `resolvent_tail_le_of_schur`: coercivity of `S` with gap `mu` gives `‖Q R Q‖ ≤ mu⁻¹`;
* `sirkTailBudget_le_fock_schur`: for `H = A + g•W`,
  `T ≤ (2‖g‖‖W‖‖P‖‖B‖ + 1) mu⁻¹`, with `mu` the gap of `S`.

The coupling is *nonzero* in this statement: it enters `S` through `(Q A P) U (P A Q)`, the
second-order term the perturbative expansion predicts, instead of being multiplied by zero. -/

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- **The Schur complement of the compressed shift inverts the compressed resolvent.**  Write
`P = 1 − Q`, `A = H − z`, and let `U` invert the `P`-block `P A P` on `range P`.  Then the Schur
complement `S = Q A Q − (Q A P) U (P A Q)` satisfies `S (Q R Q) = Q`: no commutation of `H` with
`Q` is used, and the coupling `Q A P` is allowed to be nonzero. -/
theorem schur_comp_eq (A R Q U : E →L[ℂ] E)
    (hQidem : Q.comp Q = Q) (hAR : A.comp R = ContinuousLinearMap.id ℂ E)
    (hU : U.comp ((ContinuousLinearMap.id ℂ E - Q).comp
      (A.comp (ContinuousLinearMap.id ℂ E - Q))) = ContinuousLinearMap.id ℂ E - Q) :
    ((Q.comp (A.comp Q))
      - (Q.comp (A.comp (ContinuousLinearMap.id ℂ E - Q))).comp
          (U.comp ((ContinuousLinearMap.id ℂ E - Q).comp (A.comp Q)))).comp
      (Q.comp (R.comp Q)) = Q := by
  set P : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - Q with hP
  have hQP : Q.comp P = 0 := by
    rw [hP, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id, hQidem, sub_self]
  have hPQ : P.comp Q = 0 := by
    rw [hP, ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp, hQidem, sub_self]
  have hPP : P.comp P = P := by
    rw [hP, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_comp, hQidem]
    abel
  have hsum : P + Q = ContinuousLinearMap.id ℂ E := by
    rw [hP]
    abel
  set R12 : E →L[ℂ] E := P.comp (R.comp Q) with hR12
  set R22 : E →L[ℂ] E := Q.comp (R.comp Q) with hR22
  have hR12P : P.comp R12 = R12 := by
    rw [hR12, ← ContinuousLinearMap.comp_assoc, hPP]
  have hR22Q : Q.comp R22 = R22 := by
    rw [hR22, ← ContinuousLinearMap.comp_assoc, hQidem]
  have hsplit : R.comp Q = R12 + R22 := by
    rw [hR12, hR22, ← ContinuousLinearMap.add_comp, hsum,
      ContinuousLinearMap.id_comp]
  have hA12 : (A.comp P).comp R12 = A.comp R12 := by
    rw [ContinuousLinearMap.comp_assoc, hR12P]
  have hA22 : (A.comp Q).comp R22 = A.comp R22 := by
    rw [ContinuousLinearMap.comp_assoc, hR22Q]
  have h4 : (Q.comp (A.comp P)).comp R12 + (Q.comp (A.comp Q)).comp R22 = Q := by
    have h0 : Q.comp (A.comp (R.comp Q)) = Q := by
      rw [← ContinuousLinearMap.comp_assoc A R Q, hAR, ContinuousLinearMap.id_comp]
      exact hQidem
    have step : Q.comp (A.comp R12) = (Q.comp (A.comp P)).comp R12 := by
      rw [← hA12, ← ContinuousLinearMap.comp_assoc]
    have step2 : Q.comp (A.comp R22) = (Q.comp (A.comp Q)).comp R22 := by
      rw [← hA22, ← ContinuousLinearMap.comp_assoc]
    rw [hsplit, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_add, step, step2] at h0
    exact h0
  have h2 : (P.comp (A.comp P)).comp R12 + (P.comp (A.comp Q)).comp R22 = 0 := by
    have h0 : P.comp (A.comp (R.comp Q)) = 0 := by
      rw [← ContinuousLinearMap.comp_assoc A R Q, hAR, ContinuousLinearMap.id_comp, hPQ]
    have step : P.comp (A.comp R12) = (P.comp (A.comp P)).comp R12 := by
      rw [← hA12, ← ContinuousLinearMap.comp_assoc]
    have step2 : P.comp (A.comp R22) = (P.comp (A.comp Q)).comp R22 := by
      rw [← hA22, ← ContinuousLinearMap.comp_assoc]
    rw [hsplit, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_add, step, step2] at h0
    exact h0
  have hR12eq : R12 = -((U.comp (P.comp (A.comp Q))).comp R22) := by
    have h2' : U.comp (((P.comp (A.comp P)).comp R12
        + (P.comp (A.comp Q)).comp R22)) = 0 := by
      rw [h2]
      exact ContinuousLinearMap.comp_zero U
    rw [ContinuousLinearMap.comp_add] at h2'
    have hU' : U.comp ((P.comp (A.comp P)).comp R12) = R12 := by
      rw [← ContinuousLinearMap.comp_assoc, hU, hR12P]
    rw [hU'] at h2'
    rw [← ContinuousLinearMap.comp_assoc]
    exact eq_neg_of_add_eq_zero_left h2'
  have hmain : ((Q.comp (A.comp Q))
      - (Q.comp (A.comp P)).comp (U.comp (P.comp (A.comp Q)))).comp R22 = Q := by
    rw [ContinuousLinearMap.sub_comp]
    have hinner : (U.comp (P.comp (A.comp Q))).comp R22 + R12 = 0 := by
      rw [hR12eq]
      abel
    have hz : ((Q.comp (A.comp P)).comp (U.comp (P.comp (A.comp Q)))).comp R22
        + (Q.comp (A.comp P)).comp R12 = 0 := by
      calc ((Q.comp (A.comp P)).comp (U.comp (P.comp (A.comp Q)))).comp R22
            + (Q.comp (A.comp P)).comp R12
          = (Q.comp (A.comp P)).comp ((U.comp (P.comp (A.comp Q))).comp R22)
            + (Q.comp (A.comp P)).comp R12 := by
              rw [ContinuousLinearMap.comp_assoc]
        _ = (Q.comp (A.comp P)).comp
              ((U.comp (P.comp (A.comp Q))).comp R22 + R12) := by
              rw [ContinuousLinearMap.comp_add]
        _ = 0 := by rw [hinner]; exact ContinuousLinearMap.comp_zero _
    have hs2 : ((Q.comp (A.comp P)).comp (U.comp (P.comp (A.comp Q)))).comp R22
        = -((Q.comp (A.comp P)).comp R12) := eq_neg_of_add_eq_zero_left hz
    rw [hs2, sub_neg_eq_add, add_comm]
    exact h4
  exact hmain
omit [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- **The tail bound from the Schur complement.**  If the Schur complement `S` of the compressed
shift is a right inverse of `Q R Q` — `S (Q R Q) = Q` — and is coercive on `range Q` with gap
`mu > 0`, then `‖Q R Q‖ ≤ mu⁻¹`.  No invariance of the splitting and no symmetry of `H` is
used: this replaces the commutation hypothesis of `fock_tail_le`. -/
theorem resolvent_tail_le_of_schur (Q R S : E →L[ℂ] E) (mu : ℝ)
    (hQidem : Q.comp Q = Q) (hQadj : Q.adjoint = Q)
    (hS : S.comp (Q.comp (R.comp Q)) = Q)
    (hcoer : ∀ v : E, mu * ‖Q v‖ ^ 2 ≤ (inner ℂ (Q v) (S (Q v))).re)
    (hpos : 0 < mu) : ‖Q.comp (R.comp Q)‖ ≤ mu⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  set w : E := Q x with hw
  set v : E := Q (R w) with hv
  have hQw : Q w = w := by
    rw [hw, ← ContinuousLinearMap.comp_apply, hQidem]
  have hQv : Q v = v := by
    rw [hv, ← ContinuousLinearMap.comp_apply, hQidem]
  have hfix : S v = w := by
    have h := congrArg (fun f : E →L[ℂ] E => f x) hS
    simpa [hv, hw, ContinuousLinearMap.comp_apply] using h
  have hinner : mu * ‖v‖ ^ 2 ≤ (inner ℂ v (S v)).re := by
    have := hcoer (R w)
    simpa [hv] using this
  have hquad : mu * ‖v‖ ^ 2 ≤ ‖v‖ * ‖x‖ := by
    have hre : (inner ℂ v (S v)).re = (inner ℂ v w).re := by rw [hfix]
    have h1 : mu * ‖v‖ ^ 2 ≤ (inner ℂ v w).re := by
      rw [← hre]
      exact hinner
    have h2 : (inner ℂ v w).re ≤ ‖v‖ * ‖w‖ :=
      (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
    have h3 : ‖w‖ ≤ ‖x‖ := by
      rw [hw]
      exact norm_projection_le Q hQidem hQadj x
    nlinarith [h1, h2, h3, norm_nonneg v, norm_nonneg x, norm_nonneg w]
  have hfinal : ‖v‖ ≤ mu⁻¹ * ‖x‖ := by
    rcases eq_or_lt_of_le (norm_nonneg v) with h0 | h0
    · rw [← h0]
      positivity
    · have hstep : mu * ‖v‖ ≤ ‖x‖ := by
        have h1 : mu * ‖v‖ * ‖v‖ ≤ ‖v‖ * ‖x‖ := by
          calc mu * ‖v‖ * ‖v‖ = mu * ‖v‖ ^ 2 := by ring
            _ ≤ ‖v‖ * ‖x‖ := hquad
        exact le_of_mul_le_mul_right (by simpa [mul_comm] using h1) h0
      calc ‖v‖ ≤ ‖x‖ / mu := by
            rw [le_div_iff₀ hpos]
            calc ‖v‖ * mu = mu * ‖v‖ := by ring
              _ ≤ ‖x‖ := hstep
        _ = mu⁻¹ * ‖x‖ := by rw [div_eq_inv_mul]
  have happ : (Q.comp (R.comp Q)) x = v := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hw]
  rw [happ]
  exact hfinal
/-- **§15: the Fock tail budget with no invariance hypothesis.**  The shift `z` now enters only
through the Schur complement `S = Q (H − z) Q − (Q (H − z) P) U (P (H − z) Q)`, whose coercivity
gap is `mu`: the coupling `Q (H − z) P = g · Q W P` is *allowed* to be nonzero, and is carried by
`‖g‖‖W‖‖P‖` exactly as in §13.  This is the non-degenerate replacement for
`sirkTailBudget_le_fock`. -/
theorem sirkTailBudget_le_fock_schur (V : F →L[ℂ] E) (A W H R S U : E →L[ℂ] E) (g z : ℂ)
    (mu : ℝ) (B : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hRleft : R.comp (H - z • 1) = ContinuousLinearMap.id ℂ E)
    (hRright : (H - z • 1).comp R = ContinuousLinearMap.id ℂ E)
    (hBright : (V.adjoint.comp ((H - z • 1).comp V)).comp B
      = ContinuousLinearMap.id ℂ F)
    (hblock : (sirkComplement V).comp (A.comp (sirkReconstruction V)) = 0)
    (hH : H = A + g • W)
    (hU : U.comp ((sirkReconstruction V).comp ((H - z • 1).comp (sirkReconstruction V)))
      = sirkReconstruction V)
    (hSdef : S = (sirkComplement V).comp ((H - z • 1).comp (sirkComplement V))
      - ((sirkComplement V).comp ((H - z • 1).comp (sirkReconstruction V))).comp
          (U.comp ((sirkReconstruction V).comp ((H - z • 1).comp (sirkComplement V)))))
    (hScoer : ∀ v : E, mu * ‖(sirkComplement V) v‖ ^ 2
      ≤ (inner ℂ ((sirkComplement V) v) (S ((sirkComplement V) v))).re)
    (hpos : 0 < mu) :
    sirkTailBudget V R
      ≤ (2 * (‖g‖ * ‖W‖ * ‖sirkReconstruction V‖) * ‖B‖ + 1) * mu⁻¹ := by
  have hQidem := sirkComplement_idem V hVV
  have hQadj := sirkComplement_adjoint_eq V
  have hP : sirkReconstruction V = ContinuousLinearMap.id ℂ E - sirkComplement V := by
    ext x
    simp [sirkComplement]
  have hcoupling := fock_coupling_le A W (sirkReconstruction V) (sirkComplement V) H g z
    hP hQidem hQadj hblock hH
  have hU' : U.comp ((ContinuousLinearMap.id ℂ E - sirkComplement V).comp
      ((H - z • 1).comp (ContinuousLinearMap.id ℂ E - sirkComplement V)))
      = ContinuousLinearMap.id ℂ E - sirkComplement V := by
    rw [← hP]
    exact hU
  have hSchur : S.comp ((sirkComplement V).comp (R.comp (sirkComplement V)))
      = sirkComplement V := by
    rw [hSdef, hP]
    exact schur_comp_eq (H - z • 1) R (sirkComplement V) U hQidem hRright hU'
  have htail : ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖ ≤ mu⁻¹ :=
    resolvent_tail_le_of_schur (sirkComplement V) R S mu hQidem hQadj hSchur hScoer hpos
  have hleak := sirkTailBudget_le_of_tail_coupling V (H - z • 1) R B hVV hViso hVadj
    hRleft hBright
  have hBnn : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have hmono : 2 * ‖(sirkComplement V).comp ((H - z • 1).comp (sirkReconstruction V))‖
        * ‖B‖ + 1
      ≤ 2 * (‖g‖ * ‖W‖ * ‖sirkReconstruction V‖) * ‖B‖ + 1 := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoupling (by norm_num : (0 : ℝ) ≤ 2)) hBnn
    linarith
  calc sirkTailBudget V R
      ≤ (2 * ‖(sirkComplement V).comp ((H - z • 1).comp (sirkReconstruction V))‖ * ‖B‖ + 1)
          * ‖(sirkComplement V).comp (R.comp (sirkComplement V))‖ := hleak
    _ ≤ (2 * (‖g‖ * ‖W‖ * ‖sirkReconstruction V‖) * ‖B‖ + 1) * mu⁻¹ := by
        refine mul_le_mul hmono htail (norm_nonneg _) ?_
        have h1 : 0 ≤ ‖g‖ * ‖W‖ * ‖sirkReconstruction V‖ :=
          mul_nonneg (mul_nonneg (norm_nonneg g) (norm_nonneg W))
            (norm_nonneg (sirkReconstruction V))
        have h2 : 0 ≤ 2 * (‖g‖ * ‖W‖ * ‖sirkReconstruction V‖) * ‖B‖ :=
          mul_nonneg (mul_nonneg (by norm_num) h1) hBnn
        linarith



/-! ## 16. The SIRK budget on a core: graph norms and the unbounded generator

§11–§15 need `H : E →L[ℂ] E`, while the concrete Yang–Mills Hamiltonian
`ymHamiltonian Φ fabc : D →ₗ[ℂ] L2d 99` is only a linear map on a dense core `D`.  A closed
operator is determined by its action there, so nothing is lost by carrying `D` explicitly and
measuring everything in the graph norm `‖u‖_G = ‖u‖ + ‖H u‖`.

The unbounded budget has the same two factors as the bounded one, with each factor read on the
core:

* **tail.**  The resolvent is a section `res : E → D` of `H − z`, solving `(H − z) res y = y`
  exactly, with a *vector-norm* bound `‖res y‖ ≤ mu⁻¹‖y‖` on the kept sector.  Because
  `H (res y) = y + z • res y`, the graph norm costs exactly one `‖z‖`:
  `‖res y‖_G ≤ (1 + ‖z‖)‖res y‖ + ‖y‖` (`graphNorm_res_le`), hence
  `‖Q R Q‖_G ≤ (1 + ‖z‖)mu⁻¹ + 1` (`sirkGraphTail_le`) — the analogue of `‖Q R Q‖ ≤ mu⁻¹`.
* **coupling.**  `Q (H − z) P` is no longer a continuous operator, but for a section
  `P : E → D` into the core it is pointwise defined, and only its norm on the discarded sector
  is needed: `‖Q ((H − z) (P x))‖ ≤ c` (`sirkGraphBudget_le`).

Composing the two gives `(2‖Q (H − z) P‖‖B‖ + 1)‖Q R Q‖_G ≤ (2c‖B‖ + 1)((1 + ‖z‖)mu⁻¹ + 1)`
times `‖x‖`.  What remains unproved is not analytic but physical: `mu` is the spectral gap of the
interacting complement, which this project does not claim, and the closedness needed to run the
resolvent at all is carried by the section `res` rather than derived. -/

/-- The graph norm on the core of an unbounded generator: `‖u‖ + ‖H u‖`. -/
def graphNorm {D : Submodule ℂ E} (H : D →ₗ[ℂ] E) (u : D) : ℝ :=
  ‖(u : E)‖ + ‖H u‖

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- The graph norm is nonnegative. -/
theorem graphNorm_nonneg {D : Submodule ℂ E} (H : D →ₗ[ℂ] E) (u : D) :
    0 ≤ graphNorm H u := by
  unfold graphNorm
  positivity

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- **The graph norm of a resolvent value is controlled by its vector norm.**  If `res y` solves
`(H − z) res y = y` exactly, then `H (res y) = y + z • res y`, so
`‖res y‖_G ≤ (1 + ‖z‖)‖res y‖ + ‖y‖`: on the core the graph norm costs one extra `‖z‖`, and
nothing else. -/
theorem graphNorm_res_le {D : Submodule ℂ E} {H : D →ₗ[ℂ] E} {res : E →ₗ[ℂ] D} {z : ℂ}
    (hres : ∀ y : E, H (res y) - z • ((res y : D) : E) = y) (y : E) :
    graphNorm H (res y) ≤ (1 + ‖z‖) * ‖((res y : D) : E)‖ + ‖y‖ := by
  have hH : H (res y) = y + z • ((res y : D) : E) := by
    have h := hres y
    rw [sub_eq_iff_eq_add] at h
    exact h
  have h1 : ‖H (res y)‖ ≤ ‖y‖ + ‖z‖ * ‖((res y : D) : E)‖ := by
    rw [hH]
    refine (norm_add_le _ _).trans ?_
    gcongr
    rw [norm_smul]
  unfold graphNorm
  nlinarith [norm_nonneg ((res y : D) : E), norm_nonneg y]

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] in
/-- **The resolvent estimate on the core, in graph norm.**  A vector-norm bound
`‖res y‖ ≤ mu⁻¹‖y‖` upgrades to `‖res y‖_G ≤ ((1 + ‖z‖)mu⁻¹ + 1)‖y‖`.  This is the step that
lets an unbounded generator — given only as a linear map on a core — carry a resolvent estimate
of the same shape as the bounded one. -/
theorem resolvent_graphNorm_le {D : Submodule ℂ E} {H : D →ₗ[ℂ] E} {res : E →ₗ[ℂ] D} {z : ℂ}
    {mu : ℝ} (hres : ∀ y : E, H (res y) - z • ((res y : D) : E) = y)
    (hvec : ∀ y : E, ‖((res y : D) : E)‖ ≤ mu⁻¹ * ‖y‖) (y : E) :
    graphNorm H (res y) ≤ ((1 + ‖z‖) * mu⁻¹ + 1) * ‖y‖ := by
  have h := graphNorm_res_le hres y
  have hb := hvec y
  have hz : (0 : ℝ) ≤ 1 + ‖z‖ := by positivity
  calc graphNorm H (res y)
      ≤ (1 + ‖z‖) * ‖((res y : D) : E)‖ + ‖y‖ := h
    _ ≤ (1 + ‖z‖) * (mu⁻¹ * ‖y‖) + ‖y‖ := by
        have h2 := mul_le_mul_of_nonneg_left hb hz
        linarith
    _ = ((1 + ‖z‖) * mu⁻¹ + 1) * ‖y‖ := by ring

/-- **The SIRK tail on the core, in graph norm.**  The kept sector is `range Q` with
`Q = sirkComplement V`; composing the resolvent section with `Q` costs nothing (`‖Q‖ ≤ 1`), so
the graph-norm tail of the compressed resolvent is at most
`((1 + ‖z‖)mu⁻¹ + 1)` — the unbounded analogue of `‖Q R Q‖ ≤ mu⁻¹`. -/
theorem sirkGraphTail_le (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    {D : Submodule ℂ E} {H : D →ₗ[ℂ] E} {res : E →ₗ[ℂ] D} {z : ℂ} {mu : ℝ}
    (hres : ∀ y : E, H (res y) - z • ((res y : D) : E) = y)
    (hvec : ∀ y : E, ‖((res y : D) : E)‖ ≤ mu⁻¹ * ‖y‖) (hmu : 0 < mu) (x : E) :
    graphNorm H (res ((sirkComplement V) x))
      ≤ ((1 + ‖z‖) * mu⁻¹ + 1) * ‖x‖ := by
  have hQidem := sirkComplement_idem V hVV
  have hQadj := sirkComplement_adjoint_eq V
  have hQle := norm_projection_le (sirkComplement V) hQidem hQadj x
  have h := resolvent_graphNorm_le hres hvec ((sirkComplement V) x)
  have hc : (0 : ℝ) ≤ (1 + ‖z‖) * mu⁻¹ + 1 := by positivity
  calc graphNorm H (res ((sirkComplement V) x))
      ≤ ((1 + ‖z‖) * mu⁻¹ + 1) * ‖(sirkComplement V) x‖ := h
    _ ≤ ((1 + ‖z‖) * mu⁻¹ + 1) * ‖x‖ := by
        exact mul_le_mul_of_nonneg_left hQle hc

/-- **The SIRK budget on a core, with graph norms.**  The coupling is read off the domain: for
`P` a section `E → D` into the core, the source term is `Q ((H − z) (P x))` and only its norm is
needed, `≤ c‖x‖`.  The budget is then the product of the coupling factor
`2‖Q (H − z) P‖‖B‖ + 1` and the graph-norm tail above.  This is the shape §11 gives for bounded
`H`, now with `H` merely a linear map on a core — the type of `ymHamiltonian`. -/
theorem sirkGraphBudget_le (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    {D : Submodule ℂ E} {H : D →ₗ[ℂ] E} {Pmap : E →ₗ[ℂ] D} {res : E →ₗ[ℂ] D}
    {z : ℂ} {mu c : ℝ} (B : F →L[ℂ] F)
    (hres : ∀ y : E, H (res y) - z • ((res y : D) : E) = y)
    (hvec : ∀ y : E, ‖((res y : D) : E)‖ ≤ mu⁻¹ * ‖y‖) (hmu : 0 < mu)
    (hB : (0 : ℝ) ≤ ‖B‖) (hc : 0 ≤ c)
    (hcoup : ∀ x : E, ‖(sirkComplement V) (H (Pmap x) - z • ((Pmap x : D) : E))‖ ≤ c)
    (x : E) :
    (2 * ‖(sirkComplement V) (H (Pmap x) - z • ((Pmap x : D) : E))‖ * ‖B‖ + 1)
        * graphNorm H (res ((sirkComplement V) x))
      ≤ (2 * c * ‖B‖ + 1) * (((1 + ‖z‖) * mu⁻¹ + 1) * ‖x‖) := by
  have htail := sirkGraphTail_le V hVV hres hvec hmu x
  have ht : (0 : ℝ) ≤ graphNorm H (res ((sirkComplement V) x)) := graphNorm_nonneg H _
  have hfac : 2 * ‖(sirkComplement V) (H (Pmap x) - z • ((Pmap x : D) : E))‖ * ‖B‖ + 1
      ≤ 2 * c * ‖B‖ + 1 := by
    have h1 := hcoup x
    have h2 : 0 ≤ ‖(sirkComplement V) (H (Pmap x) - z • ((Pmap x : D) : E))‖ := norm_nonneg _
    have h4 : 2 * ‖(sirkComplement V) (H (Pmap x) - z • ((Pmap x : D) : E))‖ * ‖B‖
        ≤ 2 * c * ‖B‖ := by
      have hm : ‖(sirkComplement V) (H (Pmap x) - z • ((Pmap x : D) : E))‖ * ‖B‖
          ≤ c * ‖B‖ := mul_le_mul h1 (le_refl ‖B‖) hB hc
      linarith [hm, h2]
    linarith
  have hbig : (2 * c * ‖B‖ + 1) * graphNorm H (res ((sirkComplement V) x))
      ≤ (2 * c * ‖B‖ + 1) * (((1 + ‖z‖) * mu⁻¹ + 1) * ‖x‖) := by
    have hk : (0 : ℝ) ≤ 2 * c * ‖B‖ + 1 := by nlinarith [hB, hc]
    exact mul_le_mul_of_nonneg_left htail hk
  have hk : (0 : ℝ) ≤ 2 * c * ‖B‖ + 1 := by nlinarith [hB, hc]
  calc (2 * ‖(sirkComplement V) (H (Pmap x) - z • ((Pmap x : D) : E))‖ * ‖B‖ + 1)
        * graphNorm H (res ((sirkComplement V) x))
      ≤ (2 * c * ‖B‖ + 1) * graphNorm H (res ((sirkComplement V) x)) := by
        exact mul_le_mul_of_nonneg_right hfac ht
    _ ≤ (2 * c * ‖B‖ + 1) * (((1 + ‖z‖) * mu⁻¹ + 1) * ‖x‖) := hbig

/-! ## 17. An explicit two-mode Yang–Mills model: block diagonality and coercivity

The abstract hypotheses of §11–§16 are met by an explicit truncation, so they are not empty.
The mode space is `EuclideanSpace ℂ (Fin 2)`; mode `0` is kept by the SIRK reconstruction and
mode `1` is the discarded block.  The free Hamiltonian is diagonal in the mode basis,
`freeMode w x = Σ_i (w i) • x_i e_i`, and `keepMode`, `discardMode` are the coordinate
projections.

* `freeMode_keep_discard`, `freeMode_discard_keep`: the free part is block diagonal — both
  off-diagonal blocks vanish, which is the `Q A P = 0` hypothesis (§13) and the `A21 = 0`
  special case of §15.
* `oscillator_coercive_discard`, `oscillator_coercive_keep`: on each block,
  `w i ‖x‖² ≤ Re⟪x, H_free x⟫` with the *explicit* gap `w i`.
* `oscillator_gap_discard`: a positive discarded frequency therefore supplies `mu > 0`
  (`mu = w 1`) as a witness, not a hypothesis.

What the model does not supply is the interacting gap: `mu > 0` for `H = H_free + g·W` is not
proved here, and the two-mode truncation is a toy model of the continuum operator. -/
abbrev YMMode : Type := EuclideanSpace ℂ (Fin 2)

/-- The free (mode-diagonal) Hamiltonian: frequency `w i` on mode `i`. -/
def freeMode (w : Fin 2 → ℝ) (x : YMMode) : YMMode :=
  WithLp.toLp 2 fun i => (w i : ℂ) * x.ofLp i

/-- Projection onto the kept mode `0`. -/
def keepMode (x : YMMode) : YMMode :=
  WithLp.toLp 2 fun i => if i = 0 then x.ofLp i else 0

/-- Projection onto the discarded mode `1`. -/
def discardMode (x : YMMode) : YMMode :=
  WithLp.toLp 2 fun i => if i = 0 then 0 else x.ofLp i

theorem freeMode_ofLp (w : Fin 2 → ℝ) (x : YMMode) (i : Fin 2) :
    (freeMode w x).ofLp i = (w i : ℂ) * x.ofLp i := by
  simp [freeMode]

theorem keepMode_ofLp (x : YMMode) (i : Fin 2) :
    (keepMode x).ofLp i = if i = 0 then x.ofLp i else 0 := by
  simp [keepMode]

theorem discardMode_ofLp (x : YMMode) (i : Fin 2) :
    (discardMode x).ofLp i = if i = 0 then 0 else x.ofLp i := by
  simp [discardMode]

/-- **The free part is block diagonal.**  A diagonal free Hamiltonian maps the discarded mode
into itself, so the off-diagonal block `keep (H_free (discard ·))` vanishes. -/
theorem freeMode_keep_discard (w : Fin 2 → ℝ) (x : YMMode) :
    keepMode (freeMode w (discardMode x)) = 0 := by
  ext i
  simp [keepMode_ofLp, freeMode_ofLp, discardMode_ofLp]
  by_cases h : i = 0 <;> simp [h]

theorem freeMode_discard_keep (w : Fin 2 → ℝ) (x : YMMode) :
    discardMode (freeMode w (keepMode x)) = 0 := by
  ext i
  simp [keepMode_ofLp, freeMode_ofLp, discardMode_ofLp]
  by_cases h : i = 0 <;> simp [h]

/-- The free action is `w 1` times the inner product on the discarded block. -/
theorem freeMode_inner_discard (w : Fin 2 → ℝ) (v : YMMode) :
    inner ℂ (discardMode v) (freeMode w (discardMode v))
      = (w 1 : ℂ) * inner ℂ (discardMode v) (discardMode v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Fin.sum_univ_two, freeMode_ofLp, discardMode_ofLp]
  norm_num
  ring

/-- **Oscillator coercivity on the discarded block**, with the explicit gap `mu = w 1`. -/
theorem oscillator_coercive_discard (w : Fin 2 → ℝ) (v : YMMode) :
    w 1 * ‖discardMode v‖ ^ 2
      ≤ (inner ℂ (discardMode v) (freeMode w (discardMode v))).re := by
  rw [freeMode_inner_discard, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hsq : (inner ℂ (discardMode v) (discardMode v)).re = ‖discardMode v‖ ^ 2 :=
    by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (discardMode v)
  rw [hsq]

/-- **Oscillator coercivity on the kept block**, gap `w 0`. -/
theorem oscillator_coercive_keep (w : Fin 2 → ℝ) (v : YMMode) :
    w 0 * ‖keepMode v‖ ^ 2
      ≤ (inner ℂ (keepMode v) (freeMode w (keepMode v))).re := by
  have hkey : inner ℂ (keepMode v) (freeMode w (keepMode v))
      = (w 0 : ℂ) * inner ℂ (keepMode v) (keepMode v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Fin.sum_univ_two, freeMode_ofLp, keepMode_ofLp]
    norm_num
    ring
  rw [hkey, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsq : (inner ℂ (keepMode v) (keepMode v)).re = ‖keepMode v‖ ^ 2 :=
    by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (keepMode v)
  rw [hsq]

/-- **A positive discarded frequency is a genuine gap.**  The coercivity of the model holds with
`mu = w 1 > 0`, which is exactly the `mu > 0` hypothesis of §13–§16, now witnessed by an explicit
finite model rather than assumed for the continuum theory. -/
theorem oscillator_gap_discard (w : Fin 2 → ℝ) (hw : 0 < w 1) :
    ∃ mu : ℝ, 0 < mu ∧ ∀ v : YMMode,
      mu * ‖discardMode v‖ ^ 2
        ≤ (inner ℂ (discardMode v) (freeMode w (discardMode v))).re :=
  ⟨w 1, hw, fun v => oscillator_coercive_discard w v⟩


/-! ## 18. §15 instantiated: a two-mode YM model with a nonzero coupling and an explicit gap

§17 checked the geometric hypotheses of §13–§16 on the *free* two-mode model, where the coupling
`Q A P` vanishes.  §15's point is that this is not needed, so here the coupling is switched on:
`H = H_free + g·W` with `W` the exchange of the two modes (`hamOp`).

* `discardOp_hamOp_keepOp_ne_zero`: `Q H P = g · (Q W) ≠ 0` for `g ≠ 0`, so §14's commutation
  hypothesis is genuinely false here, not merely unproved;
* `freeOp_discardOp_keepOp`, `freeOp_keepOp_discardOp`, `keepOp_freeOp_keepOp`,
  `discardOp_freeOp_discardOp`: the free part is block diagonal, `Q H_free P = P H_free Q = 0`;
* `keepOp_exchangeOp_keepOp`, `discardOp_exchangeOp_discardOp`: the interaction is purely
  off-diagonal, so the whole coupling sits in the `Q H P` block;
* `Uinv_comp`: `U = (w 0)⁻¹ P` is a one-sided inverse of `P H P = (w 0) P` on `range P`;
* `schurOp_eq`: the Schur complement collapses to `(w 1 − g²/w 0) • Q`.  The second-order
  downfolding term is exactly what the commuting bound of §13 could not see;
* `schur_identity`: §15's `schur_comp_eq` with this data, so the Schur complement inverts the
  compressed resolvent although the coupling does not vanish;
* `tail_le_schur`: §15's `resolvent_tail_le_of_schur`, giving `‖Q R Q‖ ≤ mu⁻¹` with the explicit
  gap `mu = schurGap w g = w 1 − g²/w 0`.

`resolventOp` is the genuine two-mode resolvent `Δ⁻¹ (w1 P + w0 Q − g W)`, `Δ = w0 w1 − g²`, and
`hamOp_comp_resolventOp` checks `H R = 1`: `R` is the actual inverse at the shift `z = 0`, not an
assumed operator.  The model is two-dimensional, so the gap is a number one can read off; the
continuum statement that this downfolded gap stays positive is not proved here. -/

noncomputable section
def diagOp (c : Fin 2 → ℂ) : YMMode →L[ℂ] YMMode :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => c i * x.ofLp i
      map_add' := by intro x y; ext i; simp [mul_add]
      map_smul' := by intro a x; ext i; simp [mul_left_comm] }

/-- Exchange of the two modes. -/
def exchangeOp : YMMode →L[ℂ] YMMode :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => x.ofLp (Equiv.swap 0 1 i)
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro a x; ext i; simp }

@[simp] theorem diagOp_ofLp (c : Fin 2 → ℂ) (x : YMMode) (i : Fin 2) :
    (diagOp c x).ofLp i = c i * x.ofLp i := by simp [diagOp]

@[simp] theorem exchangeOp_ofLp (x : YMMode) (i : Fin 2) :
    (exchangeOp x).ofLp i = x.ofLp (Equiv.swap (0 : Fin 2) 1 i) := by simp [exchangeOp]

theorem diagOp_congr {c d : Fin 2 → ℂ} (h : ∀ i, c i = d i) : diagOp c = diagOp d := by
  ext x i
  simp [h]

theorem diagOp_comp (c d : Fin 2 → ℂ) :
    (diagOp c).comp (diagOp d) = diagOp fun i => c i * d i := by
  ext x; simp [mul_assoc]

theorem diagOp_add (c d : Fin 2 → ℂ) : diagOp (c + d) = diagOp c + diagOp d := by
  ext x i; simp [add_mul]

@[simp] theorem diagOp_one : diagOp (fun _ => (1 : ℂ)) = ContinuousLinearMap.id ℂ YMMode := by
  ext x i; simp

theorem diagOp_zero : diagOp (fun _ => (0 : ℂ)) = 0 := by
  ext x i; simp

theorem diagOp_eq_zero {c : Fin 2 → ℂ} (h : ∀ i, c i = 0) : diagOp c = 0 :=
  (diagOp_congr h).trans diagOp_zero

theorem diagOp_smul (a : ℂ) (c : Fin 2 → ℂ) : diagOp (fun i => a * c i) = a • diagOp c := by
  ext x i; simp [mul_assoc]

theorem exchangeOp_comp_self :
    exchangeOp.comp exchangeOp = ContinuousLinearMap.id ℂ YMMode := by
  ext x i; simp [Equiv.swap_apply_self]

theorem exchangeOp_comp_diagOp (c : Fin 2 → ℂ) :
    exchangeOp.comp (diagOp c)
      = (diagOp fun i => c (Equiv.swap (0 : Fin 2) 1 i)).comp exchangeOp := by
  ext x i; simp

theorem diagOp_adjoint (c : Fin 2 → ℂ) :
    (diagOp c).adjoint = diagOp fun i => star (c i) := by
  have h : diagOp c = (diagOp fun i => star (c i)).adjoint := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Fin.sum_univ_two, diagOp_ofLp, Pi.star_apply, star_mul]
    ring_nf
  calc (diagOp c).adjoint
      = (ContinuousLinearMap.adjoint
          (ContinuousLinearMap.adjoint (diagOp fun i => star (c i)))) := by rw [h]
    _ = diagOp fun i => star (c i) := ContinuousLinearMap.adjoint_adjoint _

/-- Indicator of mode `0`. -/
def ind0 : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0

/-- Indicator of mode `1`. -/
def ind1 : Fin 2 → ℂ := fun i => if i = 0 then 0 else 1

noncomputable def keepOp : YMMode →L[ℂ] YMMode := diagOp ind0

noncomputable def discardOp : YMMode →L[ℂ] YMMode := diagOp ind1

noncomputable def freeOp (w : Fin 2 → ℝ) : YMMode →L[ℂ] YMMode := diagOp fun i => (w i : ℂ)

noncomputable def hamOp (w : Fin 2 → ℝ) (g : ℝ) : YMMode →L[ℂ] YMMode :=
  freeOp w + (g : ℂ) • exchangeOp

theorem keepOp_add_discardOp : keepOp + discardOp = ContinuousLinearMap.id ℂ YMMode := by
  rw [keepOp, discardOp, ← diagOp_add, ← diagOp_one]
  exact diagOp_congr (by intro i; fin_cases i <;> simp [ind0, ind1])

theorem keepOp_comp_discardOp : keepOp.comp discardOp = 0 := by
  rw [keepOp, discardOp, diagOp_comp]
  exact diagOp_eq_zero (by intro i; fin_cases i <;> simp [ind0, ind1])

theorem discardOp_comp_keepOp : discardOp.comp keepOp = 0 := by
  rw [keepOp, discardOp, diagOp_comp]
  exact diagOp_eq_zero (by intro i; fin_cases i <;> simp [ind0, ind1])

theorem keepOp_comp_self : keepOp.comp keepOp = keepOp := by
  rw [keepOp, diagOp_comp]
  exact diagOp_congr (by intro i; fin_cases i <;> simp [ind0])

theorem discardOp_comp_self : discardOp.comp discardOp = discardOp := by
  rw [discardOp, diagOp_comp]
  exact diagOp_congr (by intro i; fin_cases i <;> simp [ind1])

theorem keepOp_adjoint : keepOp.adjoint = keepOp := by
  rw [keepOp, diagOp_adjoint]
  exact diagOp_congr (by intro i; fin_cases i <;> simp [ind0])

theorem discardOp_adjoint : discardOp.adjoint = discardOp := by
  rw [discardOp, diagOp_adjoint]
  exact diagOp_congr (by intro i; fin_cases i <;> simp [ind1])

theorem freeOp_discardOp_keepOp : discardOp.comp ((freeOp w).comp keepOp) = 0 := by
  rw [discardOp, freeOp, keepOp, diagOp_comp, diagOp_comp]
  exact diagOp_eq_zero (by intro i; fin_cases i <;> simp [ind0, ind1])

theorem freeOp_keepOp_discardOp : keepOp.comp ((freeOp w).comp discardOp) = 0 := by
  rw [keepOp, freeOp, discardOp, diagOp_comp, diagOp_comp]
  exact diagOp_eq_zero (by intro i; fin_cases i <;> simp [ind0, ind1])

theorem keepOp_freeOp_keepOp :
    keepOp.comp ((freeOp w).comp keepOp) = (w 0 : ℂ) • keepOp := by
  rw [keepOp, freeOp, diagOp_comp, diagOp_comp, ← diagOp_smul]
  exact diagOp_congr (by intro i; fin_cases i <;> simp [ind0])

theorem discardOp_freeOp_discardOp :
    discardOp.comp ((freeOp w).comp discardOp) = (w 1 : ℂ) • discardOp := by
  rw [discardOp, freeOp, diagOp_comp, diagOp_comp, ← diagOp_smul]
  exact diagOp_congr (by intro i; fin_cases i <;> simp [ind1])

theorem keepOp_exchangeOp_keepOp : keepOp.comp (exchangeOp.comp keepOp) = 0 := by
  rw [keepOp]
  ext x i
  simp only [ContinuousLinearMap.comp_apply, diagOp_ofLp, exchangeOp_ofLp]
  fin_cases i <;> simp [ind0]

theorem discardOp_exchangeOp_discardOp :
    discardOp.comp (exchangeOp.comp discardOp) = 0 := by
  rw [discardOp]
  ext x i
  simp only [ContinuousLinearMap.comp_apply, diagOp_ofLp, exchangeOp_ofLp]
  fin_cases i <;> simp [ind1]

theorem discardOp_exchangeOp_keepOp :
    discardOp.comp (exchangeOp.comp keepOp) = discardOp.comp exchangeOp := by
  rw [discardOp]
  ext x i
  simp only [ContinuousLinearMap.comp_apply, diagOp_ofLp, exchangeOp_ofLp, keepOp]
  fin_cases i <;> simp [ind0, ind1]

theorem keepOp_exchangeOp_discardOp :
    keepOp.comp (exchangeOp.comp discardOp) = exchangeOp.comp discardOp := by
  rw [keepOp]
  ext x i
  simp only [ContinuousLinearMap.comp_apply, diagOp_ofLp, exchangeOp_ofLp, discardOp]
  fin_cases i <;> simp [ind0, ind1]

@[simp] theorem hamOp_ofLp (w : Fin 2 → ℝ) (g : ℝ) (x : YMMode) (i : Fin 2) :
    (hamOp w g x).ofLp i
      = (w i : ℂ) * x.ofLp i + (g : ℂ) * x.ofLp (Equiv.swap (0 : Fin 2) 1 i) := by
  simp [hamOp, freeOp]

theorem keepOp_hamOp_keepOp :
    keepOp.comp ((hamOp w g).comp keepOp) = (w 0 : ℂ) • keepOp := by
  rw [keepOp]
  ext x i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, diagOp_ofLp,
    hamOp_ofLp]
  fin_cases i <;> simp [ind0]

theorem discardOp_hamOp_discardOp :
    discardOp.comp ((hamOp w g).comp discardOp) = (w 1 : ℂ) • discardOp := by
  rw [discardOp]
  ext x i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, diagOp_ofLp,
    hamOp_ofLp]
  fin_cases i <;> simp [ind1]

theorem discardOp_hamOp_keepOp :
    discardOp.comp ((hamOp w g).comp keepOp) = (g : ℂ) • (discardOp.comp exchangeOp) := by
  rw [discardOp, keepOp]
  ext x i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, diagOp_ofLp,
    hamOp_ofLp]
  fin_cases i <;> simp [ind0, ind1]

theorem keepOp_hamOp_discardOp :
    keepOp.comp ((hamOp w g).comp discardOp) = (g : ℂ) • (exchangeOp.comp discardOp) := by
  rw [keepOp, discardOp]
  ext x i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, diagOp_ofLp,
    hamOp_ofLp]
  fin_cases i <;> simp [ind0, ind1]

/-- The unit vector of mode `i`. -/
def modeVec (i : Fin 2) : YMMode := EuclideanSpace.single i 1


theorem exchangeOp_modeVec (i : Fin 2) :
    exchangeOp (modeVec i) = modeVec (Equiv.swap (0 : Fin 2) 1 i) := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [modeVec]

theorem keepOp_modeVec_zero : keepOp (modeVec 0) = modeVec 0 := by
  ext j
  fin_cases j <;> simp [modeVec, keepOp, ind0]

theorem discardOp_modeVec_one : discardOp (modeVec 1) = modeVec 1 := by
  ext j
  fin_cases j <;> simp [modeVec, discardOp, ind1]

/-- **The coupling block is nonzero**, so §14's invariance hypothesis fails in this model and
§15's Schur-complement route is the relevant one. -/
theorem discardOp_hamOp_keepOp_ne_zero {w : Fin 2 → ℝ} {g : ℝ} (hg : g ≠ 0) :
    discardOp.comp ((hamOp w g).comp keepOp) ≠ 0 := by
  intro h
  rw [discardOp_hamOp_keepOp] at h
  have hx := congrArg (fun T : YMMode →L[ℂ] YMMode => T (modeVec 0)) h
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, exchangeOp_modeVec, discardOp_modeVec_one,
    Equiv.swap_apply_left] at hx
  have hnorm : ‖(((g : ℂ)) • modeVec 1 : YMMode)‖ = 0 := by rw [hx]; simp
  have h1 : ‖modeVec (1 : Fin 2)‖ = 1 := by simp [modeVec]
  rw [norm_smul, h1, mul_one] at hnorm
  exact hg (Complex.ofReal_eq_zero.mp (norm_eq_zero.mp hnorm))

/-- One-sided inverse of the kept block: `U = (w 0)⁻¹ P`, since `P (H) P = (w 0) • P`. -/
noncomputable def Uinv (w : Fin 2 → ℝ) : YMMode →L[ℂ] YMMode := ((w 0 : ℂ))⁻¹ • keepOp

theorem Uinv_comp (w : Fin 2 → ℝ) (g : ℝ) (hw0 : w 0 ≠ 0) :
    (Uinv w).comp (keepOp.comp ((hamOp w g).comp keepOp)) = keepOp := by
  have hc : (w 0 : ℂ) ≠ 0 := by simpa using hw0
  rw [Uinv, keepOp_hamOp_keepOp]
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, map_smul, ← ContinuousLinearMap.comp_apply,
    keepOp_comp_self, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The Schur complement of the compressed shifted Hamiltonian at `z = 0`. -/
noncomputable def schurOp (w : Fin 2 → ℝ) (g : ℝ) : YMMode →L[ℂ] YMMode :=
  discardOp.comp ((hamOp w g).comp discardOp)
    - (discardOp.comp ((hamOp w g).comp keepOp)).comp
        ((Uinv w).comp (keepOp.comp ((hamOp w g).comp discardOp)))

/-- The downfolded gap: the free discarded frequency shifted by the second-order coupling term. -/
noncomputable def schurGap (w : Fin 2 → ℝ) (g : ℝ) : ℝ := w 1 - g ^ 2 / w 0

theorem schurOp_eq (w : Fin 2 → ℝ) (g : ℝ) (hw0 : w 0 ≠ 0) :
    schurOp w g = ((schurGap w g : ℝ) : ℂ) • discardOp := by
  have hc : (w 0 : ℂ) ≠ 0 := by simpa using hw0
  rw [schurOp, discardOp_hamOp_discardOp, schurGap]
  push_cast
  ext x i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, WithLp.ofLp_smul, WithLp.ofLp_sub,
    Pi.smul_apply, Pi.sub_apply, diagOp_ofLp, hamOp_ofLp,
    keepOp, discardOp, Uinv]
  fin_cases i <;> simp [ind0, ind1, smul_eq_mul]
  field_simp

theorem schurOp_coercive (w : Fin 2 → ℝ) (g : ℝ) (hw0 : w 0 ≠ 0) :
    ∀ v : YMMode, schurGap w g * ‖discardOp v‖ ^ 2
      ≤ (inner ℂ (discardOp v) (schurOp w g (discardOp v))).re := by
  intro v
  have hidem : discardOp (discardOp v) = discardOp v := by
    rw [← ContinuousLinearMap.comp_apply, discardOp_comp_self]
  rw [schurOp_eq w g hw0, ContinuousLinearMap.smul_apply, hidem, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsq : (inner ℂ (discardOp v) (discardOp v)).re = ‖discardOp v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (discardOp v)
  rw [hsq]

/-- The explicit resolvent of the two-mode Hamiltonian at the shift `z = 0`. -/
noncomputable def resolventOp (w : Fin 2 → ℝ) (g : ℝ) : YMMode →L[ℂ] YMMode :=
  ((w 0 : ℂ) * (w 1 : ℂ) - (g : ℂ) ^ 2)⁻¹ •
    ((w 1 : ℂ) • keepOp + (w 0 : ℂ) • discardOp - (g : ℂ) • exchangeOp)

theorem hamOp_comp_resolventOp (w : Fin 2 → ℝ) (g : ℝ)
    (hΔ : (w 0 : ℂ) * (w 1 : ℂ) - (g : ℂ) ^ 2 ≠ 0) :
    (hamOp w g).comp (resolventOp w g) = ContinuousLinearMap.id ℂ YMMode := by
  have hΔ' : (w 1 : ℂ) * (w 0 : ℂ) - (g : ℂ) ^ 2 ≠ 0 := by
    rw [mul_comm (w 1 : ℂ) (w 0 : ℂ)]
    exact hΔ
  ext x i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    WithLp.ofLp_smul, WithLp.ofLp_add, WithLp.ofLp_sub, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, diagOp_ofLp, hamOp_ofLp, exchangeOp_ofLp, keepOp, discardOp, resolventOp]
  fin_cases i <;> simp [ind0, ind1, smul_eq_mul] <;> field_simp <;> ring

theorem keepOp_eq_one_sub : keepOp = ContinuousLinearMap.id ℂ YMMode - discardOp := by
  rw [eq_sub_iff_add_eq]
  exact keepOp_add_discardOp

/-- **§15's `schur_comp_eq` instantiated**: the explicit Schur complement of the two-mode model
inverts the compressed resolvent, although the coupling is nonzero. -/
theorem schur_identity (w : Fin 2 → ℝ) (g : ℝ) (hw0 : w 0 ≠ 0)
    (hΔ : (w 0 : ℂ) * (w 1 : ℂ) - (g : ℂ) ^ 2 ≠ 0) :
    (schurOp w g).comp (discardOp.comp ((resolventOp w g).comp discardOp)) = discardOp := by
  rw [schurOp, keepOp_eq_one_sub]
  refine schur_comp_eq (hamOp w g) (resolventOp w g) discardOp (Uinv w) discardOp_comp_self
    (hamOp_comp_resolventOp w g hΔ) ?_
  rw [← keepOp_eq_one_sub]
  exact Uinv_comp w g hw0

/-- **§15's `resolvent_tail_le_of_schur` instantiated**: the compressed resolvent of the toy model
is bounded by the reciprocal of the *explicit* gap `mu = w 1 − g²/w 0`, with no invariance
hypothesis. -/
theorem tail_le_schur (w : Fin 2 → ℝ) (g : ℝ) (hw0 : w 0 ≠ 0)
    (hΔ : (w 0 : ℂ) * (w 1 : ℂ) - (g : ℂ) ^ 2 ≠ 0) (hmu : 0 < schurGap w g) :
    ‖discardOp.comp ((resolventOp w g).comp discardOp)‖ ≤ (schurGap w g)⁻¹ :=
  resolvent_tail_le_of_schur discardOp (resolventOp w g) (schurOp w g) (schurGap w g)
    discardOp_comp_self discardOp_adjoint (schur_identity w g hw0 hΔ)
    (schurOp_coercive w g hw0) hmu


end

end BookProof.ChapterSirkEndToEnd
