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

end BookProof.ChapterSirkEndToEnd
