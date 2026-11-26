import BookProof.Qym.ChapterYangMillsGaussSkewAdjoint

/-!
# The flow of the residual rotation, and the deficiency computation

`BookProof/Qym/ChapterYangMillsGaussSkewAdjoint.lean` reduces skew-adjointness of the Gauss
closure `Ā` to the reverse domain inclusion `dom Ā† ⊆ dom Ā`, and names the missing input:
a unitary flow `e^{tM}` of the linear colour rotation, or an elliptic-regularity estimate.
This module takes up the first of those.

## The concrete flow

The Gauss constraint is the first-order operator `𝒢_d = Σ_m v_m ∂_m` whose coefficient field
`v = ymGaussVec G d` is **linear** in the coordinates.  Two identities of
`ChapterYangMillsGaussSkew` are exactly what makes such a field a *rotation*:

* `sum_X_ymGaussVec` — `Σ_m x_m v_m = 0`: the field is tangent to the spheres, so the flow
  `x ↦ E(t) x` preserves `‖x‖` (`E(t)` is orthogonal);
* `sum_pderiv_ymGaussVec` (each `pderiv_ymGaussVec_self`) — `Σ_m ∂_m v_m = 0`: the flow is
  volume preserving.

Equivalently, the matrix `M` defined by `v_m = Σ_k M_{m k} x_k` is antisymmetric, the flow is
`E(t) = e^{-tM}`, and `E(t)` is a one-parameter group of rotations of `ℝ⁹⁹`.  Composing with
`E(t)` gives a one-parameter group `U(t)` of linear isometries of `L²(ℝ⁹⁹)`, and the
Gauss–polynomial core is invariant because `‖x‖` is preserved.  `𝒢_d` is the derivative of
that family at `t = 0`.

The two algebraic steps above are in the corpus.  What is *not* built here is the realisation
of `U(t)` as operators on `L²(ℝ⁹⁹)` (matrix exponential, change of variables, core
invariance, differentiability of `t ↦ U(t) f`).  That is the hypothesis bundle of the theorem
below — `U 0 = 1`, `‖U t‖ ≤ 1`, `U` maps the core into itself, and `t ↦ U t v` is
differentiable at every `t` with derivative `A (U t v)`, which is exactly "`A` is the
generator of `U` on the core".  Everything downstream of that input is proved; the two
deficiency spaces are computed.

## What the flow gives

`deficiency_eq_zero_of_flow` is the classical argument.  If `w` lies in the deficiency space
at the eigenvalue `c = ±1` of `Ā†` — that is, `⟪A v, w⟫ = c ⟪v, w⟫` for `v` in the core —
then `f t = ⟪U t v, w⟫` satisfies `f' = c f` at every `t`: the group law shifts the base
point, the derivative at the shifted point is the derivative at `0` applied to the core
vector `U t v`, and the eigenvalue equation applies to that vector.  So `f t = f 0 · e^{ct}`,
while `‖U t‖ ≤ 1` bounds `f` uniformly in `t`; hence `f 0 = 0`.  Since `v` ranges over a
dense core, `w = 0`.  This *discharges the deficiency-index input*: the flow proves
`ker(Ā† ∓ 1) = 0`.

## Boundary

* Only the deficiency spaces are computed.  Passing from `ker(Ā† ∓ 1) = 0` to
  `dom Ā† ⊆ dom Ā` is the range argument for `Ā ∓ 1` and is not in this module.
* The L² realisation of `U(t)` is not constructed; the flow enters as hypotheses and the
  module says so.
* `A` is a plain linear map on the core, not the closure: what is computed is
  `ker(A† ∓ 1)` for the operator on the core, which is the deficiency computation.  The
  identification with the closure's adjoint (`Ā† = A†` for a closable `A`) is a separate,
  standard step not taken here.
-/

namespace BookProof.Qym.GaussFlow

open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.Qym.GaussSkew
open BookProof.Qym.GaussClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## The deficiency computation -/

/-- **The flow kills the deficiency spaces at `±1`.**  Let `D` be a dense core, `A` the
charge on it, and `U` a one-parameter family of contractions preserving `D`, with derivative
`A` at `0` on `D`.  Then a vector `w` with `⟪A v, w⟫ = c ⟪v, w⟫` (`c = ±1`) on the core
vanishes. -/
theorem deficiency_eq_zero_of_flow {D : Submodule ℂ E} (hdense : Dense (D : Set E))
    (A : D →ₗ[ℂ] E) (U : ℝ → E →L[ℂ] E) (h0 : U 0 = 1)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1)
    (hmaps : ∀ (t : ℝ) (v : D), U t (v : E) ∈ D)
    (hgen : ∀ (v : D) (t : ℝ),
      HasDerivAt (fun s : ℝ => U s (v : E)) (A ⟨U t (v : E), hmaps t v⟩) t)
    (c : ℂ) (hc : c = 1 ∨ c = -1) {w : E}
    (hw : ∀ v : D, inner ℂ (A v) w = c * inner ℂ (v : E) w) : w = 0 := by
  refine Dense.eq_zero_of_inner_left (𝕜 := ℂ) hdense (fun v => ?_)
  -- derivative of the scalar function at `0`, for a core vector
  -- the derivative of the scalar function at each time, from the generator
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => inner ℂ (U s (v : E)) w)
      (c * inner ℂ (U t (v : E)) w) t := by
    intro t
    have hzt : U t (v : E) ∈ D := hmaps t v
    have h1 : HasDerivAt (fun s : ℝ => inner ℂ (U s (v : E)) w)
        (inner ℂ (A ⟨U t (v : E), hzt⟩) w) t := by
      have hg := hgen v t
      have h2 : HasDerivAt (fun _ : ℝ => w) (0 : E) t := hasDerivAt_const t w
      simpa using hg.inner (𝕜 := ℂ) h2
    rw [hw ⟨U t (v : E), hzt⟩] at h1
    exact h1
  -- the exponential comparison function has derivative zero
  have hG : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => inner ℂ (U s (v : E)) w * Complex.exp (-(c * (s : ℂ)))) 0 t := by
    intro t
    have h1 := hderiv t
    have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-(c * (s : ℂ))))
        (Complex.exp (-(c * (t : ℂ))) * (-c)) t := by
      have hidc : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
        simpa using Complex.ofRealCLM.hasDerivAt (x := t)
      have hlin : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-c) t := by
        simpa using (hidc.const_mul c).neg
      simpa using hlin.cexp
    have hmul := h1.mul hexp
    convert hmul using 1
    ring
  have hdiff : Differentiable ℝ
      (fun s : ℝ => inner ℂ (U s (v : E)) w * Complex.exp (-(c * (s : ℂ)))) :=
    fun t => (hG t).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t => (hG t).deriv) 0
  -- from the constancy: `f 0 = f t · e^{-c t}`
  have hval : ∀ t : ℝ, inner ℂ (v : E) w
      = inner ℂ (U t (v : E)) w * Complex.exp (-(c * (t : ℂ))) := by
    intro t
    have h := hconst t
    simpa [h0, mul_comm] using h
  -- uniform bound from `‖U t‖ ≤ 1`
  have hbound : ∀ t : ℝ, ‖inner ℂ (U t (v : E)) w‖ ≤ ‖(v : E)‖ * ‖w‖ := by
    intro t
    have h1 : ‖U t (v : E)‖ ≤ ‖(v : E)‖ := by
      have hle := (U t).le_opNorm (v : E)
      have h2 : ‖U t‖ * ‖(v : E)‖ ≤ 1 * ‖(v : E)‖ :=
        mul_le_mul_of_nonneg_right (hnorm t) (norm_nonneg _)
      linarith
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg w))
  have hnormexp : ∀ x : ℝ, ‖Complex.exp ((x : ℝ) : ℂ)‖ = Real.exp x := by
    intro x
    rw [Complex.norm_exp, Complex.ofReal_re]
  -- the exponential decay: `‖⟪v, w⟫‖ ≤ bound · e^{-n}`
  have hdecay : ∀ n : ℕ,
      ‖inner ℂ (v : E) w‖ ≤ ‖(v : E)‖ * ‖w‖ * Real.exp (-(n : ℝ)) := by
    intro n
    rcases hc with rfl | rfl
    · have h := hval ((n : ℝ))
      have harg : -((1 : ℂ) * (((n : ℝ)) : ℂ)) = ((-(n : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, norm_mul, harg, hnormexp]
      exact mul_le_mul_of_nonneg_right (hbound _) (Real.exp_nonneg _)
    · have h := hval (-(n : ℝ))
      have harg : -((-1 : ℂ) * ((-(n : ℝ) : ℝ) : ℂ)) = ((-(n : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h, norm_mul, harg, hnormexp]
      exact mul_le_mul_of_nonneg_right (hbound _) (Real.exp_nonneg _)
  have hlim : Filter.Tendsto
      (fun n : ℕ => ‖(v : E)‖ * ‖w‖ * Real.exp (-(n : ℝ))) Filter.atTop (nhds 0) := by
    have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa using hexp.const_mul (‖(v : E)‖ * ‖w‖)
  have hzero : ‖inner ℂ (v : E) w‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hdecay)
  have h0' : inner ℂ (v : E) w = 0 := norm_le_zero_iff.1 hzero
  have hconj := congrArg (starRingEnd ℂ) (inner_conj_symm w (v : E))
  rw [h0', map_zero] at hconj
  have hfin := congrArg (starRingEnd ℂ) hconj
  simpa using hfin.symm

/-! ## The two signs -/

/-- The deficiency space of `A†` at `1` is trivial, given the flow. -/
theorem deficiency_one_eq_zero_of_flow {D : Submodule ℂ E} (hdense : Dense (D : Set E))
    (A : D →ₗ[ℂ] E) (U : ℝ → E →L[ℂ] E) (h0 : U 0 = 1)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1)
    (hmaps : ∀ (t : ℝ) (v : D), U t (v : E) ∈ D)
    (hgen : ∀ (v : D) (t : ℝ),
      HasDerivAt (fun s : ℝ => U s (v : E)) (A ⟨U t (v : E), hmaps t v⟩) t)
    {w : E} (hw : ∀ v : D, inner ℂ (A v) w = inner ℂ (v : E) w) : w = 0 :=
  deficiency_eq_zero_of_flow hdense A U h0 hnorm hmaps hgen 1 (Or.inl rfl)
    (by simpa using hw)

/-- The deficiency space of `A†` at `-1` is trivial, given the flow. -/
theorem deficiency_neg_one_eq_zero_of_flow {D : Submodule ℂ E} (hdense : Dense (D : Set E))
    (A : D →ₗ[ℂ] E) (U : ℝ → E →L[ℂ] E) (h0 : U 0 = 1)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1)
    (hmaps : ∀ (t : ℝ) (v : D), U t (v : E) ∈ D)
    (hgen : ∀ (v : D) (t : ℝ),
      HasDerivAt (fun s : ℝ => U s (v : E)) (A ⟨U t (v : E), hmaps t v⟩) t)
    {w : E} (hw : ∀ v : D, inner ℂ (A v) w = -inner ℂ (v : E) w) : w = 0 := by
  refine deficiency_eq_zero_of_flow hdense A U h0 hnorm hmaps hgen (-1) (Or.inr rfl) ?_
  intro v
  rw [hw v]
  ring

/-! ## The Gauss constraint

The concrete instance: `A` is the Gauss constraint `𝒢_d` on the Gauss–polynomial core, and
the flow is the residual colour rotation.  The hypotheses of these theorems are the L²
realisation of that rotation. -/

variable {D : Submodule ℂ (L2d 99)}

/-- **The flow kills the deficiency spaces of the Gauss constraint.**  With `A` the Gauss
constraint on the core, a vector in `ker(𝒢_d† ∓ 1)` vanishes as soon as the residual rotation
acts on `L²(ℝ⁹⁹)` as a contraction family preserving the core and generated by `𝒢_d`. -/
theorem gaussPMap_deficiency_eq_zero_of_flow (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99)))
    (U : ℝ → L2d 99 →L[ℂ] L2d 99) (h0 : U 0 = 1) (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1)
    (hmaps : ∀ (t : ℝ) (v : (gaussPMap G d Φ).domain),
      U t (v : L2d 99) ∈ (gaussPMap G d Φ).domain)
    (hgen : ∀ (v : (gaussPMap G d Φ).domain) (t : ℝ),
      HasDerivAt (fun s : ℝ => U s (v : L2d 99))
        ((gaussPMap G d Φ) ⟨U t (v : L2d 99), hmaps t v⟩) t)
    (w : L2d 99)
    (hw₁ : ∀ v : (gaussPMap G d Φ).domain,
      inner ℂ ((gaussPMap G d Φ) v) w = inner ℂ (v : L2d 99) w) : w = 0 :=
  deficiency_one_eq_zero_of_flow hD (gaussPMap G d Φ).toFun U h0 hnorm hmaps hgen hw₁

/-- The concrete field-space instance: the core is the Gauss–polynomial core of
`L²(ℝ⁹⁹)`. -/
theorem gaussPMap_polyGaussCore_deficiency_eq_zero_of_flow (G : GaugeAlgebra 8) (d : Fin 8)
    (U : ℝ → L2d 99 →L[ℂ] L2d 99) (h0 : U 0 = 1) (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1)
    (hmaps : ∀ (t : ℝ) (v : (gaussPMap G d (coreRepPoly 99)).domain),
      U t (v : L2d 99) ∈ (gaussPMap G d (coreRepPoly 99)).domain)
    (hgen : ∀ (v : (gaussPMap G d (coreRepPoly 99)).domain) (t : ℝ),
      HasDerivAt (fun s : ℝ => U s (v : L2d 99))
        ((gaussPMap G d (coreRepPoly 99)) ⟨U t (v : L2d 99), hmaps t v⟩) t)
    (w : L2d 99)
    (hw₁ : ∀ v : (gaussPMap G d (coreRepPoly 99)).domain,
      inner ℂ ((gaussPMap G d (coreRepPoly 99)) v) w = inner ℂ (v : L2d 99) w) : w = 0 :=
  deficiency_one_eq_zero_of_flow polyGaussCore_dense
    (gaussPMap G d (coreRepPoly 99)).toFun U h0 hnorm hmaps hgen hw₁

end

end BookProof.Qym.GaussFlow
