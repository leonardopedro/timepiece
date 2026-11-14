import Mathlib
import BookProof.Sirk.ChapterHashimotoShiftInvert
import BookProof.Sirk.ChapterSirkEndToEnd
import BookProof.Sirk.ChapterSpectralSplitting

/-!
# Chapter ResolventTransfer — moving a certified gap from `X_γ` to `h_F`

The mass-gap route runs its certificate on the Hashimoto shift-invert
`X_γ = (A + γ)⁻¹` rather than on `A` itself, because `X_γ` is bounded
(`ChapterHashimotoShiftInvert`) and because the SIRK error bound is an error in
`X_γ`.  Two transfers are then needed, and this chapter states and proves them:

* **the eigenvalue transfer.**  If `A y = e y` then `X_γ y = (e + γ)⁻¹ y`, so the
  *reflected* operator `A' := γ⁻¹ 1 − X_γ` has the same eigenvector with
  eigenvalue

  `λ' = γ⁻¹ − (e + γ)⁻¹ = e / (γ (e + γ))`   (`resolventEdge`),

  which is increasing in `e`.  That is why Temple's inequality — a statement
  about the **bottom** of the spectrum — can be run on `A'` at all: reflection
  reverses the order, so the edge of `X_γ` becomes an edge of `A'`.

* **the gap transfer.**  `g = (e₁ − e₀) ≥ γ² (λ'₁ − λ'₀) = γ² g_{X_γ}`:
  the eigenvalues are close to `γ⁻¹` on the scale of `γ`, so a resolvent gap
  shrinks by at most `γ²` when read back on `A`.

* **the assembly.**  `sirk_reflected_gap_certificate` moves the SIRK residual seam
  from `X_γ` to `A'` (`sirk_resid_reflection_le`): a residual measured against
  a multiple of the vector survives the reflection untouched, since
  `A' x − (γ⁻¹ − c) x = −(X_γ x − c x)`.  Temple on `A'` then certifies its
  bottom edge from the order-`m` data alone, and `γ² λ' ≤ e` reads the
  certificate back on `A`.

Nothing here needs a spectral theorem: both are arithmetic on eigenvalues plus
the two algebraic identities the shift-invert satisfies.  What is *not* proved
here is the spectral separation of `A` itself — `sirk_reflected_gap_certificate` takes it as
an input, and `sirk_reflected_gap_certificate_of_compression` *derives* it from a form bound

  `b ‖z‖² ≤ re ⟪z, A' z⟫`  for every `z ∈ yᗮ`,

through the compression of `A'` to `yᗮ` (`SpectralSplitting.compressed`): the compression is
self-adjoint, so `le_rayleigh_iff_le_spectrum` bounds its spectrum, and
`spectrum_subset_union_compressed` carries that back to `A'` with `λ'` covering the line.  The
older deflated form of the input is retired: `A' ∘ Q` annihilates the eigenvector, so `0` is
always in its spectrum (`zero_mem_spectrum_deflated`) and that hypothesis forces `b ≤ 0`.

Finally, the whole input is fed from the shift-invert itself: `A' = γ⁻¹ 1 − R` differs from the
scalar `γ⁻¹` by exactly `R`, so `reflected_norm_sub_smul_one_le` turns any bound `‖R‖ ≤ γ⁻¹ - b`
into the norm hypothesis of the one-step route, and the certificate
`sirk_reflected_gap_certificate_of_shiftInvertNorm` derives `hsep` from that bound and nothing
else.  The generic
per-system bound `IsShiftInvert.opNorm_le` (`‖R‖ ≤ γ⁻¹`) gives the `b = 0` endpoint
(`reflected_norm_sub_smul_one_le_inv`); a positive `b` is exactly a strict improvement on it.
A known bottom edge supplies one.  `IsShiftInvert.opNorm_le_edge` gives `‖R‖ ≤ (e + γ)⁻¹`,
which is `γ⁻¹ - resolventEdge γ e` (`sub_resolventEdge_eq_inv`), so
`sirk_reflected_gap_certificate_of_bottomEdge` runs at the level `b = resolventEdge γ e` —
positive whenever the ground-state energy is (`resolventEdge_pos`).  The two-sided form is
`sirk_reflected_temple_band_of_shiftInvertNorm`: Temple's lower bound together with
Rayleigh–Ritz's upper bound encloses `sInf (spectrum ℝ A')`, and the separation pins that edge
at `λ'` (`sInf ... = resolventEdge γ e`).  All of it comes from the single hypothesis
`e ‖x‖² ≤ re ⟪x, A x⟫` on the domain of `A`.

The two inputs are two *branches of one type*.  `ReflectedSeparationSource` says that the caller
has either a bottom edge `e` on the domain of `A` or a form bound on the compression of `A'` to
`yᗮ`; `spectralSeparation_of_source` discharges either branch into the same
`SpectralSeparation A' (resolventEdge γ e) b`, and `sirk_reflected_gap_certificate_of_source`
consumes it.  The bottom edge is not something positivity and an eigenvector can supply:
`bottomEdge_not_implied_by_positivity` exhibits `diag (5, 2)` as a positive operator with a
certified unit eigenvector at `5` on which the bottom-edge hypothesis at `5` fails, because the
edge is the bottom of the spectrum and an eigenvector pins one point of it.
-/
noncomputable section

namespace BookProof.ChapterResolventTransfer

open BookProof.HashimotoShiftInvert

/-! ## 1. The reflected edge `e ↦ e / (γ (e + γ))` -/

/-- The **reflected edge**: the eigenvalue of `A' = γ⁻¹ 1 − (A + γ)⁻¹` belonging
to an eigenvector of `A` with eigenvalue `e`. -/
def resolventEdge (γ e : ℝ) : ℝ := e / (γ * (e + γ))

@[simp] theorem resolventEdge_def (γ e : ℝ) : resolventEdge γ e = e / (γ * (e + γ)) := rfl

/-- The reflected edge is `γ⁻¹ − (e + γ)⁻¹`, the eigenvalue of
`γ⁻¹ 1 − X_γ`. -/
theorem resolventEdge_eq {γ e : ℝ} (hγ : γ ≠ 0) (he : e + γ ≠ 0) :
    resolventEdge γ e = γ⁻¹ - (e + γ)⁻¹ := by
  rw [resolventEdge_def]
  field_simp
  ring

/-- **Reflection is strictly increasing on `[0, ∞)`.**  This is what makes `A'`
usable for a *bottom*-edge certificate: the ordering of the eigenvalues is the
same, so `X_γ`'s top edge becomes `A'`'s bottom edge. -/
theorem resolventEdge_strictMonoOn {γ : ℝ} (hγ : 0 < γ) :
    StrictMonoOn (resolventEdge γ) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := hb
  have hga : 0 < γ * (a + γ) := by positivity
  have hgb : 0 < γ * (b + γ) := by positivity
  rw [resolventEdge_def, resolventEdge_def, div_lt_div_iff₀ hga hgb]
  nlinarith [mul_lt_mul_of_pos_left hab hγ]

/-- The reflected edge of `0` is `0`: the vacuum stays at the bottom. -/
@[simp] theorem resolventEdge_zero (γ : ℝ) : resolventEdge γ 0 = 0 := by
  simp [resolventEdge_def]

/-- **Read the edge back.**  `λ = e/(γ(e+γ))` is inverted by
`e = λ γ² / (1 − λ γ)`; the denominator is positive precisely because
`λ < γ⁻¹`. -/
theorem resolventEdge_inv {γ e : ℝ} (hγ : 0 < γ) (he : 0 ≤ e) :
    resolventEdge γ e * γ ^ 2 / (1 - resolventEdge γ e * γ) = e := by
  have hγne : γ ≠ 0 := ne_of_gt hγ
  have hpos : 0 < e + γ := by linarith
  rw [resolventEdge_def]
  field_simp
  rw [show e + γ - e = γ by ring]
  exact mul_div_cancel_right₀ e hγne

/-! ## 2. The gap transfer -/

/-- The reflected gaps are the original gaps rescaled by the product of the two
shifted eigenvalues. -/
theorem resolventEdge_sub {γ e₀ e₁ : ℝ} (hγ : 0 < γ) (h0 : 0 ≤ e₀) (hle : e₀ ≤ e₁) :
    resolventEdge γ e₁ - resolventEdge γ e₀
      = (e₁ - e₀) / ((e₀ + γ) * (e₁ + γ)) := by
  have ha : 0 < e₀ + γ := by linarith
  have hb : 0 < e₁ + γ := by linarith
  rw [resolventEdge_def, resolventEdge_def]
  field_simp
  ring

/-- **The gap transfer `g ≥ γ² g_X`.**

For `0 ≤ e₀ ≤ e₁` and `γ > 0`, the gap of `A` is at least `γ²` times the gap of
`X_γ = (A + γ)⁻¹`.  The constant is sharp in the scaling limit `e₀ = e₁ = 0`.

Consequently a certified resolvent gap `g_X` yields the certified gap `γ² g_X`
of the (selected) operator, and the separation needed by Temple transfers with
the same factor. -/
theorem gap_transfer {γ e₀ e₁ : ℝ} (hγ : 0 < γ) (h0 : 0 ≤ e₀) (hle : e₀ ≤ e₁) :
    γ ^ 2 * (resolventEdge γ e₁ - resolventEdge γ e₀) ≤ e₁ - e₀ := by
  have hprod : γ ^ 2 ≤ (e₀ + γ) * (e₁ + γ) := by nlinarith
  have hden : 0 < (e₀ + γ) * (e₁ + γ) := by
    have : 0 < e₀ + γ := by linarith
    have hb : 0 < e₁ + γ := by linarith
    positivity
  have hgap : 0 ≤ e₁ - e₀ := by linarith
  rw [resolventEdge_sub hγ h0 hle]
  rw [mul_div_assoc', div_le_iff₀ hden]
  nlinarith

/-! ## 3. The eigenvector transfer through the shift-invert -/

section Eigenvector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {Dom : Submodule ℂ E}

/-- **The shift-invert acts on an eigenvector by `(e + γ)⁻¹`.**  Only the two
algebraic identities of `IsShiftInvert` and the eigenvector equation are used. -/
theorem shiftInvert_apply_eigenvector {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) {y : E} (hy : y ∈ Dom) {e : ℝ}
    (heig : A ⟨y, hy⟩ = (e : ℂ) • y) (he : e + γ ≠ 0) :
    R y = ((e + γ)⁻¹ : ℝ) • y := by
  have h1 : shiftMap A γ ⟨y, hy⟩ = ((e + γ : ℝ) : ℂ) • y := by
    rw [shiftMap_apply, heig, ← add_smul]
    push_cast
    rfl
  have h2 : ((e + γ : ℝ) : ℂ) • R y = y := by
    have h := hR.1 ⟨y, hy⟩
    rw [h1, map_smul] at h
    exact h
  have h3 : R y = (((e + γ : ℝ) : ℂ))⁻¹ • y := by
    calc R y = (((e + γ : ℝ) : ℂ))⁻¹ • (((e + γ : ℝ) : ℂ) • R y) := by
          rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast he), one_smul]
      _ = (((e + γ : ℝ) : ℂ))⁻¹ • y := by rw [h2]
  rw [h3, ← Complex.ofReal_inv]
  set x : ℝ := (e + γ)⁻¹
  simp

/-- **The reflected operator `A' = γ⁻¹ 1 − X_γ` keeps the eigenvector.**  Its
eigenvalue is the reflected edge `e/(γ(e+γ))`, which is the *bottom* edge of `A'`
when `e` is the bottom edge of `A`. -/
theorem resolvent_reflection_eigenvector {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) {y : E} (hy : y ∈ Dom) {e : ℝ}
    (he : 0 ≤ e) (heig : A ⟨y, hy⟩ = (e : ℂ) • y) :
    ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) y = (resolventEdge γ e : ℂ) • y := by
  have hpos : 0 < e + γ := by linarith
  have hRy : R y = ((e + γ)⁻¹ : ℝ) • y :=
    shiftInvert_apply_eigenvector hR hy heig (ne_of_gt hpos)
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, hRy, ← sub_smul]
  have hcoef : γ⁻¹ - (e + γ)⁻¹ = resolventEdge γ e :=
    (resolventEdge_eq (ne_of_gt hγ) (ne_of_gt hpos)).symm
  rw [hcoef]
  set c : ℝ := resolventEdge γ e
  simp

end Eigenvector


/-! ## 4. The assembly: the SIRK error is a certificate on the reflected operator -/

section Reflected

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ E}

/-- The reflected operator `A' = γ⁻¹ 1 − X_γ` is self-adjoint whenever the
shift-invert is. -/
theorem isSelfAdjoint_reflection (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (γ : ℝ) :
    IsSelfAdjoint ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) := by
  have h := BookProof.RitzCertificate.isSelfAdjoint_sub_const hR γ⁻¹
  simpa [neg_sub] using h.neg

/-- **A residual survives the reflection unchanged.**

For a unit vector `x`, the `A'`-residual of `x` is at most `‖X_γ x − c x‖` for
*any* real `c` — the same bound `resid_le_norm_sub_smul` gives for `X_γ` itself.
The reason is that `A' x − (γ⁻¹ − c) x = −(X_γ x − c x)`, so reflecting only
moves the scalar: nothing is lost, and the SIRK operator-norm error becomes a
Temple residual on the operator Temple is actually run on. -/
theorem resid_reflection_le (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) {γ : ℝ} {x : E}
    (hx : ‖x‖ = 1) (c : ℝ) :
    BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) x
      ≤ ‖R x - (c : ℂ) • x‖ := by
  have hvec : ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) x - ((γ⁻¹ - c : ℝ) : ℂ) • x
      = -(R x - (c : ℂ) • x) := by
    have hone : ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E)) x = (((γ⁻¹ : ℝ) : ℂ)) • x := by
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
      simpa using (IsScalarTower.smul_assoc (γ⁻¹ : ℝ) (1 : ℂ) x).symm
    have hsub : ((γ⁻¹ - c : ℝ) : ℂ) • x = ((γ⁻¹ : ℝ) : ℂ) • x - (c : ℂ) • x := by
      rw [Complex.ofReal_sub, sub_smul]
    rw [ContinuousLinearMap.sub_apply, hone, hsub, sub_sub_sub_cancel_left, neg_sub]
  refine le_trans
    (BookProof.ChapterSirkEndToEnd.resid_le_norm_sub_smul
      (isSelfAdjoint_reflection R hR γ) hx (γ⁻¹ - c)) (le_of_eq ?_)
  rw [hvec, norm_neg]
/-- **The SIRK operator-norm error is a residual for `A' = γ⁻¹ 1 − X_γ`.**  Run
`sirk_ritz_resid_le`'s two steps (the reduced eigenpair fixes a multiple of
`V y`, and the operator-norm bound controls the difference) with the reflection
in place of `X`: the constant is unchanged, `sirkBound C Dmin h 1 m`. -/
theorem sirk_resid_reflection_le (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (γ : ℝ) (C Dmin h : ℝ) (m : ℕ) (mu : ℝ) (y : F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (heig : psiB y = (mu : ℂ) • y) (hy : ‖V y‖ = 1)
    (hbound : ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m) :
    BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V y)
      ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m := by
  have hAy : BookProof.ChapterSirkEndToEnd.sirkApprox V psiB (V y) = (mu : ℂ) • (V y) := by
    have h1 : V.adjoint (V y) = y := by
      have h := congrArg (fun f : F →L[ℂ] F => f y) hVV
      simpa using h
    rw [BookProof.ChapterSirkEndToEnd.sirkApprox_apply, h1, heig, map_smul]
  have hstep : ‖R (V y) - (mu : ℂ) • (V y)‖ ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m := by
    have h := ContinuousLinearMap.le_opNorm
      (R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB) (V y)
    rw [hy, mul_one] at h
    refine le_trans ?_ (le_trans h hbound)
    rw [ContinuousLinearMap.sub_apply, hAy]
  exact le_trans (resid_reflection_le R hR hy mu) hstep

/-- **The certified edge on the reflected operator (`sirk_reflected_gap_certificate`).**

This is the single statement the S3 route needs, and it composes the three
pieces proved in this development:

* `resolvent_reflection_eigenvector` — the bottom eigenvector `y` of `A` is an
  eigenvector of `A'` with the reflected edge `λ' = e/(γ(e+γ))`, so `A'` is the
  operator Temple can be run on;
* `sirk_resid_reflection_le` — the SIRK operator-norm error at order `m` is a
  *residual* for `A'` at the reconstructed vector `V y`, with the same constant;
* `temple_lower_bound` on `A'` and `gap_transfer` — the Temple band
  `[θ − ε²/(β − θ), θ]` sits above `λ'`, and the edge transfers back with the
  factor `γ²`: `γ² λ' ≤ e`.

The spectral separation `hsep` is the one input a two-sided enclosure cannot
avoid; it is stated for `A'`, whose bottom edge is `λ'`. -/
theorem sirk_reflected_gap_certificate
    {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) (hRsym : IsSelfAdjoint R)
    {y : E} (hy : y ∈ Dom) {e : ℝ} (he : 0 ≤ e)
    (heig : A ⟨y, hy⟩ = (e : ℂ) • y)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) {yy : F} (mu C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (heigB : psiB yy = (mu : ℂ) • yy) (hyy : ‖V yy‖ = 1)
    (hbound : ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m)
    {b : ℝ}
    (hsep : BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (resolventEdge γ e) b)
    (hlt : BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) < b) :
    ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) y = (resolventEdge γ e : ℂ) • y ∧
      BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)
        ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m ∧
      BookProof.RitzCertificate.rayleigh ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) -
          BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) ^ 2 /
            (b - BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy))
        ≤ resolventEdge γ e ∧
      γ ^ 2 * resolventEdge γ e ≤ e := by
  have hsym : IsSelfAdjoint ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) :=
    isSelfAdjoint_reflection R hRsym γ
  refine ⟨resolvent_reflection_eigenvector hR hγ hy he heig, ?_, ?_, ?_⟩
  · exact sirk_resid_reflection_le V psiB R hRsym γ C Dmin h m mu yy hVV heigB hyy hbound
  · exact BookProof.RitzCertificate.temple_lower_bound hsym hsep hyy hlt
  · have h := gap_transfer (γ := γ) (e₀ := 0) (e₁ := e) hγ (le_refl 0) he
    simpa using h

/-- **The certificate with the separation stated as a form bound on the compression.**  The
same conclusion as `sirk_reflected_gap_certificate`, but `hsep` is *derived* instead of assumed:
the input is the form bound

  `b ‖z‖² ≤ re ⟪z, A' z⟫` for every `z ∈ yᗮ`

on the complement of the certified eigenvector, where `A' = γ⁻¹ • 1 − R`.  The bridge is
`SpectralSplitting.spectralSeparation_of_compressionBound`: the compression `A'|yᗮ` is
self-adjoint (`isSelfAdjoint_compressed`), so `ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum`
turns the form bound into a spectrum bound on it, and
`SpectralSplitting.spectrum_subset_union_compressed` carries that bound back to `A'` with `λ'`
covering the line.

Unlike the deflated form retired in `13q`, this input is not degenerate: no spectral point is
forced to be `0`, so a positive `b` is admissible whenever the complement form bound holds. -/
theorem sirk_reflected_gap_certificate_of_compression
    {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) (hRsym : IsSelfAdjoint R)
    {y : E} (hy : y ∈ Dom) (hy0 : y ≠ 0) {e : ℝ} (he : 0 ≤ e)
    (heig : A ⟨y, hy⟩ = (e : ℂ) • y)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) {yy : F} (mu C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (heigB : psiB yy = (mu : ℂ) • yy) (hyy : ‖V yy‖ = 1)
    (hbound : ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m)
    {b : ℝ}
    (hC : ∀ z : ↥(BookProof.SpectralSplitting.eigenLine y)ᗮ,
      b * ‖(z : E)‖ ^ 2 ≤ (inner ℂ (z : E)
        (((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (z : E)) : ℂ).re)
    (hlb : resolventEdge γ e ≤ b)
    (hlt : BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) < b) :
    ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) y = (resolventEdge γ e : ℂ) • y ∧
      BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)
        ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m ∧
      BookProof.RitzCertificate.rayleigh ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) -
          BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) ^ 2 /
            (b - BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy))
        ≤ resolventEdge γ e ∧
      γ ^ 2 * resolventEdge γ e ≤ e := by
  have hsep : BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (resolventEdge γ e) b := by
    refine BookProof.SpectralSplitting.spectralSeparation_of_compressionBound _
      (isSelfAdjoint_reflection R hRsym γ) hy0
      (resolvent_reflection_eigenvector hR hγ hy he heig) hlb ?_
    intro z
    rw [Submodule.coe_norm, Submodule.coe_inner,
      BookProof.SpectralSplitting.compressed_apply_coe]
    exact hC z
  exact sirk_reflected_gap_certificate hR hγ hRsym hy he heig V psiB mu C Dmin h m hVV
    heigB hyy hbound hsep hlt

/-! ## 9. The norm route, fed by the shift-invert bound -/

omit [CompleteSpace E] in
/-- The reflected operator differs from the scalar `γ⁻¹` by `R`: `A' = γ⁻¹ 1 − R`, so the
distance from `A'` to that scalar is the norm of the shift-invert itself. -/
theorem reflected_sub_smul_one (R : E →L[ℂ] E) (γ : ℝ) :
    (((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) - ((γ⁻¹ : ℝ) : ℂ) • 1) = -R := by
  have h1 : ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E)) = (((γ⁻¹ : ℝ) : ℂ) • (1 : E →L[ℂ] E)) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) γ⁻¹ (1 : E →L[ℂ] E)]
    congr 1
  rw [h1]
  abel

omit [CompleteSpace E] in
/-- **The norm the form-bound route asks for**, read off a bound on the shift-invert:
`‖A' - γ⁻¹ 1‖ ≤ ρ` whenever `‖R‖ ≤ ρ`. -/
theorem reflected_norm_sub_smul_one_le (R : E →L[ℂ] E) (γ : ℝ) {ρ : ℝ} (hR : ‖R‖ ≤ ρ) :
    ‖(((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) - ((γ⁻¹ : ℝ) : ℂ) • 1)‖ ≤ ρ := by
  rw [reflected_sub_smul_one, norm_neg]
  exact hR

omit [CompleteSpace E] in
/-- **The per-system flow bound feeds the norm route.**  `IsShiftInvert.opNorm_le` gives
`‖R‖ ≤ γ⁻¹` for any positive `A`, so `A'` lies within `γ⁻¹` of the scalar `γ⁻¹` — the endpoint
`b = 0` of the separation.  A *positive* `b` asks for the strict version
`‖R‖ ≤ γ⁻¹ - b`, which is what a gap-dominated flow estimate supplies. -/
theorem reflected_norm_sub_smul_one_le_inv {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R)
    (hpos : ∀ x : Dom, 0 ≤ BookProof.FarisLavine.quadForm A x) (hγ : 0 < γ) :
    ‖(((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) - ((γ⁻¹ : ℝ) : ℂ) • 1)‖ ≤ γ⁻¹ :=
  reflected_norm_sub_smul_one_le R γ (hR.opNorm_le hpos hγ)

/-- **The end-to-end certificate, fed by the shift-invert norm bound.**

The same conclusion as `sirk_reflected_gap_certificate`, with the separation `hsep` *derived*
from `‖R‖ ≤ γ⁻¹ - b` — the per-system bound on the shift-invert — instead of assumed.  By
`reflected_norm_sub_smul_one_le` the reflected operator `A' = γ⁻¹ 1 − R` is within `γ⁻¹ - b`
of the scalar `γ⁻¹`, so `spectralSeparation_of_norm_le` supplies
`SpectralSeparation A' (resolventEdge γ e) b`, and `sirk_reflected_gap_certificate` finishes.
No spectral statement about `yᗮ` appears among the hypotheses. -/
theorem sirk_reflected_gap_certificate_of_shiftInvertNorm
    {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) (hRsym : IsSelfAdjoint R)
    {y : E} (hy : y ∈ Dom) (hy0 : y ≠ 0) {e : ℝ} (he : 0 ≤ e)
    (heig : A ⟨y, hy⟩ = (e : ℂ) • y)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) {yy : F} (mu C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (heigB : psiB yy = (mu : ℂ) • yy) (hyy : ‖V yy‖ = 1)
    (hbound : ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m)
    {b : ℝ} (hRnorm : ‖R‖ ≤ γ⁻¹ - b)
    (hlb : resolventEdge γ e ≤ b)
    (hlt : BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) < b) :
    ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) y = (resolventEdge γ e : ℂ) • y ∧
      BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)
        ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m ∧
      BookProof.RitzCertificate.rayleigh ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) -
          BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) ^ 2 /
            (b - BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy))
        ≤ resolventEdge γ e ∧
      γ ^ 2 * resolventEdge γ e ≤ e := by
  have hsep : BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (resolventEdge γ e) b :=
    BookProof.SpectralSplitting.spectralSeparation_of_norm_le
      (A := (γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (hA := isSelfAdjoint_reflection R hRsym γ)
      (y := y) (l := resolventEdge γ e) (c := γ⁻¹) hy0
      (resolvent_reflection_eigenvector hR hγ hy he heig) hlb
      (reflected_norm_sub_smul_one_le R γ hRnorm)
  exact sirk_reflected_gap_certificate (A := A) (γ := γ) (R := R) (e := e) (b := b)
    hR hγ hRsym hy he heig V psiB mu C Dmin h m hVV heigB hyy hbound hsep hlt

/-! ## 10. The bottom-edge route: a strictly positive level from the known ground state -/

/-- **The level is the strict bound.**  `‖R‖ ≤ (e + γ)⁻¹` is the norm hypothesis
`‖R‖ ≤ γ⁻¹ - b` at `b = γ⁻¹ - (e + γ)⁻¹`, and by `resolventEdge_eq` that level is exactly
the reflected edge `resolventEdge γ e`.  This is the identification the certificate below
uses: the level `b` the one-step route consumes is not a free parameter but the reflected
ground-state edge. -/
theorem inv_sub_inv_eq_resolventEdge {γ e : ℝ} (hγ : 0 < γ) (he : 0 ≤ e) :
    γ⁻¹ - (e + γ)⁻¹ = resolventEdge γ e :=
  (resolventEdge_eq (ne_of_gt hγ) (ne_of_gt (show (0 : ℝ) < e + γ by linarith))).symm

/-- **The complement of the reflected edge is the strict bound.**  `γ⁻¹ - resolventEdge γ e`
is exactly `(e + γ)⁻¹`, which is how the strict shift-invert bound becomes a separation
level: `‖R‖ ≤ (e + γ)⁻¹ = γ⁻¹ - b` with `b = resolventEdge γ e`. -/
theorem sub_resolventEdge_eq_inv {γ e : ℝ} (hγ : 0 < γ) (he : 0 ≤ e) :
    γ⁻¹ - resolventEdge γ e = (e + γ)⁻¹ := by
  rw [resolventEdge_eq (ne_of_gt hγ) (ne_of_gt (show (0 : ℝ) < e + γ by linarith))]
  ring

/-- **The level is positive** once the ground state is: `e > 0` gives
`resolventEdge γ e > 0`, so the `b = 0` endpoint of the generic positivity route is beaten
by the bottom-edge route. -/
theorem resolventEdge_pos {γ e : ℝ} (hγ : 0 < γ) (he : 0 < e) : 0 < resolventEdge γ e := by
  rw [resolventEdge_def]
  positivity

omit [CompleteSpace E] in
/-- **The bottom edge feeds the norm route.**  `IsShiftInvert.opNorm_le_edge` gives
`‖R‖ ≤ (e + γ)⁻¹`, which `inv_sub_inv_eq_resolventEdge` rewrites as
`‖A' - γ⁻¹ 1‖ ≤ γ⁻¹ - resolventEdge γ e`: the norm hypothesis of the separation, with the
level set to the reflected edge. -/
theorem reflected_norm_sub_smul_one_le_edge {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) {e : ℝ} (he : 0 ≤ e)
    (hbot : ∀ x : Dom, e * ‖(x : E)‖ ^ 2 ≤ BookProof.FarisLavine.quadForm A x) :
    ‖(((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) - ((γ⁻¹ : ℝ) : ℂ) • 1)‖
      ≤ γ⁻¹ - resolventEdge γ e := by
  rw [sub_resolventEdge_eq_inv hγ he]
  exact reflected_norm_sub_smul_one_le R γ (hR.opNorm_le_edge hbot hγ he)

omit [CompleteSpace E] in
/-- **The strict shift-invert bound as a separation level.**  `‖R‖ ≤ γ⁻¹ - b` with
`b = resolventEdge γ e`, read directly off the bottom edge. -/
theorem shiftInvert_opNorm_le_of_bottom {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) {e : ℝ} (he : 0 ≤ e)
    (hbot : ∀ x : Dom, e * ‖(x : E)‖ ^ 2 ≤ BookProof.FarisLavine.quadForm A x) :
    ‖R‖ ≤ γ⁻¹ - resolventEdge γ e := by
  rw [sub_resolventEdge_eq_inv hγ he]
  exact hR.opNorm_le_edge hbot hγ he

/-- **The end-to-end certificate with a positive level, from the bottom edge.**

The same conclusion as `sirk_reflected_gap_certificate_of_shiftInvertNorm`, but the norm
hypothesis `‖R‖ ≤ γ⁻¹ - b` and the level `b` are *both* derived from one piece of data: the
lower bound `e ‖x‖² ≤ re ⟪x, A x⟫` on the domain of `A`.  `opNorm_le_edge` turns it into
`‖R‖ ≤ (e + γ)⁻¹`, `inv_sub_inv_eq_resolventEdge` identifies `γ⁻¹ - (e + γ)⁻¹` with the
reflected edge, so the separation level is `b = resolventEdge γ e` — positive whenever the
ground-state energy is (`resolventEdge_pos`), which the generic route cannot reach.

**The Temple half of this statement is vacuous.**  In this instantiation the level *is* the
edge: §10 proves `sInf (spectrum ℝ A') = resolventEdge γ e`, so the hypothesis
`hlt : rayleigh A' (V yy) < resolventEdge γ e` asks for `θ < sInf` — and Rayleigh–Ritz puts
every Rayleigh quotient at or above the infimum (`not_rayleigh_lt_sInf`, §19), so no unit
vector satisfies it.  What the theorem records is the remaining direction: the separation
*at* the edge (every spectral point is `λ'` or above it), and the identification
`‖R‖ ≤ γ⁻¹ - λ'`.  A Temple band needs the level strictly above the edge — the isolated
eigenvalue `λ' < b` of §19 — not the edge itself. -/
theorem sirk_reflected_gap_certificate_of_bottomEdge
    {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) (hRsym : IsSelfAdjoint R)
    {y : E} (hy : y ∈ Dom) (hy0 : y ≠ 0) {e : ℝ} (he : 0 ≤ e)
    (hbot : ∀ x : Dom, e * ‖(x : E)‖ ^ 2 ≤ BookProof.FarisLavine.quadForm A x)
    (heig : A ⟨y, hy⟩ = (e : ℂ) • y)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) {yy : F} (mu C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (heigB : psiB yy = (mu : ℂ) • yy) (hyy : ‖V yy‖ = 1)
    (hbound : ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m)
    (hlt : BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) < resolventEdge γ e) :
    ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) y = (resolventEdge γ e : ℂ) • y ∧
      BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)
        ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m ∧
      BookProof.RitzCertificate.rayleigh ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) -
          BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) ^ 2 /
            (resolventEdge γ e - BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy))
        ≤ resolventEdge γ e ∧
      γ ^ 2 * resolventEdge γ e ≤ e := by
  exact sirk_reflected_gap_certificate_of_shiftInvertNorm (A := A) (γ := γ) (R := R)
    (e := e) (b := resolventEdge γ e) hR hγ hRsym hy hy0 he heig V psiB mu C Dmin h m
    hVV heigB hyy hbound (shiftInvert_opNorm_le_of_bottom hR hγ he hbot) (le_refl _) hlt

/-- **The two-sided Temple band on the reflected operator, fed by the norm bound.**

`sirk_reflected_gap_certificate_of_shiftInvertNorm` gives only the *lower* half of Temple's
enclosure.  The upper half is Rayleigh–Ritz (`sInf_spectrum_le_rayleigh`), and together the
two halves enclose the edge of the *infinite* reflected operator, not just one eigenvalue:
both endpoints, `θ = rayleigh A' (V yy)` and `ε = resid A' (V yy)`, are computed from the
finite data, and `ε` is in turn bounded by the SIRK operator-norm error.  The level `b` is
supplied by `‖R‖ ≤ γ⁻¹ - b`, exactly as in the one-sided statement.

The separation does more than bound the edge: every spectral point is either `λ'` or at least
`b`, so `sInf (spectrum ℝ A') = λ' = resolventEdge γ e`.  Reflection rescales the bottom of
the spectrum, it does not move it. -/
theorem sirk_reflected_temple_band_of_shiftInvertNorm [Nontrivial E]
    {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) (hRsym : IsSelfAdjoint R)
    {y : E} (hy : y ∈ Dom) (hy0 : y ≠ 0) {e : ℝ} (he : 0 ≤ e)
    (heig : A ⟨y, hy⟩ = (e : ℂ) • y)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) {yy : F} (mu C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (heigB : psiB yy = (mu : ℂ) • yy) (hyy : ‖V yy‖ = 1)
    (hbound : ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m)
    {b : ℝ} (hRnorm : ‖R‖ ≤ γ⁻¹ - b)
    (hlb : resolventEdge γ e ≤ b)
    (hlt : BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) < b) :
    sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) ∈ Set.Icc
        (BookProof.RitzCertificate.rayleigh ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) -
          BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) ^ 2 /
            (b - BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)))
        (BookProof.RitzCertificate.rayleigh ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)) ∧
      sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) = resolventEdge γ e ∧
      γ ^ 2 * resolventEdge γ e ≤ e ∧
      BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)
        ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m := by
  have hA' : IsSelfAdjoint ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) :=
    isSelfAdjoint_reflection R hRsym γ
  have hsep : BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (resolventEdge γ e) b :=
    BookProof.SpectralSplitting.spectralSeparation_of_norm_le
      (A := (γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (hA := hA')
      (y := y) (l := resolventEdge γ e) (c := γ⁻¹) hy0
      (resolvent_reflection_eigenvector hR hγ hy he heig) hlb
      (reflected_norm_sub_smul_one_le R γ hRnorm)
  -- every spectral point lies at or above the reflected edge
  have hle : resolventEdge γ e ≤ sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) :=
    le_csInf (BookProof.ChapterSirkRitzSpectrum.spectrum_real_nonempty _ hA')
      (fun t ht => by
        rcases hsep.2 t ht with h | h
        · exact le_of_eq h.symm
        · exact le_trans hlb h)
  -- and the edge lies at or above the infimum: Rayleigh quotients see the bottom
  have hypos : 0 < ‖y‖ ^ 2 := by
    have : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    positivity
  have hge : sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) ≤ resolventEdge γ e := by
    have hray := BookProof.ChapterSirkRitzSpectrum.rayleighInf_mul_normSq_le
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) y
    rw [← BookProof.ChapterSirkRitzSpectrum.sInf_spectrum_eq_rayleighInf _ hA'] at hray
    have hinner : (inner ℂ y y : ℂ) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [resolvent_reflection_eigenvector hR hγ hy he heig, inner_smul_right, hinner,
      ← Complex.ofReal_mul, Complex.ofReal_re] at hray
    exact le_of_mul_le_mul_right hray hypos
  have hEq : sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) = resolventEdge γ e :=
    le_antisymm hge hle
  refine ⟨⟨?_, ?_⟩, hEq, ?_, ?_⟩
  · rw [hEq]
    exact BookProof.RitzCertificate.temple_lower_bound hA' hsep hyy hlt
  · exact BookProof.RitzCertificate.sInf_spectrum_le_rayleigh _ hA' hyy
  · simpa using gap_transfer (γ := γ) (e₀ := 0) (e₁ := e) hγ (le_refl 0) he
  · exact sirk_resid_reflection_le V psiB R hRsym γ C Dmin h m mu yy hVV heigB hyy hbound

/-- **The two-sided Temple band with the level set by the bottom edge.**  The specialization of
`sirk_reflected_temple_band_of_shiftInvertNorm` to `b = resolventEdge γ e`: the two-sided enclosure
of the reflected edge, with its strictness, follows from the lower bound
`e ‖x‖² ≤ re ⟪x, A x⟫` on the domain of `A` alone.

**The hypothesis `hlt` here is unsatisfiable, so the band it produces is empty.**  The theorem also
proves `sInf (spectrum ℝ A') = resolventEdge γ e`, so `hlt : rayleigh A' (V yy) < resolventEdge γ e`
reads `θ < sInf`, which `not_rayleigh_lt_sInf` (and its edge form
`not_rayleigh_lt_resolventEdge`) rules out for a unit vector.  Nothing is wrong with the bound
itself — `temple_lower_bound` is valid at the edge — but no vector supplies its side condition.
The non-vacuous version lives in §19: at the *next* reflected edge `b = resolventEdge γ e₁ > λ'`
the same band encloses the edge from some order on
(`reflected_band_closes_at_secondEdge`), because there `θ m < b` eventually holds by convergence
rather than by assumption. -/
theorem sirk_reflected_temple_band_of_bottomEdge [Nontrivial E]
    {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) (hRsym : IsSelfAdjoint R)
    {y : E} (hy : y ∈ Dom) (hy0 : y ≠ 0) {e : ℝ} (he : 0 ≤ e)
    (hbot : ∀ x : Dom, e * ‖(x : E)‖ ^ 2 ≤ BookProof.FarisLavine.quadForm A x)
    (heig : A ⟨y, hy⟩ = (e : ℂ) • y)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) {yy : F} (mu C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (heigB : psiB yy = (mu : ℂ) • yy) (hyy : ‖V yy‖ = 1)
    (hbound : ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m)
    (hlt : BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) < resolventEdge γ e) :
    sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) ∈ Set.Icc
        (BookProof.RitzCertificate.rayleigh ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) -
          BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) ^ 2 /
            (resolventEdge γ e - BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)))
        (BookProof.RitzCertificate.rayleigh ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)) ∧
      sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) = resolventEdge γ e ∧
      γ ^ 2 * resolventEdge γ e ≤ e ∧
      BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)
        ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m :=
  sirk_reflected_temple_band_of_shiftInvertNorm (A := A) (γ := γ) (R := R) (e := e)
    (b := resolventEdge γ e) hR hγ hRsym hy hy0 he heig V psiB mu C Dmin h m hVV heigB hyy
    hbound (shiftInvert_opNorm_le_of_bottom hR hγ he hbot) (le_refl _) hlt
end Reflected

/-! ## 11. Whichever spectral input you have

The two routes above take different data — a bottom edge `e` on the domain, or a form bound on
the compression to `yᗮ` — and produce the *same* separation, at the same level.  This section
makes that a single object: `ReflectedSeparationSource` is the disjunction of the two inputs, and
`spectralSeparation_of_source` discharges it either way, so a caller holding either can use one
certificate. -/

section Source

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ E}

/-- **The two admissible spectral inputs**, as one type indexed by the level `b` they certify.

* `ofBottomEdge` — a lower bound `e ‖x‖² ≤ re ⟪x, A x⟫` on the domain of `A`.  It certifies the
  level `b = resolventEdge γ e`, the reflected bottom edge (`IsShiftInvert.opNorm_le_edge`).
* `ofCompression` — the form bound `b ‖z‖² ≤ re ⟪z, A' z⟫` on the complement of the certified
  eigenvector, for its own level `b`.

Both are sufficient for the same conclusion; neither implies the other (the bottom edge is global
data about `A`, the compression bound is data about `A'` restricted to `yᗮ`). -/
inductive ReflectedSeparationSource (A : Dom →ₗ[ℂ] E) (γ : ℝ) (R : E →L[ℂ] E)
    (e : ℝ) (y : E) : ℝ → Prop
  /-- The bottom edge of `A` certifies the reflected edge `resolventEdge γ e`. -/
  | ofBottomEdge (hbot : ∀ x : Dom, e * ‖(x : E)‖ ^ 2 ≤ BookProof.FarisLavine.quadForm A x) :
      ReflectedSeparationSource A γ R e y (resolventEdge γ e)
  /-- A form bound on the compression of `A'` to `yᗮ` certifies its own level. -/
  | ofCompression {b : ℝ} (hlb : resolventEdge γ e ≤ b)
      (hC : ∀ z : ↥(BookProof.SpectralSplitting.eigenLine y)ᗮ,
        b * ‖(z : E)‖ ^ 2 ≤ (inner ℂ (z : E)
          (((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (z : E)) : ℂ).re) :
      ReflectedSeparationSource A γ R e y b

/-- **Either input discharges the same separation.**  Both constructors of
`ReflectedSeparationSource` produce `SpectralSeparation A' (resolventEdge γ e) b`; the bottom-edge
branch goes through the strict shift-invert bound (`shiftInvert_opNorm_le_of_bottom`) and the
norm route, the compression branch through `spectralSeparation_of_compressionBound`. -/
theorem spectralSeparation_of_source {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    {e : ℝ} {y : E} {b : ℝ}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) (hRsym : IsSelfAdjoint R)
    (hy : y ∈ Dom) (hy0 : y ≠ 0) (he : 0 ≤ e)
    (heig : A ⟨y, hy⟩ = (e : ℂ) • y)
    (hsrc : ReflectedSeparationSource A γ R e y b) :
    BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (resolventEdge γ e) b := by
  cases hsrc with
  | ofBottomEdge hbot =>
    exact BookProof.SpectralSplitting.spectralSeparation_of_norm_le
      (A := (γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (hA := isSelfAdjoint_reflection R hRsym γ)
      (y := y) (l := resolventEdge γ e) (c := γ⁻¹) hy0
      (resolvent_reflection_eigenvector hR hγ hy he heig) (le_refl _)
      (reflected_norm_sub_smul_one_le R γ (shiftInvert_opNorm_le_of_bottom hR hγ he hbot))
  | ofCompression hlb hC =>
    refine BookProof.SpectralSplitting.spectralSeparation_of_compressionBound _
      (isSelfAdjoint_reflection R hRsym γ) hy0
      (resolvent_reflection_eigenvector hR hγ hy he heig) hlb ?_
    intro z
    rw [Submodule.coe_norm, Submodule.coe_inner,
      BookProof.SpectralSplitting.compressed_apply_coe]
    exact hC z

/-- **The certificate from either input.**  `sirk_reflected_gap_certificate` with `hsep` supplied
by `spectralSeparation_of_source`: the caller needs a bottom edge *or* a compression form bound,
not both, and no other spectral statement. -/
theorem sirk_reflected_gap_certificate_of_source
    {A : Dom →ₗ[ℂ] E} {γ : ℝ} {R : E →L[ℂ] E}
    (hR : IsShiftInvert A γ R) (hγ : 0 < γ) (hRsym : IsSelfAdjoint R)
    {y : E} (hy : y ∈ Dom) (hy0 : y ≠ 0) {e : ℝ} (he : 0 ≤ e)
    (heig : A ⟨y, hy⟩ = (e : ℂ) • y)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F) {yy : F} (mu C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (heigB : psiB yy = (mu : ℂ) • yy) (hyy : ‖V yy‖ = 1)
    (hbound : ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m)
    {b : ℝ} (hsrc : ReflectedSeparationSource A γ R e y b)
    (hlt : BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) < b) :
    ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) y = (resolventEdge γ e : ℂ) • y ∧
      BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy)
        ≤ BookProof.ChapterH6.sirkBound C Dmin h 1 m ∧
      BookProof.RitzCertificate.rayleigh ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) -
          BookProof.RitzCertificate.resid ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy) ^ 2 /
            (b - BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V yy))
        ≤ resolventEdge γ e ∧
      γ ^ 2 * resolventEdge γ e ≤ e :=
  sirk_reflected_gap_certificate (A := A) (γ := γ) (R := R) (e := e) (b := b)
    hR hγ hRsym hy he heig V psiB mu C Dmin h m hVV heigB hyy hbound
    (spectralSeparation_of_source hR hγ hRsym hy hy0 he heig hsrc) hlt

end Source

/-! ## 12. The bottom-edge arithmetic on the `diag (5, 2)` instance

The instance of `BookProof.SpectralSplitting` §12 has bottom edge `2` (the eigenvalue of
`vOther`) and complement level `5` (the eigenvalue of `vTrial`), so with shift `γ = 1` the
bottom-edge route reads: strict shift-invert bound `(2 + 1)⁻¹ = 1/3`, hence the level
`b = γ⁻¹ - 1/3 = 2/3 = resolventEdge 1 2`, which is positive.  The two reflected eigenvalues
are `resolventEdge 1 2 = 2/3` and `resolventEdge 1 5 = 5/6`; their difference is `1/6`, and it
agrees with `resolventEdge_sub`'s exact formula `(5 - 2)/((2 + 1)(5 + 1))`.  So the level is
strictly below the reflected trial value by exactly the transferred gap. -/

/-- **The numbers the bottom-edge route produces on `diag (5, 2)`.** -/
theorem diag52_bottomEdge_arithmetic :
    (1 : ℝ)⁻¹ - (2 + 1)⁻¹ = resolventEdge 1 2 ∧
      resolventEdge 1 2 = 2 / 3 ∧ 0 < resolventEdge 1 2 ∧
      resolventEdge 1 5 = 5 / 6 ∧
      resolventEdge 1 5 - resolventEdge 1 2 = (5 - 2) / ((2 + 1) * (5 + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [resolventEdge_def]


/-! ## 13. Why the bottom edge cannot be manufactured from positivity and an eigenvector

`13v` derived the certificate's level from a bottom edge.  It is worth recording exactly why that
hypothesis cannot be replaced by the data a finite computation actually produces — positivity of
`A` plus a certified eigenvector with eigenvalue `e`.  It cannot: on `diag (5, 2)` the operator is
positive and `vTrial` is a unit eigenvector with eigenvalue `5`, yet `5 ‖x‖² ≤ re ⟪x, A2 x⟫` fails
at `vOther`, where the form is `2`.  The bottom edge is the *bottom* of the spectrum, and no
eigenvector pins the bottom: it pins one point.  Positivity alone gives the edge `e = 0`, which is
precisely the `b = 0` endpoint of the generic route. -/

/-- **Positivity plus a certified eigenvector is not a bottom edge.**  `A2` is a positive operator,
`vTrial` is a unit eigenvector with eigenvalue `5`, and the bottom-edge hypothesis at `e = 5` is
nevertheless false. -/
theorem bottomEdge_not_implied_by_positivity :
    (∀ x : BookProof.SpectralSplitting.E2,
        0 ≤ (inner ℂ x (BookProof.SpectralSplitting.A2 x) : ℂ).re) ∧
      BookProof.SpectralSplitting.A2 BookProof.SpectralSplitting.vTrial
        = (5 : ℂ) • BookProof.SpectralSplitting.vTrial ∧
      ‖BookProof.SpectralSplitting.vTrial‖ = 1 ∧
      ¬ (∀ x : BookProof.SpectralSplitting.E2,
        (5 : ℝ) * ‖x‖ ^ 2 ≤ (inner ℂ x (BookProof.SpectralSplitting.A2 x) : ℂ).re) := by
  refine ⟨BookProof.SpectralSplitting.A2_inner_re_nonneg,
    BookProof.SpectralSplitting.A2_trial, ?_, ?_⟩
  · simp [BookProof.SpectralSplitting.vTrial]
  · intro h
    have hv := h BookProof.SpectralSplitting.vOther
    rw [BookProof.SpectralSplitting.A2_other, inner_smul_right,
      BookProof.SpectralSplitting.inner_other_other,
      BookProof.SpectralSplitting.norm_other_sq] at hv
    norm_num at hv

/-! ## 14. Closing the upper end of the gap

`gap_transfer` is one-sided (`γ² (λ'₁ − λ'₀) ≤ e₁ − e₀`), which is why a ReflectedBandRow could
transfer only its lower end.  The reason is not a defect of the band: `resolventEdge_sub` is an
*identity*,

  `λ'₁ − λ'₀ = (e₁ − e₀) / ((e₀ + γ)(e₁ + γ))`,

so the gap is recovered from the reflected gap up to the two shifted eigenvalues.  An upper bound
on the gap therefore needs one extra input — upper bounds `e_i ≤ E_i` on the two edges — and then
the band's *upper* end transfers as well.  This section supplies that half. -/

/-- **The upper transfer.**  Given upper bounds `e₀ ≤ E₀`, `e₁ ≤ E₁` on the two edges, the gap is
bounded above by the reflected gap times the shifted bounds:
`e₁ − e₀ ≤ (λ'₁ − λ'₀) (E₀ + γ)(E₁ + γ)`.  Without the `E`'s there is no upper bound at all — the
factor `(e₀ + γ)(e₁ + γ)` is what the identity contributes, and it is not determined by `λ'`. -/
theorem edge_sub_le_of_upperBounds {γ e₀ e₁ E₀ E₁ : ℝ} (hγ : 0 < γ)
    (h0 : 0 ≤ e₀) (hle : e₀ ≤ e₁) (hE₀ : e₀ ≤ E₀) (hE₁ : e₁ ≤ E₁) :
    e₁ - e₀ ≤ (resolventEdge γ e₁ - resolventEdge γ e₀) * ((E₀ + γ) * (E₁ + γ)) := by
  have h1 : 0 < e₀ + γ := by linarith
  have h2 : 0 < e₁ + γ := by linarith
  have hP : 0 < (e₀ + γ) * (e₁ + γ) := mul_pos h1 h2
  have hPE : (e₀ + γ) * (e₁ + γ) ≤ (E₀ + γ) * (E₁ + γ) := by
    exact mul_le_mul (by linarith) (by linarith) (le_of_lt h2) (by linarith)
  have hd : resolventEdge γ e₁ - resolventEdge γ e₀ = (e₁ - e₀) / ((e₀ + γ) * (e₁ + γ)) :=
    resolventEdge_sub hγ h0 hle
  have hq : 0 ≤ (e₁ - e₀) / ((e₀ + γ) * (e₁ + γ)) := div_nonneg (by linarith) hP.le
  rw [hd]
  calc e₁ - e₀ = ((e₁ - e₀) / ((e₀ + γ) * (e₁ + γ))) * ((e₀ + γ) * (e₁ + γ)) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hP)]
    _ ≤ ((e₁ - e₀) / ((e₀ + γ) * (e₁ + γ))) * ((E₀ + γ) * (E₁ + γ)) :=
        mul_le_mul_of_nonneg_left hPE hq

/-- **The two-sided gap interval from two reflected bands.**  If `[lo₀, hi₀]` and `[lo₁, hi₁]`
contain the reflected edges of the bottom and top edge, and `E₀, E₁` bound the edges above, then

  `γ² (lo₁ − hi₀) ≤ e₁ − e₀ ≤ (hi₁ − lo₀) (E₀ + γ)(E₁ + γ)`:

both ends are computed from the finite band data plus the two edge bounds, and neither is assumed.
This is the companion of `gap_transfer`, which is the lower half with `E`'s absent. -/
theorem gap_interval_of_reflected_bands {γ e₀ e₁ lo₀ hi₀ lo₁ hi₁ E₀ E₁ : ℝ}
    (hγ : 0 < γ) (h0 : 0 ≤ e₀) (hle : e₀ ≤ e₁)
    (hband₀ : resolventEdge γ e₀ ∈ Set.Icc lo₀ hi₀)
    (hband₁ : resolventEdge γ e₁ ∈ Set.Icc lo₁ hi₁)
    (hE₀ : e₀ ≤ E₀) (hE₁ : e₁ ≤ E₁) :
    γ ^ 2 * (lo₁ - hi₀) ≤ e₁ - e₀ ∧
      e₁ - e₀ ≤ (hi₁ - lo₀) * ((E₀ + γ) * (E₁ + γ)) := by
  have hsq : 0 ≤ γ ^ 2 := sq_nonneg γ
  have hlam : resolventEdge γ e₁ - resolventEdge γ e₀ ≤ hi₁ - lo₀ := by
    linarith [hband₁.2, hband₀.1]
  have hfac : 0 ≤ (E₀ + γ) * (E₁ + γ) := by
    have hE₁' : 0 ≤ E₁ := le_trans (le_trans h0 hle) hE₁
    have h1' : 0 ≤ E₀ + γ := by linarith
    have h2' : 0 ≤ E₁ + γ := by linarith
    exact mul_nonneg h1' h2'
  refine ⟨?_, ?_⟩
  · have hlow : lo₁ - hi₀ ≤ resolventEdge γ e₁ - resolventEdge γ e₀ := by
      linarith [hband₁.1, hband₀.2]
    have h := mul_le_mul_of_nonneg_left hlow hsq
    linarith [gap_transfer (γ := γ) (e₀ := e₀) (e₁ := e₁) hγ h0 hle]
  · have h := mul_le_mul_of_nonneg_left hlam hfac
    linarith [edge_sub_le_of_upperBounds hγ h0 hle hE₀ hE₁]

/-! ## 15. The two inputs are not one inequality

`ReflectedSeparationSource` carries a constructor tag, not a single number, because the two
hypotheses are *different shapes*: one is a global bound on the domain of `A`, the other a bound on
the complement of the certified eigenvector.  This section records a finite witness that the tag is
necessary — on the running `diag (5, 2)` instance, the level `3` satisfies the complement form bound
and fails the whole-space one. -/

/-- **The complement form bound holds at a level where the whole-space bound fails.**  On the
`diag (5, 2)` instance with `vOther` the eigenvector of eigenvalue `2`: `vTrial` is orthogonal to
`vOther` (`inner_trial_other`), so it spans the complement, and there the form is `5 ≥ 3`
(`bound_on_complement`); on the whole space `vOther` sees only `2 ≱ 3`
(`fails_off_complement`).

What this does *not* say: the two certificates are not logically independent — a separation on
`A'` does make `λ'` the bottom of the reflected spectrum, so the two routes conclude compatible
things from compatible data.  What fails is interchangeability of the *hypotheses* at one numeric
level, which is exactly why the source type tags its constructor instead of collapsing both to one
inequality. -/
theorem compressionInput_holds_wholeSpaceInput_fails :
    (3 : ℝ) * ‖BookProof.SpectralSplitting.vTrial‖ ^ 2 ≤
        (inner ℂ BookProof.SpectralSplitting.vTrial
          (BookProof.SpectralSplitting.A2 BookProof.SpectralSplitting.vTrial) : ℂ).re ∧
      ¬ ((3 : ℝ) * ‖BookProof.SpectralSplitting.vOther‖ ^ 2 ≤
        (inner ℂ BookProof.SpectralSplitting.vOther
          (BookProof.SpectralSplitting.A2 BookProof.SpectralSplitting.vOther) : ℂ).re) :=
  ⟨BookProof.SpectralSplitting.bound_on_complement,
    BookProof.SpectralSplitting.fails_off_complement⟩

/-! ## 16. The interval on the `diag (5, 2)` numbers

`gap_interval_of_reflected_bands` instantiated on the running instance: `γ = 1`, bottom edge
`e₀ = 2` (`A2_other`) and top edge `e₁ = 5` (`A2_trial`), with the degenerate bands at the exact
reflected edges `resolventEdge 1 2 = 2/3` and `resolventEdge 1 5 = 5/6`, and the edges themselves as
their own upper bounds `E₀ = 2`, `E₁ = 5`.  The exact bands are legitimate here because the
instance's eigenvalues are exact; in a real solve they would be the Temple bands of §10.

The arithmetic is worth reading: the reflected gap is `1/6`, so the lower end gives `1/6 ≤ 3` — the
`γ²`-scaled, deliberately lossy half — while the upper end gives `3 ≤ (1/6)(3 · 6) = 3`, *tight*,
because both the bands and the `E`'s are exact. -/

/-- **The two-sided interval on the `diag (5, 2)` numbers**, and what its ends evaluate to. -/
theorem diag52_gap_interval :
    (1 : ℝ) ^ 2 * (resolventEdge 1 5 - resolventEdge 1 2) ≤ 5 - 2 ∧
      (5 - 2) ≤ (resolventEdge 1 5 - resolventEdge 1 2) * ((2 + 1) * (5 + 1)) ∧
      resolventEdge 1 5 - resolventEdge 1 2 = 1 / 6 ∧
      (resolventEdge 1 5 - resolventEdge 1 2) * ((2 + 1) * (5 + 1)) = 3 := by
  have h := gap_interval_of_reflected_bands (γ := 1) (e₀ := 2) (e₁ := 5)
    (lo₀ := resolventEdge 1 2) (hi₀ := resolventEdge 1 2)
    (lo₁ := resolventEdge 1 5) (hi₁ := resolventEdge 1 5)
    (E₀ := 2) (E₁ := 5) one_pos (by norm_num) (by norm_num)
    ⟨le_refl _, le_refl _⟩ ⟨le_refl _, le_refl _⟩ (le_refl _) (le_refl _)
  exact ⟨h.1, h.2, by norm_num [resolventEdge_def], by norm_num [resolventEdge_def]⟩

/-! ## 17. The band closes: a rate

The certificates in §10–§15 enclose the reflected edge `λ'` in a band at each order.  This section
shows the enclosure *closes*: the band's width is `ε²/(b − θ)`, it vanishes at the SIRK rate because
`ε` is bounded by `sirkBound C Dmin h 1 m` and that decays like `e^{−hm}`, and once the widths
vanish both ends of the band converge to `λ'`.  That is the limit statement the per-order
certificate is usually asked for, and it is a rate, not just a limit: the width is at most
`ε²/δ` where `δ` is the fixed distance from the Rayleigh quotient to the level. -/


section BandRate

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ E}

open Filter
open scoped Topology

/-- The width of the reflected Temple band at order `m`: `ε m ^ 2 / (b - θ m)`. -/
def templeBandWidth (θ ε : ℕ → ℝ) (b : ℝ) (m : ℕ) : ℝ := ε m ^ 2 / (b - θ m)

/-- The width is at most `ε²/δ` once the Rayleigh quotient stays `δ` below `b`. -/
theorem templeBandWidth_le {θ ε : ℕ → ℝ} {b delta : ℝ} (m : ℕ) (hdelta : 0 < delta)
    (hgap : θ m ≤ b - delta) : templeBandWidth θ ε b m ≤ ε m ^ 2 / delta := by
  have hbθ : delta ≤ b - θ m := by linarith
  exact div_le_div_of_nonneg_left (sq_nonneg (ε m)) hdelta hbθ

/-- **The width vanishes.**  If the Rayleigh quotients stay a fixed distance below `b` and the
residuals tend to `0`, the bands' widths tend to `0` — at the rate `ε²/δ`. -/
theorem templeBandWidth_tendsto_zero {b delta : ℝ} (hdelta : 0 < delta) {θ ε : ℕ → ℝ}
    (hgap : ∀ m, θ m ≤ b - delta) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (templeBandWidth θ ε b) atTop (𝓝 0) := by
  have hε2 : Tendsto (fun m => ε m ^ 2) atTop (𝓝 0) := by simpa using hε.pow 2
  refine squeeze_zero (fun m => ?_) (fun m => templeBandWidth_le m hdelta (hgap m)) ?_
  · have hbθ : 0 < b - θ m := by
      have := hgap m
      linarith
    exact div_nonneg (sq_nonneg _) hbθ.le
  · have := hε2.div_const delta
    simpa using this

/-- **The enclosure closes.**  If `λ` lies in `[lo m, hi m]` at every order and the widths tend to
`0`, both ends converge to `λ`: the nested intervals shrink onto the certified edge. -/
theorem band_closes_of_width_tendsto_zero {lam : ℝ} {lo hi : ℕ → ℝ}
    (hlo : ∀ m, lo m ≤ lam) (hhi : ∀ m, lam ≤ hi m)
    (hw : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    Tendsto lo atTop (𝓝 lam) ∧ Tendsto hi atTop (𝓝 lam) := by
  have hhi0 : Tendsto (fun m => hi m - lam) atTop (𝓝 0) :=
    squeeze_zero (fun m => by linarith [hhi m]) (fun m => by linarith [hlo m]) hw
  have hlo0 : Tendsto (fun m => lam - lo m) atTop (𝓝 0) :=
    squeeze_zero (fun m => by linarith [hlo m]) (fun m => by linarith [hhi m]) hw
  refine ⟨?_, ?_⟩
  · have := hlo0.const_sub lam
    simpa using this
  · have := hhi0.add_const lam
    simpa using this


/-- **The reflected band closes along a SIRK sequence.**  The residual at order `m` is bounded by
the SIRK operator-norm error (`sirk_resid_reflection_le`), which
`sirk_error_decay_exponential` sends to `0` like `e^{-h m}`; so the band widths vanish at the
rate `ε²/δ`, and by `band_closes_of_width_tendsto_zero` both ends of the band converge to the
reflected edge. -/
theorem reflected_band_closes_of_sirk
    {R : E →L[ℂ] E} (hRsym : IsSelfAdjoint R) {γ : ℝ}
    {C Dmin hstep : ℝ} (hh : 0 < hstep)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    {yy : ℕ → F} {mu : ℕ → ℝ} (heigB : ∀ m, psiB (yy m) = (mu m : ℂ) • yy m)
    (hyy : ∀ m, ‖V (yy m)‖ = 1)
    (hbound : ∀ m, ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m)
    {b delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ m, BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)) ≤ b - delta) :
    Tendsto (templeBandWidth
        (fun m => BookProof.RitzCertificate.rayleigh
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)))
        (fun m => BookProof.RitzCertificate.resid
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) b) atTop (𝓝 0) := by
  have hres : ∀ m, BookProof.RitzCertificate.resid
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))
        ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m :=
    fun m => sirk_resid_reflection_le V psiB R hRsym γ C Dmin hstep m (mu m) (yy m) hVV
      (heigB m) (hyy m) (hbound m)
  have hreslim : Tendsto (fun m => BookProof.RitzCertificate.resid
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) atTop (𝓝 0) :=
    squeeze_zero (fun m => by
      simp only [BookProof.RitzCertificate.resid]
      exact norm_nonneg _) hres
      (BookProof.ChapterH6.sirk_error_decay_exponential C Dmin hstep 1 hh)
  exact templeBandWidth_tendsto_zero hdelta hgap hreslim
end BandRate

/-! ## 18. The gap comes from the edges, and the limit is the edge

§17 needs a fixed `δ` with `θ m ≤ b − δ`.  This section removes that freedom where it can be
removed: with the level `b = resolventEdge γ e₁` and the Rayleigh quotients pinned at the bottom
edge `resolventEdge γ e₀`, the gap is the *difference of the two edge values*, positive by strict
monotonicity of `resolventEdge γ` as soon as `e₀ < e₁` — nothing is chosen.  On the same
`diag (5, 2)` numbers as §13 it is `5/6 − 2/3 = 1/6`.

The second half turns the limit into an `sInf`/`sSup` statement: the sup of the lower ends and the
inf of the upper ends are both the edge, so the nested family's intersection *is* `{λ'}`. -/

section BandEdge

open Filter
open scoped Topology

/-- **The edge gap is a difference of edge values.**  For `0 ≤ e₀ < e₁` and `γ > 0` the reflected
edges are ordered, so `resolventEdge γ e₁ - resolventEdge γ e₀ > 0`. -/
theorem resolventEdge_gap_pos {γ : ℝ} (hγ : 0 < γ) {e₀ e₁ : ℝ} (h0 : 0 ≤ e₀) (hlt : e₀ < e₁) :
    0 < resolventEdge γ e₁ - resolventEdge γ e₀ := by
  have h := resolventEdge_strictMonoOn (γ := γ) hγ
    (show e₀ ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr h0)
    (show e₁ ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr (h0.trans hlt.le)) hlt
  exact sub_pos.mpr h

/-- **The band's denominator is the edge gap, not a parameter.**  With the level
`b = resolventEdge γ e₁` and `θ m ≤ resolventEdge γ e₀`, the Temple width is at most `ε²/δ` where
`δ = resolventEdge γ e₁ - resolventEdge γ e₀` — derived from the edges, not chosen.

The price is visible in the hypothesis: `θ ≤ resolventEdge γ e₀` puts the Rayleigh quotient *at* the
bottom edge, and Rayleigh–Ritz only ever gives `θ` at or above it, so this is the degenerate case.
A trial vector strictly inside `(λ', b)` therefore still needs §17's per-order `θ m ≤ b - δ`; what
this theorem removes is the freedom to *pick* `δ` when the quotient does sit at the edge. -/
theorem templeBandWidth_le_edgeGap {γ e₀ e₁ : ℝ} {θ ε : ℕ → ℝ} (m : ℕ)
    (hγ : 0 < γ) (h0 : 0 ≤ e₀) (hlt : e₀ < e₁) (hθ : θ m ≤ resolventEdge γ e₀) :
    templeBandWidth θ ε (resolventEdge γ e₁) m
      ≤ ε m ^ 2 / (resolventEdge γ e₁ - resolventEdge γ e₀) :=
  templeBandWidth_le m (resolventEdge_gap_pos hγ h0 hlt) (by linarith)

/-- On the `diag (5, 2)` numbers (`γ = 1`, edges `2` and `5`) the derived gap is `1/6`. -/
theorem diag52_edgeGap : resolventEdge 1 5 - resolventEdge 1 2 = 1 / 6 := by
  rw [resolventEdge_def, resolventEdge_def]
  norm_num

/-- **The explicit rate on `diag (5, 2)`.**  Rayleigh quotients at the bottom edge `λ' = 2/3`,
residuals `2^{-m}`, level `b = 5/6`: the widths are at most `6 · 4^{-m}`, with `6 = 1/(1/6)` the
reciprocal of the derived edge gap.

This is arithmetic on the bound, not a numerical solve: as §13's degenerate bands, both inputs are
not attained together by a non-eigenvector (`θ = λ'` pins the trial vector to the bottom eigenspace,
where the residual vanishes).  What it checks is the *constant*: the edge gap `1/6` turns into
`6 · ε²` with nothing left free. -/
theorem diag52_bandWidth_le (m : ℕ) :
    templeBandWidth (fun _ => 2 / 3) (fun k => (1 / 2 : ℝ) ^ k) (5 / 6) m
      ≤ 6 * ((1 / 2 : ℝ) ^ m) ^ 2 := by
  have hb : resolventEdge (1 : ℝ) 5 = 5 / 6 := by
    rw [resolventEdge_def]; norm_num
  have h := templeBandWidth_le_edgeGap (γ := 1) (e₀ := 2) (e₁ := 5)
    (θ := fun _ => 2 / 3) (ε := fun k => (1 / 2 : ℝ) ^ k) m
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [diag52_edgeGap] at h
  rw [hb] at h
  calc templeBandWidth (fun _ => 2 / 3) (fun k => (1 / 2 : ℝ) ^ k) (5 / 6) m
      ≤ ((1 / 2 : ℝ) ^ m) ^ 2 / (1 / 6) := h
    _ = 6 * ((1 / 2 : ℝ) ^ m) ^ 2 := by ring

/-- **The `diag (5, 2)` band closes.**  With residuals `2^{-m}` the widths vanish, so the edge is
the only point left in the limit. -/
theorem diag52_bandWidth_closes :
    Tendsto (templeBandWidth (fun _ => 2 / 3) (fun k => (1 / 2 : ℝ) ^ k) (5 / 6))
      atTop (𝓝 0) := by
  have hε : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine templeBandWidth_tendsto_zero (b := 5 / 6) (delta := 1 / 6) (by norm_num)
    (fun m => by norm_num) hε

/-- **The `diag (5, 2)` enclosure closes.**  The band `[2/3 - 6·4^{-m}, 2/3]` has both ends at the
reflected edge `2/3` in the limit. -/
theorem diag52_band_ends_converge :
    Tendsto (fun m => (2 : ℝ) / 3 - 6 * ((1 / 2 : ℝ) ^ m) ^ 2) atTop (𝓝 (2 / 3)) ∧
      Tendsto (fun _ : ℕ => (2 : ℝ) / 3) atTop (𝓝 (2 / 3)) := by
  have hε : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsq : Tendsto (fun m : ℕ => ((1 / 2 : ℝ) ^ m) ^ 2) atTop (𝓝 0) := by
    simpa [pow_two, mul_zero] using hε.mul hε
  have hw : Tendsto (fun m : ℕ => (2 : ℝ) / 3 - ((2 : ℝ) / 3 - 6 * ((1 / 2 : ℝ) ^ m) ^ 2))
      atTop (𝓝 0) := by
    have := hsq.const_mul 6
    simpa using this
  refine band_closes_of_width_tendsto_zero (lam := 2 / 3)
    (lo := fun m => (2 : ℝ) / 3 - 6 * ((1 / 2 : ℝ) ^ m) ^ 2)
    (hi := fun _ => (2 : ℝ) / 3) (fun m => ?_) (fun m => le_refl _) hw
  have : 0 ≤ 6 * ((1 / 2 : ℝ) ^ m) ^ 2 := by positivity
  linarith

/-- The upper ends of a band shrinking down to `λ` have infimum exactly `λ`. -/
theorem sInf_range_eq_of_tendsto {lam : ℝ} {hi : ℕ → ℝ} (hhi : ∀ m, lam ≤ hi m)
    (h : Tendsto hi atTop (𝓝 lam)) : sInf (Set.range hi) = lam := by
  have hbdd : BddBelow (Set.range hi) := ⟨lam, by rintro _ ⟨m, rfl⟩; exact hhi m⟩
  refine le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds h
    (fun m => csInf_le hbdd (Set.mem_range_self m))) ?_
  exact le_csInf ⟨hi 0, Set.mem_range_self 0⟩ (fun y hy => by
    rcases hy with ⟨m, rfl⟩; exact hhi m)

/-- The lower ends of a band growing up to `λ` have supremum exactly `λ`. -/
theorem sSup_range_eq_of_tendsto {lam : ℝ} {lo : ℕ → ℝ} (hlo : ∀ m, lo m ≤ lam)
    (h : Tendsto lo atTop (𝓝 lam)) : sSup (Set.range lo) = lam := by
  have hbdd : BddAbove (Set.range lo) := ⟨lam, by rintro _ ⟨m, rfl⟩; exact hlo m⟩
  refine le_antisymm (csSup_le ⟨lo 0, Set.mem_range_self 0⟩ (fun y hy => by
    rcases hy with ⟨m, rfl⟩; exact hlo m)) ?_
  exact le_of_tendsto h (Eventually.of_forall (fun m => le_csSup hbdd (Set.mem_range_self m)))

/-- **The limit is exactly the edge.**  A nested band whose width vanishes has its lower ends'
supremum and its upper ends' infimum both equal to `λ`: the limit set `⋂ m, [lo m, hi m]` is the
single point `{λ}`. -/
theorem band_limit_is_edge {lam : ℝ} {lo hi : ℕ → ℝ}
    (hlo : ∀ m, lo m ≤ lam) (hhi : ∀ m, lam ≤ hi m)
    (hw : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    sSup (Set.range lo) = lam ∧ sInf (Set.range hi) = lam := by
  obtain ⟨h1, h2⟩ := band_closes_of_width_tendsto_zero (lam := lam) hlo hhi hw
  exact ⟨sSup_range_eq_of_tendsto hlo h1, sInf_range_eq_of_tendsto hhi h2⟩

end BandEdge

/-! ## 19. The non-degenerate route: a per-order gap, nothing pinned

§17 leaves `δ` free; §18 derives it from two edge values, but only under `θ m ≤ λ'`, which
Rayleigh–Ritz forces to `θ m = λ'`.  Neither restriction is necessary.  The Rayleigh quotients may
sit anywhere strictly inside `(λ', b)` and converge to `λ'`; the isolated eigenvalue (`λ' < b`) is
then all the gap one needs.  Write `δ m = b - θ m` for the *per-order* gap: past some order it is
at least half the eigenvalue gap `b - λ'`, so the width is at most `2 ε m²/(b - λ')` and vanishes
with the residuals.  Nothing is chosen, and `θ m = λ'` is never required.

The section closes with the audit that motivated it: a Temple hypothesis at the bottom edge itself
— the level `b = resolventEdge γ e` of §10, where `b = sInf (spectrum ℝ A')` — cannot be satisfied
by any unit vector, so a band whose level *is* the edge carries no numerical information.  A useful
level has to be strictly above the edge, and that strictness is exactly `λ' < b` below. -/

section BandNondegenerate

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open Filter
open scoped Topology

/-- **The per-order gap is eventually half the eigenvalue gap.**  If the Rayleigh quotients tend to
`l` and `l < b`, then from some order on `b - θ m ≥ (b - l)/2`: the gap is not chosen, it is forced
by convergence to the edge. -/
theorem eventually_half_gap_le {θ : ℕ → ℝ} {l b : ℝ} (hlb : l < b)
    (hθ : Tendsto θ atTop (𝓝 l)) : ∀ᶠ m in atTop, (b - l) / 2 ≤ b - θ m := by
  have hnear : ∀ᶠ m in atTop, θ m < l + (b - l) / 2 :=
    (tendsto_order.1 hθ).2 (l + (b - l) / 2) (by linarith)
  filter_upwards [hnear] with m hm
  linarith

/-- **The width is bounded by the eigenvalue gap.**  Feeding the per-order gap `b - θ m` into
`templeBandWidth_le` gives eventually `width ≤ ε m²/((b-l)/2) = 2 ε m²/(b-l)` — no `δ` in sight. -/
theorem templeBandWidth_le_half_gap {θ ε : ℕ → ℝ} {l b : ℝ} (hlb : l < b)
    (hθ : Tendsto θ atTop (𝓝 l)) :
    ∀ᶠ m in atTop, templeBandWidth θ ε b m ≤ 2 * ε m ^ 2 / (b - l) := by
  have hhalf := eventually_half_gap_le hlb hθ
  have hpos : (0 : ℝ) < (b - l) / 2 := by linarith
  filter_upwards [hhalf] with m hm
  have hle := templeBandWidth_le (θ := θ) (ε := ε) (b := b) m hpos (by linarith)
  calc templeBandWidth θ ε b m ≤ ε m ^ 2 / ((b - l) / 2) := hle
    _ = 2 * ε m ^ 2 / (b - l) := by field_simp

/-- **The band closes with no free `δ`.**  Rayleigh quotients converging to the bottom edge and
residuals vanishing are enough: the widths tend to `0` at the rate `2 ε²/(b - λ')`.  Neither the
value of a `δ` nor a per-order hypothesis on `θ` is an input. -/
theorem templeBandWidth_tendsto_zero_of_tendsto {l b : ℝ} (hlb : l < b) {θ ε : ℕ → ℝ}
    (hθ : Tendsto θ atTop (𝓝 l)) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (templeBandWidth θ ε b) atTop (𝓝 0) := by
  have hε2 : Tendsto (fun m => ε m ^ 2) atTop (𝓝 0) := by simpa using hε.pow 2
  have hbound : Tendsto (fun m => 2 * ε m ^ 2 / (b - l)) atTop (𝓝 0) := by
    have := (hε2.const_mul 2).div_const (b - l)
    simpa using this
  have hnonneg : ∀ᶠ m in atTop, 0 ≤ templeBandWidth θ ε b m := by
    have hhalf := eventually_half_gap_le hlb hθ
    filter_upwards [hhalf] with m hm
    exact div_nonneg (sq_nonneg _) (by linarith)
  exact squeeze_zero' hnonneg (templeBandWidth_le_half_gap hlb hθ) hbound

/-- **A Temple hypothesis at the bottom edge is unsatisfiable.**  Rayleigh–Ritz puts every Rayleigh
quotient at or above `sInf (spectrum ℝ A)`, so no unit vector has `θ < sInf`.  Setting the level of
a Temple band to the edge itself — `b = resolventEdge γ e` in §10, where `sInf` *is* that value —
therefore leaves a hypothesis that cannot hold, and such a band says nothing numerically.  A useful
level must sit strictly above the edge, which is the `λ' < b` of the theorems above. -/
theorem not_rayleigh_lt_sInf [Nontrivial E] {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {x : E} (hx : ‖x‖ = 1) :
    ¬ (BookProof.RitzCertificate.rayleigh A x < sInf (spectrum ℝ A)) :=
  not_lt_of_ge (BookProof.RitzCertificate.sInf_spectrum_le_rayleigh A hA hx)

/-- **The reflected band closes along a SIRK sequence, with no per-order hypothesis.**  This is
`reflected_band_closes_of_sirk` with `hgap` replaced by two pieces of data that are not choices: the
reflected edge is isolated below the level (`resolventEdge γ e < b`), and the Rayleigh quotients of
the SIRK vectors converge to it.  `sirk_resid_reflection_le` bounds the residuals and
`eventually_half_gap_le` supplies the per-order gap, so the widths vanish without `θ` ever being
pinned at the edge. -/
theorem reflected_band_closes_of_sirk_of_tendsto
    {R : E →L[ℂ] E} (hRsym : IsSelfAdjoint R) {γ e : ℝ}
    {C Dmin hstep : ℝ} (hh : 0 < hstep)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    {yy : ℕ → F} {mu : ℕ → ℝ} (heigB : ∀ m, psiB (yy m) = (mu m : ℂ) • yy m)
    (hyy : ∀ m, ‖V (yy m)‖ = 1)
    (hbound : ∀ m, ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m)
    {b : ℝ} (hlb : resolventEdge γ e < b)
    (hθ : Tendsto (fun m => BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) atTop (𝓝 (resolventEdge γ e))) :
    Tendsto (templeBandWidth
        (fun m => BookProof.RitzCertificate.rayleigh
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)))
        (fun m => BookProof.RitzCertificate.resid
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) b) atTop (𝓝 0) := by
  have hres : ∀ m, BookProof.RitzCertificate.resid
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))
        ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m :=
    fun m => sirk_resid_reflection_le V psiB R hRsym γ C Dmin hstep m (mu m) (yy m) hVV
      (heigB m) (hyy m) (hbound m)
  have hreslim : Tendsto (fun m => BookProof.RitzCertificate.resid
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) atTop (𝓝 0) :=
    squeeze_zero (fun m => by
      simp only [BookProof.RitzCertificate.resid]
      exact norm_nonneg _) hres
      (BookProof.ChapterH6.sirk_error_decay_exponential C Dmin hstep 1 hh)
  exact templeBandWidth_tendsto_zero_of_tendsto hlb hθ hreslim

/-- **At the next reflected edge the level is isolated automatically.**  For `0 ≤ e₀ < e₁` the level
`b = resolventEdge γ e₁` lies strictly above the bottom edge `resolventEdge γ e₀`
(`resolventEdge_gap_pos`), so Rayleigh quotients converging to the bottom edge close the band with
no `δ` at all.  This is §18's setting with the pinning hypothesis `θ m ≤ resolventEdge γ e₀`
replaced by convergence to it. -/
theorem reflected_band_closes_at_nextEdge {γ e₀ e₁ : ℝ} (hγ : 0 < γ) (h0 : 0 ≤ e₀)
    (hlt : e₀ < e₁) {θ ε : ℕ → ℝ}
    (hθ : Tendsto θ atTop (𝓝 (resolventEdge γ e₀))) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun m => templeBandWidth θ ε (resolventEdge γ e₁) m) atTop (𝓝 0) := by
  refine templeBandWidth_tendsto_zero_of_tendsto (l := resolventEdge γ e₀)
    (b := resolventEdge γ e₁) ?_ hθ hε
  linarith [resolventEdge_gap_pos hγ h0 hlt]

/-- **`diag (5, 2)`, non-degenerate.**  Rayleigh quotients `2/3 + 2^{-m}` sit strictly inside
`(2/3, 5/6)` at every order and converge to the bottom edge, residuals are `2^{-m}`, level `5/6`:
the widths still vanish.  Compare `diag52_bandWidth_closes`, where `θ` was pinned at `2/3`. -/
theorem diag52_band_closes_nonDegenerate :
    Tendsto (templeBandWidth (fun m : ℕ => (2 : ℝ) / 3 + (1 / 2 : ℝ) ^ m)
      (fun k : ℕ => (1 / 2 : ℝ) ^ k) (5 / 6)) atTop (𝓝 0) := by
  have hb : resolventEdge (1 : ℝ) 5 = 5 / 6 := by
    rw [resolventEdge_def]; norm_num
  have hε : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hθ : Tendsto (fun m : ℕ => (2 : ℝ) / 3 + (1 / 2 : ℝ) ^ m) atTop (𝓝 (2 / 3)) := by
    simpa using hε.const_add (2 / 3 : ℝ)
  have h2 : resolventEdge (1 : ℝ) 2 = 2 / 3 := by
    rw [resolventEdge_def]; norm_num
  have hθ' : Tendsto (fun m : ℕ => (2 : ℝ) / 3 + (1 / 2 : ℝ) ^ m) atTop
      (𝓝 (resolventEdge (1 : ℝ) 2)) := by
    rw [h2]; exact hθ
  have h := reflected_band_closes_at_nextEdge (γ := 1) (e₀ := 2) (e₁ := 5)
    (by norm_num) (by norm_num) (by norm_num) hθ' hε
  have hb5 : (5 : ℝ) / 6 = resolventEdge (1 : ℝ) 5 := hb.symm
  rw [hb5]
  exact h

/-- **A level equal to the reflected edge admits no Rayleigh quotient below it.**  If the edge of
the reflected operator *is* `resolventEdge γ e`, then `θ < resolventEdge γ e` is `θ < sInf` —
impossible for a unit vector (`not_rayleigh_lt_sInf`).  This is the audit lemma behind §10's
bottom-edge instantiation; a usable Temple level has to be strictly above the edge. -/
theorem not_rayleigh_lt_resolventEdge [Nontrivial E] {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {γ e : ℝ} (hsInf : sInf (spectrum ℝ A) = resolventEdge γ e) {x : E} (hx : ‖x‖ = 1) :
    ¬ (BookProof.RitzCertificate.rayleigh A x < resolventEdge γ e) := by
  rw [← hsInf]
  exact not_rayleigh_lt_sInf hA hx

/-- **The next reflected edge is a legitimate Temple level.**  For `0 ≤ e₀ < e₁` the two reflected
edges are strictly ordered (`resolventEdge_gap_pos`), so the bottom edge `λ' = resolventEdge γ e₀`
sits strictly below the level `resolventEdge γ e₁` — the second eigenvalue's reflected value.
That strictness is what §10's bottom-edge instantiation lacks. -/
theorem secondEdge_lt_level {γ e₀ e₁ : ℝ} (hγ : 0 < γ) (h0 : 0 ≤ e₀) (hlt : e₀ < e₁) :
    resolventEdge γ e₀ < resolventEdge γ e₁ := by
  have := resolventEdge_gap_pos hγ h0 hlt
  linarith

/-- **The SIRK residual is a residual for the reflected operator, and it vanishes.**  The
pointwise bound is `sirk_resid_reflection_le`, and `sirk_error_decay_exponential` makes the SIRK
operator-norm error tend to `0` like `e^{-h m}`. -/
theorem reflected_resid_tendsto_zero {R : E →L[ℂ] E} (hRsym : IsSelfAdjoint R) {γ : ℝ}
    {C Dmin hstep : ℝ} (hh : 0 < hstep)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    {yy : ℕ → F} {mu : ℕ → ℝ} (heigB : ∀ m, psiB (yy m) = (mu m : ℂ) • yy m)
    (hyy : ∀ m, ‖V (yy m)‖ = 1)
    (hbound : ∀ m, ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m) :
    Tendsto (fun m => BookProof.RitzCertificate.resid
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) atTop (𝓝 0) := by
  have hres : ∀ m, BookProof.RitzCertificate.resid
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))
        ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m :=
    fun m => sirk_resid_reflection_le V psiB R hRsym γ C Dmin hstep m (mu m) (yy m) hVV
      (heigB m) (hyy m) (hbound m)
  exact squeeze_zero (fun m => by
    simp only [BookProof.RitzCertificate.resid]
    exact norm_nonneg _) hres
    (BookProof.ChapterH6.sirk_error_decay_exponential C Dmin hstep 1 hh)

/-- **The Rayleigh quotients of the SIRK vectors converge to the reflected edge.**  §19's hypothesis
`hθ` is not data the caller has to supply: the reflected residual vanishes at the SIRK rate
(`reflected_resid_tendsto_zero`), the separation puts the rest of the spectrum above the level `b`,
and Rayleigh–Ritz plus Temple's inequality squeeze `θ m` onto `sInf (spectrum ℝ A')`, which §10
identifies with `resolventEdge γ e`.  The only quantitative input is that the quotients stay a fixed
`δ` below `b`. -/
theorem reflected_rayleigh_tendsto_edge [Nontrivial E]
    {R : E →L[ℂ] E} (hRsym : IsSelfAdjoint R) {γ : ℝ}
    {C Dmin hstep : ℝ} (hh : 0 < hstep)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    {yy : ℕ → F} {mu : ℕ → ℝ} (heigB : ∀ m, psiB (yy m) = (mu m : ℂ) • yy m)
    (hyy : ∀ m, ‖V (yy m)‖ = 1)
    (hbound : ∀ m, ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m)
    {e b delta : ℝ} (hdelta : 0 < delta)
    (hsInf : sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) = resolventEdge γ e)
    (hsep : BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (resolventEdge γ e) b)
    (hgap : ∀ m, BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)) ≤ b - delta) :
    Tendsto (fun m => BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) atTop (𝓝 (resolventEdge γ e)) := by
  have hsym : IsSelfAdjoint ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) :=
    isSelfAdjoint_reflection R hRsym γ
  have hsep' : BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)
      (sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R))) b := by
    rw [hsInf]
    exact hsep
  have h := BookProof.RitzCertificate.rayleigh_tendsto_sInf hsym hsep' hdelta hyy hgap
    (reflected_resid_tendsto_zero hRsym hh V psiB hVV heigB hyy hbound)
  rwa [hsInf] at h

/-- **The reflected band closes with no Rayleigh-quotient hypothesis.**  The next-edge form
`reflected_band_closes_at_nextEdge` takes `hθ` (convergence of the quotients to the bottom edge) as
data.  Here it is derived: the SIRK residuals vanish, the separation puts the level above the edge,
and `reflected_rayleigh_tendsto_edge` supplies the convergence.  Nothing about `θ` is assumed. -/
theorem reflected_band_closes_of_sirk_of_resid [Nontrivial E]
    {R : E →L[ℂ] E} (hRsym : IsSelfAdjoint R) {γ : ℝ}
    {C Dmin hstep : ℝ} (hh : 0 < hstep)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    {yy : ℕ → F} {mu : ℕ → ℝ} (heigB : ∀ m, psiB (yy m) = (mu m : ℂ) • yy m)
    (hyy : ∀ m, ‖V (yy m)‖ = 1)
    (hbound : ∀ m, ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m)
    {e b delta : ℝ} (hdelta : 0 < delta)
    (hsInf : sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) = resolventEdge γ e)
    (hsep : BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (resolventEdge γ e) b)
    (hgap : ∀ m, BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)) ≤ b - delta) :
    Tendsto (templeBandWidth
        (fun m => BookProof.RitzCertificate.rayleigh
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)))
        (fun m => BookProof.RitzCertificate.resid
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) b) atTop (𝓝 0) := by
  have hsym : IsSelfAdjoint ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) :=
    isSelfAdjoint_reflection R hRsym γ
  have hlvl : resolventEdge γ e < b := by
    have h0 := BookProof.RitzCertificate.sInf_spectrum_le_rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) hsym (hyy 0)
    rw [hsInf] at h0
    linarith [hgap 0]
  exact templeBandWidth_tendsto_zero_of_tendsto hlvl
    (reflected_rayleigh_tendsto_edge hRsym hh V psiB hVV heigB hyy hbound hdelta hsInf hsep hgap)
    (reflected_resid_tendsto_zero hRsym hh V psiB hVV heigB hyy hbound)

/-- **The Temple band at the second reflected edge is not vacuous.**  With `0 ≤ e₀ < e₁` the
level is `b = resolventEdge γ e₁` — the reflected value of an isolated second eigenvalue — and it
lies strictly above the bottom edge `λ' = resolventEdge γ e₀` (`secondEdge_lt_level`).  Then the
hypothesis `θ m < b` of `temple_band_mem` is not a certificate condition at all: it holds from
some order on, and from that order on every emitted band `[θ − ε²/(b−θ), θ]` encloses
`sInf (spectrum ℝ A')`, while its widths vanish.  Contrast
`sirk_reflected_temple_band_of_bottomEdge`, where the level *is* the edge and `hlt` can never be
met. -/
theorem reflected_band_closes_at_secondEdge [Nontrivial E]
    {R : E →L[ℂ] E} (hRsym : IsSelfAdjoint R) {γ : ℝ}
    {C Dmin hstep : ℝ} (hh : 0 < hstep)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    {yy : ℕ → F} {mu : ℕ → ℝ} (heigB : ∀ m, psiB (yy m) = (mu m : ℂ) • yy m)
    (hyy : ∀ m, ‖V (yy m)‖ = 1)
    (hbound : ∀ m, ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m)
    {e₀ e₁ : ℝ} (hγ : 0 < γ) (h0 : 0 ≤ e₀) (hlt : e₀ < e₁)
    (hsInf : sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) = resolventEdge γ e₀)
    (hsep : BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (resolventEdge γ e₀) (resolventEdge γ e₁))
    {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ m, BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)) ≤ resolventEdge γ e₁ - delta) :
    Tendsto (templeBandWidth
        (fun m => BookProof.RitzCertificate.rayleigh
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)))
        (fun m => BookProof.RitzCertificate.resid
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)))
        (resolventEdge γ e₁)) atTop (𝓝 0) ∧
      ∀ᶠ m in atTop,
        sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) ∈
          Set.Icc (BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)) -
            BookProof.RitzCertificate.resid
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)) ^ 2 /
              (resolventEdge γ e₁ - BookProof.RitzCertificate.rayleigh
                ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))))
            (BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) := by
  have hsym : IsSelfAdjoint ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) :=
    isSelfAdjoint_reflection R hRsym γ
  have hlvl : resolventEdge γ e₀ < resolventEdge γ e₁ := secondEdge_lt_level hγ h0 hlt
  have hθ := reflected_rayleigh_tendsto_edge (b := resolventEdge γ e₁) hRsym hh V psiB hVV
    heigB hyy hbound hdelta hsInf hsep hgap
  refine ⟨templeBandWidth_tendsto_zero_of_tendsto hlvl hθ
    (reflected_resid_tendsto_zero hRsym hh V psiB hVV heigB hyy hbound), ?_⟩
  have hsep' : BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)
      (sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R))) (resolventEdge γ e₁) := by
    rw [hsInf]
    exact hsep
  have hθ' : Tendsto (fun m => BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) atTop
      (𝓝 (sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)))) := by
    rw [hsInf]
    exact hθ
  have hlvl' : sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) < resolventEdge γ e₁ := by
    rw [hsInf]
    exact hlvl
  exact BookProof.RitzCertificate.temple_band_eventually_mem hsym hsep' hyy hθ' hlvl'

/-- **The second-edge separation from the compression form bound.**  `hsep` in
`reflected_band_closes_at_secondEdge` is not data a caller has to own: `ChapterSpectralSplitting`
turns a *form* bound on the compression to `yᗮ` into a spectrum bound, and with `y` the reflected
edge eigenvector the remaining hypothesis `l ≤ b` is `secondEdge_lt_level`.  What is left is the
number a run can estimate — `resolventEdge γ e₁ ‖z‖² ≤ re ⟪z, A' z⟫` on `yᗮ`. -/
theorem spectralSeparation_at_secondEdge_of_compressionBound [Nontrivial E]
    {R : E →L[ℂ] E} (hRsym : IsSelfAdjoint R) {γ e₀ e₁ : ℝ} (hγ : 0 < γ) (h0 : 0 ≤ e₀)
    (hlt : e₀ < e₁) {y : E} (hy0 : y ≠ 0)
    (hAy : ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) y = (resolventEdge γ e₀ : ℂ) • y)
    (hC : ∀ z : ↥(BookProof.SpectralSplitting.eigenLine y)ᗮ,
      resolventEdge γ e₁ * ‖z‖ ^ 2 ≤
        (inner ℂ z (BookProof.SpectralSplitting.compressed
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (isSelfAdjoint_reflection R hRsym γ) hAy z)
          : ℂ).re) :
    BookProof.RitzCertificate.SpectralSeparation
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (resolventEdge γ e₀) (resolventEdge γ e₁) :=
  BookProof.SpectralSplitting.spectralSeparation_of_compressionBound _ 
    (isSelfAdjoint_reflection R hRsym γ) hy0 hAy
    (le_of_lt (secondEdge_lt_level hγ h0 hlt)) hC

/-- **The second-edge band closes from a form bound, with no `hsep`.**  The hypothesis of
`reflected_band_closes_at_secondEdge` is discharged by the compression bound of
`spectralSeparation_at_secondEdge_of_compressionBound`; everything else is unchanged, so the widths
vanish and the edge lies in the emitted band eventually. -/
theorem reflected_band_closes_at_secondEdge_of_formBound [Nontrivial E]
    {R : E →L[ℂ] E} (hRsym : IsSelfAdjoint R) {γ : ℝ}
    {C Dmin hstep : ℝ} (hh : 0 < hstep)
    (V : F →L[ℂ] E) (psiB : F →L[ℂ] F)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    {yy : ℕ → F} {mu : ℕ → ℝ} (heigB : ∀ m, psiB (yy m) = (mu m : ℂ) • yy m)
    (hyy : ∀ m, ‖V (yy m)‖ = 1)
    (hbound : ∀ m, ‖R - BookProof.ChapterSirkEndToEnd.sirkApprox V psiB‖
      ≤ BookProof.ChapterH6.sirkBound C Dmin hstep 1 m)
    {e₀ e₁ : ℝ} (hγ : 0 < γ) (h0 : 0 ≤ e₀) (hlt : e₀ < e₁)
    (hsInf : sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) = resolventEdge γ e₀)
    {y : E} (hy0 : y ≠ 0)
    (hAy : ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) y = (resolventEdge γ e₀ : ℂ) • y)
    (hC : ∀ z : ↥(BookProof.SpectralSplitting.eigenLine y)ᗮ,
      resolventEdge γ e₁ * ‖z‖ ^ 2 ≤
        (inner ℂ z (BookProof.SpectralSplitting.compressed
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (isSelfAdjoint_reflection R hRsym γ) hAy z)
          : ℂ).re)
    {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ m, BookProof.RitzCertificate.rayleigh
      ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)) ≤ resolventEdge γ e₁ - delta) :
    Tendsto (templeBandWidth
        (fun m => BookProof.RitzCertificate.rayleigh
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)))
        (fun m => BookProof.RitzCertificate.resid
          ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)))
        (resolventEdge γ e₁)) atTop (𝓝 0) ∧
      ∀ᶠ m in atTop,
        sInf (spectrum ℝ ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R)) ∈
          Set.Icc (BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)) -
            BookProof.RitzCertificate.resid
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m)) ^ 2 /
              (resolventEdge γ e₁ - BookProof.RitzCertificate.rayleigh
                ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))))
            (BookProof.RitzCertificate.rayleigh
              ((γ⁻¹ : ℝ) • (1 : E →L[ℂ] E) - R) (V (yy m))) :=
  reflected_band_closes_at_secondEdge hRsym hh V psiB hVV heigB hyy hbound hγ h0 hlt hsInf
    (spectralSeparation_at_secondEdge_of_compressionBound hRsym hγ h0 hlt hy0 hAy hC)
    hdelta hgap

end BandNondegenerate


/-! ## 20. A worked second-edge instance

The two-dimensional model `diag (5/6, 2/3)` on `EuclideanSpace ℂ (Fin 2)`, in the frame of
`vTrial` / `vOther` from `ChapterSpectralSplitting`, the operator written as
`5/6 − (1/6) P_{vOther}`.  Its bottom spectral point is `2/3` (`Aedge_sInf`) — the reflected edge
of `diag (2, 5)` at `γ = 1`, since `resolventEdge 1 2 = 2/3` and `resolventEdge 1 5 = 5/6`.  The
mixed vector `wMix` has Rayleigh quotient `109/150` and residual squared `4/625`, and at the level
`b = 5/6` the band `[θ − ε²/(b − θ), θ]` has lower end exactly `2/3`: the enclosure
`Aedge_band_membership` is an equality on the left, and `norm_num` checks it. -/

section SecondEdgeInstance

open BookProof.RitzCertificate
open BookProof.SpectralSplitting


noncomputable def projO : E2 →L[ℂ] E2 := (innerSL ℂ vOther).smulRight vOther

noncomputable def Aedge : E2 →L[ℂ] E2 := (5 / 6 : ℂ) • 1 - (1 / 6 : ℂ) • projO

theorem projO_apply (x : E2) : projO x = (inner ℂ vOther x) • vOther := rfl

theorem projO_sa : IsSelfAdjoint projO := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  change (inner ℂ (projO x) y) = (inner ℂ x (projO y))
  rw [projO_apply, projO_apply, inner_smul_left, inner_smul_right]
  have hx' : (inner ℂ x vOther) = starRingEnd ℂ (inner ℂ vOther x) := by rw [inner_conj_symm]
  rw [hx']
  ring

theorem Aedge_sa : IsSelfAdjoint Aedge := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_
  change (inner ℂ (Aedge x) y) = (inner ℂ x (Aedge y))
  have hAx : Aedge x = (5 / 6 : ℂ) • x - (1 / 6 : ℂ) • (projO x) := rfl
  have hAy : Aedge y = (5 / 6 : ℂ) • y - (1 / 6 : ℂ) • (projO y) := rfl
  simp only [hAx, hAy, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    projO_apply]
  have hx : (inner ℂ x vOther) = starRingEnd ℂ (inner ℂ vOther x) := by rw [inner_conj_symm]
  rw [hx]
  simp only [map_div₀, map_one, Complex.conj_ofNat]
  ring

theorem projO_self : projO vOther = vOther := by
  rw [projO_apply, inner_other_other]
  simp

theorem Aedge_other : Aedge vOther = (2 / 3 : ℂ) • vOther := by
  rw [Aedge, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, projO_self]
  module

theorem inner_other_trial : (inner ℂ vOther vTrial) = 0 := by
  have h' : (inner ℂ vOther vTrial) = starRingEnd ℂ (inner ℂ vTrial vOther) := by
    rw [inner_conj_symm]
  rw [h', inner_trial_other]
  simp

theorem Aedge_orth (z : ↥(eigenLine vOther)ᗮ) :
    Aedge (z : E2) = (5 / 6 : ℂ) • (z : E2) := by
  have hz0 : (inner ℂ (z : E2) vOther) = 0 :=
    (Submodule.mem_orthogonal' (K := eigenLine vOther) (z : E2)).mp z.2 vOther
      (Submodule.mem_span_singleton_self vOther)
  have hz : (inner ℂ vOther (z : E2)) = 0 := by
    have h' : (inner ℂ vOther (z : E2)) = starRingEnd ℂ (inner ℂ (z : E2) vOther) := by
      rw [inner_conj_symm]
    rw [h', hz0]
    simp
  rw [Aedge, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, projO_apply, hz]
  module

theorem Aedge_form (x : E2) : (2 / 3 : ℝ) * ‖x‖ ^ 2 ≤ (inner ℂ x (Aedge x)).re := by
  have hx2 : (inner ℂ x x) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hproj : (inner ℂ x (projO x)) = ((Complex.normSq (inner ℂ vOther x) : ℝ) : ℂ) := by
    rw [projO_apply, inner_smul_right, ← inner_conj_symm (𝕜 := ℂ) x vOther]
    exact Complex.mul_conj _
  have hexp : (inner ℂ x (Aedge x))
      = (5 / 6 : ℂ) * (inner ℂ x x) - (1 / 6 : ℂ) * (inner ℂ x (projO x)) := by
    simp only [Aedge, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_sub_right, inner_smul_right]
  have hreal : (inner ℂ x (Aedge x))
      = (((5 / 6 : ℝ) * ‖x‖ ^ 2 - (1 / 6) * Complex.normSq (inner ℂ vOther x) : ℝ) : ℂ) := by
    rw [hexp, hx2, hproj]
    push_cast
    ring
  rw [hreal, Complex.ofReal_re]
  have hb : Complex.normSq (inner ℂ vOther x) ≤ ‖x‖ ^ 2 := by
    have h1 : ‖inner ℂ vOther x‖ ≤ ‖x‖ := by
      have h2 := norm_inner_le_norm (𝕜 := ℂ) vOther x
      simpa [show ‖vOther‖ = 1 from by simp [vOther]] using h2
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (inner ℂ vOther x)]
  nlinarith

theorem Aedge_spectrum_lower : ∀ t ∈ spectrum ℝ Aedge, (2 / 3 : ℝ) ≤ t :=
  (BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum Aedge Aedge_sa (2 / 3)).mp
    Aedge_form

theorem Aedge_two_thirds_mem : (2 / 3 : ℝ) ∈ spectrum ℝ Aedge := by
  rw [spectrum.mem_iff]
  intro hunit
  have hkill : ((algebraMap ℝ (E2 →L[ℂ] E2)) (2 / 3) - Aedge) vOther = 0 := by
    rw [Algebra.algebraMap_eq_smul_one,
      RCLike.real_smul_eq_coe_smul (K := ℂ) (2 / 3) (1 : E2 →L[ℂ] E2)]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, Aedge_other]
    module
  obtain ⟨u, hu⟩ := hunit
  have h0 : (u : E2 →L[ℂ] E2) vOther = 0 := by rw [hu]; exact hkill
  have hv0 : vOther = 0 := by
    have h1 : u.inv ((u : E2 →L[ℂ] E2) vOther) = u.inv 0 := by rw [h0]
    rw [← ContinuousLinearMap.mul_apply, u.inv_val, ContinuousLinearMap.one_apply,
      map_zero] at h1
    exact h1
  have : (vOther : E2) ≠ 0 := by simp [vOther]
  exact this hv0

theorem Aedge_sInf : sInf (spectrum ℝ Aedge) = 2 / 3 := by
  refine le_antisymm ?_ ?_
  · exact csInf_le (BookProof.ChapterSirkRitzSpectrum.spectrum_real_bddBelow Aedge Aedge_sa)
      Aedge_two_thirds_mem
  · exact le_csInf (BookProof.ChapterSirkRitzSpectrum.spectrum_real_nonempty Aedge Aedge_sa)
      Aedge_spectrum_lower


/-- The mixed test vector: three fifths `vTrial` and four fifths `vOther`. -/
noncomputable def wMix : E2 := (3 / 5 : ℂ) • vTrial + (4 / 5 : ℂ) • vOther

theorem projO_trial : projO vTrial = 0 := by
  rw [projO_apply, inner_other_trial]
  simp

theorem Aedge_trial : Aedge vTrial = (5 / 6 : ℂ) • vTrial := by
  rw [Aedge, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, projO_trial]
  module

theorem Aedge_wMix : Aedge wMix = (1 / 2 : ℂ) • vTrial + (8 / 15 : ℂ) • vOther := by
  rw [wMix, map_add, map_smul, map_smul, Aedge_trial, Aedge_other]
  module

theorem wMix_inner_self : (inner ℂ wMix wMix) = 1 := by
  simp only [wMix, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_trial_trial, inner_other_other, inner_trial_other, inner_other_trial, map_div₀,
    Complex.conj_ofNat, mul_zero, mul_one, add_zero, zero_add]
  norm_num

theorem wMix_norm : ‖wMix‖ = 1 := by
  have h : (inner ℂ wMix wMix) = ((‖wMix‖ : ℂ)) ^ 2 := inner_self_eq_norm_sq_to_K wMix
  rw [wMix_inner_self, ← Complex.ofReal_pow] at h
  have h2 : ‖wMix‖ ^ 2 = 1 := by exact_mod_cast h.symm
  nlinarith [norm_nonneg wMix]

theorem rayleigh_wMix : rayleigh Aedge wMix = 109 / 150 := by
  rw [rayleigh, Aedge_wMix]
  have h : (inner ℂ wMix ((1 / 2 : ℂ) • vTrial + (8 / 15 : ℂ) • vOther))
      = ((109 / 150 : ℝ) : ℂ) := by
    simp only [wMix, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_trial_trial, inner_other_other, inner_trial_other, inner_other_trial, map_div₀,
      Complex.conj_ofNat, mul_zero, mul_one, add_zero, zero_add]
    norm_num
  rw [h, Complex.ofReal_re]

theorem norm_A_wMix_sq : ‖Aedge wMix‖ ^ 2 = 481 / 900 := by
  have hinner : (inner ℂ ((1 / 2 : ℂ) • vTrial + (8 / 15 : ℂ) • vOther)
      ((1 / 2 : ℂ) • vTrial + (8 / 15 : ℂ) • vOther)) = ((481 / 900 : ℝ) : ℂ) := by
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_trial_trial, inner_other_other, inner_trial_other, inner_other_trial, map_div₀,
      Complex.conj_ofNat, mul_zero, mul_one, add_zero, zero_add]
    norm_num
  have h : (inner ℂ (Aedge wMix) (Aedge wMix)) = ((481 / 900 : ℝ) : ℂ) := by
    rw [Aedge_wMix]
    exact hinner
  have h' : (inner ℂ (Aedge wMix) (Aedge wMix)) = ((‖Aedge wMix‖ : ℂ)) ^ 2 :=
    inner_self_eq_norm_sq_to_K _
  rw [← Complex.ofReal_pow] at h'
  rw [h'] at h
  exact_mod_cast h

theorem resid_wMix_sq : resid Aedge wMix ^ 2 = 4 / 625 := by
  have h := norm_apply_sq Aedge wMix wMix_norm
  rw [rayleigh_wMix, norm_A_wMix_sq] at h
  linarith

/-- **The second-edge band holds numerically on `diag (5/6, 2/3)`.**  With `vTrial` a unit vector
of quotient `5/6` and `vOther` the edge eigenvector, the mixed vector `wMix` has
`θ = 109/150` and `ε² = 4/625`; at the level `b = 5/6` the band's lower end is exactly `2/3`, so
`sInf (spectrum ℝ Aedge) = 2/3` lies in `[θ − ε²/(b − θ), θ]`.  The endpoints are `norm_num`. -/
theorem Aedge_band_membership :
    (2 / 3 : ℝ) ∈ Set.Icc (rayleigh Aedge wMix - resid Aedge wMix ^ 2 /
      (5 / 6 - rayleigh Aedge wMix)) (rayleigh Aedge wMix) := by
  rw [rayleigh_wMix, resid_wMix_sq]
  norm_num

/-- The same membership with the numbers exposed: the band is `[2/3, 109/150]`. -/
theorem Aedge_band_membership_num :
    (2 / 3 : ℝ) ∈ Set.Icc ((109 : ℝ) / 150 - (4 : ℝ) / 625 / (5 / 6 - 109 / 150))
      (109 / 150) := by
  rw [← rayleigh_wMix, ← resid_wMix_sq]
  exact Aedge_band_membership


end SecondEdgeInstance

end BookProof.ChapterResolventTransfer

end
