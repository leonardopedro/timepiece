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
ground-state energy is (`resolventEdge_pos`), which the generic route cannot reach. -/
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
`sirk_reflected_temple_band_of_shiftInvertNorm` to `b = resolventEdge γ e`: the complete
two-sided enclosure of the reflected edge, with its strictness, follows from the lower bound
`e ‖x‖² ≤ re ⟪x, A x⟫` on the domain of `A` alone. -/
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

end BookProof.ChapterResolventTransfer

end
