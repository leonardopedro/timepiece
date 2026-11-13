import Mathlib
import BookProof.Sirk.ChapterHashimotoShiftInvert
import BookProof.Sirk.ChapterSirkEndToEnd

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
here is the spectral separation of `A` itself — that stays the S2 input.
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

end Reflected

end BookProof.ChapterResolventTransfer

end
