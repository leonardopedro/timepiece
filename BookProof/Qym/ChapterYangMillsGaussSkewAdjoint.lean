import BookProof.Qym.ChapterYangMillsGaussClosure

/-!
# Skew-adjointness of the Gauss closure: the one inclusion that is missing

`BookProof/Qym/ChapterYangMillsGaussClosure.lean` proves `closure 𝒢_d ≤ −(closure 𝒢_d)†`:
the domain of the closure sits inside the domain of its adjoint, where the adjoint acts as
the negative.  A skew operator is **skew-adjoint** when the two domains coincide, i.e. when
`A† = −A`.  This module states that target as a predicate and proves that, given the
inclusion already available, skew-adjointness is *equivalent* to the reverse inclusion
`dom A† ⊆ dom A` — so nothing else is missing.

## Why the reverse inclusion is not proved here

`dom A† ⊆ dom A` is the classical essential-skew-adjointness statement for the derivation
`Σ_m v_m ∂_m` of the colour rotation on the Gauss–polynomial core.  The two standard proofs
both need input the corpus does not carry: either the unitary group `e^{tM}` of the linear
flow (a Stone theorem, absent from Mathlib), or the density of the polynomial core in the
graph norm of `A†` (an elliptic-regularity/Fourier estimate).  What is proved below is the
reduction: the domain inclusion is the *only* remaining hypothesis, and the module records
the two equivalent forms it can be attacked in.

## Contents

* `SkewAdjoint` — the predicate `A† = −A`;
* `skewAdjoint_iff_adjoint_domain_le` — under `A ≤ −A†`, it is equivalent to
  `dom A† ≤ dom A`;
* `skewAdjoint_adjoint_domain` — a skew-adjoint operator has `dom A† = dom A`;
* `skew_norm_add_one` — on a skew operator the graph norm is the orthogonal sum:
  `‖A x + x‖² = ‖A x‖² + ‖x‖²`, hence `A + 1` is injective and bounded below by `1`
  (the deficiency-index input, `skew_add_one_injective`, `skew_add_one_norm_le`);
* the Gauss instantiations `gaussPMap_closure_skewAdjoint_iff_domain_le` and
  `gaussPMap_closure_skewAdjoint_of_domain_le`.
-/

open MvPolynomial

namespace BookProof.Qym.GaussSkewAdjoint

open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.Qym.GaussSkew
open BookProof.Qym.GaussClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## The predicate -/

/-- **Skew-adjointness** of a densely defined operator: the adjoint is the negative, so in
particular `dom A† = dom A`.  This is the operator-theoretic form of
`⟪A x, y⟫ = −⟪x, A y⟫` *on the adjoint's domain*, and the hypothesis of Stone's theorem for
`A`. -/
def SkewAdjoint (A : E →ₗ.[ℂ] E) : Prop := A.adjoint = -A

/-! ## The reduction -/

/-- **Skew-adjointness is exactly the reverse domain inclusion.**  If `−A†` already extends
`A` (`A ≤ −A†`, the content of `gaussPMap_closure_le_negAdjoint`), then `A† = −A` holds iff
`dom A† ⊆ dom A`.  So the only missing input is a domain statement. -/
theorem skewAdjoint_iff_adjoint_domain_le {A : E →ₗ.[ℂ] E} (hle : A ≤ -(A.adjoint)) :
    A.adjoint.domain ≤ A.domain ↔ SkewAdjoint A := by
  constructor
  · intro hdom
    -- on `dom A` the extension `−A†` agrees with `A`
    have hval : ∀ z : A.domain, A z = -(A.adjoint ⟨(z : E), hle.1 z.2⟩) := by
      intro z
      simpa using hle.2 (x := z) (y := ⟨(z : E), hle.1 z.2⟩) rfl
    refine LinearPMap.eq_of_le_of_domain_eq ?_ ?_
    · refine ⟨fun z hz => hdom hz, ?_⟩
      intro z w hzw
      rw [LinearPMap.neg_apply]
      have h1 : A.adjoint z = -(A ⟨(z : E), hdom z.2⟩) := by
        have h2 := hval ⟨(z : E), hdom z.2⟩
        rw [show (A.adjoint ⟨(z : E), hle.1 (hdom z.2)⟩) = A.adjoint z from rfl] at h2
        have h3 := congrArg Neg.neg h2
        simp only [neg_neg] at h3
        exact h3.symm
      have h2 : (⟨(z : E), hdom z.2⟩ : A.domain) = w := Subtype.ext hzw
      rw [h1, h2]
    · rw [LinearPMap.neg_domain]
      exact le_antisymm hdom hle.1
  · intro h
    rw [SkewAdjoint] at h
    rw [h, LinearPMap.neg_domain]

/-- A skew-adjoint operator has the adjoint's domain equal to its own. -/
theorem skewAdjoint_adjoint_domain {A : E →ₗ.[ℂ] E} (h : SkewAdjoint A) :
    A.adjoint.domain = A.domain := by
  rw [SkewAdjoint] at h
  rw [h, LinearPMap.neg_domain]

/-! ## The graph norm on a skew operator

On a skew operator `‖A x + x‖² = ‖A x‖² + ‖x‖²`: the graph norm is the orthogonal sum of
`‖A x‖²` and `‖x‖²`.  This is what makes `A ∓ 1` injective with closed range, i.e. it is
the deficiency-index computation in its one available half. -/

omit [CompleteSpace E] in
/-- The real part of `⟪A x, x⟫` vanishes for a skew operator. -/
theorem skew_re_inner_zero {A : E →ₗ.[ℂ] E}
    (hskew : ∀ x y : A.domain, inner ℂ (A x) (y : E) = -inner ℂ (x : E) (A y))
    (x : A.domain) :
    (inner ℂ (A x) (x : E)).re = 0 := by
  have h := hskew x x
  have hconj : inner ℂ (x : E) (A x) = (starRingEnd ℂ) (inner ℂ (A x) (x : E)) :=
    (inner_conj_symm (x : E) (A x)).symm
  rw [hconj] at h
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

omit [CompleteSpace E] in
/-- On a skew operator the graph norm is the orthogonal sum: `‖A x + x‖² = ‖A x‖² + ‖x‖²`. -/
theorem skew_norm_add_one {A : E →ₗ.[ℂ] E}
    (hskew : ∀ x y : A.domain, inner ℂ (A x) (y : E) = -inner ℂ (x : E) (A y))
    (x : A.domain) :
    ‖A x + (x : E)‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ)]
  have h := skew_re_inner_zero hskew x
  rw [show RCLike.re (inner ℂ (A x) (x : E)) = 0 from h]
  ring

omit [CompleteSpace E] in
/-- Consequently `A + 1` is bounded below by `1` on the domain. -/
theorem skew_add_one_norm_le {A : E →ₗ.[ℂ] E}
    (hskew : ∀ x y : A.domain, inner ℂ (A x) (y : E) = -inner ℂ (x : E) (A y))
    (x : A.domain) :
    ‖(x : E)‖ ≤ ‖A x + (x : E)‖ := by
  have h := skew_norm_add_one hskew x
  have hle : ‖(x : E)‖ ^ 2 ≤ ‖A x + (x : E)‖ ^ 2 := by
    rw [h]
    have hnn : (0 : ℝ) ≤ ‖A x‖ ^ 2 := sq_nonneg _
    linarith
  have hsqrt := Real.sqrt_le_sqrt hle
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsqrt

omit [CompleteSpace E] in
/-- Hence `A + 1` is injective on the domain. -/
theorem skew_add_one_injective {A : E →ₗ.[ℂ] E}
    (hskew : ∀ x y : A.domain, inner ℂ (A x) (y : E) = -inner ℂ (x : E) (A y))
    {x : A.domain} (hx : A x + (x : E) = 0) : (x : E) = 0 := by
  have h := skew_add_one_norm_le hskew x
  rw [hx, norm_zero] at h
  exact norm_le_zero_iff.1 h

/-! ## The Gauss closure -/

variable {D : Submodule ℂ (L2d 99)}

/-- **Skew-adjointness of the Gauss closure is exactly `dom A† ⊆ dom A`**: the forward
inclusion is `gaussPMap_closure_le_negAdjoint`, so only the reverse one is missing. -/
theorem gaussPMap_closure_skewAdjoint_iff_domain_le (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99))) :
    (gaussPMap G d Φ).closure.adjoint.domain ≤ (gaussPMap G d Φ).closure.domain
      ↔ SkewAdjoint (gaussPMap G d Φ).closure :=
  skewAdjoint_iff_adjoint_domain_le (gaussPMap_closure_le_negAdjoint G d Φ hD)

/-- **Skew-adjointness from the reverse domain inclusion.**  This is the conditional form:
`gaussPMap_closure_skewAdjoint_iff_domain_le` says the hypothesis is not a weakening. -/
theorem gaussPMap_closure_skewAdjoint_of_domain_le (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99)))
    (hdom : (gaussPMap G d Φ).closure.adjoint.domain ≤ (gaussPMap G d Φ).closure.domain) :
    SkewAdjoint (gaussPMap G d Φ).closure :=
  (gaussPMap_closure_skewAdjoint_iff_domain_le G d Φ hD).1 hdom

/-- On the Gauss closure the graph norm is the orthogonal sum of `‖A x‖²` and `‖x‖²`. -/
theorem gaussPMap_closure_norm_add_one (G : GaugeAlgebra 8) (d : Fin 8)
    (Φ : CoreRep 99 D) (hD : Dense (D : Set (L2d 99)))
    (x : (gaussPMap G d Φ).closure.domain) :
    ‖(gaussPMap G d Φ).closure x + (x : L2d 99)‖ ^ 2
      = ‖(gaussPMap G d Φ).closure x‖ ^ 2 + ‖(x : L2d 99)‖ ^ 2 :=
  skew_norm_add_one (fun x y => gaussPMap_closure_skew G d Φ hD x y) x

/-- The field-space closure is skew-adjoint exactly when the adjoint's domain is contained
in the closure's domain. -/
theorem gaussPMap_polyGaussCore_skewAdjoint_iff_domain_le (G : GaugeAlgebra 8) (d : Fin 8) :
    (gaussPMap G d (coreRepPoly 99)).closure.adjoint.domain
        ≤ (gaussPMap G d (coreRepPoly 99)).closure.domain
      ↔ SkewAdjoint (gaussPMap G d (coreRepPoly 99)).closure :=
  gaussPMap_closure_skewAdjoint_iff_domain_le G d (coreRepPoly 99) polyGaussCore_dense

end

end BookProof.Qym.GaussSkewAdjoint
