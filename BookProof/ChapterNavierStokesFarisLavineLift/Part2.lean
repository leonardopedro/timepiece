import Mathlib
import BookProof.ChapterNavierStokesFullEsa
import BookProof.ChapterNavierStokesFarisLavineLift.Part1

/-!
# The one-particle comparison operator, and how the Faris–Lavine bounds lift

Companion to `BookProof.ChapterNavierStokesSecondQuant`, which lifts *essential
self-adjointness* from the sectors of a Fock space to the finite-particle
domain.  This module supplies the other two ingredients of the Faris–Lavine
route to essential self-adjointness of the Navier–Stokes Hamiltonian:

**1. The one-particle comparison operator.**  In the fiber space the advection
term is a *linear* vector field `V(u)`, so the natural comparison operator is
`n = ∑ᵢ πᵢ² + ∑ᵢ Vᵢ² + I`.  `ComparisonData` packages the (symmetric) momenta
`πᵢ` and drifts `Vᵢ` on a dense domain of an arbitrary complex inner product
space, and `ComparisonData.comparison` is the operator.  Proved here:
`comparison_isSymmetricDom` (symmetry), `comparison_inner_eq` (the quadratic
form is `∑‖πᵢv‖² + ∑‖Vᵢv‖² + ‖v‖²` — no cross terms, because the squares are
squares of symmetric operators), `comparison_ge_norm_sq` (`n ≥ I`, the
positivity Faris–Lavine asks of the comparison operator) and two criteria for
essential self-adjointness: `comparison_hasZeroDeficiencyOn_of_eigenvectors`
from a total family of eigenvectors, and `diagComparison_hasZeroDeficiencyOn`,
an unconditional instance in the representation in which the `πᵢ` and `Vᵢ` are
simultaneously diagonal (the fiber momentum representation), where the operator
is also genuinely unbounded (`diagComparison_not_bounded`).

**2. How the two Faris–Lavine bounds behave when summed over particles.**  On an
`m`-particle sector the second-quantized operators are `Ĥ = ∑ₖ hₖ` and
`N̂ = ∑ₖ nₖ + I`.

* `norm_sum_le_of_pairwise` — the *operator* bound lifts with the **same**
  constant provided the domination holds *pairwise*,
  `|Re⟪hₖv, hₗv⟫| ≤ c² Re⟪nₖv, nₗv⟫` for all pairs `k, l`.
* `not_forall_norm_sum_le_of_pointwise` — and pairwise is genuinely needed: the
  naive argument "triangle inequality plus the one-particle bound" is **not**
  valid.  There are two pairs `(hₖ, nₖ)` with `‖hₖ x‖ ≤ ‖nₖ x‖` for every `x`
  and yet `‖(h₀ + h₁)x‖ > ‖(n₀ + n₁)x‖`; the step
  `∑ₖ ‖nₖ Ψ‖ ≤ ‖N̂ Ψ‖` in the informal argument is false as stated.
* `abs_re_inner_commutator_sum_le` — the *form commutator* bound, by contrast,
  lifts exactly as the informal argument says, because quadratic forms are
  additive: with `[hₖ, nₗ] = 0` for `k ≠ l` (different particles) one has
  `[Ĥ, N̂] = ∑ₖ [hₖ, nₖ]`(`commDom_sum`, `commDom_add_id`) and therefore
  `|Re⟪Ψ, [Ĥ, N̂]Ψ⟫| ≤ c₂ Re⟪Ψ, N̂Ψ⟫`.

## Scope

Nothing here claims essential self-adjointness of the continuum Navier–Stokes
generator.  The Faris–Lavine criterion itself is not proved anywhere in this
project; it enters as a named hypothesis (`ns_esa_of_farisLavine_dense`).  What
is established here is exactly which bounds survive second quantization, and in
what form.
-/

namespace BookProof.NavierStokesFlow

namespace FarisLavineLift

open FullEsa
/-! ## Lifting the two Faris–Lavine bounds over the particles of a sector -/

section Lifting

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem coe_sum_apply (s : Finset κ) (A : κ → (D →ₗ[ℂ] D)) (v : D) :
    (((∑ k ∈ s, A k) v : D) : F) = ∑ k ∈ s, ((A k v : D) : F) := by
  simp

/-- **Lifting the operator bound to a sector.**  If the one-particle domination
holds *pairwise* — `|Re⟪hₖ v, hₗ v⟫| ≤ c² Re⟪nₖ v, nₗ v⟫` for every pair of
particles — then the sums obey the same bound with the same constant:
`‖∑ₖ hₖ v‖ ≤ c ‖∑ₖ nₖ v‖`.  The diagonal `k = l` of the hypothesis is the
one-particle bound `‖hv‖ ≤ c‖nv‖`; the off-diagonal part is what the tensor
structure of the Fock sector provides, and by
`not_forall_norm_sum_le_of_pointwise` it cannot be dispensed with. -/
theorem norm_sum_le_of_pairwise (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (cst : ℝ)
    (hc : 0 ≤ cst) (v : D)
    (hpair : ∀ k ∈ s, ∀ l ∈ s,
      |(inner ℂ ((h k v : D) : F) ((h l v : D) : F) : ℂ).re|
        ≤ cst ^ 2 * (inner ℂ ((n k v : D) : F) ((n l v : D) : F) : ℂ).re) :
    ‖(((∑ k ∈ s, h k) v : D) : F)‖ ≤ cst * ‖(((∑ k ∈ s, n k) v : D) : F)‖ := by
  have hL : ‖(((∑ k ∈ s, h k) v : D) : F)‖ ^ 2
      = ∑ k ∈ s, ∑ l ∈ s, (inner ℂ ((h k v : D) : F) ((h l v : D) : F) : ℂ).re := by
    rw [coe_sum_apply s h v]
    exact norm_sum_sq_eq s fun k => ((h k v : D) : F)
  have hR : ‖(((∑ k ∈ s, n k) v : D) : F)‖ ^ 2
      = ∑ k ∈ s, ∑ l ∈ s, (inner ℂ ((n k v : D) : F) ((n l v : D) : F) : ℂ).re := by
    rw [coe_sum_apply s n v]
    exact norm_sum_sq_eq s fun k => ((n k v : D) : F)
  have hsq : ‖(((∑ k ∈ s, h k) v : D) : F)‖ ^ 2
      ≤ cst ^ 2 * ‖(((∑ k ∈ s, n k) v : D) : F)‖ ^ 2 := by
    rw [hL, hR, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l hl => le_trans (le_abs_self _) (hpair k hk l hl)
  nlinarith [norm_nonneg (((∑ k ∈ s, h k) v : D) : F),
    norm_nonneg (((∑ k ∈ s, n k) v : D) : F),
    mul_nonneg hc (norm_nonneg (((∑ k ∈ s, n k) v : D) : F))]

/-- Adding the identity to the comparison operator can only help, provided the
comparison operator is non-negative on the state. -/
theorem norm_le_norm_add_id (N : D →ₗ[ℂ] D) (v : D)
    (hpos : 0 ≤ (inner ℂ ((N v : D) : F) ((v : F)) : ℂ).re) :
    ‖((N v : D) : F)‖ ≤ ‖((((N + LinearMap.id : D →ₗ[ℂ] D)) v : D) : F)‖ := by
  have : ((((N + LinearMap.id : D →ₗ[ℂ] D)) v : D) : F) = ((N v : D) : F) + (v : F) := by
    simp
  rw [this]
  exact norm_le_norm_add_of_re_inner_nonneg hpos

/-! ### The commutator -/

/-- The commutator of two domain-preserving operators. -/
def commDom (A B : D →ₗ[ℂ] D) : D →ₗ[ℂ] D := A.comp B - B.comp A

@[simp] theorem commDom_apply (A B : D →ₗ[ℂ] D) (v : D) :
    commDom A B v = A (B v) - B (A v) := rfl

/-- Adding the identity to the second argument does not change the
commutator: `[Ĥ, N̂ + I] = [Ĥ, N̂]`. -/
theorem commDom_add_id (A B : D →ₗ[ℂ] D) :
    commDom A (B + LinearMap.id) = commDom A B := by
  ext v
  simp [commDom]

/-- **The commutator of second-quantized operators is the second quantization of
the commutators**: if operators belonging to different particles commute, then
`[∑ₖ hₖ, ∑ₗ nₗ] = ∑ₖ [hₖ, nₖ]`. -/
theorem commDom_sum (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D))
    (hcomm : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (h k).comp (n l) = (n l).comp (h k)) :
    commDom (∑ k ∈ s, h k) (∑ k ∈ s, n k) = ∑ k ∈ s, commDom (h k) (n k) := by
  ext v
  have hexp : (commDom (∑ k ∈ s, h k) (∑ k ∈ s, n k)) v
      = ∑ k ∈ s, ∑ l ∈ s, (h k (n l v) - n l (h k v)) := by
    simp only [commDom, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
      Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  rw [hexp]
  have hdiag : ∀ k ∈ s, ∑ l ∈ s, (h k (n l v) - n l (h k v)) = commDom (h k) (n k) v := by
    intro k hk
    rw [Finset.sum_eq_single_of_mem k hk]
    · simp [commDom]
    · intro l hl hlk
      have := hcomm k hk l hl (Ne.symm hlk)
      have happ := congrArg (fun T : D →ₗ[ℂ] D => T v) this
      simp only [LinearMap.comp_apply] at happ
      rw [happ]
      simp
  rw [Finset.sum_congr rfl hdiag]
  simp

/-- **Lifting the form-commutator bound to a sector.**  Quadratic forms are
additive over the particles, so the one-particle bound
`|⟪v, [hₖ, nₖ]v⟫| ≤ c₂ Re⟪v, nₖ v⟫` sums, and — unlike the operator bound —
this lifting needs nothing beyond the commutation of operators belonging to
different particles.  The comparison operator on the sector is `N̂ = ∑ₖ nₖ + I`,
whose form exceeds that of `∑ₖ nₖ` by `‖v‖² ≥ 0`.

The commutator expectation is bounded in modulus, not in real part: for
symmetric `hₖ`, `nₖ` the number `⟪v, [hₖ, nₖ]v⟫` is purely imaginary, so a bound
on its real part would say nothing. -/
theorem norm_inner_commutator_sum_le (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (c₂ : ℝ)
    (hc₂ : 0 ≤ c₂) (v : D)
    (hcomm : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (h k).comp (n l) = (n l).comp (h k))
    (hbound : ∀ k ∈ s, ‖(inner ℂ ((v : F)) ((commDom (h k) (n k) v : D) : F) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : F)) ((n k v : D) : F) : ℂ).re) :
    ‖(inner ℂ ((v : F))
        ((commDom (∑ k ∈ s, h k) ((∑ k ∈ s, n k) + LinearMap.id) v : D) : F) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : F))
        ((((∑ k ∈ s, n k) + LinearMap.id : D →ₗ[ℂ] D) v : D) : F) : ℂ).re := by
  rw [commDom_add_id, commDom_sum s h n hcomm]
  have hleft : (inner ℂ ((v : F)) (((∑ k ∈ s, commDom (h k) (n k)) v : D) : F) : ℂ)
      = ∑ k ∈ s, (inner ℂ ((v : F)) ((commDom (h k) (n k) v : D) : F) : ℂ) := by
    rw [coe_sum_apply s (fun k => commDom (h k) (n k)) v, inner_sum]
  have hright : (inner ℂ ((v : F))
        ((((∑ k ∈ s, n k) + LinearMap.id : D →ₗ[ℂ] D) v : D) : F) : ℂ).re
      = (∑ k ∈ s, (inner ℂ ((v : F)) ((n k v : D) : F) : ℂ).re) + ‖(v : F)‖ ^ 2 := by
    have hcoe : ((((∑ k ∈ s, n k) + LinearMap.id : D →ₗ[ℂ] D) v : D) : F)
        = (∑ k ∈ s, ((n k v : D) : F)) + (v : F) := by
      simp
    rw [hcoe, inner_add_right, Complex.add_re, inner_sum, Complex.re_sum]
    congr 1
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((v : F))
  rw [hleft, hright]
  have habs : ‖∑ k ∈ s, (inner ℂ ((v : F)) ((commDom (h k) (n k) v : D) : F) : ℂ)‖
      ≤ ∑ k ∈ s, c₂ * (inner ℂ ((v : F)) ((n k v : D) : F) : ℂ).re :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum hbound)
  have hsq : (0 : ℝ) ≤ c₂ * ‖(v : F)‖ ^ 2 := mul_nonneg hc₂ (sq_nonneg _)
  rw [← Finset.mul_sum] at habs
  nlinarith [habs, hsq]

/-- The same bound in the shape the Faris–Lavine criterion is stated in: the
right-hand side is the modulus of `⟪v, N̂ v⟫`, which for a non-negative
comparison operator agrees with its real part. -/
theorem norm_inner_commutator_sum_le' (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (c₂ : ℝ)
    (hc₂ : 0 ≤ c₂) (v : D)
    (hcomm : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (h k).comp (n l) = (n l).comp (h k))
    (hbound : ∀ k ∈ s, ‖(inner ℂ ((v : F)) ((commDom (h k) (n k) v : D) : F) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : F)) ((n k v : D) : F) : ℂ).re) :
    ‖(inner ℂ ((v : F))
        ((commDom (∑ k ∈ s, h k) ((∑ k ∈ s, n k) + LinearMap.id) v : D) : F) : ℂ)‖
      ≤ c₂ * ‖(inner ℂ ((v : F))
        ((((∑ k ∈ s, n k) + LinearMap.id : D →ₗ[ℂ] D) v : D) : F) : ℂ)‖ := by
  refine le_trans (norm_inner_commutator_sum_le s h n c₂ hc₂ v hcomm hbound) ?_
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hc₂

end Lifting

/-! ## Sharpness: the naive lifting of the operator bound is invalid -/

section Sharpness

open EuclideanSpace

/-- The two-dimensional fiber used for the counterexample. -/
abbrev E2 := EuclideanSpace ℂ (Fin 2)

/-- `hₖ x = xₖ · e₀`: both "particles" push into the same direction. -/
noncomputable def hEx (k : Fin 2) : E2 →ₗ[ℂ] E2 :=
  LinearMap.smulRight (EuclideanSpace.projₗ (𝕜 := ℂ) k)
    (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

/-- `nₖ x = xₖ · eₖ`: the comparison operators are the coordinate
projections. -/
noncomputable def nEx (k : Fin 2) : E2 →ₗ[ℂ] E2 :=
  LinearMap.smulRight (EuclideanSpace.projₗ (𝕜 := ℂ) k) (EuclideanSpace.single k (1 : ℂ))

theorem norm_hEx (k : Fin 2) (x : E2) : ‖hEx k x‖ = ‖x k‖ := by
  simp [hEx, norm_smul]

theorem norm_nEx (k : Fin 2) (x : E2) : ‖nEx k x‖ = ‖x k‖ := by
  simp [nEx, norm_smul]

/-- The state on which the naive lifting fails: both coordinates equal to 1. -/
noncomputable def vEx : E2 :=
  EuclideanSpace.single (0 : Fin 2) (1 : ℂ) + EuclideanSpace.single (1 : Fin 2) (1 : ℂ)

theorem vEx_apply (i : Fin 2) : vEx i = 1 := by
  fin_cases i <;> simp [vEx, EuclideanSpace.single_apply]

theorem norm_vEx_sq : ‖vEx‖ ^ 2 = 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [vEx_apply]

theorem sum_nEx_vEx : (nEx 0 + nEx 1) vEx = vEx := by
  simp [nEx, vEx]

theorem sum_hEx_vEx :
    (hEx 0 + hEx 1) vEx = (2 : ℂ) • EuclideanSpace.single (0 : Fin 2) (1 : ℂ) := by
  simp only [LinearMap.add_apply, hEx, LinearMap.smulRight_apply, ← add_smul]
  rw [show (EuclideanSpace.projₗ (𝕜 := ℂ) (0 : Fin 2)) vEx = vEx 0 from rfl,
    show (EuclideanSpace.projₗ (𝕜 := ℂ) (1 : Fin 2)) vEx = vEx 1 from rfl,
    vEx_apply, vEx_apply]
  norm_num

/-- **The informal Fock-space argument for the operator bound is not valid.**
The step `∑ₖ ‖hₖΨ‖ ≤ c ∑ₖ ‖nₖΨ‖ ≤ c ‖N̂Ψ‖` uses the triangle inequality in the
wrong direction: `∑ₖ ‖nₖΨ‖` can exceed `‖∑ₖ nₖΨ‖`.  Concretely there are two
pairs of operators with `‖hₖ x‖ ≤ ‖nₖ x‖` for every `x` and every `k`, and a
state on which the sums violate the same bound.  This is why
`norm_sum_le_of_pairwise` assumes the *pairwise* domination. -/
theorem not_forall_norm_sum_le_of_pointwise :
    ∃ (h n : Fin 2 → (E2 →ₗ[ℂ] E2)) (v : E2),
      (∀ (k : Fin 2) (x : E2), ‖h k x‖ ≤ ‖n k x‖) ∧
        ‖(n 0 + n 1) v‖ < ‖(h 0 + h 1) v‖ := by
  refine ⟨hEx, nEx, vEx, fun k x => le_of_eq (by rw [norm_hEx, norm_nEx]), ?_⟩
  have hn : ‖(nEx 0 + nEx 1) vEx‖ ^ 2 = 2 := by
    rw [sum_nEx_vEx]; exact norm_vEx_sq
  have hh : ‖(hEx 0 + hEx 1) vEx‖ = 2 := by
    rw [sum_hEx_vEx, norm_smul, EuclideanSpace.norm_single]
    norm_num
  rw [hh]
  nlinarith [hn, norm_nonneg ((nEx 0 + nEx 1) vEx)]

end Sharpness

end FarisLavineLift

end BookProof.NavierStokesFlow
