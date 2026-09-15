import Mathlib
import BookProof.ChapterHermiteGalerkinFriedrichs
import BookProof.ChapterComplexShiftCore
import BookProof.ChapterHashimotoShiftInvert.Part1

/-!
# The shift-invert (Hashimoto) trick: the Galerkin/Friedrichs selection theorem
for **unbounded** Hamiltonians

`BookProof.ChapterHermiteGalerkinFriedrichs` proves that a Galerkin/Rayleigh–Ritz
truncation in a complete (Hermite) basis converges — strongly, and in the strong
resolvent sense — to the positive self-adjoint (Friedrichs) extension of the
matrix it is fed, under a standing hypothesis that the operator is **bounded**
on its domain.

That hypothesis is not a restriction on the *physics* the Hashimoto algorithm
does, because the algorithm never applies `H` itself: it applies the
*shift-inverted* operator `R = (H + γ)⁻¹`.  And `R` is bounded — indeed
`‖R‖ ≤ 1/γ` — for **every** positive symmetric `H`, however unbounded, purely
because of positivity.  This module makes that precise and closes the gap:

* `norm_shiftMap_ge` — the shift bound `‖(A + γ)x‖ ≥ γ‖x‖` for a positive
  symmetric operator.  This is why the *effective* Hamiltonian is bounded even
  when `H` is not.
* `closed_of_selfAdjointCriterion`, `shiftRange_isClosed`, `shiftRange_dense`,
  `shiftMap_surjective` — for a positive self-adjoint operator (in the sense of
  `IsPositiveSelfAdjointExtension`) the shifted operator `A + γ` is a bijection
  of its domain onto the whole space.  No boundedness is used.
* `IsShiftInvert`, `exists_isShiftInvert` — hence the bounded inverse
  `R = (A + γ)⁻¹` exists as a genuine element of `F →L[ℂ] F`, with
  `‖R‖ ≤ γ⁻¹` (`IsShiftInvert.opNorm_le`), self-adjoint
  (`IsShiftInvert.isSelfAdjoint`), positive and injective.
* `IsShiftInvert.dom_eq_range`, `IsShiftInvert.apply_eq`,
  `shiftInvert_determines` — `R` remembers everything: its range is the domain
  of `A`, and `A = R⁻¹ − γ` there.  Two positive self-adjoint operators with the
  same shift-invert are the same operator.
* `galerkinCompression_shiftInvert_tendsto`,
  `galerkinResolvent_shiftInvert_tendsto` — the bounded Galerkin theory of
  `BookProof.ChapterHermiteGalerkinFriedrichs` applies verbatim to `R`.
* `hashimoto_shiftInvert_selects_friedrichs` — the headline, **with no
  boundedness hypothesis anywhere**: for a symmetric positive matrix in a
  complete basis and any positive self-adjoint extension `A` of it (the
  Friedrichs extension being one), the shift-inverted operator `R = (A+γ)⁻¹` is
  bounded, the Galerkin truncations of `R` converge strongly to `R` (this is
  precisely strong resolvent convergence of the truncations to `A`), and `R`
  determines `A` uniquely — so the algorithm selects that extension and no
  other.
* `ell2UnboundedExample` and `unbounded_shiftInvert_example` — the hypotheses
  are satisfied by a genuinely **unbounded** operator: the diagonal operator
  `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, whose shift-invert at `γ = 1` is the bounded
  diagonal operator `eₙ ↦ eₙ/(n+1)`.  The boundedness hypothesis of
  `hermiteGalerkin_selects_friedrichs` fails for this `A`
  (`ell2UnboundedExample_unbounded`), while the theorems here apply.

This module treats one **real positive** shift `γ`, where invertibility of
`A + γ` comes from positivity of `A`.  The shifts the Shift-invert Rational
Krylov method actually uses are complex with non-zero imaginary part (which
makes `γ I − A` invertible for every self-adjoint `A`, positive or not), and
they change from step to step; that generalisation, in the same namespace, is
`BookProof.ChapterHashimotoComplexShifts`, whose
`isShiftInvertC_neg_of_isShiftInvert` relates the two notions.
-/

namespace BookProof.HashimotoShiftInvert

open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

/-! ## Part 4 — the Galerkin theory applies to the effective Hamiltonian -/

section Galerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

omit [CompleteSpace F] in
/-- **The Galerkin truncations of the effective Hamiltonian converge.**  This is
the bounded theory of `BookProof.ChapterHermiteGalerkinFriedrichs` applied to
`R = (A + γ)⁻¹`; since `R` is the resolvent of `A` at `−γ`, this *is* strong
resolvent convergence of the truncations to the unbounded `A`. -/
theorem galerkinCompression_shiftInvert_tendsto {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (b : HilbertBasis ℕ ℂ F) (u : F) :
    ∃ (x : F) (hx : x ∈ Dom), A ⟨x, hx⟩ + (γ : ℂ) • x = u ∧
      Tendsto (fun m : ℕ => galerkinCompression R b m u) atTop (nhds x) :=
  ⟨R u, h.mem u, h.shift_apply u, galerkinCompression_tendsto R b u⟩

/-- The resolvents of the Galerkin truncations of the effective Hamiltonian
converge to the resolvent of the effective Hamiltonian. -/
theorem galerkinResolvent_shiftInvert_tendsto {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) (b : HilbertBasis ℕ ℂ F)
    {z : ℂ} (hz : z.im ≠ 0) (u : F) :
    Tendsto (fun m : ℕ => resolvent (galerkinCompression R b m) z u) atTop
      (nhds (resolvent R z u)) :=
  galerkinResolvent_tendsto (h.isSelfAdjoint hsym) b hz u

end Galerkin

/-! ## Part 5 — the headline: no boundedness hypothesis -/

section Headline

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The Hashimoto/Galerkin algorithm selects the Friedrichs extension, for an
unbounded Hamiltonian.**

Let `H` be the matrix of a symmetric positive Hamiltonian in a complete
orthonormal (Hermite) basis, on the domain of finite linear combinations, and
let `A` be *any* positive self-adjoint extension of it — the Friedrichs
extension in particular.  **No boundedness is assumed of `H` or of `A`.**  Then
for every shift `γ > 0`:

1. the shift-inverted operator `R = (A + γ)⁻¹` exists, is everywhere defined,
   self-adjoint, positive and **bounded**, with `‖R‖ ≤ 1/γ` — this is the
   operator the algorithm iterates;
2. its Galerkin truncations converge to it strongly, and their resolvents
   converge to its resolvent at every non-real spectral parameter;
3. `R` determines `A`: any positive self-adjoint operator with the same
   shift-invert has the same domain and the same values.

So the bounded convergence theory covers the unbounded Hamiltonian, and the
extension the algorithm converges to is the one it was given. -/
theorem hashimoto_shiftInvert_selects_friedrichs (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension H A) {γ : ℝ} (hγ : 0 < γ) :
    ∃ R : F →L[ℂ] F,
      IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
      (∀ u : F, 0 ≤ (inner ℂ u (R u) : ℂ).re) ∧
      (∀ u : F, Tendsto (fun m : ℕ => galerkinCompression R b m u) atTop (nhds (R u))) ∧
      (∀ z : ℂ, z.im ≠ 0 → ∀ u : F,
        Tendsto (fun m : ℕ => resolvent (galerkinCompression R b m) z u) atTop
          (nhds (resolvent R z u))) ∧
      (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by
  obtain ⟨-, hsym, hpos, hsa⟩ := hA
  obtain ⟨R, hR⟩ := exists_isShiftInvert hpos hγ (shiftMap_surjective hsym hpos hsa hγ)
  have hRsa : IsSelfAdjoint R := hR.isSelfAdjoint hsym
  refine ⟨R, hR, hR.opNorm_le hpos hγ, hRsa, hR.inner_nonneg hpos hγ,
    fun u => galerkinCompression_tendsto R b u,
    fun z hz u => galerkinResolvent_tendsto hRsa b hz u, ?_⟩
  intro Dom' A' hA'
  obtain ⟨hdom, hval⟩ := shiftInvert_determines hA' hR
  exact ⟨hdom, fun x hx hx' => hval x hx' hx⟩

end Headline

end BookProof.HashimotoShiftInvert
