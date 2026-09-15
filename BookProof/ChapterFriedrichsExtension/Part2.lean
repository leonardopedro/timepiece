import Mathlib
import BookProof.ChapterHashimotoShiftInvert
import BookProof.ChapterFriedrichsExtension.Part1

/-!
# The Friedrichs extension of an **unbounded** positive symmetric operator

`CONSOLIDATED_PLAN.md` §11.4 records two plan items that stand between the proved
Hashimoto/shift-invert machinery and the full claim *"the unbounded continuum
Weyl-gauge Hamiltonian has a Friedrichs extension, and the infinite
Hashimoto/SIRK limit selects exactly it"*.  This module closes the first one.

Until now the Friedrichs theorem entered the project in two forms:

* as a **named hypothesis**
  (`BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded`), shown
  consistent only for an operator already defined on the whole space;
* **discharged by construction, but only in the bounded regime**
  (`BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded`: a densely defined
  symmetric positive operator with `‖H x‖ ≤ C‖x‖` extends continuously).

Here the theorem is **proved with no boundedness hypothesis at all**: every
densely defined, symmetric, positive operator on a complex Hilbert space has a
positive self-adjoint extension.  The construction is the classical one, carried
out in full:

**Part A — the form space.**  The domain carries the *form inner product*
`⟪x, y⟫₁ = ⟪x, y⟫ + ⟪x, H y⟫`.  Symmetry makes it Hermitian and positivity makes
it positive definite (indeed `‖x‖ ≤ ‖x‖₁`), so `FormDom P` — the domain retyped
with that inner product — is an inner product space (`instCore`, `instIPS`), and
`FormSpace P`, its completion, is a Hilbert space.

**Part B — the form space sits inside `F`.**  The inclusion `FormDom P → F` is
norm-decreasing, so it extends to `formExt P : FormSpace P →L[ℂ] F`.  The key
identity `inner_coe_eq` — `⟪x, k⟫₁ = ⟪x + H x, formExt k⟫` for a domain vector
`x` — is the closability of the form in disguise, and it gives
`formExt_injective`: *the form completion adds no ghost vectors*.  This is the
one place where symmetry and positivity of `H` do analytic work.

**Part C — Riesz representation.**  For `u : F` the functional
`k ↦ ⟪u, formExt k⟫` is continuous on the Hilbert space `FormSpace P`, so it is
represented by a vector `formRiesz P u`, and
`friedrichsResolvent P u = formExt P (formRiesz P u)` is a bounded, injective,
positive, self-adjoint operator on `F` with `‖·‖ ≤ 1`.  It is `(H + 1)⁻¹` on the
nose: `friedrichsResolvent_shift` proves `S (x + H x) = x` for every `x` in the
domain.

**Part D — the extension.**  Feeding `S` to the project's own converse
construction `BookProof.HashimotoShiftInvert.invShiftOperator` (`A = S⁻¹ − 1`)
produces the extension, and `friedrichs_extension_exists` states it in the form
the rest of the project consumes,
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`.  Consequences:

* `friedrichs_hypothesis_holds` — the named hypothesis of
  `friedrichs_extension_of_semibounded` is a theorem, not an assumption;
* `friedrichs_extension_of_semibounded_below` — the classical statement, for a
  symmetric operator that is merely *bounded below* (`⟪x, Hx⟫ ≥ −c‖x‖²`), by the
  shift `H ↦ H + c`;
* `weyl_friedrichs_extension_unconditional` — the Weyl-gauge Yang–Mills
  Hamiltonian `½ Σ πᵢ² + ½ Σ Bₐ²` on any dense domain has a Friedrichs
  extension, with **no boundedness hypothesis** (plan item §11.4.1);
* `weyl_hashimoto_selects_friedrichs` — combining with
  `hashimoto_shiftInvert_selects_friedrichs`: in the occupation-number (Hermite)
  realization the extension *exists* and the Hashimoto/SIRK algorithm converges
  to it and to nothing else;
* `unbounded_friedrichs_example` — the construction applied to a genuinely
  unbounded operator (`A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, restricted to the finite-mode
  domain), so nothing here is vacuous.

## Scope

This is the abstract Friedrichs theorem and its application to the Weyl-gauge
Hamiltonian *as an operator on a Hilbert space*.  It does **not** claim the mass
gap, nor a differential (field-space) realization of the magnetic-field operator
`B_{i a}` — that is the second, definitional item of §11.4, settled there in
favour of the occupation-number/Hermite realization.
-/

namespace BookProof.FriedrichsExtension

open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
/-! ## Part D — the Friedrichs extension theorem, with no boundedness -/

open FormDom

variable [CompleteSpace F]

/-- **The Friedrichs extension theorem (K. Friedrichs 1934; Reed–Simon Vol. II
Thm X.23), proved — not assumed — with no boundedness hypothesis.**

Every densely defined, symmetric, positive operator on a complex Hilbert space
has a positive self-adjoint extension: the Friedrichs extension, constructed
here as `S⁻¹ − 1` for the resolvent `S = (H + 1)⁻¹` obtained by Riesz
representation in the completed form space.

This is the unbounded analogue of
`BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded`, and it closes plan
item 1 of `CONSOLIDATED_PLAN.md` §11.4. -/
theorem friedrichs_extension_exists (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension P.op A := by
  have hinj : Function.Injective (friedrichsResolvent P) :=
    friedrichsResolvent_injective P hdense
  refine ⟨_, invShiftOperator (friedrichsResolvent P) hinj 1, ?_⟩
  refine invShiftOperator_isPositiveSelfAdjointExtension (friedrichsResolvent P) hinj 1
    (friedrichsResolvent_isSelfAdjoint P) (friedrichsResolvent_pos P) (dom_le_range P) P.op ?_
  intro x
  have hpre : preim (friedrichsResolvent P) ⟨(x : F), dom_le_range P x.2⟩
      = (x : F) + P.op x :=
    preim_eq _ hinj _ (friedrichsResolvent_shift P x)
  rw [invShiftOperator_apply, hpre]
  push_cast
  module

/-- **The named hypothesis of
`BookProof.YangMillsFriedrichs.friedrichs_extension_of_semibounded` is a
theorem.**  Wherever the project carried "Friedrichs" as an explicit hypothesis,
it can now be discharged. -/
theorem friedrichs_hypothesis_holds :
    ∀ (D' : Submodule ℂ F) (H' : D' →ₗ[ℂ] F), Dense (D' : Set F) →
      SymmetricOn D' H' → (∀ x : D', 0 ≤ quadForm H' x) →
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension H' A :=
  fun D' H' hdense hsym hpos =>
    friedrichs_extension_exists ⟨D', H', hsym, hpos⟩ hdense

/-- **The Weyl-gauge Yang–Mills Hamiltonian has a Friedrichs extension —
unconditionally.**  `½ Σᵢ πᵢ² + ½ Σₐ Bₐ²` on a dense domain, with symmetric
electric- and magnetic-field operators, has a positive self-adjoint extension.
No boundedness of `πᵢ`, `Bₐ` or of the Hamiltonian is assumed: this is
`BookProof.YangMillsFriedrichs.weyl_friedrichs_extension` with its hypothesis
removed. -/
theorem weyl_friedrichs_extension_unconditional {D : Submodule ℂ F} {n m : ℕ}
    {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D}
    (hdense : Dense (D : Set F))
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F),
      IsPositiveSelfAdjointExtension (weylOp pi Bf) A :=
  friedrichs_extension_exists
    ⟨D, weylOp pi Bf, weylOpDom_symmetricOn hpi hB, weylOpDom_quadForm_nonneg hpi hB⟩ hdense

/-! ### The classical statement: symmetric and *bounded below* -/

/-- "`A` on the domain `Dom` is a self-adjoint extension of `H` that is bounded
below by `−c`" — the semibounded analogue of
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension`, which is the case
`c = 0`. -/
def IsSemiboundedSelfAdjointExtension (c : ℝ) {D Dom : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (A : Dom →ₗ[ℂ] F) : Prop :=
  (∀ x : D, ∃ h : (x : F) ∈ Dom, A ⟨(x : F), h⟩ = H x) ∧ SymmetricOn Dom A ∧
    (∀ y : Dom, -c * ‖(y : F)‖ ^ 2 ≤ quadForm A y) ∧
    (∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)

/-- **The Friedrichs extension theorem in its classical form**: a densely defined
symmetric operator that is *bounded below* — `⟪x, H x⟫ ≥ −c‖x‖²`, not necessarily
positive — has a self-adjoint extension with the same lower bound.  Reduced to
the positive case by the shift `H ↦ H + c`. -/
theorem friedrichs_extension_of_semibounded_below {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D H) (c : ℝ)
    (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsSemiboundedSelfAdjointExtension c H A := by
  -- the shifted operator `H + c` is positive
  set Hc : D →ₗ[ℂ] F := H + (c : ℂ) • D.subtype with hHc
  have hshift : ∀ x : D, quadForm Hc x = quadForm H x + c * ‖(x : F)‖ ^ 2 := by
    intro x
    simp only [hHc, quadForm, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_add_right, inner_smul_right, Complex.add_re]
    congr 1
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hcsym : SymmetricOn D Hc := by
    intro x y
    simp only [hHc, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hsym x y]
  have hcpos : ∀ x : D, 0 ≤ quadForm Hc x := by
    intro x
    rw [hshift]
    linarith [hbelow x]
  obtain ⟨Dom, A', hA'⟩ := friedrichs_extension_exists ⟨D, Hc, hcsym, hcpos⟩ hdense
  obtain ⟨hagree, hsymA, hposA, hsa⟩ := hA'
  refine ⟨Dom, A' - (c : ℂ) • Dom.subtype, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨h, hx⟩ := hagree x
    refine ⟨h, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, hx, hHc,
      LinearMap.add_apply]
    module
  · intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hsymA x y]
  · intro y
    have h : quadForm (A' - (c : ℂ) • Dom.subtype) y = quadForm A' y - c * ‖(y : F)‖ ^ 2 := by
      simp only [quadForm, LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        inner_sub_right, inner_smul_right, Complex.sub_re]
      congr 1
      rw [inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    rw [h]
    linarith [hposA y]
  · intro w u hw
    have hw' : ∀ v : Dom, (inner ℂ (A' v) w : ℂ) = inner ℂ (v : F) (u + (c : ℂ) • w) := by
      intro v
      have := hw v
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        inner_sub_left, inner_smul_left, Complex.conj_ofReal] at this
      rw [inner_add_right, inner_smul_right, ← this]
      ring
    obtain ⟨h, hval⟩ := hsa w (u + (c : ℂ) • w) hw'
    refine ⟨h, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply, hval]
    module

/-! ## Part E — the Hashimoto/SIRK limit selects the constructed extension -/

open Filter Topology

/-- **The unbounded selection theorem, with the extension constructed rather than
assumed.**  For a symmetric positive Hamiltonian given by its matrix in a
complete orthonormal (Hermite/occupation-number) basis — *no boundedness* — the
Friedrichs extension `A` exists, and for every shift `γ > 0` the shift-inverted
operator `R = (A + γ)⁻¹` is bounded and self-adjoint, its Galerkin truncations
converge to it strongly and in the resolvent sense, and `R` determines `A`
uniquely.

Together with `friedrichs_extension_exists` this is the full statement of
`CONSOLIDATED_PLAN.md` §11.4: existence *and* selection, for the unbounded
operator. -/
theorem friedrichs_hashimoto_selects (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (R : F →L[ℂ] F),
      IsPositiveSelfAdjointExtension H A ∧ IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧
        IsSelfAdjoint R ∧
        (∀ u : F, Tendsto (fun k : ℕ => galerkinCompression R b k u) atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : F,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R b k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by
  obtain ⟨Dom, A, hA⟩ :=
    friedrichs_extension_exists ⟨finiteModeDomain b, H, hsym, hpos⟩ (finiteModeDomain_dense b)
  obtain ⟨R, hR, hnorm, hsa, -, hstrong, hres, huniq⟩ :=
    hashimoto_shiftInvert_selects_friedrichs b H A hA hγ
  exact ⟨Dom, A, R, hA, hR, hnorm, hsa, hstrong, hres, huniq⟩

/-- **The Weyl-gauge Hamiltonian in the occupation-number realization.**  Plan
item 2 of `CONSOLIDATED_PLAN.md` §11.4 settles the continuum realization in
favour of the occupation-number/Hermite picture: the fields act on the
finite-mode domain of a complete orthonormal basis of the Fock space.  In that
realization the Weyl-gauge Hamiltonian `½ Σ πᵢ² + ½ Σ Bₐ²` — unbounded, with no
boundedness hypothesis — has a Friedrichs extension, and the Hashimoto/SIRK
algorithm selects exactly it. -/
theorem weyl_hashimoto_selects_friedrichs (b : HilbertBasis ℕ ℂ F) {n m : ℕ}
    {pi : Fin n → finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    {Bf : Fin m → finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    (hpi : ∀ i, SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp (Bf a)))
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (R : F →L[ℂ] F),
      IsPositiveSelfAdjointExtension (weylOp pi Bf) A ∧ IsShiftInvert A γ R ∧
        IsSelfAdjoint R ∧
        (∀ u : F, Tendsto (fun k : ℕ => galerkinCompression R b k u) atTop (nhds (R u))) ∧
        (∀ (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvert A' γ R → Dom' = Dom) := by
  obtain ⟨Dom, A, R, hA, hR, -, hsa, hstrong, -, huniq⟩ :=
    friedrichs_hashimoto_selects b (weylOp pi Bf) (weylOpDom_symmetricOn hpi hB)
      (weylOpDom_quadForm_nonneg hpi hB) hγ
  exact ⟨Dom, A, R, hA, hR, hsa, hstrong, fun Dom' A' hA' => (huniq Dom' A' hA').1⟩

/-! ## Part F — the construction is not vacuous: a genuinely unbounded operator -/

/-- **The construction applied to a genuinely unbounded operator.**  For the
diagonal operator `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)` restricted to the finite-mode
domain — unbounded, by
`BookProof.HashimotoShiftInvert.ell2ExampleMatrix_unbounded` — the Friedrichs
extension is produced by `friedrichs_extension_exists`, with no extension
assumed as input. -/
theorem unbounded_friedrichs_example :
    (∃ (Dom : Submodule ℂ (ℓ²(ℕ, ℂ))) (A : Dom →ₗ[ℂ] ℓ²(ℕ, ℂ)),
        IsPositiveSelfAdjointExtension ell2ExampleMatrix A) ∧
      ∀ C : ℝ, ∃ x : finiteModeDomain ell2Basis,
        C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖ := by
  obtain ⟨-, hsym, hpos, -⟩ := ell2Example_isPositiveSelfAdjointExtension
  refine ⟨friedrichs_extension_exists
    ⟨finiteModeDomain ell2Basis, ell2ExampleMatrix, ?_, ?_⟩ (finiteModeDomain_dense ell2Basis),
    ell2ExampleMatrix_unbounded⟩
  · intro x y
    exact hsym ⟨(x : ℓ²(ℕ, ℂ)), finiteModeDomain_le_range x.2⟩
      ⟨(y : ℓ²(ℕ, ℂ)), finiteModeDomain_le_range y.2⟩
  · intro x
    exact hpos ⟨(x : ℓ²(ℕ, ℂ)), finiteModeDomain_le_range x.2⟩

end BookProof.FriedrichsExtension
