/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import BookProof.Sm.ChapterSmQuartet

/-!
# A b-ghost with a formula

§8 of `BookProof.Sm.ChapterSmQuartet` produces the Standard Model's b-ghost as a
`Classical.choice`: the quartet data exists, but no map is exhibited.  This module removes the
choice.  For a finite-dimensional space the contracting homotopy of the charge can be written
down,

  `P = (Q ↾ (ker Q)ᗮ)⁻¹ ∘ π_{range Q}`,

i.e. the orthogonal projection onto the exact states, followed by the inverse of the charge on
the orthogonal complement of its kernel.  The two ingredients are canonical:

* `x ↦ Q x` is a linear equivalence `(ker Q)ᗮ ≃ₗ range Q` (`kerEquivOfBrst`): `Q` is
  injective on `(ker Q)ᗮ`, and every exact vector is `Q` of the `(ker Q)ᗮ`–component of a
  preimage;
* `π_{range Q}` is Mathlib's orthogonal projection, whose kernel is `(range Q)ᗮ`.

Consequently `Q P = π_{range Q}` and `P Q = π_{(ker Q)ᗮ}`, so `Q P Q = Q` and `P Q P = P`
(`canonicalHomotopy_QSQ`, `canonicalHomotopy_SQS`).  Feeding this `P` into §5's construction gives
the physical projector with the **explicit range**

  `range V = ker Q ⊓ (range Q)ᗮ`   (`range_physProjOf_canonical`),

the closed states orthogonal to the exact ones — the canonical harmonic representatives.  This is
the transverse half of the no-ghost statement, proved rather than assumed.

At the Standard Model charge (`smBghostFormula`), `smBghostCanonical` is exactly §8's b-ghost
position, now with a formula and no `Classical.choice`, and `smPhysProjCanonical` is the
orthogonal projection onto `ker (smBrstCharge m T f3) ⊓ (range (smBrstCharge m T f3))ᗮ`.

## Honest boundary

Ghost **parity** is a separate input and is not constructed here: the corpus has no ghost-parity
operator on `FermiFock (m + 12)`, so `range smPhysProjCanonical` is proved transverse
(orthogonal to the exact states) but is *not* proved ghost-parity even.  The positivity input
stays where §9 put it: positivity of the charge form on that range
(`physicalPositivity_of_quartet_on_range`).

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmQuartet

open BookProof.SmBrstQuotient
open BookProof.SmBrstGhost
open BookProof.SmCar

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## 1. The canonical pairing of the exact states -/

/-- **The map `x ↦ Q x` from `(ker Q)ᗮ` to `range Q`.**  It is the candidate equivalence whose
inverse is the transport half of the b-ghost. -/
def spineMap (Q : H →ₗ[ℂ] H) : (LinearMap.ker Q)ᗮ →ₗ[ℂ] LinearMap.range Q where
  toFun x := ⟨Q x.1, LinearMap.mem_range_self Q x.1⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- **The pairing is injective**: a vector of `(ker Q)ᗮ` killed by `Q` is orthogonal to itself,
hence zero. -/
theorem spineMap_injective (Q : H →ₗ[ℂ] H) : Function.Injective (spineMap Q) := by
  intro x y hxy
  have hv : Q x.1 = Q y.1 := congrArg Subtype.val hxy
  have hq : Q (x.1 - y.1) = 0 := by rw [map_sub, hv, sub_self]
  have hmem : x.1 - y.1 ∈ LinearMap.ker Q := hq
  have horth : x.1 - y.1 ∈ (LinearMap.ker Q)ᗮ := Submodule.sub_mem _ x.2 y.2
  have hzero : ⟪x.1 - y.1, x.1 - y.1⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal (LinearMap.ker Q) _).mp horth _ hmem
  exact Subtype.ext (sub_eq_zero.mp (inner_self_eq_zero.mp hzero))

/-- **The pairing is surjective**, by splitting a preimage along `ker Q ⊕ (ker Q)ᗮ`. -/
theorem spineMap_surjective [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) :
    Function.Surjective (spineMap Q) := by
  have hcompl : IsCompl (LinearMap.ker Q) (LinearMap.ker Q)ᗮ :=
    Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  intro r
  obtain ⟨z, hz⟩ := r.2
  obtain ⟨u, v, huv, -⟩ := Submodule.existsUnique_add_of_isCompl hcompl z
  refine ⟨⟨v.1, v.2⟩, ?_⟩
  apply Subtype.ext
  change Q v.1 = r.1
  have hv : (v : H) = z - (u : H) := by rw [← huv]; abel
  have hu : Q (u : H) = 0 := u.2
  rw [hv, map_sub, hu, sub_zero, ← hz]

/-- **The canonical linear equivalence `(ker Q)ᗮ ≃ₗ range Q`, `x ↦ Q x`.** -/
def kerEquivOfBrst [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) :
    (LinearMap.ker Q)ᗮ ≃ₗ[ℂ] LinearMap.range Q :=
  LinearEquiv.ofBijective (spineMap Q) ⟨spineMap_injective Q, spineMap_surjective Q⟩

/-- The equivalence is the pairing: `e x = Q x`. -/
theorem kerEquivOfBrst_apply [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H)
    (x : (LinearMap.ker Q)ᗮ) : (kerEquivOfBrst Q x : LinearMap.range Q) = spineMap Q x :=
  LinearEquiv.ofBijective_apply (f := spineMap Q)
    (hf := ⟨spineMap_injective Q, spineMap_surjective Q⟩) x

/-- **The inverse of the pairing is a right inverse of `Q`**: `Q (e.symm r) = r`. -/
theorem Q_kerEquivOfBrst_symm [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H)
    (r : LinearMap.range Q) : Q ((kerEquivOfBrst Q).symm r : H) = (r : H) := by
  have h := congrArg Subtype.val ((kerEquivOfBrst Q).apply_symm_apply r)
  rw [kerEquivOfBrst_apply] at h
  exact h

/-! ## 2. The canonical b-ghost -/

/-- **The canonical b-ghost**: project onto the exact states, then invert the charge on
`(ker Q)ᗮ`,

  `P = (Q ↾ (ker Q)ᗮ)⁻¹ ∘ π_{range Q}`.

No choice is involved: both factors are canonical (`kerEquivOfBrst`, Mathlib's orthogonal
projection). -/
def canonicalHomotopy [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  (LinearMap.ker Q)ᗮ.subtype.comp ((kerEquivOfBrst Q).symm.toLinearMap.comp
    (LinearMap.range Q).orthogonalProjection.toLinearMap)

/-- How the canonical b-ghost acts: project, then transport back. -/
theorem canonicalHomotopy_apply [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) (x : H) :
    canonicalHomotopy Q x =
      ((kerEquivOfBrst Q).symm ((LinearMap.range Q).orthogonalProjection x) : H) := rfl

/-- **`Q P` is the orthogonal projection onto the exact states**: `Q (P x) = π_{range Q} x`. -/
theorem Q_canonicalHomotopy [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) (x : H) :
    Q (canonicalHomotopy Q x) = ((LinearMap.range Q).orthogonalProjection x : H) := by
  rw [canonicalHomotopy_apply]
  exact Q_kerEquivOfBrst_symm Q _

/-- **`P Q` is the orthogonal projection onto `(ker Q)ᗮ`**, read off from `Q P = π_{range Q}`. -/
theorem canonicalHomotopy_Q [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) (x : H) :
    canonicalHomotopy Q (Q x) =
      ((kerEquivOfBrst Q).symm
        (⟨Q x, LinearMap.mem_range_self Q x⟩ : LinearMap.range Q) : H) := by
  rw [canonicalHomotopy_apply]
  exact congrArg (fun v : LinearMap.range Q => ((kerEquivOfBrst Q).symm v : H))
    (Submodule.orthogonalProjection_mem_subspace_eq_self
      (K := LinearMap.range Q) ⟨Q x, LinearMap.mem_range_self Q x⟩)

/-- **First contraction identity**: `Q P Q = Q`. -/
theorem canonicalHomotopy_QSQ [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) (x : H) :
    Q (canonicalHomotopy Q (Q x)) = Q x := by
  rw [Q_canonicalHomotopy]
  exact congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self
    (K := LinearMap.range Q) ⟨Q x, LinearMap.mem_range_self Q x⟩)

/-- **Second contraction identity**: `P Q P = P`. -/
theorem canonicalHomotopy_SQS [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) (x : H) :
    canonicalHomotopy Q (Q (canonicalHomotopy Q x)) = canonicalHomotopy Q x := by
  rw [Q_canonicalHomotopy, canonicalHomotopy_apply, canonicalHomotopy_apply]
  exact congrArg (fun v : LinearMap.range Q => ((kerEquivOfBrst Q).symm v : H))
    (Submodule.orthogonalProjection_mem_subspace_eq_self (K := LinearMap.range Q)
      ((LinearMap.range Q).orthogonalProjection x))

/-- **The canonical b-ghost's kernel**: `ker P = (range Q)ᗮ`, since `π_{range Q}` is injective on
the image of the equivalence. -/
theorem ker_canonicalHomotopy [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) :
    LinearMap.ker (canonicalHomotopy Q) = (LinearMap.range Q)ᗮ := by
  ext x
  rw [LinearMap.mem_ker, canonicalHomotopy_apply]
  constructor
  · intro hx
    have hsub : (kerEquivOfBrst Q).symm ((LinearMap.range Q).orthogonalProjection x) = 0 :=
      Subtype.ext hx
    have hπ : (LinearMap.range Q).orthogonalProjection x = 0 := by
      have := congrArg (kerEquivOfBrst Q) hsub
      simpa using this
    exact (Submodule.orthogonalProjection_eq_zero_iff).mp hπ
  · intro hx
    have hπ : (LinearMap.range Q).orthogonalProjection x = 0 :=
      (Submodule.orthogonalProjection_eq_zero_iff).mpr hx
    simp [hπ]

/-- **The physical subspace of the canonical b-ghost is the harmonic one**:

  `range V = ker Q ⊓ (range Q)ᗮ`.

This is the transverse statement: the closed states orthogonal to the exact ones.  It is a
theorem about the explicit projector `physProjOf Q (canonicalHomotopy Q)`, not an assumption. -/
theorem range_physProjOf_canonical [FiniteDimensional ℂ H] {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) :
    LinearMap.range (BrstQuartet.physProjOf Q (canonicalHomotopy Q)) =
      closed Q ⊓ (LinearMap.range Q)ᗮ := by
  rw [BrstQuartet.range_physProjOf hQ (canonicalHomotopy_QSQ Q) (canonicalHomotopy_SQS Q),
    ker_canonicalHomotopy]

/-- **The quartet built from the canonical b-ghost**, with no choice. -/
def quartet_canonical [FiniteDimensional ℂ H] {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) :
    BrstQuartet Q :=
  BrstQuartet.quartetOfHomotopy hQ (canonicalHomotopy_QSQ Q) (canonicalHomotopy_SQS Q)

/-- The b-ghost of the canonical quartet is §5's `bGhostOf` at the canonical homotopy. -/
theorem quartet_canonical_bGhost [FiniteDimensional ℂ H] {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) :
    (quartet_canonical hQ).bGhost = BrstQuartet.bGhostOf Q (canonicalHomotopy Q) := rfl

/-- The physical projector of the canonical quartet is §5's `physProjOf`, so its range is
`ker Q ⊓ (range Q)ᗮ` (`range_physProjOf_canonical`). -/
theorem quartet_canonical_physProj [FiniteDimensional ℂ H] {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) :
    (quartet_canonical hQ).physProj = BrstQuartet.physProjOf Q (canonicalHomotopy Q) := rfl

/-! ## 3. The Standard-Model b-ghost, with a formula

The joint charge is an endomorphism of `FermiFock (m + 12)`, which is finite-dimensional, so
§1–§2 apply with no further input: no property of the mode content, and no choice. -/

variable {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
  {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}

/-- **The Standard-Model b-ghost, with a formula**:

  `smBghostFormula = (Ω ↾ (ker Ω)ᗮ)⁻¹ ∘ π_{range Ω}`,

where `Ω = smBrstCharge m T f3`.  This is the b-ghost of §8 (`smBghost`) as an explicit map: it
needs no gauge-algebra hypothesis, only the charge. -/
def smBghostFormula : FermiFock (m + 12) →ₗ[ℂ] FermiFock (m + 12) :=
  canonicalHomotopy (smBrstCharge m T f3)

/-- **The Standard-Model physical projector, with a formula**: §5's

  `V = 1 − (Ω P + P Ω) + Ω P² Ω`

at the canonical b-ghost.  Its range is `ker Ω ⊓ (range Ω)ᗮ` (`smPhysProjFormula_range`). -/
def smPhysProjFormula : FermiFock (m + 12) →ₗ[ℂ] FermiFock (m + 12) :=
  BrstQuartet.physProjOf (smBrstCharge m T f3) (smBghostFormula (m := m) (T := T) (f3 := f3))

/-- **The kernel of the formula b-ghost is the orthogonal complement of the exact states.** -/
theorem ker_smBghostFormula :
    LinearMap.ker (smBghostFormula (m := m) (T := T) (f3 := f3)) =
      (LinearMap.range (smBrstCharge m T f3))ᗮ :=
  ker_canonicalHomotopy (smBrstCharge m T f3)

/-- **The range of the formula projector is the transverse physical subspace**:
`ker Ω ⊓ (range Ω)ᗮ`.  This is the no-ghost theorem's subspace, *described and proved* — the
statement §9 could only characterise through the chosen homotopy.  Ghost parity is still not
available: no ghost-parity operator is constructed for `smBrstCharge` in this corpus. -/
theorem smPhysProjFormula_range (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T
    (smStruct f3)) (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3)) =
      closed (smBrstCharge m T f3) ⊓ (LinearMap.range (smBrstCharge m T f3))ᗮ :=
  range_physProjOf_canonical (isBrst_smBrstCharge hT h3anti h3jac)

end

end BookProof.SmQuartet
