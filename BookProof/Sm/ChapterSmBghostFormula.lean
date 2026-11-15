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
statement §9 could only characterise through the chosen homotopy.  This is the transverse subspace
of the no-ghost theorem, and the ghost parity `smGhostParity` of `ChapterSmBrstGhost` §6 acts on it;
what is *not* available is a proof that this subspace is ghost-parity even — see
`ChapterSmQuartet` §13 and `docs/HONEST_BOUNDARIES_SM.md`. -/
theorem smPhysProjFormula_range (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T
    (smStruct f3)) (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3)) =
      closed (smBrstCharge m T f3) ⊓ (LinearMap.range (smBrstCharge m T f3))ᗮ :=
  range_physProjOf_canonical (isBrst_smBrstCharge hT h3anti h3jac)

-- As in `ChapterSmQuartet` §8: with the two model constants opaque the unifier never evaluates
-- their bodies.  The statements below put `smBrstCharge` inside a typeclass-carrying expression
-- (`Module.finrank` of a submodule of `FermiFock (m + 12)`), which is the shape that otherwise
-- exhausts the heartbeat budget while elaborating the *statement*.
attribute [local irreducible] BookProof.SmBrstGhost.smBrstCharge
  BookProof.SmBrstGhost.smGhostParity

/-! ## 4. The two projectors have equally large ranges

`ChapterSmQuartet` §15–§16 describe the chosen projector `smPhysProj` (range `ker Ω ⊓ ker P`) and
this chapter the canonical one (`range smPhysProjFormula = ker Ω ⊓ (range Ω)ᗮ`).  They are different
subspaces, because the two homotopies are different complements of the exact states — but they are
equally large: both are complements of `range Ω` inside `ker Ω`, so both have dimension
`dim ker Ω − dim range Ω`.

This is the precise form of "characterised, not canonical": the choice of complement moves the
physical subspace around inside the closed space without changing its dimension.  Nothing here
identifies the two ranges, and nothing here supplies the metric; positivity on either is the
separate no-ghost input. -/

/-- **The formula projector's range has the cohomology's dimension.**  Its homotopy is the canonical
one, so `finrank_range_physProjOf` applies with no choice involved. -/
theorem finrank_smPhysProjFormula_range (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T
    (smStruct f3)) (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    Module.finrank ℂ (LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3)))
        + Module.finrank ℂ (LinearMap.range (smBrstCharge m T f3))
      = Module.finrank ℂ (closed (smBrstCharge m T f3)) :=
  BrstQuartet.finrank_range_physProjOf (isBrst_smBrstCharge hT h3anti h3jac)
    (canonicalHomotopy_QSQ (smBrstCharge m T f3))
    (canonicalHomotopy_SQS (smBrstCharge m T f3))

/-- **The chosen and the canonical physical subspaces are equally large**: both ranges are
complements of the exact states in the closed space, so their dimensions agree even though the
subspaces need not. -/
theorem smPhysProj_finrank_eq_formula (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T
    (smStruct f3)) (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    Module.finrank ℂ (LinearMap.range (smPhysProj hT h3anti h3jac))
      = Module.finrank ℂ (LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3))) := by
  have h1 := smPhysProj_finrank (m := m) (T := T) (f3 := f3) hT h3anti h3jac
  have h2 := finrank_smPhysProjFormula_range (m := m) (T := T) (f3 := f3) hT h3anti h3jac
  omega

/-! ## 5. A metric for the SM charge: the projection onto the canonical physical range

§4 compares the two projectors and records that "nothing here supplies the metric".  §19 of
`ChapterSmQuartet` shows the quartet does supply one, once it is allowed to be *semidefinite*: the
orthogonal projection onto the physical range.  Here that metric is written at the model.

Both hypotheses of `physicalPositivity_starProjection` are properties of the canonical range itself:
the split `ker Ω = range Ω ⊔ range V` (§91) and orthogonality to the exact states, which is
`smPhysProjFormula_range` read as a statement about the subspace.  So the no-ghost condition is a
*theorem* for this `η`, and the price is visible: `η` is semidefinite with radical the gauge orbit,
and on the physical range its form is the ambient norm squared
(`smPhysMetric_kform_eq_norm_sq_of_mem`).

**Boundary.**  This is not a Krein metric, it does not identify the physical range with the
transverse even sector, and it does not prove the norm inequality of `ChapterSmQuartet` §12.  What
it establishes is that the no-ghost *definition* is satisfiable at the model's charge and which
operator satisfies it, so what survives as an input is an identification, not positivity as such. -/

/-- **A metric for the SM charge**: the orthogonal projection onto the canonical physical range
`ker Ω ⊓ (range Ω)ᗮ`. -/
noncomputable def smPhysMetric : FermiFock (m + 12) →ₗ[ℂ] FermiFock (m + 12) :=
  ((LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3))).starProjection).toLinearMap

/-- **The canonical physical range is orthogonal to the exact states.**  It is
`ker Ω ⊓ (range Ω)ᗮ` (`smPhysProjFormula_range`), so this is the second conjunct of that equality
read as a subspace statement. -/
theorem smPhysProjFormula_le_orthogonal (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T
    (smStruct f3)) (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    LinearMap.range (smBrstCharge m T f3) ≤
      (LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3)))ᗮ := by
  have hD : LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3)) ≤
      (LinearMap.range (smBrstCharge m T f3))ᗮ := by
    rw [smPhysProjFormula_range hT h3anti h3jac]
    exact inf_le_right
  exact le_trans (Submodule.le_orthogonal_orthogonal _) (Submodule.orthogonal_le hD)

/-- **The closed space splits along the canonical physical range**: `ker Ω = range Ω ⊔ D`. -/
theorem closed_eq_sup_range_smPhysProjFormula
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    closed (smBrstCharge m T f3) = LinearMap.range (smBrstCharge m T f3) ⊔
      LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3)) :=
  BrstQuartet.closed_eq_sup_range_physProjOf (isBrst_smBrstCharge hT h3anti h3jac)
    (canonicalHomotopy_QSQ (smBrstCharge m T f3))

/-- **The projection metric is no-ghost at the SM charge.**  The closed space splits off the exact
states along the canonical range (§91) and every exact state is orthogonal to that range
(`smPhysProjFormula_range`), so `PhysicalPositivity` holds for `smPhysMetric`. -/
theorem smPhysicalPositivity_physMetric (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T
    (smStruct f3)) (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    PhysicalPositivity (smBrstCharge m T f3) (smPhysMetric (m := m) (T := T) (f3 := f3)) :=
  BrstQuartet.physicalPositivity_starProjection _
    (smPhysProjFormula_le_orthogonal hT h3anti h3jac)
    (closed_eq_sup_range_smPhysProjFormula hT h3anti h3jac)

/-- **The metric is the ambient norm on the physical range**: on `ker Ω ⊓ (range Ω)ᗮ` the form is
positive definite, so the descended form is an inner product on the cohomology. -/
theorem smPhysMetric_kform_eq_norm_sq_of_mem {d : BookProof.SmCar.FermiFock (m + 12)}
    (hd : d ∈ LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3))) :
    (kform (smPhysMetric (m := m) (T := T) (f3 := f3)) d d).re = ‖d‖ ^ 2 :=
  BrstQuartet.kform_starProjection_eq_norm_sq_of_mem _ hd

/-! ## 6. The radical is the gauge orbit: the quotient inner product at the model

`ChapterSmQuartet` §21 states the four facts that make a projector form an inner product on
`ker Ω / range Ω`; this section is those four facts at `smPhysMetric`:

* `smPhysMetric_radical_eq_gauge` — on the closed space the form vanishes exactly on the exact
  states, so it is definite on the cohomology rather than merely semidefinite;
* `smPhysMetric_descends` — shifting either argument by an exact state changes nothing, so the form
  is a function of the cohomology class;
* `smPhysMetric_definite` — on the canonical range it *is* the ambient norm, hence positive;
* `smPhysMetric_representative` — every closed state is exact plus a member of that range.

Taken together: the cohomology is modelled by the canonical range `ker Ω ⊓ (range Ω)ᗮ`, and the
descended form is the ambient inner product transported along `ker Ω / range Ω ≃ D`.  The radical
being the gauge orbit is exactly what makes the semidefinite metric of §5 an inner product on the
physical Hilbert space instead of just a non-negative form.

**Boundary.**  The identification is stated as a decomposition (with uniqueness available from
`BrstQuartet.representative_unique`), not as an `Equiv` or an `InnerProductSpace` instance, and `D`
is the canonical range — so the identification is a property of that choice of complement. -/

/-- **The metric's radical on the closed space is the gauge orbit.** -/
theorem smPhysMetric_radical_eq_gauge
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0)
    {x : BookProof.SmCar.FermiFock (m + 12)} (hx : x ∈ closed (smBrstCharge m T f3)) :
    (kform (smPhysMetric (m := m) (T := T) (f3 := f3)) x x).re = 0 ↔
      x ∈ gauge (smBrstCharge m T f3) :=
  BrstQuartet.kform_starProjection_radical _
    (smPhysProjFormula_le_orthogonal (m := m) (T := T) (f3 := f3) hT h3anti h3jac)
    (closed_eq_sup_range_smPhysProjFormula (m := m) (T := T) (f3 := f3) hT h3anti h3jac) hx

/-- **The metric descends to the cohomology**: exact shifts in either argument are invisible. -/
theorem smPhysMetric_descends
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0)
    (x y z w : BookProof.SmCar.FermiFock (m + 12)) :
    kform (smPhysMetric (m := m) (T := T) (f3 := f3))
        (x + smBrstCharge m T f3 z) (y + smBrstCharge m T f3 w)
      = kform (smPhysMetric (m := m) (T := T) (f3 := f3)) x y :=
  BrstQuartet.kform_starProjection_descends _
    (smPhysProjFormula_le_orthogonal (m := m) (T := T) (f3 := f3) hT h3anti h3jac) x y z w

/-- **The descended form is positive definite on the canonical range.**  No hypothesis on the
representation is needed: on that range the form is the ambient norm squared
(`smPhysMetric_kform_eq_norm_sq_of_mem`). -/
theorem smPhysMetric_definite
    {d : BookProof.SmCar.FermiFock (m + 12)}
    (hd : d ∈ LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3)))
    (h0 : (kform (smPhysMetric (m := m) (T := T) (f3 := f3)) d d).re = 0) : d = 0 :=
  BrstQuartet.kform_starProjection_definite _ hd h0

/-- **Every closed state is exact plus one member of the canonical range.** -/
theorem smPhysMetric_representative
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0)
    {x : BookProof.SmCar.FermiFock (m + 12)} (hx : x ∈ closed (smBrstCharge m T f3)) :
    ∃ e ∈ LinearMap.range (smBrstCharge m T f3),
      ∃ d ∈ LinearMap.range (smPhysProjFormula (m := m) (T := T) (f3 := f3)), x = e + d :=
  BrstQuartet.exists_gauge_add_mem _
    (closed_eq_sup_range_smPhysProjFormula (m := m) (T := T) (f3 := f3) hT h3anti h3jac) hx

end

end BookProof.SmQuartet
