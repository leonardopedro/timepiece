import Mathlib
import BookProof.OSReconstruction.HilbertSpace
import BookProof.OSReconstruction.TransferSemigroupRight

/-!
# What an identification of the OS Hilbert space with a Fock space has to satisfy

`OSReconstruction.HilbertSpace` builds `Hphys Λ`, the completion of `𝔄 / 𝔑` in the OS norm, and
`TransferSemigroupRight` builds the transfer semigroup `P(τ) = physEvolCompletionRightFun hinv τ`,
which exists for `τ ≥ 0` only.  On the Fock side the corpus has an entirely different construction
— `ymFockSpace` with `ymFockHam` and its Friedrichs extension
— and between the two there is **no map at all**: no `LinearIsometry` from `Hphys Λ` to any Fock
space occurs anywhere in `BookProof`.

This module states the condition such a map would have to satisfy, and proves what the condition
forces, so that the analytic work has a target instead of a slogan.  A *bridge* is an isometry
`U : Hphys Λ →ₗᵢ[ℝ] F` with dense range which turns the transfer semigroup into the Fock flow:

`U (P(τ) x) = Q(τ) (U x)`  for all `τ ≥ 0`   (`OsFockBridge.intertwines`).

Those are the three fields of `OsFockBridge`; everything else is proved from them.  Since an
isometry with dense range into a complete space is onto, the bridge is in fact a *unitary*
(`toIsometryEquiv`), and then

* the two-point functions agree, `⟪x, P(τ)y⟫ = ⟪U x, Q(τ)(U y)⟫` (`inner_intertwines`), which is
  the matrix element studied by `Clustering` and `KallenLehmannModel` on the OS side;
* contractivity, isometry and fixed points transfer in both directions (`contractive_iff`,
  `isometry_iff`, `fixed_iff`);
* symmetry of `P(τ)` is equivalent to symmetry of `Q(τ)` (`symmetric_iff`);
* the semigroup law transfers from `Q` to `P` (`semigroup_transfer`).

The bundle is inhabited (`OsFockBridge.id`), so the axioms are consistent; but they are not
trivial, and a bridge for a given pair `(P, Q)` *is* the OS-to-Fock identification.

## Boundary

The bundle is stated for a real inner product space `F`.  `ymFockSpace` is complex, so a concrete
bridge would land in its realification; nothing here depends on how `F` is built, which is
deliberate — the content is the list of conditions, not one choice of model.

Two things are *not* in the bundle and are not derivable from it: writing `Q(τ) = e^{−τH}` for a
self-adjoint `H` (the bundle only sees the flow), and identifying that `H` with the Friedrichs
extension of `ymFockHam`.  Both are Fock-side hypotheses.  On the OS side the corpus supplies `P`
and, in `SemigroupGenerator`, a symmetric `LinearPMap` `generatorRight` — not a self-adjoint
operator, and not a functional calculus, so the correspondence with an `e^{−τH}` cannot be stated
as an equality of generated semigroups here.
-/

namespace BookProof.OSReconstruction

open scoped RealInnerProductSpace

noncomputable section

variable {Λ : OSState}

/-- **An identification of the OS Hilbert space with a Fock space.**  `U` is an isometry with dense
range intertwining the transfer semigroup `P` (`τ ≥ 0`) with the Fock flow `Q`. -/
structure OsFockBridge (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (P : ℝ → Hphys Λ →L[ℝ] Hphys Λ) (Q : ℝ → F →L[ℝ] F) where
  /-- The identification, as a real-linear isometry. -/
  U : Hphys Λ →ₗᵢ[ℝ] F
  /-- Its range is dense: the identification sees the whole of `F`. -/
  dense_range : DenseRange U
  /-- It intertwines the transfer semigroup with the Fock flow, for nonnegative time. -/
  intertwines : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ, U (P τ x) = Q τ (U x)

namespace OsFockBridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {P : ℝ → Hphys Λ →L[ℝ] Hphys Λ} {Q : ℝ → F →L[ℝ] F}

/-! ## The bridge is unitary -/

/-- An isometry into a complete space has closed range. -/
theorem closed_range (B : OsFockBridge F P Q) : IsClosed (Set.range B.U) :=
  B.U.antilipschitz.isClosed_range B.U.isometry.uniformContinuous

/-- **A bridge is onto**: its range is closed and dense, so it is everything. -/
theorem surjective (B : OsFockBridge F P Q) : Function.Surjective B.U := by
  have huniv : Set.range B.U = Set.univ := by
    rw [← B.closed_range.closure_eq]
    exact B.dense_range.closure_eq
  intro y
  have hy : y ∈ Set.range B.U := by rw [huniv]; trivial
  exact hy

theorem injective (B : OsFockBridge F P Q) : Function.Injective B.U :=
  B.U.injective

/-- **The bridge, as a linear isometry equivalence** — a unitary between the OS Hilbert space and
the Fock space. -/
def toIsometryEquiv (B : OsFockBridge F P Q) : Hphys Λ ≃ₗᵢ[ℝ] F :=
  LinearIsometryEquiv.ofSurjective B.U B.surjective

@[simp]
theorem toIsometryEquiv_apply (B : OsFockBridge F P Q) (x : Hphys Λ) :
    B.toIsometryEquiv x = B.U x := rfl

@[simp]
theorem toIsometryEquiv_symm_apply_apply (B : OsFockBridge F P Q) (x : Hphys Λ) :
    B.toIsometryEquiv.symm (B.U x) = x :=
  LinearIsometryEquiv.symm_apply_apply B.toIsometryEquiv x

@[simp]
theorem apply_toIsometryEquiv_symm_apply (B : OsFockBridge F P Q) (y : F) :
    B.U (B.toIsometryEquiv.symm y) = y :=
  LinearIsometryEquiv.apply_symm_apply B.toIsometryEquiv y

/-! ## Intertwining in the other direction -/

/-- The inverse bridge intertwines the flows in the opposite order. -/
theorem intertwines_symm (B : OsFockBridge F P Q) {τ : ℝ} (hτ : 0 ≤ τ) (y : F) :
    B.toIsometryEquiv.symm (Q τ y) = P τ (B.toIsometryEquiv.symm y) := by
  have h : B.U (P τ (B.toIsometryEquiv.symm y)) = Q τ y := by
    rw [B.intertwines τ hτ, B.apply_toIsometryEquiv_symm_apply]
  rw [← h, B.toIsometryEquiv_symm_apply_apply]

/-! ## The two-point functions agree -/

/-- **The matrix element of the transfer semigroup is the Fock matrix element** of the identified
vectors.  This is the identity that makes the KL representation on `ℋ` a statement about the Fock
Hamiltonian. -/
theorem inner_intertwines (B : OsFockBridge F P Q) {τ : ℝ} (hτ : 0 ≤ τ)
    (x y : Hphys Λ) :
    ⟪x, P τ y⟫ = ⟪B.U x, Q τ (B.U y)⟫ := by
  rw [← B.U.inner_map_map x (P τ y), B.intertwines τ hτ y]

/-- The physical two-point function is the Fock two-point function. -/
theorem twoPoint (B : OsFockBridge F P Q) {τ : ℝ} (hτ : 0 ≤ τ) (x : Hphys Λ) :
    ⟪x, P τ x⟫ = ⟪B.U x, Q τ (B.U x)⟫ :=
  B.inner_intertwines hτ x x

/-- Operator norms are matched by the identification. -/
theorem norm_intertwines (B : OsFockBridge F P Q) {τ : ℝ} (hτ : 0 ≤ τ) (x : Hphys Λ) :
    ‖P τ x‖ = ‖Q τ (B.U x)‖ := by
  rw [← B.U.norm_map (P τ x), B.intertwines τ hτ x]

/-- ... and in the other direction. -/
theorem norm_intertwines_symm (B : OsFockBridge F P Q) {τ : ℝ} (hτ : 0 ≤ τ) (y : F) :
    ‖Q τ y‖ = ‖P τ (B.toIsometryEquiv.symm y)‖ := by
  have h : Q τ y = Q τ (B.U (B.toIsometryEquiv.symm y)) := by
    rw [B.apply_toIsometryEquiv_symm_apply]
  rw [h, ← B.norm_intertwines hτ (B.toIsometryEquiv.symm y)]

/-! ## Properties transfer both ways -/

/-- **Contractivity transfers in both directions.** -/
theorem contractive_iff (B : OsFockBridge F P Q) :
    (∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ, ‖P τ x‖ ≤ ‖x‖) ↔
      (∀ (τ : ℝ), 0 ≤ τ → ∀ y : F, ‖Q τ y‖ ≤ ‖y‖) := by
  constructor
  · intro hP τ hτ y
    have h := hP τ hτ (B.toIsometryEquiv.symm y)
    rw [B.norm_intertwines_symm hτ y]
    simpa using h
  · intro hQ τ hτ x
    have h := hQ τ hτ (B.U x)
    rw [B.norm_intertwines hτ x]
    simpa using h

/-- **Being an isometry transfers in both directions.** -/
theorem isometry_iff (B : OsFockBridge F P Q) :
    (∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ, ‖P τ x‖ = ‖x‖) ↔
      (∀ (τ : ℝ), 0 ≤ τ → ∀ y : F, ‖Q τ y‖ = ‖y‖) := by
  constructor
  · intro hP τ hτ y
    have h := hP τ hτ (B.toIsometryEquiv.symm y)
    rw [B.norm_intertwines_symm hτ y]
    simpa using h
  · intro hQ τ hτ x
    have h := hQ τ hτ (B.U x)
    rw [B.norm_intertwines hτ x]
    simpa using h

/-- **Fixed points correspond**: a vector is invariant under the transfer semigroup exactly when its
image is invariant under the Fock flow. -/
theorem fixed_iff (B : OsFockBridge F P Q) {τ : ℝ} (hτ : 0 ≤ τ) (x : Hphys Λ) :
    P τ x = x ↔ Q τ (B.U x) = B.U x := by
  constructor
  · intro h
    rw [← B.intertwines τ hτ x, h]
  · intro h
    refine B.U.injective ?_
    rw [B.intertwines τ hτ x, h]

/-- **Symmetry transfers in both directions**: an identification of the semigroups identifies the
symmetric ones.  Neither side is assumed symmetric — this is an equivalence, and it is what makes
`TransferSelfAdjoint`'s degeneracy a statement about both sides at once. -/
theorem symmetric_iff (B : OsFockBridge F P Q) {τ : ℝ} (hτ : 0 ≤ τ) :
    (∀ x y : Hphys Λ, ⟪P τ x, y⟫ = ⟪x, P τ y⟫) ↔
      (∀ y z : F, ⟪Q τ y, z⟫ = ⟪y, Q τ z⟫) := by
  constructor
  · intro hP y z
    obtain ⟨x, rfl⟩ := B.surjective y
    obtain ⟨w, rfl⟩ := B.surjective z
    rw [← B.intertwines τ hτ x, ← B.intertwines τ hτ w]
    simp only [LinearIsometry.inner_map_map]
    exact hP x w
  · intro hQ x w
    rw [← B.U.inner_map_map (P τ x) w, ← B.U.inner_map_map x (P τ w),
      B.intertwines τ hτ x, B.intertwines τ hτ w]
    exact hQ _ _

/-- **The semigroup law transfers from the Fock flow to the transfer semigroup.**  This is the
statement that a bridge compatible with one `e^{−τH}` automatically makes `P` a semigroup, so the
`P(0) = 1`, `P(s + t) = P(s)P(t)` half of the OS reconstruction can be read off the Fock side. -/
theorem semigroup_transfer (B : OsFockBridge F P Q)
    (hQ : ∀ (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ → ∀ y : F, Q (τ + σ) y = Q τ (Q σ y))
    {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (x : Hphys Λ) :
    P (τ + σ) x = P τ (P σ x) := by
  refine B.U.injective ?_
  rw [B.intertwines (τ + σ) (add_nonneg hτ hσ) x, B.intertwines τ hτ (P σ x),
    B.intertwines σ hσ x, hQ τ σ hτ hσ]

/-! ## Inhabitation -/

/-- **The bundle is inhabited**: the identity identification of `ℋ` with itself, with the same
semigroup on both sides.  So the axioms are consistent, and the obstruction to identifying `ℋ`
with a *Fock* space is not a contradiction in the bundle but the absence of a map. -/
def id (P : ℝ → Hphys Λ →L[ℝ] Hphys Λ) : OsFockBridge (Hphys Λ) P P where
  U := LinearIsometry.id
  dense_range := by
    simpa using (denseRange_id (X := Hphys Λ))
  intertwines := fun _ _ _ => rfl

end OsFockBridge

end

end BookProof.OSReconstruction
