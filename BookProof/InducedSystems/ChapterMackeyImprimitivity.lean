import Mathlib

/-!
# Mackey's imprimitivity theorem (book.tex, Note 33 and Note 84)

`book.tex` states the imprimitivity theorem (Note 33, quoted from Varadarajan's
*Geometry of Quantum Theory*, Thm 6.12) as an external input, and uses it twice: for
Lemma 34 (Schur's lemma for systems of imprimitivity — proved independently in
`BookProof.ChapterSchurRepresentation`) and in Note 84, the one-to-one correspondence
between systems of imprimitivity based on `ℝ³` and representations of the little group.

This file **proves the theorem** in the transitive, discrete (finite) case: a system of
imprimitivity `(U, p)` of a group `G` over a finite transitive `G`-space `X ≅ G/H` is
unitarily equivalent to the system *induced* from the representation of the stabilizer
`H = Stab(x₀)` on the fibre `𝒦 = ran p x₀`.  This is the whole mechanism of Mackey's
theorem; the general case replaces the finite sum over `X` by an integral against a
quasi-invariant measure on `G/H`.

## The set-up

A **system of imprimitivity** (`ImprimitivitySystem`; the book's Definition 32 for a
discrete base) consists of a unitary representation `U : G →* (E ≃ₗᵢ[ℂ] E)` and a
projection-valued measure on the discrete space `X`, given by its atoms
`p : X → (E →L[ℂ] E)`: self-adjoint idempotents, pairwise orthogonal, summing to the
identity, and covariant, `U g (p x ψ) = p (g • x) (U g ψ)`, which is the book's
`U(g) π(A) U(g)⁻¹ = π(gA)`.

The **induced system** is realized concretely as the space of "fields on `X` with values
in the fibre" (`InducedSpace`): the functions `f : X → E` with `p x₀ (f x) = f x`, with
squared norm `∑ x, ‖f x‖²`.  Given a choice of coset representatives `s : X → G`
(`s x • x₀ = x`, which exists exactly because the action is transitive), the induced
representation and the induced projection-valued measure are

  `(inducedRep g f) x = U (cocycle g x) (f (g⁻¹ • x))`,  `cocycle g x = (s x)⁻¹ g (s (g⁻¹ • x))`,
  `(inducedPvm y f) x = if x = y then f x else 0`,

where the cocycle takes its values in the stabilizer `H` (`cocycle_mem_stabilizer`) and
`U` restricted to `H` preserves the fibre (`fibre_stabilizer_invariant`); so the induced
data only depend on the representation `L = U|_H` of `H` on the fibre `𝒦` — this is
Mackey's induced system `(V_L, E_L)`.

## Results

* `pvm_parseval` — Parseval's identity `∑ x, ‖p x ψ‖² = ‖ψ‖²` for the measure;
* `mackeyMap` (`W ψ x = U (s x)⁻¹ (p x ψ)`, equal to `p x₀ (U (s x)⁻¹ ψ)`), which is
  linear (`mackeyMap_add`, `mackeyMap_smul`), takes values in the induced space
  (`mackeyMap_mem_inducedSpace`), is norm-preserving (`mackeyMap_norm_sq`), injective
  (`mackeyMap_injective`) and onto the induced space (`mackeyMap_surjective`);
* `mackeyMap_intertwines_U` — `W (U g ψ) = inducedRep g (W ψ)`;
* `mackeyMap_intertwines_pvm` — `W (p y ψ) = inducedPvm y (W ψ)`;
* `mackey_imprimitivity` — all of it bundled: **every transitive system of imprimitivity
  over a finite base is unitarily equivalent to the system induced by the representation
  of the stabilizer on the fibre.**

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace
open Finset

namespace BookProof.ChapterMackeyImprimitivity

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A **system of imprimitivity** over a discrete base `X` (the book's Definition 32): a
unitary representation `U` together with the atoms `p x` of a projection-valued measure on
`X`, satisfying the covariance relation `U(g) π(A) U(g)⁻¹ = π(gA)`. -/
structure ImprimitivitySystem (G X E : Type*) [Group G] [Fintype X] [MulAction G X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The unitary representation. -/
  U : G →* (E ≃ₗᵢ[ℂ] E)
  /-- The atoms of the projection-valued measure. -/
  p : X → (E →L[ℂ] E)
  /-- Each atom is self-adjoint. -/
  selfAdjoint : ∀ x u v, ⟪p x u, v⟫_ℂ = ⟪u, p x v⟫_ℂ
  /-- Each atom is idempotent. -/
  idem : ∀ x ψ, p x (p x ψ) = p x ψ
  /-- Distinct atoms are orthogonal. -/
  orthogonal : ∀ x y, x ≠ y → ∀ ψ, p x (p y ψ) = 0
  /-- The atoms sum to the identity: `π(X) = 1`. -/
  complete : ∀ ψ, ∑ x, p x ψ = ψ
  /-- Covariance: `U(g) π(A) U(g)⁻¹ = π(gA)`. -/
  covariant : ∀ g x ψ, U g (p x ψ) = p (g • x) (U g ψ)

/-- A finite pairwise-orthogonal decomposition is norm-additive (Pythagoras). -/
theorem sum_norm_sq_of_orthogonal {f : X → E} {ψ : E} (hsum : ∑ x, f x = ψ)
    (horth : ∀ x y, x ≠ y → ⟪f x, f y⟫_ℂ = 0) :
    ∑ x : X, ‖f x‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have hip : ⟪ψ, ψ⟫_ℂ = ∑ x, ⟪f x, f x⟫_ℂ := by
    rw [← hsum, sum_inner]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [inner_sum, Finset.sum_eq_single x]
    · intro y _ hy
      exact horth x y (Ne.symm hy)
    · intro h; simp at h
  have h2 := congrArg (RCLike.re (K := ℂ)) hip
  rw [map_sum] at h2
  simp only [inner_self_eq_norm_sq] at h2
  exact h2.symm

namespace ImprimitivitySystem

variable (S : ImprimitivitySystem G X E)

theorem U_inv_apply (g : G) (ψ : E) : S.U g⁻¹ (S.U g ψ) = ψ := by
  have h : S.U g⁻¹ (S.U g ψ) = S.U (g⁻¹ * g) ψ := by rw [map_mul]; rfl
  rw [h, inv_mul_cancel, map_one]
  rfl

theorem U_apply_inv (g : G) (ψ : E) : S.U g (S.U g⁻¹ ψ) = ψ := by
  have h : S.U g (S.U g⁻¹ ψ) = S.U (g * g⁻¹) ψ := by rw [map_mul]; rfl
  rw [h, mul_inv_cancel, map_one]
  rfl

theorem U_mul_apply (g h : G) (ψ : E) : S.U g (S.U h ψ) = S.U (g * h) ψ := by
  rw [map_mul]; rfl

/-- **Parseval's identity for the projection-valued measure.** -/
theorem pvm_parseval (ψ : E) : ∑ x : X, ‖S.p x ψ‖ ^ 2 = ‖ψ‖ ^ 2 :=
  sum_norm_sq_of_orthogonal (S.complete ψ) (by
    intro x y hxy
    rw [S.selfAdjoint x ψ (S.p y ψ), S.orthogonal x y hxy, inner_zero_right])

end ImprimitivitySystem

/-! ## The induced system -/

variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)

/-- The fibre over the base point: the range of the atom `p x₀`, described by the
idempotent equation `p x₀ v = v`. -/
def InducedSpace : Set (X → E) := {f | ∀ x, S.p x₀ (f x) = f x}

/-- Mackey's cocycle `(s x)⁻¹ g s(g⁻¹ x)`, with values in the stabilizer of `x₀`. -/
def cocycle (g : G) (x : X) : G := (s x)⁻¹ * g * s (g⁻¹ • x)

/-- The induced representation of `G` on fields over `X` with values in the fibre. -/
def inducedRep (g : G) (f : X → E) : X → E := fun x => S.U (cocycle s g x) (f (g⁻¹ • x))

/-- The induced projection-valued measure: multiplication by the indicator of `{y}`. -/
def inducedPvm [DecidableEq X] (y : X) (f : X → E) : X → E := fun x => if x = y then f x else 0

/-- **Mackey's intertwiner** `W ψ x = U (s x)⁻¹ (p x ψ)`. -/
def mackeyMap (ψ : E) : X → E := fun x => S.U (s x)⁻¹ (S.p x ψ)

variable {S x₀ s}

omit [Fintype X] in
/-- The section property `s x • x₀ = x` (transitivity of the action) rewritten. -/
theorem inv_smul_section (hs : ∀ x, s x • x₀ = x) (x : X) : (s x)⁻¹ • x = x₀ :=
  calc (s x)⁻¹ • x = (s x)⁻¹ • (s x • x₀) := by rw [hs x]
    _ = x₀ := inv_smul_smul _ _

/-- The second formula for the intertwiner: `W ψ x = p x₀ (U (s x)⁻¹ ψ)`. -/
theorem mackeyMap_eq (hs : ∀ x, s x • x₀ = x) (ψ : E) (x : X) :
    mackeyMap S s ψ x = S.p x₀ (S.U (s x)⁻¹ ψ) := by
  have h := S.covariant (s x)⁻¹ x ψ
  rw [inv_smul_section hs x] at h
  exact h

theorem mackeyMap_add (ψ φ : E) : mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ := by
  funext x
  simp [mackeyMap]

theorem mackeyMap_smul (a : ℂ) (ψ : E) : mackeyMap S s (a • ψ) = a • mackeyMap S s ψ := by
  funext x
  simp [mackeyMap]

/-- The intertwiner takes values in the induced space. -/
theorem mackeyMap_mem_inducedSpace (hs : ∀ x, s x • x₀ = x) (ψ : E) :
    mackeyMap S s ψ ∈ InducedSpace S x₀ := by
  intro x
  rw [mackeyMap_eq hs, S.idem]

/-- The intertwiner is norm-preserving componentwise. -/
theorem mackeyMap_norm (ψ : E) (x : X) : ‖mackeyMap S s ψ x‖ = ‖S.p x ψ‖ := by
  simp [mackeyMap]

/-- **`W` is an isometry**: `∑ x, ‖W ψ x‖² = ‖ψ‖²`. -/
theorem mackeyMap_norm_sq (ψ : E) : ∑ x : X, ‖mackeyMap S s ψ x‖ ^ 2 = ‖ψ‖ ^ 2 := by
  simp only [mackeyMap_norm]
  exact S.pvm_parseval ψ

/-- Reconstruction of the state from its field: `ψ = ∑ x, U (s x) (W ψ x)`. -/
theorem mackeyMap_reconstruct (ψ : E) : ∑ x : X, S.U (s x) (mackeyMap S s ψ x) = ψ := by
  have : ∀ x : X, S.U (s x) (mackeyMap S s ψ x) = S.p x ψ := by
    intro x
    simp [mackeyMap]
  simp only [this]
  exact S.complete ψ

theorem mackeyMap_injective : Function.Injective (mackeyMap S s) := by
  intro ψ φ h
  rw [← mackeyMap_reconstruct (S := S) (s := s) ψ, ← mackeyMap_reconstruct (S := S) (s := s) φ, h]

/-- **`W` is onto the induced space**: every fibre-valued field comes from a state. -/
theorem mackeyMap_surjective (hs : ∀ x, s x • x₀ = x) {f : X → E}
    (hf : f ∈ InducedSpace S x₀) : ∃ ψ : E, mackeyMap S s ψ = f := by
  refine ⟨∑ x : X, S.U (s x) (f x), ?_⟩
  -- each summand lies in the `x`-th fibre
  have hfib : ∀ x : X, S.p x (S.U (s x) (f x)) = S.U (s x) (f x) := by
    intro x
    have h := S.covariant (s x) x₀ (f x)
    rw [hf x, hs x] at h
    exact h.symm
  funext y
  have hsum : S.p y (∑ x : X, S.U (s x) (f x)) = S.U (s y) (f y) := by
    rw [map_sum, Finset.sum_eq_single y]
    · exact hfib y
    · intro x _ hx
      rw [← hfib x]
      exact S.orthogonal y x (Ne.symm hx) _
    · intro h; simp at h
  simp only [mackeyMap, hsum, S.U_inv_apply]

/-! ### The cocycle and the fibre representation of the stabilizer -/

omit [Fintype X] in
theorem cocycle_mem_stabilizer (hs : ∀ x, s x • x₀ = x) (g : G) (x : X) :
    cocycle s g x ∈ MulAction.stabilizer G x₀ := by
  change cocycle s g x • x₀ = x₀
  rw [cocycle, mul_smul, mul_smul, hs (g⁻¹ • x), smul_inv_smul, inv_smul_section hs x]

/-- The unitaries of the stabilizer preserve the fibre: this is the representation `L` of
`H` on `𝒦` that the theorem induces. -/
theorem fibre_stabilizer_invariant {h : G} (hh : h ∈ MulAction.stabilizer G x₀) {v : E}
    (hv : S.p x₀ v = v) : S.p x₀ (S.U h v) = S.U h v := by
  have hx : h • x₀ = x₀ := hh
  have := S.covariant h x₀ v
  rw [hx, hv] at this
  exact this.symm

/-- Elements of the stabilizer commute with the fibre projection. -/
theorem stabilizer_comm_fibre {h : G} (hh : h ∈ MulAction.stabilizer G x₀) (v : E) :
    S.U h (S.p x₀ v) = S.p x₀ (S.U h v) := by
  have hx : h • x₀ = x₀ := hh
  have := S.covariant h x₀ v
  rw [hx] at this
  exact this

/-! ### The two intertwining relations -/

/-- **`W` turns `U` into the induced representation.** -/
theorem mackeyMap_intertwines_U (hs : ∀ x, s x • x₀ = x) (g : G) (ψ : E) :
    mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ) := by
  funext x
  rw [mackeyMap_eq hs, inducedRep, mackeyMap_eq hs,
    stabilizer_comm_fibre (cocycle_mem_stabilizer hs g x), S.U_mul_apply, S.U_mul_apply]
  congr 2
  rw [cocycle]
  group

/-- **`W` turns the projection-valued measure into multiplication by indicators.** -/
theorem mackeyMap_intertwines_pvm [DecidableEq X] (y : X) (ψ : E) :
    mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ) := by
  funext x
  by_cases hxy : x = y
  · subst hxy
    simp [mackeyMap, inducedPvm, S.idem]
  · simp [mackeyMap, inducedPvm, hxy, S.orthogonal x y hxy]

/-! ## Mackey's imprimitivity theorem -/

/-- **Mackey's imprimitivity theorem (transitive discrete case).**  Let `(U, p)` be a
system of imprimitivity of `G` over the finite transitive `G`-space `X`, `x₀ ∈ X` a base
point, `H = Stab(x₀)` and `𝒦 = ran p x₀` the fibre over `x₀`.  Then, for any choice of
coset representatives `s`, the map `W ψ x = U (s x)⁻¹ (p x ψ)` is a linear bijection of
the Hilbert space onto the space of `𝒦`-valued fields on `X`, it preserves the norm, and
it carries `U` to the representation induced from `L = U|_H` and the projection-valued
measure to multiplication by indicators.  Hence the system is unitarily equivalent to the
canonical system induced by `L`. -/
theorem mackey_imprimitivity [DecidableEq X] (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
    (hs : ∀ x, s x • x₀ = x) :
    (∀ ψ φ : E, mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ) ∧
    (∀ (a : ℂ) (ψ : E), mackeyMap S s (a • ψ) = a • mackeyMap S s ψ) ∧
    (∀ ψ : E, mackeyMap S s ψ ∈ InducedSpace S x₀) ∧
    (∀ ψ : E, ∑ x : X, ‖mackeyMap S s ψ x‖ ^ 2 = ‖ψ‖ ^ 2) ∧
    Function.Injective (mackeyMap S s) ∧
    (∀ f ∈ InducedSpace S x₀, ∃ ψ : E, mackeyMap S s ψ = f) ∧
    (∀ (g : G) (ψ : E), mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ)) ∧
    (∀ (y : X) (ψ : E), mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ)) :=
  ⟨mackeyMap_add, mackeyMap_smul, fun ψ => mackeyMap_mem_inducedSpace hs ψ,
    mackeyMap_norm_sq, mackeyMap_injective,
    fun _ hf => mackeyMap_surjective hs hf,
    fun g ψ => mackeyMap_intertwines_U hs g ψ, mackeyMap_intertwines_pvm⟩

end BookProof.ChapterMackeyImprimitivity
