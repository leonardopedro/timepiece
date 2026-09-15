import Mathlib
import BookProof.ChapterMackeyImprimitivity
import BookProof.ChapterOrthogonalSums

/-!
# Mackey's imprimitivity theorem over an arbitrary transitive base

`BookProof.ChapterMackeyImprimitivity` proves Mackey's theorem for a **finite** transitive
base `X` and a *chosen* section `s : X → G`.  This file removes both restrictions: the base
is an arbitrary (possibly infinite) `G`-set, the projection-valued measure is summable in
the unconditional (`HasSum`) sense — which is exactly what a projection-valued measure on a
discrete space gives — and the section is *constructed* from transitivity, so the theorem
takes only the transitivity hypothesis.

## The set-up

`ImprimitivitySystem` is the same structure as in the finite case except that the
completeness relation `∑ x, p x ψ = ψ` is replaced by `HasSum (fun x => p x ψ) ψ`.  The
induced space is the `ℓ²`-space of fibre-valued fields:

  `InducedSpace S x₀ = {f | (∀ x, p x₀ (f x) = f x) ∧ Summable fun x => ‖f x‖²}`.

## Results

(The Hilbert-space facts about unconditional sums of orthogonal families that the proof
needs are in `BookProof.ChapterOrthogonalSums`.)

* `pvm_hasSum_norm_sq` — Parseval for the projection-valued measure, `∑ x ‖p x ψ‖² = ‖ψ‖²`;
* `mackeyMap_*` — Mackey's intertwiner `W ψ x = U (s x)⁻¹ (p x ψ)` is linear, lands in the
  induced space, is isometric in the `ℓ²` sense, injective, and **onto** the induced space
  (here the square-summability of the field is exactly what makes the reconstruction
  `ψ = ∑ x U (s x) (f x)` converge);
* `mackeyMap_intertwines_U`, `mackeyMap_intertwines_pvm` — the two covariance relations;
* **`mackey_imprimitivity_general`** — Mackey's imprimitivity theorem: for *any* transitive
  `G`-space `X`, any system of imprimitivity over `X` is unitarily equivalent, through a
  section built from transitivity, to the system induced by the representation of the
  stabilizer of a base point on the fibre over it.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace

namespace BookProof.ChapterMackeyGeneralBase

open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A **system of imprimitivity** over an arbitrary discrete base `X`: a unitary
representation `U` together with the atoms `p x` of a projection-valued measure on `X`
(self-adjoint, idempotent, pairwise orthogonal and unconditionally summing to the
identity), satisfying the covariance relation `U(g) π(A) U(g)⁻¹ = π(gA)`. -/
structure ImprimitivitySystem (G X E : Type*) [Group G] [MulAction G X]
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
  /-- The atoms sum to the identity, unconditionally: `π(X) = 1`. -/
  complete : ∀ ψ, HasSum (fun x => p x ψ) ψ
  /-- Covariance: `U(g) π(A) U(g)⁻¹ = π(gA)`. -/
  covariant : ∀ g x ψ, U g (p x ψ) = p (g • x) (U g ψ)

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

/-- The atoms of the measure are pairwise orthogonal as vectors. -/
theorem inner_pvm_eq_zero {x y : X} (hxy : x ≠ y) (ψ φ : E) :
    ⟪S.p x ψ, S.p y φ⟫_ℂ = 0 := by
  rw [S.selfAdjoint x ψ (S.p y φ), S.orthogonal x y hxy, inner_zero_right]

/-- **Parseval's identity for the projection-valued measure.** -/
theorem pvm_hasSum_norm_sq (ψ : E) : HasSum (fun x => ‖S.p x ψ‖ ^ 2) (‖ψ‖ ^ 2) :=
  hasSum_norm_sq_of_hasSum (S.complete ψ) fun _ _ hxy => S.inner_pvm_eq_zero hxy ψ ψ

end ImprimitivitySystem

/-! ## The induced system -/

variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)

/-- The `ℓ²`-space of fields over `X` with values in the fibre over `x₀`. -/
def InducedSpace : Set (X → E) :=
  {f | (∀ x, S.p x₀ (f x) = f x) ∧ Summable fun x => ‖f x‖ ^ 2}

/-- Mackey's cocycle `(s x)⁻¹ g s(g⁻¹ x)`, with values in the stabilizer of `x₀`. -/
def cocycle (g : G) (x : X) : G := (s x)⁻¹ * g * s (g⁻¹ • x)

/-- The induced representation of `G` on fields over `X` with values in the fibre. -/
def inducedRep (g : G) (f : X → E) : X → E := fun x => S.U (cocycle s g x) (f (g⁻¹ • x))

/-- The induced projection-valued measure: multiplication by the indicator of `{y}`. -/
def inducedPvm [DecidableEq X] (y : X) (f : X → E) : X → E := fun x => if x = y then f x else 0

/-- **Mackey's intertwiner** `W ψ x = U (s x)⁻¹ (p x ψ)`. -/
def mackeyMap (ψ : E) : X → E := fun x => S.U (s x)⁻¹ (S.p x ψ)

variable {S x₀ s}

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

/-- The intertwiner is norm-preserving componentwise. -/
theorem mackeyMap_norm (ψ : E) (x : X) : ‖mackeyMap S s ψ x‖ = ‖S.p x ψ‖ := by
  simp [mackeyMap]

/-- **`W` is an isometry onto the `ℓ²`-space**: `∑ x ‖W ψ x‖² = ‖ψ‖²`. -/
theorem mackeyMap_hasSum_norm_sq (ψ : E) :
    HasSum (fun x => ‖mackeyMap S s ψ x‖ ^ 2) (‖ψ‖ ^ 2) := by
  simpa only [mackeyMap_norm] using S.pvm_hasSum_norm_sq ψ

/-- The intertwiner takes values in the induced space. -/
theorem mackeyMap_mem_inducedSpace (hs : ∀ x, s x • x₀ = x) (ψ : E) :
    mackeyMap S s ψ ∈ InducedSpace S x₀ := by
  refine ⟨fun x => ?_, (mackeyMap_hasSum_norm_sq (S := S) (s := s) ψ).summable⟩
  rw [mackeyMap_eq hs, S.idem]

/-- Reconstruction of the state from its field: `ψ = ∑ x U (s x) (W ψ x)`. -/
theorem mackeyMap_reconstruct (ψ : E) :
    HasSum (fun x => S.U (s x) (mackeyMap S s ψ x)) ψ := by
  have h : ∀ x : X, S.U (s x) (mackeyMap S s ψ x) = S.p x ψ := by
    intro x
    simp [mackeyMap]
  simpa only [h] using S.complete ψ

theorem mackeyMap_injective : Function.Injective (mackeyMap S s) := by
  intro ψ φ h
  have h1 : HasSum (fun x => S.U (s x) (mackeyMap S s ψ x)) ψ := mackeyMap_reconstruct ψ
  have h2 : HasSum (fun x => S.U (s x) (mackeyMap S s φ x)) φ := mackeyMap_reconstruct φ
  rw [h] at h1
  exact h1.unique h2

/-- **`W` is onto the induced space**: every square-summable fibre-valued field comes from a
state. -/
theorem mackeyMap_surjective [CompleteSpace E] (hs : ∀ x, s x • x₀ = x) {f : X → E}
    (hf : f ∈ InducedSpace S x₀) : ∃ ψ : E, mackeyMap S s ψ = f := by
  obtain ⟨hfib₀, hsum⟩ := hf
  -- each summand lies in the `x`-th fibre
  have hfib : ∀ x : X, S.p x (S.U (s x) (f x)) = S.U (s x) (f x) := by
    intro x
    have h := S.covariant (s x) x₀ (f x)
    rw [hfib₀ x, hs x] at h
    exact h.symm
  have horth : ∀ x y : X, x ≠ y → ⟪S.U (s x) (f x), S.U (s y) (f y)⟫_ℂ = 0 := by
    intro x y hxy
    rw [← hfib x, ← hfib y]
    exact S.inner_pvm_eq_zero hxy _ _
  have hnorm : ∀ x : X, ‖S.U (s x) (f x)‖ = ‖f x‖ := fun x => by simp
  have hsum' : Summable fun x => ‖S.U (s x) (f x)‖ ^ 2 := by
    simpa only [hnorm] using hsum
  obtain ⟨ψ, hψ⟩ := summable_of_orthogonal_of_summable_norm_sq horth hsum'
  refine ⟨ψ, ?_⟩
  funext y
  have hpy : HasSum (fun x => S.p y (S.U (s x) (f x))) (S.p y ψ) := hψ.mapL (S.p y)
  have hpy' : HasSum (fun x => S.p y (S.U (s x) (f x))) (S.U (s y) (f y)) := by
    have h : ∀ x : X, x ≠ y → S.p y (S.U (s x) (f x)) = 0 := by
      intro x hx
      rw [← hfib x]
      exact S.orthogonal y x (Ne.symm hx) _
    have := hasSum_single (f := fun x => S.p y (S.U (s x) (f x))) y h
    rwa [hfib y] at this
  have hval : S.p y ψ = S.U (s y) (f y) := hpy.unique hpy'
  simp [mackeyMap, hval]

/-! ### The cocycle and the fibre representation of the stabilizer -/

theorem cocycle_mem_stabilizer (hs : ∀ x, s x • x₀ = x) (g : G) (x : X) :
    cocycle s g x ∈ MulAction.stabilizer G x₀ := by
  change cocycle s g x • x₀ = x₀
  rw [cocycle, mul_smul, mul_smul, hs (g⁻¹ • x), smul_inv_smul, inv_smul_section hs x]

/-- The unitaries of the stabilizer preserve the fibre: this is the representation `L` of
`H = Stab(x₀)` on the fibre `𝒦`. -/
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

/-! ## Mackey's imprimitivity theorem over an arbitrary transitive base -/

/-- **Mackey's imprimitivity theorem.**  Let `X` be *any* transitive `G`-space, `x₀ ∈ X` a
base point, `H = Stab(x₀)`, and let `(U, p)` be a system of imprimitivity of `G` over `X` on
a complex Hilbert space.  Then there is a section `s` of the orbit map (built from
transitivity) for which Mackey's map `W ψ x = U (s x)⁻¹ (p x ψ)` is a linear bijection of
the Hilbert space onto the `ℓ²`-space of fields with values in the fibre `𝒦 = ran p x₀`, it
preserves the norm, and it carries `U` to the representation induced from `L = U|_H` and the
projection-valued measure to multiplication by indicators.  No finiteness of `X` and no
choice of section are assumed. -/
theorem mackey_imprimitivity_general [CompleteSpace E] [DecidableEq X]
    (S : ImprimitivitySystem G X E) (x₀ : X) (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) :
    ∃ s : X → G, (∀ x, s x • x₀ = x) ∧
      (∀ ψ φ : E, mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ) ∧
      (∀ (a : ℂ) (ψ : E), mackeyMap S s (a • ψ) = a • mackeyMap S s ψ) ∧
      (∀ ψ : E, mackeyMap S s ψ ∈ InducedSpace S x₀) ∧
      (∀ ψ : E, HasSum (fun x => ‖mackeyMap S s ψ x‖ ^ 2) (‖ψ‖ ^ 2)) ∧
      Function.Injective (mackeyMap S s) ∧
      (∀ f ∈ InducedSpace S x₀, ∃ ψ : E, mackeyMap S s ψ = f) ∧
      (∀ (g : G) (ψ : E), mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ)) ∧
      (∀ (y : X) (ψ : E), mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ)) := by
  classical
  refine ⟨fun x => (htrans x).choose, fun x => (htrans x).choose_spec, mackeyMap_add,
    mackeyMap_smul, fun ψ => mackeyMap_mem_inducedSpace (fun x => (htrans x).choose_spec) ψ,
    mackeyMap_hasSum_norm_sq, mackeyMap_injective,
    fun _ hf => mackeyMap_surjective (fun x => (htrans x).choose_spec) hf,
    fun g ψ => mackeyMap_intertwines_U (fun x => (htrans x).choose_spec) g ψ,
    mackeyMap_intertwines_pvm⟩

/-! ## The finite theory is a special case

Every system of imprimitivity over a finite base in the sense of
`BookProof.ChapterMackeyImprimitivity` is one in the present sense, so the general theorem
above really extends the finite one (and its hypotheses are consistent). -/

/-- A system of imprimitivity over a finite base, viewed as a system over an arbitrary
base: the finite sum `∑ x, p x ψ = ψ` is an unconditional sum. -/
def ofFintype [Fintype X] (S : ChapterMackeyImprimitivity.ImprimitivitySystem G X E) :
    ImprimitivitySystem G X E where
  U := S.U
  p := S.p
  selfAdjoint := S.selfAdjoint
  idem := S.idem
  orthogonal := S.orthogonal
  complete ψ := by
    have h : ∑ x, S.p x ψ = ψ := S.complete ψ
    simpa [h] using hasSum_fintype (fun x => S.p x ψ)
  covariant := S.covariant

end BookProof.ChapterMackeyGeneralBase
