import Mathlib
import BookProof.Toolbox.ChapterHermiteProductBasis

/-!
# The 4D Euclidean Hermite product basis

Plan: `cftproof.md`, Phase 1.1 — "Define the 4D product Hermite basis
`EuclideanHermiteBasis4D : OrthonormalBasis (ℕ⁴ × Fin 4 × Fin (N^2-1)) ℂ ...`".

## What is proved here (not stubbed)

The corpus already contains the product Hermite basis of `L²(ℝᵈ)`, *with* the ladder
relations, as `BookProof.HermiteProductBasis.hermiteMvBasis (d : ℕ)`:
a `HilbertBasis` indexed by the multi-indices `Fin d →₀ ℕ`, whose vectors are the
normalized products `ψ_α(x) = ∏ᵢ He_{αᵢ}(xᵢ) e^{-‖x‖²/4}` (`hermiteMvLp`).
Its orthonormality is `orthonormal_hermiteMvLp`; its totality is the density of the
Gauss–polynomial core (`polyGaussCore_dense`).

That is precisely the object Phase 1.1 asks for, at `d = 4`, so here it is *instantiated*
rather than re-proved: `euclideanHermiteBasis4D` **is** `hermiteMvBasis (d := 4)`.
Consequently every statement about it below is a theorem about a Hilbert basis that
already exists in the corpus, and the ladder operators it is meant to support are already
proved there (`annPoly_hermiteMvLp`, `crePoly_hermiteMvLp`).

## Index dictionary (Lean ⇄ plan)

| plan index component | Lean index | meaning |
|---|---|---|
| `ℕ⁴` | `Fin 4 →₀ ℕ` | Hermite multi-index `α = (α₀,…,α₃)` (finsupp out of `Fin 4` *is* `ℕ⁴`) |
| `Fin 4` | — (see §Boundary) | Lorentz/vector index `μ` of `A_μ` |
| `Fin (N^2-1)` | — (see §Boundary), `colourBasis` | `su(N)` colour index `a` |

`ℕ⁴` and `Fin 4 →₀ ℕ` are the same data; we write the finsupp because that is the index
type of the corpus basis (and the type on which its ladder relations are stated).

## Boundary (recorded, not assumed away)

Mathlib has **no Hilbert tensor product**, so the plan's index `ℕ⁴ × Fin 4 × Fin (N²−1)`
cannot be realized as the index of an `OrthonormalBasis` of one space: the `μ` and colour
factors require `L²(ℝ⁴) ⊗ ℝ⁴ ⊗ ℝ^{N²−1}`, and there is no `InnerProductSpace`
instance on `PiLp 2` / `lp` in this Mathlib (checked: `Mathlib/Analysis/Normed/Lp/PiLp.lean`
and `lpSpace.lean` carry no `InnerProductSpace` instance), nor an `OrthonormalBasis.prod`.
What is therefore proved is the basis of the *scalar* layer `L²(ℝ⁴)` — the layer that
carries the measure, the reflection and the positivity statements of the later phases —
together with the colour factor's own orthonormal basis (`colourBasis`), which is the
finite-rank factor the book multiplies in by hand. The finite-rank passage is carried
as a hypothesis by the phases that need it, not silently dropped.
-/

namespace BookProof.EuclideanFock4D

open BookProof.HermiteProductCore BookProof.HermiteProductBasis

noncomputable section

/-! ## The layers -/

/-- The Euclidean `4`-space of the free field: spacetime points `x = (x₀,x₁,x₂,x₃)`. -/
abbrev Spacetime4D : Type := Vd 4

/-- The one-particle Hilbert space of the free Euclidean scalar field: `L²(ℝ⁴, ℂ)`. -/
abbrev FockLayerSpace : Type := L2d 4

/-- The dimension of the `su(N)` colour factor. -/
def colourDim (N : ℕ) : ℕ := N ^ 2 - 1

/-! ## Phase 1.1: the 4D product Hermite basis -/

/-- **The 4D product Hermite orthonormal basis** of `L²(ℝ⁴, ℂ)`.

This is `hermiteMvBasis` at `d = 4`: the family `ψ_α / ‖ψ_α‖`, `α : Fin 4 →₀ ℕ`, of
normalized products of the one-dimensional Hermite functions.  Being a `HilbertBasis`
it is simultaneously orthonormal and total; both facts are inherited from the corpus. -/
def euclideanHermiteBasis4D : HilbertBasis (Fin 4 →₀ ℕ) ℂ FockLayerSpace :=
  hermiteMvBasis (d := 4)

/-- The `α`-th basis vector is the normalized product Hermite function. -/
@[simp]
theorem euclideanHermiteBasis4D_apply (a : Fin 4 →₀ ℕ) :
    euclideanHermiteBasis4D a = hermiteMvLp (d := 4) a := by
  rw [euclideanHermiteBasis4D, hermiteMvBasis_apply]

/-- **Orthonormality** of the 4D product Hermite basis. -/
theorem euclideanHermiteBasis4D_orthonormal : Orthonormal ℂ (⇑euclideanHermiteBasis4D) :=
  euclideanHermiteBasis4D.orthonormal

/-- **Totality**: the closure of the span of the 4D product Hermite basis is everything.
This is the `HilbertBasis` content of `hermiteMvBasis`, itself built from
`orthonormal_hermiteMvLp`, `span_hermiteMvLp` and the density of the Gauss–polynomial core. -/
theorem euclideanHermiteBasis4D_total :
    (Submodule.span ℂ (Set.range (⇑euclideanHermiteBasis4D))).topologicalClosure = ⊤ :=
  euclideanHermiteBasis4D.dense_span

/-- The span of the 4D basis is the Gauss–polynomial core of the corpus. -/
theorem euclideanHermiteBasis4D_span_eq :
    Submodule.span ℂ (Set.range (⇑euclideanHermiteBasis4D)) = polyGaussCore (d := 4) := by
  rw [euclideanHermiteBasis4D]
  have hrange : Set.range (⇑(hermiteMvBasis (d := 4))) = Set.range (hermiteMvLp (d := 4)) := by
    ext v
    simp only [Set.mem_range, hermiteMvBasis_apply]
  rw [hrange, span_hermiteMvLp]

/-- The basis, enumerated by `ℕ`: the `net` of Phase 1.1.  (The plan's `_net` is the
sequence-shaped version of the basis used when the `S^∞` inductive limit is taken; it needs
an enumeration `e : ℕ ≃ (Fin 4 →₀ ℕ)`, exactly as `coreFamily`/`coreBasis` in
`ChapterHermiteProductCore` take one.) -/
def euclideanHermiteNet4D (e : ℕ ≃ (Fin 4 →₀ ℕ)) : ℕ → FockLayerSpace :=
  fun n => euclideanHermiteBasis4D (e n)

/-- The enumerated basis is still orthonormal. -/
theorem euclideanHermiteNet4D_orthonormal (e : ℕ ≃ (Fin 4 →₀ ℕ)) :
    Orthonormal ℂ (euclideanHermiteNet4D e) := by
  rw [orthonormal_iff_ite]
  intro m n
  have h := (orthonormal_iff_ite.mp euclideanHermiteBasis4D_orthonormal) (e m) (e n)
  simpa [euclideanHermiteNet4D, e.injective.eq_iff] using h

/-- Every sector carries an orthonormal basis: the instance shape used by the plan's
`instance (N : ℕ) : SectorHasONB`. -/
instance instSectorHasONB : Nonempty (HilbertBasis (Fin 4 →₀ ℕ) ℂ FockLayerSpace) :=
  ⟨euclideanHermiteBasis4D⟩

/-! ## The colour factor -/

/-- The `su(N)` colour factor `ℝ^{N²−1}` (complexified) with its standard orthonormal basis.
This is the finite-rank factor the plan multiplies into the index; see the boundary note for
why it is not merged into `euclideanHermiteBasis4D`'s index. -/
def colourBasis (N : ℕ) :
    OrthonormalBasis (Fin (colourDim N)) ℂ (EuclideanSpace ℂ (Fin (colourDim N))) :=
  EuclideanSpace.basisFun (Fin (colourDim N)) ℂ

end

end BookProof.EuclideanFock4D
