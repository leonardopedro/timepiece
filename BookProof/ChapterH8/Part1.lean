import Mathlib
import BookProof.ChapterH4
import BookProof.ChapterH5
import BookProof.ChapterH6

/-!
# Chapter H8 — the SIRK approximation orders nest (plan `PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`)

The Hashimoto SIRK approximations form a *nested tower of orders*: the order-`n+1`
approximation refines the order-`n` one.  This file proves the four ingredients of
that statement for the generic Krylov–Hashimoto machinery of `ChapterH4`–`ChapterH6`
(it is not Navier–Stokes specific — it constrains any SIRK evolution).

## Deliverables

* **(a) subspace nesting** — `sirk_krylov_tower`: `Kry n ≤ Kry (n+1)`, the tower
  form of `ChapterH5.krylovSpan_mono`;
* **(b) block compatibility (new)** — `sirk_compression_block` /
  `sirk_compression_submatrix`: for nested orthonormal bases
  (`Vₙ eᵢ = Vₙ₊₁ e_{castSucc i}`) the order-`n` reduced generator
  (`ChapterH6.reduceGenerator`) is the leading `n × n` block of the order-`n+1`
  one; between any two orders `m ≤ n` this is `sirk_compression_block_le` /
  `sirk_compression_submatrix_le`.  Its operator form is `sirk_compression_block_op`,
  `compress Vₙ X = J∗ (compress Vₙ₊₁ X) J` for the coordinate inclusion `J`
  with `Vₙ = Vₙ₊₁ ∘ J`;
* **(c) projection refinement (new, headline)** — `sirk_band_refinement`: on the
  order-`n` data (`v ∈ Kry n`, i.e. `Vₙ Vₙ∗ v = v`) the order-`n+1` approximant
  *equals* the order-`n` approximant, and `sirk_band_refinement_proj` states this
  as "project the finer approximant back into `Kry n`".  On the *whole* space the
  statement `sirk_approx_projection` needs `Kry n` to reduce `X` (invariant under
  both `X` and `X∗`); the intertwining engine is
  `compress_comp_intertwine` / `compress_pow_comp_intertwine`;
* **(c′) polynomial and rational refinement (new)** — the same refinement for the
  functions the SIRK method actually evaluates: `sirk_band_refinement_poly` for
  an arbitrary polynomial `p` of the reduced generator,
  `sirk_band_refinement_rational` for a rational function `p/q` (an invertible
  denominator and its invertible compression), and `sirk_approx_projection_poly`
  for the whole-space projection form, and `sirk_approx_projection_rational` for
  the whole-space form of the rational case (the subspace must reduce both the
  numerator generator and the denominator).  The transfer engines are
  `compress_aeval_comp`, `compress_aeval_transfer`, `compress_inv_transfer_apply`,
  `compress_rational_transfer`, the transposed intertwinings
  `compress_adjoint_intertwine` / `compress_adjoint_intertwine_poly` and the
  inverse-intertwining lemma `inv_comp_intertwine`;
* **(c″) the hypotheses are realized** — the refinement theorems here are stated
  for an abstract factorization `Vₘ = Vₙ ∘ J`; the companion module
  `BookProof/ChapterH8Bases.lean` shows the hypotheses are met by any nested pair
  of orthonormal families, and by the orthonormal Krylov bases themselves
  (`sirk_band_refinement_of_orthonormal`, `sirk_band_refinement_krylov`);
* **(d) band containment** — `sirk_band_contained`: the error bands nest,
  `[0, sirkBound (n+1)] ⊆ [0, sirkBound n]` (from
  `ChapterH6.sirk_error_bound_antitone`), and `sirk_bands_tendsto_zero` records
  that the nested family collapses to `{0}`
  (`ChapterH6.sirk_error_decay_exponential`);
* **the tower** — `sirk_nested_orders` assembles (a) and (d) for every `n`, and
  `sirk_nested_orders_le` / `sirk_band_contained_le` do so between any two orders
  `m ≤ n`.

## Correspondence

`ChapterH5.lean` supplies the Krylov span and its monotonicity, `ChapterH6.lean`
the reduced generator and the antitone/decaying bound, `ChapterH4.lean` the
compression `compress = V∗ X V` and its transfer identities
(`compress_pow`, `compress_transfer`, `compress_inv_transfer`).  The prose
counterpart is the nested-orders paragraph of `Book/FreeField.lean`
§"Dimensional Reduction".

## The exact boundary

Everything here is finite-dimensional linear algebra over the decidable skeleton:
no Crouzeix inequality, no infinite spectrum, no `EXTERNAL` hypothesis.  What is
**not** claimed is the numerical *width* of the bands — that the true error lies
inside `sirkBound n` is conditional on Crouzeix's inequality, which enters
`ChapterH4.sirk_error_bound_decay` as a *named hypothesis*, never an axiom.  The
nesting (a)–(d) holds whether or not Crouzeix is ever proved.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterH8

open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

/-! ## Part 1 — the Krylov subspaces nest -/

section Tower

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- **(a)** The Krylov flag is a tower: the order-`n` subspace sits inside the
order-`n+1` subspace.  Tower form of `ChapterH5.krylovSpan_mono`. -/
theorem sirk_krylov_tower (H : E →ₗ[K] E) (v : E) (n : ℕ) :
    krylovSpan H v n ≤ krylovSpan H v (n + 1) :=
  krylovSpan_mono (Nat.le_succ n)

end Tower

/-! ## Part 2 — the block compatibility lemma -/

section Compression

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

open ContinuousLinearMap in
/-- **(b), operator form.**  If the coarse embedding factors through the fine one,
`Vₙ = Vₙ₊₁ ∘ J`, then the coarse compression is the `J`-block of the fine
compression: `V∗ₙ X Vₙ = J∗ (V∗ₙ₊₁ X Vₙ₊₁) J`. -/
theorem sirk_compression_block_op (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) :
    compress Vn X = (adjoint J).comp ((compress Vm X).comp J) := by
  subst hJ
  ext x
  simp [compress]

open ContinuousLinearMap in
/-- The coarse embedding is isometric as soon as the fine one is and the
coordinate inclusion `J` is: `V∗ₙ Vₙ = 1`. -/
theorem adjoint_comp_self_of_nested (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F) :
    (adjoint Vn).comp Vn = ContinuousLinearMap.id ℂ F := by
  subst hJ
  ext x
  have hx : (adjoint Vm) (Vm (J x)) = J x :=
    congrArg (fun f : G →L[ℂ] G => f (J x)) hVm
  have hy : (adjoint J) (J x) = x :=
    congrArg (fun f : F →L[ℂ] F => f x) hJJ
  simp [hx, hy]

open ContinuousLinearMap in
/-- The coarse adjoint composed with the fine embedding is the coordinate
projection: `V∗ₙ Vₙ₊₁ = J∗`. -/
theorem adjoint_comp_nested (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G) :
    (adjoint Vn).comp Vm = adjoint J := by
  subst hJ
  ext x
  have hx : (adjoint Vm) (Vm x) = x :=
    congrArg (fun f : G →L[ℂ] G => f x) hVm
  simp [hx]

open ContinuousLinearMap in
/-- The adjoint of a compression is the compression of the adjoint. -/
theorem adjoint_compress (V : F →L[ℂ] E) (X : E →L[ℂ] E) :
    adjoint (compress V X) = compress V (adjoint X) := by
  rw [compress, compress, adjoint_comp, adjoint_comp, adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

open ContinuousLinearMap in
/-- The adjoint of a power is the power of the adjoint. -/
theorem adjoint_pow (A : F →L[ℂ] F) (k : ℕ) : adjoint (A ^ k) = (adjoint A) ^ k := by
  simp [← ContinuousLinearMap.star_eq_adjoint, star_pow]

end Compression

/-! ### The matrix form of the block lemma -/

section Block

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **(b), matrix entry form.**  For nested orthonormal Krylov bases
(`Vₙ eᵢ = Vₙ₊₁ e_{castSucc i}`) the order-`n` reduced generator entry `(i, j)` is
the entry `(castSucc i, castSucc j)` of the order-`n+1` reduced generator: the
order-`n` reduced matrix is the leading `n × n` submatrix of the order-`n+1`
one. -/
theorem sirk_compression_block (n : ℕ) (X : E →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] E)
    (hnest : ∀ i : Fin n, Vn (EuclideanSpace.single i (1 : ℂ))
      = Vm (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)))
    (i j : Fin n) :
    reduceGenerator n Vn X i j
      = reduceGenerator (n + 1) Vm X (Fin.castSucc i) (Fin.castSucc j) := by
  simp [reduceGenerator, hnest]

omit [CompleteSpace E] in
/-- **(b), submatrix form.**  `Bₙ` is the leading `n × n` submatrix of `Bₙ₊₁`. -/
theorem sirk_compression_submatrix (n : ℕ) (X : E →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] E)
    (hnest : ∀ i : Fin n, Vn (EuclideanSpace.single i (1 : ℂ))
      = Vm (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ))) :
    reduceGenerator n Vn X
      = (reduceGenerator (n + 1) Vm X).submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simpa using sirk_compression_block n X Vn Vm hnest i j

omit [CompleteSpace E] in
/-- **(b) at arbitrary orders.**  For any pair of orders `m ≤ n` with nested bases
(`Vₘ eᵢ = Vₙ e_{castLE i}`) the order-`m` reduced generator is the leading
`m × m` submatrix of the order-`n` one — the block identity iterated up the whole
tower, not just one step. -/
theorem sirk_compression_block_le {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin m) →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (hnest : ∀ i : Fin m, Vm (EuclideanSpace.single i (1 : ℂ))
      = Vn (EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ)))
    (i j : Fin m) :
    reduceGenerator m Vm X i j
      = reduceGenerator n Vn X (Fin.castLE hmn i) (Fin.castLE hmn j) := by
  simp [reduceGenerator, hnest]

omit [CompleteSpace E] in
/-- **(b) at arbitrary orders, submatrix form.** -/
theorem sirk_compression_submatrix_le {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin m) →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (hnest : ∀ i : Fin m, Vm (EuclideanSpace.single i (1 : ℂ))
      = Vn (EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ))) :
    reduceGenerator m Vm X
      = (reduceGenerator n Vn X).submatrix (Fin.castLE hmn) (Fin.castLE hmn) := by
  ext i j
  simpa using sirk_compression_block_le hmn X Vm Vn hnest i j

end Block

/-! ## Part 3 — the projection-refinement theorems -/

section Refinement

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

open ContinuousLinearMap

/-- **Intertwining.**  If the coarse range `Kry n` is `X`-invariant, the coarse
compression intertwines with the fine one along the coordinate inclusion:
`Bₙ₊₁ ∘ J = J ∘ Bₙ`.  (This is the block-triangularity that makes the leading
block of the fine reduced generator a *generator in its own right*.) -/
theorem compress_comp_intertwine (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y) :
    (compress Vm X).comp J = J.comp (compress Vn X) := by
  have hVn : (adjoint Vn).comp Vn = ContinuousLinearMap.id ℂ F :=
    adjoint_comp_self_of_nested Vn Vm J hJ hVm hJJ
  ext x
  obtain ⟨y, hy⟩ := hinvn x
  have hVmJ : Vm (J x) = Vn x := by rw [hJ]; rfl
  have hVmJy : Vm (J y) = Vn y := by rw [hJ]; rfl
  have hleft : (adjoint Vm) (Vm (J y)) = J y :=
    congrArg (fun f : G →L[ℂ] G => f (J y)) hVm
  have hright : (adjoint Vn) (Vn y) = y :=
    congrArg (fun f : F →L[ℂ] F => f y) hVn
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, compress]
  rw [hVmJ, hy, hright, ← hVmJy, hleft]

/-- Powers of the intertwining relation: `Bₙ₊₁^k ∘ J = J ∘ Bₙ^k`. -/
theorem compress_pow_comp_intertwine (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y) (k : ℕ) :
    ((compress Vm X) ^ k).comp J = J.comp ((compress Vn X) ^ k) := by
  have hstep := compress_comp_intertwine Vn Vm J X hJ hVm hJJ hinvn
  induction k with
  | zero => ext x; simp
  | succ k ih =>
    ext x
    have h1 : ((compress Vm X) ^ (k + 1)) (J x)
        = ((compress Vm X) ^ k) ((compress Vm X) (J x)) := by
      rw [pow_succ]
      rfl
    have h2 : J (((compress Vn X) ^ (k + 1)) x)
        = J (((compress Vn X) ^ k) ((compress Vn X) x)) := by
      rw [pow_succ]
      rfl
    have hs : (compress Vm X) (J x) = J ((compress Vn X) x) :=
      congrArg (fun f : F →L[ℂ] G => f x) hstep
    have hi := congrArg (fun f : F →L[ℂ] G => f ((compress Vn X) x)) ih
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hi ⊢
    rw [h1, h2, hs, hi]

/-- Membership in the coarse range is inherited by the fine range. -/
theorem fine_range_of_coarse (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (v : E) (hv : Vn ((adjoint Vn) v) = v) :
    Vm ((adjoint Vm) v) = v := by
  set w : F := (adjoint Vn) v with hw
  have hvw : v = Vm (J w) := by rw [hJ] at hv; exact hv.symm
  have hmm : (adjoint Vm) (Vm (J w)) = J w :=
    congrArg (fun f : G →L[ℂ] G => f (J w)) hVm
  rw [hvw, hmm]

/-- **(c) Headline — the finer band restricted to the coarser data is the coarser
band.**  For `v` in the order-`n` Krylov subspace (`Vₙ Vₙ∗ v = v`) the order-`n+1`
SIRK approximant of `Xᵏ v` and the order-`n` one *coincide*: both equal `Xᵏ v` by
the transfer identity `ChapterH4.compress_transfer`. -/
theorem sirk_band_refinement (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y)
    (hinvm : ∀ x : G, ∃ y : G, X (Vm x) = Vm y)
    (k : ℕ) (v : E) (hv : Vn ((adjoint Vn) v) = v) :
    Vm (((compress Vm X) ^ k) ((adjoint Vm) v)) = Vn (((compress Vn X) ^ k) ((adjoint Vn) v)) := by
  have hVn : (adjoint Vn).comp Vn = ContinuousLinearMap.id ℂ F :=
    adjoint_comp_self_of_nested Vn Vm J hJ hVm hJJ
  have hvm : Vm ((adjoint Vm) v) = v := fine_range_of_coarse Vn Vm J hJ hVm v hv
  have hn := compress_transfer Vn X hVn hinvn k v hv
  have hm := compress_transfer Vm X hVm hinvm k v hvm
  rw [← hm, ← hn]

/-- **(c) as a projection statement.**  On the order-`n` data, projecting the
order-`n+1` approximant back into `Kry n` (the projection is `Vₙ Vₙ∗`) returns the
order-`n` approximant. -/
theorem sirk_band_refinement_proj (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvn : ∀ x : F, ∃ y : F, X (Vn x) = Vn y)
    (hinvm : ∀ x : G, ∃ y : G, X (Vm x) = Vm y)
    (k : ℕ) (v : E) (hv : Vn ((adjoint Vn) v) = v) :
    Vn ((adjoint Vn) (Vm (((compress Vm X) ^ k) ((adjoint Vm) v))))
      = Vn (((compress Vn X) ^ k) ((adjoint Vn) v)) := by
  have hVn : (adjoint Vn).comp Vn = ContinuousLinearMap.id ℂ F :=
    adjoint_comp_self_of_nested Vn Vm J hJ hVm hJJ
  have href := sirk_band_refinement Vn Vm J X hJ hVm hJJ hinvn hinvm k v hv
  rw [href]
  have := congrArg (fun f : F →L[ℂ] F => f (((compress Vn X) ^ k) ((adjoint Vn) v))) hVn
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq] at this
  rw [this]

/-- **(c) on the whole space.**  If the order-`n` Krylov subspace *reduces* `X`
(its range is invariant under both `X` and `X∗`), then for **every** `v` the
order-`n` approximant is exactly the order-`n+1` approximant projected back into
`Kry n`.  The `X∗`-invariance is genuinely needed: without it the leading block
governs only the coarse data (`sirk_band_refinement`), not arbitrary vectors. -/
theorem sirk_approx_projection (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F)
    (hinvadj : ∀ x : F, ∃ y : F, (adjoint X) (Vn x) = Vn y)
    (k : ℕ) (v : E) :
    Vn ((adjoint Vn) (Vm (((compress Vm X) ^ k) ((adjoint Vm) v))))
      = Vn (((compress Vn X) ^ k) ((adjoint Vn) v)) := by
  -- the `X∗`-intertwining, transposed to `J∗ ∘ Bₙ₊₁ᵏ = Bₙᵏ ∘ J∗`
  have hstar := compress_pow_comp_intertwine Vn Vm J (adjoint X) hJ hVm hJJ hinvadj k
  have hadj := congrArg ContinuousLinearMap.adjoint hstar
  rw [adjoint_comp, adjoint_comp, adjoint_pow, adjoint_pow, adjoint_compress, adjoint_compress,
    adjoint_adjoint] at hadj
  -- `V∗ₙ Vₙ₊₁ = J∗`
  have hproj : (adjoint Vn).comp Vm = adjoint J := adjoint_comp_nested Vn Vm J hJ hVm
  have h1 : (adjoint Vn) (Vm (((compress Vm X) ^ k) ((adjoint Vm) v)))
      = (adjoint J) (((compress Vm X) ^ k) ((adjoint Vm) v)) :=
    congrArg (fun f : G →L[ℂ] F => f (((compress Vm X) ^ k) ((adjoint Vm) v))) hproj
  have h2 : (adjoint J) (((compress Vm X) ^ k) ((adjoint Vm) v))
      = ((compress Vn X) ^ k) ((adjoint J) ((adjoint Vm) v)) :=
    congrArg (fun f : G →L[ℂ] F => f ((adjoint Vm) v)) hadj
  have h3 : (adjoint J) ((adjoint Vm) v) = (adjoint Vn) v := by
    have : (adjoint Vn) = (adjoint J).comp (adjoint Vm) := by
      rw [hJ, adjoint_comp]
    rw [this]
    rfl
  rw [h1, h2, h3]

end Refinement

end BookProof.ChapterH8

end
