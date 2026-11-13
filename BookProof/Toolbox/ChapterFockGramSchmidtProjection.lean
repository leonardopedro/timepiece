import Mathlib
import BookProof.Toolbox.ChapterHermiteProductCore
import BookProof.Toolbox.ChapterHermiteVanishing

/-!
# Gram–Schmidt as “the monomial minus its lower-degree projection”

The finite-mode domain of the Yang–Mills theorems is `finiteModeDomain (coreBasis e)`, where
`coreBasis e` is the Gram–Schmidt orthonormalization of the enumerated monomial Gauss functions
`coreFamily e k = [x^{e k} e^{-‖x‖²/4}]` (`BookProof.HermiteProductCore`).  To compare it with
the *product Hermite* basis one has to say exactly what a Gram–Schmidt vector is, and this module
supplies that statement in the form the comparison needs.

Write `gsSpan f k` for the span of the Gram–Schmidt vectors of `f` strictly before `k`.  Then

* `sub_gramSchmidt_mem_gsSpan` — `f k − gramSchmidt f k ∈ gsSpan f k`, i.e. the Gram–Schmidt
  vector is `f k` minus its projection onto the earlier one-dimensional spans;
* `gramSchmidt_mem_orthogonal_gsSpan` — `gramSchmidt f k` is orthogonal to `gsSpan f k`;
* `eq_of_decomp_orthogonal` — that pair of properties determines the vector: any `u` with
  `u − f k ∈ gsSpan f k` and `u ⊥ gsSpan f k` equals `gramSchmidt f k`;
* `gramSchmidt_eq_smul_of_decomp` — **the projection-comparison lemma**: if `f k − c • g` lies in
  the earlier span and `g` is orthogonal to it, then `gramSchmidt f k = c • g`.  This is what
  turns “the monomial minus its lower-degree projection” into a statement about any vector that
  *is* the orthogonal component — in particular the Hermite function, once its orthogonality below
  the degree is known;
* `gsSpan_eq_span_Iio` — the earlier Gram–Schmidt span is the span of the earlier
  monomials (`InnerProductSpace.span_gramSchmidt_Iio`);
* `coreBasis_eq_sub_projection` — `coreBasis e k` is the *normalization* of
  `x^{e k} e^{-‖x‖²/4}` minus its projection onto the earlier Gram–Schmidt spans;
* `hermiteMvLp_mem_orthogonal_gsSpan` — with the degree-compatibility hypothesis that every
  earlier monomial is smaller in some coordinate, the product Hermite function `ψ_{e k}` is
  orthogonal to the earlier Gram–Schmidt span.  This uses the vanishing lemma of
  `BookProof.HermiteVanishing`.

## Honest boundary

`gramSchmidt_eq_smul_of_decomp` still leaves two inputs open before it identifies `coreBasis e k`
with `ψ_{e k}`: expressing `x^{e k} e^{-‖x‖²/4}` in the form `w + c • ψ_{e k}` with
`w` in the earlier span (monic triangularity plus the degree-compatibility count), and the fact
that `‖c‖ = 1` for the normalized vectors.  Neither is claimed here.
-/

namespace BookProof.FockGramSchmidtProjection

open InnerProductSpace BookProof.HermiteProductCore BookProof.HermiteProductBasis
  BookProof.HermiteVanishing

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {d : ℕ}

/-! ## The span of the earlier Gram–Schmidt vectors -/

/-- The span of the Gram–Schmidt vectors of `f` with index strictly before `k`. -/
def gsSpan (f : ℕ → E) (k : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (gramSchmidt ℂ f '' Set.Iio k)

/-- The earlier Gram–Schmidt span is the span of the earlier vectors of the family. -/
theorem gsSpan_eq_span_Iio (f : ℕ → E) (k : ℕ) :
    gsSpan f k = Submodule.span ℂ (f '' Set.Iio k) :=
  span_gramSchmidt_Iio ℂ f k

/-- **The Gram–Schmidt vector is the vector minus its projection onto the earlier spans.** -/
theorem sub_gramSchmidt_mem_gsSpan (f : ℕ → E) (k : ℕ) :
    f k - gramSchmidt ℂ f k ∈ gsSpan f k := by
  rw [gramSchmidt_def]
  have hS : f k - (f k - ∑ i ∈ Finset.Iio k,
      (ℂ ∙ gramSchmidt ℂ f i).starProjection (f k))
      = ∑ i ∈ Finset.Iio k, (ℂ ∙ gramSchmidt ℂ f i).starProjection (f k) := by
    abel
  rw [hS]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hle : ℂ ∙ gramSchmidt ℂ f i ≤ gsSpan f k := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨i, Set.mem_Iio.mpr (Finset.mem_Iio.mp hi), rfl⟩
  exact hle (Submodule.starProjection_apply_mem _ _)

/-- **The Gram–Schmidt vector is orthogonal to the earlier spans.** -/
theorem gramSchmidt_mem_orthogonal_gsSpan (f : ℕ → E) (k : ℕ) :
    gramSchmidt ℂ f k ∈ (gsSpan f k)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro w hw
  refine Submodule.span_induction (p := fun w _ => ⟪gramSchmidt ℂ f k, w⟫_ℂ = 0) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨j, hj, rfl⟩
    have hj' : j < k := by simpa using hj
    have hne : k ≠ j := by omega
    exact gramSchmidt_pairwise_orthogonal ℂ f hne
  · simp
  · intro x y _ _ hx hy
    rw [inner_add_right, hx, hy, add_zero]
  · intro c x _ hx
    rw [inner_smul_right, hx, mul_zero]

/-! ## Uniqueness of the orthogonal component -/

/-- **The orthogonal component is unique.**  A vector whose difference from `f k` lies in the
earlier span and which is orthogonal to it is the Gram–Schmidt vector. -/
theorem eq_of_decomp_orthogonal {f : ℕ → E} {k : ℕ} {u : E}
    (hu : u - f k ∈ gsSpan f k) (hu' : u ∈ (gsSpan f k)ᗮ) :
    u = gramSchmidt ℂ f k := by
  have hgs := gramSchmidt_mem_orthogonal_gsSpan f k
  have hsub : u - gramSchmidt ℂ f k ∈ gsSpan f k := by
    have : u - gramSchmidt ℂ f k = (u - f k) + (f k - gramSchmidt ℂ f k) := by abel
    rw [this]
    exact Submodule.add_mem _ hu (sub_gramSchmidt_mem_gsSpan f k)
  have horth : u - gramSchmidt ℂ f k ∈ (gsSpan f k)ᗮ := by
    rw [Submodule.mem_orthogonal'] at hu' hgs ⊢
    intro w hw
    rw [inner_sub_left, hu' w hw, hgs w hw, sub_zero]
  have hzero : ⟪u - gramSchmidt ℂ f k, u - gramSchmidt ℂ f k⟫_ℂ = 0 := horth _ hsub
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-- **The Gram–Schmidt vector is the orthogonal component of the family vector**: if
`f k − c • g` lies in the earlier span and `g` is orthogonal to that span, then
`gramSchmidt f k = c • g`.  This is the lemma that carries a “monomial minus its lower-degree
projection” decomposition over to any vector realising the orthogonal direction. -/
theorem gramSchmidt_eq_smul_of_decomp {f : ℕ → E} {k : ℕ} {g : E} {c : ℂ}
    (hg : g ∈ (gsSpan f k)ᗮ) (hdec : f k - c • g ∈ gsSpan f k) :
    gramSchmidt ℂ f k = c • g := by
  refine (eq_of_decomp_orthogonal ?_ ?_).symm
  · have : c • g - f k = -(f k - c • g) := by abel
    rw [this]
    exact Submodule.neg_mem _ hdec
  · rw [Submodule.mem_orthogonal'] at hg ⊢
    intro w hw
    rw [inner_smul_left, hg w hw, mul_zero]

/-! ## The core basis -/

/-- `coreBasis e k` is the normalized monomial `x^{e k} e^{-‖x‖²/4}` minus its projection onto the
earlier Gram–Schmidt spans. -/
theorem coreBasis_eq_sub_projection (e : ℕ ≃ (Fin d →₀ ℕ)) (k : ℕ) :
    coreBasis e k
      = ((‖gramSchmidt ℂ (coreFamily e) k‖ : ℝ) : ℂ)⁻¹ •
        (coreFamily e k - ∑ i ∈ Finset.Iio k,
          (ℂ ∙ gramSchmidt ℂ (coreFamily e) i).starProjection (coreFamily e k)) := by
  rw [coreBasis, HilbertBasis.coe_mk, gramSchmidtNormed, gramSchmidt_def]
  rfl

/-- The monomial family vector is the monomial Gauss function. -/
theorem coreFamily_apply (e : ℕ ≃ (Fin d →₀ ℕ)) (k : ℕ) :
    coreFamily e k = pgLp (MvPolynomial.monomial (e k) (1 : ℂ)) := rfl

/-- **The Hermite function is orthogonal to the earlier monomial span** when every earlier
monomial is smaller in some coordinate — the degree-compatibility hypothesis of the bridge, in
the form the vanishing lemma consumes. -/
theorem hermiteMvLp_mem_orthogonal_gsSpan (e : ℕ ≃ (Fin d →₀ ℕ)) {k : ℕ}
    (h : ∀ j < k, ∃ i, e j i < e k i) :
    hermiteMvLp (e k) ∈ (gsSpan (coreFamily e) k)ᗮ := by
  rw [gsSpan_eq_span_Iio, Submodule.mem_orthogonal']
  intro w hw
  refine Submodule.span_induction
    (p := fun w _ => ⟪hermiteMvLp (e k), w⟫_ℂ = 0) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨j, hj, rfl⟩
    rw [coreFamily_apply]
    have hzero := inner_monomial_hermiteMvLp_eq_zero (e j) (e k) (h j (Set.mem_Iio.mp hj))
    rw [← inner_conj_symm, hzero, map_zero]
  · simp
  · intro x y _ _ hx hy
    rw [inner_add_right, hx, hy, add_zero]
  · intro c x _ hx
    rw [inner_smul_right, hx, mul_zero]

end

end BookProof.FockGramSchmidtProjection
