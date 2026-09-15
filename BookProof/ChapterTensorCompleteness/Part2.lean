import Mathlib
import BookProof.ChapterSolovayHilbertTensor
import BookProof.ChapterTensorCompleteness.Part1

/-!
# Pure tensors are total in `L²(μ ⊗ ν)`

`ChapterSolovayHilbertTensor` builds the elementary tensors `f ⊗ g` inside
`L²(μ ⊗ ν)` and proves the defining identity `⟪f₁⊗g₁, f₂⊗g₂⟫ = ⟪f₁,f₂⟫·⟪g₁,g₂⟫`.
What it explicitly did **not** claim is the *completeness* half — that these
elementary tensors exhaust the space.  This module proves it for finite
measures:

  `tensorSpan_eq_top` : the closed linear span of `{ f ⊗ g }` is all of
  `L²(μ ⊗ ν)`,

equivalently `pureTensors_dense` (the span is dense) and
`exists_tensor_approx` (every `L²` function of two variables is an `L²`-limit of
finite sums of products of one-variable functions — the separation of variables
statement).  Together with `inner_tensorLp` this says `L²(μ ⊗ ν)` *is* the
Hilbert tensor product of `L²(μ)` and `L²(ν)`, without a Hilbert tensor product
having to be available in the library.

The proof is the classical π–λ argument:

* `indicatorConstLp_prod` — the indicator of a measurable rectangle `s ×ˢ t` is
  the pure tensor `1_s ⊗ 1_t`;
* `indicator_mem_tensorSpan` — the family of measurable `E ⊆ α × β` whose
  indicator lies in the closed span contains the rectangles and is closed under
  complements and countable disjoint unions, hence is everything
  (`MeasurableSpace.induction_on_inter` against `generateFrom_prod`);
* `tensorSpan_eq_top` — indicators generate `L²` (`Lp.induction`), and the span
  is closed.

A final section draws the practical corollary.  `tensorOf u v` is the pure tensor
of two `L²` *elements*; `inner_tensorOf` and `norm_tensorOf` are its inner-product
and norm identities, `tensorOf_add_left`/`tensorOf_smul_left` (and the right-hand
versions) its bilinearity, `tensorRight`/`tensorLeft` the associated continuous
linear maps.  `orthonormal_tensorOf` says the products of two orthonormal families
are orthonormal, and `tensorFamily_span_eq_top` that the products of two *total*
families are total: the products of two orthonormal bases form an orthonormal
basis of `L²(μ ⊗ ν)`.  `tensorHilbertBasis` packages the two into the `HilbertBasis`
object itself, with `tensorHilbertBasis_repr_apply` (its coefficients are the
two-variable Fourier coefficients), `hasSum_tensorHilbertBasis` (the two-variable
expansion) and `hasSum_sq_norm_inner_tensorHilbertBasis` (Parseval in product
form).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open MeasureTheory ENNReal Complex Filter Topology

namespace BookProof.ChapterTensorCompleteness

open BookProof.ChapterSolovayHilbertTensor

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
/-! ## Product orthonormal families

With completeness in hand the tensor identification takes its usual concrete
form: the products of two orthonormal families form an orthonormal family, and if
both families are total then so is the product family.  This is the statement one
uses in practice (a product basis of a two-particle state space). -/

section ProductBasis

/-- The pure tensor of two `L²` *elements* (rather than of two functions). -/
def tensorOf (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  tensorLp (Lp.memLp u) (Lp.memLp v)

theorem tensorOf_mem_pureTensors (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensorOf u v ∈ pureTensors μ ν :=
  ⟨_, _, Lp.memLp u, Lp.memLp v, rfl⟩

/-- The inner product of two element-level pure tensors multiplies. -/
theorem inner_tensorOf (u₁ u₂ : Lp ℂ 2 μ) (v₁ v₂ : Lp ℂ 2 ν) :
    (inner ℂ (tensorOf u₁ v₁) (tensorOf u₂ v₂) : ℂ)
      = (inner ℂ u₁ u₂ : ℂ) * (inner ℂ v₁ v₂ : ℂ) := by
  rw [tensorOf, tensorOf, inner_tensorLp, Lp.toLp_coeFn, Lp.toLp_coeFn, Lp.toLp_coeFn,
    Lp.toLp_coeFn]

theorem norm_tensorOf (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    ‖tensorOf u v‖ = ‖u‖ * ‖v‖ := by
  have h := inner_tensorOf u u v v
  simp only [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h
  have h'' : (‖tensorOf u v‖ : ℝ) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by exact_mod_cast h
  have hnn : (0 : ℝ) ≤ ‖u‖ * ‖v‖ := by positivity
  nlinarith [norm_nonneg (tensorOf u v), hnn, h'']

omit [IsFiniteMeasure μ] in
theorem tensorOf_add_left (u₁ u₂ : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensorOf (u₁ + u₂) v = tensorOf u₁ v + tensorOf u₂ v := by
  refine Lp.ext ?_
  filter_upwards [(tensorMemLp (Lp.memLp (u₁ + u₂)) (Lp.memLp v)).coeFn_toLp,
    (tensorMemLp (Lp.memLp u₁) (Lp.memLp v)).coeFn_toLp,
    (tensorMemLp (Lp.memLp u₂) (Lp.memLp v)).coeFn_toLp,
    Lp.coeFn_add (tensorOf u₁ v) (tensorOf u₂ v),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_add u₁ u₂)] with z h1 h2 h3 h4 h5
  simp only [tensorOf, tensorLp, Function.comp_apply] at *
  rw [h1, h4]
  simp only [Pi.add_apply]
  rw [h2, h3, h5]
  simp only [Pi.add_apply]
  ring

omit [IsFiniteMeasure μ] in
theorem tensorOf_smul_left (c : ℂ) (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensorOf (c • u) v = c • tensorOf u v := by
  refine Lp.ext ?_
  filter_upwards [(tensorMemLp (Lp.memLp (c • u)) (Lp.memLp v)).coeFn_toLp,
    (tensorMemLp (Lp.memLp u) (Lp.memLp v)).coeFn_toLp,
    Lp.coeFn_smul c (tensorOf u v),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_smul c u)] with z h1 h2 h3 h4
  simp only [tensorOf, tensorLp, Function.comp_apply] at *
  rw [h1, h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2, h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [IsFiniteMeasure μ] in
theorem tensorOf_add_right (u : Lp ℂ 2 μ) (v₁ v₂ : Lp ℂ 2 ν) :
    tensorOf u (v₁ + v₂) = tensorOf u v₁ + tensorOf u v₂ := by
  refine Lp.ext ?_
  filter_upwards [(tensorMemLp (Lp.memLp u) (Lp.memLp (v₁ + v₂))).coeFn_toLp,
    (tensorMemLp (Lp.memLp u) (Lp.memLp v₁)).coeFn_toLp,
    (tensorMemLp (Lp.memLp u) (Lp.memLp v₂)).coeFn_toLp,
    Lp.coeFn_add (tensorOf u v₁) (tensorOf u v₂),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_add v₁ v₂)] with z h1 h2 h3 h4 h5
  simp only [tensorOf, tensorLp, Function.comp_apply] at *
  rw [h1, h4]
  simp only [Pi.add_apply]
  rw [h2, h3, h5]
  simp only [Pi.add_apply]
  ring

omit [IsFiniteMeasure μ] in
theorem tensorOf_smul_right (c : ℂ) (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensorOf u (c • v) = c • tensorOf u v := by
  refine Lp.ext ?_
  filter_upwards [(tensorMemLp (Lp.memLp u) (Lp.memLp (c • v))).coeFn_toLp,
    (tensorMemLp (Lp.memLp u) (Lp.memLp v)).coeFn_toLp,
    Lp.coeFn_smul c (tensorOf u v),
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_smul c v)] with z h1 h2 h3 h4
  simp only [tensorOf, tensorLp, Function.comp_apply] at *
  rw [h1, h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2, h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Products of orthonormal families are orthonormal.** -/
theorem orthonormal_tensorOf {ι κ : Type*} {e : ι → Lp ℂ 2 μ} {f : κ → Lp ℂ 2 ν}
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) :
    Orthonormal ℂ fun p : ι × κ => tensorOf (e p.1) (f p.2) := by
  classical
  rw [orthonormal_iff_ite] at he hf ⊢
  intro p q
  rw [inner_tensorOf, he, hf]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [Prod.ext_iff, h1, h2]

/-- Tensoring with a fixed first factor, as a continuous linear map. -/
def tensorRight (u : Lp ℂ 2 μ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := fun v => tensorOf u v
      map_add' := tensorOf_add_right u
      map_smul' := fun c v => tensorOf_smul_right c u v } ‖u‖
    (fun v => le_of_eq (norm_tensorOf u v))

@[simp] theorem tensorRight_apply (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensorRight u v = tensorOf u v := rfl

/-- Tensoring with a fixed second factor, as a continuous linear map. -/
def tensorLeft (v : Lp ℂ 2 ν) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    { toFun := fun u => tensorOf u v
      map_add' := fun u₁ u₂ => tensorOf_add_left u₁ u₂ v
      map_smul' := fun c u => tensorOf_smul_left c u v } ‖v‖
    (fun u => le_of_eq ((norm_tensorOf u v).trans (mul_comm _ _)))

@[simp] theorem tensorLeft_apply (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensorLeft v u = tensorOf u v := rfl

omit [IsFiniteMeasure μ] in
/-- Every pure tensor is an element-level pure tensor. -/
theorem tensorLp_eq_tensorOf {f : α → ℂ} {g : β → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    tensorLp hf hg = tensorOf (hf.toLp f) (hg.toLp g) := by
  refine Lp.ext ?_
  filter_upwards [(tensorMemLp hf hg).coeFn_toLp,
    (tensorMemLp (Lp.memLp (hf.toLp f)) (Lp.memLp (hg.toLp g))).coeFn_toLp,
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hf.coeFn_toLp,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hg.coeFn_toLp] with z h1 h2 h3 h4
  simp only [tensorOf, tensorLp, Function.comp_apply] at *
  rw [h1, h2, h3, h4]

/-- **Totality of the product family.**  If two families are total in `L²(μ)` and
`L²(ν)` respectively, then their products are total in `L²(μ ⊗ ν)`.  Combined with
`orthonormal_tensorOf`, the products of two orthonormal bases form an orthonormal
basis of `L²(μ ⊗ ν)`. -/
theorem tensorFamily_span_eq_top {ι κ : Type*} {e : ι → Lp ℂ 2 μ} {f : κ → Lp ℂ 2 ν}
    (he : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤)
    (hf : (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range fun p : ι × κ => tensorOf (e p.1) (f p.2))).topologicalClosure
      = ⊤ := by
  set S : Submodule ℂ (Lp ℂ 2 (μ.prod ν)) :=
    (Submodule.span ℂ (Set.range fun p : ι × κ => tensorOf (e p.1) (f p.2))).topologicalClosure
    with hS
  have hSclosed : IsClosed (S : Set (Lp ℂ 2 (μ.prod ν))) :=
    Submodule.isClosed_topologicalClosure _
  -- first slot fixed to a basis vector
  have hstep1 : ∀ (i : ι) (v : Lp ℂ 2 ν), tensorOf (e i) v ∈ S := by
    intro i v
    have hsub : Submodule.span ℂ (Set.range f)
        ≤ S.comap (tensorRight (μ := μ) (ν := ν) (e i)).toLinearMap := by
      rw [Submodule.span_le]
      rintro w ⟨j, rfl⟩
      have hmemS : tensorOf (e i) (f j) ∈ S :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i, j), rfl⟩)
      exact hmemS
    have hclosed : IsClosed
        ((S.comap (tensorRight (μ := μ) (ν := ν) (e i)).toLinearMap : Submodule ℂ _) :
          Set (Lp ℂ 2 ν)) :=
      hSclosed.preimage (tensorRight (e i)).continuous
    have := Submodule.topologicalClosure_minimal _ hsub hclosed
    rw [hf] at this
    exact this (Submodule.mem_top)
  -- now the first slot is arbitrary
  have hstep2 : ∀ (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν), tensorOf u v ∈ S := by
    intro u v
    have hsub : Submodule.span ℂ (Set.range e)
        ≤ S.comap (tensorLeft (μ := μ) (ν := ν) v).toLinearMap := by
      rw [Submodule.span_le]
      rintro w ⟨i, rfl⟩
      exact hstep1 i v
    have hclosed : IsClosed
        ((S.comap (tensorLeft (μ := μ) (ν := ν) v).toLinearMap : Submodule ℂ _) :
          Set (Lp ℂ 2 μ)) :=
      hSclosed.preimage (tensorLeft v).continuous
    have := Submodule.topologicalClosure_minimal _ hsub hclosed
    rw [he] at this
    exact this (Submodule.mem_top)
  -- hence `S` contains all pure tensors, so it contains their closed span, which is everything
  have hpure : pureTensors μ ν ⊆ (S : Set (Lp ℂ 2 (μ.prod ν))) := by
    rintro w ⟨g, h, hg, hh, rfl⟩
    rw [tensorLp_eq_tensorOf]
    exact hstep2 _ _
  have hspan : tensorSpan μ ν ≤ S :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hpure) hSclosed
  rw [tensorSpan_eq_top] at hspan
  exact eq_top_iff.mpr hspan

end ProductBasis

section ProductHilbertBasis

variable {ι κ : Type*}

/-- **The product of two Hilbert bases is a Hilbert basis.**  If `b` is a Hilbert
basis of `L²(μ)` and `c` one of `L²(ν)`, then the pure tensors `b i ⊗ c j`, indexed
by `ι × κ`, form a Hilbert basis of `L²(μ ⊗ ν)`.  This is the object form of
`orthonormal_tensorOf` together with `tensorFamily_span_eq_top`. -/
def tensorHilbertBasis (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    HilbertBasis (ι × κ) ℂ (Lp ℂ 2 (μ.prod ν)) :=
  HilbertBasis.mk (orthonormal_tensorOf b.orthonormal c.orthonormal)
    (by
      rw [tensorFamily_span_eq_top b.dense_span c.dense_span])

@[simp] theorem coe_tensorHilbertBasis
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    ⇑(tensorHilbertBasis b c) = fun p : ι × κ => tensorOf (b p.1) (c p.2) :=
  HilbertBasis.coe_mk _ _

/-- The coefficients of the product basis are the two-variable Fourier coefficients
`⟪bᵢ ⊗ cⱼ, F⟫`. -/
theorem tensorHilbertBasis_repr_apply
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (F : Lp ℂ 2 (μ.prod ν)) (p : ι × κ) :
    (tensorHilbertBasis b c).repr F p = (inner ℂ (tensorOf (b p.1) (c p.2)) F : ℂ) := by
  rw [HilbertBasis.repr_apply_apply, coe_tensorHilbertBasis]

/-- **Two-variable Fourier expansion.**  Every `F ∈ L²(μ ⊗ ν)` is the unconditional
sum of its product-basis components. -/
theorem hasSum_tensorHilbertBasis
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (F : Lp ℂ 2 (μ.prod ν)) :
    HasSum (fun p : ι × κ =>
        (inner ℂ (tensorOf (b p.1) (c p.2)) F : ℂ) • tensorOf (b p.1) (c p.2)) F := by
  have h := (tensorHilbertBasis b c).hasSum_repr F
  simpa only [tensorHilbertBasis_repr_apply, coe_tensorHilbertBasis] using h

/-- **Parseval for the product basis.**  The squared `L²` norm of a function of two
variables is the sum of the squared moduli of its two-variable Fourier
coefficients. -/
theorem hasSum_sq_norm_inner_tensorHilbertBasis
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (c : HilbertBasis κ ℂ (Lp ℂ 2 ν))
    (F : Lp ℂ 2 (μ.prod ν)) :
    HasSum (fun p : ι × κ => ‖(inner ℂ (tensorOf (b p.1) (c p.2)) F : ℂ)‖ ^ 2) (‖F‖ ^ 2) := by
  have h := (tensorHilbertBasis b c).hasSum_inner_mul_inner F F
  rw [← Complex.hasSum_ofReal]
  have hcast : ∀ p : ι × κ,
      ((‖(inner ℂ (tensorOf (b p.1) (c p.2)) F : ℂ)‖ ^ 2 : ℝ) : ℂ)
        = (inner ℂ F ((tensorHilbertBasis b c) p) : ℂ)
            * (inner ℂ ((tensorHilbertBasis b c) p) F : ℂ) := by
    intro p
    rw [coe_tensorHilbertBasis, ← inner_conj_symm (𝕜 := ℂ) (tensorOf (b p.1) (c p.2)) F,
      RCLike.norm_conj]
    push_cast
    exact (RCLike.mul_conj (K := ℂ) (inner ℂ F (tensorOf (b p.1) (c p.2)))).symm
  have h2 : ((‖F‖ ^ 2 : ℝ) : ℂ) = (inner ℂ F F : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  rw [h2]
  simpa only [hcast] using h

end ProductHilbertBasis

end BookProof.ChapterTensorCompleteness

end
