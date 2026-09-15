import Mathlib
import BookProof.ChapterSolovayHilbertTensor

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

/-- The set of pure tensors `f ⊗ g` inside `L²(μ ⊗ ν)`. -/
def pureTensors (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Set (Lp ℂ 2 (μ.prod ν)) :=
  {v | ∃ (f : α → ℂ) (g : β → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 ν), v = tensorLp hf hg}

/-- The closed linear span of the pure tensors. -/
def tensorSpan (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Submodule ℂ (Lp ℂ 2 (μ.prod ν)) :=
  (Submodule.span ℂ (pureTensors μ ν)).topologicalClosure

theorem isClosed_tensorSpan : IsClosed (tensorSpan μ ν : Set (Lp ℂ 2 (μ.prod ν))) :=
  Submodule.isClosed_topologicalClosure _

theorem pureTensor_mem_tensorSpan {f : α → ℂ} {g : β → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) : tensorLp hf hg ∈ tensorSpan μ ν :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, g, hf, hg, rfl⟩)

/-- The indicator of a measurable rectangle is the pure tensor of the two
indicators. -/
theorem indicatorConstLp_prod {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    indicatorConstLp (μ := μ.prod ν) 2 (hs.prod ht) (measure_ne_top _ _) (1 : ℂ)
      = tensorLp (μ := μ) (ν := ν) ((memLp_const (1 : ℂ)).indicator hs)
          ((memLp_const (1 : ℂ)).indicator ht) := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ.prod ν)
      (hs := hs.prod ht) (hμs := measure_ne_top _ _) (c := (1 : ℂ)),
    (tensorMemLp (μ := μ) (ν := ν) ((memLp_const (1 : ℂ)).indicator hs)
      ((memLp_const (1 : ℂ)).indicator ht)).coeFn_toLp] with z h1 h2
  simp only [tensorLp] at h2 ⊢
  rw [h1, h2]
  by_cases hz1 : z.1 ∈ s <;> by_cases hz2 : z.2 ∈ t <;>
    simp [hz1, hz2, Set.mem_prod]

/-- The whole space is a rectangle, so its indicator is in the span. -/
theorem indicatorConstLp_univ_mem :
    indicatorConstLp (μ := μ.prod ν) 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℂ)
      ∈ tensorSpan μ ν := by
  have h : (Set.univ : Set (α × β)) = (Set.univ : Set α) ×ˢ (Set.univ : Set β) := by
    ext z; simp
  have := indicatorConstLp_prod (μ := μ) (ν := ν) MeasurableSet.univ MeasurableSet.univ
  have hmem := pureTensor_mem_tensorSpan (μ := μ) (ν := ν)
    ((memLp_const (1 : ℂ)).indicator (MeasurableSet.univ (α := α)))
    ((memLp_const (1 : ℂ)).indicator (MeasurableSet.univ (α := β)))
  rw [← this] at hmem
  convert hmem using 2

/-- Indicators subtract: for `t ⊆ s` the difference of the two indicators is the
indicator of the difference. -/
theorem indicatorConstLp_diff {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ} [IsFiniteMeasure ρ]
    {s t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s) :
    indicatorConstLp (μ := ρ) 2 hs (measure_ne_top _ _) (1 : ℂ)
        - indicatorConstLp (μ := ρ) 2 ht (measure_ne_top _ _) (1 : ℂ)
      = indicatorConstLp (μ := ρ) 2 (hs.diff ht) (measure_ne_top _ _) (1 : ℂ) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (indicatorConstLp (μ := ρ) 2 hs (measure_ne_top _ _) (1 : ℂ))
      (indicatorConstLp (μ := ρ) 2 ht (measure_ne_top _ _) (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := ρ) (hs := hs)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := ρ) (hs := ht)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := ρ) (hs := hs.diff ht)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ))] with x h0 h1 h2 h3
  rw [h0]
  simp only [Pi.sub_apply]
  rw [h1, h2, h3]
  rcases em (x ∈ t) with hxt | hxt
  · simp [hts hxt, hxt, Set.mem_diff]
  · by_cases hxs : x ∈ s <;> simp [hxs, hxt, Set.mem_diff]

/-- The `L²` norm of the difference of two nested indicators. -/
theorem norm_indicatorConstLp_diff {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ}
    [IsFiniteMeasure ρ] {s t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hts : t ⊆ s) :
    ‖indicatorConstLp (μ := ρ) 2 hs (measure_ne_top _ _) (1 : ℂ)
        - indicatorConstLp (μ := ρ) 2 ht (measure_ne_top _ _) (1 : ℂ)‖
      = Real.sqrt (ρ.real (s \ t)) := by
  rw [indicatorConstLp_diff hs ht hts,
    norm_indicatorConstLp (by norm_num) (by norm_num), Real.sqrt_eq_rpow]
  simp

/-- Indicators add over a disjoint union. -/
theorem indicatorConstLp_union_disjoint {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ}
    [IsFiniteMeasure ρ] {s t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    indicatorConstLp (μ := ρ) 2 (hs.union ht) (measure_ne_top _ _) (1 : ℂ)
      = indicatorConstLp (μ := ρ) 2 hs (measure_ne_top _ _) (1 : ℂ)
        + indicatorConstLp (μ := ρ) 2 ht (measure_ne_top _ _) (1 : ℂ) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (indicatorConstLp (μ := ρ) 2 hs (measure_ne_top _ _) (1 : ℂ))
      (indicatorConstLp (μ := ρ) 2 ht (measure_ne_top _ _) (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := ρ) (hs := hs)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := ρ) (hs := ht)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := ρ) (hs := hs.union ht)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ))] with x h0 h1 h2 h3
  rw [h3, h0]
  simp only [Pi.add_apply]
  rw [h1, h2]
  rcases em (x ∈ s) with hxs | hxs
  · have hxt : x ∉ t := Set.disjoint_left.mp hst hxs
    simp [hxs, hxt, Set.mem_union]
  · by_cases hxt : x ∈ t <;> simp [hxs, hxt, Set.mem_union]

/-- Indicators only depend on the set, not on the measurability proof. -/
theorem indicatorConstLp_congr_set {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ}
    [IsFiniteMeasure ρ] {s t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : s = t) :
    indicatorConstLp (μ := ρ) 2 hs (measure_ne_top _ _) (1 : ℂ)
      = indicatorConstLp (μ := ρ) 2 ht (measure_ne_top _ _) (1 : ℂ) := by
  subst h; rfl

/-- The indicator of the empty set is `0`. -/
theorem indicatorConstLp_empty_eq_zero {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ}
    [IsFiniteMeasure ρ] (h : MeasurableSet (∅ : Set γ)) :
    indicatorConstLp (μ := ρ) 2 h (measure_ne_top _ _) (1 : ℂ) = 0 := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := ρ) (hs := h)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ)), Lp.coeFn_zero ℂ 2 ρ] with x h1 h2
  rw [h1, h2]
  simp

/-- Partial unions of a disjoint measurable family stay in the span. -/
theorem partialUnion_indicator_mem {f : ℕ → Set (α × β)}
    (hdisj : Pairwise (Function.onFun Disjoint f)) (hfm : ∀ i, MeasurableSet (f i))
    (hmem : ∀ i, indicatorConstLp (μ := μ.prod ν) 2 (hfm i) (measure_ne_top _ _) (1 : ℂ)
      ∈ tensorSpan μ ν) :
    ∀ (N : ℕ) (hN : MeasurableSet (⋃ i ∈ Finset.range N, f i)),
      indicatorConstLp (μ := μ.prod ν) 2 hN (measure_ne_top _ _) (1 : ℂ) ∈ tensorSpan μ ν := by
  intro N
  induction N with
  | zero =>
    intro hN
    rw [indicatorConstLp_congr_set hN MeasurableSet.empty (by simp),
      indicatorConstLp_empty_eq_zero]
    exact Submodule.zero_mem _
  | succ N ih =>
    intro hN
    have hprev : MeasurableSet (⋃ i ∈ Finset.range N, f i) :=
      Finset.measurableSet_biUnion _ fun i _ => hfm i
    have hsplit : (⋃ i ∈ Finset.range (N + 1), f i) = (⋃ i ∈ Finset.range N, f i) ∪ f N := by
      ext z
      simp only [Finset.mem_range, Set.mem_iUnion, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨i, hi, hz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact Or.inl ⟨i, hi', hz⟩
        · exact Or.inr hz
      · rintro (⟨i, hi, hz⟩ | hz)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hz⟩
        · exact ⟨N, Nat.lt_succ_self N, hz⟩
    have hdisj' : Disjoint (⋃ i ∈ Finset.range N, f i) (f N) := by
      rw [Set.disjoint_left]
      rintro z hz hzN
      simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hz
      obtain ⟨i, hi, hzi⟩ := hz
      exact (Set.disjoint_left.mp (hdisj (Nat.ne_of_lt hi)) hzi) hzN
    rw [indicatorConstLp_congr_set hN (hprev.union (hfm N)) hsplit,
      indicatorConstLp_union_disjoint hprev (hfm N) hdisj']
    exact Submodule.add_mem _ (ih hprev) (hmem N)

/-- The countable disjoint union case. -/
theorem iUnion_indicator_mem {f : ℕ → Set (α × β)}
    (hdisj : Pairwise (Function.onFun Disjoint f)) (hfm : ∀ i, MeasurableSet (f i))
    (hmem : ∀ i, indicatorConstLp (μ := μ.prod ν) 2 (hfm i) (measure_ne_top _ _) (1 : ℂ)
      ∈ tensorSpan μ ν) :
    indicatorConstLp (μ := μ.prod ν) 2 (MeasurableSet.iUnion hfm) (measure_ne_top _ _) (1 : ℂ)
      ∈ tensorSpan μ ν := by
  set ρ : Measure (α × β) := μ.prod ν with hρ
  set E : Set (α × β) := ⋃ i, f i with hE
  have hEm : MeasurableSet E := MeasurableSet.iUnion hfm
  set F : ℕ → Set (α × β) := fun N => ⋃ i ∈ Finset.range N, f i with hF
  have hFm : ∀ N, MeasurableSet (F N) := fun N =>
    Finset.measurableSet_biUnion _ fun i _ => hfm i
  have hFsub : ∀ N, F N ⊆ E := by
    intro N z hz
    simp only [hF, Set.mem_iUnion, Finset.mem_range, exists_prop] at hz
    obtain ⟨i, _, hzi⟩ := hz
    exact Set.mem_iUnion.mpr ⟨i, hzi⟩
  have hFmono : Monotone F := by
    intro m n hmn z hz
    simp only [hF, Set.mem_iUnion, Finset.mem_range, exists_prop] at hz ⊢
    obtain ⟨i, hi, hzi⟩ := hz
    exact ⟨i, lt_of_lt_of_le hi hmn, hzi⟩
  have hFunion : ⋃ N, F N = E := by
    apply Set.Subset.antisymm (Set.iUnion_subset hFsub)
    intro z hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨i + 1, by
      simp only [hF, Set.mem_iUnion, Finset.mem_range, exists_prop]
      exact ⟨i, Nat.lt_succ_self i, hzi⟩⟩
  -- the measures of the partial unions converge to the measure of the union
  have hmeas_tendsto : Tendsto (fun N => ρ (F N)) atTop (𝓝 (ρ E)) := by
    have := tendsto_measure_iUnion_atTop (μ := ρ) hFmono
    rwa [hFunion] at this
  have hreal_tendsto : Tendsto (fun N => ρ.real (F N)) atTop (𝓝 (ρ.real E)) := by
    simp only [measureReal_def]
    exact (ENNReal.tendsto_toReal (measure_ne_top ρ E)).comp hmeas_tendsto
  have hdiff_tendsto : Tendsto (fun N => ρ.real (E \ F N)) atTop (𝓝 0) := by
    have hEq : ∀ N, ρ.real (E \ F N) = ρ.real E - ρ.real (F N) := fun N =>
      measureReal_diff (hFsub N) (hFm N) (measure_ne_top ρ E)
    simp only [hEq]
    have := (tendsto_const_nhds (x := ρ.real E) (f := atTop (α := ℕ))).sub hreal_tendsto
    simpa using this
  -- hence the indicators converge in `L²`
  have hnorm : Tendsto (fun N => ‖indicatorConstLp (μ := ρ) 2 hEm (measure_ne_top _ _) (1 : ℂ)
      - indicatorConstLp (μ := ρ) 2 (hFm N) (measure_ne_top _ _) (1 : ℂ)‖) atTop (𝓝 0) := by
    have hrw : ∀ N, ‖indicatorConstLp (μ := ρ) 2 hEm (measure_ne_top _ _) (1 : ℂ)
        - indicatorConstLp (μ := ρ) 2 (hFm N) (measure_ne_top _ _) (1 : ℂ)‖
        = Real.sqrt (ρ.real (E \ F N)) := fun N =>
      norm_indicatorConstLp_diff hEm (hFm N) (hFsub N)
    simp only [hrw]
    have := (Real.continuous_sqrt.tendsto 0).comp hdiff_tendsto
    simpa using this
  have hconv : Tendsto (fun N => indicatorConstLp (μ := ρ) 2 (hFm N) (measure_ne_top _ _) (1 : ℂ))
      atTop (𝓝 (indicatorConstLp (μ := ρ) 2 hEm (measure_ne_top _ _) (1 : ℂ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [norm_sub_rev] using hnorm
  have hmemF : ∀ N, indicatorConstLp (μ := ρ) 2 (hFm N) (measure_ne_top _ _) (1 : ℂ)
      ∈ tensorSpan μ ν := fun N => partialUnion_indicator_mem hdisj hfm hmem N (hFm N)
  exact isClosed_tensorSpan.mem_of_tendsto hconv (Filter.Eventually.of_forall hmemF)

/-- **The π–λ step.**  The indicator of every measurable subset of `α × β` lies
in the closed span of the pure tensors. -/
theorem indicator_mem_tensorSpan {E : Set (α × β)} (hE : MeasurableSet E) :
    indicatorConstLp (μ := μ.prod ν) 2 hE (measure_ne_top _ _) (1 : ℂ) ∈ tensorSpan μ ν := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E hE => indicatorConstLp (μ := μ.prod ν) 2 hE (measure_ne_top _ _) (1 : ℂ)
      ∈ tensorSpan μ ν)
    (generateFrom_prod (α := α) (β := β)).symm isPiSystem_prod ?_ ?_ ?_ ?_ E hE
  · -- the empty set
    dsimp only
    have hzero : indicatorConstLp (μ := μ.prod ν) 2 MeasurableSet.empty
        (measure_ne_top _ _) (1 : ℂ) = 0 := by
      refine Lp.ext ?_
      filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ.prod ν)
          (hs := MeasurableSet.empty) (hμs := measure_ne_top _ _) (c := (1 : ℂ)),
        Lp.coeFn_zero ℂ 2 (μ.prod ν)] with z h1 h2
      rw [h1, h2]
      simp
    rw [hzero]
    exact Submodule.zero_mem _
  · -- rectangles
    dsimp only
    rintro R ⟨s, hs, t, ht, rfl⟩
    rw [indicatorConstLp_prod hs ht]
    exact pureTensor_mem_tensorSpan _ _
  · -- complements
    dsimp only
    intro F hF hmem
    have hgoal : indicatorConstLp (μ := μ.prod ν) 2 hF.compl (measure_ne_top _ _) (1 : ℂ)
        = indicatorConstLp (μ := μ.prod ν) 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℂ)
          - indicatorConstLp (μ := μ.prod ν) 2 hF (measure_ne_top _ _) (1 : ℂ) := by
      rw [indicatorConstLp_diff (ρ := μ.prod ν) MeasurableSet.univ hF (Set.subset_univ F)]
      congr 1
      exact Set.compl_eq_univ_diff F
    rw [hgoal]
    exact Submodule.sub_mem _ indicatorConstLp_univ_mem hmem
  · -- countable disjoint unions
    dsimp only
    intro f hdisj hfm hmem
    exact iUnion_indicator_mem hdisj hfm hmem

/-- **Completeness of the pure tensors.**  The closed linear span of the
elementary tensors `f ⊗ g` is the whole of `L²(μ ⊗ ν)`.  With
`ChapterSolovayHilbertTensor.inner_tensorLp` this says that `L²(μ ⊗ ν)` is the
Hilbert tensor product of `L²(μ)` and `L²(ν)`. -/
theorem tensorSpan_eq_top : tensorSpan μ ν = ⊤ := by
  refine Submodule.eq_top_iff'.mpr ?_
  refine Lp.induction (p := (2 : ℝ≥0∞)) (by norm_num)
    (motive := fun v => v ∈ tensorSpan μ ν) ?_ ?_ ?_
  · intro c s hs hμs
    have hcoe : ((Lp.simpleFunc.indicatorConst 2 hs hμs.ne c :
        Lp.simpleFunc ℂ 2 (μ.prod ν)) : Lp ℂ 2 (μ.prod ν))
        = indicatorConstLp 2 hs hμs.ne c := Lp.simpleFunc.coe_indicatorConst hs hμs.ne c
    rw [hcoe]
    have hsmul : indicatorConstLp (μ := μ.prod ν) 2 hs hμs.ne c
        = c • indicatorConstLp (μ := μ.prod ν) 2 hs (measure_ne_top _ _) (1 : ℂ) := by
      refine Lp.ext ?_
      filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ.prod ν) (hs := hs)
          (hμs := hμs.ne) (c := c),
        Lp.coeFn_smul c (indicatorConstLp (μ := μ.prod ν) 2 hs (measure_ne_top _ _) (1 : ℂ)),
        indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ.prod ν) (hs := hs)
          (hμs := measure_ne_top _ _) (c := (1 : ℂ))] with z h1 h2 h3
      rw [h1, h2, Pi.smul_apply, h3]
      by_cases hz : z ∈ s <;> simp [hz]
    rw [hsmul]
    exact Submodule.smul_mem _ _ (indicator_mem_tensorSpan hs)
  · intro g h hg hh _ hgm hhm
    exact Submodule.add_mem _ hgm hhm
  · exact isClosed_tensorSpan

/-- **Density form.**  Finite sums of products of one-variable functions are
dense in `L²(μ ⊗ ν)`. -/
theorem pureTensors_dense :
    Dense ((Submodule.span ℂ (pureTensors μ ν)) : Set (Lp ℂ 2 (μ.prod ν))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact tensorSpan_eq_top

/-- **Separation of variables.**  Every `L²` function of two variables is an
`L²`-limit of finite sums of products of one-variable functions: for every
`ε > 0` there is an element of the span of the pure tensors within `ε`. -/
theorem exists_tensor_approx (v : Lp ℂ 2 (μ.prod ν)) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ Submodule.span ℂ (pureTensors μ ν), ‖v - w‖ < ε := by
  obtain ⟨w, hw, hlt⟩ := Metric.mem_closure_iff.mp
    ((pureTensors_dense (μ := μ) (ν := ν)) v) ε hε
  exact ⟨w, hw, by rwa [← dist_eq_norm]⟩

end BookProof.ChapterTensorCompleteness

end
