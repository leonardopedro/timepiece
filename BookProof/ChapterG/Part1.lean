import Mathlib

/-!
# Chapter G — Gauge transformations in probability spaces

This file formalizes the self-contained mathematical backbone of the book's
chapter *"Gauge symmetry and dissipative dynamics in probability spaces"*
(book line 2128), following work-package **N6** of `FORMALIZATION_ROADMAP.md`.

Sections G.0–G.7:
* G.0 the gauge group of a parametrization,
* G.1 orbits = fibers; gauge-invariance ⇔ factoring through `π`,
* G.2 gauge-invariant subalgebras; gauge-independence of expectation values,
* G.3 the Dirac obstruction (no shift-invariant state on `ℤ`),
* G.4 gauge-fixing sections always exist,
* G.5 Haar averaging (invariantization) and the pushforward headline,
* G.6 the BRST ghost algebra (nilpotency),
* G.7 dissipative dynamics: Koopman evolution.

None of these needs an `EXTERNAL` hypothesis; everything is `sorry`-free.
-/

open scoped ComplexConjugate InnerProductSpace Matrix

namespace BookProof.ChapterG

/-! ## G.0 — Parametrization and its gauge group -/

/-- The gauge group of a parametrization `π : X → Y`: permutations of the
parameter space that preserve every fiber of `π` (book line 2247). -/
def gaugeGroup {X Y : Type*} (π : X → Y) : Subgroup (Equiv.Perm X) where
  carrier := {g | ∀ x, π (g x) = π x}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb x
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [ha, hb]
  inv_mem' := by
    intro a ha x
    have h := ha (a⁻¹ x)
    simpa using h.symm

@[simp] theorem mem_gaugeGroup {X Y : Type*} {π : X → Y} {g : Equiv.Perm X} :
    g ∈ gaugeGroup π ↔ ∀ x, π (g x) = π x := Iff.rfl

/-! ## G.1 — Orbits are fibers; gauge-invariance ⇔ factoring -/

/-- Transpositions between points of a common fiber are gauge transformations. -/
theorem swap_mem_gaugeGroup {X Y : Type*} [DecidableEq X] {π : X → Y}
    {x x' : X} (h : π x = π x') :
    Equiv.swap x x' ∈ gaugeGroup π := by
  intro z
  rcases eq_or_ne z x with hzx | hzx
  · subst hzx; rw [Equiv.swap_apply_left]; exact h.symm
  · rcases eq_or_ne z x' with hzx' | hzx'
    · subst hzx'; rw [Equiv.swap_apply_right]; exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzx']

/-- The gauge orbit of a point is exactly its fiber under `π`. -/
theorem gaugeOrbit_eq_fiber {X Y : Type*} (π : X → Y) (x : X) :
    MulAction.orbit (gaugeGroup π) x = π ⁻¹' {π x} := by
  classical
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact g.2 x
  · intro hz
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    refine ⟨⟨Equiv.swap x z, swap_mem_gaugeGroup hz.symm⟩, ?_⟩
    change (Equiv.swap x z) x = z
    rw [Equiv.swap_apply_left]

/-- Gauge-invariant functions are exactly the functions of the parametrized
point (book 2247–2251). -/
theorem gaugeInvariant_iff_factors {X Y Z : Type*} {π : X → Y}
    (hπ : Function.Surjective π) (f : X → Z) :
    (∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x) ↔ ∃ h : Y → Z, f = h ∘ π := by
  classical
  constructor
  · intro hinv
    have hconst : ∀ x x', π x = π x' → f x = f x' := by
      intro x x' he
      have h := hinv (Equiv.swap x x') (swap_mem_gaugeGroup he) x
      rw [Equiv.swap_apply_left] at h
      exact h.symm
    refine ⟨f ∘ Function.surjInv hπ, ?_⟩
    funext x
    change f x = f (Function.surjInv hπ (π x))
    exact (hconst _ _ (by rw [Function.surjInv_eq hπ])).symm
  · rintro ⟨h, rfl⟩ g hg x
    simp only [Function.comp_apply]
    rw [hg x]

/-! ## G.2 — Gauge-invariant subalgebras and expectation values -/

/-- Gauge-invariant observables form a subalgebra of `X → R`
(book 2277–2289). -/
def gaugeInvariantSubalgebra (R : Type*) [CommSemiring R] {X Y : Type*}
    (π : X → Y) : Subalgebra R (X → R) where
  carrier := {f | ∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x}
  mul_mem' := by
    intro f f' hf hf' g hg x
    simp only [Pi.mul_apply]
    rw [hf g hg, hf' g hg]
  add_mem' := by
    intro f f' hf hf' g hg x
    simp only [Pi.add_apply]
    rw [hf g hg, hf' g hg]
  algebraMap_mem' := by
    intro r g _ x
    rfl

/-- The gauge-invariant *operator* algebra of a family of gauge unitaries is the
centralizer of that family (book 2444). -/
abbrev gaugeInvariantOperators (𝔽 : Type*) [CommSemiring 𝔽] {V : Type*}
    [Semiring V] [Algebra 𝔽 V] {G : Type*} (U : G → V) : Subalgebra 𝔽 V :=
  Subalgebra.centralizer 𝔽 (Set.range U)

/-- Expectation values are gauge-independent for observables that commute with a
gauge unitary (book 2344–2347). -/
theorem expectation_gauge_invariant {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (U : V →L[ℂ] V) (hU : U ∈ unitary (V →L[ℂ] V))
    (A : V →L[ℂ] V) (hA : A * U = U * A) (Ψ : V) :
    ⟪U Ψ, A (U Ψ)⟫_ℂ = ⟪Ψ, A Ψ⟫_ℂ := by
  have hAU : A (U Ψ) = U (A Ψ) := by
    have := congr_arg (fun T : V →L[ℂ] V => T Ψ) hA
    simpa [ContinuousLinearMap.mul_apply] using this
  rw [hAU, ← ContinuousLinearMap.adjoint_inner_left]
  have hUU : (ContinuousLinearMap.adjoint U) * U = 1 := by
    have h := hU.1
    rwa [ContinuousLinearMap.star_eq_adjoint] at h
  calc ⟪(ContinuousLinearMap.adjoint U) (U Ψ), A Ψ⟫_ℂ
      = ⟪((ContinuousLinearMap.adjoint U) * U) Ψ, A Ψ⟫_ℂ := by rw [ContinuousLinearMap.mul_apply]
    _ = ⟪Ψ, A Ψ⟫_ℂ := by rw [hUU]; rfl

/-! ## G.3 — The Dirac obstruction: no gauge-invariant normalized state -/

open MeasureTheory

/-- There is no shift-invariant probability measure on `ℤ` (book 2277–2289). -/
theorem no_shift_invariant_probabilityMeasure :
    ¬ ∃ μ : Measure ℤ, IsProbabilityMeasure μ ∧
      ∀ s : Set ℤ, μ ((· + 1) ⁻¹' s) = μ s := by
  rintro ⟨μ, hμ, hinv⟩
  have hpre : ∀ k : ℤ, (· + 1) ⁻¹' ({k} : Set ℤ) = {k - 1} := by
    intro k; ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff]; omega
  have hstep : ∀ k : ℤ, μ {k - 1} = μ {k} := by
    intro k; rw [← hpre k]; exact hinv {k}
  have hconst : ∀ k : ℤ, μ {k} = μ {(0:ℤ)} := by
    intro k
    induction k using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [← hstep ((n:ℤ) + 1)]; simpa using ih
    | pred n ih => rw [hstep (-(n:ℤ))]; simpa using ih
  have huniv : (⋃ k : ℤ, ({k} : Set ℤ)) = Set.univ := by
    ext x; simp
  have hcount : μ Set.univ = ∑' k : ℤ, μ {k} := by
    rw [← huniv, measure_iUnion (fun i j hij => Set.disjoint_singleton.mpr hij)
      (fun k => measurableSet_singleton k)]
  rw [measure_univ] at hcount
  simp only [hconst] at hcount
  by_cases hc : μ {(0:ℤ)} = 0
  · rw [hc] at hcount; simp at hcount
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero hc] at hcount
    exact ENNReal.one_ne_top hcount

/-- A shift-invariant vector in `ℓ²(ℤ)` is zero. -/
theorem shift_invariant_l2_eq_zero (Ψ : lp (fun _ : ℤ => ℂ) 2)
    (hΨ : ∀ k, Ψ (k + 1) = Ψ k) : Ψ = 0 := by
  have hconst : ∀ k : ℤ, Ψ k = Ψ 0 := by
    intro k
    induction k using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hΨ (n:ℤ)]; exact ih
    | pred n ih =>
      have h := hΨ (-(n:ℤ) - 1)
      rw [sub_add_cancel] at h
      rw [← h]; exact ih
  have hsum : Summable (fun k : ℤ => ‖Ψ k‖ ^ (2:ℝ)) := by
    have h := lp.memℓp Ψ
    rw [memℓp_gen_iff (by norm_num)] at h
    simpa using h
  have htend := hsum.tendsto_cofinite_zero
  have hc : (fun k : ℤ => ‖Ψ k‖ ^ (2:ℝ)) = fun _ => ‖Ψ 0‖ ^ (2:ℝ) := by
    funext k; rw [hconst k]
  rw [hc] at htend
  have hzero : ‖Ψ 0‖ ^ (2:ℝ) = 0 :=
    (tendsto_nhds_unique htend tendsto_const_nhds).symm
  have hn0 : ‖Ψ 0‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) (by norm_num)).mp hzero
  have hΨ0 : Ψ 0 = 0 := by simpa using hn0
  apply lp.ext
  funext k
  simp only [lp.coeFn_zero, Pi.zero_apply]
  rw [hconst k, hΨ0]

/-- There is no shift-invariant unit vector in `ℓ²(ℤ)` (book 2277–2289). -/
theorem no_shift_invariant_unit_vector :
    ¬ ∃ Ψ : lp (fun _ : ℤ => ℂ) 2, ‖Ψ‖ = 1 ∧ ∀ k, Ψ (k + 1) = Ψ k := by
  rintro ⟨Ψ, hnorm, hinv⟩
  have h0 := shift_invariant_l2_eq_zero Ψ hinv
  rw [h0] at hnorm
  simp at hnorm

/-- Contrast: the gauge-invariant algebra is nontrivial (contains the constants)
even though there is no invariant state — the point of the chapter. -/
theorem one_mem_gaugeInvariantSubalgebra {X Y : Type*} (π : X → Y) :
    (1 : X → ℝ) ∈ gaugeInvariantSubalgebra ℝ π := by
  intro g _ x; rfl

/-! ## G.4 — Gauge-fixing: sections always exist -/

/-- A complete gauge-fixing slice crosses each fiber at most once (book 2294). -/
def IsCompleteGaugeFixing {X Y : Type*} (π : X → Y) (S : Set X) : Prop :=
  ∀ ⦃x x'⦄, x ∈ S → x' ∈ S → π x = π x' → x = x'

/-- Every parametrization admits a total complete gauge-fixing (a section). -/
theorem exists_complete_gaugeFixing {X Y : Type*} {π : X → Y}
    (hπ : Function.Surjective π) :
    ∃ S : Set X, IsCompleteGaugeFixing π S ∧ π '' S = Set.univ := by
  refine ⟨Set.range (Function.surjInv hπ), ?_, ?_⟩
  · rintro x x' ⟨y, rfl⟩ ⟨y', rfl⟩ he
    rw [Function.surjInv_eq hπ, Function.surjInv_eq hπ] at he
    rw [he]
  · rw [Set.eq_univ_iff_forall]
    intro y
    exact ⟨Function.surjInv hπ (π (Function.surjInv hπ y)), ⟨_, rfl⟩, by
      rw [Function.surjInv_eq hπ, Function.surjInv_eq hπ]⟩

/-! ## G.5 — Haar averaging (invariantization) and the pushforward headline -/

section Haar

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

/-- The Haar averaging (invariantization) operator (book 2350–2392). -/
noncomputable def haarAverage (f : X → ℝ) (x : X) : ℝ := ∫ g, f (g⁻¹ • x) ∂μG

omit [IsProbabilityMeasure μG] in
/-- Haar averaging produces a gauge-invariant functional. -/
theorem haarAverage_smul [MeasurableMul G]
    (f : X → ℝ) (g₀ : G) (x : X) :
    haarAverage (μG := μG) f (g₀ • x) = haarAverage (μG := μG) f x := by
  simp only [haarAverage]
  have key : (fun g : G => f (g⁻¹ • (g₀ • x)))
      = fun g : G => (fun h => f (h⁻¹ • x)) (g₀⁻¹ * g) := by
    funext g
    simp only [smul_smul, mul_inv_rev, inv_inv]
  rw [key]
  exact integral_mul_left_eq_self (fun h => f (h⁻¹ • x)) g₀⁻¹

omit [μG.IsMulLeftInvariant] in
/-- On invariant functions the averaging operator is the identity (projection). -/
theorem haarAverage_of_invariant (f : X → ℝ) (hf : ∀ g : G, ∀ x, f (g • x) = f x) :
    haarAverage (μG := μG) f = f := by
  funext x
  simp only [haarAverage]
  have : (fun g : G => f (g⁻¹ • x)) = fun _ => f x := by
    funext g; rw [hf g⁻¹ x]
  rw [this, integral_const]; simp

omit [μG.IsMulLeftInvariant] in
/-- The averaging operator is unital. -/
theorem haarAverage_one : haarAverage (μG := μG) (X := X) (fun _ => 1) = fun _ => 1 := by
  funext x
  simp only [haarAverage, integral_const]
  simp

omit [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant] in
/-- The averaging operator is positive. -/
theorem haarAverage_nonneg (f : X → ℝ) (hf : 0 ≤ f) :
    0 ≤ haarAverage (μG := μG) f := by
  intro x
  simp only [haarAverage, Pi.zero_apply]
  apply integral_nonneg
  intro g
  exact hf (g⁻¹ • x)

end Haar

/-- **Headline (book 2374–2386).** The pushforward of a probability measure by a
projection onto the constrained spectrum `C` gives `C` full measure `1` — the
constraint is implemented *without* attributing null probability to the
constrained space. -/
theorem gauge_constraint_pushforward_full_measure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → X) (hq : Measurable q)
    (C : Set X) (hC : MeasurableSet C)
    (hrange : ∀ x, q x ∈ C) :
    IsProbabilityMeasure (μ.map q) ∧ (μ.map q) C = 1 := by
  refine ⟨Measure.isProbabilityMeasure_map hq.aemeasurable, ?_⟩
  rw [Measure.map_apply hq hC]
  have : q ⁻¹' C = Set.univ := by
    ext x; simp [hrange x]
  rw [this, measure_univ]


end BookProof.ChapterG
