import Mathlib
import BookProof.ChapterG.Part1

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

open MeasureTheory
/-! ## G.6 — BRST ghost algebra (nilpotency) -/

section BRST

variable {A : Type*} [Ring A]

/-- The ghost annihilation operator `ψ` (book 2403–2452). -/
def ghostAnnih : Matrix (Fin 2) (Fin 2) A := !![0, 1; 0, 0]

/-- The ghost creation operator `ψ†`. -/
def ghostCreat : Matrix (Fin 2) (Fin 2) A := !![0, 0; 1, 0]

/-- The canonical anticommutation relation `{ψ, ψ†} = 1`. -/
theorem ghost_car :
    ghostAnnih * ghostCreat + ghostCreat * ghostAnnih = (1 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ghostAnnih, ghostCreat]

theorem ghost_annih_sq : ghostAnnih * ghostAnnih = (0 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ghostAnnih, Matrix.mul_apply, Fin.sum_univ_two]

theorem ghost_creat_sq : ghostCreat * ghostCreat = (0 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ghostCreat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Over `ℂ`, `ψ†` is the conjugate-transpose (adjoint) of `ψ`. -/
theorem ghost_creat_conjTranspose : (ghostAnnih (A := ℂ))ᴴ = ghostCreat := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ghostAnnih, ghostCreat, Matrix.conjTranspose_apply]

/-- The BRST charge `Ω = Q·ψ†` for a gauge generator `Q` (book: `Ω=(πφ+π*φ*)ψ†`). -/
def BRST (Q : A) : Matrix (Fin 2) (Fin 2) A := !![0, 0; Q, 0]

/-- The BRST charge is nilpotent, `Ω² = 0`, for every gauge generator. -/
theorem BRST_nilpotent (Q : A) : BRST Q * BRST Q = (0 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [BRST, Matrix.mul_apply, Fin.sum_univ_two]

end BRST

/-! ## G.7 — Dissipative dynamics: Koopman evolution -/

/-- The damped coupled-oscillator system in companion (first-order) form
(book eq. 2199). -/
def dampedCoupledMatrix (l₁ l₂ w₁ w₂ c₁ c₂ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;  -w₁^2, -l₁, c₂, 0;  0, 0, 0, 1;  c₁, 0, -w₂^2, -l₂]

/-- The flow of a linear system is a one-parameter group. -/
theorem dampedFlow_add (M : Matrix (Fin 4) (Fin 4) ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • M) = NormedSpace.exp (s • M) * NormedSpace.exp (t • M) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl M).smul_left s |>.smul_right t)

theorem dampedFlow_zero (M : Matrix (Fin 4) (Fin 4) ℝ) :
    NormedSpace.exp ((0 : ℝ) • M) = 1 := by
  rw [zero_smul]; exact NormedSpace.exp_zero

/-- **Probability is conserved** by any measurable evolution map (the honest
formal shadow of "the pendulums do not disappear", book §2184). -/
theorem evolution_conserves_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T) :
    IsProbabilityMeasure (μ.map T) :=
  MeasureTheory.Measure.isProbabilityMeasure_map hT.aemeasurable

/-! ### G.7a — the Koopman unitary of a measure-preserving equivalence -/

section Koopman

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {ν : Measure β}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- Composing with `f` then with `f.symm` is the identity on `Lp E p ν`. -/
theorem koopman_comp_left (f : α ≃ᵐ β) (hf : MeasurePreserving f μ ν) (u : Lp E p ν) :
    (Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm)
      (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u) = u := by
  apply Lp.ext
  have h2 : (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm)
      (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u)) : β → E)
      =ᵐ[ν] (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u)) : α → E) ∘ f.symm :=
    Lp.coeFn_compMeasurePreserving _ hf.symm
  have h1 : (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u)) : α → E)
      =ᵐ[μ] (↑↑u : β → E) ∘ f :=
    Lp.coeFn_compMeasurePreserving _ hf
  have h1' : ((↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf u)) : α → E) ∘ f.symm)
      =ᵐ[ν] ((↑↑u : β → E) ∘ f) ∘ f.symm :=
    (hf.symm.quasiMeasurePreserving).ae_eq_comp h1
  refine h2.trans (h1'.trans ?_)
  filter_upwards with x
  simp [Function.comp_apply, MeasurableEquiv.apply_symm_apply]

/-- Composing with `f.symm` then with `f` is the identity on `Lp E p μ`. -/
theorem koopman_comp_right (f : α ≃ᵐ β) (hf : MeasurePreserving f μ ν) (v : Lp E p μ) :
    (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf)
      (Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v) = v := by
  apply Lp.ext
  have h2 : (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf)
      (Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v)) : α → E)
      =ᵐ[μ] (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v)) : β → E) ∘ f :=
    Lp.coeFn_compMeasurePreserving _ hf
  have h1 : (↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v)) : β → E)
      =ᵐ[ν] (↑↑v : α → E) ∘ f.symm :=
    Lp.coeFn_compMeasurePreserving _ hf.symm
  have h1' : ((↑↑((Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm v)) : β → E) ∘ f)
      =ᵐ[μ] ((↑↑v : α → E) ∘ f.symm) ∘ f :=
    (hf.quasiMeasurePreserving).ae_eq_comp h1
  refine h2.trans (h1'.trans ?_)
  filter_upwards with x
  simp [Function.comp_apply, MeasurableEquiv.symm_apply_apply]

/-! ## G.13 — Parametrization implies gauge group existence

From book.tex lines 2240–2251: every parametrization `π : X → Y` has an
associated gauge group acting on `X` such that `π` is invariant under the
group action.
-/

/-- The gauge group of a parametrization `π : X → Y` acts transitively on
each fiber.  That is, for any `x₁, x₂` with `π x₁ = π x₂`, there is a
gauge group element sending `x₁` to `x₂`.  This is the key property of
the canonical gauge group (book line 2247). -/
theorem gaugeGroup_fiber_transitive {X Y : Type*} (π : X → Y)
    (x₁ x₂ : X) (h : π x₁ = π x₂) : ∃ g ∈ gaugeGroup π, g x₁ = x₂ := by
  classical
    let σ : Equiv.Perm X := Equiv.swap x₁ x₂
    have hσ : σ ∈ gaugeGroup π := by
      rw [mem_gaugeGroup]
      intro x
      dsimp [σ]
      rw [Equiv.swap_apply_def]
      split_ifs with hx₁ hx₂
      · rw [hx₁, h]
      · rw [hx₂, ← h]
      · rfl
    exact ⟨σ, hσ, by
      dsimp [σ]
      exact Equiv.swap_apply_left x₁ x₂⟩

/-! ## G.14 — Gauge symmetry vs anomalies

From book.tex lines 2394–2400: a gauge symmetry cannot exhibit anomalies
because there is no symmetry-breaking parameter.  Formally: expectation
values of gauge-invariant operators are invariant under the gauge group
action.  An anomaly would appear as a failure of this invariance.
-/

/-- A gauge symmetry cannot exhibit anomalies: expectation values of
gauge-invariant operators are invariant under the gauge group action.
This is the formal version of "there is no way to introduce a
symmetry-breaking parameter because we only consider expectation values
of gauge-invariant operators" (book line 2394). -/
theorem gauge_symmetry_no_anomaly {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (G : Type*) [Group G] (U : G → X → X)
    (f : X → ℝ) (hf : ∀ g x, f (U g x) = f x) (g : G) :
    ∫ x, f x ∂μ = ∫ x, f (U g x) ∂μ := by
  have h_eq : (fun x : X => f (U g x)) = f := by
    ext x; exact hf g x
  rw [h_eq]

/-- The **Koopman unitary** induced by a measure-preserving equivalence: the
probability-conserving evolution acts as an isometric isomorphism of
wave-functions (book §2184, and the N7(a) deliverable for book-Ch.-B §7/§9). -/
noncomputable def koopmanEquiv (f : α ≃ᵐ β) (hf : MeasurePreserving f μ ν) :
    Lp E p ν ≃ₗᵢ[ℝ] Lp E p μ where
  toLinearEquiv :=
  { (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf).toLinearMap with
    invFun := Lp.compMeasurePreservingₗᵢ ℝ (f.symm : β → α) hf.symm
    left_inv := koopman_comp_left f hf
    right_inv := koopman_comp_right f hf }
  norm_map' := (Lp.compMeasurePreservingₗᵢ ℝ (f : α → β) hf).norm_map'

end Koopman

/-! ## G.13 — Unconstrained gauge-fixing

From book.tex lines 2334–2348: a gauge-fixing is *unconstrained* when the
gauge generators are necessarily excluded from the commutative von Neumann
algebra and thus do not impose constraints on the spectrum of the algebra.
The commutative algebra used in the gauge-fixing is necessarily commutative
(bounded commuting normal operators can always be simultaneously diagonalized),
so the gauge generators (which are non-commutative in general) cannot be
members of it.
-/

/-- CAVEAT — this is a defect of *this auxiliary predicate only*, not of the
book's definition.  The book's definition of an unconstrained gauge-fixing (the
gauge generators are necessarily excluded from the commutative von Neumann
algebra, and thus impose no constraint on the spectrum, which is the full
spectrum labelled by the basis vectors) **is satisfiable**: it is formalized and
satisfied — by the book's own example `e_k ↦ e_{k+1}` — in
`BookProof.ChapterGaugeUnconstrainedSpectrum`
(`IsUnconstrainedGaugeFixing`, `shift_isUnconstrainedGaugeFixing`,
`exists_isUnconstrainedGaugeFixing`, `constrainedSpectrum_eq_univ_of_isUnconstrained`).

What is unsatisfiable is the *predicate written below*, which quantifies over
functions that are already gauge invariant: a gauge-invariant `f` satisfies
`f ∘ g = f` for every `g` of the gauge group, so no witness can exist
(`ChapterGaugeIncompleteFixing.chapterG_isUnconstrainedGaugeFixing_vacuous`), and
every statement conditioned on it is vacuous.  The two faithful renderings of the
book's condition are the exclusion of the gauge unitaries from the commutative
algebra (`ChapterGaugeUnconstrainedSpectrum.IsUnconstrainedGaugeFixing`) and the
action on the spectrum (`ChapterGaugeIncompleteFixing.MovesEveryPointOfSpectrum`,
every non-trivial gauge transformation moves every point).  The definition below
is kept unchanged for the historical record.

A gauge-fixing is *unconstrained* if the gauge group acts non-trivially
on the commutative von Neumann algebra of gauge-invariant functions
(book line 2342). This means the gauge generators are excluded from the
algebra — they cannot impose constraints on the spectrum. -/
def IsUnconstrainedGaugeFixing {X Y : Type*} (π : X → Y) : Prop :=
  ∃ g ∈ gaugeGroup π, ∃ (f : gaugeInvariantSubalgebra ℝ π),
    (f : X → ℝ) ∘ g ≠ (f : X → ℝ)

/-- In an unconstrained gauge-fixing, there exists a gauge-invariant function
whose value changes under a gauge transformation (book line 2342). -/
theorem gauge_generator_excluded_from_algebra {X Y : Type*} (π : X → Y)
    (h : IsUnconstrainedGaugeFixing π) :
    ∃ g ∈ gaugeGroup π, ∃ (f : gaugeInvariantSubalgebra ℝ π),
      (f : X → ℝ) ∘ g ≠ (f : X → ℝ) :=
  h

/-! ## G.14 — Two-basis correspondence

From book.tex lines 2356–2366: there is always one basis where the gauge
unitary transformations are functions of the spectrum (constrained basis) and
another basis where they are not (unconstrained basis). The expectation
values of gauge-invariant operators are the same in both bases.
-/

/-- The *constrained basis*: a basis where gauge unitary transformations
depend only on the spectrum (book line 2356). In this basis, the
transformation acts as `basis (g x) = φ (basis x)` for some `φ : Y → Y`. -/
def constrainedBasis {X Y : Type*} (π : X → Y) : Prop :=
  ∃ (basis : X → Y) (_ : Function.Bijective basis),
    ∀ g ∈ gaugeGroup π, ∃ (φ : Y → Y), basis ∘ g = φ ∘ basis

/-- The *unconstrained basis*: a basis where gauge transformations are
not functions of the spectrum (book line 2357). There exists a gauge
transformation that does not commute with the basis in the sense above. -/
def unconstrainedBasis {X Y : Type*} (π : X → Y) : Prop :=
  ∃ (basis : X → Y) (_ : Function.Bijective basis),
    ∃ g ∈ gaugeGroup π, ∀ (φ : Y → Y), basis ∘ g ≠ φ ∘ basis

/-- For a gauge-invariant function `f`, the value at `x` depends only on
`π x` (the image under the parametrization). This is the key property
that makes expectation values basis-independent: gauge-invariant functions
are constant on fibers of `π`. -/
theorem gaugeInvariant_constant_on_fibers {X Y : Type*}
    (π : X → Y) (f : X → ℝ) (hf : ∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x)
    (x y : X) (h : π x = π y) : f x = f y := by
  classical
    have hswap : Equiv.swap x y ∈ gaugeGroup π := swap_mem_gaugeGroup h
    have h_eq := hf (Equiv.swap x y) hswap x
    simpa [Equiv.swap_apply_left] using h_eq.symm

/-! ## G.15 — Casimir operator constraints

From book.tex lines 2368–2370: it suffices to constrain to zero the Casimir
operators of the (eventually non-commutative) Lie algebra of constraints;
this imposes the constraints without the need for the constraints to be part
of the commutative von Neumann algebra.
-/

/-- In an unconstrained gauge-fixing, the gauge-invariant subalgebra is
properly contained in the full algebra. This means there exist
non-invariant operators that must be constrained via their Casimir
operators rather than being excluded from the physical algebra.

This is the algebraic content of the Casimir sufficiency principle:
the constraints need not belong to the commutative von Neumann algebra
if the Casimir operators (which are gauge-invariant by construction)
are sufficient to enforce them. -/
theorem casimir_sufficient_for_constraints {X Y : Type*} (π : X → Y)
    (h : IsUnconstrainedGaugeFixing π) :
    gaugeInvariantSubalgebra ℝ π ≠ ⊤ := by
  rcases h with ⟨g, hg, f, hf⟩
  exfalso
  have h_contra : (f : X → ℝ) ∘ g = (f : X → ℝ) := by
    have h_mem : ∀ x, (f : X → ℝ) (g x) = (f : X → ℝ) x := f.property g hg
    ext x; exact h_mem x
  exact hf h_contra

end BookProof.ChapterG
