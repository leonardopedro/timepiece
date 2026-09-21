import BookProof.ChapterGaugeIncompleteFixing

/-!
# Every parametrization carries a gauge symmetry

This module formalizes the opening argument of the section *"Gauge transformations,
constrained systems and conditioned probability"* of `book.tex` (lines 2240–2252):

> "This includes the case of parametrizations, since these are surjective but
> often there are two or more points in the space of parameters which correspond
> to the same point in the parametrized space […].  As a matter of principle, for
> all parametrizations we can define a gauge group transforming points in the
> parameter space without modifying the corresponding point in the parametrized
> space.  Thus all parametrizations are solutions to constraint equations
> requiring gauge invariance."

Given any parametrization `π : X → Y` of a space `Y` by a parameter space `X`, the
**gauge group of the parametrization** is the group `fiberGauge π` of the
permutations of the parameter space that do not move the parametrized point.

## Results

* `fiberGauge` — the gauge group of a parametrization, a subgroup of the
  permutations of the parameter space.
* `orbit_eq_fiber` — its orbits are *exactly* the fibers of `π`: two parameters
  describe the same point iff they are gauge equivalent.
* `isPhysicalObservable_iff_factors_through` — the gauge-invariant observables of
  this gauge group are exactly the functions of the parametrized point.  This is
  the book's "all parametrizations are solutions to constraint equations requiring
  gauge invariance".
* `fiberGauge_ne_bot_iff` — the gauge group is non-trivial precisely when the
  parametrization is redundant (two parameters for one point), and
  `fiberGauge_eq_bot_iff` is the injective case.
* `isCompleteGaugeFixing'_iff_injOn`,
  `isComprehensiveGaugeFixing_iff_surjOn` — a gauge fixing of this gauge symmetry
  is complete exactly when `π` is injective on it, and comprehensive exactly when
  it already meets every fiber, i.e. when `π` maps it onto the whole parametrized
  space.  A complete comprehensive gauge fixing is therefore the same thing as a
  set of parameters in bijection with the parametrized space.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ChapterGaugeParametrization

open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

/-- The **gauge group of a parametrization** `π : X → Y`: the permutations of the
parameter space `X` that leave the parametrized point `π x` unchanged. -/
def fiberGauge (π : X → Y) : Subgroup (Equiv.Perm X) where
  carrier := {σ | ∀ x, π (σ x) = π x}
  mul_mem' {a b} ha hb x := by
    simp only [Equiv.Perm.mul_apply]
    rw [ha (b x), hb x]
  one_mem' _ := rfl
  inv_mem' {a} ha x := by
    have h := ha (a⁻¹ x)
    simpa using h.symm

@[simp] theorem mem_fiberGauge {π : X → Y} {σ : Equiv.Perm X} :
    σ ∈ fiberGauge π ↔ ∀ x, π (σ x) = π x := Iff.rfl

@[simp] theorem fiberGauge_smul (π : X → Y) (σ : fiberGauge π) (x : X) :
    ((σ • x : X)) = (σ : Equiv.Perm X) x := rfl

/-- The gauge transformations do not move the parametrized point. -/
theorem apply_eq (π : X → Y) (σ : fiberGauge π) (x : X) : π (σ • x) = π x :=
  σ.property x

/-- **The orbits of the gauge group of a parametrization are exactly its fibers**:
two parameters are gauge equivalent iff they describe the same point. -/
theorem orbit_eq_fiber (π : X → Y) (x : X) :
    MulAction.orbit (fiberGauge π) x = π ⁻¹' {π x} := by
  classical
  ext y
  constructor
  · rintro ⟨σ, rfl⟩
    exact apply_eq π σ x
  · intro hy
    have hy' : π y = π x := hy
    refine ⟨⟨Equiv.swap x y, ?_⟩, ?_⟩
    · intro z
      rcases eq_or_ne z x with rfl | hzx
      · simp [Equiv.swap_apply_left, hy']
      · rcases eq_or_ne z y with rfl | hzy
        · simp [Equiv.swap_apply_right, hy']
        · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    · change Equiv.swap x y x = y
      simp

/-- **All parametrizations are gauge-invariance constraints.** A real observable
of the parameter space is invariant under the gauge group of `π` if and only if it
is a function of the parametrized point. -/
theorem isPhysicalObservable_iff_factors_through (π : X → Y) (f : X → ℝ) :
    IsPhysicalObservable (fiberGauge π) f ↔ ∃ F : Y → ℝ, ∀ x, f x = F (π x) := by
  classical
  constructor
  · intro hf
    have hfib : ∀ x y : X, π x = π y → f x = f y := by
      intro x y hxy
      have hmem : y ∈ MulAction.orbit (fiberGauge π) x := by
        rw [orbit_eq_fiber]
        exact hxy.symm
      obtain ⟨σ, hσ⟩ := hmem
      have := hf σ x
      rw [show σ • x = y from hσ] at this
      exact this.symm
    refine ⟨fun y => if h : ∃ x, π x = y then f h.choose else 0, fun x => ?_⟩
    have hex : ∃ z, π z = π x := ⟨x, rfl⟩
    simp only [dif_pos hex]
    exact hfib x hex.choose hex.choose_spec.symm
  · rintro ⟨F, hF⟩ σ x
    rw [hF (σ • x), hF x, apply_eq π σ x]

/-- The gauge group of a parametrization is trivial exactly when the
parametrization is not redundant. -/
theorem fiberGauge_eq_bot_iff (π : X → Y) :
    fiberGauge π = ⊥ ↔ Function.Injective π := by
  classical
  constructor
  · intro hbot x y hxy
    by_contra hne
    have hmem : Equiv.swap x y ∈ fiberGauge π := by
      intro z
      rcases eq_or_ne z x with rfl | hzx
      · simp [Equiv.swap_apply_left, hxy]
      · rcases eq_or_ne z y with rfl | hzy
        · simp [Equiv.swap_apply_right, hxy]
        · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hne ((Equiv.swap_apply_left x y) ▸ congrArg (fun σ : Equiv.Perm X => σ x) hmem).symm
  · intro hinj
    refine le_antisymm (fun σ hσ => ?_) bot_le
    rw [Subgroup.mem_bot]
    ext x
    exact hinj (hσ x)

/-- Equivalently: the parametrization is redundant exactly when its gauge group is
non-trivial. -/
theorem fiberGauge_ne_bot_iff (π : X → Y) :
    fiberGauge π ≠ ⊥ ↔ ¬ Function.Injective π := by
  rw [Ne, fiberGauge_eq_bot_iff]

/-- A gauge fixing of a parametrization is **complete** exactly when the
parametrization is injective on it. -/
theorem isCompleteGaugeFixing'_iff_injOn (π : X → Y) (S : Set X) :
    IsCompleteGaugeFixing' (fiberGauge π) S ↔ Set.InjOn π S := by
  classical
  constructor
  · intro hS x hx y hy hxy
    have hmem : y ∈ MulAction.orbit (fiberGauge π) x := by
      rw [orbit_eq_fiber]
      exact hxy.symm
    obtain ⟨σ, hσ⟩ := hmem
    exact hS x hx y hy σ hσ
  · intro hinj s hs t ht σ hσ
    refine hinj hs ht ?_
    rw [← hσ, apply_eq π σ s]

/-- A gauge fixing of a parametrization is **comprehensive** exactly when every
parametrized point is described by a parameter in it. -/
theorem isComprehensiveGaugeFixing_iff_surjOn (π : X → Y) (S : Set X) :
    IsComprehensiveGaugeFixing (fiberGauge π) S ↔ ∀ x : X, ∃ s ∈ S, π s = π x := by
  constructor
  · intro hS x
    obtain ⟨s, hsS, σ, hσ⟩ := hS x
    exact ⟨s, hsS, by rw [← hσ, apply_eq π σ s]⟩
  · intro hS x
    obtain ⟨s, hsS, hs⟩ := hS x
    have hmem : x ∈ MulAction.orbit (fiberGauge π) s := by
      rw [orbit_eq_fiber]
      exact hs.symm
    obtain ⟨σ, hσ⟩ := hmem
    exact ⟨s, hsS, σ, hσ⟩

end BookProof.ChapterGaugeParametrization
