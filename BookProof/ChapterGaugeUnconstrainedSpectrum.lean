import Mathlib

/-!
# Unconstrained gauge-fixing: the book's definition, and why it *is* satisfiable

`book.tex` (line ~2296) defines:

> "We define gauge-fixing as unconstrained whenever the gauge generators are
> necessarily excluded from the commutative von Neumann algebra and thus do not
> impose constraints on the spectrum of the commutative algebra."

and later (line ~2356):

> "since bounded commuting normal operators can always be simultaneously
> diagonalized there is always one basis where the gauge unitary transformations
> are a function of the spectrum and (if the gauge-fixing is unconstrained) there
> is another basis where the gauge unitary transformations are not a function of
> the spectrum and thus there are no constraints."

The point of this module is that this definition is **satisfiable**, and that it
is satisfied by the book's own example.  The *spectrum* that the definition talks
about is the full spectrum labelled by the basis vectors `{e_x}` of the chosen
basis — **not** a subset carved out by the gauge generators.  A constraint on the
spectrum is a condition of the form "this element of the commutative algebra
takes the value `1` at the point `x` of the spectrum": only an operator that is a
*function of the spectrum* (i.e. a member of the commutative algebra, diagonal in
the basis) can impose such a condition.  When the gauge unitaries permute the
basis vectors non-trivially they are not diagonal, hence not members of the
commutative algebra, hence they impose no condition at all and the constrained
spectrum is the whole spectrum.

## The model

The commutative von Neumann algebra is presented in its Gelfand picture: the
spectrum is an index type `X`, the algebra is the algebra of functions `X → ℂ`
acting as the diagonal operators `diagOp d : f ↦ (x ↦ d x * f x)`, and the basis
vectors are the point masses `basisVec y`.  A gauge transformation which permutes
the basis, `e_y ↦ e_{σ y}`, is the operator `permOp σ`.

## What is proved

* `diagOp_mul_comm` — the algebra of the gauge-fixing is commutative, as the book
  insists.
* `permOp_isFunctionOfSpectrum_iff` — a basis permutation is a function of the
  spectrum **iff** it is trivial: every non-trivial gauge transformation is
  *necessarily excluded* from the commutative algebra.  This is exactly the
  book's clause "the gauge generators are necessarily excluded".
* `IsUnconstrainedGaugeFixing` — the book's definition, as a property of the
  family of gauge unitaries: no non-trivial gauge unitary is a function of the
  spectrum.
* `isUnconstrained_of_faithful`, `isUnconstrained_of_movesEveryPoint` — the
  definition **is satisfied** by every faithful permutation representation of the
  gauge group on the basis, in particular whenever every non-trivial gauge
  transformation moves every point of the spectrum.
* `shift_isUnconstrainedGaugeFixing`, `exists_isUnconstrainedGaugeFixing` — the
  book's own example `e_k ↦ e_{k+1}` on the basis indexed by `ℤ` is an
  unconstrained gauge-fixing; in particular the notion is **not vacuous**.
* `constrainedSpectrum_eq_univ_of_isUnconstrained` — and then the constrained
  spectrum is the *full* spectrum: the gauge generators impose no constraint on
  it.
* `signRep_isNotUnconstrained`, `signRep_constrainedSpectrum` — the
  contrast of the book's two-basis discussion: in a basis where the gauge
  unitaries *are* functions of the spectrum the very same gauge group does impose
  a constraint, cutting the spectrum down to a proper subset.

* `isPhysicalFunction_iff_factors`, `shift_observableSpectrum_subsingleton`,
  `shift_full_spectrum_vs_observable_spectrum` — the two spectra are *not* the
  same: the spectrum of the commutative subalgebra of gauge-invariant
  (observable) functions is the orbit space, a single point in the book's
  example, while the spectrum of the definition — the full spectrum labelled by
  the basis vectors — is all of `ℤ` and is left entirely unconstrained.

Everything is `sorry`-free.
-/

namespace BookProof.ChapterGaugeUnconstrainedSpectrum

variable {X : Type*}

/-! ## 1. The commutative algebra, its spectrum and its basis -/

/-- Operators in the chosen basis: linear maps of the space of coefficient
functions of the basis `{e_x}_{x ∈ X}`. -/
abbrev Op (X : Type*) := (X → ℂ) →ₗ[ℂ] (X → ℂ)

/-- The element of the commutative algebra given by the function `d` of the
spectrum: the operator diagonal in the basis, `e_x ↦ d x • e_x`.  These are the
*functions of the spectrum*. -/
def diagOp (d : X → ℂ) : Op X where
  toFun f := fun x => d x * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp [mul_left_comm]

/-- The gauge transformation permuting the basis vectors, `e_y ↦ e_{σ y}`. -/
def permOp (σ : Equiv.Perm X) : Op X where
  toFun f := fun x => f (σ.symm x)
  map_add' f g := by funext x; simp
  map_smul' c f := by funext x; simp

/-- The basis vector `e_y`, i.e. the point mass at the point `y` of the
spectrum. -/
def basisVec [DecidableEq X] (y : X) : X → ℂ := fun x => if x = y then 1 else 0

/-- An operator **is a function of the spectrum** when it belongs to the
commutative von Neumann algebra of the gauge-fixing, i.e. when it is diagonal in
the basis. -/
def IsFunctionOfSpectrum (T : Op X) : Prop := ∃ d : X → ℂ, T = diagOp d

@[simp] theorem diagOp_apply (d f : X → ℂ) (x : X) : diagOp d f x = d x * f x := rfl

@[simp] theorem permOp_apply (σ : Equiv.Perm X) (f : X → ℂ) (x : X) :
    permOp σ f x = f (σ.symm x) := rfl

/-- **The algebra of the gauge-fixing is commutative** (`book.tex`: "it is
crucial that the von Neumann algebra used in the gauge-fixing is
commutative"). -/
theorem diagOp_mul_comm (d e : X → ℂ) :
    diagOp d ∘ₗ diagOp e = diagOp e ∘ₗ diagOp d := by
  ext f x
  simp [mul_left_comm]

/-- Distinct functions of the spectrum are distinct operators: the Gelfand
picture is faithful. -/
theorem diagOp_injective : Function.Injective (diagOp (X := X)) := by
  intro d e h
  funext x
  have := congrArg (fun T : Op X => T (fun _ => (1 : ℂ)) x) h
  simpa using this

/-- The gauge transformation `permOp σ` sends the basis vector `e_y` to
`e_{σ y}` — the book's `e_k ↦ e_{k+1}`. -/
theorem permOp_basisVec [DecidableEq X] (σ : Equiv.Perm X) (y : X) :
    permOp σ (basisVec y) = basisVec (σ y) := by
  funext x
  simp only [permOp_apply, basisVec]
  by_cases hx : x = σ y
  · simp [hx]
  · have : σ.symm x ≠ y := fun h => hx (by rw [← h, Equiv.apply_symm_apply])
    simp [hx, this]

/-- An element of the commutative algebra acts on each basis vector by a scalar:
the basis vectors are the points of the spectrum. -/
theorem diagOp_basisVec [DecidableEq X] (d : X → ℂ) (y : X) :
    diagOp d (basisVec y) = d y • basisVec y := by
  funext x
  simp only [diagOp_apply, basisVec, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x = y <;> simp [hx]

/-- An operator that is a function of the spectrum preserves every basis ray. -/
theorem exists_eigenvalue_of_isFunctionOfSpectrum [DecidableEq X] {T : Op X}
    (hT : IsFunctionOfSpectrum T) (y : X) :
    ∃ c : ℂ, T (basisVec y) = c • basisVec y := by
  obtain ⟨d, rfl⟩ := hT
  exact ⟨d y, diagOp_basisVec d y⟩

/-- **The gauge generators are necessarily excluded from the commutative
algebra.**  A permutation of the basis is a function of the spectrum if and only
if it is the identity, so every non-trivial gauge transformation is outside the
commutative von Neumann algebra of the gauge-fixing. -/
theorem permOp_isFunctionOfSpectrum_iff (σ : Equiv.Perm X) :
    IsFunctionOfSpectrum (permOp σ) ↔ σ = 1 := by
  classical
  constructor
  · intro hσ
    ext y
    obtain ⟨c, hc⟩ := exists_eigenvalue_of_isFunctionOfSpectrum hσ y
    rw [permOp_basisVec] at hc
    have h := congrArg (fun f : X → ℂ => f (σ y)) hc
    simp only [basisVec, Pi.smul_apply, smul_eq_mul] at h
    by_cases hy : σ y = y
    · simpa using hy
    · rw [if_neg hy, mul_zero] at h
      exact absurd h one_ne_zero
  · rintro rfl
    refine ⟨fun _ => 1, ?_⟩
    ext f x
    simp

/-! ## 2. The book's definition of an unconstrained gauge-fixing -/

variable {G : Type*} [Group G]

/-- **The book's definition** (`book.tex` ~2296): a gauge-fixing — a commutative
von Neumann algebra, here the diagonal operators of a basis, together with the
family `U` of gauge unitaries — is *unconstrained* when the gauge generators are
necessarily excluded from the commutative algebra, i.e. when no non-trivial gauge
unitary is a function of the spectrum. -/
def IsUnconstrainedGaugeFixing (U : G → Op X) : Prop :=
  ∀ g : G, g ≠ 1 → ¬ IsFunctionOfSpectrum (U g)

/-- The **constrained spectrum**: the points of the full spectrum that survive
the constraints "the gauge unitary equals the identity" *as conditions on the
spectrum*.  Only a gauge unitary that is a function of the spectrum, `U g =
diagOp d`, produces such a condition, namely `d x = 1`. -/
def constrainedSpectrum (U : G → Op X) : Set X :=
  {x : X | ∀ (g : G) (d : X → ℂ), U g = diagOp d → d x = 1}

/-- **No constraint on the spectrum.**  For an unconstrained gauge-fixing the
constrained spectrum is the *full* spectrum: the gauge generators, being excluded
from the commutative algebra, impose no condition on the points of the spectrum.
(The only hypothesis besides `IsUnconstrainedGaugeFixing` is that the gauge
unitary of the neutral element is the identity operator.) -/
theorem constrainedSpectrum_eq_univ_of_isUnconstrained {U : G → Op X}
    (hU : IsUnconstrainedGaugeFixing U) (hU1 : U 1 = LinearMap.id) :
    constrainedSpectrum U = Set.univ := by
  ext x
  simp only [constrainedSpectrum, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro g d hd
  by_cases hg : g = 1
  · subst hg
    have hid : diagOp (fun _ : X => (1 : ℂ)) = diagOp d := by
      rw [← hd, hU1]; ext f x; simp
    have := diagOp_injective hid
    exact (congrFun this x).symm
  · exact absurd ⟨d, hd⟩ (hU g hg)

/-- **The definition is satisfied** by every faithful action of the gauge group
on the basis: the gauge unitaries `e_y ↦ e_{ρ g y}` of an injective
representation `ρ` form an unconstrained gauge-fixing. -/
theorem isUnconstrained_of_faithful {ρ : G →* Equiv.Perm X}
    (hρ : Function.Injective ρ) :
    IsUnconstrainedGaugeFixing (fun g => permOp (ρ g)) := by
  intro g hg hmem
  exact hg (hρ (by simpa using (permOp_isFunctionOfSpectrum_iff (ρ g)).1 hmem))

/-- **The unconstrained condition in the book's other phrasing** (`book.tex`
~2336: "any non-trivial gauge transformation necessarily modifies any point of
the spectrum"): if every non-trivial gauge transformation moves every point of
the spectrum, the gauge-fixing is unconstrained. -/
theorem isUnconstrained_of_movesEveryPoint [Nonempty X]
    {ρ : G →* Equiv.Perm X} (hmoves : ∀ g : G, g ≠ 1 → ∀ x : X, ρ g x ≠ x) :
    IsUnconstrainedGaugeFixing (fun g => permOp (ρ g)) := by
  intro g hg hmem
  have hρg : ρ g = 1 := (permOp_isFunctionOfSpectrum_iff (ρ g)).1 hmem
  obtain ⟨x⟩ := ‹Nonempty X›
  exact hmoves g hg x (by rw [hρg]; rfl)

/-! ## 3. The book's own example: the lattice translations `e_k ↦ e_{k+1}` -/

/-- The translation representation of `ℤ` on the basis `{e_k}_{k ∈ ℤ}`:
`e_k ↦ e_{k+m}` (`book.tex` 2281–2289). -/
def shiftPerm : Multiplicative ℤ →* Equiv.Perm ℤ where
  toFun m := Equiv.addRight (Multiplicative.toAdd m)
  map_one' := by ext k; simp
  map_mul' m n := by
    ext k
    simp [Equiv.addRight, add_comm, add_left_comm]

@[simp] theorem shiftPerm_apply (m : Multiplicative ℤ) (k : ℤ) :
    shiftPerm m k = k + Multiplicative.toAdd m := rfl

/-- Every non-trivial translation moves every point of the spectrum. -/
theorem shiftPerm_movesEveryPoint (m : Multiplicative ℤ) (hm : m ≠ 1) (k : ℤ) :
    shiftPerm m k ≠ k := by
  have hm' : Multiplicative.toAdd m ≠ 0 := fun h => hm (by
    apply Multiplicative.toAdd.injective
    simpa using h)
  simp only [shiftPerm_apply]
  omega

/-- **The book's example is an unconstrained gauge-fixing.**  The gauge group
generated by `e_k ↦ e_{k+1}` acting on the commutative algebra of the operators
diagonal in the basis `{e_k}` satisfies the book's definition: no non-trivial
translation is a function of the spectrum. -/
theorem shift_isUnconstrainedGaugeFixing :
    IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m)) :=
  isUnconstrained_of_movesEveryPoint shiftPerm_movesEveryPoint

/-- **The definition of an unconstrained gauge-fixing is satisfiable**: there is
a gauge group with a non-trivial element, a basis, and a family of gauge
unitaries which is an unconstrained gauge-fixing, whose constrained spectrum is
the full spectrum. -/
theorem exists_isUnconstrainedGaugeFixing :
    ∃ (G : Type) (_ : Group G) (X : Type) (U : G → Op X),
      Nontrivial G ∧ IsUnconstrainedGaugeFixing U ∧
        constrainedSpectrum U = Set.univ := by
  refine ⟨Multiplicative ℤ, inferInstance, ℤ,
    fun m => permOp (shiftPerm m), inferInstance, shift_isUnconstrainedGaugeFixing, ?_⟩
  refine constrainedSpectrum_eq_univ_of_isUnconstrained
    shift_isUnconstrainedGaugeFixing ?_
  ext f k
  simp [shiftPerm]

/-! ## 4. The contrast: a *constrained* gauge-fixing

The book's two-basis discussion (`book.tex` ~2356): in a basis where the gauge
unitaries *are* functions of the spectrum, the same gauge group does impose
constraints, and the constrained spectrum is a proper subset of the full
spectrum.  Here is the sign representation of `ℤ`, diagonal in the basis, whose
constrained spectrum is the single point `0`. -/

/-- A gauge representation which *is* diagonal in the basis: `U m` multiplies the
basis vector `e_k` by `1` for `k = 0` and by `(-1)^m` otherwise. -/
noncomputable def signRep (m : Multiplicative ℤ) : Op ℤ :=
  diagOp fun k => if k = 0 then 1 else (-1 : ℂ) ^ (Multiplicative.toAdd m)

/-- This gauge-fixing is **not** unconstrained: the gauge unitaries are functions
of the spectrum. -/
theorem signRep_isNotUnconstrained : ¬ IsUnconstrainedGaugeFixing signRep := by
  intro h
  exact h (Multiplicative.ofAdd 1) (by
    intro hm
    have : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)) = 0 := by
      rw [hm]; rfl
    simp at this) ⟨_, rfl⟩

/-- **And then the gauge generators do constrain the spectrum**: the constrained
spectrum of the diagonal representation is the proper subset `{0}` of the full
spectrum `ℤ`. -/
theorem signRep_constrainedSpectrum : constrainedSpectrum signRep = {0} := by
  ext k
  simp only [constrainedSpectrum, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hk
    have hd := h (Multiplicative.ofAdd 1)
      (fun j => if j = 0 then 1 else (-1 : ℂ) ^ (1 : ℤ)) rfl
    simp only [if_neg hk] at hd
    norm_num at hd
  · rintro rfl
    intro m d hd
    have := diagOp_injective (hd ▸ rfl : diagOp
      (fun k => if k = 0 then 1 else (-1 : ℂ) ^ (Multiplicative.toAdd m)) = diagOp d)
    rw [← congrFun this 0]
    simp

/-! ## 5. The two spectra: the full spectrum of the basis, and the spectrum of the
observables

The definition speaks of "the spectrum of the commutative algebra" used in the
gauge-fixing — the *full* spectrum, labelled by the basis vectors `{e_x}_{x ∈ X}`
— and **not** of the spectrum of the commutative subalgebra of gauge-invariant
(physical) observables, which is the orbit space `X/G`.  The two are genuinely
different, and it is the first one on which the gauge generators impose no
constraint.  In the book's own example they are as different as can be: the full
spectrum is all of `ℤ`, the spectrum of the observables is a single point. -/

/-- A function of the spectrum is a **physical observable** when it is gauge
invariant, i.e. constant on the gauge orbits. -/
def IsPhysicalFunction (ρ : G →* Equiv.Perm X) (d : X → ℂ) : Prop :=
  ∀ (g : G) (x : X), d (ρ g x) = d x

/-- The orbit equivalence of the gauge action on the full spectrum. -/
def orbitSetoid (ρ : G →* Equiv.Perm X) : Setoid X where
  r x y := ∃ g : G, ρ g x = y
  iseqv :=
    { refl := fun x => ⟨1, by simp⟩
      symm := by
        rintro x y ⟨g, rfl⟩
        exact ⟨g⁻¹, by rw [map_inv]; simp⟩
      trans := by
        rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
        exact ⟨h * g, by rw [map_mul]; rfl⟩ }

/-- **The spectrum of the commutative subalgebra of observables**: the orbit
space `X/G` of the gauge action on the full spectrum. -/
def observableSpectrum (ρ : G →* Equiv.Perm X) : Type _ := Quotient (orbitSetoid ρ)

/-- The physical observables are exactly the functions of the *observable*
spectrum: a gauge-invariant function of the full spectrum factors through the
orbit space, and conversely. -/
theorem isPhysicalFunction_iff_factors (ρ : G →* Equiv.Perm X) (d : X → ℂ) :
    IsPhysicalFunction ρ d ↔
      ∃ D : observableSpectrum ρ → ℂ, ∀ x : X, d x = D (Quotient.mk (orbitSetoid ρ) x) := by
  constructor
  · intro hd
    refine ⟨Quotient.lift d ?_, fun x => rfl⟩
    rintro x y ⟨g, rfl⟩
    exact (hd g x).symm
  · rintro ⟨D, hD⟩ g x
    rw [hD (ρ g x), hD x]
    exact congrArg D (Quotient.sound ⟨g⁻¹, by rw [map_inv]; simp⟩)

/-- In the book's example the spectrum of the subalgebra of observables is a
**single point**: the translations act transitively on the basis, so every gauge
invariant function of the spectrum is constant. -/
theorem shift_observableSpectrum_subsingleton :
    Subsingleton (observableSpectrum shiftPerm) := by
  constructor
  refine Quotient.ind₂ (fun k l => ?_)
  refine Quotient.sound ⟨Multiplicative.ofAdd (l - k), ?_⟩
  simp only [shiftPerm_apply]
  change k + (l - k) = l
  omega

/-- Equivalently: every physical observable of the book's example is a constant
function. -/
theorem shift_isPhysicalFunction_const {d : ℤ → ℂ} (hd : IsPhysicalFunction shiftPerm d)
    (k l : ℤ) : d k = d l := by
  have h := hd (Multiplicative.ofAdd (l - k)) k
  simp only [shiftPerm_apply] at h
  rw [show k + Multiplicative.toAdd (Multiplicative.ofAdd (l - k)) = l from by
    change k + (l - k) = l; omega] at h
  exact h.symm

/-- **The two spectra, side by side** (the point of the book's definition): for
the gauge-fixing of the book's example the gauge-fixing is unconstrained, the
full spectrum labelled by the basis vectors is the infinite set `ℤ` and it is
left *entirely* unconstrained by the gauge generators — while the spectrum of the
commutative subalgebra of observables is a single point.  "The spectrum" of the
definition is the first one. -/
theorem shift_full_spectrum_vs_observable_spectrum :
    IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m)) ∧
      constrainedSpectrum (fun m : Multiplicative ℤ => permOp (shiftPerm m)) =
        (Set.univ : Set ℤ) ∧
      (Set.univ : Set ℤ).Infinite ∧
      Subsingleton (observableSpectrum shiftPerm) := by
  refine ⟨shift_isUnconstrainedGaugeFixing, ?_, Set.infinite_univ,
    shift_observableSpectrum_subsingleton⟩
  refine constrainedSpectrum_eq_univ_of_isUnconstrained shift_isUnconstrainedGaugeFixing ?_
  ext f k
  simp [shiftPerm]

end BookProof.ChapterGaugeUnconstrainedSpectrum
