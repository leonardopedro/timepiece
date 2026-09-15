import Mathlib

/-!
# A time-dependent evolution becomes time-independent in a larger space

Source: `book.tex`, chapter *"Resolution of the singularity of the ODE x'=x^2 when the
initial x has uncertainties"*, §*General picture* (`book.tex` line ~1000):

> *"any solution in a standard probability space is given by a time-dependent self-adjoint
> Hamiltonian in a larger probability space, then the singularities in a standard
> probability space are consequence of a time-dependent Hamiltonian which is non-integrable.
> But since any time-dependent Hamiltonian can be converted into a time-independent
> Hamiltonian in an even larger sample space, then we can always resolve the singularities
> in a larger sample space which better defines the dynamical system."*

Two levels of that statement are formalized here.

## The classical level: a non-autonomous vector field is autonomous on `ℝ × E`

`autonomize f (s, x) = (1, f s x)` is the extended vector field, and
`hasDerivAt_autonomize` says that the graph `t ↦ (t, x t)` of a solution of the
non-autonomous equation `ẋ = f(t, x)` is a solution of the autonomous equation `ż = F z`;
`hasDerivAt_of_autonomize` is the converse, so nothing is lost by enlarging the space.

## The quantum level: the Howland evolution group

For a time-dependent Hamiltonian the natural object is the family of propagators
`U(t,s)`, which is *not* a one-parameter group.  On the enlarged space of
time-dependent states `ψ : ℝ → H` — the "even larger sample space" of the quotation — the
translated evolution

```
(𝒰(σ)ψ)(t) = U(t, t − σ) ψ(t − σ)
```

**is** a one-parameter group (`howland_add`, `howland_zero`, `howland_neg`) of
probability-preserving maps (`howland_lintegral_normSq`), i.e. an autonomous evolution; by
Stone's theorem (formalized in this project in `BookProof.ChapterStoneTheorem` and
`BookProof.ChapterStoneConverse`) its generator is a *time-independent* self-adjoint
Hamiltonian on the larger space.  Only the three defining properties of a unitary
propagator are used: `U t t = id`, the cocycle law, and pointwise isometry.
-/

namespace BookProof.Howland

open MeasureTheory

/-! ## The classical level -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The autonomous vector field on `ℝ × E` attached to a non-autonomous field `f`. -/
def autonomize (f : ℝ → E → E) : ℝ × E → ℝ × E := fun z => (1, f z.1 z.2)

/-- A solution of `ẋ = f(t, x)` gives a solution of the autonomous extension. -/
theorem hasDerivAt_autonomize (f : ℝ → E → E) (x : ℝ → E) (t : ℝ)
    (hx : HasDerivAt x (f t (x t)) t) :
    HasDerivAt (fun s : ℝ => ((s, x s) : ℝ × E)) (autonomize f (t, x t)) t := by
  simpa [autonomize] using (hasDerivAt_id t).prodMk hx

/-- Conversely, the second component of a solution of the autonomous extension whose first
component is the time solves the original non-autonomous equation. -/
theorem hasDerivAt_of_autonomize (f : ℝ → E → E) (x : ℝ → E) (t : ℝ)
    (h : HasDerivAt (fun s : ℝ => ((s, x s) : ℝ × E)) (autonomize f (t, x t)) t) :
    HasDerivAt x (f t (x t)) t := by
  have := h.snd
  simpa [autonomize] using this

/-! ## The quantum level: the Howland group of a time-dependent propagator -/

variable {H : Type*} [NormedAddCommGroup H]

/-- The defining properties of the propagator family of a time-dependent Hamiltonian:
`U t s` evolves a state from time `s` to time `t`. -/
structure IsPropagator (U : ℝ → ℝ → H → H) : Prop where
  refl : ∀ t x, U t t x = x
  cocycle : ∀ t s r x, U t s (U s r x) = U t r x
  isometry : ∀ t s x, ‖U t s x‖ = ‖x‖

/-- The hypotheses are satisfiable: the trivial propagator. -/
theorem isPropagator_id : IsPropagator (fun (_ _ : ℝ) (x : H) => x) where
  refl := by intro t x; rfl
  cocycle := by intro t s r x; rfl
  isometry := by intro t s x; rfl

/-- A time-**independent** Hamiltonian gives the propagator `U(t,s) = V(t-s)` of its
unitary group; it satisfies the three axioms.  (For such a `U`, the Howland group is the
original group acting pointwise in time.) -/
theorem isPropagator_of_group (V : ℝ → H → H) (hzero : ∀ x, V 0 x = x)
    (hadd : ∀ a b x, V a (V b x) = V (a + b) x) (hiso : ∀ a x, ‖V a x‖ = ‖x‖) :
    IsPropagator (fun t s (x : H) => V (t - s) x) where
  refl := by intro t x; simpa using hzero x
  cocycle := by
    intro t s r x
    have : t - s + (s - r) = t - r := by ring
    rw [hadd, this]
  isometry := by intro t s x; exact hiso _ x

variable {U : ℝ → ℝ → H → H}

/-- The Howland evolution on time-dependent states: `(𝒰(σ)ψ)(t) = U(t, t−σ) ψ(t−σ)`. -/
def howland (U : ℝ → ℝ → H → H) (σ : ℝ) (ψ : ℝ → H) : ℝ → H :=
  fun t => U t (t - σ) (ψ (t - σ))

@[simp] theorem howland_zero (hU : IsPropagator U) (ψ : ℝ → H) :
    howland U 0 ψ = ψ := by
  funext t
  simp [howland, hU.refl]

/-- **The group law.**  On the enlarged space the time-dependent evolution is a genuine
one-parameter group — an autonomous evolution. -/
theorem howland_add (hU : IsPropagator U) (σ τ : ℝ) (ψ : ℝ → H) :
    howland U σ (howland U τ ψ) = howland U (σ + τ) ψ := by
  funext t
  have hsub : t - σ - τ = t - (σ + τ) := by ring
  simp only [howland]
  rw [hU.cocycle, hsub]

theorem howland_neg (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) :
    howland U (-σ) (howland U σ ψ) = ψ := by
  rw [howland_add hU, neg_add_cancel, howland_zero hU]

/-- **Probability is conserved** by the Howland group: it is a group of isometries of
`L²(ℝ; H)`, so by Stone's theorem its generator is a time-independent self-adjoint
Hamiltonian. -/
theorem howland_lintegral_normSq (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) :
    ∫⁻ t, ENNReal.ofReal (‖howland U σ ψ t‖ ^ 2)
      = ∫⁻ t, ENNReal.ofReal (‖ψ t‖ ^ 2) := by
  have hpt : ∀ t : ℝ, ENNReal.ofReal (‖howland U σ ψ t‖ ^ 2)
      = ENNReal.ofReal (‖ψ (t - σ)‖ ^ 2) := by
    intro t
    simp [howland, hU.isometry]
  calc ∫⁻ t, ENNReal.ofReal (‖howland U σ ψ t‖ ^ 2)
      = ∫⁻ t, ENNReal.ofReal (‖ψ (t + -σ)‖ ^ 2) := by
        refine lintegral_congr fun t => ?_
        rw [hpt t]
        ring_nf
    _ = ∫⁻ t, ENNReal.ofReal (‖ψ t‖ ^ 2) :=
        lintegral_add_right_eq_self (fun t => ENNReal.ofReal (‖ψ t‖ ^ 2)) (-σ)

end BookProof.Howland
