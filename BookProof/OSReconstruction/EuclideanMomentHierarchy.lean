import Mathlib

/-!
# C2, first slice: the regulated Euclidean moment hierarchy

`cftproof.md` **C2** asks, at fixed cutoff, for the physical observables and the Euclidean
moments of ordered times built from `exp(-(t_{i+1} - t_i) K)` between reference vectors, with
domain and integrability of every word, the extension conventions, and a demonstration that
the resulting correlations are nonzero and have nontrivial time dependence.

This module formalizes that hierarchy for a **bounded** generator `K` on a complex Hilbert
space — the finite‑mode regulator, where every operator is bounded and every moment is a
finite scalar, so domain and integrability hold by construction rather than by assumption.
The interacting, unbounded, distribution‑valued case is the boundary (below).

## Contents

* `euclidEvol K t` — the Euclidean evolution `e^{-tK}`, with `euclidEvol_zero` and the
  semigroup law `euclidEvol_add` (exponentials of commuting multiples of one generator);
* `euclidWord K A word` — the ordered product `A₀ e^{-Δ₁K} A₁ ⋯ e^{-ΔₙK} Aₙ`;
* `euclidMoment K Ω A word` — the moment `⟨Ω, (that product) Ω⟩`;
* `euclidWord_append` — the **extension convention**: splitting a word at a time gap
  composes the corresponding operator products, so appending a word is composing with its
  operator;
* `euclidMoment_nil`, `euclidMoment_one_nil` — the empty word and the **normalization** of a
  unit reference vector;
* `euclidMoment_zero_adjoint` — **two‑point positivity at coincident times**:
  `⟨Ω, A† A Ω⟩ = ‖A Ω‖² ≥ 0`, the regulator‑level square that the OS form generalizes;
* the **one‑mode free regulator** `scalarK m = m • 1` with `euclidMoment_scalarK` giving
  `e^{-t m}`: a correlation that is nonzero for every `t` and genuinely time dependent
  (`scalarMoment_ne_one`), which is the C2 acceptance's non‑triviality condition at the
  regulator level.

## Honest boundary

* `K` is a **bounded** operator on a complete complex Hilbert space: this is the finite‑mode
  regulator `NestedSpec` at a fixed cutoff, not the unbounded `h_sigma` with an identified
  domain.  No selection theorem for the unbounded closure is used or claimed here.
* Only the moment hierarchy and its conventions are constructed.  **Half‑space OS positivity
  at the interacting regulator**, the configuration/field‑law representation, and the
  positivity‑preserving semigroup with ground function are not built in this slice; a
  positive but non‑contracting `K` supplies moments, not a classical path measure.  In
  particular `euclidMoment K Ω A [(t, A)] = e^{-tm}` below is a **scalar** free moment, not
  a proof that the interaction survives.
* The reference vector is a unit vector; the ground‑state condition `K Ω = 0`, the spectral
  positivity of `K`, and the contraction `‖e^{-tK}‖ ≤ 1` are stated as hypotheses where used,
  not derived.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace BookProof.OSReconstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## 1. Euclidean evolution and its semigroup -/

/-- The **Euclidean time evolution** `e^{-tK}` of a bounded generator `K`, as a bounded
operator.  On the finite‑mode regulator this is the only operator the moment hierarchy
needs. -/
def euclidEvol (K : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  NormedSpace.exp ((-(t : ℂ)) • K)

theorem euclidEvol_zero (K : E →L[ℂ] E) : euclidEvol K 0 = 1 := by
  unfold euclidEvol
  simp

/-- Two Euclidean evolutions of the same generator commute. -/
theorem commute_euclidEvol (K : E →L[ℂ] E) (s t : ℝ) :
    Commute (euclidEvol K s) (euclidEvol K t) := by
  unfold euclidEvol
  exact (((Commute.refl K).smul_left _).smul_right _).exp

/-- **The semigroup law** `e^{-(s+t)K} = e^{-sK} e^{-tK}` for the Euclidean evolution. -/
theorem euclidEvol_add (K : E →L[ℂ] E) (s t : ℝ) :
    euclidEvol K (s + t) = euclidEvol K s * euclidEvol K t := by
  unfold euclidEvol
  have h : (-((s + t : ℝ) : ℂ)) • K = (-(s : ℂ)) • K + (-(t : ℂ)) • K := by
    push_cast
    rw [neg_add, add_smul]
  rw [h]
  haveI : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_add_of_commute (((Commute.refl K).smul_left _).smul_right _)

/-! ## 2. Words and moments -/

/-- The **ordered product** of a word: the accumulator starts at the first observable `A`,
and each later `(Δ, B)` multiplies by `e^{-ΔK} B` on the right.  Thus
`euclidWord K A [(Δ₁, A₁), (Δ₂, A₂)] = A e^{-Δ₁K} A₁ e^{-Δ₂K} A₂`. -/
def euclidWord (K : E →L[ℂ] E) : (E →L[ℂ] E) → List (ℝ × (E →L[ℂ] E)) → E →L[ℂ] E
  | A, [] => A
  | A, (Δ, B) :: rest => euclidWord K (A * euclidEvol K Δ * B) rest

/-- The **Euclidean moment** of an ordered word between the reference vector `Ω`:
`⟨Ω, A e^{-Δ₁K} A₁ ⋯ e^{-ΔₙK} Aₙ Ω⟩`. -/
def euclidMoment (K : E →L[ℂ] E) (Ω : E) (A : E →L[ℂ] E)
    (word : List (ℝ × (E →L[ℂ] E))) : ℂ :=
  ⟪Ω, euclidWord K A word Ω⟫_ℂ

/-- **The extension convention**: splitting a word at a gap composes the two operator
products, so appending a word is composing with the operator of the appended word. -/
theorem euclidWord_append (K : E →L[ℂ] E) (A : E →L[ℂ] E) (l₁ l₂ : List (ℝ × (E →L[ℂ] E))) :
    euclidWord K A (l₁ ++ l₂) = euclidWord K (euclidWord K A l₁) l₂ := by
  induction l₁ generalizing A with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨Δ, B⟩ := head
    exact ih (A * euclidEvol K Δ * B)

theorem euclidMoment_nil (K : E →L[ℂ] E) (Ω : E) (A : E →L[ℂ] E) :
    euclidMoment K Ω A [] = ⟪Ω, A Ω⟫_ℂ := rfl

/-- **Normalization of the reference vector**: for `‖Ω‖ = 1` the empty word of the identity
observable has moment one. -/
theorem euclidMoment_one_nil (K : E →L[ℂ] E) (Ω : E) (hΩ : ‖Ω‖ = 1) :
    euclidMoment K Ω 1 [] = 1 := by
  rw [euclidMoment_nil]
  simp [hΩ]

/-- **Two-point positivity at coincident times**: with the adjoint observable,
`⟨Ω, A† A Ω⟩ = ‖A Ω‖²`, so the real part is nonnegative.  This is the regulator-level square
that the half-space OS form has to generalize to separated times. -/
theorem euclidMoment_zero_adjoint (K : E →L[ℂ] E) (Ω : E) (A : E →L[ℂ] E) :
    euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(0, A)]
      = ((‖A Ω‖ ^ 2 : ℝ) : ℂ) := by
  unfold euclidMoment euclidWord
  simp only [euclidEvol_zero, mul_one, euclidWord]
  rw [ContinuousLinearMap.mul_apply]
  rw [ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ) (A := A) (x := Ω) (y := A Ω)]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (A Ω)]
  push_cast
  rfl

theorem euclidMoment_zero_adjoint_re_nonneg (K : E →L[ℂ] E) (Ω : E) (A : E →L[ℂ] E) :
    0 ≤ (euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(0, A)]).re := by
  rw [euclidMoment_zero_adjoint, Complex.ofReal_re]
  positivity

/-! ## 3. The one-mode free regulator -/

/-- The **one-mode free regulator**: the generator `K = m • 1` on the one-dimensional complex
Hilbert space.  Its moments are the free Euclidean correlations of a single mode. -/
def scalarK (m : ℝ) : ℂ →L[ℂ] ℂ := (m : ℂ) • 1

/-- The Euclidean evolution of the one-mode regulator is scalar multiplication by
`e^{-t m}`. -/
theorem euclidEvol_scalarK (m t : ℝ) :
    euclidEvol (scalarK m) t = (Real.exp (-(t * m)) : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
  unfold euclidEvol scalarK
  have h : (-(t : ℂ)) • ((m : ℂ) • (1 : ℂ →L[ℂ] ℂ))
      = ((-(t * m) : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
    rw [smul_smul]
    push_cast
    ring_nf
  rw [h]
  have hkey := NormedSpace.algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := ℂ →L[ℂ] ℂ) ((-(t * m) : ℝ) : ℂ)
  simp only [Algebra.algebraMap_eq_smul_one] at hkey
  rw [← hkey]
  have hscalar : NormedSpace.exp ((-(t * m) : ℝ) : ℂ)
      = ((Real.exp (-(t * m)) : ℝ) : ℂ) := by
    rw [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]
  rw [hscalar]

/-- **The free one-mode moment** `⟨1, e^{-tK} 1⟩ = e^{-t m}`: nonzero for every `t` and
strictly time dependent for `m ≠ 0`. -/
theorem euclidMoment_scalarK (m t : ℝ) :
    euclidMoment (scalarK m) 1 1 [(t, 1)] = (Real.exp (-(t * m)) : ℂ) := by
  simp only [euclidMoment, euclidWord, one_mul, mul_one]
  rw [euclidEvol_scalarK]
  simp

/-- The free one-mode moment is **strictly positive**. -/
theorem euclidMoment_scalarK_re_pos (m t : ℝ) :
    0 < (euclidMoment (scalarK m) 1 1 [(t, 1)]).re := by
  rw [euclidMoment_scalarK, Complex.ofReal_re]
  exact Real.exp_pos _

/-- The free one-mode moment has **nontrivial time dependence**: for a nonzero mass the
moment at Euclidean time `1` differs from the moment at time `0`. -/
theorem scalarMoment_ne_one (m : ℝ) (hm : m ≠ 0) :
    euclidMoment (scalarK m) 1 1 [(1, 1)] ≠ euclidMoment (scalarK m) 1 1 [(0, 1)] := by
  rw [euclidMoment_scalarK, euclidMoment_scalarK]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  intro h
  have h' : Real.exp (-(1 * m)) = 1 := by exact_mod_cast h
  have hzero : -(1 * m) = 0 := (Real.exp_eq_one_iff (-(1 * m))).mp h'
  exact hm (by linarith)

/-! ## 4. Separated-time two-point functions -/

/-- The **separated-time two-point function** of the hierarchy: `A` inserted at time `0`,
`B` inserted at the later time `h`, i.e. `⟨Ω, A e^{-hK} B Ω⟩`.  `h` is the time gap, and on
this convention `A` is the earlier insertion. -/
def twoPoint (K : E →L[ℂ] E) (Ω : E) (A B : E →L[ℂ] E) (h : ℝ) : ℂ :=
  euclidMoment K Ω A [(h, B)]

theorem twoPoint_eq (K : E →L[ℂ] E) (Ω : E) (A B : E →L[ℂ] E) (h : ℝ) :
    twoPoint K Ω A B h = ⟪Ω, A (euclidEvol K h (B Ω))⟫_ℂ := by
  simp [twoPoint, euclidMoment, euclidWord, ContinuousLinearMap.mul_apply]

/-- At zero separation the two insertions sit at the same time. -/
theorem twoPoint_zero (K : E →L[ℂ] E) (Ω : E) (A B : E →L[ℂ] E) :
    twoPoint K Ω A B 0 = ⟪Ω, A (B Ω)⟫_ℂ := by
  rw [twoPoint_eq, euclidEvol_zero, ContinuousLinearMap.one_apply]

/-- **Coincident-time square**: the two-point function of an observable with its adjoint at
zero separation is `‖A Ω‖²`.  The separated-time form below generalizes this. -/
theorem twoPoint_adjoint_zero (K : E →L[ℂ] E) (Ω : E) (A : E →L[ℂ] E) :
    twoPoint K Ω (ContinuousLinearMap.adjoint A) A 0 = ((‖A Ω‖ ^ 2 : ℝ) : ℂ) :=
  euclidMoment_zero_adjoint K Ω A

/-- The two-point function at separation `h` is the moment of the **appended word**:
splitting a word at a gap is composing with `e^{-hK}` and the later insertion. -/
theorem twoPoint_eq_euclidMoment (K : E →L[ℂ] E) (Ω : E) (A B : E →L[ℂ] E) (h : ℝ) :
    twoPoint K Ω A B h = euclidMoment K Ω A [(h, B)] := rfl

/-! ## 5. Reflection positivity of the separated-time form -/

/-- The moment of an **adjoint insertion paired with a later one** unfolds to the inner
product `⟪A Ω, e^{-(s+t)K} (B Ω)⟫`; this is the entry that time reflection produces. -/
theorem euclidMoment_adjoint_pair (K : E →L[ℂ] E) (Ω : E) (A B : E →L[ℂ] E) (s t : ℝ) :
    euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + t, B)]
      = ⟪A Ω, euclidEvol K (s + t) (B Ω)⟫_ℂ := by
  unfold euclidMoment euclidWord
  simp only [euclidWord, ContinuousLinearMap.mul_apply]
  rw [ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ) (A := A) (x := Ω)
    (y := euclidEvol K (s + t) (B Ω))]

/-- **Inner-product symmetry of a self-adjoint Euclidean evolution**. -/
theorem inner_euclidEvol_selfAdjoint (K : E →L[ℂ] E) {s : ℝ}
    (hT : IsSelfAdjoint (euclidEvol K s)) (x y : E) :
    ⟪euclidEvol K s x, y⟫_ℂ = ⟪x, euclidEvol K s y⟫_ℂ := by
  have hadj : ContinuousLinearMap.adjoint (euclidEvol K s) = euclidEvol K s :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hT
  rw [← ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ) (A := euclidEvol K s) (x := x)
    (y := y), hadj]

/-- A **self-adjoint generator** has a self-adjoint Euclidean evolution: the exponent
`-(t : ℂ) • K` is self-adjoint for real `t`, and `exp` preserves self-adjointness. -/
theorem euclidEvol_isSelfAdjoint (K : E →L[ℂ] E) (hK : IsSelfAdjoint K) (s : ℝ) :
    IsSelfAdjoint (euclidEvol K s) := by
  have hs : IsSelfAdjoint ((-(s : ℂ)) • K) := by
    refine IsSelfAdjoint.smul (r := (-(s : ℂ))) (x := K) ?_ hK
    rw [isSelfAdjoint_iff]
    simp
  unfold euclidEvol
  exact IsSelfAdjoint.exp (x := (-(s : ℂ)) • K) hs

/-- **The reflected two-point moment is an inner product of evolved vectors** — the
regulator-level form of `⟨θ F, F⟩`.  For real times `s`, `t` the adjoint insertion at `s`
paired with the insertion at `t` is `⟪e^{-sK}(A Ω), e^{-tK}(B Ω)⟫`. -/
theorem euclidMoment_adjoint_eq_inner (K : E →L[ℂ] E) (Ω : E) (A B : E →L[ℂ] E)
    (s t : ℝ) (hS : IsSelfAdjoint (euclidEvol K s)) :
    euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + t, B)]
      = ⟪euclidEvol K s (A Ω), euclidEvol K t (B Ω)⟫_ℂ := by
  rw [euclidMoment_adjoint_pair (K := K) (Ω := Ω) (A := A) (B := B) (s := s) (t := t),
    euclidEvol_add, ContinuousLinearMap.mul_apply]
  exact (inner_euclidEvol_selfAdjoint K hS (A Ω) _).symm

/-- The **reflected vector** of a finite family of positive-time insertions:
`Σᵢ e^{-sᵢK}(Aᵢ Ω)`.  It is the vector whose norm square is the reflected (OS) form. -/
def reflectedVector (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι]
    (f : ι → ℝ × (E →L[ℂ] E)) : E :=
  ∑ i, euclidEvol K (f i).1 ((f i).2 Ω)

/-- The **reflected (OS) form** of a finite family of insertions: the adjoint of each
insertion at its time `sᵢ` paired with every insertion at `sⱼ`, i.e.
`Σᵢ Σⱼ ⟨Aᵢ Ω, e^{-(sᵢ+sⱼ)K} Aⱼ Ω⟩`.  Time reflection sends `Aᵢ` at `+sᵢ` to `Aᵢ†` at `-sᵢ`,
so the exponent is the sum of the two positive times. -/
def reflectedForm (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι]
    (f : ι → ℝ × (E →L[ℂ] E)) : ℂ :=
  ∑ i, ∑ j, euclidMoment K Ω (ContinuousLinearMap.adjoint (f i).2)
    [((f i).1 + (f j).1, (f j).2)]

/-- **The reflected form is a squared norm.**  This is the reflection-positivity statement
at the regulator: with a self-adjoint generator the doubly-summed separated-time form
collapses to `‖Σᵢ e^{-sᵢK}(Aᵢ Ω)‖²`, with no degree restriction on the observables. -/
theorem reflectedForm_eq_inner (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι]
    (f : ι → ℝ × (E →L[ℂ] E)) (hK : IsSelfAdjoint K) :
    reflectedForm K Ω f = ⟪reflectedVector K Ω f, reflectedVector K Ω f⟫_ℂ := by
  have hterm : ∀ i j : ι, euclidMoment K Ω (ContinuousLinearMap.adjoint (f i).2)
      [((f i).1 + (f j).1, (f j).2)]
      = ⟪euclidEvol K (f i).1 ((f i).2 Ω), euclidEvol K (f j).1 ((f j).2 Ω)⟫_ℂ :=
    fun i j => euclidMoment_adjoint_eq_inner K Ω _ _ _ _
      (euclidEvol_isSelfAdjoint K hK _)
  simp only [reflectedForm, reflectedVector, hterm]
  rw [sum_inner]
  simp only [inner_sum]

/-- The real part of `↑r ^ 2` is the nonnegative number `r ^ 2`. -/
theorem ofReal_sq_re (r : ℝ) : (((r : ℂ) ^ 2)).re = r ^ 2 := by
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem ofReal_sq_re_nonneg (r : ℝ) : 0 ≤ (((r : ℂ) ^ 2)).re := by
  rw [ofReal_sq_re]
  positivity

/-- **Reflection positivity at the regulator**: the reflected form has nonnegative real
part, for every finite family of insertions at arbitrary (positive or negative) times, and
for every bounded observable. -/
theorem reflectedForm_re_nonneg (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι]
    (f : ι → ℝ × (E →L[ℂ] E)) (hK : IsSelfAdjoint K) :
    0 ≤ (reflectedForm K Ω f).re := by
  rw [reflectedForm_eq_inner K Ω f hK, inner_self_eq_norm_sq_to_K]
  exact ofReal_sq_re_nonneg _

/-- **Reflection positivity of two separated-time insertions, explicitly.**  For a
self-adjoint generator the four-term reflected form of insertions at times `s` and `t` is the
squared norm of `e^{-sK}(A Ω) + e^{-tK}(B Ω)`.  The cross terms are the separated-time
two-point functions `⟨A† e^{-(s+t)K} B⟩`, so this is exactly OS positivity of the two-point
function at the regulator. -/
theorem twoPoint_reflected_eq_normSq (K : E →L[ℂ] E) (Ω : E) (A B : E →L[ℂ] E)
    (s t : ℝ) (hK : IsSelfAdjoint K) :
    euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + s, A)]
        + euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + t, B)]
        + euclidMoment K Ω (ContinuousLinearMap.adjoint B) [(t + s, A)]
        + euclidMoment K Ω (ContinuousLinearMap.adjoint B) [(t + t, B)]
      = ((‖euclidEvol K s (A Ω) + euclidEvol K t (B Ω)‖ ^ 2 : ℝ) : ℂ) := by
  have hS := euclidEvol_isSelfAdjoint K hK s
  have hT := euclidEvol_isSelfAdjoint K hK t
  set x := euclidEvol K s (A Ω)
  set y := euclidEvol K t (B Ω)
  have h1 : euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + s, A)] = ⟪x, x⟫_ℂ :=
    euclidMoment_adjoint_eq_inner K Ω A A s s hS
  have h2 : euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + t, B)] = ⟪x, y⟫_ℂ :=
    euclidMoment_adjoint_eq_inner K Ω A B s t hS
  have h3 : euclidMoment K Ω (ContinuousLinearMap.adjoint B) [(t + s, A)] = ⟪y, x⟫_ℂ :=
    euclidMoment_adjoint_eq_inner K Ω B A t s hT
  have h4 : euclidMoment K Ω (ContinuousLinearMap.adjoint B) [(t + t, B)] = ⟪y, y⟫_ℂ :=
    euclidMoment_adjoint_eq_inner K Ω B B t t hT
  have hnorm : ⟪x + y, x + y⟫_ℂ = ((‖x + y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [h1, h2, h3, h4, ← hnorm, inner_add_left, inner_add_right, inner_add_right]
  ring

/-- **Reflection positivity of two separated-time insertions**: the real part of the
four-term form is nonnegative. -/
theorem twoPoint_reflected_re_nonneg (K : E →L[ℂ] E) (Ω : E) (A B : E →L[ℂ] E)
    (s t : ℝ) (hK : IsSelfAdjoint K) :
    0 ≤ (euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + s, A)]
        + euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + t, B)]
        + euclidMoment K Ω (ContinuousLinearMap.adjoint B) [(t + s, A)]
        + euclidMoment K Ω (ContinuousLinearMap.adjoint B) [(t + t, B)]).re := by
  rw [twoPoint_reflected_eq_normSq K Ω A B s t hK, Complex.ofReal_re]
  positivity

/-- The free one-mode regulator is **self-adjoint**: its generator is a real multiple of the
identity. -/
theorem scalarK_isSelfAdjoint (m : ℝ) : IsSelfAdjoint (scalarK m) := by
  unfold scalarK
  refine IsSelfAdjoint.smul (r := (m : ℂ)) (x := (1 : ℂ →L[ℂ] ℂ)) ?_ ?_
  · rw [isSelfAdjoint_iff]
    simp
  · rw [isSelfAdjoint_iff]
    simp

/-- **Reflection positivity of the free regulator** follows from the general statement. -/
theorem reflectedForm_scalarK_re_nonneg {ι : Type*} [Fintype ι] (m : ℝ)
    (f : ι → ℝ × (ℂ →L[ℂ] ℂ)) : 0 ≤ (reflectedForm (scalarK m) 1 f).re :=
  reflectedForm_re_nonneg (scalarK m) 1 f (scalarK_isSelfAdjoint m)

/-! ## 6. The reflected form as a positive semidefinite form

Reflection positivity gives nonnegativity on the diagonal.  What the Euclidean
reconstruction needs next is the structure that nonnegativity buys: the reflected form is a
**sesquilinear** form, its null space is exactly the kernel of the reflected vector (so the
quotient by null vectors is well posed), and it satisfies **Cauchy–Schwarz**.  At the
regulator this is the whole of the first reconstruction step: no degree restriction and no
measure theory is involved, because the form *is* an inner product already.
-/

/-- The **reflected pairing** of two finite families of insertions: the adjoint of each
insertion of `f` at its time `sᵢ` paired with each insertion of `g` at its time `tⱼ`.
`reflectedPair K Ω f f` is the reflected form of `f`. -/
def reflectedPair (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℝ × (E →L[ℂ] E)) (g : κ → ℝ × (E →L[ℂ] E)) : ℂ :=
  ∑ i, ∑ j, euclidMoment K Ω (ContinuousLinearMap.adjoint (f i).2)
    [((f i).1 + (g j).1, (g j).2)]

/-- The reflected pairing of a family with itself is its reflected form. -/
theorem reflectedPair_self (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι]
    (f : ι → ℝ × (E →L[ℂ] E)) : reflectedPair K Ω f f = reflectedForm K Ω f := rfl

/-- **The reflected pairing is the inner product of the reflected vectors.** -/
theorem reflectedPair_eq_inner (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℝ × (E →L[ℂ] E)) (g : κ → ℝ × (E →L[ℂ] E)) (hK : IsSelfAdjoint K) :
    reflectedPair K Ω f g = ⟪reflectedVector K Ω f, reflectedVector K Ω g⟫_ℂ := by
  have hterm : ∀ (i : ι) (j : κ), euclidMoment K Ω (ContinuousLinearMap.adjoint (f i).2)
      [((f i).1 + (g j).1, (g j).2)]
      = ⟪euclidEvol K (f i).1 ((f i).2 Ω), euclidEvol K (g j).1 ((g j).2 Ω)⟫_ℂ :=
    fun i j => euclidMoment_adjoint_eq_inner K Ω _ _ _ _
      (euclidEvol_isSelfAdjoint K hK _)
  simp only [reflectedPair, reflectedVector, hterm]
  rw [sum_inner]
  simp only [inner_sum]

/-- **The reflected pairing is conjugate-symmetric.** -/
theorem reflectedPair_conj_swap (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → ℝ × (E →L[ℂ] E)) (g : κ → ℝ × (E →L[ℂ] E)) (hK : IsSelfAdjoint K) :
    reflectedPair K Ω g f = (starRingEnd ℂ) (reflectedPair K Ω f g) := by
  rw [reflectedPair_eq_inner K Ω g f hK, reflectedPair_eq_inner K Ω f g hK, inner_conj_symm]

/-- The real part of the reflected form is the **squared norm** of the reflected vector. -/
theorem reflectedForm_re_eq_normSq (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι]
    (f : ι → ℝ × (E →L[ℂ] E)) (hK : IsSelfAdjoint K) :
    (reflectedForm K Ω f).re = ‖reflectedVector K Ω f‖ ^ 2 := by
  rw [reflectedForm_eq_inner K Ω f hK]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

/-- **The null space of the reflected form is the kernel of the reflected vector**: a family
whose reflected form vanishes reflects to the zero vector.  This is what makes the
reconstructed inner product well defined on the quotient by null families. -/
theorem reflectedForm_eq_zero_iff (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι]
    (f : ι → ℝ × (E →L[ℂ] E)) (hK : IsSelfAdjoint K) :
    reflectedForm K Ω f = 0 ↔ reflectedVector K Ω f = 0 := by
  rw [reflectedForm_eq_inner K Ω f hK, inner_self_eq_zero]

/-- **Null families pair to zero with everything**: the reflected pairing descends to the
quotient by the null space of the reflected form. -/
theorem reflectedPair_eq_zero_of_null (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (f : ι → ℝ × (E →L[ℂ] E)) (g : κ → ℝ × (E →L[ℂ] E)) (hK : IsSelfAdjoint K)
    (hf : reflectedForm K Ω f = 0) : reflectedPair K Ω f g = 0 := by
  rw [reflectedPair_eq_inner K Ω f g hK, (reflectedForm_eq_zero_iff K Ω f hK).1 hf,
    inner_zero_left]

/-- **Cauchy–Schwarz for the reflected pairing.**  This is the inequality that turns
reflection positivity into a usable positive semidefinite inner product: the reflected
pairing of two families is bounded by the geometric mean of their reflected forms. -/
theorem reflectedPair_cauchy_schwarz (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (f : ι → ℝ × (E →L[ℂ] E)) (g : κ → ℝ × (E →L[ℂ] E)) (hK : IsSelfAdjoint K) :
    ‖reflectedPair K Ω f g‖
      ≤ Real.sqrt (reflectedForm K Ω f).re * Real.sqrt (reflectedForm K Ω g).re := by
  rw [reflectedPair_eq_inner K Ω f g hK, reflectedForm_re_eq_normSq K Ω f hK,
    reflectedForm_re_eq_normSq K Ω g hK, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm _ _

/-- **Cauchy–Schwarz for the two-point function**, the distinguished consequence of
reflection positivity: the squared separated-time correlation is bounded by the product of
the two coincident-time squares.  Equivalently, the two-by-two reflected matrix of the pair
of insertions is positive semidefinite. -/
theorem twoPoint_cauchy_schwarz (K : E →L[ℂ] E) (Ω : E) (A B : E →L[ℂ] E) (s t : ℝ)
    (hK : IsSelfAdjoint K) :
    ‖euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + t, B)]‖ ^ 2
      ≤ (euclidMoment K Ω (ContinuousLinearMap.adjoint A) [(s + s, A)]).re
        * (euclidMoment K Ω (ContinuousLinearMap.adjoint B) [(t + t, B)]).re := by
  have hS := euclidEvol_isSelfAdjoint K hK s
  have hT := euclidEvol_isSelfAdjoint K hK t
  rw [euclidMoment_adjoint_eq_inner K Ω A B s t hS,
    euclidMoment_adjoint_eq_inner K Ω A A s s hS,
    euclidMoment_adjoint_eq_inner K Ω B B t t hT]
  have hx : (⟪euclidEvol K s (A Ω), euclidEvol K s (A Ω)⟫_ℂ).re
      = ‖euclidEvol K s (A Ω)‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hy : (⟪euclidEvol K t (B Ω), euclidEvol K t (B Ω)⟫_ℂ).re
      = ‖euclidEvol K t (B Ω)‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [hx, hy]
  have h := norm_inner_le_norm (𝕜 := ℂ) (euclidEvol K s (A Ω)) (euclidEvol K t (B Ω))
  have h2 := mul_self_le_mul_self (norm_nonneg (⟪euclidEvol K s (A Ω),
    euclidEvol K t (B Ω)⟫_ℂ)) h
  nlinarith [h2, sq_nonneg (‖euclidEvol K s (A Ω)‖ : ℝ),
    sq_nonneg (‖euclidEvol K t (B Ω)‖ : ℝ)]

/-! ## 7. The pre-Hilbert space of the reconstruction

Sections 5 and 6 prove that the reflected form is nonnegative and that its null families
pair to zero with everything.  Here that observation is upgraded to the reconstruction
statement itself: the reflected pairing of two families is the inner product of an
explicitly given **linear map** into the ambient Hilbert space, so the quotient by null
families carries a genuine inner product — namely the restriction of the ambient one to
the range of the reconstruction map — and the class norm is the ambient norm.
-/

/-- The **reflected vector** of a family whose insertion times are kept separate from its
operators: `Σᵢ e^{-sᵢK}(Aᵢ Ω)`.  Separating `s` from `A` is what lets the operators carry a
vector-space structure, so that the reconstruction becomes a linear map. -/
def familyVector (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (A : ι → E →L[ℂ] E) : E :=
  ∑ i, euclidEvol K (s i) (A i Ω)

/-- The reflected vector is additive in the operators. -/
theorem familyVector_add (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (A B : ι → E →L[ℂ] E) :
    familyVector K Ω s (A + B) = familyVector K Ω s A + familyVector K Ω s B := by
  simp only [familyVector, Pi.add_apply, ContinuousLinearMap.add_apply, map_add,
    Finset.sum_add_distrib]

/-- The reflected vector is complex-homogeneous in the operators. -/
theorem familyVector_smul (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (c : ℂ) (A : ι → E →L[ℂ] E) :
    familyVector K Ω s (c • A) = c • familyVector K Ω s A := by
  simp only [familyVector, Pi.smul_apply, ContinuousLinearMap.smul_apply, map_smul,
    Finset.smul_sum]

/-- **The reconstruction map**: families of operators at fixed insertion times map linearly
into the ambient Hilbert space. -/
def familyVectorLM (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι] (s : ι → ℝ) :
    (ι → E →L[ℂ] E) →ₗ[ℂ] E where
  toFun := familyVector K Ω s
  map_add' := familyVector_add K Ω s
  map_smul' := familyVector_smul K Ω s

/-- **The reflected pairing of two families**, as the inner product of their reflected
vectors. -/
def familyPair (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → ℝ) (A : ι → E →L[ℂ] E) (t : κ → ℝ) (B : κ → E →L[ℂ] E) : ℂ :=
  ⟪familyVector K Ω s A, familyVector K Ω t B⟫_ℂ

/-- A family of insertions as a function of index type, so that the pairing of section 6 and
the pairing of this section are literally the same object. -/
def toInsertions {ι : Type*} (s : ι → ℝ) (A : ι → E →L[ℂ] E) : ι → ℝ × (E →L[ℂ] E) :=
  fun i => (s i, A i)

/-- **Compatibility with section 6**: the pairing of the insertion families is the
section-6 reflected pairing of the same families. -/
theorem familyPair_eq_reflectedPair (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (s : ι → ℝ) (A : ι → E →L[ℂ] E) (t : κ → ℝ) (B : κ → E →L[ℂ] E)
    (hK : IsSelfAdjoint K) :
    familyPair K Ω s A t B = reflectedPair K Ω (toInsertions s A) (toInsertions t B) := by
  rw [reflectedPair_eq_inner K Ω (toInsertions s A) (toInsertions t B) hK]
  rfl

/-- The pairing is additive in its first family. -/
theorem familyPair_add_left (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → ℝ) (A A' : ι → E →L[ℂ] E) (t : κ → ℝ) (B : κ → E →L[ℂ] E) :
    familyPair K Ω s (A + A') t B = familyPair K Ω s A t B + familyPair K Ω s A' t B := by
  simp only [familyPair, familyVector_add, inner_add_left]

/-- The pairing is additive in its second family. -/
theorem familyPair_add_right (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : ι → ℝ) (A : ι → E →L[ℂ] E) (t : κ → ℝ) (B B' : κ → E →L[ℂ] E) :
    familyPair K Ω s A t (B + B') = familyPair K Ω s A t B + familyPair K Ω s A t B' := by
  simp only [familyPair, familyVector_add, inner_add_right]

/-- The **reflected form** of a family in the reconstruction picture. -/
def familyForm (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (A : ι → E →L[ℂ] E) : ℂ :=
  familyPair K Ω s A s A

/-- The reflected form is the squared norm of the reflected vector. -/
theorem familyForm_eq_normSq (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (A : ι → E →L[ℂ] E) :
    familyForm K Ω s A = ((‖familyVector K Ω s A‖ : ℝ) ^ 2 : ℂ) := by
  rw [familyForm, familyPair, inner_self_eq_norm_sq_to_K]
  norm_num

/-- The real part of the reflected form is the squared norm, hence nonnegative. -/
theorem familyForm_re_nonneg (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (A : ι → E →L[ℂ] E) : 0 ≤ (familyForm K Ω s A).re := by
  rw [familyForm_eq_normSq]
  exact ofReal_sq_re_nonneg _

/-- **Positive definiteness modulo null families**: a family has zero reflected form exactly
when its reflected vector vanishes. -/
theorem familyForm_eq_zero_iff (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (A : ι → E →L[ℂ] E) :
    familyForm K Ω s A = 0 ↔ familyVector K Ω s A = 0 := by
  simp only [familyForm, familyPair, inner_self_eq_zero]

/-- Null families pair to zero with every family, so the pairing is a function of the class
of the reflected vector. -/
theorem familyPair_eq_zero_of_null (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (s : ι → ℝ) (A : ι → E →L[ℂ] E) (t : κ → ℝ) (B : κ → E →L[ℂ] E)
    (hA : familyForm K Ω s A = 0) : familyPair K Ω s A t B = 0 := by
  rw [familyPair, (familyForm_eq_zero_iff K Ω s A).1 hA, inner_zero_left]

/-- **The class pairing depends only on the reflected vectors.**  Two families with the same
reflected vector — i.e. the same class modulo null families — pair identically. -/
theorem familyPair_congr_left {K : E →L[ℂ] E} {Ω : E} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {s : ι → ℝ} {A A' : ι → E →L[ℂ] E} {t : κ → ℝ} {B : κ → E →L[ℂ] E}
    (h : familyVector K Ω s A = familyVector K Ω s A') :
    familyPair K Ω s A t B = familyPair K Ω s A' t B := by
  rw [familyPair, familyPair, h]

/-- **The class form is the ambient squared norm**, i.e. the reconstruction is isometric on
the quotient: the class norm of a family is the norm of its reflected vector. -/
theorem familyForm_sub_re_eq_dist_sq (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (A A' : ι → E →L[ℂ] E) :
    (familyForm K Ω s (A - A')).re
      = ‖familyVector K Ω s A - familyVector K Ω s A'‖ ^ 2 := by
  have h : familyVector K Ω s (A - A')
      = familyVector K Ω s A - familyVector K Ω s A' :=
    (familyVectorLM K Ω s).map_sub A A'
  rw [familyForm_eq_normSq, h, ofReal_sq_re]

/-- **Cauchy–Schwarz for the reflected pairing of families.** -/
theorem familyPair_cauchy_schwarz (K : E →L[ℂ] E) (Ω : E) {ι κ : Type*} [Fintype ι]
    [Fintype κ] (s : ι → ℝ) (A : ι → E →L[ℂ] E) (t : κ → ℝ) (B : κ → E →L[ℂ] E) :
    ‖familyPair K Ω s A t B‖
      ≤ Real.sqrt (familyForm K Ω s A).re * Real.sqrt (familyForm K Ω t B).re := by
  rw [familyPair, familyForm_eq_normSq, familyForm_eq_normSq, ofReal_sq_re, ofReal_sq_re,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact norm_inner_le_norm _ _

/-- **The reflection-positive reconstruction at the regulator.**  The reflected pairing of
families is the inner product of their images under a complex-linear map, the kernel of that
map is exactly the null families, the diagonal is nonnegative, and the pairing obeys
Cauchy–Schwarz.  Taken together these are the axioms of an inner product on the quotient of
families by null families, realized isometrically inside the regulator Hilbert space. -/
theorem reflected_reconstruction (K : E →L[ℂ] E) (Ω : E) {ι : Type*} [Fintype ι]
    (s : ι → ℝ) (A : ι → E →L[ℂ] E) :
    (∀ B, familyPair K Ω s A s B = ⟪familyVector K Ω s A, familyVector K Ω s B⟫_ℂ) ∧
    (familyForm K Ω s A = 0 ↔ familyVector K Ω s A = 0) ∧
    (0 ≤ (familyForm K Ω s A).re) ∧
    (∀ B, ‖familyPair K Ω s A s B‖
      ≤ Real.sqrt (familyForm K Ω s A).re * Real.sqrt (familyForm K Ω s B).re) :=
  ⟨fun _ => rfl, familyForm_eq_zero_iff K Ω s A, familyForm_re_nonneg K Ω s A,
    fun B => familyPair_cauchy_schwarz K Ω s A s B⟩

end BookProof.OSReconstruction
