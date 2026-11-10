import BookProof.Toolbox.ChapterFarisLavineCore

/-!
# Analytic vectors, and Nelson's criterion in the geometrically bounded form

Nelson's analytic-vector theorem says that a symmetric operator with a dense set of
analytic vectors is essentially self-adjoint.  This module formalizes the notions and the
part of the argument the corpus can prove today, on top of the Faris–Lavine instrument
`BookProof.Toolbox.ChapterFarisLavineCore` — in particular its deficiency propagation
lemmas `dense_range_of_deficiencyTrivialAt` and `deficiencyTrivialAt_of_dense_range`, which
convert "the deficiency space vanishes at *one* point off the real axis" into essential
self-adjointness.

## What is here

* `InvariantOn`, `orbitD`, `orbit` — the iterates of a partially defined operator `T` on a
  domain `D`, which only exist when `T` maps `D` into itself.
* `IsGeometric T x r` — the *geometric* bound `‖Tⁿx‖ ≤ C rⁿ`.  `IsAnalytic T x` — the
  analytic-vector condition `Σ rⁿ/n! ‖Tⁿx‖ < ∞` for some `r > 0`.  The first implies the
  second (`isAnalytic_of_isGeometric`): a power series with a geometric bound converges
  with any radius.
* `inner_orbit` — the cheap but decisive identity: if `w` is a deficiency vector at `z`,
  then `⟪Tⁿx, w⟫ = zⁿ ⟪x, w⟫` for every analytic vector `x`.
* `inner_eq_zero_of_isGeometric` — hence `x ⟂ w` whenever the geometric ratio of `x` is
  smaller than `|z|`.
* `deficiencyTrivialAt_of_dense_geometric` — a dense set of geometrically bounded vectors
  with a **common radius** `r` kills the deficiency space at every `z` with `|z| > r`.
* `essentiallySelfAdjointOn_of_dense_geometric` — **Nelson's criterion** for such a set, on
  a complete space, by propagating from `±d i` (`d > r`) to `±i` with the Faris–Lavine
  propagation lemma.
* `IsVectorOfUniqueness`, `inner_eq_zero_of_isVectorOfUniqueness`,
  `deficiencyTrivialAt_of_dense_vectorsOfUniqueness` and
  `essentiallySelfAdjointOn_of_dense_vectorsOfUniqueness` — Nussbaum's reduction, the route
  that actually reaches a dense set of analytic vectors: a dense set of vectors each of which
  lies in the closure of the range of `T ∓ i` already forces essential self-adjointness, with
  no radius anywhere.
* `essentiallySelfAdjointOn_of_dense_eigenvectors` — the sharper elementary criterion a
  dense set of *eigenvectors with real eigenvalues* gives.  Symmetry is not even needed:
  the eigenvalue relation at a real `λ` forces `λ = z` at a deficiency point `z`.

## Honest boundary

The classical statement allows a *different* radius for each vector, and **that step cannot
be made by a deficiency estimate**.  The reason is arithmetic, not missing API: the only
decay in `|⟪x, w⟫| ≤ ‖Tⁿx‖/|z|ⁿ` comes from the geometric bound, whereas an analytic vector
has the factorial bound `‖Tⁿx‖ ≤ C n!/ρⁿ`, for which `C n!/|z|ⁿ` *grows* at every fixed `z`.
Deficiency-index constancy is no help either: it transports triviality between points of a
half plane once one point is known, and it cannot produce the first point when the radii are
unbounded.  (The orthogonality lemma needs `r < ‖z‖`, so a common radius is genuinely
required by that argument.)

So the per-vector statement is reached instead through Nussbaum's reduction, proved in the
section above: analyticity is used only to put each vector in the closure of the range of
`T ∓ i`, which is Carleman's criterion (Simon, *The classical moment problem as a
self-adjoint finite difference operator*, Cor. 2.16 — an analytic or quasi-analytic vector
is a vector of uniqueness).  Carleman's determinacy argument is the one ingredient the
corpus does not have; everything after it is proved here, and
`essentiallySelfAdjointOn_of_dense_geometric` remains the strictly weaker geometric
statement.

For a concrete operator with a complete eigenbasis — which is the case that matters for
`gaussDirichlet`, whose Hermite eigenfunctions are explicit — the criterion at the end of
this file is both stronger than the geometric one and far cheaper: no summability, no
propagation.  The hypothesis is that the *span* of the eigenvectors with real eigenvalues is
dense, not that the eigenvectors themselves are dense.  The difference is not cosmetic: for
a simple spectrum the union of the eigenlines is nowhere near dense (in the complexification
of a real operator each eigenspace is a line `ℂ • v_n`), while the span of a complete
eigenbasis is everything.  `essentiallySelfAdjointOn_of_dense_eigenvectors` keeps the
weaker dense-set hypothesis for the cases where it does hold; the spectral argument uses
`essentiallySelfAdjointOn_of_dense_span_eigenvectors`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NelsonAnalytic

open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

/-! ## Iterates of a partially defined operator -/

/-- `T` maps its domain into itself, so that all iterates of `T` are defined. -/
def InvariantOn (T : D →ₗ[ℂ] F) : Prop := ∀ x : D, T x ∈ D

/-- The `n`-th iterate of `T`, carried along inside the domain. -/
def orbitD (T : D →ₗ[ℂ] F) (hT : InvariantOn T) : ℕ → D → D
  | 0, x => x
  | n + 1, x => ⟨T (orbitD T hT n x), hT _⟩

/-- The zeroth iterate is the vector itself. -/
@[simp] theorem orbitD_zero (T : D →ₗ[ℂ] F) (hT : InvariantOn T) (x : D) :
    orbitD T hT 0 x = x := rfl

/-- One step of the recursion: the next iterate is `T` applied to the previous one. -/
theorem orbitD_succ (T : D →ₗ[ℂ] F) (hT : InvariantOn T) (n : ℕ) (x : D) :
    orbitD T hT (n + 1) x = ⟨T (orbitD T hT n x), hT (orbitD T hT n x)⟩ := rfl

/-- The `n`-th iterate, seen as an element of the Hilbert space. -/
def orbit (T : D →ₗ[ℂ] F) (hT : InvariantOn T) (n : ℕ) (x : D) : F :=
  (orbitD T hT n x : F)

/-- The zeroth iterate in the space is the vector itself. -/
@[simp] theorem orbit_zero (T : D →ₗ[ℂ] F) (hT : InvariantOn T) (x : D) :
    orbit T hT 0 x = (x : F) := rfl

/-- One step of the recursion, in the space. -/
theorem orbit_succ (T : D →ₗ[ℂ] F) (hT : InvariantOn T) (n : ℕ) (x : D) :
    orbit T hT (n + 1) x = T (orbitD T hT n x) := rfl

/-! ## The two notions of growth -/

/-- **A geometrically bounded orbit**: `‖Tⁿx‖ ≤ C rⁿ` for a constant `C` and all `n`.  This
is the quantitative input the deficiency argument actually consumes. -/
def IsGeometric (T : D →ₗ[ℂ] F) (hT : InvariantOn T) (x : D) (r : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ‖orbit T hT n x‖ ≤ C * r ^ n

/-- **An analytic vector** (Nelson): the exponential-type series `Σ rⁿ/n! ‖Tⁿx‖` converges
for some radius `r > 0`. -/
def IsAnalytic (T : D →ₗ[ℂ] F) (hT : InvariantOn T) (x : D) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Summable (fun n : ℕ => (r ^ n / (n.factorial : ℝ)) * ‖orbit T hT n x‖)

/-- A geometric bound with ratio `r` makes `x` analytic: `Σ r₀ⁿ/n! C rⁿ = C e^{r₀ r}`.  This
is the elementary direction, and the only one used below. -/
theorem isAnalytic_of_isGeometric {T : D →ₗ[ℂ] F} {hT : InvariantOn T} {x : D} {r : ℝ}
    (hr : 0 < r) (h : IsGeometric T hT x r) : IsAnalytic T hT x := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hC 0)
  refine ⟨r, hr, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_pow_div_factorial (r * r)).mul_left C)
  have hn : (0 : ℝ) ≤ r ^ n / (n.factorial : ℝ) := by positivity
  calc (r ^ n / (n.factorial : ℝ)) * ‖orbit T hT n x‖
      ≤ (r ^ n / (n.factorial : ℝ)) * (C * r ^ n) :=
        mul_le_mul_of_nonneg_left (hC n) hn
    _ = C * ((r * r) ^ n / (n.factorial : ℝ)) := by
        rw [mul_pow]
        field_simp

/-! ## The deficiency identity and its consequence -/

/-- **The orbit identity.**  If `w` is a deficiency vector of `T` at `z` — that is,
`⟪T v, w⟫ = z ⟪v, w⟫` for all `v` in the domain — then the whole orbit of `x` inherits it:
`⟪Tⁿx, w⟫ = zⁿ ⟪x, w⟫`. -/
theorem inner_orbit {T : D →ₗ[ℂ] F} {hT : InvariantOn T} {z : ℂ} {w : F}
    (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = z * inner ℂ (v : F) w) (n : ℕ) (x : D) :
    (inner ℂ (orbit T hT n x) w : ℂ) = z ^ n * inner ℂ (x : F) w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orbit_succ, hw (orbitD T hT n x)]
    have hdef : ((orbitD T hT n x : D) : F) = orbit T hT n x := rfl
    rw [hdef, ih, pow_succ]
    ring

/-- **A geometrically bounded vector is orthogonal to every deficiency vector at a point
outside its radius.**  From the orbit identity,
`|⟪x, w⟫| = |z|⁻ⁿ |⟪Tⁿx, w⟫| ≤ C ‖w‖ (r/|z|)ⁿ → 0`. -/
theorem inner_eq_zero_of_isGeometric {T : D →ₗ[ℂ] F} {hT : InvariantOn T} {x : D} {r : ℝ}
    (hr : 0 ≤ r) (hC : IsGeometric T hT x r) {z : ℂ} {w : F}
    (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = z * inner ℂ (v : F) w) (hz : r < ‖z‖) :
    (inner ℂ (x : F) w : ℂ) = 0 := by
  obtain ⟨C, hC⟩ := hC
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hz
    linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hq0 : 0 ≤ r / ‖z‖ := div_nonneg hr hzn.le
  have hq1 : r / ‖z‖ < 1 := (div_lt_one hzn).mpr hz
  have hbound : ∀ n : ℕ, ‖(inner ℂ (x : F) w : ℂ)‖ ≤ C * ‖w‖ * (r / ‖z‖) ^ n := by
    intro n
    have hid : (inner ℂ (x : F) w : ℂ)
        = (z ^ n)⁻¹ * inner ℂ (orbit T hT n x) w := by
      rw [inner_orbit hw n x, inv_mul_cancel_left₀ (pow_ne_zero n hz0)]
    calc ‖(inner ℂ (x : F) w : ℂ)‖
        = ‖(z ^ n)⁻¹‖ * ‖(inner ℂ (orbit T hT n x) w : ℂ)‖ := by rw [hid, norm_mul]
      _ ≤ ‖(z ^ n)⁻¹‖ * (‖orbit T hT n x‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by positivity)
      _ ≤ ‖(z ^ n)⁻¹‖ * ((C * r ^ n) * ‖w‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (hC n) (norm_nonneg w)
      _ = C * ‖w‖ * (r / ‖z‖) ^ n := by
          rw [norm_inv, norm_pow, div_pow, div_eq_mul_inv]
          ring
  have hlim : Filter.Tendsto (fun n : ℕ => C * ‖w‖ * (r / ‖z‖) ^ n) Filter.atTop
      (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (C * ‖w‖)
  have hle : ‖(inner ℂ (x : F) w : ℂ)‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hbound)
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

/-! ## Nussbaum's reduction: vectors of uniqueness

Nothing above allows a *different* radius for each vector.  The reason is not an accident of
the estimates: the geometric bound is the only thing that produces decay in
`|⟪x, w⟫| ≤ ‖Tⁿx‖/|z|ⁿ`, and an analytic vector has a factorial bound
`‖Tⁿx‖ ≤ C n!/ρⁿ`, for which that quotient *grows* for every fixed `z`.  So Nelson's theorem
for per-vector radii cannot be reached by a deficiency estimate at all, and no amount of
deficiency-index constancy on the half planes helps: constancy transports triviality in `z`
once it is known at one point, it does not produce the first point.

The classical route is Nussbaum's.  Replace the estimate by a *range* statement: a vector
`x` is a vector of uniqueness when it lies in the closure of the range of `T - z`.  That
membership is what Carleman's criterion extracts from analyticity (Simon, *The classical
moment problem as a self-adjoint finite difference operator*, Cor. 2.16: an analytic or
quasi-analytic vector is a vector of uniqueness).  The step from "dense set of vectors of
uniqueness" to essential self-adjointness is elementary, and it is the content of this
section; the Carleman step is the one piece the corpus does not have, so the theorem below
is Nelson's theorem *modulo* that step, with the per-vector data living in the hypothesis
rather than in a radius. -/

/-- `x` is a **vector of uniqueness** for `T` at the shift `z`: it lies in the closure of the
range of `T - z`.  Equivalently (see `inner_eq_zero_of_isVectorOfUniqueness`), every `w`
with `⟪T v, w⟫ = z̄ ⟪v, w⟫` is orthogonal to it. -/
def IsVectorOfUniqueness (T : D →ₗ[ℂ] F) (z : ℂ) (x : F) : Prop :=
  x ∈ closure (Set.range fun v : D => (T v : F) - z • (v : F))

/-- **A vector of uniqueness annihilates the deficiency space at the conjugate point.**  This
is the whole content of the notion: on the range of `T - z` the pairing with `w` vanishes
identically, and both sides are continuous. -/
theorem inner_eq_zero_of_isVectorOfUniqueness {T : D →ₗ[ℂ] F} {z : ℂ} {x w : F}
    (hx : IsVectorOfUniqueness T z x)
    (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = (starRingEnd ℂ z) * inner ℂ (v : F) w) :
    (inner ℂ x w : ℂ) = 0 := by
  have hclosed : IsClosed {y : F | (inner ℂ y w : ℂ) = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : (Set.range fun v : D => (T v : F) - z • (v : F))
      ⊆ {y : F | (inner ℂ y w : ℂ) = 0} := by
    rintro y ⟨v, rfl⟩
    change (inner ℂ ((T v : F) - z • (v : F)) w : ℂ) = 0
    rw [inner_sub_left, hw v, inner_smul_left]
    ring
  exact hclosed.closure_subset_iff.mpr hsub hx

/-- **A vector orthogonal to a dense set is zero**, stated for a dense subset of the space
itself rather than of the domain.  This is the form the uniqueness argument needs. -/
theorem eq_zero_of_dense_orthogonal (A : Set F) (hAdense : Dense A) {w : F}
    (h : ∀ x ∈ A, (inner ℂ x w : ℂ) = 0) : w = 0 := by
  have hsub : A ⊆ {y : F | (inner ℂ y w : ℂ) = 0} := h
  have hclosed : IsClosed {y : F | (inner ℂ y w : ℂ) = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have huniv : (Set.univ : Set F) ⊆ {y : F | (inner ℂ y w : ℂ) = 0} := by
    rw [← hAdense.closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have hself : (inner ℂ w w : ℂ) = 0 := huniv (Set.mem_univ w)
  have h4 : ((‖w‖ : ℂ)) ^ 2 = 0 := by simpa [inner_self_eq_norm_sq_to_K] using hself
  rw [← Complex.ofReal_pow] at h4
  have h5 : ‖w‖ ^ 2 = 0 := Complex.ofReal_eq_zero.mp h4
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])

/-- **Nussbaum's lemma.**  A dense set of vectors of uniqueness at `z` kills the deficiency
space of the adjoint at `z̄`.  No radius, no summability, no common constant. -/
theorem deficiencyTrivialAt_of_dense_vectorsOfUniqueness (T : D →ₗ[ℂ] F) (A : Set F)
    (hAdense : Dense A) {z : ℂ} (hA : ∀ x ∈ A, IsVectorOfUniqueness T z x) :
    DeficiencyTrivialAt D T (starRingEnd ℂ z) := by
  intro w hw
  refine eq_zero_of_dense_orthogonal A hAdense fun x hx => ?_
  exact inner_eq_zero_of_isVectorOfUniqueness (hA x hx) hw

/-- **Nelson's criterion, with a per-vector hypothesis and no radius.**  If the domain of `T`
carries a dense set of vectors, each of which is a vector of uniqueness at *both* `±i`, then
`T` is essentially self-adjoint.  This is the shape the per-vector-radius theorem takes once
the deficiency estimate is replaced by Nussbaum's reduction: the individual vector's growth
data is hidden in `IsVectorOfUniqueness`, where Carleman's criterion can supply it. -/
theorem essentiallySelfAdjointOn_of_dense_vectorsOfUniqueness (T : D →ₗ[ℂ] F) (A : Set F)
    (hAdense : Dense A)
    (hA : ∀ x ∈ A, IsVectorOfUniqueness T Complex.I x ∧
      IsVectorOfUniqueness T (-Complex.I) x) :
    EssentiallySelfAdjointOn D T := by
  have hI : DeficiencyTrivialAt D T Complex.I := by
    have := deficiencyTrivialAt_of_dense_vectorsOfUniqueness T A hAdense
      (z := -Complex.I) (fun x hx => (hA x hx).2)
    simpa using this
  have hneg : DeficiencyTrivialAt D T (-Complex.I) := by
    have := deficiencyTrivialAt_of_dense_vectorsOfUniqueness T A hAdense
      (z := Complex.I) (fun x hx => (hA x hx).1)
    simpa using this
  exact ⟨hI, hneg⟩

/-! ## Vanishing of a deficiency space from a dense set -/

/-- **A vector orthogonal to a dense set is zero.**  Bundled separately because both
criteria below end this way, and because the density is used only here. -/
theorem eq_zero_of_dense_inner_zero (A : Set D) (hAdense : Dense (((↑) : D → F) '' A))
    {w : F} (h : ∀ x ∈ A, (inner ℂ (x : F) w : ℂ) = 0) : w = 0 := by
  have hsub : (((↑) : D → F) '' A) ⊆ {y : F | (inner ℂ y w : ℂ) = 0} := by
    rintro y ⟨x, hx, rfl⟩
    exact h x hx
  have hclosed : IsClosed {y : F | (inner ℂ y w : ℂ) = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have huniv : (Set.univ : Set F) ⊆ {y : F | (inner ℂ y w : ℂ) = 0} := by
    rw [← hAdense.closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have hself : (inner ℂ w w : ℂ) = 0 := huniv (Set.mem_univ w)
  have h4 : ((‖w‖ : ℂ)) ^ 2 = 0 := by simpa [inner_self_eq_norm_sq_to_K] using hself
  rw [← Complex.ofReal_pow] at h4
  have h5 : ‖w‖ ^ 2 = 0 := Complex.ofReal_eq_zero.mp h4
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])

/-- **A dense set of geometrically bounded vectors with a common radius kills the
deficiency space at every point outside that radius.** -/
theorem deficiencyTrivialAt_of_dense_geometric (T : D →ₗ[ℂ] F) (hT : InvariantOn T)
    (A : Set D) (hAdense : Dense (((↑) : D → F) '' A))
    {r : ℝ} (hr : 0 ≤ r) (hA : ∀ x ∈ A, IsGeometric T hT x r) {z : ℂ} (hz : r < ‖z‖) :
    DeficiencyTrivialAt D T z := by
  intro w hw
  refine eq_zero_of_dense_inner_zero A hAdense fun x hx => ?_
  exact inner_eq_zero_of_isGeometric hr (hA x hx) hw hz

/-! ## Nelson's criterion -/

/-- **Nelson's analytic-vector criterion, in the geometrically bounded form.**  Let `T` be
symmetric on a domain `D` that it leaves invariant, and suppose `D` carries a dense set `A`
whose orbits share the bound `‖Tⁿx‖ ≤ C_x rⁿ` with a **single** `r ≥ 0`.  Then `T` is
essentially self-adjoint: both deficiency spaces of its adjoint vanish.

The proof takes `d = r + 1`, so `|d i| > r`; the orthogonality lemma kills the deficiency
spaces at `±d i`, `dense_range_of_deficiencyTrivialAt` turns that into density of the range
of `T - d i`, and the Faris–Lavine propagation lemma `deficiencyTrivialAt_of_dense_range`
carries the conclusion to the two points `±i` that define essential self-adjointness. -/
theorem essentiallySelfAdjointOn_of_dense_geometric [CompleteSpace F] (T : D →ₗ[ℂ] F)
    (hT : InvariantOn T) (hSym : SymmetricOn D T)
    (A : Set D) (hAdense : Dense (((↑) : D → F) '' A))
    {r : ℝ} (hr : 0 ≤ r) (hA : ∀ x ∈ A, IsGeometric T hT x r) :
    EssentiallySelfAdjointOn D T := by
  set d : ℝ := r + 1 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hdr : r < d := by rw [hd]; linarith
  have hnorm : ‖((d : ℂ) * Complex.I)‖ = d := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdpos]
  have hplus : DeficiencyTrivialAt D T ((d : ℂ) * Complex.I) :=
    deficiencyTrivialAt_of_dense_geometric T hT A hAdense hr hA (by rw [hnorm]; exact hdr)
  have hminus : DeficiencyTrivialAt D T (((-d : ℝ) : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_dense_geometric T hT A hAdense hr hA ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos hdpos]
    exact hdr
  have hconj : starRingEnd ℂ ((d : ℂ) * Complex.I) = ((-d : ℝ) : ℂ) * Complex.I := by simp
  have hdense : Dense (Set.range fun x : D => T x - ((d : ℂ) * Complex.I) • (x : F)) :=
    dense_range_of_deficiencyTrivialAt T ((d : ℂ) * Complex.I) (by rw [hconj]; exact hminus)
  refine ⟨deficiencyTrivialAt_of_dense_range T hSym d (ne_of_gt hdpos) Complex.I (by simp)
      hdense hplus,
    deficiencyTrivialAt_of_dense_range T hSym d (ne_of_gt hdpos) (-Complex.I) (by simp)
      hdense hplus⟩

/-! ## The eigenvector criterion -/

/-- **The elementary criterion this is all in service of, in its sharpest form.**  If the
domain contains a dense set of eigenvectors of `T` with *real* eigenvalues, then `T` is
essentially self-adjoint.  No symmetry hypothesis is needed and nothing has to converge:
at a deficiency point `z` off the real axis, `c ⟪x, w⟫ = z ⟪x, w⟫` with `c` real and `z`
not, so `⟪x, w⟫ = 0` for every eigenvector, and density finishes. -/
theorem essentiallySelfAdjointOn_of_dense_eigenvectors (T : D →ₗ[ℂ] F)
    (A : Set D) (hAdense : Dense (((↑) : D → F) '' A))
    (hA : ∀ x ∈ A, ∃ c : ℝ, T x = (c : ℂ) • (x : F)) :
    EssentiallySelfAdjointOn D T := by
  have hkey : ∀ z : ℂ, z.im ≠ 0 → DeficiencyTrivialAt D T z := by
    intro z hz w hw
    refine eq_zero_of_dense_inner_zero A hAdense fun x hx => ?_
    obtain ⟨c, hc⟩ := hA x hx
    have h1 := hw x
    rw [hc, inner_smul_left, Complex.conj_ofReal] at h1
    have h2 : ((c : ℂ) - z) * inner ℂ (x : F) w = 0 := by
      rw [sub_mul, h1, sub_self]
    have hne : ((c : ℂ) - z) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at him
      exact hz (by linarith)
    exact (mul_eq_zero.mp h2).resolve_left hne
  exact ⟨hkey Complex.I (by simp), hkey (-Complex.I) (by simp)⟩

/-! ## The criterion for a complete eigenbasis -/

/-- **The eigenbasis criterion, in the form that covers a simple spectrum.**  If the *span* of
a set `S` of eigenvectors of `T` with *real* eigenvalues is dense, then `T` is essentially
self-adjoint.  No symmetry hypothesis is needed.  At a deficiency point `z` off the real axis,
`c ⟪x, w⟫ = z ⟪x, w⟫` with `c ∈ ℝ` kills `⟪x, w⟫` for each eigenvector `x ∈ S`, and
conjugate-linearity carries that to the whole span; density then forces `w = 0`.

This is strictly stronger than `essentiallySelfAdjointOn_of_dense_eigenvectors`: a dense set
of eigenvectors is a very special situation, its own union of eigenlines being sparse as soon
as the eigenvalues are simple, whereas the span of a complete eigenbasis is dense by
definition.  It is the form in which an explicit spectral decomposition is used. -/
theorem essentiallySelfAdjointOn_of_dense_span_eigenvectors (T : D →ₗ[ℂ] F)
    (S : Set D) (hS : ∀ x ∈ S, ∃ c : ℝ, T x = (c : ℂ) • (x : F))
    (hdense : Dense (((↑) : D → F) '' ((Submodule.span ℂ S : Submodule ℂ D) : Set D))) :
    EssentiallySelfAdjointOn D T := by
  have hkey : ∀ z : ℂ, z.im ≠ 0 → DeficiencyTrivialAt D T z := by
    intro z hz w hw
    set A : Set D := ((Submodule.span ℂ S : Submodule ℂ D) : Set D) with hA
    have hAdense : Dense (((↑) : D → F) '' A) := hdense
    refine eq_zero_of_dense_inner_zero A hAdense ?_
    have hkill : ∀ a ∈ ((Submodule.span ℂ S : Submodule ℂ D) : Set D),
        (inner ℂ ((a : D) : F) w : ℂ) = 0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨c, hc⟩ := hS x hx
          have h1 := hw x
          rw [hc, inner_smul_left, Complex.conj_ofReal] at h1
          have h2 : ((c : ℂ) - z) * inner ℂ (x : F) w = 0 := by
            rw [sub_mul, h1, sub_self]
          have hne : ((c : ℂ) - z) ≠ 0 := by
            intro h
            have him := congrArg Complex.im h
            simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at him
            exact hz (by linarith)
          exact (mul_eq_zero.mp h2).resolve_left hne
      | zero => simp
      | add x y hx hy ihx ihy =>
          simp only [Submodule.coe_add, inner_add_left, ihx, ihy, add_zero]
      | smul c x hx ihx => simp only [Submodule.coe_smul, inner_smul_left, ihx, mul_zero]
    exact hkill
  exact ⟨hkey Complex.I (by simp), hkey (-Complex.I) (by simp)⟩

end BookProof.NelsonAnalytic
