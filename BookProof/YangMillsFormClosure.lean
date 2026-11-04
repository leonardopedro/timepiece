import Mathlib
import BookProof.YangMillsFormDomination
import BookProof.YangMillsEffectiveBarrier

/-!
# Chapter YangMillsFormClosure — the `L²` closure of the Gauss–polynomial core

`YangMillsFormDomination` states the Phase-4 comparison of quadratic forms — the certificate
`c₁ · q_ref ≤ q + c₂‖·‖²` — on the **Gauss–polynomial core**: finite coefficient families
`c : CoreCoeff d = (Fin d → ℕ) →₀ ℂ`, i.e. polynomials times the Gaussian.  The honest boundary
of `ChapterReferenceGap` names the missing step: the inequality is stated on the core, and the
form that actually has a spectrum is the *closure* of the core form in `L²`.  This chapter
supplies that closure.

## The space

`L2 d = ℓ²(Idx d, ℂ)` is `ℓ²` over the multi-indices — for arbitrary index type, hence
infinite-dimensional, with `lp`'s inner product `⟪x, y⟫ = ∑' n, ⟪x n, y n⟫`.  The core sits in it
by `coreEmbed c = ∑ n ∈ c.support, lp.single 2 n (c n)`, the finite linear combination of basis
vectors.

* `coreEmbed_apply` — the coefficients are the coefficients: `coreEmbed c n = c n`;
* `coreEmbed_single` — the basis vector with multi-index `n` is the core state `Finsupp.single n 1`;
* `norm_sq_coreEmbed` — **the core norm is the `ℓ²` norm**: `‖coreEmbed c‖² = coreNormSq c`, so the
  embedding is isometric down to the pairing with `coreNormSq`;
* `coreEmbed_injective` — distinct coefficient families give distinct states;
* `dense_range_coreEmbed` — **the core is dense in `L²`**: `lp.hasSum_single` exhibits an element
  of `ℓ²` as the sum of the series of its basis coefficients, and every partial sum of that series
  is the truncation `truncate x s`, hence a core state, so it lies in the closure.

## The closed form

Every form of `YangMillsFormDomination` is **diagonal** in the multi-index: it is
`diagonalForm f c = ∑ n ∈ c.support, f n ‖c n‖²` for a symbol `f` (`coreForm`, `degreeForm`,
`quarticDegreeForm`).  On `L²` the same symbol defines the `ℝ≥0∞`-valued form

`closedForm f x = ∑' n, ofReal (f n) · ofReal (‖x n‖²)`,

and this is *the closure of the core form*:

* `closedForm_coreEmbed` — it extends the core form:
  `closedForm f (coreEmbed c) = ofReal (diagonalForm f c)`;
* `lowerSemicontinuous_closedForm` — it is lower semicontinuous (supremum of finite sums of
  continuous functions), so it is a closed form in the sense of form theory;
* `closedForm_eq_iSup_truncate` — it is the supremum of the core forms of the truncations, which
  are precisely the core states converging to the state (`dense_range_coreEmbed`).

Together: extends, lsc, and the supremum over the approximating core states — the three properties
that characterise the closure of a form, proved here rather than assumed.

## Form domination transfers

`formDomination_symbol` reads a certificate on the core as the symbolwise inequality
`c₁ μ(n) − c₂ ≤ g(n)`, and `formDomination_closed` carries that inequality to the closed forms on
all of `L²`:

`ofReal c₁ · closedForm μ x ≤ closedForm g x + ofReal (max c₂ 0) · closedNormSq x`,

with the same constants — the shift is read on the `ℓ²` norm and a negative `c₂` is clipped at
zero, which loses nothing.  The concrete certificates `freeFormDomination` and
`interactingFormDomination` transfer the same way (`freeFormDomination_closed`,
`interactingFormDomination_closed`), and the Phase-3/Phase-4 gap statements follow on the closed
form with no core hypothesis: `closed_refGap`, `closed_refGap_norm`, `closed_degreeGap`,
`closed_interactingGap`.

The Yang–Mills form of record `yangMillsForm T g = degreeForm + quarticDegreeForm + barrierForm`
is diagonal too, the barrier being the symbol `rootCount T · zeroPoint g (parallelDegree T n)`
(`Barrier.yangMillsForm_eq_diagonalForm`), so the closure covers the object the plan actually asks
about: `yangMillsForm_closed` transfers its certificate, and `closed_yangMillsGap` gives the
`c₁Δ_ref` separation on the whole vacuum-orthogonal sector of `L²`.

## The bottom survives the elimination

`softmodes.md` Phase 1 asks, as its open item 4, that the bounds Phases 2–5 prove on the
*unreduced* core remain bounds for the *reduced* one — "restriction to the transverse sector
does not lower `θ_∞`".  For a diagonal form that is a theorem here, and a short one, because
the form never mixes multi-indices: the coercivity bound is symbolwise, so it holds state by
state and therefore on every subspace at once.

* `formBottom f = sInf (Set.range f)`, with `formBottom_le_of_bddBelow` (`ℝ` is only
  *conditionally* complete, so every statement below is equally available in the "any lower
  bound `θ`" form);
* `diagonalForm_ge_of_le_symbol` / `closedForm_ge_of_le_symbol` — `θ · ‖·‖² ≤ q` for any
  `θ ≤ f n`, on the core and on `L²`;
* `diagonalForm_ge_formBottom` / `closedForm_ge_formBottom` — the same at the bottom;
* `sector_bottom_ge_of_le_symbol` / **`sector_bottom_ge_formBottom`** — for *any* set `S` of
  normalised retained states, `ofReal θ ≤ sInf (closedForm f '' S)`: the Rayleigh infimum over a
  sector is bounded below by the same constant as the whole space, so the eliminated directions
  carry no spectral weight below the bottom and the reduction cannot have moved it.

## Honest boundary

The transfer is proved for diagonal forms, which is what all forms of this chapter are.  It does
not claim that an arbitrary non-diagonal `q` — a genuine magnetic interaction mixing multi-indices —
is closeable with the same constants; for those the termwise estimate that `closedForm_scaled_le`
performs does not apply and the closure would have to be built from a closability (KLM) argument.
`YangMillsFormDomination`'s magnetic column forms are nonnegative and enter only through
`FormDomination.add_nonneg`, which is exactly the monotonicity that a diagonal argument supports.
-/

noncomputable section

namespace BookProof.YangMillsFormClosure

open Finset
open scoped ENNReal

open BookProof.ReferenceGap
open BookProof.YangMillsFormDomination

variable {d : ℕ}

/-- The multi-indices of the product Hermite basis. -/
abbrev Idx (d : ℕ) := Fin d → ℕ

/-- **The `L²` space of the core**: `ℓ²` over the multi-indices, i.e. coefficient families with
`∑' n, ‖x n‖² < ∞`.  It is a Hilbert space because each summand is a Hilbert space. -/
abbrev L2 (d : ℕ) := ℓ²(Idx d, ℂ)

/-! ## 1. The Gauss–polynomial core inside `L²` -/

/-- The embedding of the Gauss–polynomial core into `L²`: a finite coefficient family is sent to
the finite linear combination of basis vectors with those coefficients. -/
def coreEmbed (c : CoreCoeff d) : L2 d :=
  ∑ n ∈ c.support, lp.single (E := fun _ : Idx d => ℂ) 2 n (c n)

/-- **The coefficients of a core state are its coefficients**: `coreEmbed` does not mix
multi-indices, which is what makes every form below diagonal. -/
@[simp]
theorem coreEmbed_apply (c : CoreCoeff d) (m : Idx d) : coreEmbed c m = c m := by
  rw [coreEmbed, lp.coeFn_sum, Finset.sum_apply]
  by_cases hm : m ∈ c.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hbm
      rw [lp.single_apply_ne _ _ _ (Ne.symm hbm)]
    · intro h
      exact absurd hm h
  · rw [Finset.sum_eq_zero]
    · exact (Finsupp.notMem_support_iff.mp hm).symm
    · intro b hb
      by_cases hbm : b = m
      · subst hbm
        exact absurd hb hm
      · rw [lp.single_apply_ne _ _ _ (Ne.symm hbm)]

/-- The core state of a single basis vector: `Finsupp.single n a ↦ a · eₙ`. -/
theorem coreEmbed_single (n : Idx d) (a : ℂ) :
    coreEmbed (Finsupp.single n a) = lp.single (E := fun _ : Idx d => ℂ) 2 n a := by
  apply lp.ext
  funext m
  rw [coreEmbed_apply]
  by_cases h : m = n
  · subst h
    simp
  · rw [lp.single_apply_ne _ _ _ h, Finsupp.single_eq_of_ne' (Ne.symm h)]

/-- `coreEmbed` is additive: it is the coordinatewise map on an orthonormal family. -/
theorem coreEmbed_add (c₁ c₂ : CoreCoeff d) :
    coreEmbed (c₁ + c₂) = coreEmbed c₁ + coreEmbed c₂ := by
  apply lp.ext
  funext m
  simp [Finsupp.add_apply]

/-- `coreEmbed` is homogeneous. -/
theorem coreEmbed_smul (a : ℂ) (c : CoreCoeff d) :
    coreEmbed (a • c) = a • coreEmbed c := by
  apply lp.ext
  funext m
  simp

/-- The core as a linear map into `L²`. -/
def coreEmbedLM : CoreCoeff d →ₗ[ℂ] L2 d where
  toFun := coreEmbed
  map_add' := coreEmbed_add
  map_smul' := coreEmbed_smul

/-- **The core embedding is isometric, in the sense that it carries `coreNormSq` to the square of
the `ℓ²` norm.**  The orthonormality of the basis vectors is `lp.norm_sum_single`. -/
theorem norm_sq_coreEmbed (c : CoreCoeff d) : ‖coreEmbed c‖ ^ 2 = coreNormSq c := by
  have h := lp.norm_sum_single (E := fun _ : Idx d => ℂ) (p := (2 : ℝ≥0∞)) (by norm_num) (⇑c)
    c.support
  simpa [coreEmbed, coreNormSq] using h

/-- The core embedding is injective: a state with all coefficients zero is the zero state. -/
theorem coreEmbed_injective : Function.Injective (coreEmbed (d := d)) := by
  intro c₁ c₂ h
  ext m
  have h' : coreEmbed c₁ m = coreEmbed c₂ m := by rw [h]
  simpa using h'

/-! ## 2. The core is dense in `L²`

`lp.hasSum_single` says that an element of `ℓ²` is the sum of the series of its basis
coefficients.  Every finite partial sum of that series is a core state, so the series converges
inside the closure of the core. -/

/-- The coefficient family obtained by truncating a state to a finite set of multi-indices. -/
def truncate (x : L2 d) (s : Finset (Idx d)) : CoreCoeff d :=
  ∑ n ∈ s, Finsupp.single n (x n)

/-- A finite sum of core states is the core state of the sum of the coefficient families. -/
theorem coreEmbed_finset_sum (s : Finset (Idx d)) (f : Idx d → ℂ) :
    coreEmbed (∑ n ∈ s, Finsupp.single n (f n))
      = ∑ n ∈ s, lp.single (E := fun _ : Idx d => ℂ) 2 n (f n) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coreEmbed]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, coreEmbed_add, coreEmbed_single, ih]

/-- The core embedding of a truncation is the corresponding finite partial sum of the basis
series. -/
theorem coreEmbed_truncate (x : L2 d) (s : Finset (Idx d)) :
    coreEmbed (truncate x s)
      = ∑ n ∈ s, lp.single (E := fun _ : Idx d => ℂ) 2 n (x n) :=
  coreEmbed_finset_sum s ⇑x

/-- **Every state is a limit of core states**: `lp.hasSum_single` writes `x` as the limit of its
partial basis sums, and those partial sums are the core embeddings of the truncations. -/
theorem mem_closure_range_coreEmbed (x : L2 d) :
    x ∈ closure (Set.range (coreEmbed (d := d))) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hsum : HasSum (fun n : Idx d => lp.single (E := fun _ : Idx d => ℂ) 2 n (x n)) x :=
    lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x
  exact mem_closure_of_tendsto hsum
    (Filter.Eventually.of_forall fun s => ⟨truncate x s, coreEmbed_truncate x s⟩)

/-- **The Gauss–polynomial core is dense in `L²`.** -/
theorem dense_range_coreEmbed : Dense (Set.range (coreEmbed (d := d))) := by
  rw [dense_iff_closure_eq]
  exact Set.eq_univ_of_forall mem_closure_range_coreEmbed

/-! ## 3. The diagonal forms and their symbols

Every form of `YangMillsFormDomination` is diagonal in the multi-index: `coreForm`, `degreeForm` and
`quarticDegreeForm` all read `∑ n ∈ c.support, f n ‖c n‖²` for a symbol `f`.  Recording this once
is what lets a single closure statement cover all of them. -/

/-- The diagonal form on the core with symbol `f`. -/
def diagonalForm (f : Idx d → ℝ) (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, f n * ‖c n‖ ^ 2

/-- The reference form is the diagonal form of the reference energy. -/
theorem coreForm_eq_diagonalForm (ω : Fin d → ℝ) :
    coreForm ω = diagonalForm (d := d) (fun n => refEnergy ω n) := rfl

/-- The free kinetic form is the diagonal form of the degree symbol. -/
theorem degreeForm_eq_diagonalForm :
    degreeForm (d := d) = diagonalForm (fun n => ∑ i, (n i : ℝ)) := rfl

/-- The quartic form is the diagonal form of the squared degree symbol. -/
theorem quarticDegreeForm_eq_diagonalForm :
    quarticDegreeForm (d := d) = diagonalForm (fun n => (∑ i, (n i : ℝ)) ^ 2) := rfl

/-- Diagonal forms add symbolwise. -/
theorem diagonalForm_add (f g : Idx d → ℝ) (c : CoreCoeff d) :
    diagonalForm (fun n => f n + g n) c = diagonalForm f c + diagonalForm g c := by
  rw [diagonalForm, diagonalForm, diagonalForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => by ring

/-- The diagonal form of a single basis vector is its symbol: the form reads the symbol without
mixing multi-indices. -/
theorem diagonalForm_single (f : Idx d → ℝ) (n : Idx d) (a : ℂ) :
    diagonalForm f (Finsupp.single n a) = f n * ‖a‖ ^ 2 := by
  by_cases ha : a = 0
  · subst ha
    rw [Finsupp.single_zero, diagonalForm]
    simp
  · rw [diagonalForm, Finsupp.support_single_ne_zero n ha, Finset.sum_singleton,
      Finsupp.single_eq_same]

/-- The reference form on a basis vector is the reference energy. -/
theorem coreForm_single (ω : Fin d → ℝ) (n : Idx d) :
    coreForm ω (Finsupp.single n 1) = refEnergy ω n := by
  rw [coreForm, Finsupp.support_single_ne_zero n one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, norm_one, one_pow, mul_one]

/-- The core norm of a basis vector is one. -/
theorem coreNormSq_single (n : Idx d) : coreNormSq (Finsupp.single n 1) = 1 := by
  rw [coreNormSq, Finsupp.support_single_ne_zero n one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, norm_one, one_pow]

/-- **A domination certificate reads off as a symbolwise inequality.**  Evaluating the core
inequality on the basis vector `eₙ` gives `c₁ μ(n) − c₂ ≤ g(n)`: for diagonal forms the core
inequality and the symbolwise one are the same statement. -/
theorem formDomination_symbol {ω : Fin d → ℝ} {g : Idx d → ℝ}
    (D : FormDomination ω (diagonalForm g)) (n : Idx d) :
    D.c₁ * refEnergy ω n - D.c₂ ≤ g n := by
  have h := D.dom (Finsupp.single n 1)
  rw [coreForm_single, coreNormSq_single, diagonalForm_single] at h
  simpa using h

/-! ## 4. The closed form on `L²` -/

/-- The squared norm of a state, as an `ℝ≥0∞`-valued form. -/
def closedNormSq (x : L2 d) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (‖x n‖ ^ 2)

/-- The **closed form** of the diagonal symbol `f` on `L²`. -/
def closedForm (f : Idx d → ℝ) (x : L2 d) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (f n) * ENNReal.ofReal (‖x n‖ ^ 2)

/-- The closed norm form is the `ℓ²` norm: `∑' n ‖x n‖² = ‖x‖²`. -/
theorem closedNormSq_eq (x : L2 d) : closedNormSq x = ENNReal.ofReal (‖x‖ ^ 2) := by
  have hsum : HasSum (fun n : Idx d => ‖x n‖ ^ 2) (‖x‖ ^ 2) := by
    have h := lp.hasSum_norm (E := fun _ : Idx d => ℂ) (p := (2 : ℝ≥0∞)) (by norm_num) x
    simpa using h
  rw [closedNormSq, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable,
    hsum.tsum_eq]

/-- **The closed form extends the core form**: on the core it is the core form of the symbol. -/
theorem closedForm_coreEmbed (f : Idx d → ℝ) (hf : ∀ n, 0 ≤ f n) (c : CoreCoeff d) :
    closedForm f (coreEmbed c) = ENNReal.ofReal (diagonalForm f c) := by
  classical
  have hzero : ∀ n ∉ c.support, f n * ‖c n‖ ^ 2 = 0 := by
    intro n hn
    rw [Finsupp.notMem_support_iff.mp hn, norm_zero]
    ring
  have hsummable : Summable (fun n => f n * ‖c n‖ ^ 2) :=
    (hasSum_sum_of_ne_finset_zero hzero).summable
  have hterm : ∀ n, ENNReal.ofReal (f n) * ENNReal.ofReal (‖coreEmbed c n‖ ^ 2)
      = ENNReal.ofReal (f n * ‖c n‖ ^ 2) := by
    intro n
    rw [coreEmbed_apply, ENNReal.ofReal_mul (hf n)]
  simp only [closedForm, hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hf n) (by positivity)) hsummable,
    (hasSum_sum_of_ne_finset_zero hzero).tsum_eq, diagonalForm]

/-- A constant symbol is a multiple of the closed norm form. -/
theorem closedForm_const (C : ℝ) (x : L2 d) :
    closedForm (fun _ : Idx d => C) x = ENNReal.ofReal C * closedNormSq x := by
  rw [closedForm, closedNormSq, ENNReal.tsum_mul_left]

/-- The closed form is monotone in its symbol. -/
theorem closedForm_mono_symbol {f g : Idx d → ℝ} (hfg : ∀ n, f n ≤ g n) (x : L2 d) :
    closedForm f x ≤ closedForm g x := by
  refine ENNReal.tsum_le_tsum fun n => ?_
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hfg n)) _

/-- **Monotonicity that ignores the vacuum**: a symbolwise bound only has to hold where the state
is nonzero.  This is what lets a gap inequality, which fails at the vacuum level, hold on the
vacuum-orthogonal sector. -/
theorem closedForm_le_of_on_support {f g : Idx d → ℝ} (x : L2 d)
    (hfg : ∀ n, x n ≠ 0 → f n ≤ g n) : closedForm f x ≤ closedForm g x := by
  refine ENNReal.tsum_le_tsum fun n => ?_
  by_cases hx : x n = 0
  · rw [hx]
    simp
  · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hfg n hx)) _

/-- **The scaled comparison, on `L²`.**  If the symbols satisfy `c₁ f ≤ g + C` with `c₁, C ≥ 0`
and `g ≥ 0`, then the closed forms satisfy the same inequality with the `ℓ²` norm as the shift. -/
theorem closedForm_scaled_le {f g : Idx d → ℝ} {c₁ C : ℝ} (hc₁ : 0 ≤ c₁)
    (hg : ∀ n, 0 ≤ g n) (hC : 0 ≤ C) (h : ∀ n, c₁ * f n ≤ g n + C) (x : L2 d) :
    ENNReal.ofReal c₁ * closedForm f x
      ≤ closedForm g x + ENNReal.ofReal C * closedNormSq x := by
  rw [closedForm, closedForm, closedNormSq, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun n => ?_
  have h1 : ENNReal.ofReal c₁ * (ENNReal.ofReal (f n) * ENNReal.ofReal (‖x n‖ ^ 2))
      = ENNReal.ofReal (c₁ * f n) * ENNReal.ofReal (‖x n‖ ^ 2) := by
    rw [← mul_assoc, ENNReal.ofReal_mul hc₁]
  have h2 : ENNReal.ofReal (g n) * ENNReal.ofReal (‖x n‖ ^ 2)
        + ENNReal.ofReal C * ENNReal.ofReal (‖x n‖ ^ 2)
      = ENNReal.ofReal (g n + C) * ENNReal.ofReal (‖x n‖ ^ 2) := by
    rw [← add_mul, ← ENNReal.ofReal_add (hg n) hC]
  rw [h1, h2]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (h n)) _

/-! ## 5. The closed form is the closure of the core form

The two properties that make `closedForm f` *the* closed form of the core form are that it is
lower semicontinuous and that it is the supremum of the core forms of the truncations.  Both hold
because the sum is a supremum of finite sums of continuous functions. -/

/-- The truncation of a state to a finite set of multi-indices, read at a multi-index. -/
theorem truncate_apply (x : L2 d) (s : Finset (Idx d)) (m : Idx d) :
    truncate x s m = if m ∈ s then x m else 0 := by
  classical
  rw [truncate]
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finsupp.add_apply]
      by_cases hma : m = a
      · subst hma
        rw [Finsupp.single_eq_same, ih, if_neg ha, if_pos (Finset.mem_insert_self _ _), add_zero]
      · rw [Finsupp.single_eq_of_ne' (Ne.symm hma), zero_add, ih]
        by_cases hms : m ∈ s
        · rw [if_pos hms, if_pos (Finset.mem_insert_of_mem hms)]
        · rw [if_neg hms, if_neg (by simp [Finset.mem_insert, hma, hms])]

/-- The diagonal form commutes with truncation. -/
theorem diagonalForm_truncate (f : Idx d → ℝ) (x : L2 d) (s : Finset (Idx d)) :
    diagonalForm f (truncate x s) = ∑ n ∈ s, f n * ‖x n‖ ^ 2 := by
  classical
  have hsupp : (truncate x s).support ⊆ s := by
    intro m hm
    by_contra hms
    rw [Finsupp.mem_support_iff] at hm
    exact hm (by rw [truncate_apply, if_neg hms])
  rw [diagonalForm, Finset.sum_subset hsupp]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [truncate_apply, if_pos hm]
  · intro m _ hm
    rw [Finsupp.notMem_support_iff.mp hm, norm_zero]
    ring

/-- **The closed form is the supremum of the core forms of the truncations.**  With
`dense_range_coreEmbed` (the truncations converge to the state) this identifies the closed form as
the closure of the core form, not merely an extension of it. -/
theorem closedForm_eq_iSup_truncate (f : Idx d → ℝ) (hf : ∀ n, 0 ≤ f n) (x : L2 d) :
    closedForm f x = ⨆ s : Finset (Idx d), ENNReal.ofReal (diagonalForm f (truncate x s)) := by
  classical
  rw [closedForm, ENNReal.tsum_eq_iSup_sum]
  refine iSup_congr fun s => ?_
  rw [diagonalForm_truncate]
  calc ∑ n ∈ s, ENNReal.ofReal (f n) * ENNReal.ofReal (‖x n‖ ^ 2)
      = ∑ n ∈ s, ENNReal.ofReal (f n * ‖x n‖ ^ 2) :=
        Finset.sum_congr rfl fun n _ => (ENNReal.ofReal_mul (hf n)).symm
    _ = ENNReal.ofReal (∑ n ∈ s, f n * ‖x n‖ ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (hf n) (by positivity))).symm

/-- Each fixed-`n` term of the closed form is continuous in the state. -/
theorem continuous_closedForm_term (f : Idx d → ℝ) (n : Idx d) :
    Continuous fun x : L2 d => ENNReal.ofReal (f n) * ENNReal.ofReal (‖x n‖ ^ 2) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hval : Continuous fun x : L2 d => (x : Idx d → ℂ) :=
    (lp.uniformContinuous_coe (E := fun _ : Idx d => ℂ) (p := (2 : ℝ≥0∞))).continuous
  have hcoord : Continuous fun x : L2 d => (x : Idx d → ℂ) n :=
    (continuous_apply n).comp hval
  have hterm : Continuous fun x : L2 d => ENNReal.ofReal (‖x n‖ ^ 2) :=
    ENNReal.continuous_ofReal.comp (hcoord.norm.pow 2)
  exact (ENNReal.continuous_const_mul (a := ENNReal.ofReal (f n)) ENNReal.ofReal_ne_top).comp
    hterm

/-- A finite partial sum of the closed form is continuous in the state. -/
theorem continuous_closedForm_sum (f : Idx d → ℝ) (s : Finset (Idx d)) :
    Continuous fun x : L2 d =>
      ∑ n ∈ s, ENNReal.ofReal (f n) * ENNReal.ofReal (‖x n‖ ^ 2) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
      have hfun : (fun x : L2 d =>
            ∑ n ∈ insert a s, ENNReal.ofReal (f n) * ENNReal.ofReal (‖x n‖ ^ 2))
          = fun x : L2 d => ENNReal.ofReal (f a) * ENNReal.ofReal (‖x a‖ ^ 2)
              + ∑ n ∈ s, ENNReal.ofReal (f n) * ENNReal.ofReal (‖x n‖ ^ 2) := by
        funext x
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact (continuous_closedForm_term f a).add ih

/-- **The closed form is lower semicontinuous**: it is a supremum of finite sums of continuous
functions of the state. -/
theorem lowerSemicontinuous_closedForm (f : Idx d → ℝ) :
    LowerSemicontinuous (fun x : L2 d => closedForm f x) := by
  have h : (fun x : L2 d => closedForm f x)
      = fun x : L2 d => ⨆ s : Finset (Idx d),
          ∑ n ∈ s, ENNReal.ofReal (f n) * ENNReal.ofReal (‖x n‖ ^ 2) := by
    funext x
    rw [closedForm, ENNReal.tsum_eq_iSup_sum]
  rw [h]
  refine lowerSemicontinuous_iSup fun s => ?_
  exact (continuous_closedForm_sum f s).lowerSemicontinuous

/-! ## 6. Domination transfers to the closed form -/

/-- **Form domination transfers to the closed form.**  If `q = diagonalForm g` dominates the
reference form on the Gauss–polynomial core with constants `c₁ > 0`, `c₂`, and `g ≥ 0`, then the
closed forms satisfy the same domination inequality on all of `L²`, with the shift read off the
`ℓ²` norm and `c₂` clipped at zero (a negative shift only weakens the inequality, so clipping loses
nothing).  No constant is lost. -/
theorem formDomination_closed {ω : Fin d → ℝ} {g : Idx d → ℝ}
    (D : FormDomination ω (diagonalForm g)) (hg : ∀ n, 0 ≤ g n) (x : L2 d) :
    ENNReal.ofReal D.c₁ * closedForm (fun n => refEnergy ω n) x
      ≤ closedForm g x + ENNReal.ofReal (max D.c₂ 0) * closedNormSq x := by
  refine closedForm_scaled_le D.hc₁.le hg (le_max_right _ _) (fun n => ?_) x
  have h := formDomination_symbol D n
  have h2 : D.c₂ ≤ max D.c₂ 0 := le_max_left _ _
  linarith

/-- The free-plus-interacting core form is the diagonal form of the symbol `deg + deg²`. -/
theorem interactingForm_eq_diagonalForm :
    (fun c : CoreCoeff d => degreeForm c + quarticDegreeForm c)
      = diagonalForm (fun n => (∑ i, (n i : ℝ)) + (∑ i, (n i : ℝ)) ^ 2) := by
  funext c
  change diagonalForm (fun n : Idx d => ∑ i, (n i : ℝ)) c
      + diagonalForm (fun n : Idx d => (∑ i, (n i : ℝ)) ^ 2) c = _
  rw [← diagonalForm_add]

/-- **The symbolwise form of the free certificate**: `c₁(μ(n) − μ₀) ≤ deg n`.  This is the core
inequality of `freeFormDomination` read on the basis vector `eₙ`. -/
theorem free_symbol {ω : Fin d → ℝ} {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1)
    (n : Idx d) :
    c₁ * refEnergy ω n - c₁ * refEnergy ω 0 ≤ ∑ i, (n i : ℝ) := by
  have h := (freeFormDomination (d := d) ω hc₁ hω₁).dom (Finsupp.single n 1)
  have hc1 : (freeFormDomination (d := d) ω hc₁ hω₁).c₁ = c₁ := rfl
  have hc2 : (freeFormDomination (d := d) ω hc₁ hω₁).c₂ = c₁ * refEnergy ω 0 := rfl
  rw [hc1, hc2, coreForm_single, coreNormSq_single, degreeForm_eq_diagonalForm,
    diagonalForm_single, norm_one, one_pow, mul_one] at h
  simpa using h

/-- **The Phase-4 certificate, on `L²`.**  The concrete certificate `freeFormDomination`
(`−Δ` dominates `H_ref`) transfers to the closed forms on all of `L²` with its constants intact. -/
theorem freeFormDomination_closed {ω : Fin d → ℝ} {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (x : L2 d) :
    ENNReal.ofReal c₁ * closedForm (fun n => refEnergy ω n) x
      ≤ closedForm (fun n => ∑ i, (n i : ℝ)) x
          + ENNReal.ofReal (max (c₁ * refEnergy ω 0) 0) * closedNormSq x := by
  refine closedForm_scaled_le hc₁.le (fun n => ?_) (le_max_right _ _) (fun n => ?_) x
  · exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
  · have h := free_symbol (d := d) hc₁ hω₁ n
    have h2 : c₁ * refEnergy ω 0 ≤ max (c₁ * refEnergy ω 0) 0 := le_max_left _ _
    linarith

/-- **The free-plus-quartic certificate, on `L²`.** -/
theorem interactingFormDomination_closed {ω : Fin d → ℝ} {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) (x : L2 d) :
    ENNReal.ofReal c₁ * closedForm (fun n => refEnergy ω n) x
      ≤ closedForm (fun n => (∑ i, (n i : ℝ)) + (∑ i, (n i : ℝ)) ^ 2) x
          + ENNReal.ofReal (max (c₁ * refEnergy ω 0) 0) * closedNormSq x := by
  refine closedForm_scaled_le hc₁.le (fun n => ?_) (le_max_right _ _) (fun n => ?_) x
  · have hnn : 0 ≤ ∑ i, (n i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
    nlinarith [sq_nonneg (∑ i, (n i : ℝ))]
  · have h := free_symbol (d := d) hc₁ hω₁ n
    have hnn : 0 ≤ ∑ i, (n i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
    have h2 : c₁ * refEnergy ω 0 ≤ max (c₁ * refEnergy ω 0) 0 := le_max_left _ _
    nlinarith [sq_nonneg (∑ i, (n i : ℝ))]


/-! ## 7. The Phase-3 and Phase-4 gaps, now on the closed form -/

/-- **The Phase-3 reference gap on the closed form.**  On the vacuum-orthogonal sector the closed
reference form is at least `(μ₀ + Δ_ref)‖x‖²` for *every* state of `L²` — the core hypothesis is
gone. -/
theorem closed_refGap [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i) {x : L2 d}
    (hx : x 0 = 0) :
    ENNReal.ofReal (refEnergy ω 0 + refGap ω) * closedNormSq x
      ≤ closedForm (fun n => refEnergy ω n) x := by
  rw [← closedForm_const (refEnergy ω 0 + refGap ω) x]
  refine closedForm_le_of_on_support x (fun n hn => ?_)
  have hne : n ≠ 0 := by
    rintro rfl
    exact hn hx
  have h := refEnergy_ge_vacuum_add_gap hω hne
  linarith

/-- The same statement with the `ℓ²` norm made explicit. -/
theorem closed_refGap_norm [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i) {x : L2 d}
    (hx : x 0 = 0) :
    ENNReal.ofReal ((refEnergy ω 0 + refGap ω) * ‖x‖ ^ 2)
      ≤ closedForm (fun n => refEnergy ω n) x := by
  have hC : 0 ≤ refEnergy ω 0 + refGap ω := by
    have := refEnergy_nonneg ω hω 0
    have := refGap_pos hω
    linarith
  rw [ENNReal.ofReal_mul hC, ← closedNormSq_eq]
  exact closed_refGap hω hx

/-- **The certified free gap on the closed form.**  The degree form of `−Δ` clears the vacuum by
`c₁Δ_ref` on the whole vacuum-orthogonal sector of `L²`. -/
theorem closed_degreeGap [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i) {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) {x : L2 d} (hx : x 0 = 0) :
    ENNReal.ofReal (c₁ * refGap ω) * closedNormSq x
      ≤ closedForm (fun n => ∑ i, (n i : ℝ)) x := by
  rw [← closedForm_const (c₁ * refGap ω) x]
  refine closedForm_le_of_on_support x (fun n hn => ?_)
  have hne : n ≠ 0 := by
    rintro rfl
    exact hn hx
  have hμ := refEnergy_ge_vacuum_add_gap hω hne
  have hsc := scaled_refEnergy_sub_zero_le_degree ω hω₁ n
  have hsub := refEnergy_sub_zero ω n
  have hΔ : refGap ω ≤ refEnergy ω n - refEnergy ω 0 := by linarith
  have hmul : c₁ * refGap ω ≤ c₁ * (refEnergy ω n - refEnergy ω 0) :=
    mul_le_mul_of_nonneg_left hΔ hc₁.le
  linarith

/-- **The certified interacting gap on the closed form**: adding the quartic `:N²:` term cannot
lower the level, so the gap survives on `L²`. -/
theorem closed_interactingGap [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i) {c₁ : ℝ}
    (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) {x : L2 d} (hx : x 0 = 0) :
    ENNReal.ofReal (c₁ * refGap ω) * closedNormSq x
      ≤ closedForm (fun n => (∑ i, (n i : ℝ)) + (∑ i, (n i : ℝ)) ^ 2) x := by
  refine le_trans (closed_degreeGap hω hc₁ hω₁ hx) (closedForm_le_of_on_support x (fun n _ => ?_))
  have hnn : 0 ≤ ∑ i, (n i : ℝ) :=
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
  nlinarith [sq_nonneg (∑ i, (n i : ℝ))]


/-! ## 8. The Yang–Mills form of record, on the closed form

`yangMillsForm T g = degreeForm + quarticDegreeForm + barrierForm` — the `H_W`-shaped form of
record of `YangMillsEffectiveBarrier` — is diagonal as well: the barrier is
`rootCount T · zeroPoint g (parallelDegree T n)` read on each multi-index.  So the closure covers
the form the plan actually asks about, not only its free part. -/

namespace Barrier

open BookProof.YangMillsEffectiveBarrier

/-- The Simon barrier as a symbol: `rootCount T · zeroPoint g (parallelDegree T n)`. -/
def barrierSymbol (T : Finset (Fin d)) (g : ℝ) (n : Idx d) : ℝ :=
  rootCount T * zeroPoint g (parallelDegree T n)

theorem barrierForm_eq_diagonalForm (T : Finset (Fin d)) (g : ℝ) :
    barrierForm T g = diagonalForm (barrierSymbol T g) := rfl

theorem barrierSymbol_nonneg {g : ℝ} (hg : 0 ≤ g) (T : Finset (Fin d)) (n : Idx d) :
    0 ≤ barrierSymbol T g n :=
  mul_nonneg (rootCount_nonneg T) (zeroPoint_nonneg hg (parallelDegree_nonneg T n))

/-- **The `H_W`-shaped form of record is diagonal**, with the symbol
`deg + deg² + rootCount · zeroPoint`. -/
theorem yangMillsForm_eq_diagonalForm (T : Finset (Fin d)) (g : ℝ) :
    yangMillsForm T g = diagonalForm (fun n =>
      (∑ i, (n i : ℝ)) + (∑ i, (n i : ℝ)) ^ 2 + barrierSymbol T g n) := by
  funext c
  rw [yangMillsForm, degreeForm_eq_diagonalForm, quarticDegreeForm_eq_diagonalForm,
    barrierForm_eq_diagonalForm, ← diagonalForm_add, ← diagonalForm_add]

end Barrier

/-- **Form domination for the Yang–Mills form of record, on `L²`.**  The certificate
`yangMillsForm_certified` transfers to the closed form of `q_W` with its constants intact. -/
theorem yangMillsForm_closed {ω : Fin d → ℝ} {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g)
    {c₁ : ℝ} (hc₁ : 0 < c₁) (hω₁ : ∀ i, c₁ * ω i ≤ 1) (x : L2 d) :
    ENNReal.ofReal c₁ * closedForm (fun n => refEnergy ω n) x
      ≤ closedForm (fun n => (∑ i, (n i : ℝ)) + (∑ i, (n i : ℝ)) ^ 2
          + Barrier.barrierSymbol T g n) x
          + ENNReal.ofReal (max (c₁ * refEnergy ω 0) 0) * closedNormSq x := by
  refine closedForm_scaled_le hc₁.le (fun n => ?_) (le_max_right _ _) (fun n => ?_) x
  · have h1 : 0 ≤ ∑ i, (n i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
    have h2 := Barrier.barrierSymbol_nonneg hg T n
    nlinarith [sq_nonneg (∑ i, (n i : ℝ))]
  · have h := free_symbol (d := d) hc₁ hω₁ n
    have hb := Barrier.barrierSymbol_nonneg hg T n
    have hnn : 0 ≤ ∑ i, (n i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
    have h2 : c₁ * refEnergy ω 0 ≤ max (c₁ * refEnergy ω 0) 0 := le_max_left _ _
    nlinarith [sq_nonneg (∑ i, (n i : ℝ))]

/-- **The Phase-4 gap on the Yang–Mills form of record, on the closed form**: on the
vacuum-orthogonal sector of `L²` the closed form of `q_W` is at least `c₁Δ_ref‖x‖²`. -/
theorem closed_yangMillsGap [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i)
    {T : Finset (Fin d)} {g : ℝ} (hg : 0 ≤ g) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hω₁ : ∀ i, c₁ * ω i ≤ 1) {x : L2 d} (hx : x 0 = 0) :
    ENNReal.ofReal (c₁ * refGap ω) * closedNormSq x
      ≤ closedForm (fun n => (∑ i, (n i : ℝ)) + (∑ i, (n i : ℝ)) ^ 2
          + Barrier.barrierSymbol T g n) x := by
  refine le_trans (closed_interactingGap hω hc₁ hω₁ hx)
    (closedForm_mono_symbol (fun n => ?_) x)
  have hnn : 0 ≤ ∑ i, (n i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
  nlinarith [Barrier.barrierSymbol_nonneg hg T n]

/-! ## 5. Stability of the bottom under the elimination (`softmodes.md` Phase 1, open item 4)

Phases 2–5 bound the bottom and the first excited level of the operator on the *unreduced* core
(`degreeForm`, `barrierForm`, and the `FormDomination` certificate).  For the BRST elimination
of Phase 1 to be legitimate those numbers must still be bounds for the *reduced* operator: the
eliminated (pure-gauge) directions must not carry spectral weight that the reduction removes, in
the sense that dropping them cannot lower the bottom.  The plan states this as "restriction to
the transverse sector does not lower `θ_∞`".

For a **diagonal** form the answer is exact, and it is proved here.  Every term of the sum
`∑' n, ofReal (f n) · ofReal (‖x n‖²)` is indexed by a single multi-index, so the form never mixes
retained and eliminated directions: the coercivity bound holds state by state, and therefore on
every subspace at once.  Concretely:

* `formBottom f = sInf (Set.range f)` — the bottom of the symbol, and
  `formBottom_le_of_bddBelow` for a bounded-below symbol (`ℝ` is only *conditionally* complete,
  which is why every statement below is equally available in the "lower bound `θ`" form);
* **`diagonalForm_ge_of_le_symbol`** / **`diagonalForm_ge_formBottom`** — on the core,
  `θ · coreNormSq c ≤ diagonalForm f c` for any `θ ≤ f n`;
* **`closedForm_ge_of_le_symbol`** / **`closedForm_ge_formBottom`** — on `L²`,
  `ofReal θ · closedNormSq x ≤ closedForm f x`;
* **`sector_bottom_ge_of_le_symbol`** / **`sector_bottom_ge_formBottom`** — consequently, for
  *any* set `S` of normalised retained states, `ofReal θ ≤ sInf (closedForm f '' S)`: the
  Rayleigh infimum over a sector is bounded below by the *same* constant as the whole space.

That last statement is the content the plan asks for.  The bottom is a property of the **symbol**,
and restriction cannot change a symbolwise bound — so Phases 2–5's `c₁Δ_ref` remains valid on the
reduced space, and the elimination cannot have removed the directions that dominate the bottom.

**Honest boundary.**  What this does *not* supply is the decoupling hypothesis in the interacting
theory.  Diagonality is exactly why the argument is short, and it is a property of the free,
quartic and barrier forms the corpus models; a genuinely magnetic interaction mixes
multi-indices, and then "the eliminated directions carry no spectral weight near the bottom" is
a genuine statement about the off-diagonal blocks — the transfer is proved for diagonal forms
only, which is what the boundary note of this file already records for `formDomination_closed`.
The reduced space itself — the quotient `H/(exact ⊕ harmonic)` — is built in
`ChapterBrstReducedTransfer` / `ChapterBrstUnbounded`; what is missing there is not the
decomposition but the identification `closure (range Ω) = span{∂_i φ}`, which is open item 3 of
the same phase.
-/

/-- The **bottom of a diagonal form**: `sInf` of its symbol over the multi-indices.  `ℝ` is only
*conditionally* complete, so the value is usable exactly when the symbol is bounded below;
`formBottom_le_of_bddBelow` reads the bottom off, and `diagonalForm_ge_formBottom` consumes it. -/
noncomputable def formBottom (f : Idx d → ℝ) : ℝ := sInf (Set.range f)

/-- A bounded-below symbol has its bottom at or below every one of its values. -/
theorem formBottom_le_of_bddBelow {f : Idx d → ℝ} (hf : BddBelow (Set.range f)) (n : Idx d) :
    formBottom f ≤ f n :=
  csInf_le hf ⟨n, rfl⟩

/-- **Coercivity at a lower bound of the symbol, on the core.** -/
theorem diagonalForm_ge_of_le_symbol {f : Idx d → ℝ} {θ : ℝ} (hθ : ∀ n, θ ≤ f n)
    (c : CoreCoeff d) : θ * coreNormSq c ≤ diagonalForm f c := by
  rw [diagonalForm, coreNormSq, Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ =>
    mul_le_mul_of_nonneg_right (hθ n) (by positivity)

/-- **Coercivity at the bottom, on the core.** -/
theorem diagonalForm_ge_formBottom {f : Idx d → ℝ} (hf : BddBelow (Set.range f))
    (c : CoreCoeff d) : formBottom f * coreNormSq c ≤ diagonalForm f c :=
  diagonalForm_ge_of_le_symbol (fun n => formBottom_le_of_bddBelow hf n) c

/-- **Coercivity at a lower bound of the symbol, on `L²`.** -/
theorem closedForm_ge_of_le_symbol {f : Idx d → ℝ} {θ : ℝ} (hθ : ∀ n, θ ≤ f n) (x : L2 d) :
    ENNReal.ofReal θ * closedNormSq x ≤ closedForm f x := by
  rw [← closedForm_const θ x]
  exact closedForm_mono_symbol hθ x

/-- **Coercivity at the bottom, on `L²`.**  Every state — retained or eliminated — satisfies it,
because the closed form carries one term per multi-index. -/
theorem closedForm_ge_formBottom {f : Idx d → ℝ} (hf : BddBelow (Set.range f)) (x : L2 d) :
    ENNReal.ofReal (formBottom f) * closedNormSq x ≤ closedForm f x :=
  closedForm_ge_of_le_symbol (fun n => formBottom_le_of_bddBelow hf n) x

/-- A bound that holds at every point of a set bounds the infimum of that set. -/
theorem sInf_ge_of_forall {X : Type*} {q : X → ℝ≥0∞} {c : ℝ≥0∞} {S : Set X}
    (h : ∀ x ∈ S, c ≤ q x) : c ≤ sInf (q '' S) :=
  le_sInf fun _ ⟨x, hxS, hy⟩ => hy ▸ h x hxS

/-- **Restriction to any sector does not lower the bottom.**  Let `S` be any set of *normalised*
retained states — in particular the transverse sector left by the BRST elimination.  The Rayleigh
infimum of the closed form over `S` is bounded below by any lower bound of the symbol, hence by
the bottom of the symbol itself (`sector_bottom_ge_formBottom`).  This is the plan's "restriction
to the transverse sector does not lower `θ_∞`", and its reformulation "the eliminated directions
carry no spectral weight near the bottom", in the only form this model has: the coercivity bound
is symbolwise, so restriction cannot improve on it. -/
theorem sector_bottom_ge_of_le_symbol {f : Idx d → ℝ} {θ : ℝ} (hθ : ∀ n, θ ≤ f n)
    (S : Set (L2 d)) (hS : ∀ x ∈ S, closedNormSq x = 1) :
    ENNReal.ofReal θ ≤ sInf (closedForm f '' S) :=
  sInf_ge_of_forall fun x hx => by
    have h1 : closedNormSq x = 1 := hS x hx
    rw [← mul_one (ENNReal.ofReal θ), ← h1]
    exact closedForm_ge_of_le_symbol hθ x

/-- The same statement at the bottom of a bounded-below symbol. -/
theorem sector_bottom_ge_formBottom {f : Idx d → ℝ} (hf : BddBelow (Set.range f))
    (S : Set (L2 d)) (hS : ∀ x ∈ S, closedNormSq x = 1) :
    ENNReal.ofReal (formBottom f) ≤ sInf (closedForm f '' S) :=
  sector_bottom_ge_of_le_symbol (fun n => formBottom_le_of_bddBelow hf n) S hS

end BookProof.YangMillsFormClosure
