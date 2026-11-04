import Mathlib
import BookProof.ReflectionPositivity.WilsonLinkLattice

/-!
# The past-class Wilson weight: reflection identity and measurability

`BookProof.ReflectionPositivity.WilsonLinkLattice` derives the plaquette classification and proves
that the Wilson action of the box is invariant under the reflected link configuration
(`wilsonLatticeAction_reflectConfig`).  Its `Honest boundary` records two missing links of the
reflection-positivity argument; this chapter supplies both.

## 1. The reflection identity for the concrete past-class weight

`wilsonLatticeAction_split` writes the action of the box as

`S = pastSideWeight + futureSideWeight − invariantWeight`,

and `pastSideWeight_congr` says the past sum is a function of the links based at time `≤ M` alone.
What was missing is the *identity* that makes the two sides the same function read on the two
half-spaces: reflecting the configuration carries the past-class sum onto the future-class sum,

`pastSideWeight β N (reflectConfig U) M = futureSideWeight β N U M`
(**`pastSideWeight_reflectConfig`**), and the invariant sum is reflection invariant
(**`invariantWeight_reflectConfig`**).

The geometric input is that the reflection of a plaquette has the time support of the original
under `t ↦ L − 1 − t` (**`timeSet_reflectPlaq`**, from the corner lemmas
`reflectS_*`/`reflectT_*`/`reflectT2_*` of the previous chapter), so with `L = 2M + 1` the past
side becomes the future side (**`IsPastSide_reflectPlaq`**) and the invariant class is preserved
(**`IsInvariant_reflectPlaq`**).  The matrix input is the trace identity
`Plaquette.trace_holonomy_reflectPlaq`.

Assembled with `wilsonLatticeAction_split`, these give the reflection invariance of the action
*as an identity between the three class sums*
(**`wilsonLatticeAction_reflectConfig_of_split`**) — the form `wilsonAction_reflect` of
`WilsonLattice` takes as an input — and consistency with the unconditional
`wilsonLatticeAction_reflectConfig` of the previous chapter is
**`wilsonLatticeAction_reflectConfig_agrees`**.

## 2. The past-class sum as a measurable half-space observable

`pastSideWeight` is a sum over *all* plaquettes with an `if`, hence a function on the full link
configuration.  For reflection positivity it must be a measurable function of the half-space plus
boundary data alone, which is the `hmeas`-style input `wilson_reflectionPositive` needs.  Here the
half-space configuration space is made explicit:

* `PastLink L M` (links based at time `≤ M`) and `BoundaryLink L M` (links based in the reflection
  slice `t = M`), with `PastConf`/`BoundConf` their matrix-valued configuration spaces;
* `pastLinkVar` — the link variable read from the past configuration below the slice and from the
  boundary configuration in the slice (a link that neither covers is sent to `0`; no past-side
  plaquette reads such a link, by `Plaquette.pastSide_link_time`);
* `pastConfig`, `pastHolonomy` — the link configuration and the plaquette holonomy rebuilt from
  `pastLinkVar`;
* **`measurable_of_inv_apply`** — the entries of `A ↦ A⁻¹` are measurable, from
  `A⁻¹ = det A⁻¹ • adjugate A` and continuity of the determinant and the adjugate (no continuity of
  the inverse map itself is claimed, which indeed fails at singular matrices);
* **`measurable_pastHolonomy_apply`** / **`measurable_pastHolonomy_trace`** — the entries and the
  trace of the past holonomy are measurable in `(y, z)`, assembled entrywise by
  `measurable_entry_mul` rather than by `fun_prop`, so no measurable structure on `Matrix` itself is
  needed;
* **`pastSideObservable`**, **`measurable_pastSideObservable`** — the past-class Wilson sum, as a
  function `PastConf → BoundConf → ℝ`, is measurable, and
  **`pastSideWeight_eq_observable_of_eq`** identifies it with `pastSideWeight` of any link
  configuration that agrees with `pastConfig y z` below the reflection slice.

## Honest boundary

The observable is measurable and *is* the past-class sum, but the reference measure on the
half-space configuration space is not instantiated: the measure-theoretic hypotheses of
`wilson_reflectionPositive` (`MeasureSpace` instances and `SFinite volume`) are left to the caller,
since the choice of the group measure is exactly the modelling decision that chapter records as
open.  No Haar measure, no gauge invariance, and no evaluation of the normalising constant is
claimed here.
-/

namespace BookProof.ReflectionPositivity

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {L : ℕ}

/-! ## 1. The time support of the reflected plaquette -/

/-- The base corner of the reflected square, spatial case. -/
@[simp] theorem reflectS_base' (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).base = theta p.base :=
  Plaquette.reflectS_base p h h2

/-- The base corner of the reflected square, time-first case. -/
theorem reflectT_base' (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).base = theta p.c10 := rfl

/-- The base corner of the reflected square, time-second case. -/
theorem reflectT2_base' (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).base = theta p.c01 := rfl

/-- **The corner set of the reflected plaquette is the `θ`-image of the original's**, spatial
case. -/
theorem siteSet_reflectS (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).siteSet = p.siteSet.image theta := by
  simp only [Plaquette.siteSet, reflectS_base' p h h2, Plaquette.reflectS_c10 p h h2,
    Plaquette.reflectS_c01 p h h2, Plaquette.reflectS_c11 p h h2]
  ext s
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨p.base, by simp, rfl⟩
    · exact ⟨p.c10, by simp, rfl⟩
    · exact ⟨p.c01, by simp, rfl⟩
    · exact ⟨p.c11, by simp, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl <;> simp

/-- **The corner set of the reflected plaquette is the `θ`-image of the original's**, time-first
case. -/
theorem siteSet_reflectT (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).siteSet = p.siteSet.image theta := by
  simp only [Plaquette.siteSet, reflectT_base' p h, Plaquette.reflectT_c10 p h,
    Plaquette.reflectT_c01 p h, Plaquette.reflectT_c11 p h]
  ext s
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨p.c10, by simp, rfl⟩
    · exact ⟨p.c11, by simp, rfl⟩
    · exact ⟨p.base, by simp, rfl⟩
    · exact ⟨p.c01, by simp, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl <;> simp

/-- **The corner set of the reflected plaquette is the `θ`-image of the original's**, time-second
case. -/
theorem siteSet_reflectT2 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).siteSet = p.siteSet.image theta := by
  simp only [Plaquette.siteSet, reflectT2_base' p h h2, Plaquette.reflectT2_c10 p h h2,
    Plaquette.reflectT2_c01 p h h2, Plaquette.reflectT2_c11 p h h2]
  ext s
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨p.c01, by simp, rfl⟩
    · exact ⟨p.base, by simp, rfl⟩
    · exact ⟨p.c11, by simp, rfl⟩
    · exact ⟨p.c10, by simp, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl <;> simp

/-- **The time support of the reflected plaquette is the `θ`-image of the original's**: replacing
`t` by `L − 1 − t` in the corner times. -/
theorem timeSet_reflectPlaq (p : Plaquette L) :
    (p.reflectPlaq).timeSet = p.timeSet.image (reflectTime L) := by
  have key : ∀ (q : Plaquette L), q.siteSet = p.siteSet.image theta →
      q.timeSet = p.timeSet.image (reflectTime L) := by
    intro q hq
    rw [Plaquette.timeSet, hq, Plaquette.timeSet, Finset.image_image, Finset.image_image]
    refine Finset.image_congr (f := fun x => time (theta x))
      (g := fun x => reflectTime L (time x)) (s := p.siteSet) fun x _ => ?_
    simp only [time_theta, reflectTime]
  by_cases h : p.dir = 2
  · rw [Plaquette.reflectPlaq_of_dir_eq p h]
    exact key _ (siteSet_reflectT p h)
  · by_cases h2 : p.dir2 = 2
    · rw [Plaquette.reflectPlaq_of_dir2_eq p h h2]
      exact key _ (siteSet_reflectT2 p h h2)
    · rw [Plaquette.reflectPlaq_of_dir_ne p h h2]
      exact key _ (siteSet_reflectS p h h2)

/-- The time of every corner of a plaquette is at most `2M` when `L = 2M + 1`, i.e. when the
reflection plane `t = M` is the middle slice: `s` is an actual site time, hence `< L`. -/
theorem timeSet_le_of_code {M : ℕ} (hL : L = 2 * M + 1) (p : Plaquette L) :
    ∀ s ∈ p.timeSet, s ≤ 2 * M := by
  intro s hs
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.1 hs
  have hlt : time x < L := (x 2).isLt
  omega

/-! ## 2. The reflection swaps the past and the future class -/

/-- **The reflection carries the past side to the future side**: for the middle reflection plane
`L = 2M + 1`, a plaquette is on the past side of the reflected square exactly when it is on the
future side of the original. -/
theorem IsPastSide_reflectPlaq {M : ℕ} (hL : L = 2 * M + 1) (p : Plaquette L) :
    IsPastSide M p.reflectPlaq ↔ IsFutureSide M p := by
  simp only [IsPastSide, IsFutureSide, timeSet_reflectPlaq]
  constructor
  · intro h s hs
    have hmem : reflectTime L s ∈ p.timeSet.image (reflectTime L) :=
      Finset.mem_image.2 ⟨s, hs, rfl⟩
    have h1 := h _ hmem
    have h2 := timeSet_le_of_code hL p s hs
    simp only [reflectTime] at h1 ⊢
    omega
  · intro h t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    have h1 := h s hs
    simp only [reflectTime]
    omega

/-- **The reflection preserves the invariant class**: a plaquette lies in the reflection slice
exactly when its reflection does. -/
theorem IsInvariant_reflectPlaq {M : ℕ} (hL : L = 2 * M + 1) (p : Plaquette L) :
    IsInvariant M p.reflectPlaq ↔ IsInvariant M p := by
  simp only [IsInvariant, timeSet_reflectPlaq]
  constructor
  · intro h s hs
    have hmem : reflectTime L s ∈ p.timeSet.image (reflectTime L) :=
      Finset.mem_image.2 ⟨s, hs, rfl⟩
    have h1 := h _ hmem
    have h2 := timeSet_le_of_code hL p s hs
    simp only [reflectTime] at h1 ⊢
    omega
  · intro h t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    have h1 := h s hs
    simp only [reflectTime, h1]
    omega

/-! ## 3. The reflection identity for the class sums -/

/-- **The reflection of the past-class Wilson sum is the future-class sum.**  Reflecting the link
configuration exchanges the two half-spaces, so summing the Wilson weights of the past-side
plaquettes of the reflected configuration gives the future-side sum of the original one.

This is the identity that makes `wilsonAction_reflect`'s `A(z, y₋)` and `A(z, y₊)` the same
function: with `pastSideWeight_congr` it says the two half-space actions agree term by term. -/
theorem pastSideWeight_reflectConfig {N M : ℕ} (hL : L = 2 * M + 1) (β : ℝ)
    (U : Link L → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    pastSideWeight β N (reflectConfig U) M = futureSideWeight β N U M := by
  classical
  let e : Plaquette L ≃ Plaquette L :=
    { toFun := Plaquette.reflectPlaq
      invFun := Plaquette.reflectPlaq
      left_inv := Plaquette.reflectPlaq_involutive
      right_inv := Plaquette.reflectPlaq_involutive }
  simp only [pastSideWeight, futureSideWeight]
  rw [← Equiv.sum_comp e
    (fun p => if IsPastSide M p then Plaquette.weight β N (reflectConfig U) p else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [IsPastSide_reflectPlaq hL p, Plaquette.weight, Plaquette.weight, plaqDensity, plaqDensity,
    Plaquette.trace_holonomy_reflectPlaq U hU p]

/-- **The reflection of the future-class sum is the past-class sum** — the same identity read the
other way, using that `reflectConfig` is an involution on unitary configurations. -/
theorem futureSideWeight_reflectConfig {N M : ℕ} (hL : L = 2 * M + 1) (β : ℝ)
    (U : Link L → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    futureSideWeight β N (reflectConfig U) M = pastSideWeight β N U M := by
  have h := pastSideWeight_reflectConfig (L := L) hL β (reflectConfig U)
    (reflectConfig_mem_unitaryGroup hU)
  rw [reflectConfig_involutive hU] at h
  exact h.symm

/-- **The invariant (boundary) sum is reflection invariant**: the boundary class is exactly the
fixed slice, so the reflection permutes it. -/
theorem invariantWeight_reflectConfig {N M : ℕ} (hL : L = 2 * M + 1) (β : ℝ)
    (U : Link L → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    invariantWeight β N (reflectConfig U) M = invariantWeight β N U M := by
  classical
  let e : Plaquette L ≃ Plaquette L :=
    { toFun := Plaquette.reflectPlaq
      invFun := Plaquette.reflectPlaq
      left_inv := Plaquette.reflectPlaq_involutive
      right_inv := Plaquette.reflectPlaq_involutive }
  simp only [invariantWeight]
  rw [← Equiv.sum_comp e
    (fun p => if IsInvariant M p then Plaquette.weight β N (reflectConfig U) p else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [IsInvariant_reflectPlaq hL p, Plaquette.weight, Plaquette.weight, plaqDensity, plaqDensity,
    Plaquette.trace_holonomy_reflectPlaq U hU p]

/-- **The reflection identity for the action, derived from the split.**  With
`wilsonLatticeAction_split` applied to both the configuration and its reflection, the three class
identities above give `S(U_θ) = S(U)`: the past sum of `U_θ` is the future sum of `U`, the future
sum of `U_θ` is the past sum of `U`, and the boundary sum is unchanged.  This is the invariance
`wilsonAction_reflect` of `WilsonLattice` takes as an input, obtained here from the concrete
past-class weight rather than assumed. -/
theorem wilsonLatticeAction_reflectConfig_of_split {N M : ℕ} (hL : L = 2 * M + 1) (β : ℝ)
    (U : Link L → Matrix (Fin N) (Fin N) ℂ) (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    wilsonLatticeAction β N (reflectConfig U) = wilsonLatticeAction β N U := by
  rw [wilsonLatticeAction_split (L := L) β N (reflectConfig U) M,
    wilsonLatticeAction_split (L := L) β N U M,
    pastSideWeight_reflectConfig hL β U hU,
    futureSideWeight_reflectConfig hL β U hU,
    invariantWeight_reflectConfig hL β U hU]
  ring

/-! ## 4. The past-class sum as a half-space observable -/

/-- The links that a past-side plaquette can use: those based at time at most `M`. -/
abbrev PastLink (L M : ℕ) : Type := {l : Link L // time l.base ≤ M}

/-- The links based in the reflection slice `t = M`. -/
abbrev BoundaryLink (L M : ℕ) : Type := {l : Link L // time l.base = M}

/-- The past half-space configuration space: matrix-valued link variables on the links based at
time at most `M`. -/
abbrev PastConf (L M N : ℕ) : Type := PastLink L M → Fin N → Fin N → ℂ

/-- The boundary-slice configuration space: matrix-valued link variables on the links based in the
reflection slice. -/
abbrev BoundConf (L M N : ℕ) : Type := BoundaryLink L M → Fin N → Fin N → ℂ

/-- **The link variable of a link**, read off the past half-space configuration (for links strictly
below the reflection slice) and the boundary configuration (for links in the slice).  A link that
neither covers is sent to `0`; no past-side plaquette reads such a link
(`Plaquette.pastSide_link_time`). -/
def pastLinkVar {M N : ℕ} (y : PastConf L M N) (z : BoundConf L M N) (l : Link L) :
    Fin N → Fin N → ℂ :=
  if h : time l.base ≤ M then (if hb : time l.base = M then z ⟨l, hb⟩ else y ⟨l, h⟩) else 0

/-- **The link configuration rebuilt from the half-space and boundary data.** -/
def pastConfig {M N : ℕ} (y : PastConf L M N) (z : BoundConf L M N) :
    Link L → Matrix (Fin N) (Fin N) ℂ :=
  fun l => Matrix.of (pastLinkVar y z l)

/-- **The holonomy of a plaquette, computed from the past-half-space link variable.**  It is the
holonomy of `pastConfig y z`, spelled out through `pastLinkVar` so that each factor is a matrix of
explicitly measurable functions. -/
def pastHolonomy {M N : ℕ} (y : PastConf L M N) (z : BoundConf L M N) (p : Plaquette L) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (pastLinkVar y z p.link0) * Matrix.of (pastLinkVar y z p.link1)
    * (Matrix.of (pastLinkVar y z p.link2))⁻¹ * (Matrix.of (pastLinkVar y z p.link3))⁻¹

theorem holonomy_pastConfig {M N : ℕ} (y : PastConf L M N) (z : BoundConf L M N)
    (p : Plaquette L) : p.holonomy (pastConfig y z) = pastHolonomy y z p := rfl

/-! ### Measurability of the pieces -/

/-- **Measurability of the entries of the matrix inverse**, from the determinant and the adjugate:
`A⁻¹ = A.det⁻¹ • A.adjugate` (`Matrix.inv_def`), and both factors are continuous in the entries
(`Continuous.matrix_det`, `Continuous.matrix_adjugate`).  No continuity of `A ↦ A⁻¹` itself is
claimed — that map is not continuous at singular matrices. -/
theorem measurable_of_inv_apply {α : Type*} [MeasurableSpace α] {n : Type*} [Fintype n]
    [DecidableEq n] (v : α → n → n → ℂ) (hv : Measurable v) (i j : n) :
    Measurable fun a => (Matrix.of (v a))⁻¹ i j := by
  have hof : Continuous fun g : (n → n → ℂ) => Matrix.of g := continuous_id
  have hdet : Measurable fun a => (Matrix.of (v a)).det :=
    (Continuous.matrix_det hof).measurable.comp hv
  have hadj_cont : Continuous fun g : (n → n → ℂ) => (Matrix.of g).adjugate :=
    Continuous.matrix_adjugate hof
  have hentry_cont : Continuous fun M : Matrix n n ℂ => M i j :=
    (continuous_apply j).comp (continuous_apply i)
  have hadj : Measurable fun a => (Matrix.of (v a)).adjugate i j :=
    (hentry_cont.comp hadj_cont).measurable.comp hv
  have hentry : ∀ a, (Matrix.of (v a))⁻¹ i j
      = (Matrix.of (v a)).det⁻¹ * (Matrix.of (v a)).adjugate i j := by
    intro a
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  simp only [hentry]
  exact (measurable_inv.comp hdet).mul hadj

theorem measurable_fst_apply {M N : ℕ} (l : PastLink L M) (i j : Fin N) :
    Measurable fun q : PastConf L M N × BoundConf L M N => q.1 l i j := by
  have h : Measurable fun f : PastConf L M N => f l i j :=
    (measurable_pi_apply (a := j)).comp
      ((measurable_pi_apply (a := i)).comp (measurable_pi_apply (a := l)))
  exact h.comp measurable_fst

theorem measurable_snd_apply {M N : ℕ} (l : BoundaryLink L M) (i j : Fin N) :
    Measurable fun q : PastConf L M N × BoundConf L M N => q.2 l i j := by
  have h : Measurable fun f : BoundConf L M N => f l i j :=
    (measurable_pi_apply (a := j)).comp
      ((measurable_pi_apply (a := i)).comp (measurable_pi_apply (a := l)))
  exact h.comp measurable_snd

/-- **The link variable is measurable in the half-space and boundary configurations.** -/
theorem measurable_pastLinkVar {M N : ℕ} (l : Link L) (i j : Fin N) :
    Measurable fun q : PastConf L M N × BoundConf L M N => pastLinkVar q.1 q.2 l i j := by
  by_cases h : time l.base ≤ M
  · by_cases hb : time l.base = M
    · simp only [pastLinkVar, dif_pos h, dif_pos hb]
      exact measurable_snd_apply (M := M) ⟨l, hb⟩ i j
    · simp only [pastLinkVar, dif_pos h, dif_neg hb]
      exact measurable_fst_apply (M := M) ⟨l, h⟩ i j
  · simp only [pastLinkVar, dif_neg h]
    exact measurable_const

theorem measurable_pastLinkVar_fn {M N : ℕ} (l : Link L) :
    Measurable fun q : PastConf L M N × BoundConf L M N => pastLinkVar q.1 q.2 l :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => measurable_pastLinkVar l i j

/-- **Entrywise measurability of a product of matrix-valued functions**, from entrywise
measurability of the factors — stated entrywise so that no measurable structure on `Matrix` itself
is needed. -/
theorem measurable_entry_mul {α : Type*} [MeasurableSpace α] {n : Type*} [Fintype n]
    {A B : α → Matrix n n ℂ} (hA : ∀ i j, Measurable fun a => A a i j)
    (hB : ∀ i j, Measurable fun a => B a i j) (i j : n) :
    Measurable fun a => (A a * B a) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul (hB k j)

/-- **The entries of the past-class holonomy are measurable** in the half-space and boundary
configurations.  The four factors are handled one at a time (`measurable_entry_mul`), the second
and third links through `measurable_of_inv_apply`. -/
theorem measurable_pastHolonomy_apply {M N : ℕ} (p : Plaquette L) (i j : Fin N) :
    Measurable fun q : PastConf L M N × BoundConf L M N => pastHolonomy q.1 q.2 p i j := by
  have h0 : ∀ k l' : Fin N, Measurable fun q : PastConf L M N × BoundConf L M N =>
      Matrix.of (pastLinkVar q.1 q.2 p.link0) k l' :=
    fun k l' => measurable_pastLinkVar p.link0 k l'
  have h1 : ∀ k l' : Fin N, Measurable fun q : PastConf L M N × BoundConf L M N =>
      Matrix.of (pastLinkVar q.1 q.2 p.link1) k l' :=
    fun k l' => measurable_pastLinkVar p.link1 k l'
  have h2 : ∀ k l' : Fin N, Measurable fun q : PastConf L M N × BoundConf L M N =>
      (Matrix.of (pastLinkVar q.1 q.2 p.link2))⁻¹ k l' := by
    intro k l'
    refine measurable_of_inv_apply (n := Fin N)
      (v := fun q : PastConf L M N × BoundConf L M N => pastLinkVar q.1 q.2 p.link2)
      (measurable_pastLinkVar_fn p.link2) k l'
  have h3 : ∀ k l' : Fin N, Measurable fun q : PastConf L M N × BoundConf L M N =>
      (Matrix.of (pastLinkVar q.1 q.2 p.link3))⁻¹ k l' := by
    intro k l'
    refine measurable_of_inv_apply (n := Fin N)
      (v := fun q : PastConf L M N × BoundConf L M N => pastLinkVar q.1 q.2 p.link3)
      (measurable_pastLinkVar_fn p.link3) k l'
  have h01 : ∀ k l' : Fin N, Measurable fun q : PastConf L M N × BoundConf L M N =>
      (Matrix.of (pastLinkVar q.1 q.2 p.link0) * Matrix.of (pastLinkVar q.1 q.2 p.link1)) k l' :=
    fun k l' => measurable_entry_mul h0 h1 k l'
  have h012 : ∀ k l' : Fin N, Measurable fun q : PastConf L M N × BoundConf L M N =>
      (Matrix.of (pastLinkVar q.1 q.2 p.link0) * Matrix.of (pastLinkVar q.1 q.2 p.link1)
        * (Matrix.of (pastLinkVar q.1 q.2 p.link2))⁻¹) k l' :=
    fun k l' => measurable_entry_mul h01 h2 k l'
  have h0123 : ∀ k l' : Fin N, Measurable fun q : PastConf L M N × BoundConf L M N =>
      (Matrix.of (pastLinkVar q.1 q.2 p.link0) * Matrix.of (pastLinkVar q.1 q.2 p.link1)
        * (Matrix.of (pastLinkVar q.1 q.2 p.link2))⁻¹
        * (Matrix.of (pastLinkVar q.1 q.2 p.link3))⁻¹) k l' :=
    fun k l' => measurable_entry_mul h012 h3 k l'
  exact h0123 i j

/-- **The trace of the past-class holonomy is measurable.** -/
theorem measurable_pastHolonomy_trace {M N : ℕ} (p : Plaquette L) :
    Measurable fun q : PastConf L M N × BoundConf L M N => (pastHolonomy q.1 q.2 p).trace := by
  have h : (fun q : PastConf L M N × BoundConf L M N => (pastHolonomy q.1 q.2 p).trace)
      = fun q => ∑ i : Fin N, pastHolonomy q.1 q.2 p i i := by
    funext q
    rfl
  rw [h]
  exact Finset.measurable_sum _ fun i _ => measurable_pastHolonomy_apply p i i

/-- **The Wilson weight of a plaquette is measurable in the half-space and boundary data.** -/
theorem measurable_weight_pastConfig {M N : ℕ} (β : ℝ) (p : Plaquette L) :
    Measurable fun q : PastConf L M N × BoundConf L M N =>
      Plaquette.weight β N (pastConfig q.1 q.2) p := by
  have htr : Measurable fun q : PastConf L M N × BoundConf L M N =>
      (pastHolonomy q.1 q.2 p).trace.re :=
    Complex.measurable_re.comp (measurable_pastHolonomy_trace p)
  have hval : ∀ q : PastConf L M N × BoundConf L M N,
      Plaquette.weight β N (pastConfig q.1 q.2) p
        = β * (1 - (pastHolonomy q.1 q.2 p).trace.re / (N : ℝ)) := by
    intro q
    simp only [Plaquette.weight, plaqDensity, holonomy_pastConfig]
  simp only [hval]
  exact measurable_const.mul (measurable_const.sub (htr.div_const (N : ℝ)))

/-! ### The past-class sum as a measurable half-space observable -/

/-- **The past-class Wilson sum, as a half-space observable**: the past-side weight of the link
configuration rebuilt from the past half-space and boundary data.  This is the `A(z, y₋)` of the
reflection-positivity argument, now a function on an explicit configuration space. -/
def pastSideObservable (β : ℝ) (N M : ℕ) : PastConf L M N → BoundConf L M N → ℝ :=
  fun y z => pastSideWeight β N (pastConfig y z) M

/-- The observable is the past-class sum of the reconstructed configuration, definitionally. -/
theorem pastSideWeight_eq_observable {N M : ℕ} (β : ℝ) (y : PastConf L M N)
    (z : BoundConf L M N) :
    pastSideWeight β N (pastConfig y z) M = pastSideObservable β N M y z := rfl

/-- **The past-class Wilson sum is a measurable half-space observable.**  It is a finite sum over
plaquettes, each term either `0` or `β · (1 − Re tr U_p / N)` with `U_p` the holonomy built from
`pastLinkVar` — measurable by `measurable_weight_pastConfig`. -/
theorem measurable_pastSideObservable {M N : ℕ} (β : ℝ) :
    Measurable fun q : PastConf L M N × BoundConf L M N => pastSideObservable β N M q.1 q.2 := by
  classical
  have hterm : ∀ p ∈ (Finset.univ : Finset (Plaquette L)),
      Measurable fun q : PastConf L M N × BoundConf L M N =>
        (if IsPastSide M p then Plaquette.weight β N (pastConfig q.1 q.2) p else 0) := by
    intro p _
    by_cases hp : IsPastSide M p
    · simp only [if_pos hp]
      exact measurable_weight_pastConfig β p
    · simp only [if_neg hp]
      exact measurable_const
  exact Finset.measurable_sum _ hterm

/-- **The packaging**: for any link configuration `U` that agrees with the reconstructed one below
the reflection slice, the past-class sum of `U` is the value of the half-space observable.  So the
past sum really is a function of `(z, y₋)` alone, and `measurable_pastSideObservable` applies to it
through this bridge — the `hmeas` input of `wilson_reflectionPositive`. -/
theorem pastSideWeight_eq_observable_of_eq {N M : ℕ} (β : ℝ)
    (U : Link L → Matrix (Fin N) (Fin N) ℂ) (y : PastConf L M N) (z : BoundConf L M N)
    (h : ∀ l : Link L, time l.base ≤ M → U l = pastConfig y z l) :
    pastSideWeight β N U M = pastSideObservable β N M y z := by
  rw [pastSideWeight_congr β N h, pastSideWeight_eq_observable]

end

end BookProof.ReflectionPositivity
