import Mathlib
import BookProof.ReflectionPositivity.WilsonLattice

/-!
# The plaquette past / invariant / future classification, derived from an explicit lattice

`BookProof.ReflectionPositivity.WilsonLattice` takes the classification of plaquettes as an
*input*: the holonomy of the `p`-th plaquette is a black-box function `U p y z` of the past
half-space and the boundary slice, and the action is *defined* as a sum of a past-, a future- and a
boundary-supported term.  Its `Honest boundary` says so explicitly: "the lattice geometry is an
input, not a construction".

This chapter removes that input.  It builds the lattice box, its links and its plaquettes with
their four corners, and *derives* the classification: the time support of a plaquette spans at most
one time step, every plaquette lies on the past side or on the future side of the reflection plane,
the invariant (boundary) class is exactly the intersection of the two, and the reflection swaps the
past and the future side.  On top of that it builds the plaquette holonomy from the four links and
*proves the sum split* of the resulting Wilson action: past, future and invariant, with the
invariant plaquettes counted on both sides.

## Contents

* `Site`, `stepSite`, `Link`, **`Link.ofStep`** — the sites of the `L × L × L` box and its
  oriented links (a base, a direction, the target, and the proof that the target is the step in
  that direction);
* `time`, `theta`, **`theta_involutive`**, **`time_theta`**, `time_theta_le` — the time coordinate
  and the reflection `t ↦ L − 1 − t`, an involution that fixes the middle slice when `L = 2M + 1`;
* `Plaquette` with `c10`, `c01`, `c11` (its four corners), `siteSet` (the corner set) and
  **`link0`, `link1`, `link2`, `link3`** — **the four links, attached to the corner data**:
  `base → c10`, `c10 → c11`, `c01 → c11`, `base → c01` (**`link_targets`**,
  **`link_endpoints_mem`**).  The diagonal step closes the square (**`stepSite_c01`**); that the
  spatial steps commute is `c10_apply_dir2` / `c01_apply_dir`;
* **`timeSet_subset`** — **the time support of a plaquette is contained in `{t, t + 1}`** with `t`
  the time of its base corner: a plaquette is either spatial (all four corners at one time) or
  spans exactly one time step;
* `IsPastSide`, `IsFutureSide`, `IsInvariant` — the three classes relative to the reflection plane
  `t = M`;
* **`plaq_cover`** — **every plaquette is on the past side or on the future side**: there is no
  fourth class;
* **`plaq_classification`** — the two sides cover the plaquettes and their intersection is exactly
  the invariant (boundary) class, so past / invariant / future partition them;
* **`pastSide_image_iff`** — under the reflection `t ↦ L − 1 − t` the past side becomes the future
  side: the future class is the image of the past class;
* **`Plaquette.holonomy`** — the holonomy of a plaquette, built from its four links,
  `U(base→c10) · U(c10→c11) · U(c01→c11)⁻¹ · U(base→c01)⁻¹`;
* **`Plaquette.holonomy_mem_unitaryGroup`** — with unitary link variables the holonomy is unitary,
  and **`re_trace_inv_of_mem_unitaryGroup`** gives `Re tr (h⁻¹) = Re tr h`, so
  **`Plaquette.plaqDensity_holonomy_inv`** / **`Plaquette.plaquetteWeight_holonomy_inv`**: the
  Wilson weight does not see the orientation of the square;
* `Plaquette.pastSide_link_time`, `Plaquette.futureSide_link_time` — a past-side plaquette uses
  only links at times at most `M`, a future-side one only links at times at least `M`: the past
  and future classes really are supported on the two half-spaces plus the boundary slice;
* **`wilsonLatticeAction`**, `pastSideWeight`, `futureSideWeight`, `invariantWeight` and
  **`wilsonLatticeAction_split`** — **the action of the box splits along the reflection plane**,
  `S = (past) + (future) − (invariant)`;
* **`pastSideWeight_congr`**, **`futureSideWeight_congr`**, **`invariantWeight_congr`** — **each
  class sum depends only on the links of its own class**: the past-side action is unchanged when the
  configuration is changed on links based in the future, and conversely; the invariant sum sees only
  links based in the reflection slice;
* `theta`, `theta_apply_ne`, `theta_apply_two`, `theta_update_ne`, `theta_update_two`,
  `stepSite_theta_of_ne`, `stepSite_theta_two` — the reflection `θ` on sites, its action on
  coordinate updates, and how it moves a single step in a direction; `Link.reflect` with its
  projections, `Link.reflect_of_ne`, `Link.reflect_of_eq` and `Link.reflect_involutive` — the
  reflection on links, involutive;
* `Plaquette.reflectT`, `Plaquette.reflectT2`, **`Plaquette.reflectS`**, `Plaquette.reflectPlaq` —
  the reflected square.  A *spatial* plaquette is the case where both of its directions are
  spatial, and then the reflection leaves the direction pair alone; in the two temporal cases the
  label `dir`/`dir2` is swapped, which is exactly the reversal of the time step;
* **`Plaquette.reflectS_link0`**, **`reflectS_link1`**, **`reflectS_link2`**, **`reflectS_link3`** —
  **the reflected square's four links are the reflected links of the original**: for a spatial
  plaquette, `(p.reflectS h h2).link k = Link.reflect (p.link k)` for all four `k`;
* **`Plaquette.reflectT_link0`**–**`reflectT_link3`**, **`Plaquette.reflectT2_link0`**–
  **`reflectT2_link3`** — **the four link identities in the two temporal cases**, through the corner
  lemmas `reflectT_c10`/`_c01`/`_c11` and `reflectT2_c10`/`_c01`/`_c11` (and the step lemmas
  `stepSite_c10`, `stepSite_base_dir2`, `stepSite_c11`, `stepSite_*_two`).  The correspondence is
  cyclic: time-first `link0' = R link1`, `link1' = R link2`, `link2' = R link3`, `link3' = R link0`;
  time-second `link0'' = R link3`, `link1'' = R link0`, `link2'' = R link1`, `link3'' = R link2`;
* **`Plaquette.holonomy_reflectS`**, **`Plaquette.trace_holonomy_reflectS`** — **the holonomy is
  carried across the reflection**: for a spatial plaquette and the reflected configuration
  `reflectConfig`, `U_θ (h_θp) = U_p⁻¹`, hence `Re tr (U_θ h_θp) = Re tr (U_p h_p)`.  This is the
  bridge `plaquetteWeight`'s black-box `U` in `WilsonLattice` needs, in the spatial case;
* **`Plaquette.holonomy_reflectT`**, **`holonomy_reflectT2`** — the same in the two temporal cases,
  where the reflected holonomy is the cyclic rotation `u₁u₂⁻¹u₃⁻¹u₀` (time-first) or
  `u₃⁻¹u₀u₁u₂⁻¹` (time-second) of `u₀u₁u₂⁻¹u₃⁻¹`; the inverses that the time reversal introduces are
  removed by `inv_inv_of_mem_unitaryGroup`, so both statements take unitarity of the links;
* **`Plaquette.trace_holonomy_reflectT`**, **`trace_holonomy_reflectT2`**, and the umbrella
  **`Plaquette.trace_holonomy_reflectPlaq`** — **the trace identity in every case**
  (`Re tr h_{θp} = Re tr h_p`), by `trace_rot` / `trace_rot_inv`;
* **`Plaquette.reflectPlaq_involutive`** — the reflection of plaquettes is an involution (through
  `Plaquette.eq_of_data`, which reduces an equality of plaquettes to their base and two
  directions), hence a permutation of the plaquette set; with it the trace identity becomes
  **`wilsonLatticeAction_reflectConfig`**: the Wilson action of the box is *unchanged* by
  replacing the link configuration by its reflection.

## Honest boundary

The chapter derives the *classification*, attaches the four links of every plaquette to its corner
data, builds the holonomy from them, and splits the resulting action along the reflection plane.
What is **not** done here, and is recorded rather than assumed:

* the holonomy is now carried across the reflection in **all three cases**, and the trace identity
  `Re tr h_{θp} = Re tr h_p` holds for every plaquette (`trace_holonomy_reflectPlaq`).  The
temporal cases are not equalities of holonomies but cyclic rotations of them — a time-link is sent
  by the reflection to a link based at the *other* end, since the time coordinate is reversed, so
  the reflected square's time-step base is `θ(c11)` or `θ(c01)` rather than `θ(base)` — which is why
  those two cases are stated for the trace, and why they need unitarity of the link variables;
  and the trace identity is lifted to the **action** by the reindexing `Σ_p w_p (U_θ) =
  Σ_p w_{θp} (U_θ) = Σ_p w_p (U)`, for which `reflectPlaq` is an involution of the plaquette set
  (`reflectPlaq_involutive`) — so `wilsonLatticeAction_reflectConfig` holds: the action is exactly
  invariant under `reflectConfig`;
* the split is proved as a sum identity over the classes, and each class sum is proved to depend
  only on the links of its class (`pastSideWeight_congr` and its two companions), so the past sum is
  a function of the past-half-space and boundary link data alone.  What is not carried out is the
  packaging: a named half-space configuration space with the induced measurable structure, the
  identification of the past sum with a function on it, and its measurability — i.e. the
  `hmeas`-style input `wilsonAction`'s Feynman–Kac form needs.
-/

namespace BookProof.ReflectionPositivity

open scoped BigOperators

/-! ## 1. Sites and links -/

/-- The sites of the `L × L × L` box: three coordinates in `Fin L`. -/
abbrev Site (L : ℕ) := Fin 3 → Fin L

/-- The site one step from `x` in direction `μ`, when that step stays inside the box. -/
def stepSite {L : ℕ} (x : Site L) (μ : Fin 3) : Option (Site L) :=
  if h : (x μ).val + 1 < L then some (Function.update x μ ⟨(x μ).val + 1, h⟩) else none

/-- An **oriented link**: a base site, a direction, the target site, and the proof that the target
is the step from the base in that direction. -/
structure Link (L : ℕ) where
  /-- The lower end of the link. -/
  base : Site L
  /-- The direction of the link. -/
  dir : Fin 3
  /-- The upper end of the link. -/
  target : Site L
  /-- The target is the step from the base. -/
  isStep : stepSite base dir = some target

/-- **The link from a site in a direction that has room**: the oriented link whose base is the
site and whose target is the step.  This is how the four links of a plaquette are attached to its
corner data. -/
def Link.ofStep {L : ℕ} (x : Site L) (μ : Fin 3) (h : (x μ).val + 1 < L) : Link L :=
  ⟨x, μ, Function.update x μ ⟨(x μ).val + 1, h⟩, by simp only [stepSite, dif_pos h]⟩

/-- The time coordinate of a site. -/
def time {L : ℕ} (x : Site L) : ℕ := (x 2).val

/-- The **time reflection** `t ↦ L − 1 − t`: it reverses the time coordinate and fixes the spatial
ones.  For `L = 2M + 1` it fixes the middle slice `t = M`. -/
def theta {L : ℕ} (x : Site L) : Site L := Function.update x 2 (Fin.rev (x 2))

/-- The reflection is an involution. -/
theorem theta_involutive {L : ℕ} : Function.Involutive (theta (L := L)) := by
  intro x
  funext j
  by_cases h : j = 2
  · subst h
    simp only [theta, Function.update_apply, if_true, Fin.rev_rev]
  · simp only [theta, Function.update_apply, if_neg h]

/-- The reflection sends the time `t` to `L − 1 − t`. -/
theorem time_theta {L : ℕ} (x : Site L) : time (theta x) = L - 1 - time x := by
  have hx := (x 2).isLt
  simp only [theta, time, Function.update_apply, if_true, Fin.val_rev]
  omega

/-- The reflected time stays in the box. -/
theorem time_theta_le {L : ℕ} (x : Site L) : time (theta x) ≤ L - 1 := by
  rw [time_theta]
  omega

/-! ## 2. Plaquettes and the time support -/

/-- A **plaquette**: a base corner, two distinct directions and the room to step in both, so that
the four corners `base`, `c10`, `c01`, `c11` all lie in the box. -/
structure Plaquette (L : ℕ) where
  /-- The corner with the lowest coordinates in both directions. -/
  base : Site L
  /-- The first direction of the square. -/
  dir : Fin 3
  /-- The second direction of the square. -/
  dir2 : Fin 3
  /-- The two directions are distinct — a plaquette is a genuine square. -/
  ne : dir ≠ dir2
  /-- There is room to step in the first direction. -/
  ok1 : (base dir).val + 1 < L
  /-- There is room to step in the second direction. -/
  ok2 : (base dir2).val + 1 < L

namespace Plaquette

variable {L : ℕ}

/-- The corner one step in the first direction. -/
def c10 (p : Plaquette L) : Site L :=
  Function.update p.base p.dir ⟨(p.base p.dir).val + 1, p.ok1⟩

/-- The corner one step in the second direction. -/
def c01 (p : Plaquette L) : Site L :=
  Function.update p.base p.dir2 ⟨(p.base p.dir2).val + 1, p.ok2⟩

/-- Stepping in the first direction leaves the second coordinate untouched, so the room to step
from `c10` in the second direction is the room at the base corner. -/
theorem c10_apply_dir2 (p : Plaquette L) : p.c10 p.dir2 = p.base p.dir2 := by
  simp only [c10, Function.update_apply, if_neg (Ne.symm p.ne)]

/-- Stepping in the second direction leaves the first coordinate untouched. -/
theorem c01_apply_dir (p : Plaquette L) : p.c01 p.dir = p.base p.dir := by
  simp only [c01, Function.update_apply, if_neg p.ne]

/-- The room to step from `c10` in the second direction. -/
theorem ok11 (p : Plaquette L) : (p.c10 p.dir2).val + 1 < L := by
  rw [c10_apply_dir2]
  exact p.ok2

/-- The room to step from `c01` in the first direction. -/
theorem ok11' (p : Plaquette L) : (p.c01 p.dir).val + 1 < L := by
  rw [c01_apply_dir]
  exact p.ok1

/-- The corner one step in both directions, reached from `c10` along the second direction. -/
def c11 (p : Plaquette L) : Site L :=
  Function.update p.c10 p.dir2 ⟨(p.c10 p.dir2).val + 1, p.ok11⟩

/-- The four corners of the plaquette, as a finite set of sites. -/
def siteSet (p : Plaquette L) : Finset (Site L) := {p.base, p.c10, p.c01, p.c11}

/-- **The first link of the square**, `base → c10`. -/
def link0 (p : Plaquette L) : Link L := Link.ofStep p.base p.dir p.ok1

/-- **The second link of the square**, `c10 → c11`. -/
def link1 (p : Plaquette L) : Link L := Link.ofStep p.c10 p.dir2 p.ok11

/-- **The third link of the square**, `base → c01`. -/
def link3 (p : Plaquette L) : Link L := Link.ofStep p.base p.dir2 p.ok2

theorem link0_base (p : Plaquette L) : p.link0.base = p.base := rfl
theorem link0_target (p : Plaquette L) : p.link0.target = p.c10 := rfl
theorem link1_base (p : Plaquette L) : p.link1.base = p.c10 := rfl
theorem link1_target (p : Plaquette L) : p.link1.target = p.c11 := rfl
theorem link3_base (p : Plaquette L) : p.link3.base = p.base := rfl
theorem link3_target (p : Plaquette L) : p.link3.target = p.c01 := rfl

/-- **The square closes**: the step from `c01` in the first direction lands on `c11`, so the
fourth link `c01 → c11` really is a link of the lattice. -/
theorem stepSite_c01 (p : Plaquette L) : stepSite p.c01 p.dir = some p.c11 := by
  rw [stepSite, dif_pos p.ok11']
  congr 1
  funext μ
  simp only [c11, c10, c01, Function.update_apply]
  by_cases h1 : μ = p.dir
  · subst h1
    simp [p.ne]
  · by_cases h2 : μ = p.dir2
    · subst h2
      simp [Ne.symm p.ne]
    · simp [h1, h2]

/-- **The fourth link of the square**, `c01 → c11`. -/
def link2 (p : Plaquette L) : Link L := ⟨p.c01, p.dir, p.c11, p.stepSite_c01⟩

theorem link2_base (p : Plaquette L) : p.link2.base = p.c01 := rfl
theorem link2_target (p : Plaquette L) : p.link2.target = p.c11 := rfl

/-- **The four links of a plaquette, attached to its corner data**: the square is
`base → c10 → c11` and `base → c01 → c11`, i.e. the four links read around the boundary of the
plaquette. -/
theorem link_targets (p : Plaquette L) :
    p.link0.base = p.base ∧ p.link0.target = p.c10
      ∧ p.link1.base = p.c10 ∧ p.link1.target = p.c11
      ∧ p.link2.base = p.c01 ∧ p.link2.target = p.c11
      ∧ p.link3.base = p.base ∧ p.link3.target = p.c01 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Both ends of every link are corners of the plaquette**: the links use nothing outside the
corner data. -/
theorem link_endpoints_mem (p : Plaquette L) :
    p.link0.base ∈ p.siteSet ∧ p.link0.target ∈ p.siteSet
      ∧ p.link1.base ∈ p.siteSet ∧ p.link1.target ∈ p.siteSet
      ∧ p.link2.base ∈ p.siteSet ∧ p.link2.target ∈ p.siteSet
      ∧ p.link3.base ∈ p.siteSet ∧ p.link3.target ∈ p.siteSet := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [siteSet, link0_base, link0_target, link1_base, link1_target, link2_base,
      link2_target, link3_base, link3_target]
  all_goals simp

/-- The time support of the plaquette: the times of its four corners. -/
def timeSet (p : Plaquette L) : Finset ℕ := p.siteSet.image time

/-- The time of the corner stepped in the first direction. -/
theorem time_c10 (p : Plaquette L) :
    time p.c10 = if p.dir = 2 then time p.base + 1 else time p.base := by
  simp only [c10, time, Function.update_apply]
  by_cases h : p.dir = 2
  · simp [h]
  · simp [h, Ne.symm h]

/-- The time of the corner stepped in the second direction. -/
theorem time_c01 (p : Plaquette L) :
    time p.c01 = if p.dir2 = 2 then time p.base + 1 else time p.base := by
  simp only [c01, time, Function.update_apply]
  by_cases h : p.dir2 = 2
  · simp [h]
  · simp [h, Ne.symm h]

/-- The time of the doubly stepped corner. -/
theorem time_c11 (p : Plaquette L) :
    time p.c11 = if p.dir2 = 2 then time p.base + 1 else time p.c10 := by
  have hv : (p.c10 p.dir2).val = (p.base p.dir2).val := by rw [c10_apply_dir2]
  simp only [c11, time, Function.update_apply]
  by_cases h : p.dir2 = 2
  · simp only [h] at hv
    simp [h, hv]
  · simp [h, Ne.symm h]

/-- **The time support of a plaquette spans at most one time step**: it is contained in
`{t, t + 1}`, where `t` is the time of the base corner.  A plaquette using no time direction is
spatial (support `{t}`); one using the time direction spans `{t, t + 1}`. -/
theorem timeSet_subset (p : Plaquette L) : p.timeSet ⊆ {time p.base, time p.base + 1} := by
  intro s hs
  simp only [timeSet, siteSet, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  obtain ⟨x, hx, rfl⟩ := hs
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · rw [time_c10]; split_ifs <;> omega
  · rw [time_c01]; split_ifs <;> omega
  · rw [time_c11, time_c10]; split_ifs <;> omega

end Plaquette

/-! ## 3. The three classes, relative to the reflection plane -/

/-- On the **past side** of the reflection plane `t = M`: every corner of the plaquette is at a
time no larger than `M`.  Such a plaquette uses only links in the past half-space and in the
boundary slice, so it contributes to the past half-space action. -/
def IsPastSide {L : ℕ} (M : ℕ) (p : Plaquette L) : Prop :=
  ∀ s ∈ p.timeSet, s ≤ M

/-- On the **future side** of the reflection plane: every corner is at a time no smaller than
`M`. -/
def IsFutureSide {L : ℕ} (M : ℕ) (p : Plaquette L) : Prop :=
  ∀ s ∈ p.timeSet, M ≤ s

/-- **Invariant under the reflection**: the plaquette lies in the reflection slice itself, so it
uses only links at time `M` and contributes to the boundary action `b(z)` only. -/
def IsInvariant {L : ℕ} (M : ℕ) (p : Plaquette L) : Prop :=
  ∀ s ∈ p.timeSet, s = M

/-- **Covering**: relative to the reflection plane, every plaquette is on the past side or on the
future side.  This is the derived form of the classification the Wilson action takes as an input:
no plaquette needs a fourth class. -/
theorem plaq_cover {L : ℕ} (M : ℕ) (p : Plaquette L) :
    IsPastSide M p ∨ IsFutureSide M p := by
  by_cases h : M ≤ time p.base
  · refine Or.inr fun s hs => ?_
    have hsub := Plaquette.timeSet_subset p hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
    rcases hsub with rfl | rfl <;> omega
  · refine Or.inl fun s hs => ?_
    have hsub := Plaquette.timeSet_subset p hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
    rcases hsub with rfl | rfl <;> omega

/-- **The classification**: the past side and the future side cover all plaquettes, and their
intersection is exactly the reflection-invariant class.  So with the two sides read as "supported
in the past half-space together with the boundary slice" and likewise for the future, the three
classes past / invariant / future partition the plaquettes. -/
theorem plaq_classification {L : ℕ} (M : ℕ) (p : Plaquette L) :
    (IsPastSide M p ∨ IsFutureSide M p)
      ∧ (IsPastSide M p ∧ IsFutureSide M p ↔ IsInvariant M p) := by
  refine ⟨plaq_cover M p, ?_⟩
  constructor
  · rintro ⟨hp, hf⟩ s hs
    exact le_antisymm (hp s hs) (hf s hs)
  · intro h
    exact ⟨fun s hs => (h s hs).le, fun s hs => (h s hs).ge⟩

/-! ## 4. The reflection swaps past and future -/

/-- The action of the time reflection on a time: `t ↦ L − 1 − t`. -/
def reflectTime (L : ℕ) (t : ℕ) : ℕ := L - 1 - t

/-- **The reflection carries the past side to the future side.**  For a set of times `S` inside the
box, "all times at most `M`" becomes, after `t ↦ L − 1 − t`, "all times at least `M`": the future
class is the image of the past class.  This is exactly the hypothesis that `wilsonAction` (and
`wilsonAction_reflect`) took as an input. -/
theorem pastSide_image_iff {L M : ℕ} (hL : L = 2 * M + 1) (S : Finset ℕ)
    (hS : ∀ s ∈ S, s ≤ 2 * M) :
    (∀ s ∈ S, s ≤ M) ↔ ∀ s ∈ S.image (reflectTime L), M ≤ s := by
  constructor
  · intro h t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    simp only [reflectTime]
    have := h s hs
    omega
  · intro h s hs
    have hmem : reflectTime L s ∈ S.image (reflectTime L) := Finset.mem_image.2 ⟨s, hs, rfl⟩
    have := h _ hmem
    simp only [reflectTime] at this
    have := hS s hs
    omega

/-! ## 5. The holonomy, from the four links -/

/-! A link variable is a matrix `U l` attached to each oriented link `l`.  The holonomy of a
plaquette is the ordered product of its four link variables; the two links that run into the top
corner are traversed backwards and hence enter inverted.  The lemmas in this section are the ones
the reflection argument needs: the holonomy of a square with unitary links is unitary, and the real
trace — the only thing the Wilson weight sees — is unchanged when the square is traversed the
other way round. -/

variable {L N : ℕ}

/-- The inverse of a unitary matrix is its star. -/
theorem inv_eq_star_of_mem_unitaryGroup {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : U⁻¹ = star U := by
  have h : star U * U = 1 := mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.1 hU)
  exact Matrix.inv_eq_left_inv h

/-- Unitary matrices are closed under inversion. -/
theorem mem_unitaryGroup_inv {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : U⁻¹ ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, inv_eq_star_of_mem_unitaryGroup hU]
  simp only [star_star]
  exact mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.1 hU)

/-- **The real trace is unchanged by inversion of a unitary matrix.**  For a unitary `U`,
`U⁻¹ = star U` and the trace of `star U` is the complex conjugate of the trace, so the real parts
agree: `Re tr` does not see the orientation of a square. -/
theorem re_trace_inv_of_mem_unitaryGroup {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : (U⁻¹).trace.re = U.trace.re := by
  rw [inv_eq_star_of_mem_unitaryGroup hU, Matrix.star_eq_conjTranspose,
    Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]

/-- The **plaquette holonomy**, read around the square `base → c10 → c11 → c01 → base`:
`U(base→c10) · U(c10→c11) · U(c01→c11)⁻¹ · U(base→c01)⁻¹`.  The links starting at `c01` and
`c11` are traversed from their upper end, which is why they appear inverted. -/
noncomputable def Plaquette.holonomy (U : Link L → Matrix (Fin N) (Fin N) ℂ) (p : Plaquette L) :
    Matrix (Fin N) (Fin N) ℂ :=
  U p.link0 * U p.link1 * (U p.link2)⁻¹ * (U p.link3)⁻¹

/-- The holonomy written out in terms of the four corner steps. -/
theorem Plaquette.holonomy_def (U : Link L → Matrix (Fin N) (Fin N) ℂ) (p : Plaquette L) :
    p.holonomy U = U (Link.ofStep p.base p.dir p.ok1) * U (Link.ofStep p.c10 p.dir2 p.ok11)
      * (U p.link2)⁻¹ * (U (Link.ofStep p.base p.dir2 p.ok2))⁻¹ :=
  rfl

/-- **The holonomy of a square with unitary links is unitary**: products and inverses of unitary
matrices are unitary. -/
theorem Plaquette.holonomy_mem_unitaryGroup {U : Link L → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) (p : Plaquette L) :
    p.holonomy U ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  unfold Plaquette.holonomy
  refine mul_mem (mul_mem (mul_mem (hU p.link0) (hU p.link1))
    (mem_unitaryGroup_inv (hU p.link2))) (mem_unitaryGroup_inv (hU p.link3))

/-- **The Wilson weight does not see the orientation of the square**: the holonomy of the square
traversed the other way round is the inverse matrix, and `Re tr` of an inverse unitary matrix is
the `Re tr` of the matrix. -/
theorem Plaquette.plaqDensity_holonomy_inv {U : Link L → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) (p : Plaquette L) :
    plaqDensity N (p.holonomy U)⁻¹ = plaqDensity N (p.holonomy U) := by
  have hunit := Plaquette.holonomy_mem_unitaryGroup hU p
  simp only [plaqDensity, re_trace_inv_of_mem_unitaryGroup hunit]

/-- The same statement for the Boltzmann weight. -/
theorem Plaquette.plaquetteWeight_holonomy_inv {β : ℝ} {U : Link L → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) (p : Plaquette L) :
    plaquetteWeight β N (p.holonomy U)⁻¹ = plaquetteWeight β N (p.holonomy U) := by
  simp only [plaquetteWeight, Plaquette.plaqDensity_holonomy_inv hU p]

/-! ## 6. The action of the box, and its split along the reflection plane -/

/-! With the classes in hand, the Wilson action of the box — the sum of the plaquette weights over
*all* plaquettes, with the geometry derived above — is split into the three classes.  This is the
sum split `S = A(z,y₋) + A(z,y₊) + b(z)` that `wilsonAction` in `WilsonLattice` takes as an
input: the past and future sums are the two half-space actions, and the invariant plaquettes are
counted on both sides, so they enter once with a minus sign. -/

noncomputable section

/-- The Wilson weight of a lattice plaquette, from its holonomy. -/
def Plaquette.weight (β : ℝ) (N : ℕ) (U : Link L → Matrix (Fin N) (Fin N) ℂ) (p : Plaquette L) :
    ℝ :=
  β * plaqDensity N (p.holonomy U)

/-- A plaquette is determined by its data — the base corner and the two directions; the remaining
fields are proofs. -/
theorem Plaquette.data_injective :
    Function.Injective fun p : Plaquette L => (p.base, p.dir, p.dir2) := by
  rintro ⟨b, μ, ν, h1, h2, h3⟩ ⟨b', μ', ν', h1', h2', h3'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- The plaquettes of the box form a finite type. -/
instance Plaquette.instFintype : Fintype (Plaquette L) :=
  Fintype.ofInjective (fun p : Plaquette L => (p.base, p.dir, p.dir2)) Plaquette.data_injective

/-- Paired with the classical decidability of the equality of plaquettes, the plaquettes of the
box can be summed over. -/
instance Plaquette.instDecidableEq : DecidableEq (Plaquette L) := Classical.decEq _

/-- **The Wilson action of the box**: the sum of the plaquette weights over all plaquettes. -/
def wilsonLatticeAction (β : ℝ) (N : ℕ) (U : Link L → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ p : Plaquette L, p.weight β N U

/-- The total weight of the **past-side** plaquettes. -/
def pastSideWeight (β : ℝ) (N : ℕ) (U : Link L → Matrix (Fin N) (Fin N) ℂ) (M : ℕ) : ℝ := by
  classical
  exact ∑ p : Plaquette L, if IsPastSide M p then p.weight β N U else 0

/-- The total weight of the **future-side** plaquettes. -/
def futureSideWeight (β : ℝ) (N : ℕ) (U : Link L → Matrix (Fin N) (Fin N) ℂ) (M : ℕ) : ℝ := by
  classical
  exact ∑ p : Plaquette L, if IsFutureSide M p then p.weight β N U else 0

/-- The total weight of the **invariant** plaquettes (the reflection slice). -/
def invariantWeight (β : ℝ) (N : ℕ) (U : Link L → Matrix (Fin N) (Fin N) ℂ) (M : ℕ) : ℝ := by
  classical
  exact ∑ p : Plaquette L, if IsInvariant M p then p.weight β N U else 0

/-- **A past-side plaquette uses only links at times at most `M`**: its four links have their base
in the past half-space or in the reflection slice, so its weight is a function of the past
half-space configuration and the boundary slice alone — it is a term of `A(z, y₋)`. -/
theorem Plaquette.pastSide_link_time {M : ℕ} (p : Plaquette L) (hp : IsPastSide M p) :
    time p.link0.base ≤ M ∧ time p.link1.base ≤ M
      ∧ time p.link2.base ≤ M ∧ time p.link3.base ≤ M := by
  have hmem : ∀ x ∈ p.siteSet, time x ≤ M := fun x hx => hp _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [link0_base, link1_base, link2_base, link3_base]
  · exact hmem _ (by simp [Plaquette.siteSet])
  · exact hmem _ (by simp [Plaquette.siteSet])
  · exact hmem _ (by simp [Plaquette.siteSet])
  · exact hmem _ (by simp [Plaquette.siteSet])

/-- **A future-side plaquette uses only links at times at least `M`**: its weight is a term of
`A(z, y₊)`. -/
theorem Plaquette.futureSide_link_time {M : ℕ} (p : Plaquette L) (hf : IsFutureSide M p) :
    M ≤ time p.link0.base ∧ M ≤ time p.link1.base
      ∧ M ≤ time p.link2.base ∧ M ≤ time p.link3.base := by
  have hmem : ∀ x ∈ p.siteSet, M ≤ time x := fun x hx => hf _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [link0_base, link1_base, link2_base, link3_base]
  · exact hmem _ (by simp [Plaquette.siteSet])
  · exact hmem _ (by simp [Plaquette.siteSet])
  · exact hmem _ (by simp [Plaquette.siteSet])
  · exact hmem _ (by simp [Plaquette.siteSet])

/-- **The split of the action along the reflection plane.**  Every plaquette lies in one of the
three classes and an invariant plaquette lies on both sides, so
`S = (past sum) + (future sum) − (invariant sum)`.  Combined with `pastSide_link_time` and
`futureSide_link_time` this is the sum split `S = A(z,y₋) + A(z,y₊) + b(z)` of `wilsonAction`,
with `b` the negative of the invariant sum. -/
theorem wilsonLatticeAction_split (β : ℝ) (N : ℕ) (U : Link L → Matrix (Fin N) (Fin N) ℂ)
    (M : ℕ) :
    wilsonLatticeAction (L := L) β N U
      = pastSideWeight β N U M + futureSideWeight β N U M - invariantWeight β N U M := by
  classical
  have hpt : ∀ p : Plaquette L, p.weight β N U
      = (if IsPastSide M p then p.weight β N U else 0)
        + (if IsFutureSide M p then p.weight β N U else 0)
        - (if IsInvariant M p then p.weight β N U else 0) := by
    intro p
    have hclass := plaq_classification M p
    by_cases hp : IsPastSide M p
    · by_cases hf : IsFutureSide M p
      · have hi : IsInvariant M p := hclass.2.1 ⟨hp, hf⟩
        simp [hp, hf, hi]
      · have hi : ¬ IsInvariant M p := fun h => hf (hclass.2.2 h).2
        simp [hp, hf, hi]
    · by_cases hf : IsFutureSide M p
      · have hi : ¬ IsInvariant M p := fun h => hp (hclass.2.2 h).1
        simp [hp, hf, hi]
      · exact absurd hclass.1 (by tauto)
  simp only [wilsonLatticeAction, pastSideWeight, futureSideWeight, invariantWeight]
  rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-! ### Each class sum depends only on the links of that class

The three sums of `wilsonLatticeAction_split` are the two half-space actions and the boundary
term of `wilsonAction`.  That requires them to be functions of the *half-space data*: the
past-side sum must not see a link whose base lies in the future, and conversely.  This is what the
next three theorems say — together with `pastSide_link_time` / `futureSide_link_time`, which locate
the links of each plaquette. -/

/-- **The past-side sum depends only on the links based in the past half-space or the reflection
slice.**  Two link configurations that agree on every link based at time `≤ M` have the same
past-side action. -/
theorem pastSideWeight_congr (β : ℝ) (N : ℕ) {M : ℕ} {U U' : Link L → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ l : Link L, time l.base ≤ M → U l = U' l) :
    pastSideWeight β N U M = pastSideWeight β N U' M := by
  classical
  simp only [pastSideWeight]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : IsPastSide M p
  · have hlt := p.pastSide_link_time hp
    have hhol : p.holonomy U = p.holonomy U' :=
      show U p.link0 * U p.link1 * (U p.link2)⁻¹ * (U p.link3)⁻¹
        = U' p.link0 * U' p.link1 * (U' p.link2)⁻¹ * (U' p.link3)⁻¹ by
        rw [h p.link0 hlt.1, h p.link1 hlt.2.1, h p.link2 hlt.2.2.1, h p.link3 hlt.2.2.2]
    rw [if_pos hp, if_pos hp, Plaquette.weight, Plaquette.weight, hhol]
  · rw [if_neg hp, if_neg hp]

/-- **The future-side sum depends only on the links based in the future half-space or the
reflection slice.** -/
theorem futureSideWeight_congr (β : ℝ) (N : ℕ) {M : ℕ}
    {U U' : Link L → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ l : Link L, M ≤ time l.base → U l = U' l) :
    futureSideWeight β N U M = futureSideWeight β N U' M := by
  classical
  simp only [futureSideWeight]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hf : IsFutureSide M p
  · have hlt := p.futureSide_link_time hf
    have hhol : p.holonomy U = p.holonomy U' :=
      show U p.link0 * U p.link1 * (U p.link2)⁻¹ * (U p.link3)⁻¹
        = U' p.link0 * U' p.link1 * (U' p.link2)⁻¹ * (U' p.link3)⁻¹ by
        rw [h p.link0 hlt.1, h p.link1 hlt.2.1, h p.link2 hlt.2.2.1, h p.link3 hlt.2.2.2]
    rw [if_pos hf, if_pos hf, Plaquette.weight, Plaquette.weight, hhol]
  · rw [if_neg hf, if_neg hf]

/-- **The invariant (boundary) sum depends only on the links based in the reflection slice.** -/
theorem invariantWeight_congr (β : ℝ) (N : ℕ) {M : ℕ}
    {U U' : Link L → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ l : Link L, time l.base = M → U l = U' l) :
    invariantWeight β N U M = invariantWeight β N U' M := by
  classical
  simp only [invariantWeight]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hi : IsInvariant M p
  · have hmem : ∀ x ∈ p.siteSet, time x = M :=
      fun x hx => hi _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)
    have h0 := h p.link0 (by rw [Plaquette.link0_base]; exact hmem _ (by simp [Plaquette.siteSet]))
    have h1 := h p.link1 (by rw [Plaquette.link1_base]; exact hmem _ (by simp [Plaquette.siteSet]))
    have h2 := h p.link2 (by rw [Plaquette.link2_base]; exact hmem _ (by simp [Plaquette.siteSet]))
    have h3 := h p.link3 (by rw [Plaquette.link3_base]; exact hmem _ (by simp [Plaquette.siteSet]))
    have hhol : p.holonomy U = p.holonomy U' :=
      show U p.link0 * U p.link1 * (U p.link2)⁻¹ * (U p.link3)⁻¹
        = U' p.link0 * U' p.link1 * (U' p.link2)⁻¹ * (U' p.link3)⁻¹ by
        rw [h0, h1, h2, h3]
    rw [if_pos hi, if_pos hi, Plaquette.weight, Plaquette.weight, hhol]
  · rw [if_neg hi, if_neg hi]

/-! ## 7. The time reflection on sites, links and configurations -/

/-! The reflection `t ↦ L − 1 − t` acts on links: a spatial link `x → x + e_μ` is carried to the
spatial link `θx → θx + e_μ`, while a *time* link `x → x + e_2` is carried to `θx → θx − e_2`,
which as an oriented link of the lattice is based at `θ(x + e_2)`.  That reversal is why the
reflected configuration inverts the value attached to a time link: the image link, read from its
base, points the other way, and it must carry the image element.

With that convention the reflected square is a verbatim copy of the original, so its holonomy has
the same trace, and `Re tr` is transported across the reflection — the `Re tr h_θp = Re tr h_p`
half of the bridge the Wilson action's reflection positivity needs.

Proved here: the site lemmas `theta_apply_ne`, `theta_apply_two`, `theta_update_ne`,
`theta_update_two`; the step lemmas `stepSite_some_iff`, **`stepSite_theta_of_ne`** (a spatial step
is carried to the spatial step from the reflected site) and **`stepSite_theta_two`** (a time step is
reversed: `x → x + e_2` becomes `θ(x + e_2) → θx`); the link reflection **`Link.reflect`** with its
base/target/direction accessors and **`Link.reflect_involutive`**; and the configuration reflection
**`reflectConfig`**, unitary on unitary configurations (**`reflectConfig_mem_unitaryGroup`**) and an
involution on them (**`reflectConfig_involutive`**).

The reflected plaquette is **`Plaquette.reflectPlaq`**, built from its three cases —
`reflectT` (time first: base `θ c10`, directions swapped), `reflectT2` (time second: base `θ c01`,
directions swapped) and `reflectS` (spatial: base `θ base`, directions unchanged) — because the
minimal corner of the reflected square is the image of the corner stepped in the *time* direction,
so the temporal cases have to swap `dir` and `dir2`.  With the corner lemmas `theta_c10`,
theta_c01`, `reflectS_c10`, `reflectS_c01`, `reflectS_c11` and the step lemma
`stepSite_target_congr`, the reflected square's corners are the `θ`-images of the original's.  The
trace bookkeeping is in place as `trace_rot` (`tr(ABCD) = tr(BCDA)`) and `trace_rot_inv`
(`tr(ABCD) = tr(DABC)`), and the value lemmas `reflectConfig_reflect_of_ne` / `_of_eq` turn each
reflected link's matrix into the original one (or its inverse, for time links).

The four link identities are proved for all three cases (`reflectS_link0`–`link3`,
`reflectT_link0`–`link3`, `reflectT2_link0`–`link3`), and with them the trace identity
(`trace_holonomy_reflectS`, `trace_holonomy_reflectT`, `trace_holonomy_reflectT2`, and the umbrella
`trace_holonomy_reflectPlaq`).  The two temporal cases are deliberately stated for the trace only:
the reflected holonomy there is the cyclic rotation `u₁u₂⁻¹u₃⁻¹u₀` (time-first) or
`u₃⁻¹u₀u₁u₂⁻¹` (time-second) of `u₀u₁u₂⁻¹u₃⁻¹`, one `trace_rot_inv` / `trace_rot` away from it,
and the inverse the time reversal introduces is removed by unwrapping the double inverse
(`inv_inv_of_mem_unitaryGroup`), which is why those statements carry the unitarity hypothesis.

The bookkeeping point that made this delicate is worth recording: `Link.ofStep`, `Plaquette.c10`
and `Plaquette.reflectT` are plain definitions, but `simp` does not reduce a projection of a
definition, so the corner lemmas are proved by comparing two *step* facts — `stepSite` is
determined by its base and direction, so two steps from the same base in the same direction have
the same target (`Option.some.inj` after rewriting one fact into the other).  The step facts for
the time direction come from `stepSite_theta_two`, whose hypothesis is the step *before*
reflection: `stepSite c01 2 = c11` gives `stepSite (θ c11) 2 = θ c01`, and that is exactly the
corner that a naive `θ`-image computation misses. -/

theorem theta_apply_ne {x : Site L} {μ : Fin 3} (h : μ ≠ 2) : theta x μ = x μ := by
  simp only [theta, Function.update_apply, if_neg h]

theorem theta_apply_two (x : Site L) : theta x 2 = Fin.rev (x 2) := by
  simp [theta]

/-- The reflection commutes with a spatial translation of the site. -/
theorem theta_update_ne (x : Site L) {μ : Fin 3} (h : μ ≠ 2) (v : Fin L) :
    theta (Function.update x μ v) = Function.update (theta x) μ v := by
  revert h
  fin_cases μ
  · intro _; funext ν; fin_cases ν <;> simp [theta]
  · intro _; funext ν; fin_cases ν <;> simp [theta]
  · intro h; simp at h

/-- The reflection reverses a time translation: the time coordinate is replaced by its mirror. -/
theorem theta_update_two (x : Site L) (v : Fin L) :
    theta (Function.update x 2 v) = Function.update (theta x) 2 (Fin.rev v) := by
  funext ν
  fin_cases ν <;> simp [theta]

/-- **A step, unfolded**: a step in a direction that has room is the update of that coordinate. -/
theorem stepSite_some_iff {x y : Site L} {μ : Fin 3} :
    stepSite x μ = some y ↔
      ∃ (h : (x μ).val + 1 < L), y = Function.update x μ ⟨(x μ).val + 1, h⟩ := by
  constructor
  · intro hs
    unfold stepSite at hs
    split at hs
    · rename_i h
      exact ⟨h, by simpa using hs.symm⟩
    · simp at hs
  · rintro ⟨h, rfl⟩
    simp only [stepSite, dif_pos h]

/-- **The reflection carries a spatial step to the spatial step from the reflected site.**  A step
in a direction that is not the time direction is untouched by the time reversal (which only acts
on the time coordinate), so it becomes the same step from the reflected site. -/
theorem stepSite_theta_of_ne {x y : Site L} {μ : Fin 3} (hμ : μ ≠ 2)
    (h : stepSite x μ = some y) : stepSite (theta x) μ = some (theta y) := by
  obtain ⟨hb, rfl⟩ := stepSite_some_iff.1 h
  revert hμ
  fin_cases μ
  · intro _
    rw [stepSite, dif_pos (by simpa [theta] using hb)]
    congr 1
    funext ν
    fin_cases ν <;> simp [theta]
  · intro _
    rw [stepSite, dif_pos (by simpa [theta] using hb)]
    congr 1
    funext ν
    fin_cases ν <;> simp [theta]
  · intro hμ
    exact absurd rfl hμ

/-- **The reflection reverses a time step.**  The mirror of `x → x + e_2` runs *down* in time, so on
the lattice it is the link based at the mirrored upper end, `θ(x + e_2) → θx`. -/
theorem stepSite_theta_two {x y : Site L} (h : stepSite x 2 = some y) :
    stepSite (theta y) 2 = some (theta x) := by
  obtain ⟨hb, rfl⟩ := stepSite_some_iff.1 h
  have hval :
      (theta (Function.update x 2 ⟨(x 2).val + 1, hb⟩) 2).val + 1 = (Fin.rev (x 2)).val := by
    rw [theta_update_two]
    simp only [Fin.val_rev]
    simp
    omega
  rw [stepSite, dif_pos (by rw [hval]; exact (x 2).rev.isLt)]
  congr 1
  funext ν
  fin_cases ν
  · simp [theta]
  · simp [theta]
  · simp only [Function.update_apply]
    exact Fin.ext hval

/-! ### The reflection on links -/

/-- The inverse of the inverse of a unitary matrix is the matrix itself. -/
theorem inv_inv_of_mem_unitaryGroup {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : (U⁻¹)⁻¹ = U := by
  have hstar : star U ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_star]
    exact mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.1 hU)
  rw [inv_eq_star_of_mem_unitaryGroup hU, inv_eq_star_of_mem_unitaryGroup hstar, star_star]

/-- Two links with the same base, direction and target are equal. -/
theorem Link.ext' {l l' : Link L} (hb : l.base = l'.base) (hd : l.dir = l'.dir)
    (ht : l.target = l'.target) : l = l' := by
  obtain ⟨b, μ, t, hs⟩ := l
  obtain ⟨b', μ', t', hs'⟩ := l'
  simp only at hb hd ht
  subst hb; subst hd; subst ht
  rfl

/-- **The image of a link under the time reflection.**  A spatial link is carried to the spatial
link from the reflected base; a time link has its direction reversed, so its image is the link
based at the reflected *upper* end. -/
def Link.reflect (l : Link L) : Link L :=
  if h : l.dir = 2 then
    ⟨theta l.target, 2, theta l.base, stepSite_theta_two (h ▸ l.isStep)⟩
  else
    ⟨theta l.base, l.dir, theta l.target, stepSite_theta_of_ne h l.isStep⟩

/-- The reflected link of a spatial link runs from the reflected base to the reflected target. -/
theorem Link.reflect_of_ne (l : Link L) (h : l.dir ≠ 2) :
    Link.reflect l = ⟨theta l.base, l.dir, theta l.target, stepSite_theta_of_ne h l.isStep⟩ := by
  simp only [Link.reflect, dif_neg h]

/-- The reflected link of a time link runs from the reflected upper end down to the reflected
base. -/
theorem Link.reflect_of_eq (l : Link L) (h : l.dir = 2) :
    Link.reflect l = ⟨theta l.target, 2, theta l.base, stepSite_theta_two (h ▸ l.isStep)⟩ := by
  simp only [Link.reflect, dif_pos h]

theorem Link.reflect_base_of_ne (l : Link L) (h : l.dir ≠ 2) :
    (Link.reflect l).base = theta l.base := by
  rw [Link.reflect_of_ne l h]

theorem Link.reflect_target_of_ne (l : Link L) (h : l.dir ≠ 2) :
    (Link.reflect l).target = theta l.target := by
  rw [Link.reflect_of_ne l h]

theorem Link.reflect_dir_of_ne (l : Link L) (h : l.dir ≠ 2) : (Link.reflect l).dir = l.dir := by
  rw [Link.reflect_of_ne l h]

theorem Link.reflect_base_of_eq (l : Link L) (h : l.dir = 2) :
    (Link.reflect l).base = theta l.target := by
  rw [Link.reflect_of_eq l h]

theorem Link.reflect_target_of_eq (l : Link L) (h : l.dir = 2) :
    (Link.reflect l).target = theta l.base := by
  rw [Link.reflect_of_eq l h]

theorem Link.reflect_dir_of_eq (l : Link L) (h : l.dir = 2) : (Link.reflect l).dir = 2 := by
  rw [Link.reflect_of_eq l h]

/-- **The reflection of links is an involution.** -/
theorem Link.reflect_involutive (l : Link L) : Link.reflect (Link.reflect l) = l := by
  by_cases h : l.dir = 2
  · have hd : (Link.reflect l).dir = 2 := Link.reflect_dir_of_eq l h
    refine Link.ext' ?_ ?_ ?_
    · rw [Link.reflect_base_of_eq _ hd, Link.reflect_target_of_eq l h, theta_involutive]
    · rw [Link.reflect_dir_of_eq _ hd, h]
    · rw [Link.reflect_target_of_eq _ hd, Link.reflect_base_of_eq l h, theta_involutive]
  · have hd : (Link.reflect l).dir ≠ 2 := by rw [Link.reflect_dir_of_ne l h]; exact h
    refine Link.ext' ?_ ?_ ?_
    · rw [Link.reflect_base_of_ne _ hd, Link.reflect_base_of_ne l h, theta_involutive]
    · rw [Link.reflect_dir_of_ne _ hd, Link.reflect_dir_of_ne l h]
    · rw [Link.reflect_target_of_ne _ hd, Link.reflect_target_of_ne l h, theta_involutive]

/-- **The reflected link configuration.**  The value at the reflected link is the image of the value
at the original link — the same matrix, except for time links, whose orientation the reflection
reverses and where the inverse is therefore the correct image. -/
noncomputable def reflectConfig (U : Link L → Matrix (Fin N) (Fin N) ℂ) (l : Link L) :
    Matrix (Fin N) (Fin N) ℂ :=
  if l.dir = 2 then (U (Link.reflect l))⁻¹ else U (Link.reflect l)

theorem reflectConfig_of_ne (U : Link L → Matrix (Fin N) (Fin N) ℂ) (l : Link L) (h : l.dir ≠ 2) :
    reflectConfig U l = U (Link.reflect l) := by
  rw [reflectConfig, if_neg h]

theorem reflectConfig_of_eq (U : Link L → Matrix (Fin N) (Fin N) ℂ) (l : Link L) (h : l.dir = 2) :
    reflectConfig U l = (U (Link.reflect l))⁻¹ := by
  rw [reflectConfig, if_pos h]

/-- The reflected configuration of unitary link variables is unitary. -/
theorem reflectConfig_mem_unitaryGroup {U : Link L → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) (l : Link L) :
    reflectConfig U l ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  by_cases h : l.dir = 2
  · rw [reflectConfig_of_eq U l h]
    exact mem_unitaryGroup_inv (hU _)
  · rw [reflectConfig_of_ne U l h]
    exact hU _

/-- **The reflection of configurations is an involution** on unitary link variables: reflecting
twice returns the original configuration. -/
theorem reflectConfig_involutive {U : Link L → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) : reflectConfig (reflectConfig U) = U := by
  funext l
  by_cases h : l.dir = 2
  · have hd : (Link.reflect l).dir = 2 := Link.reflect_dir_of_eq l h
    rw [reflectConfig_of_eq _ l h, reflectConfig_of_eq _ (Link.reflect l) hd,
      Link.reflect_involutive]
    exact inv_inv_of_mem_unitaryGroup (hU l)
  · have hd : (Link.reflect l).dir ≠ 2 := by
      rw [Link.reflect_dir_of_ne l h]; exact h
    rw [reflectConfig_of_ne _ l h, reflectConfig_of_ne _ (Link.reflect l) hd,
      Link.reflect_involutive]

/-- The value of the reflected configuration at a reflected *spatial* link is the original value. -/
theorem reflectConfig_reflect_of_ne (U : Link L → Matrix (Fin N) (Fin N) ℂ) (l : Link L)
    (h : l.dir ≠ 2) : reflectConfig U (Link.reflect l) = U l := by
  have hd : (Link.reflect l).dir ≠ 2 := by rw [Link.reflect_dir_of_ne l h]; exact h
  rw [reflectConfig_of_ne U _ hd, Link.reflect_involutive]

/-- The value of the reflected configuration at a reflected *time* link is the inverse of the
original value: the image link points the other way. -/
theorem reflectConfig_reflect_of_eq (U : Link L → Matrix (Fin N) (Fin N) ℂ) (l : Link L)
    (h : l.dir = 2) : reflectConfig U (Link.reflect l) = (U l)⁻¹ := by
  have hd : (Link.reflect l).dir = 2 := Link.reflect_dir_of_eq l h
  rw [reflectConfig_of_eq U _ hd, Link.reflect_involutive]

/-- Two sites that set the same coordinate to values of the same index are equal: only the proof
of the bound differs. -/
theorem update_val_congr {x : Site L} {μ : Fin 3} {a b : ℕ} (hab : a = b) (ha : a < L)
    (hb : b < L) :
    Function.update x μ (⟨a, ha⟩ : Fin L) = Function.update x μ ⟨b, hb⟩ := by
  subst hab
  rfl

@[simp] theorem Link.ofStep_base {x : Site L} {μ : Fin 3} (h : (x μ).val + 1 < L) :
    (Link.ofStep x μ h).base = x := rfl

@[simp] theorem Link.ofStep_dir {x : Site L} {μ : Fin 3} (h : (x μ).val + 1 < L) :
    (Link.ofStep x μ h).dir = μ := rfl

@[simp] theorem Link.ofStep_target {x : Site L} {μ : Fin 3} (h : (x μ).val + 1 < L) :
    (Link.ofStep x μ h).target = Function.update x μ ⟨(x μ).val + 1, h⟩ := rfl

/-- **The reflection of a spatial step.**  The step from `x` in a spatial direction is carried to
the step from the reflected site. -/
theorem Link.reflect_ofStep_of_ne {x : Site L} {μ : Fin 3} (hμ : μ ≠ 2)
    (h : (x μ).val + 1 < L) :
    Link.reflect (Link.ofStep x μ h) =
      Link.ofStep (theta x) μ (by rw [theta_apply_ne hμ]; exact h) := by
  have hd : (Link.ofStep x μ h).dir ≠ 2 := by simpa using hμ
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_ne _ hd, Link.ofStep_base]
    rfl
  · rw [Link.reflect_dir_of_ne _ hd, Link.ofStep_dir]
    rfl
  · simp only [Link.reflect_target_of_ne _ hd, Link.ofStep_target]
    rw [theta_update_ne x hμ]
    exact update_val_congr (by rw [theta_apply_ne hμ]) _ _

/-- **The trace of a fourfold product is invariant under rotation.** -/
theorem trace_rot {A B C D : Matrix (Fin N) (Fin N) ℂ} :
    (A * B * C * D).trace = (B * C * D * A).trace := by
  rw [← Matrix.trace_mul_comm A (B * C * D)]
  simp only [mul_assoc]

/-- The other rotation of a fourfold product. -/
theorem trace_rot_inv {A B C D : Matrix (Fin N) (Fin N) ℂ} :
    (A * B * C * D).trace = (D * A * B * C).trace := by
  rw [trace_rot, trace_rot, trace_rot]

namespace Plaquette

theorem time_c10_of_eq (p : Plaquette L) (h : p.dir = 2) : time p.c10 = time p.base + 1 := by
  rw [Plaquette.time_c10, if_pos h]

theorem time_c01_of_eq (p : Plaquette L) (h : p.dir2 = 2) : time p.c01 = time p.base + 1 := by
  rw [Plaquette.time_c01, if_pos h]

/-- **The reflected plaquette, time-first case.**  When `dir` is the time direction, the corner of
the reflected square with minimal coordinates is the image of the corner stepped in *time*, so the
base is `θ c10` and the two directions swap places. -/
def reflectT (p : Plaquette L) (h : p.dir = 2) : Plaquette L where
  base := theta p.c10
  dir := p.dir2
  dir2 := p.dir
  ne := Ne.symm p.ne
  ok1 := by
    have hne : p.dir2 ≠ 2 := fun hc => p.ne (h.trans hc.symm)
    rw [theta_apply_ne hne, Plaquette.c10_apply_dir2]
    exact p.ok2
  ok2 := by
    rw [h, theta_apply_two, Fin.val_rev]
    have ht : (p.c10 2).val = (p.base 2).val + 1 := p.time_c10_of_eq h
    have hb : (p.base 2).val < L := (p.base 2).isLt
    omega

/-- **The reflected plaquette, time-second case.**  Here the corner stepped in time is `c01`, so the
reflected base is `θ c01` and again the directions swap. -/
def reflectT2 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) : Plaquette L where
  base := theta p.c01
  dir := p.dir2
  dir2 := p.dir
  ne := Ne.symm p.ne
  ok1 := by
    rw [h2, theta_apply_two, Fin.val_rev]
    have ht : (p.c01 2).val = (p.base 2).val + 1 := p.time_c01_of_eq h2
    have hb : (p.base 2).val < L := (p.base 2).isLt
    omega
  ok2 := by
    rw [theta_apply_ne h, Plaquette.c01_apply_dir]
    exact p.ok1

/-- **The reflected plaquette, spatial case.**  Both directions are spatial, so the reflection
preserves the labelling: the base is the reflected base and the directions are unchanged. -/
def reflectS (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) : Plaquette L where
  base := theta p.base
  dir := p.dir
  dir2 := p.dir2
  ne := p.ne
  ok1 := by
    rw [theta_apply_ne h]
    exact p.ok1
  ok2 := by
    rw [theta_apply_ne h2]
    exact p.ok2

/-- The reflection of the first corner step, written as an update of the reflected base. -/
theorem theta_c10 (p : Plaquette L) (h : p.dir ≠ 2) :
    theta p.c10 = Function.update (theta p.base) p.dir
      ⟨(theta p.base p.dir).val + 1, (by rw [theta_apply_ne h]; exact p.ok1)⟩ := by
  rw [Plaquette.c10, theta_update_ne p.base h]
  exact (update_val_congr (by rw [theta_apply_ne h]) _ _).symm

/-- A step is determined by its base and direction, so two steps from equal sites in the same
direction have equal targets. -/
theorem stepSite_target_congr {x x' : Site L} {μ : Fin 3} {y y' : Site L} (hx : x = x')
    (h : stepSite x μ = some y) (h' : stepSite x' μ = some y') : y = y' := by
  subst hx
  rw [h] at h'
  exact Option.some.inj h'

theorem reflectS_c10 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).c10 = theta p.c10 := by
  rw [p.theta_c10 h, Plaquette.c10]
  exact update_val_congr (by
    rw [show (p.reflectS h h2).base = theta p.base from rfl,
      show (p.reflectS h h2).dir = p.dir from rfl, theta_apply_ne h]) _ _

theorem theta_c01 (p : Plaquette L) (h2 : p.dir2 ≠ 2) :
    theta p.c01 = Function.update (theta p.base) p.dir2
      ⟨(theta p.base p.dir2).val + 1, (by rw [theta_apply_ne h2]; exact p.ok2)⟩ := by
  rw [Plaquette.c01, theta_update_ne p.base h2]
  exact (update_val_congr (by rw [theta_apply_ne h2]) _ _).symm

theorem reflectS_c01 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).c01 = theta p.c01 := by
  rw [p.theta_c01 h2, Plaquette.c01]
  exact update_val_congr (by
    rw [show (p.reflectS h h2).base = theta p.base from rfl,
      show (p.reflectS h h2).dir2 = p.dir2 from rfl, theta_apply_ne h2]) _ _

theorem reflectS_c11 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).c11 = theta p.c11 := by
  refine stepSite_target_congr (p.reflectS_c01 h h2) (Plaquette.stepSite_c01 (p.reflectS h h2)) ?_
  have hstep : stepSite (theta p.c01) p.dir = some (theta p.c11) := by
    simpa using stepSite_theta_of_ne h p.stepSite_c01
  simpa using hstep

/-! ### The four links of the reflected plaquette, spatial case -/

theorem link0_dir (p : Plaquette L) : p.link0.dir = p.dir := rfl
theorem link1_dir (p : Plaquette L) : p.link1.dir = p.dir2 := rfl
theorem link2_dir (p : Plaquette L) : p.link2.dir = p.dir := rfl
theorem link3_dir (p : Plaquette L) : p.link3.dir = p.dir2 := rfl

@[simp] theorem reflectS_base (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).base = theta p.base := by
  rw [Plaquette.reflectS]

@[simp] theorem reflectS_dir (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).dir = p.dir := by
  rw [Plaquette.reflectS]

@[simp] theorem reflectS_dir2' (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).dir2 = p.dir2 := by
  rw [Plaquette.reflectS]

/-! ### The four links of the reflected plaquette, spatial case

The links are compared through their base, direction and target: each of those is a corner of the
square, so the corner lemmas above settle it without ever unfolding `Link.ofStep`. -/

theorem reflectS_link0 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).link0 = Link.reflect p.link0 := by
  have hd : p.link0.dir ≠ 2 := by rw [Plaquette.link0_dir]; exact h
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_ne _ hd, Plaquette.link0_base, Plaquette.link0_base]
    exact p.reflectS_base h h2
  · rw [Link.reflect_dir_of_ne _ hd, Plaquette.link0_dir, Plaquette.link0_dir]
    exact p.reflectS_dir h h2
  · rw [Link.reflect_target_of_ne _ hd, Plaquette.link0_target, Plaquette.link0_target]
    exact p.reflectS_c10 h h2

theorem reflectS_link3 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).link3 = Link.reflect p.link3 := by
  have hd : p.link3.dir ≠ 2 := by rw [Plaquette.link3_dir]; exact h2
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_ne _ hd, Plaquette.link3_base, Plaquette.link3_base]
    exact p.reflectS_base h h2
  · rw [Link.reflect_dir_of_ne _ hd, Plaquette.link3_dir, Plaquette.link3_dir]
    exact p.reflectS_dir2' h h2
  · rw [Link.reflect_target_of_ne _ hd, Plaquette.link3_target, Plaquette.link3_target]
    exact p.reflectS_c01 h h2

theorem reflectS_link1 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).link1 = Link.reflect p.link1 := by
  have hd : p.link1.dir ≠ 2 := by rw [Plaquette.link1_dir]; exact h2
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_ne _ hd, Plaquette.link1_base, Plaquette.link1_base]
    exact p.reflectS_c10 h h2
  · rw [Link.reflect_dir_of_ne _ hd, Plaquette.link1_dir, Plaquette.link1_dir]
    exact p.reflectS_dir2' h h2
  · rw [Link.reflect_target_of_ne _ hd, Plaquette.link1_target, Plaquette.link1_target]
    exact p.reflectS_c11 h h2

theorem reflectS_link2 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).link2 = Link.reflect p.link2 := by
  have hd : p.link2.dir ≠ 2 := by rw [Plaquette.link2_dir]; exact h
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_ne _ hd, Plaquette.link2_base, Plaquette.link2_base]
    exact p.reflectS_c01 h h2
  · rw [Link.reflect_dir_of_ne _ hd, Plaquette.link2_dir, Plaquette.link2_dir]
    exact p.reflectS_dir h h2
  · rw [Link.reflect_target_of_ne _ hd, Plaquette.link2_target, Plaquette.link2_target]
    exact p.reflectS_c11 h h2

/-- **The reflected plaquette's holonomy in the reflected configuration, spatial case**: the
reflected square carries the same four matrices in the same order, so the holonomies are literally
equal — no trace is needed. -/
theorem holonomy_reflectS (U : Link L → Matrix (Fin N) (Fin N) ℂ) (p : Plaquette L)
    (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    (p.reflectS h h2).holonomy (reflectConfig U) = p.holonomy U := by
  rw [Plaquette.holonomy, Plaquette.holonomy, p.reflectS_link0 h h2, p.reflectS_link1 h h2,
    p.reflectS_link2 h h2, p.reflectS_link3 h h2,
    reflectConfig_reflect_of_ne U p.link0 h, reflectConfig_reflect_of_ne U p.link1 h2,
    reflectConfig_reflect_of_ne U p.link2 h, reflectConfig_reflect_of_ne U p.link3 h2]

/-- The spatial case of the reflection identity for the trace. -/
theorem trace_holonomy_reflectS (U : Link L → Matrix (Fin N) (Fin N) ℂ) (p : Plaquette L)
    (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    ((p.reflectS h h2).holonomy (reflectConfig U)).trace = (p.holonomy U).trace := by
  rw [p.holonomy_reflectS U h h2]

/-- **The refected plaquette**: the square whose four corners are the reflections of the four
corners of `p`.  For a temporal plaquette this is *not* the same `dir`/`dir2` labelling — the
minimal reflected corner is the image of the corner stepped in the time direction — which is why
the two temporal cases swap the directions. -/
def reflectPlaq (p : Plaquette L) : Plaquette L :=
  if h : p.dir = 2 then p.reflectT h
  else if h2 : p.dir2 = 2 then p.reflectT2 h h2
  else p.reflectS h h2

/-! ### The four links of the reflected plaquette, temporal cases

The corner lemmas here are the `θ`-images of the corners, and each link of the reflected square is
named by the link of the original square it comes from.  The time reversal swaps the two links
that end at the top corner, so the correspondence is cyclic: in the time-first case
`link0' = R link1`, `link1' = R link2`, `link2' = R link3`, `link3' = R link0`; in the time-second
case `link0'' = R link3`, `link1'' = R link0`, `link2'' = R link1`, `link3'' = R link2`. -/

/-- The step from the base in the first direction lands on `c10`. -/
theorem stepSite_c10 (p : Plaquette L) : stepSite p.base p.dir = some p.c10 := by
  rw [stepSite, dif_pos p.ok1]
  rfl

/-- The step from the base in the second direction lands on `c01`. -/
theorem stepSite_base_dir2 (p : Plaquette L) : stepSite p.base p.dir2 = some p.c01 := by
  rw [stepSite, dif_pos p.ok2]
  rfl

/-- The step from `c10` in the second direction lands on `c11`. -/
theorem stepSite_c11 (p : Plaquette L) : stepSite p.c10 p.dir2 = some p.c11 := by
  rw [stepSite, dif_pos p.ok11]
  rfl

/-- When the first direction is time, the step from the base in that direction is the one to
`c10`. -/
theorem stepSite_base_two (p : Plaquette L) (h : p.dir = 2) :
    stepSite p.base 2 = some p.c10 := by
  have hstep : stepSite p.base p.dir = some p.c10 := p.stepSite_c10
  rwa [h] at hstep

/-- When the second direction is time, the step from the base in that direction is the one to
`c01`. -/
theorem stepSite_base_two' (p : Plaquette L) (h2 : p.dir2 = 2) :
    stepSite p.base 2 = some p.c01 := by
  have hstep : stepSite p.base p.dir2 = some p.c01 := p.stepSite_base_dir2
  rwa [h2] at hstep

/-- When the second direction is time, the step from `c10` in that direction is the one to `c11`. -/
theorem stepSite_c10_two (p : Plaquette L) (h2 : p.dir2 = 2) :
    stepSite p.c10 2 = some p.c11 := by
  have hstep : stepSite p.c10 p.dir2 = some p.c11 := p.stepSite_c11
  rwa [h2] at hstep

/-- When the first direction is time, the step from `c01` in that direction is the one to `c11`. -/
theorem stepSite_c01_two (p : Plaquette L) (h : p.dir = 2) :
    stepSite p.c01 2 = some p.c11 := by
  have hstep : stepSite p.c01 p.dir = some p.c11 := p.stepSite_c01
  rwa [h] at hstep

/-- **The first corner of the reflected square, time-first case**: it is the image of `c11`. -/
theorem reflectT_c10 (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).c10 = theta p.c11 := by
  have hne : p.dir2 ≠ 2 := fun hc => p.ne (h.trans hc.symm)
  have h1 : stepSite (theta p.c10) p.dir2 = some ((p.reflectT h).c10) := by
    simpa using Plaquette.stepSite_c10 (p.reflectT h)
  have h2 : stepSite (theta p.c10) p.dir2 = some (theta p.c11) :=
    stepSite_theta_of_ne hne (Plaquette.stepSite_c11 p)
  rw [h1] at h2
  exact Option.some.inj h2

/-- **The second corner of the reflected square, time-first case**: it is the image of `base`. -/
theorem reflectT_c01 (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).c01 = theta p.base := by
  have h1 : stepSite (theta p.c10) 2 = some ((p.reflectT h).c01) := by
    have h0 := Plaquette.stepSite_base_dir2 (p.reflectT h)
    rw [show (p.reflectT h).base = theta p.c10 from rfl,
      show (p.reflectT h).dir2 = p.dir from rfl, h] at h0
    exact h0
  have h2 : stepSite (theta p.c10) 2 = some (theta p.base) :=
    stepSite_theta_two (p.stepSite_base_two h)
  rw [h1] at h2
  exact Option.some.inj h2

/-- **The fourth corner of the reflected square, time-first case**: it is the image of `c01`. -/
theorem reflectT_c11 (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).c11 = theta p.c01 := by
  have h1 : stepSite (theta p.c11) 2 = some ((p.reflectT h).c11) := by
    have h0 := Plaquette.stepSite_c11 (p.reflectT h)
    rw [show (p.reflectT h).c10 = theta p.c11 from p.reflectT_c10 h,
      show (p.reflectT h).dir2 = p.dir from rfl, h] at h0
    exact h0
  have h2 : stepSite (theta p.c11) 2 = some (theta p.c01) :=
    stepSite_theta_two (p.stepSite_c01_two h)
  rw [h1] at h2
  exact Option.some.inj h2

/-- **The first corner of the reflected square, time-second case**: it is the image of `base`. -/
theorem reflectT2_c10 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).c10 = theta p.base := by
  have h1 : stepSite (theta p.c01) 2 = some ((p.reflectT2 h h2).c10) := by
    have h0 := Plaquette.stepSite_c10 (p.reflectT2 h h2)
    rw [show (p.reflectT2 h h2).base = theta p.c01 from rfl,
      show (p.reflectT2 h h2).dir = p.dir2 from rfl, h2] at h0
    exact h0
  have h2' : stepSite (theta p.c01) 2 = some (theta p.base) :=
    stepSite_theta_two (p.stepSite_base_two' h2)
  rw [h1] at h2'
  exact Option.some.inj h2'

/-- **The second corner of the reflected square, time-second case**: it is the image of `c11`. -/
theorem reflectT2_c01 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).c01 = theta p.c11 := by
  have h1 : stepSite (theta p.c01) p.dir = some ((p.reflectT2 h h2).c01) := by
    simpa using Plaquette.stepSite_base_dir2 (p.reflectT2 h h2)
  have h2' : stepSite (theta p.c01) p.dir = some (theta p.c11) :=
    stepSite_theta_of_ne h (Plaquette.stepSite_c01 p)
  rw [h1] at h2'
  exact Option.some.inj h2'

/-- **The fourth corner of the reflected square, time-second case**: it is the image of `c10`. -/
theorem reflectT2_c11 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).c11 = theta p.c10 := by
  have h1 : stepSite (theta p.base) p.dir = some ((p.reflectT2 h h2).c11) := by
    simpa [p.reflectT2_c10 h h2] using Plaquette.stepSite_c11 (p.reflectT2 h h2)
  have h2' : stepSite (theta p.base) p.dir = some (theta p.c10) :=
    stepSite_theta_of_ne h (Plaquette.stepSite_c10 p)
  rw [h1] at h2'
  exact Option.some.inj h2'

/-- Time-first case, first link: it is the image of the second link of the original square. -/
theorem reflectT_link0 (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).link0 = Link.reflect p.link1 := by
  have hne : p.dir2 ≠ 2 := fun hc => p.ne (h.trans hc.symm)
  have hd : p.link1.dir ≠ 2 := by rw [Plaquette.link1_dir]; exact hne
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_ne _ hd, Plaquette.link1_base, Plaquette.link0_base]
    exact (show (p.reflectT h).base = theta p.c10 from rfl)
  · rw [Link.reflect_dir_of_ne _ hd, Plaquette.link1_dir, Plaquette.link0_dir]
    exact (show (p.reflectT h).dir = p.dir2 from rfl)
  · rw [Link.reflect_target_of_ne _ hd, Plaquette.link1_target, Plaquette.link0_target]
    exact p.reflectT_c10 h

/-- Time-first case, second link: it is the image of the third link. -/
theorem reflectT_link1 (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).link1 = Link.reflect p.link2 := by
  have hd : p.link2.dir = 2 := by rw [Plaquette.link2_dir]; exact h
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_eq _ hd, Plaquette.link2_target, Plaquette.link1_base]
    exact p.reflectT_c10 h
  · rw [Link.reflect_dir_of_eq _ hd, Plaquette.link1_dir]
    exact (show p.dir = 2 from h)
  · rw [Link.reflect_target_of_eq _ hd, Plaquette.link2_base, Plaquette.link1_target]
    exact p.reflectT_c11 h

/-- Time-first case, third link: it is the image of the fourth link. -/
theorem reflectT_link2 (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).link2 = Link.reflect p.link3 := by
  have hne : p.dir2 ≠ 2 := fun hc => p.ne (h.trans hc.symm)
  have hd : p.link3.dir ≠ 2 := by rw [Plaquette.link3_dir]; exact hne
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_ne _ hd, Plaquette.link3_base, Plaquette.link2_base]
    exact p.reflectT_c01 h
  · rw [Link.reflect_dir_of_ne _ hd, Plaquette.link3_dir, Plaquette.link2_dir]
    exact (show (p.reflectT h).dir = p.dir2 from rfl)
  · rw [Link.reflect_target_of_ne _ hd, Plaquette.link3_target, Plaquette.link2_target]
    exact p.reflectT_c11 h

/-- Time-first case, fourth link: it is the image of the first link. -/
theorem reflectT_link3 (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).link3 = Link.reflect p.link0 := by
  have hd : p.link0.dir = 2 := by rw [Plaquette.link0_dir]; exact h
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_eq _ hd, Plaquette.link0_target, Plaquette.link3_base]
    exact (show (p.reflectT h).base = theta p.c10 from rfl)
  · rw [Link.reflect_dir_of_eq _ hd, Plaquette.link3_dir]
    exact (show p.dir = 2 from h)
  · rw [Link.reflect_target_of_eq _ hd, Plaquette.link0_base, Plaquette.link3_target]
    exact p.reflectT_c01 h

/-- Time-second case, first link: it is the image of the fourth link. -/
theorem reflectT2_link0 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).link0 = Link.reflect p.link3 := by
  have hd : p.link3.dir = 2 := by rw [Plaquette.link3_dir]; exact h2
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_eq _ hd, Plaquette.link3_target, Plaquette.link0_base]
    exact (show (p.reflectT2 h h2).base = theta p.c01 from rfl)
  · rw [Link.reflect_dir_of_eq _ hd, Plaquette.link0_dir]
    exact (show p.dir2 = 2 from h2)
  · rw [Link.reflect_target_of_eq _ hd, Plaquette.link3_base, Plaquette.link0_target]
    exact p.reflectT2_c10 h h2

/-- Time-second case, second link: it is the image of the first link. -/
theorem reflectT2_link1 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).link1 = Link.reflect p.link0 := by
  have hd : p.link0.dir ≠ 2 := by rw [Plaquette.link0_dir]; exact h
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_ne _ hd, Plaquette.link0_base, Plaquette.link1_base]
    exact p.reflectT2_c10 h h2
  · rw [Link.reflect_dir_of_ne _ hd, Plaquette.link0_dir, Plaquette.link1_dir]
    exact (show (p.reflectT2 h h2).dir2 = p.dir from rfl)
  · rw [Link.reflect_target_of_ne _ hd, Plaquette.link0_target, Plaquette.link1_target]
    exact p.reflectT2_c11 h h2

/-- Time-second case, third link: it is the image of the second link. -/
theorem reflectT2_link2 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).link2 = Link.reflect p.link1 := by
  have hd : p.link1.dir = 2 := by rw [Plaquette.link1_dir]; exact h2
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_eq _ hd, Plaquette.link1_target, Plaquette.link2_base]
    exact p.reflectT2_c01 h h2
  · rw [Link.reflect_dir_of_eq _ hd, Plaquette.link2_dir]
    exact (show p.dir2 = 2 from h2)
  · rw [Link.reflect_target_of_eq _ hd, Plaquette.link1_base, Plaquette.link2_target]
    exact p.reflectT2_c11 h h2

/-- Time-second case, fourth link: it is the image of the third link. -/
theorem reflectT2_link3 (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).link3 = Link.reflect p.link2 := by
  have hd : p.link2.dir ≠ 2 := by rw [Plaquette.link2_dir]; exact h
  refine Link.ext' ?_ ?_ ?_
  · rw [Link.reflect_base_of_ne _ hd, Plaquette.link2_base, Plaquette.link3_base]
    exact (show (p.reflectT2 h h2).base = theta p.c01 from rfl)
  · rw [Link.reflect_dir_of_ne _ hd, Plaquette.link2_dir, Plaquette.link3_dir]
    exact (show (p.reflectT2 h h2).dir2 = p.dir from rfl)
  · rw [Link.reflect_target_of_ne _ hd, Plaquette.link2_target, Plaquette.link3_target]
    exact p.reflectT2_c01 h h2

/-- **The reflected holonomy in the reflected configuration, time-first case**: the reflected
square carries the four matrices `u₁, u₂⁻¹, u₃⁻¹, u₀`, one cyclic rotation of the original product
away from `u₀u₁u₂⁻¹u₃⁻¹`. -/
theorem holonomy_reflectT (U : Link L → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) (p : Plaquette L) (h : p.dir = 2) :
    (p.reflectT h).holonomy (reflectConfig U)
      = U p.link1 * (U p.link2)⁻¹ * (U p.link3)⁻¹ * U p.link0 := by
  have hne : p.dir2 ≠ 2 := fun hc => p.ne (h.trans hc.symm)
  rw [Plaquette.holonomy, p.reflectT_link0 h, p.reflectT_link1 h, p.reflectT_link2 h,
    p.reflectT_link3 h, reflectConfig_reflect_of_ne U p.link1 hne,
    reflectConfig_reflect_of_eq U p.link2 h, reflectConfig_reflect_of_ne U p.link3 hne,
    reflectConfig_reflect_of_eq U p.link0 h, inv_inv_of_mem_unitaryGroup (hU p.link0)]

/-- The time-first case of the reflection identity for the trace. -/
theorem trace_holonomy_reflectT (U : Link L → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) (p : Plaquette L) (h : p.dir = 2) :
    ((p.reflectT h).holonomy (reflectConfig U)).trace = (p.holonomy U).trace := by
  rw [p.holonomy_reflectT U hU h, Plaquette.holonomy,
    trace_rot_inv (A := U p.link1) (B := (U p.link2)⁻¹) (C := (U p.link3)⁻¹) (D := U p.link0)]

/-- **The reflected holonomy in the reflected configuration, time-second case**: the reflected
square carries `u₃⁻¹, u₀, u₁, u₂⁻¹`, again one cyclic rotation of the original product away. -/
theorem holonomy_reflectT2 (U : Link L → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) (p : Plaquette L)
    (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    (p.reflectT2 h h2).holonomy (reflectConfig U)
      = (U p.link3)⁻¹ * U p.link0 * U p.link1 * (U p.link2)⁻¹ := by
  rw [Plaquette.holonomy, p.reflectT2_link0 h h2, p.reflectT2_link1 h h2, p.reflectT2_link2 h h2,
    p.reflectT2_link3 h h2, reflectConfig_reflect_of_eq U p.link3 h2,
    reflectConfig_reflect_of_ne U p.link0 h, reflectConfig_reflect_of_eq U p.link1 h2,
    reflectConfig_reflect_of_ne U p.link2 h, inv_inv_of_mem_unitaryGroup (hU p.link1)]

/-- The time-second case of the reflection identity for the trace. -/
theorem trace_holonomy_reflectT2 (U : Link L → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) (p : Plaquette L)
    (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    ((p.reflectT2 h h2).holonomy (reflectConfig U)).trace = (p.holonomy U).trace := by
  rw [p.holonomy_reflectT2 U hU h h2, Plaquette.holonomy,
    trace_rot (A := (U p.link3)⁻¹) (B := U p.link0) (C := U p.link1) (D := (U p.link2)⁻¹)]

/-- **The reflection identity for the trace, all cases**: for a plaquette of the box, the holonomy
of its reflected square in the reflected configuration has the same trace as the original
holonomy — `Re tr h_{θp} = Re tr h_p`, which is what the Wilson weight sees. -/
theorem trace_holonomy_reflectPlaq (U : Link L → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) (p : Plaquette L) :
    ((p.reflectPlaq).holonomy (reflectConfig U)).trace = (p.holonomy U).trace := by
  rw [Plaquette.reflectPlaq]
  split
  · exact p.trace_holonomy_reflectT U hU (by assumption)
  · split
    · exact p.trace_holonomy_reflectT2 U hU (by assumption) (by assumption)
    · exact p.trace_holonomy_reflectS U (by assumption) (by assumption)

/-! ### The reflection of plaquettes is an involution

With the trace identity in all three cases, the reflection invariance of the Wilson action is a
reindexing of the sum over plaquettes — which is legitimate exactly because `reflectPlaq` is an
involution, so it is a permutation of the plaquette set. -/

/-- A plaquette is determined by its base and its two directions. -/
theorem eq_of_data {p q : Plaquette L} (hb : p.base = q.base) (h1 : p.dir = q.dir)
    (h2 : p.dir2 = q.dir2) : p = q :=
  data_injective (by simp only [hb, h1, h2])

/-- The reflected plaquette, time-first case, in the form of an equation. -/
theorem reflectPlaq_of_dir_eq (p : Plaquette L) (h : p.dir = 2) :
    p.reflectPlaq = p.reflectT h := by
  rw [reflectPlaq, dif_pos h]

/-- The reflected plaquette, time-second case, in the form of an equation. -/
theorem reflectPlaq_of_dir2_eq (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 = 2) :
    p.reflectPlaq = p.reflectT2 h h2 := by
  rw [reflectPlaq, dif_neg h, dif_pos h2]

/-- The reflected plaquette, spatial case, in the form of an equation. -/
theorem reflectPlaq_of_dir_ne (p : Plaquette L) (h : p.dir ≠ 2) (h2 : p.dir2 ≠ 2) :
    p.reflectPlaq = p.reflectS h h2 := by
  rw [reflectPlaq, dif_neg h, dif_neg h2]

/-- **The reflection of plaquettes is an involution.**  Reflecting twice returns the plaquette: the
four corners come back (`θ` is involutive) and the `dir`/`dir2` swap of the temporal cases is
undone by the second swap. -/
theorem reflectPlaq_involutive (p : Plaquette L) : p.reflectPlaq.reflectPlaq = p := by
  by_cases h : p.dir = 2
  · have hne : p.dir2 ≠ 2 := fun hc => p.ne (h.trans hc.symm)
    have h1 : (p.reflectT h).dir ≠ 2 := fun hc => hne (hc ▸ rfl)
    have h2 : (p.reflectT h).dir2 = 2 := h
    rw [reflectPlaq_of_dir_eq p h, reflectPlaq_of_dir2_eq (p.reflectT h) h1 h2]
    refine eq_of_data ?_ ?_ ?_
    · change theta (p.reflectT h).c01 = p.base
      rw [p.reflectT_c01 h, theta_involutive]
    · rfl
    · rfl
  · by_cases h2 : p.dir2 = 2
    · have hq : (p.reflectT2 h h2).dir = 2 := h2
      rw [reflectPlaq_of_dir2_eq p h h2, reflectPlaq_of_dir_eq (p.reflectT2 h h2) hq]
      refine eq_of_data ?_ ?_ ?_
      · change theta (p.reflectT2 h h2).c10 = p.base
        rw [p.reflectT2_c10 h h2, theta_involutive]
      · rfl
      · rfl
    · have h1 : (p.reflectS h h2).dir ≠ 2 := fun hc => h hc
      have h2' : (p.reflectS h h2).dir2 ≠ 2 := fun hc => h2 hc
      rw [reflectPlaq_of_dir_ne p h h2, reflectPlaq_of_dir_ne (p.reflectS h h2) h1 h2']
      refine eq_of_data ?_ ?_ ?_
      · change theta (p.reflectS h h2).base = p.base
        rw [p.reflectS_base h h2, theta_involutive]
      · rfl
      · rfl

end Plaquette

/-- **The Wilson action of the box is invariant under the reflected configuration.**  The reflection
of plaquettes is an involution (`Plaquette.reflectPlaq_involutive`), so the sum over plaquettes may
be reindexed by it; the trace identity `Re tr h_{θp} = Re tr h_p`
(`Plaquette.trace_holonomy_reflectPlaq`) then makes each reindexed weight equal to the original one.
Together with `wilsonLatticeAction_split` this is the invariance of the action under
`reflectConfig` that the reflection-positivity argument of `WilsonLattice` uses. -/
theorem wilsonLatticeAction_reflectConfig (β : ℝ) (N : ℕ)
    (U : Link L → Matrix (Fin N) (Fin N) ℂ)
    (hU : ∀ l, U l ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    wilsonLatticeAction β N (reflectConfig U) = wilsonLatticeAction β N U := by
  let e : Plaquette L ≃ Plaquette L :=
    { toFun := Plaquette.reflectPlaq
      invFun := Plaquette.reflectPlaq
      left_inv := Plaquette.reflectPlaq_involutive
      right_inv := Plaquette.reflectPlaq_involutive }
  unfold wilsonLatticeAction
  rw [← Equiv.sum_comp e (fun p => Plaquette.weight β N (reflectConfig U) p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [Plaquette.weight, Plaquette.weight, plaqDensity, plaqDensity,
    p.trace_holonomy_reflectPlaq U hU]

end

end BookProof.ReflectionPositivity
