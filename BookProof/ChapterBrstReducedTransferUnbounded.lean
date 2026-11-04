import Mathlib
import BookProof.ChapterBrstUnbounded
import BookProof.Toolbox.ChapterStoneGenerator

/-!
# The BRST-reduced transfer for a *closed densely defined* charge

`BookProof.BrstReducedTransfer` proves that the unitary evolution descends to BRST cohomology,
for a **bounded** nilpotent charge `Ω : H →L[ℂ] H`.  `BookProof.BrstUnbounded` reproves the
*decomposition* side — the Hodge decomposition and the quotient-norm identity — for a charge
`Om : H →ₗ.[ℂ] H` that is only closed and densely defined.  Between them they left one gap,
recorded in `softmodes.md` Phase 1 item 1:

> What remains bounded-only is the **descent**, not the decomposition: `transfer`,
> `transfer_comp`, `transfer_bijective`, `infDist_exactStates_eq_of_comm_explicit` and the Stone
> instance are statements about `Ω ∈ H →L[ℂ] H` commuting with a unitary group, and no
> unbounded analogue (nor an unbounded form of the commutation hypothesis) is claimed.

This module closes that gap.

## The unbounded form of `[H, Ω] = 0`

For a bounded `Ω` the commutation hypothesis `∀ t y, U t (Ω y) = Ω (U t y)` is a single
equation.  For a partially defined `Ω` it splits in two, and neither half can be dropped:

* **`DomPreserve Om U`** — `U` maps the domain of `Ω` into itself.  Without it `Ω (U y)` is not
  even a term, so the equation is meaningless; this is the clause `IsNilpotent` already needs
  on the *charge* itself (`Ω x` need not be defined again without it).
* **`StrongCommute Om U hdom`** — `U (Ω y) = Ω (U y)` for `y` in the domain, with `Ω (U y)`
  read at `hdom y`.

The evolution `U t` stays **bounded** (it is a continuous linear map — a unitary one in the
Stone application); only `Ω` is unbounded.  That is why the argument survives: the closure
step in `exactStates_invariant` still uses continuity of `U`, and the quotient-norm step still
uses that `U` is an isometry.

## What is proved here

* `physicalStates_invariant` / `exactStates_invariant` — a domain-preserving strongly
  commuting `U` maps closed states to closed states and exact states to exact states.
  The second is where nilpotency is *not* needed but continuity is: `closure (range Ω)` is
  carried into itself because the preimage of a closed set under a continuous map is closed.
* `reducedMap` — the induced ℂ-linear map on `Cohomology Om = physicalStates Om ⧸ trivialSub Om`.
* **`transfer`**, with `transfer_zero`, `transfer_comp`, `transfer_apply_transfer` and
  `transfer_bijective` — a one-parameter group of linear automorphisms of BRST cohomology.
* **`infDist_exactStates_eq_of_comm_explicit`** — for an isometric `U` the distance to the
  exact states, i.e. the quotient (BRST) norm of the class, is preserved.
* The Stone instance `stoneTransfer` with `stoneTransfer_zero`, `stoneTransfer_comp`,
  `stoneTransfer_bijective`, `stoneU_mem_physicalStates_of_comm_explicit`,
  `stoneU_sub_mem_exactStates_of_comm_explicit` and
  `infDist_exactStates_stoneU_eq_of_comm_explicit`: the unitary group `e^{-itT}` of an
  unbounded self-adjoint Hamiltonian, strongly commuting with a closed densely defined charge,
  descends to a one-parameter group of norm-preserving automorphisms of the BRST cohomology.

## Honest boundary

* Nilpotency is carried where it is needed (`exactStates_le_physicalStates`, from
  `ChapterBrstUnbounded`) but the *descent* itself does not use it: invariance of the two
  sectors and preservation of the quotient norm are statements about an arbitrary closed
  densely defined `Ω`.
* Nothing here identifies `closure (range Ω)` with the longitudinal (pure-gauge) span
  `span {∂_i φ}`, nor supplies an `H_phys` for the field-theoretic charge — that is
  `softmodes.md` Phase 1 item 3, which needs the concrete realization, not the transfer.
* The commutation hypothesis is exactly `[H, Ω] = 0` in the only form a partial map can state
  it; proving it for the concrete field-theoretic `H` and `Ω` is the input this module awaits.
-/

namespace BookProof.BrstReducedTransferUnbounded

open BookProof.BrstUnbounded BookProof.ChapterStoneResolvent

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Om : H →ₗ.[ℂ] H)

/-! ### The unbounded form of the commutation hypothesis -/

/-- **Domain preservation.**  `U` maps the domain of the charge into itself.  For a partially
defined `Ω` this is a hypothesis in its own right: without it `Ω (U y)` is not a term, so the
commutation equation below cannot even be stated. -/
def DomPreserve (U : H →L[ℂ] H) : Prop :=
  ∀ y : Om.domain, (U y : H) ∈ Om.domain

/-- **Strong commutation on the domain**: `U (Ω y) = Ω (U y)` for `y` in the domain of `Ω`,
with the right-hand side read at `hdom y`.  This is `[H, Ω] = 0` in the only form a partially
defined charge can state. -/
def StrongCommute (U : H →L[ℂ] H) (hdom : DomPreserve Om U) : Prop :=
  ∀ y : Om.domain, U (Om y) = Om ⟨(U y : H), hdom y⟩

/-! ### The two sectors are invariant -/

omit [CompleteSpace H] in
/-- A domain-preserving strongly commuting operator preserves the physical (BRST-closed)
states.  Nilpotency is not needed: `Ω x = 0` is transported to `Ω (U x) = U (Ω x) = U 0 = 0`. -/
theorem physicalStates_invariant (U : H →L[ℂ] H) {hdom : DomPreserve Om U}
    (hcomm : StrongCommute Om U hdom) {x : H} (hx : x ∈ physicalStates Om) :
    U x ∈ physicalStates Om := by
  obtain ⟨hxd, h0⟩ := (mem_physicalStates (Om := Om)).mp hx
  refine (mem_physicalStates (Om := Om)).mpr ⟨hdom ⟨x, hxd⟩, ?_⟩
  have h1 : Om ⟨U x, hdom ⟨x, hxd⟩⟩ = U (Om ⟨x, hxd⟩) := (hcomm ⟨x, hxd⟩).symm
  rw [h1, h0, map_zero]

omit [CompleteSpace H] in
/-- A domain-preserving strongly commuting operator preserves the exact (pure-gauge) states.
Continuity of `U` — not boundedness of `Ω` — carries the range into its closure, exactly as in
the bounded chapter. -/
theorem exactStates_invariant (U : H →L[ℂ] H) {hdom : DomPreserve Om U}
    (hcomm : StrongCommute Om U hdom) {x : H} (hx : x ∈ exactStates Om) :
    U x ∈ exactStates Om := by
  have hcl : IsClosed (U ⁻¹' (exactStates Om : Set H)) :=
    (isClosed_exactStates Om).preimage U.continuous
  have hrange : (LinearMap.range Om.toFun : Set H) ⊆ U ⁻¹' (exactStates Om : Set H) := by
    rintro z ⟨y, hy⟩
    rw [← hy]
    have h1 : U (Om.toFun y) = Om ⟨(U y : H), hdom y⟩ := hcomm y
    change U (Om.toFun y) ∈ exactStates Om
    rw [h1]
    exact mem_exactStates_of_apply Om ⟨(U y : H), hdom y⟩
  have hsub : closure (LinearMap.range Om.toFun : Set H)
      ⊆ U ⁻¹' (exactStates Om : Set H) := closure_minimal hrange hcl
  exact hsub (by simpa [exactStates, Submodule.topologicalClosure_coe] using hx)

/-! ### Cohomology and the reduced map -/

/-- The exact states, seen inside the physical subspace. -/
def trivialSub : Submodule ℂ (physicalStates Om) :=
  (exactStates Om).comap (physicalStates Om).subtype

/-- **BRST cohomology** for a closed densely defined charge: physical (closed) states modulo
exact (pure gauge) ones. -/
abbrev Cohomology := physicalStates Om ⧸ trivialSub Om

/-- The map induced on BRST cohomology by a domain-preserving strongly commuting operator. -/
def reducedMap (U : H →L[ℂ] H) (hdom : DomPreserve Om U) (hcomm : StrongCommute Om U hdom) :
    Cohomology Om →ₗ[ℂ] Cohomology Om :=
  Submodule.mapQ _ _
    ((U : H →ₗ[ℂ] H).restrict fun _ hx => physicalStates_invariant Om U hcomm hx)
    fun _ hx => exactStates_invariant Om U hcomm hx

omit [CompleteSpace H] in
@[simp] theorem reducedMap_mk (U : H →L[ℂ] H) (hdom : DomPreserve Om U)
    (hcomm : StrongCommute Om U hdom) (x : physicalStates Om) :
    reducedMap Om U hdom hcomm (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk ⟨U x, physicalStates_invariant Om U hcomm x.2⟩ := rfl

end General

/-! ### The reduced transfer -/

section Group

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Om : H →ₗ.[ℂ] H)
variable (U : ℝ → (H →L[ℂ] H))
variable (hdom : ∀ (t : ℝ), DomPreserve Om (U t))
variable (hcomm : ∀ (t : ℝ), StrongCommute Om (U t) (hdom t))

/-- **The BRST-reduced transfer.**  A one-parameter family preserving the domain of the charge
and strongly commuting with it descends to BRST cohomology. -/
def transfer (t : ℝ) : Cohomology Om →ₗ[ℂ] Cohomology Om :=
  reducedMap Om (U t) (hdom t) (hcomm t)

omit [CompleteSpace H] in
@[simp] theorem transfer_mk (t : ℝ) (x : physicalStates Om) :
    transfer Om U hdom hcomm t (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk ⟨U t x, physicalStates_invariant Om (U t) (hcomm t) x.2⟩ := rfl

omit [CompleteSpace H] in
include hdom hcomm in
theorem transfer_zero (hzero : ∀ x : H, U 0 x = x) :
    transfer Om U hdom hcomm 0 = LinearMap.id := by
  refine LinearMap.ext fun c => ?_
  induction c using Submodule.Quotient.induction_on with
  | H x =>
    rw [transfer_mk, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (hzero x)

include hdom hcomm in
omit [CompleteSpace H] in
theorem transfer_comp (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (s t : ℝ) :
    (transfer Om U hdom hcomm s).comp (transfer Om U hdom hcomm t)
      = transfer Om U hdom hcomm (s + t) := by
  refine LinearMap.ext fun c => ?_
  induction c using Submodule.Quotient.induction_on with
  | H x =>
    simp only [LinearMap.comp_apply, transfer_mk]
    congr 1
    exact Subtype.ext (hgroup s t x)

omit [CompleteSpace H] in
include hdom hcomm in
theorem transfer_apply_transfer (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x)
    (s t : ℝ) (c : Cohomology Om) :
    transfer Om U hdom hcomm s (transfer Om U hdom hcomm t c)
      = transfer Om U hdom hcomm (s + t) c := by
  have := congrArg (fun L : Cohomology Om →ₗ[ℂ] Cohomology Om => L c)
    (transfer_comp Om U hdom hcomm hgroup s t)
  simpa using this

omit [CompleteSpace H] in
include hdom hcomm in
/-- The reduced transfer is invertible: `transfer (-t)` undoes `transfer t`. -/
theorem transfer_bijective (hzero : ∀ x : H, U 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (t : ℝ) :
    Function.Bijective (transfer Om U hdom hcomm t) := by
  constructor
  · intro a b hab
    have h := congrArg (transfer Om U hdom hcomm (-t)) hab
    rw [transfer_apply_transfer Om U hdom hcomm hgroup,
      transfer_apply_transfer Om U hdom hcomm hgroup, neg_add_cancel,
      transfer_zero Om U hdom hcomm hzero] at h
    simpa using h
  · intro c
    refine ⟨transfer Om U hdom hcomm (-t) c, ?_⟩
    rw [transfer_apply_transfer Om U hdom hcomm hgroup, add_neg_cancel,
      transfer_zero Om U hdom hcomm hzero]
    simp

/-! ### The commutation hypothesis is written in each binder list

As in `BookProof.BrstReducedTransfer`: `include hdom hcomm in` makes the hypotheses arguments
only through the *value*, so a textual export that re-elaborates the statement alone drops them
and asserts norm preservation for an arbitrary isometric family — false, since a translation is
isometric but moves the exact states.  The binders below keep the signatures unchanged while
making the exported statements self-contained.  Do not remove them. -/

omit [CompleteSpace H] in
/-- **The reduced transfer preserves the BRST norm.**  For an isometric family preserving the
domain and strongly commuting with the charge, the distance to the exact states — the quotient
norm of the cohomology class — is unchanged. -/
theorem infDist_exactStates_eq_of_comm_explicit
    (hdom : ∀ (t : ℝ), DomPreserve Om (U t))
    (hcomm : ∀ (t : ℝ), StrongCommute Om (U t) (hdom t))
    (hzero : ∀ x : H, U 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x)
    (hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ = ‖x‖) (t : ℝ) (x : H) :
    Metric.infDist (U t x) (exactStates Om) = Metric.infDist x (exactStates Om) := by
  have hne : (exactStates Om : Set H).Nonempty := ⟨0, (exactStates Om).zero_mem⟩
  have key : ∀ (s : ℝ) (y : H),
      Metric.infDist (U s y) (exactStates Om) ≤ Metric.infDist y (exactStates Om) := by
    intro s y
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hz, hdz⟩ := (Metric.infDist_lt_iff hne).1
      (by linarith [Metric.infDist_nonneg (x := y) (s := (exactStates Om : Set H))] :
        Metric.infDist y (exactStates Om) < Metric.infDist y (exactStates Om) + ε)
    have hd : dist (U s y) (U s z) = dist y z := by
      simp [dist_eq_norm, ← map_sub, hisom]
    calc Metric.infDist (U s y) (exactStates Om)
        ≤ dist (U s y) (U s z) :=
          Metric.infDist_le_dist_of_mem (exactStates_invariant Om (U s) (hcomm s) hz)
      _ = dist y z := hd
      _ ≤ Metric.infDist y (exactStates Om) + ε := le_of_lt hdz
  refine le_antisymm (key t x) ?_
  have hback := key (-t) (U t x)
  rwa [hgroup, neg_add_cancel, hzero] at hback

end Group

/-! ### The Stone instance -/

section Stone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H) (Om : H →ₗ.[ℂ] H)
variable (hdom : ∀ (t : ℝ), DomPreserve Om (T.stoneU t))
variable (hcomm : ∀ (t : ℝ), StrongCommute Om (T.stoneU t) (hdom t))

/-- **The BRST-reduced transfer of the exact unitary group.**  The group `e^{-itT}` of an
unbounded self-adjoint Hamiltonian, strongly commuting with a closed densely defined charge,
descends to BRST cohomology. -/
noncomputable def stoneTransfer (t : ℝ) : Cohomology Om →ₗ[ℂ] Cohomology Om :=
  transfer Om (fun s => T.stoneU s) hdom hcomm t

theorem stoneTransfer_zero : stoneTransfer T Om hdom hcomm 0 = LinearMap.id :=
  transfer_zero Om _ hdom hcomm (by simp)

theorem stoneTransfer_comp (s t : ℝ) :
    (stoneTransfer T Om hdom hcomm s).comp (stoneTransfer T Om hdom hcomm t)
      = stoneTransfer T Om hdom hcomm (s + t) :=
  transfer_comp Om _ hdom hcomm (fun s t x => T.stoneU_apply_stoneU s t x) s t

theorem stoneTransfer_bijective (t : ℝ) :
    Function.Bijective (stoneTransfer T Om hdom hcomm t) :=
  transfer_bijective Om _ hdom hcomm (by simp) (fun s t x => T.stoneU_apply_stoneU s t x) t

/-- **The exact dynamics maps the physical subspace to itself** — the caveat of §10.3. -/
theorem stoneU_mem_physicalStates_of_comm_explicit
    (hdom : ∀ (t : ℝ), DomPreserve Om (T.stoneU t))
    (hcomm : ∀ (t : ℝ), StrongCommute Om (T.stoneU t) (hdom t))
    (t : ℝ) {x : H} (hx : x ∈ physicalStates Om) :
    T.stoneU t x ∈ physicalStates Om :=
  physicalStates_invariant Om (T.stoneU t) (hcomm t) hx

/-- Gauge invariance of the exact dynamics: two states differing by a pure-gauge (exact)
vector still differ by a pure-gauge vector after evolving. -/
theorem stoneU_sub_mem_exactStates_of_comm_explicit
    (hdom : ∀ (t : ℝ), DomPreserve Om (T.stoneU t))
    (hcomm : ∀ (t : ℝ), StrongCommute Om (T.stoneU t) (hdom t))
    (t : ℝ) {x y : H} (h : x - y ∈ exactStates Om) :
    T.stoneU t x - T.stoneU t y ∈ exactStates Om := by
  rw [← map_sub]
  exact exactStates_invariant Om (T.stoneU t) (hcomm t) h

/-- The exact dynamics is norm-preserving on BRST cohomology. -/
theorem infDist_exactStates_stoneU_eq_of_comm_explicit
    (hdom : ∀ (t : ℝ), DomPreserve Om (T.stoneU t))
    (hcomm : ∀ (t : ℝ), StrongCommute Om (T.stoneU t) (hdom t))
    (t : ℝ) (x : H) :
    Metric.infDist (T.stoneU t x) (exactStates Om) = Metric.infDist x (exactStates Om) :=
  infDist_exactStates_eq_of_comm_explicit Om _ hdom hcomm (by simp)
    (fun s t x => T.stoneU_apply_stoneU s t x) (fun s y => T.norm_stoneU_apply s y) t x

end Stone

end BookProof.BrstReducedTransferUnbounded
