/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import BookProof.Sm.ChapterSmBrstQuotient
import BookProof.Sm.ChapterSmBrstGhost

/-!
# The quartet structure of a BRST charge

§46 built the algebra of the BRST quotient and left the Kugo–Ojima positivity
condition `PhysicalPositivity` as a *named input*, because non-negativity of the
charge form on the closed space is not a consequence of nilpotency alone.  This
module supplies the mechanism that does produce it: the **quartet**.

The physical content of Kugo–Ojima is that the unphysical states of a gauge theory
come in quartets `(A_L, B, c, c̄)` which the charge pairs up — `Q` maps one member
onto another and the b-ghost `P` maps it back — while the transverse, genuinely
physical states are annihilated by both.  Algebraically this is a single identity,

  `Q P + P Q = 1 - V`,

with `Q² = 0`, `V` a projector onto the physical subspace and `V` in the kernel of
`Q`.  The four members of a quartet sit in the two-dimensional block where
`Q P + P Q = 1`; the physical states are the ones where it is `0`.

What the identity buys, and what is *proved* here:

* **The physical projector is BRST-closed on both sides** (`quartet_physProj_comp_Q`):
  `V Q = 0` follows from `{Q, P} = 1 - V` and `Q² = 0`, so `V`'s range consists of
  closed vectors and the hypothesis set is not over-specified.
* **Every closed vector splits as an exact vector plus a physical one**
  (`quartet_decompose`): `x = Q (P x) + V x` for `x ∈ ker Q`.
* **The charge form sees only the physical part** (`kform_quartet_reduce`): the
  exact part is null against everything closed (ghost nullity, §46) and orthogonal
  to the physical part, so `kform η x x = kform η (Vx) (Vx)`.
* **Kugo–Ojima positivity follows** (`physicalPositivity_of_quartet`): if the
  metric operator fixes the range of `V` — i.e. the physical subspace is in the
  ghost-parity-even sector, which is the no-ghost theorem's content — then the
  charge form is `‖Vx‖²` on the closed space, hence non-negative, and its radical
  is exactly the gauge orbit.  **`PhysicalPositivity` is a theorem here, not an
  input.**
* **Sector by sector** (`physicalPositivity_of_quartet_sectors`): when positivity of
  the physical subspace is only known one parity sector at a time, the split of
  §46 assembles the two halves, which is the shape a physical smoke test takes.

**The b-ghost of the Standard-Model charge.**  §8 constructs it: on a
finite-dimensional space every endomorphism has a contracting homotopy
(`exists_contractingHomotopy`), obtained by splitting the range off a complement of
the kernel, and `FermiFock (m + 12)` is finite-dimensional.  So `smBghost` is a
b-ghost for `smBrstCharge` and `smQuartet` is its quartet, not a toy block.

**What the construction pins down, and what it does not.**  §5 characterises the
physical subspace of a contracting homotopy exactly: `range V = ker Q ⊓ ker P`
(`range_physProjOf`), the harmonic representatives of the cohomology.  That
characterisation is a property of the *chosen* `P`: a b-ghost is a choice of
complement of the exact states, so the range is not the transverse, ghost-parity-even
subspace unless `P` is the model's own mode pairing (and a ghost parity `U` with
`U P = P U` is supplied).  §8 does not fix such a pairing — the quartet is
choice-based — so that identification is not made, and `smPhysProj_mem_closed` is
the SM-level half of it that does hold.

The standing input was written in §3 as the fixing hypothesis `hEtaPhys`
(`η (V y) = V y`), which is stronger than the no-ghost argument needs and is not
what an indefinite ghost metric gives.  `physicalPositivity_of_quartet_on_range`
replaces it by positivity of the charge form *on* the range of `V`, and
`smPhysicalPositivity_of_physForm` is that statement at `smBrstCharge`: the open
input is a no-ghost estimate on `range smPhysProj`, not an identity on `η`.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmQuartet

open BookProof.SmBrstQuotient
open BookProof.SmPhysicalReduction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## 1. The quartet data -/

/-- **The quartet structure of a nilpotent charge.**  `bGhost` is the b-ghost `P` (the
antighost momentum that pairs each unphysical mode with its partner) and `physProj` is the
projector `V` onto the physical subspace.  The single identity `Q P + P Q = 1 - V` is the
quartet mechanism: on a quartet block the right-hand side is the identity, on the physical
subspace it vanishes. -/
structure BrstQuartet (Q : H →ₗ[ℂ] H) where
  /-- The b-ghost `P`. -/
  bGhost : H →ₗ[ℂ] H
  /-- The projector `V` onto the physical subspace. -/
  physProj : H →ₗ[ℂ] H
  /-- `V` is a projector. -/
  physProj_idem : ∀ x : H, physProj (physProj x) = physProj x
  /-- The physical subspace is BRST-closed: `V`'s range lies in `ker Q`. -/
  Q_physProj : ∀ x : H, Q (physProj x) = 0
  /-- **The quartet identity** `Q P + P Q = 1 - V`. -/
  quartet_anticomm : ∀ x : H, Q (bGhost x) + bGhost (Q x) = x - physProj x

namespace BrstQuartet

variable {Q : H →ₗ[ℂ] H}

/-- Nilpotency, pointwise: `Q (Q x) = 0`. -/
theorem Q_apply_apply (hQ : IsBrst Q) (x : H) : Q (Q x) = 0 := by
  have h := congrFun (congrArg DFunLike.coe hQ) x
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

/-- **The physical projector is annihilated by the charge on the other side too**: `V Q = 0`.
This is *derived*, not assumed.  Applying `Q` to the quartet identity at `x` gives
`Q (P (Q x)) = Q x` (the `Q²` term vanishes and `Q V x = 0`), while the identity at `Q x`
gives `Q (P (Q x)) = Q x - V (Q x)`; comparing yields `V (Q x) = 0`. -/
theorem quartet_physProj_comp_Q (hQ : IsBrst Q) (q : BrstQuartet Q) (x : H) :
    q.physProj (Q x) = 0 := by
  have h1 : Q (q.bGhost (Q x)) = Q x := by
    have h := congrArg Q (q.quartet_anticomm x)
    simp only [map_add, map_sub, Q_apply_apply hQ (q.bGhost x), q.Q_physProj x, sub_zero,
      zero_add] at h
    exact h
  have h2 : Q (q.bGhost (Q x)) = Q x - q.physProj (Q x) := by
    have h := q.quartet_anticomm (Q x)
    simpa only [Q_apply_apply hQ x, map_zero, add_zero] using h
  exact sub_eq_self.mp (h2.symm.trans h1)

/-- A vector in the range of the physical projector is closed. -/
theorem mem_closed_physProj (q : BrstQuartet Q) (y : H) : q.physProj y ∈ closed Q :=
  q.Q_physProj y

/-- **The range of the physical projector, as a set of fixed points.**  For an idempotent `V`,
being in the range and being fixed are the same condition, which is the form in which a
concrete `V` (an orthogonal projection, say) is usually recognised. -/
theorem mem_range_physProj_iff (q : BrstQuartet Q) (x : H) :
    x ∈ LinearMap.range q.physProj ↔ q.physProj x = x := by
  refine ⟨?_, fun h => ⟨x, h⟩⟩
  rintro ⟨y, rfl⟩
  exact q.physProj_idem y

/-- The range of the physical projector lies in the closed space. -/
theorem range_physProj_le_closed (q : BrstQuartet Q) :
    LinearMap.range q.physProj ≤ closed Q := by
  rintro _ ⟨y, rfl⟩
  exact q.mem_closed_physProj y

/-- **Every closed vector is exact plus physical**: `x = Q (P x) + V x`.  This is the
quartet decomposition of the state space. -/
theorem quartet_decompose (q : BrstQuartet Q) {x : H} (hx : x ∈ closed Q) :
    x = Q (q.bGhost x) + q.physProj x := by
  have hQx : Q x = 0 := hx
  have h := q.quartet_anticomm x
  rw [hQx, map_zero, add_zero] at h
  rw [h]
  abel

/-! ## 2. The charge form sees only the physical part -/

/-- **The exact part is null for the charge form**: an exact vector has vanishing charge-form
square, since the charge is self-adjoint for that form. -/
theorem kform_exact_self {Q η : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y)) (z : H) :
    kform η (Q z) (Q z) = 0 := by
  rw [hKrein z (Q z), Q_apply_apply hQ, kform_zero_right]

/-- **The quartet reduction of the charge form**: on a closed vector, the charge form is the one
of its physical part.  Both the exact–exact term and the two cross terms vanish: the first by
nilpotency, the cross terms by ghost nullity (§46) and the symmetry of the form. -/
theorem kform_quartet_reduce (hQ : IsBrst Q) (q : BrstQuartet Q) {η : H →ₗ[ℂ] H}
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    {x : H} (hx : x ∈ closed Q) :
    kform η x x = kform η (q.physProj x) (q.physProj x) := by
  set a : H := Q (q.bGhost x) with ha
  set v : H := q.physProj x with hv
  have hvC : v ∈ closed Q := q.mem_closed_physProj x
  have hdecomp : x = a + v := q.quartet_decompose hx
  have haa : kform η a a = 0 := kform_exact_self hQ hKrein (q.bGhost x)
  have hav : kform η a v = 0 := by
    rw [ha, hv, hKrein (q.bGhost x) (q.physProj x), q.Q_physProj x, kform_zero_right]
  have hva : kform η v a = 0 := by
    rw [hSymm v a, hav]
    simp
  rw [hdecomp, kform_add_left, kform_add_right, kform_add_right, haa, hav, hva]
  simp

/-! ## 3. The no-ghost theorem -/

/-- **Kugo–Ojima positivity from a quartet decomposition.**  If the metric operator `η` fixes
the range of the physical projector — the physical subspace is in the ghost-parity-even sector,
`η (V y) = V y` — then, for a closed vector,

  `⟨x, x⟩_η = ‖V x‖²`,

so the charge form is non-negative on the closed space and its radical is exactly the gauge
orbit: `‖V x‖ = 0` forces `V x = 0`, whence `x = Q (P x)` is exact.  `PhysicalPositivity` is
therefore a *theorem* once the quartet exists. -/
theorem physicalPositivity_of_quartet (hQ : IsBrst Q) (q : BrstQuartet Q) {η : H →ₗ[ℂ] H}
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    (hEtaPhys : ∀ y : H, η (q.physProj y) = q.physProj y) :
    PhysicalPositivity Q η := by
  have hval : ∀ x : H, x ∈ closed Q → (kform η x x).re = ‖q.physProj x‖ ^ 2 := by
    intro x hx
    rw [kform_quartet_reduce hQ q hKrein hSymm hx, kform, hEtaPhys,
      inner_self_eq_norm_sq_to_K, sq, Complex.mul_re]
    simp [pow_two]
  refine ⟨fun x hx => ?_, fun x hx hzero => ?_⟩
  · rw [hval x hx]
    positivity
  · have hzero' : ‖q.physProj x‖ ^ 2 = 0 := by rw [← hval x hx]; exact hzero
    have hv : q.physProj x = 0 := by
      have : ‖q.physProj x‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero'
      exact norm_eq_zero.mp this
    refine ⟨q.bGhost x, ?_⟩
    have h := q.quartet_decompose hx
    rw [hv, add_zero] at h
    exact h.symm

/-- **Kugo–Ojima positivity from positivity *on the physical subspace*.**  The fixing hypothesis
`η (V y) = V y` of `physicalPositivity_of_quartet` is stronger than the no-ghost argument needs:
a metric that merely *defines an inner product* on the range of `V` suffices, because the quartet
reduction turns the charge form of a closed state into the charge form of its physical part.  So
this version replaces "`η` fixes the physical subspace" — false for an indefinite ghost metric —
by "`η` is positive definite there", which is what a no-ghost estimate actually establishes. -/
theorem physicalPositivity_of_quartet_on_range (hQ : IsBrst Q) (q : BrstQuartet Q)
    {η : H →ₗ[ℂ] H}
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    (hPos : ∀ y : H, 0 ≤ (kform η (q.physProj y) (q.physProj y)).re)
    (hDef : ∀ y : H, (kform η (q.physProj y) (q.physProj y)).re = 0 → q.physProj y = 0) :
    PhysicalPositivity Q η := by
  refine ⟨fun x hx => ?_, fun x hx hzero => ?_⟩
  · rw [kform_quartet_reduce hQ q hKrein hSymm hx]
    exact hPos x
  · rw [kform_quartet_reduce hQ q hKrein hSymm hx] at hzero
    have hv : q.physProj x = 0 := hDef x hzero
    refine ⟨q.bGhost x, ?_⟩
    have h := q.quartet_decompose hx
    rw [hv, add_zero] at h
    exact h.symm

/-! ## 4. Positivity sector by sector -/

/-- **The quartet reduction, resolved into parity sectors.**  Adding §46's split of the charge
form to the quartet reduction: on a closed vector the form is the sum of the forms of the even
and odd parts of the *physical* part. -/
theorem kform_quartet_reduce_sectors (hQ : IsBrst Q) (q : BrstQuartet Q) {η U : H →ₗ[ℂ] H}
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    {x : H} (hx : x ∈ closed Q) :
    (kform η x x).re
      = (kform η (evenPart U (q.physProj x)) (evenPart U (q.physProj x))).re
        + (kform η (oddPart U (q.physProj x)) (oddPart U (q.physProj x))).re := by
  rw [kform_quartet_reduce hQ q hKrein hSymm hx]
  exact kform_quadForm_split hU hUnorm hηU (q.physProj x)

/-- **The no-ghost theorem, sector by sector.**  If the charge form is non-negative on the
physical subspace inside each parity sector, and vanishes there only on `0`, then
`PhysicalPositivity` holds.  This is the shape a physical smoke test takes: each sector is a
separate estimate, and the quartet mechanism assembles them. -/
theorem physicalPositivity_of_quartet_sectors (hQ : IsBrst Q) (q : BrstQuartet Q)
    {η U : H →ₗ[ℂ] H} (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    (hev : ∀ y : H, y ∈ evenSpace U → 0 ≤ (kform η y y).re)
    (hod : ∀ y : H, y ∈ oddSpace U → 0 ≤ (kform η y y).re)
    (hevDef : ∀ y : H, y ∈ evenSpace U → (kform η y y).re = 0 → y = 0)
    (hodDef : ∀ y : H, y ∈ oddSpace U → (kform η y y).re = 0 → y = 0) :
    PhysicalPositivity Q η := by
  refine ⟨fun x hx => ?_, fun x hx hzero => ?_⟩
  · rw [kform_quartet_reduce_sectors hQ q hU hUnorm hηU hKrein hSymm hx]
    exact add_nonneg
      (hev (evenPart U (q.physProj x)) (evenPart_mem hU (q.physProj x)))
      (hod (oddPart U (q.physProj x)) (oddPart_mem hU (q.physProj x)))
  · set a := evenPart U (q.physProj x) with ha
    set b := oddPart U (q.physProj x) with hb
    have hsum := kform_quartet_reduce_sectors hQ q hU hUnorm hηU hKrein hSymm hx
    rw [← ha, ← hb, hzero] at hsum
    have han := hev a (ha ▸ evenPart_mem hU (q.physProj x))
    have hbn := hod b (hb ▸ oddPart_mem hU (q.physProj x))
    have ha0 : (kform η a a).re = 0 := by linarith
    have hb0 : (kform η b b).re = 0 := by linarith
    have hzeroV : q.physProj x = 0 := by
      have he : a = 0 := hevDef a (ha ▸ evenPart_mem hU (q.physProj x)) ha0
      have ho : b = 0 := hodDef b (hb ▸ oddPart_mem hU (q.physProj x)) hb0
      have hsplit := evenPart_add_oddPart (U := U) (q.physProj x)
      rw [← ha, ← hb, he, ho, add_zero] at hsplit
      exact hsplit.symm
    refine ⟨q.bGhost x, ?_⟩
    have h := q.quartet_decompose hx
    rw [hzeroV, add_zero] at h
    exact h.symm


/-! ## 5. The physical projector is *constructed* from the b-ghost

§47 states the no-ghost theorem from quartet data `(P, V)`.  That leaves two objects to exhibit.
This section removes one of them: if `P` only contracts — `Q P Q = Q` and `P Q P = P`, which is
what a b-ghost does — then the projector is *computed*,

  `V = 1 − (Q P + P Q) + Q P² Q`,

and the b-ghost of the quartet is `P − Q P²`.  The correction term is not decoration: with the
naive `1 − (QP + PQ)` the idempotency fails by exactly `Q P² Q`, and the anticommutator misses
`− Q P² Q` as well.  Both defects come from the same product `(QP)(PQ) = Q P² Q`, and placing it
in `V` fixes them simultaneously.

So the physics input for the Standard Model is a single object — the contracting homotopy of the
ghost complex, i.e. the gauge-fixed b-ghost — and `quartetOfHomotopy` produces the quartet from
it.  If that `P` is ghost-parity even (`U P = P U` for the parity `U`), `V` is even too, hence
`V` preserves each parity sector, which is what `physicalPositivity_of_quartet_sectors` consumes:
positivity on the ghost-parity-even sector and on the odd one. -/

/-- **The physical projector determined by a contracting homotopy**:
`V = 1 − (Q P + P Q) + Q P² Q`. -/
def physProjOf (Q P : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  LinearMap.id - (Q.comp P + P.comp Q) + Q.comp (P.comp (P.comp Q))

/-- **The b-ghost of the quartet**: `P` itself, corrected by `Q P²` so that its anticommutator
with `Q` is `1 − V` rather than `1 − V + Q P² Q`. -/
def bGhostOf (Q P : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  P - Q.comp (P.comp P)

theorem physProjOf_apply (Q P : H →ₗ[ℂ] H) (x : H) :
    physProjOf Q P x = x - (Q (P x) + P (Q x)) + Q (P (P (Q x))) := rfl

theorem bGhostOf_apply (Q P : H →ₗ[ℂ] H) (x : H) :
    bGhostOf Q P x = P x - Q (P (P x)) := rfl

/-- **`Q P` is a projection** whenever `P Q P = P`. -/
theorem QP_idem {Q P : H →ₗ[ℂ] H} (hSQS : ∀ x : H, P (Q (P x)) = P x) (x : H) :
    Q (P (Q (P x))) = Q (P x) := by
  rw [hSQS x]

/-- **The range of the constructed projector is BRST-closed.** -/
theorem physProjOf_Q {Q P : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hQSQ : ∀ x : H, Q (P (Q x)) = Q x) (x : H) :
    Q (physProjOf Q P x) = 0 := by
  simp only [physProjOf_apply, map_add, map_sub, hQSQ x, Q_apply_apply hQ (P x),
    Q_apply_apply hQ (P (P (Q x))), add_zero]
  abel

/-- **The constructed projector kills the gauge orbit**: `V Q = 0`. -/
theorem physProjOf_comp_Q {Q P : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hQSQ : ∀ x : H, Q (P (Q x)) = Q x) (x : H) :
    physProjOf Q P (Q x) = 0 := by
  simp only [physProjOf_apply, hQSQ x, Q_apply_apply hQ x, map_zero]
  abel

/-- **The correction term is exactly what idempotency needs**: `Q P (V x) = 0`. -/
theorem QP_physProjOf {Q P : H →ₗ[ℂ] H} (hSQS : ∀ x : H, P (Q (P x)) = P x)
    (x : H) : Q (P (physProjOf Q P x)) = 0 := by
  simp only [physProjOf_apply, map_add, map_sub, QP_idem hSQS x, QP_idem hSQS (P (Q x))]
  abel

/-- **The constructed `V` is a projector.**  `Π = QP + PQ − QP²Q` is idempotent, and `V = 1 − Π`;
`Π (V x) = 0` because `QP`, `PQ` and `QP²Q` all annihilate `V x` — the first by
`QP_physProjOf`, the other two because `Q (V x) = 0`. -/
theorem physProjOf_idem {Q P : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hQSQ : ∀ x : H, Q (P (Q x)) = Q x) (hSQS : ∀ x : H, P (Q (P x)) = P x) (x : H) :
    physProjOf Q P (physProjOf Q P x) = physProjOf Q P x := by
  set y : H := physProjOf Q P x with hy
  have hQy : Q y = 0 := physProjOf_Q hQ hQSQ x
  have hQPy : Q (P y) = 0 := QP_physProjOf hSQS x
  have hPQy : P (Q y) = 0 := by rw [hQy, map_zero]
  rw [show physProjOf Q P y = y - (Q (P y) + P (Q y)) + Q (P (P (Q y)))
    from physProjOf_apply Q P y]
  rw [hQPy, hPQy]
  simp only [map_zero]
  abel

/-- **The b-ghost kills its own projector's range**: `P (V x) = 0`.  `P` applied to
`Π = QP + PQ − QP²Q` is `P x + P²Q x − P Q (P²Q) x`, and the last two terms agree by the
contraction identity `P Q P = P`, so `P (V x) = P x − P (Π x) = 0`. -/
theorem P_physProjOf {Q P : H →ₗ[ℂ] H} (hSQS : ∀ x : H, P (Q (P x)) = P x) (x : H) :
    P (physProjOf Q P x) = 0 := by
  have ht : P (Q (P (P (Q x)))) = P (P (Q x)) := hSQS (P (Q x))
  simp only [physProjOf_apply, map_add, map_sub, hSQS x, ht]
  abel

/-- **The physical subspace of a contracting homotopy, exactly**: the range of the constructed
projector is the closed states that the contracting homotopy kills,

  `range V = ker Q ⊓ ker P`.

Both inclusions are immediate from the contraction identities: `V x` is closed and
`P (V x) = 0` by `P_physProjOf`, while a closed vector with `P x = 0` has `V x = x`.  This is the
precise content of "harmonic representatives"; note that *which* complement of the exact states
it cuts out is entirely a property of `P` — nothing here singles out a transverse or parity
description. -/
theorem range_physProjOf {Q P : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hQSQ : ∀ x : H, Q (P (Q x)) = Q x) (hSQS : ∀ x : H, P (Q (P x)) = P x) :
    LinearMap.range (physProjOf Q P) = closed Q ⊓ LinearMap.ker P := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    exact ⟨physProjOf_Q hQ hQSQ y, P_physProjOf hSQS y⟩
  · rintro x ⟨hx, hPx⟩
    refine ⟨x, ?_⟩
    have hQx : Q x = 0 := hx
    have hP : P x = 0 := hPx
    rw [physProjOf_apply, hQx, hP, map_zero, map_zero, map_zero, map_zero]
    abel

/-- **The quartet identity for the constructed pair**: `Q P' + P' Q = 1 − V` with
`P' = P − Q P²`.  The two terms are `Q P` and `P Q − Q P² Q`, whose sum is exactly `1 − V`. -/
theorem bGhostOf_anticomm {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) (P : H →ₗ[ℂ] H) (x : H) :
    Q (bGhostOf Q P x) + bGhostOf Q P (Q x) = x - physProjOf Q P x := by
  have h1 : Q (Q (P (P x))) = 0 := Q_apply_apply hQ (P (P x))
  have h2 : Q (Q (P (P (Q x)))) = 0 := Q_apply_apply hQ (P (P (Q x)))
  simp only [bGhostOf_apply, physProjOf_apply, map_sub, h1]
  abel

/-- **The quartet assembled from a contracting homotopy.**  `P` is the b-ghost and the physical
projector is computed from it; nothing about `V` is assumed. -/
def quartetOfHomotopy {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) {P : H →ₗ[ℂ] H}
    (hQSQ : ∀ x : H, Q (P (Q x)) = Q x) (hSQS : ∀ x : H, P (Q (P x)) = P x) :
    BrstQuartet Q where
  bGhost := bGhostOf Q P
  physProj := physProjOf Q P
  physProj_idem := physProjOf_idem hQ hQSQ hSQS
  Q_physProj := physProjOf_Q hQ hQSQ
  quartet_anticomm := bGhostOf_anticomm hQ P

/-- **Kugo–Ojima positivity from a b-ghost alone.**  The only physical input is the contracting
homotopy `P` of the ghost complex and the metric hypothesis on its constructed range. -/
theorem physicalPositivity_of_homotopy {Q P η : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hQSQ : ∀ x : H, Q (P (Q x)) = Q x) (hSQS : ∀ x : H, P (Q (P x)) = P x)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    (hEtaPhys : ∀ y : H, η (physProjOf Q P y) = physProjOf Q P y) :
    PhysicalPositivity Q η :=
  physicalPositivity_of_quartet hQ (quartetOfHomotopy hQ hQSQ hSQS) hKrein hSymm hEtaPhys

/-- **The no-ghost theorem from a b-ghost, with positivity only on the constructed range.**  The
fixing hypothesis `η (V y) = V y` is dropped in favour of `η` being positive definite on `ker Q ⊓
ker P` — the subspace `range_physProjOf` identifies — so the physical input is a genuine
no-ghost estimate on the physical subspace rather than an identity on the metric. -/
theorem physicalPositivity_of_homotopy_on_range {Q P η : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hQSQ : ∀ x : H, Q (P (Q x)) = Q x) (hSQS : ∀ x : H, P (Q (P x)) = P x)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    (hPos : ∀ y : H, 0 ≤ (kform η (physProjOf Q P y) (physProjOf Q P y)).re)
    (hDef : ∀ y : H, (kform η (physProjOf Q P y) (physProjOf Q P y)).re = 0 →
      physProjOf Q P y = 0) :
    PhysicalPositivity Q η :=
  physicalPositivity_of_quartet_on_range hQ (quartetOfHomotopy hQ hQSQ hSQS) hKrein hSymm hPos hDef

/-- **A parity-even b-ghost gives a parity-even projector.**  `V` is a polynomial in `Q` and `P`,
so any `U` commuting with both commutes with `V`. -/
theorem physProjOf_commute_parity {Q P U : H →ₗ[ℂ] H}
    (hUQ : ∀ x : H, U (Q x) = Q (U x)) (hUP : ∀ x : H, U (P x) = P (U x)) (x : H) :
    U (physProjOf Q P x) = physProjOf Q P (U x) := by
  simp only [physProjOf_apply, map_add, map_sub, hUQ, hUP]

/-- **The constructed projector preserves the ghost-parity-even sector**: on the even sector, `V`
takes values in the same sector, so the physical subspace restricted to the even sector is `V`'s
range there. -/
theorem physProjOf_mem_even {Q P U : H →ₗ[ℂ] H}
    (hUQ : ∀ x : H, U (Q x) = Q (U x)) (hUP : ∀ x : H, U (P x) = P (U x))
    {x : H} (hx : x ∈ evenSpace U) : physProjOf Q P x ∈ evenSpace U := by
  have hx' : U x = x := by simpa [evenSpace, sub_eq_zero] using hx
  refine LinearMap.mem_ker.mpr ?_
  have hsub : (U - (LinearMap.id : H →ₗ[ℂ] H)) (physProjOf Q P x)
      = U (physProjOf Q P x) - physProjOf Q P x := by
    rw [LinearMap.sub_apply, LinearMap.id_apply]
  rw [hsub, physProjOf_commute_parity hUQ hUP x, hx', sub_self]

/-- **The no-ghost theorem sector by sector, from a parity-even b-ghost.**  Non-negativity and
definiteness are required only on the physical subspace inside each parity sector; the quartet
mechanism and the constructed projector assemble them into `PhysicalPositivity`. -/
theorem physicalPositivity_of_homotopy_sectors {Q P η U : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hQSQ : ∀ x : H, Q (P (Q x)) = Q x) (hSQS : ∀ x : H, P (Q (P x)) = P x)
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖) (hηU : η ∘ₗ U = U ∘ₗ η)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    (hev : ∀ y : H, y ∈ evenSpace U → 0 ≤ (kform η y y).re)
    (hod : ∀ y : H, y ∈ oddSpace U → 0 ≤ (kform η y y).re)
    (hevDef : ∀ y : H, y ∈ evenSpace U → (kform η y y).re = 0 → y = 0)
    (hodDef : ∀ y : H, y ∈ oddSpace U → (kform η y y).re = 0 → y = 0) :
    PhysicalPositivity Q η :=
  physicalPositivity_of_quartet_sectors hQ (quartetOfHomotopy hQ hQSQ hSQS) hU hUnorm hηU
    hKrein hSymm hev hod hevDef hodDef

end BrstQuartet

/-! ## 6. The hypotheses are not vacuous: a quartet block plus a physical line -/

/-- Extensionality for `EuclideanSpace` through its coordinate representation. -/
private theorem lp_ext {x y : EuclideanSpace ℂ (Fin 3)} (h : x.ofLp = y.ofLp) : x = y := by
  rw [← WithLp.toLp_ofLp 2 x, ← WithLp.toLp_ofLp 2 y, h]

/-- The quartet block `Q : e₀ ↦ e₁` on `ℂ³`: it shifts the first coordinate onto the second and
is nilpotent. -/
def exQ : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun v := WithLp.toLp 2 (Pi.single 1 (v.ofLp 0))
  map_add' x y := by
    apply lp_ext
    simp [Pi.single_add]
  map_smul' c x := by
    apply lp_ext
    simp [← Pi.single_smul, smul_eq_mul]

/-- The b-ghost `P : e₁ ↦ e₀` of the quartet block. -/
def exP : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun v := WithLp.toLp 2 (Pi.single 0 (v.ofLp 1))
  map_add' x y := by
    apply lp_ext
    simp [Pi.single_add]
  map_smul' c x := by
    apply lp_ext
    simp [← Pi.single_smul, smul_eq_mul]

/-- The physical projector `V : e₂ ↦ e₂`. -/
def exV : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun v := WithLp.toLp 2 (Pi.single 2 (v.ofLp 2))
  map_add' x y := by
    apply lp_ext
    simp [Pi.single_add]
  map_smul' c x := by
    apply lp_ext
    simp [← Pi.single_smul, smul_eq_mul]

/-- The metric operator: `σ₁` acting on the quartet block, the identity on the physical line.
It is indefinite, as it must be: a nilpotent self-adjoint charge cannot exist in a definite
space (`Q² = 0` with `Q = Q*` forces `Q = 0`). -/
def exEta : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun v := WithLp.toLp 2 (Pi.single 0 (v.ofLp 1) + Pi.single 1 (v.ofLp 0)
    + Pi.single 2 (v.ofLp 2))
  map_add' x y := by
    apply lp_ext
    simp only [WithLp.ofLp_add, Pi.add_apply, Pi.single_add]
    abel
  map_smul' c x := by
    apply lp_ext
    simp [← Pi.single_smul, smul_eq_mul]

theorem exQ_apply (v : EuclideanSpace ℂ (Fin 3)) :
    (exQ v).ofLp = Pi.single 1 (v.ofLp 0) := rfl

theorem exP_apply (v : EuclideanSpace ℂ (Fin 3)) :
    (exP v).ofLp = Pi.single 0 (v.ofLp 1) := rfl

theorem exV_apply (v : EuclideanSpace ℂ (Fin 3)) :
    (exV v).ofLp = Pi.single 2 (v.ofLp 2) := rfl

theorem exEta_apply (v : EuclideanSpace ℂ (Fin 3)) :
    (exEta v).ofLp = Pi.single 0 (v.ofLp 1) + Pi.single 1 (v.ofLp 0)
      + Pi.single 2 (v.ofLp 2) := rfl

/-- **The worked example is reconstructed from its b-ghost**: `exP` contracts (`exQ exP exQ = exQ`,
`exP exQ exP = exP`), and the projector computed from it is `exV`.  So the construction of §5 is
not vacuous on the model block. -/
theorem exQ_exP_exQ (v : EuclideanSpace ℂ (Fin 3)) : exQ (exP (exQ v)) = exQ v := by
  apply lp_ext
  funext i
  fin_cases i <;>
    simp [exQ_apply, exP_apply, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem exP_exQ_exP (v : EuclideanSpace ℂ (Fin 3)) : exP (exQ (exP v)) = exP v := by
  apply lp_ext
  funext i
  fin_cases i <;>
    simp [exQ_apply, exP_apply, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem exP_exQ_exP_gives_V (v : EuclideanSpace ℂ (Fin 3)) :
    BrstQuartet.physProjOf exQ exP v = exV v := by
  apply lp_ext
  funext i
  fin_cases i <;>
    simp [BrstQuartet.physProjOf_apply, exQ_apply, exP_apply, exV_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne]

theorem exQ_nil : IsBrst exQ := by
  refine LinearMap.ext fun v => lp_ext ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply, exQ_apply, exQ_apply]
  simp

/-- The example charge kills the physical line. -/
theorem exQ_exV (v : EuclideanSpace ℂ (Fin 3)) : exQ (exV v) = 0 := by
  apply lp_ext
  rw [exQ_apply, exV_apply]
  simp

/-- The example projector is idempotent. -/
theorem exV_idem (v : EuclideanSpace ℂ (Fin 3)) : exV (exV v) = exV v := by
  apply lp_ext
  rw [exV_apply, exV_apply, Pi.single_eq_same]

/-- **The quartet identity `Q P + P Q = 1 - V` in the example.** -/
theorem exQuartet_anticomm (v : EuclideanSpace ℂ (Fin 3)) :
    exQ (exP v) + exP (exQ v) = v - exV v := by
  apply lp_ext
  simp only [WithLp.ofLp_add, WithLp.ofLp_sub, exQ_apply, exP_apply, exV_apply]
  ext i
  fin_cases i <;>
    simp [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne]

/-- **The 3-dimensional example satisfies the quartet hypotheses**: a two-dimensional quartet
block plus a physical line, with `V` the projector onto the line.  The quartet identity
`Q P + P Q = 1 - V` holds, so the hypotheses of `physicalPositivity_of_quartet` are consistent. -/
def exQuartet : BrstQuartet exQ where
  bGhost := exP
  physProj := exV
  physProj_idem := exV_idem
  Q_physProj := exQ_exV
  quartet_anticomm := exQuartet_anticomm

/-- The example metric fixes the physical line, which is what the no-ghost theorem needs. -/
theorem exEta_physProj_v (v : EuclideanSpace ℂ (Fin 3)) : exEta (exV v) = exV v := by
  apply lp_ext
  rw [exEta_apply, exV_apply]
  ext i
  fin_cases i <;>
    simp [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem exEta_physProj (v : EuclideanSpace ℂ (Fin 3)) :
    exEta (exQuartet.physProj v) = exQuartet.physProj v :=
  exEta_physProj_v v

/-- The example charge is self-adjoint for the example charge form: `Qᵀ η = η Q` holds for the
pair `(Q, η)`, which is the Krein self-adjointness hypothesis. -/
theorem exKrein (x y : EuclideanSpace ℂ (Fin 3)) :
    kform exEta (exQ x) y = kform exEta x (exQ y) := by
  rw [kform, kform, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three,
    Fin.sum_univ_three]
  simp [exQ_apply, exEta_apply, Pi.single_eq_same, Pi.single_eq_of_ne]

/-- The example charge form is symmetric. -/
theorem exSymm (x y : EuclideanSpace ℂ (Fin 3)) :
    kform exEta x y = star (kform exEta y x) := by
  rw [kform, kform, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_three,
    Fin.sum_univ_three]
  simp only [exEta_apply]
  simp [star_add, star_mul, Pi.single_eq_same, Pi.single_eq_of_ne]
  ring

/-- **`PhysicalPositivity` holds in the example**, obtained from the quartet rather than assumed:
the charge form is `‖V x‖²` on the closed space, and its radical is the gauge orbit. -/
theorem exPhysicalPositivity : PhysicalPositivity exQ exEta :=
  BrstQuartet.physicalPositivity_of_quartet exQ_nil exQuartet exKrein exSymm exEta_physProj

/-- The physical vector `e₂` of the example. -/
def exE2 : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 (Pi.single 2 1)

/-- The physical line of the example lies in the closed space. -/
theorem exE2_closed : exE2 ∈ closed exQ := by
  apply lp_ext
  rw [exQ_apply]
  simp [exE2]

/-- …and is *not* exact, so the example's cohomology is non-trivial: `PhysicalPositivity` is
not being applied to a space on which everything is a gauge orbit. -/
theorem exE2_not_exact : ¬ ∃ w : EuclideanSpace ℂ (Fin 3), exQ w = exE2 := by
  rintro ⟨w, hw⟩
  have h := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => z.ofLp 2) hw
  simp [exQ_apply, exE2, Pi.single_eq_of_ne] at h

/-! ## 7. The link to the Standard Model charge -/

open BookProof.SmBrstGhost in
/-- **The Standard-Model charge is a BRST charge in the sense of §46.**  This is the hypothesis
`IsBrst` of the quartet mechanism, discharged for `smBrstCharge` by the nilpotency proved in
`ChapterSmBrstGhost`.  The rest of the quartet data — the b-ghost `P` and the projector `V` — is
constructed in §8 (`smBghost`, `smQuartet`), so `physicalPositivity_of_quartet` does apply to the
SM; what stays a hypothesis is positivity of the charge form on `V`'s range (§9,
`smPhysicalPositivity_of_physForm`). -/
theorem isBrst_smBrstCharge {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    IsBrst (smBrstCharge m T f3) := by
  rw [IsBrst, ← Module.End.mul_eq_comp]
  exact smBrstCharge_nilpotent hT h3anti h3jac

/-! ## 8. The b-ghost of the Standard-Model charge

§47.5 reduced the quartet data to a single object, a contracting homotopy of the charge.  On a
finite-dimensional space `Q` is injective on a complement `C` of its kernel and onto its range, so
inverting `Q` on `C` and projecting onto the range produces `P` with `Q P Q = Q` and
`P Q P = P` (`exists_contractingHomotopy`).  `FermiFock (m + 12)` is finite-dimensional, so nothing
about the model's mode content obstructs the construction: `smQuartet` is the quartet of
`smBrstCharge` itself, `smBghost` its b-ghost, and `smPhysProj` its physical projector.

The construction is *choice-based*: `smQuartet` is picked from a `Nonempty` proof, so no formula
for the b-ghost is exhibited.  That is also its limit.  The quartet *data* exists, the quartet
identity holds, and §9 characterises the range of the projector exactly
(`range V = ker Q ⊓ ker P`), but nothing identifies that range with the transverse,
ghost-parity-even states of the gauge-fixed model — that needs a concrete mode pairing, which a
chosen homotopy does not supply.  §9 therefore also shows that the fixing hypothesis `hEtaPhys`
is not needed: positivity of the charge form on `range smPhysProj` suffices
(`smPhysicalPositivity_of_physForm`), so P5's open part is a no-ghost estimate on the physical
subspace, not the existence of the quartet data. -/

/-- **Every endomorphism of a finite-dimensional space has a contracting homotopy.**  Split the
kernel off a complement `C`: `Q` is injective on `C` and onto its range, so inverting `Q` there and
projecting onto the range gives `Q P Q = Q` and `P Q P = P`.  Nilpotency is *not* used here; it
enters only when the homotopy is turned into a quartet. -/
theorem exists_contractingHomotopy [FiniteDimensional ℂ H] (Q : H →ₗ[ℂ] H) :
    ∃ P : H →ₗ[ℂ] H, (∀ x : H, Q (P (Q x)) = Q x) ∧ ∀ x : H, P (Q (P x)) = P x := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker Q)
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (LinearMap.range Q)
  let πK : H →ₗ[ℂ] H := Submodule.IsCompl.projection hC
  have hπK_range : πK.range = LinearMap.ker Q := Submodule.IsCompl.projection_range hC
  have hQπK : ∀ x : H, Q (πK x) = 0 := by
    intro x
    have hx : πK x ∈ LinearMap.ker Q := by
      rw [← hπK_range]
      exact LinearMap.mem_range_self πK x
    exact hx
  have hCmem : ∀ x : H, x - πK x ∈ C := by
    intro x
    have hfix : πK (πK x) = πK x := by
      have hmem : πK x ∈ LinearMap.ker Q := by
        rw [← hπK_range]
        exact LinearMap.mem_range_self πK x
      exact Submodule.IsCompl.projection_apply_left hC ⟨πK x, hmem⟩
    have hidem : πK (x - πK x) = 0 := by
      rw [map_sub, hfix, sub_self]
    exact Submodule.IsCompl.projection_apply_eq_zero_iff hC |>.mp hidem
  let φ : C →ₗ[ℂ] (LinearMap.range Q) :=
    (Q.domRestrict C).codRestrict (LinearMap.range Q)
      (fun c => LinearMap.mem_range_self Q (c : H))
  have hφ_inj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have hQc : Q (c : H) = 0 := by
      have h := congrArg Subtype.val hc
      simpa [φ] using h
    have hboth : (c : H) ∈ (LinearMap.ker Q) ⊓ C := ⟨hQc, c.property⟩
    rw [hC.inf_eq_bot] at hboth
    exact Subtype.ext (by simpa using hboth)
  have hφ_surj : Function.Surjective φ := by
    intro r
    obtain ⟨x, hx⟩ := r.property
    refine ⟨⟨x - πK x, hCmem x⟩, ?_⟩
    apply Subtype.ext
    have hQz : Q ((⟨x - πK x, hCmem x⟩ : C) : H) = Q x := by
      change Q (x - πK x) = Q x
      rw [map_sub, hQπK x, sub_zero]
    have hφz : (φ ⟨x - πK x, hCmem x⟩ : H) = Q ((⟨x - πK x, hCmem x⟩ : C) : H) := rfl
    change (φ ⟨x - πK x, hCmem x⟩ : H) = (r : H)
    rw [hφz, hQz, hx]
  have hbij : Function.Bijective φ := ⟨hφ_inj, hφ_surj⟩
  let e : C ≃ₗ[ℂ] (LinearMap.range Q) := LinearEquiv.ofBijective φ hbij
  let πR : H →ₗ[ℂ] (LinearMap.range Q) := (LinearMap.range Q).linearProjOfIsCompl D hD
  let P : H →ₗ[ℂ] H := C.subtype.comp (e.symm.toLinearMap.comp πR)
  have hψ : ∀ r : LinearMap.range Q, (φ (e.symm r) : H) = (r : H) := by
    intro r
    have he : (e (e.symm r) : LinearMap.range Q) = φ (e.symm r) :=
      LinearEquiv.ofBijective_apply (f := φ) (hf := hbij) (e.symm r)
    have h := congrArg Subtype.val (LinearEquiv.apply_symm_apply e r)
    rw [he] at h
    exact h
  have hQP : ∀ z : H, Q (P z) = (πR z : H) := by
    intro z
    have hz : Q (P z) = (φ (e.symm (πR z)) : H) := rfl
    rw [hz, hψ (πR z)]
  refine ⟨P, ?_, ?_⟩
  · intro y
    rw [hQP (Q y)]
    exact congrArg Subtype.val
      (Submodule.linearProjOfIsCompl_apply_left hD ⟨Q y, LinearMap.mem_range_self Q y⟩)
  · intro y
    rw [hQP y]
    have hfix : πR (πR y : H) = πR y := Submodule.linearProjOfIsCompl_apply_left hD (πR y)
    simp [P, hfix]

open BookProof.SmBrstGhost BookProof.SmCar in
/-- **The quartet data of the Standard-Model charge exists.**  The contracting homotopy of
`smBrstCharge` is turned into a quartet by §47.5's construction; `FermiFock (m + 12)` is
finite-dimensional, so no property of the mode content is needed. -/
theorem smBrstCharge_quartet_nonempty {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    Nonempty (BrstQuartet (smBrstCharge m T f3)) := by
  classical
  obtain ⟨P, hQSQ, hSQS⟩ := exists_contractingHomotopy (smBrstCharge m T f3)
  exact ⟨BrstQuartet.quartetOfHomotopy (isBrst_smBrstCharge hT h3anti h3jac) hQSQ hSQS⟩

open BookProof.SmBrstGhost BookProof.SmCar in
/-- **The quartet of the Standard-Model charge**, chosen from `smBrstCharge_quartet_nonempty`.
The b-ghost `smBghost` and the physical projector `smPhysProj` are its fields. -/
noncomputable def smQuartet {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    BrstQuartet (smBrstCharge m T f3) :=
  Classical.choice (smBrstCharge_quartet_nonempty hT h3anti h3jac)

open BookProof.SmBrstGhost BookProof.SmCar in
/-- **The b-ghost of the Standard-Model charge**: the `bGhost` field of `smQuartet`, a b-ghost for
the full joint matter ⊗ ghost charge `smBrstCharge` rather than for a reduced block. -/
noncomputable def smBghost {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    BookProof.SmCar.FermiFock (m + 12) →ₗ[ℂ] BookProof.SmCar.FermiFock (m + 12) :=
  (smQuartet hT h3anti h3jac).bGhost

open BookProof.SmBrstGhost BookProof.SmCar in
/-- **The physical projector of the Standard-Model charge**: the `physProj` field of `smQuartet`.
It is determined by the b-ghost, not assumed. -/
noncomputable def smPhysProj {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    BookProof.SmCar.FermiFock (m + 12) →ₗ[ℂ] BookProof.SmCar.FermiFock (m + 12) :=
  (smQuartet hT h3anti h3jac).physProj

open BookProof.SmBrstGhost BookProof.SmCar in
/-- **Kugo–Ojima positivity for the Standard-Model charge from one metric hypothesis.**  The
quartet is `smQuartet` and the b-ghost is `smBghost`; the only remaining input is that the metric
`η` fixes the range of `smPhysProj` — the no-ghost statement, which is not derived here.  The
quartet identity itself is the field `(smQuartet hT h3anti h3jac).quartet_anticomm`, whose
`bGhost` and `physProj` are `smBghost` and `smPhysProj` by definition.  The fixing hypothesis is
stronger than necessary: `smPhysicalPositivity_of_physForm` derives the same conclusion from
positivity of the charge form on that range, which is the form a no-ghost estimate takes. -/
theorem smPhysicalPositivity_of_etaPhys {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0)
    (η : BookProof.SmCar.FermiFock (m + 12) →ₗ[ℂ] BookProof.SmCar.FermiFock (m + 12))
    (hKrein : ∀ x y : BookProof.SmCar.FermiFock (m + 12),
      kform η (smBrstCharge m T f3 x) y = kform η x (smBrstCharge m T f3 y))
    (hSymm : ∀ x y : BookProof.SmCar.FermiFock (m + 12),
      kform η x y = star (kform η y x))
    (hEtaPhys : ∀ y : BookProof.SmCar.FermiFock (m + 12),
      η (smPhysProj hT h3anti h3jac y) = smPhysProj hT h3anti h3jac y) :
    PhysicalPositivity (smBrstCharge m T f3) η :=
  BrstQuartet.physicalPositivity_of_quartet (isBrst_smBrstCharge hT h3anti h3jac)
    (smQuartet hT h3anti h3jac) hKrein hSymm hEtaPhys

/-! ## 9. The range of the SM physical projector

What §8 constructs is a projector whose range is *characterised*, not identified.  The general
statement `BrstQuartet.range_physProjOf` says that for a contracting homotopy `P`,

  `range V = ker Q ⊓ ker P`,

i.e. the physical subspace is the closed states killed by the b-ghost — the harmonic
representatives of the cohomology.  For the SM quartet this reads: the range of `smPhysProj` is
contained in the closed space of `smBrstCharge` (`smPhysProj_mem_closed`), and it is exactly the
intersection cut out by the chosen contracting homotopy.

That is as far as a *choice-based* construction reaches, and the limit is intrinsic: a
contracting homotopy is a choice of complement of the exact states inside the closed space, and
`range V = ker Q ⊓ ker P` depends on that choice.  Nothing in §8 fixes a mode pairing, so
nothing there singles out the transverse, ghost-parity-even subspace: that would need (i) a
concrete `P` (the pairing of each longitudinal/ghost mode with its partner), and (ii) a ghost
parity `U` with `U P = P U`, after which `physProjOf_mem_even` would place `range V` in the even
sector.  Neither is available for `smBrstCharge` in the corpus.

The compensating point is that the fixing hypothesis `hEtaPhys` was never the right form of the
input.  `physicalPositivity_of_quartet_on_range` derives `PhysicalPositivity` from `η` being
positive definite *on* the range of `V`, with no fixing of individual vectors — which is what a
no-ghost estimate on the physical subspace establishes — and `smPhysicalPositivity_of_physForm`
is that statement at `smBrstCharge`.  So the remaining input is positivity of the charge form on
`range smPhysProj`, not an identity `η (V y) = V y`. -/

open BookProof.SmBrstGhost BookProof.SmCar in
/-- **The range of the SM physical projector is closed.**  Pointwise form of
`BrstQuartet.mem_closed_physProj` at `smBrstCharge`, i.e. the first half of the description
`range V = ker Q ⊓ ker P`. -/
theorem smPhysProj_mem_closed {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0)
    (y : BookProof.SmCar.FermiFock (m + 12)) :
    smPhysProj hT h3anti h3jac y ∈ closed (smBrstCharge m T f3) :=
  BrstQuartet.mem_closed_physProj (smQuartet hT h3anti h3jac) y

open BookProof.SmBrstGhost BookProof.SmCar in
/-- **Kugo–Ojima positivity for the Standard-Model charge from positivity on its physical
subspace.**  This is the weakest correct form of the remaining input: `η` defines an inner
product on the range of `smPhysProj` (non-negative there, and vanishing only at `0`).  No
identity `η (V y) = V y` is assumed, and no identification of that range with a transverse or
parity-even subspace is used — the quartet mechanism turns the charge form of a closed state
into the charge form of its physical part, and the estimate is taken there. -/
theorem smPhysicalPositivity_of_physForm {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ}
    (hT : BookProof.YangMillsSU3.ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0)
    (η : BookProof.SmCar.FermiFock (m + 12) →ₗ[ℂ] BookProof.SmCar.FermiFock (m + 12))
    (hKrein : ∀ x y : BookProof.SmCar.FermiFock (m + 12),
      kform η (smBrstCharge m T f3 x) y = kform η x (smBrstCharge m T f3 y))
    (hSymm : ∀ x y : BookProof.SmCar.FermiFock (m + 12),
      kform η x y = star (kform η y x))
    (hPos : ∀ y : BookProof.SmCar.FermiFock (m + 12),
      0 ≤ (kform η (smPhysProj hT h3anti h3jac y) (smPhysProj hT h3anti h3jac y)).re)
    (hDef : ∀ y : BookProof.SmCar.FermiFock (m + 12),
      (kform η (smPhysProj hT h3anti h3jac y) (smPhysProj hT h3anti h3jac y)).re = 0 →
        smPhysProj hT h3anti h3jac y = 0) :
    PhysicalPositivity (smBrstCharge m T f3) η :=
  BrstQuartet.physicalPositivity_of_quartet_on_range (isBrst_smBrstCharge hT h3anti h3jac)
    (smQuartet hT h3anti h3jac) hKrein hSymm hPos hDef


/-! ## 10. The quartet does not supply positivity: a decided counterexample

§9 reduced Kugo–Ojima positivity to positivity of the charge form on the physical range.  This
section shows that the reduction cannot be sharpened any further *by the quartet mechanism alone*:
there is a three-dimensional quartet — nilpotent charge, b-ghost, quartet identity, and a metric
that is self-adjoint and for which the charge is symmetric, i.e. all of §1's hypotheses except
positivity itself — for which the physical direction is negative.

The model: `Q` maps `e₀ ↦ e₁` and kills `e₁, e₂`; `b` maps `e₁ ↦ e₀`; `Q b + b Q = 1 − V` with `V`
the projection onto `e₂`, so `e₂` is the physical state — closed, and fixed by `V`.  The metric
`η x = x₁ e₀ + x₀ e₁ − x₂ e₂` is the ghost pairing on the `(e₀, e₁)` pair and `−1` on `e₂`; it is
self-adjoint (`kform_exEtah_symm`) and the charge is symmetric for it (`kform_exEtah_Q`), which are
exactly §3's `hSymm` and `hKrein`.  Positivity fails at the physical state itself:
`(kform η e₂ e₂).re = −1` (`exNotPhysicalPositivity`), so no strengthening of the *projection*
side can recover positivity — a no-ghost estimate on the metric must do it.

**Scope.**  This is a statement about the quartet *schema*, not about the Standard Model: the
model's charge is not this `Q`, and the section does not claim that the SM's physical sector is
negative.
What it decides is that `PhysicalPositivity` is an independent input rather than a consequence of
§1–§9, which is why §8's `smQuartet` does not discharge it.

-/

/-- The three-dimensional model space of the counterexample. -/
abbrev ExSpace := EuclideanSpace ℂ (Fin 3)

/-- The `i`-th coordinate functional on `EuclideanSpace ℂ (Fin 3)`. -/
def exProjL (i : Fin 3) : ExSpace →ₗ[ℂ] ℂ := (EuclideanSpace.proj i).toLinearMap

/-- The `i`-th basis vector. -/
def exE3 (i : Fin 3) : ExSpace := EuclideanSpace.single i 1

/-- The charge: `e₀ ↦ e₁`, `e₁, e₂ ↦ 0`. -/
def exQh : ExSpace →ₗ[ℂ] ExSpace := (LinearMap.toSpanSingleton ℂ ExSpace (exE3 1)).comp (exProjL 0)

/-- The b-ghost: `e₁ ↦ e₀`. -/
def exBh : ExSpace →ₗ[ℂ] ExSpace := (LinearMap.toSpanSingleton ℂ ExSpace (exE3 0)).comp (exProjL 1)

/-- The physical projector: onto `e₂`. -/
def exVh : ExSpace →ₗ[ℂ] ExSpace := (LinearMap.toSpanSingleton ℂ ExSpace (exE3 2)).comp (exProjL 2)

/-- The Krein metric: the ghost pairing on `0, 1` and `−1` on the physical direction. -/
def exEtah : ExSpace →ₗ[ℂ] ExSpace :=
  (LinearMap.toSpanSingleton ℂ ExSpace (exE3 0)).comp (exProjL 1)
    + (LinearMap.toSpanSingleton ℂ ExSpace (exE3 1)).comp (exProjL 0)
    - (LinearMap.toSpanSingleton ℂ ExSpace (exE3 2)).comp (exProjL 2)

theorem exQh_apply (x : ExSpace) : exQh x = x.ofLp 0 • exE3 1 := rfl

theorem exBh_apply (x : ExSpace) : exBh x = x.ofLp 1 • exE3 0 := rfl

theorem exVh_apply (x : ExSpace) : exVh x = x.ofLp 2 • exE3 2 := rfl

theorem exEtah_apply (x : ExSpace) :
    exEtah x = x.ofLp 1 • exE3 0 + x.ofLp 0 • exE3 1 - x.ofLp 2 • exE3 2 := by
  simp [exEtah, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, exProjL]

theorem exOfLpSingle (i j : Fin 3) :
    (EuclideanSpace.single i (1 : ℂ)).ofLp j = if i = j then 1 else 0 := by
  simp [EuclideanSpace.single_apply, eq_comm]

theorem exInnerE3 (i j : Fin 3) (a b : ℂ) :
    inner ℂ (a • exE3 i) (b • exE3 j) = (starRingEnd ℂ) a * b * (if i = j then 1 else 0) := by
  rw [exE3, exE3, inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left, exOfLpSingle]
  simp only [map_one]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The coordinate of a scaled basis vector. -/
theorem exSmulE3 (i j : Fin 3) (a : ℂ) : (a • exE3 i).ofLp j = a * (if i = j then 1 else 0) := by
  rw [PiLp.smul_apply, smul_eq_mul, exE3, exOfLpSingle]

theorem exQh_comp : exQh ∘ₗ exQh = 0 := by
  refine LinearMap.ext fun x => ?_
  have h : exQh (exQh x) = 0 := by
    rw [exQh_apply, exQh_apply, exSmulE3]
    simp
  simpa using h

theorem quartet_pt (x : ExSpace) : exQh (exBh x) + exBh (exQh x) = x - exVh x := by
  rw [exBh_apply, exQh_apply, exQh_apply, exBh_apply, exVh_apply]
  refine PiLp.ext fun i => ?_
  rw [PiLp.add_apply, PiLp.sub_apply, exSmulE3, exSmulE3, exSmulE3]
  fin_cases i <;> simp [PiLp.smul_apply, smul_eq_mul, exE3]

theorem isBrst_exQh : IsBrst exQh := exQh_comp

theorem exInnerE3r (i j : Fin 3) (a : ℂ) :
    inner ℂ (a • exE3 i) (exE3 j) = (starRingEnd ℂ) a * (if i = j then 1 else 0) := by
  simpa using exInnerE3 i j a 1

theorem exInnerE3l (i j : Fin 3) (b : ℂ) :
    inner ℂ (exE3 i) (b • exE3 j) = b * (if i = j then 1 else 0) := by
  simpa using exInnerE3 i j 1 b

theorem exInnerE3b (i j : Fin 3) :
    inner ℂ (exE3 i) (exE3 j) = (if i = j then 1 else 0) := by
  simpa using exInnerE3 i j 1 1

theorem kform_exEtah_Q (x y : ExSpace) : kform exEtah (exQh x) y = kform exEtah x (exQh y) := by
  rw [exQh_apply, exQh_apply, kform, kform, exEtah_apply, exEtah_apply, exSmulE3, exSmulE3,
    exSmulE3]
  simp only [inner_add_right, inner_sub_right, exInnerE3b, inner_smul_right,
    EuclideanSpace.inner_single_right, exE3, PiLp.smul_apply, smul_eq_mul, map_mul]
  simp

theorem kform_exEtah_symm (x y : ExSpace) : kform exEtah x y = star (kform exEtah y x) := by
  rw [kform, kform, exEtah_apply, exEtah_apply]
  simp only [inner_add_right, inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right,
    exE3, map_one, map_mul, map_sub, map_add, star_add, star_sub, star_mul, star_one]
  have h2 : ∀ z : ℂ, star ((starRingEnd ℂ) z) = z := fun z => star_star z
  have h3 : ∀ z : ℂ, (starRingEnd ℂ) z = star z := fun z => rfl
  simp only [h2, h3, star_star]
  ring

theorem exVh_idem (x : ExSpace) : exVh (exVh x) = exVh x := by
  rw [exVh_apply, exVh_apply, exSmulE3]
  simp

theorem exQh_Vh (x : ExSpace) : exQh (exVh x) = 0 := by
  rw [exVh_apply, exQh_apply, exSmulE3]
  simp

noncomputable def exQuartet3 : BrstQuartet exQh where
  bGhost := exBh
  physProj := exVh
  physProj_idem := exVh_idem
  Q_physProj := exQh_Vh
  quartet_anticomm := quartet_pt

theorem exNotPhysicalPositivity : ¬ PhysicalPositivity exQh exEtah := by
  intro h
  have hx : (exE3 2 : ExSpace) ∈ closed exQh := by
    show exQh (exE3 2) = 0
    rw [exQh_apply, exE3, exOfLpSingle]
    simp
  have hval := h.1 (exE3 2) hx
  have hneg : (kform exEtah (exE3 2) (exE3 2)).re = -1 := by
    rw [kform, exEtah_apply]
    simp only [exE3, inner_add_right, inner_sub_right, inner_smul_right,
      EuclideanSpace.inner_single_right, exOfLpSingle]
    simp
  rw [hneg] at hval
  norm_num at hval


end

end BookProof.SmQuartet
