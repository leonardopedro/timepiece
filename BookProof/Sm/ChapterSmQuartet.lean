/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import BookProof.Sm.ChapterSmBrstQuotient
import BookProof.Sm.ChapterSmBrstGhost

/-!
# The Kugo–Ojima quartet and physical positivity

`SmBrstQuotient` left the physical half of P5 as a **named input**: `PhysicalPositivity Q η`, the
statement that the charge form is non-negative on the closed space with radical exactly the gauge
orbit.  This module proves it from quartet data, which is the classical Kugo–Ojima mechanism.

## 1. The quartet

`BrstQuartet Q` is the b-ghost `P` together with the physical projector `V`:

`Q P + P Q = 1 - V`,   and   `V`'s range lies in `ker Q`.

That is the algebraic residue of the Hodge decomposition `x = Q(Px) + P(Qx) + Vx` of a BRST
complex with a ghost pair: `P` lowers the ghost number, `V` is the harmonic (physical) projection.
No positivity of `V`, and no definiteness of `η`, is assumed.

## 2. What the quartet forces

* **`V` annihilates the exact space** (`quartet_physProj_comp_Q`): applying the charge to the
  decomposition of `Q y` and using nilpotency gives `Q (P (Q y)) = Q y`, hence `V (Q y) = 0`.  So
  `V` kills the gauge orbit even though only `V`'s *range* was assumed closed.
* **Every closed vector splits** (`quartet_decompose`): `x = Q (P x) + V x` for `x ∈ ker Q`.  The
  `P (Q x)` term drops out precisely on the closed space.
* **The charge form sees only the physical part** (`kform_quartet_reduce`):
  `⟨x, y⟩_η = ⟨V x, V y⟩_η` for closed `x, y`.  The three discarded terms are ghost-null: `Q (P x)`
  is exact and `V y` is closed, so they pair to zero (`kform_ghost_null`,
  `kform_ghost_null_right`).
* **Parity composes** (`kform_quartet_reduce_sectors`): if the involution preserves `V`, then the
  reduced form still vanishes across the parity sectors — so a quartet attack can be mounted
  sector by sector.

## 3. Positivity

`physicalPositivity_of_quartet` discharges §46's named input: if the charge form is the ambient
inner product **on the physical subspace** (`kform η (V x) (V x) = ⟪V x, V x⟫`), then on the closed
space the form is `‖V x‖²` and its radical is exactly the gauge orbit:

`PhysicalPositivity Q η`   (`physicalPositivity_of_quartet`).

`physicalPositivity_of_quartet_sectors` records the same conclusion in the parity shape, together
with the cross-sector vanishing, so the sector formulation is not a weakening.

## Boundary

The quartet is **data**, not a construction: this module does not produce `P` and `V` for the
Standard Model's BRST charge, so the SM's own `PhysicalPositivity` is still open at the level of
exhibiting its quartet.  What changes is the logical status of the condition: it is now a *theorem*
of quartet data rather than an unexplained input, and what remains is the model's `P` and `V` —
the same data §46's boundary note asked for.  `isBrst_of_mul_eq_zero` connects §46's predicate to
the endomorphism form in which the model supplies its charge (`smBrstCharge_nilpotent`), so only
the quartet itself is missing.

`exQuartet'`/`exPhysicalPositivity` instantiate the bundle on `ℂ³` in the only way a
**definite** metric allows: a nilpotent self-adjoint charge vanishes, so the quartet is
`Q = 0`, `P = 0`, `V = 1`, the closed space is everything, the form is `‖x‖²` and its radical
`{0}` is the gauge orbit.  The cohomology is then the whole space (`exE2_not_exact`: a unit vector
is closed but not exact).  That is a consistency check rather than a model of ghost cancellation —
a *non-trivial* quartet needs the indefinite metric of §46, and the `2 ⊕ 1` Krein instance is not
built here.

Everything here is `sorry`-free.
-/

namespace BookProof.SmQuartet

open BookProof.SmBrstQuotient
open BookProof.SmPhysicalReduction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## 1. The quartet bundle -/

/-- **A Kugo–Ojima quartet**: the b-ghost `P` and the physical projector `V`, with
`Q P + P Q = 1 - V` and `V`'s range inside the closed space. -/
structure BrstQuartet (Q : H →ₗ[ℂ] H) where
  /-- The b-ghost: it lowers the ghost number. -/
  P : H →ₗ[ℂ] H
  /-- The physical (harmonic) projector. -/
  V : H →ₗ[ℂ] H
  /-- The Hodge decomposition `Q P + P Q = 1 - V`. -/
  quartet : Q ∘ₗ P + P ∘ₗ Q = LinearMap.id - V
  /-- The physical projector lands in the closed space. -/
  phys_range : ∀ x : H, V x ∈ closed Q

/-- `Q² = 0` read pointwise. -/
theorem apply_apply_eq_zero {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) (z : H) : Q (Q z) = 0 := by
  have h := congrFun (congrArg DFunLike.coe hQ) z
  simpa [LinearMap.comp_apply, LinearMap.zero_apply] using h

/-- **Applying the charge to the decomposition splits off the b-ghost**: `Q P Q = Q`.  This is
`Q` times the quartet identity, with `Q² = 0` on the left and `Q V = 0` on the right. -/
theorem quartet_QPQ {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) (D : BrstQuartet Q) :
    Q ∘ₗ D.P ∘ₗ Q = Q := by
  ext y
  have hid := congrFun (congrArg DFunLike.coe D.quartet) y
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply] at hid
  have h := congrArg Q hid
  simp only [map_add, map_sub] at h
  rw [apply_apply_eq_zero hQ, D.phys_range y] at h
  simpa using h

/-- **The physical projector annihilates the gauge orbit**: `V Q = 0`.  Only `V`'s range being
closed was assumed; that `V` kills exact vectors is forced by nilpotency. -/
theorem quartet_physProj_comp_Q {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) (D : BrstQuartet Q) :
    D.V ∘ₗ Q = 0 := by
  ext y
  have hP := congrFun (congrArg DFunLike.coe (quartet_QPQ hQ D)) y
  simp only [LinearMap.comp_apply] at hP
  have hid := congrFun (congrArg DFunLike.coe D.quartet) (Q y)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply] at hid
  rw [apply_apply_eq_zero hQ, map_zero, hP, add_zero] at hid
  have h2 : Q y - D.V (Q y) = Q y := hid.symm
  have h3 : Q y - D.V (Q y) = Q y - 0 := by rw [h2, sub_zero]
  simpa using (sub_right_inj (a := Q y)).mp h3

/-- **Every closed vector splits as exact plus physical**: `x = Q (P x) + V x`. -/
theorem quartet_decompose {Q : H →ₗ[ℂ] H} (D : BrstQuartet Q) {x : H}
    (hx : x ∈ closed Q) : x = Q (D.P x) + D.V x := by
  have hid := congrFun (congrArg DFunLike.coe D.quartet) x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply] at hid
  rw [show Q x = 0 from hx, map_zero, add_zero] at hid
  rw [hid]
  abel

/-! ## 2. The charge form sees only the physical part -/

/-- **Quartet reduction of the charge form**: on the closed space,
`⟨x, y⟩_η = ⟨V x, V y⟩_η`.  The exact parts are ghost-null against the closed space in the first
slot, and the closed part is ghost-null against the exact part in the second. -/
theorem kform_quartet_reduce {Q η : H →ₗ[ℂ] H} (hQ : IsBrst Q) (D : BrstQuartet Q)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    {x y : H} (hx : x ∈ closed Q) (hy : y ∈ closed Q) :
    kform η x y = kform η (D.V x) (D.V y) := by
  conv_lhs =>
    rw [quartet_decompose D hx]
    rw [quartet_decompose D hy]
  rw [kform_add_left, kform_add_right, kform_add_right]
  have h1 : kform η (Q (D.P x)) (Q (D.P y)) = 0 :=
    kform_ghost_null hKrein (D.P x) (apply_apply_eq_zero hQ (D.P y))
  have h2 : kform η (Q (D.P x)) (D.V y) = 0 :=
    kform_ghost_null hKrein (D.P x) (D.phys_range y)
  have h3 : kform η (D.V x) (Q (D.P y)) = 0 :=
    kform_ghost_null_right hKrein hSymm (D.phys_range x) (D.P y)
  rw [h1, h2, h3]
  ring

/-- **The reduced form still vanishes across the parity sectors**, so a quartet reduction can be
read sector by sector. -/
theorem kform_quartet_reduce_sectors {Q η U : H →ₗ[ℂ] H} (hQ : IsBrst Q) (D : BrstQuartet Q)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η) (hVU : D.V ∘ₗ U = U ∘ₗ D.V)
    {x y : H} (hx : x ∈ closed Q) (hy : y ∈ closed Q)
    (ha : x ∈ evenSpace U) (hb : y ∈ oddSpace U) : kform η x y = 0 := by
  rw [kform_quartet_reduce hQ D hKrein hSymm hx hy]
  have hVUapply : ∀ z : H, D.V (U z) = U (D.V z) := fun z => by
    have h := congrFun (congrArg DFunLike.coe hVU) z
    simpa [LinearMap.comp_apply] using h
  have hVe : D.V x ∈ evenSpace U := by
    rw [mem_evenSpace_iff] at ha ⊢
    rw [← hVUapply x, ha]
  have hVo : D.V y ∈ oddSpace U := by
    rw [mem_oddSpace_iff] at hb ⊢
    rw [← hVUapply y, hb, map_neg]
  exact kform_eq_zero_of_mem_even_of_mem_odd hU hUnorm hηU hVe hVo

/-! ## 3. Positivity -/

/-- The real part of the self-pairing is the squared norm: `(⟪y, y⟫).re = ‖y‖²`. -/
theorem inner_self_re_eq_norm_sq (y : H) : (inner ℂ y y).re = ‖y‖ ^ 2 := by
  have hpow : inner ℂ y y = (‖y‖ : ℂ) * (‖y‖ : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, sq]
    rfl
  rw [hpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Kugo–Ojima positivity from a quartet.**  If the charge form agrees with the ambient inner
product on the physical subspace, then on the closed space the form is `‖V x‖²`, whose radical is
the gauge orbit — so §46's named input `PhysicalPositivity Q η` is a theorem of quartet data. -/
theorem physicalPositivity_of_quartet {Q η : H →ₗ[ℂ] H} (hQ : IsBrst Q) (D : BrstQuartet Q)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    (hVphys : ∀ x : H, kform η (D.V x) (D.V x) = inner ℂ (D.V x) (D.V x)) :
    PhysicalPositivity Q η := by
  have hred : ∀ {x : H}, x ∈ closed Q → kform η x x = inner ℂ (D.V x) (D.V x) := by
    intro x hx
    rw [kform_quartet_reduce hQ D hKrein hSymm hx hx, hVphys]
  constructor
  · intro x hx
    rw [hred hx, inner_self_re_eq_norm_sq]
    positivity
  · intro x hx hzero
    have hnorm : ‖D.V x‖ = 0 := by
      rw [hred hx, inner_self_re_eq_norm_sq] at hzero
      exact pow_eq_zero_iff two_ne_zero |>.1 hzero
    have hV : D.V x = 0 := norm_eq_zero.mp hnorm
    have hdec := quartet_decompose D hx
    have hQx : Q (D.P x) = x := by
      conv_rhs => rw [hdec, hV, add_zero]
    rw [BookProof.SmBrstQuotient.gauge, LinearMap.mem_range]
    exact ⟨D.P x, hQx⟩

/-- **The sector form of the theorem**: a quartet gives the whole condition, its two sector
restrictions, and the cross-sector vanishing — so the sector formulation is not a weakening. -/
theorem physicalPositivity_of_quartet_sectors {Q η U : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (D : BrstQuartet Q) (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    (hVphys : ∀ x : H, kform η (D.V x) (D.V x) = inner ℂ (D.V x) (D.V x))
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η) (hVU : D.V ∘ₗ U = U ∘ₗ D.V) :
    PhysicalPositivity Q η ∧
      (∀ x : H, x ∈ closed Q → x ∈ evenSpace U → 0 ≤ (kform η x x).re) ∧
        (∀ x : H, x ∈ closed Q → x ∈ oddSpace U → 0 ≤ (kform η x x).re) ∧
          (∀ x y : H, x ∈ closed Q → y ∈ closed Q → x ∈ evenSpace U → y ∈ oddSpace U →
            kform η x y = 0) := by
  have hpos := physicalPositivity_of_quartet hQ D hKrein hSymm hVphys
  exact ⟨hpos, fun x hx _ => hpos.1 x hx, fun x hx _ => hpos.1 x hx,
    fun x y hx hy ha hb => kform_quartet_reduce_sectors hQ D hKrein hSymm hU hUnorm hηU hVU
      hx hy ha hb⟩

/-! ## 4. Reading a nilpotent endomorphism as a BRST operator -/

/-- **A nilpotent endomorphism is a BRST operator**: `Ω * Ω = 0` in the endomorphism ring is
§46's `IsBrst Ω`.  This is the form in which the model supplies its charge — the ghost module's
`smBrstCharge_nilpotent` is an input of exactly this shape, so the quartet machinery applies to the
Standard-Model charge as soon as a quartet `(P, V)` for it exists. -/
theorem isBrst_of_mul_eq_zero (Q : Module.End ℂ H) (h : Q * Q = 0) :
    IsBrst (Q : H →ₗ[ℂ] H) := by
  refine LinearMap.ext fun x => ?_
  have hx : Q (Q x) = 0 := by
    have := congrArg (fun e : Module.End ℂ H => e x) h
    simpa [Module.End.mul_apply] using this
  simpa [IsBrst, LinearMap.comp_apply] using hx

end

/-! ## 5. An instance -/

/-- The carrier of the instance: `ℂ³` with its standard inner product.  The example is
deliberately one where the quartet is forced: in a definite metric a nilpotent self-adjoint charge
vanishes, so `Q = 0`, `P = 0`, `V = 1` is the only quartet with `η = 1`. -/
abbrev ExH : Type := EuclideanSpace ℂ (Fin 3)

/-- **The example's quartet**: the trivial nilpotent charge `Q = 0`, the b-ghost `P = 0` and the
physical projector `V = 1`.  The decomposition `Q P + P Q = 1 - V` holds, `V`'s range (everything)
is closed, and the cohomology is the whole space — which is exactly what a definite-metric quartet
must look like. -/
noncomputable def exQuartet' : BrstQuartet (0 : ExH →ₗ[ℂ] ExH) where
  P := 0
  V := 1
  quartet := by
    ext x
    simp
  phys_range := by
    simp [closed]

/-- **`PhysicalPositivity` holds for the example**: the charge form on the closed space is
`‖x‖²`, whose radical `{0}` is the gauge orbit of the zero charge. -/
theorem exPhysicalPositivity :
    PhysicalPositivity (0 : ExH →ₗ[ℂ] ExH) (LinearMap.id : ExH →ₗ[ℂ] ExH) :=
  physicalPositivity_of_quartet (by simp [IsBrst]) exQuartet'
    (by simp [kform]) (by simp [kform]) (by simp [kform])

/-- The cohomology of the example is non-trivial: a unit vector of the third direction is closed
but not exact. -/
theorem exE2_not_exact :
    EuclideanSpace.single (2 : Fin 3) (1 : ℂ) ∉ gauge (0 : ExH →ₗ[ℂ] ExH) := by
  rw [BookProof.SmBrstQuotient.gauge, LinearMap.mem_range]
  rintro ⟨z, hz⟩
  rw [LinearMap.zero_apply] at hz
  have hne : EuclideanSpace.single (2 : Fin 3) (1 : ℂ) ≠ 0 := by
    intro h
    have := EuclideanSpace.norm_single (2 : Fin 3) (1 : ℂ)
    rw [h, norm_zero] at this
    norm_num at this
  exact hne hz.symm

end BookProof.SmQuartet
