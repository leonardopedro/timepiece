/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import BookProof.Sm.ChapterSmPhysicalReductionEsa

/-!
# The BRST quotient and the parity split

§44 reduced the matter normal form's closure to its parity sectors.  This module
builds the algebra that P5's *physical* half needs on top of that split: the
cohomology of a nilpotent charge, the descent of the charge form to it, and the
parity grading of the result.

The setup is deliberately the indefinite-metric one, because that is what a BRST
charge actually requires.  In a positive-definite space a nilpotent self-adjoint
charge vanishes, so the naive route — quotient by the exact space and inherit the
ambient inner product — cannot be the physical construction.  What the physical
construction uses is a **charge form** `kform η x y = ⟪x, ηy⟫`, and the three
facts proved here are the classical ones:

* **Nilpotency puts the exact space inside the closed space** (`gauge_le_ker`).
* **Ghost nullity**: if the charge is symmetric for the charge form,
  `kform η (Qx) y = kform η x (Qy)`, then every exact vector is null *for the
  closed space* (`kform_ghost_null`).  This is what makes the quotient form
  well defined, and `kform_well_defined` proves exactly that: representatives
  modulo the gauge orbit give the same charge form.
* **Parity descent**: a unitary involution commuting with the charge preserves
  both the closed space and the gauge orbit (`U_mem_closed`, `U_mem_gauge`), the
  charge form splits over the two sectors (`kform_quadForm_split`, because the
  sectors are orthogonal for the charge form as well), and therefore
  non-negativity of the charge form is a *sector-by-sector* statement
  (`kform_quadForm_nonneg`).

**What is not built, and must not be read into this.** The named input
`PhysicalPositivity` — non-negativity of the charge form on the closed space with
radical exactly the gauge orbit — is *not* proved, neither here nor anywhere in
the corpus. It is the Kugo–Ojima no-ghost condition, and proving it requires the
quartet structure of the actual BRST charge of the matter model, which has not
been constructed. Nothing here produces a physical inner product for the SM; it
produces the reduction, the well-definedness, and the parity grading, so that a
future quartet construction has only the sector conditions to verify.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmBrstQuotient

open BookProof.SmPhysicalReduction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## 1. Nilpotency, the closed space and the gauge orbit -/

/-- **The charge is nilpotent**, `Q² = 0`. -/
def IsBrst (Q : H →ₗ[ℂ] H) : Prop := Q ∘ₗ Q = 0

/-- The **gauge orbit**: the exact space `im Q`, whose classes are quotiented out. -/
def gauge (Q : H →ₗ[ℂ] H) : Submodule ℂ H := LinearMap.range Q

/-- The **closed space** `ker Q`. -/
def closed (Q : H →ₗ[ℂ] H) : Submodule ℂ H := LinearMap.ker Q

/-- **Nilpotency puts the gauge orbit inside the closed space**: an exact vector is closed. -/
theorem gauge_le_ker {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) : gauge Q ≤ closed Q := by
  rintro _ ⟨z, rfl⟩
  rw [closed, LinearMap.mem_ker]
  have h := congrFun (congrArg DFunLike.coe hQ) z
  simpa [LinearMap.comp_apply, LinearMap.zero_apply] using h

/-- The same statement for an element of the gauge orbit. -/
theorem mem_closed_of_mem_gauge {Q : H →ₗ[ℂ] H} (hQ : IsBrst Q) {x : H}
    (hx : x ∈ gauge Q) : x ∈ closed Q :=
  gauge_le_ker hQ hx

/-! ## 2. The charge form and ghost nullity -/

/-- The **charge form** `⟨x, y⟩_η = ⟪x, ηy⟫` attached to a metric operator `η`.  For `η` a unitary
involution it is the Krein form of the indefinite Fock space; for `η = 1` it is the ambient inner
product. -/
def kform (η : H →ₗ[ℂ] H) (x y : H) : ℂ := inner ℂ x (η y)

theorem kform_add_right (η : H →ₗ[ℂ] H) (x y z : H) :
    kform η x (y + z) = kform η x y + kform η x z := by
  rw [kform, kform, kform, map_add, inner_add_right]

theorem kform_smul_right (η : H →ₗ[ℂ] H) (c : ℂ) (x y : H) :
    kform η x (c • y) = c * kform η x y := by
  rw [kform, kform, map_smul, inner_smul_right]

theorem kform_add_left (η : H →ₗ[ℂ] H) (x y z : H) :
    kform η (x + y) z = kform η x z + kform η y z := by
  rw [kform, kform, kform, inner_add_left]

theorem kform_zero_right (η : H →ₗ[ℂ] H) (x : H) : kform η x 0 = 0 := by
  rw [kform, map_zero, inner_zero_right]

/-- **Ghost nullity**: if the charge is symmetric for the charge form, `kform η (Qx) y = kform η x
(Qy)`, then every exact vector pairs to zero with every closed vector — in the first slot.  This is
the classical statement that a BRST-exact state has no overlap with a physical state. -/
theorem kform_ghost_null {Q : H →ₗ[ℂ] H} {η : H →ₗ[ℂ] H}
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y)) (z : H) {y : H}
    (hy : y ∈ closed Q) : kform η (Q z) y = 0 := by
  have hy' : Q y = 0 := hy
  rw [hKrein, hy', kform_zero_right]

/-- The same in the second slot, from the symmetry of the charge form. -/
theorem kform_ghost_null_right {Q : H →ₗ[ℂ] H} {η : H →ₗ[ℂ] H}
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x)) {x : H}
    (hx : x ∈ closed Q) (z : H) : kform η x (Q z) = 0 := by
  rw [hSymm, kform_ghost_null hKrein z hx]; simp

/-- **The quotient form is well defined**: two representatives of the same class — modulo the gauge
orbit, inside the closed space — give the same charge form.  This is what lets the physical form be
defined on the cohomology rather than on the closed space. -/
theorem kform_well_defined {Q : H →ₗ[ℂ] H} {η : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hSymm : ∀ x y : H, kform η x y = star (kform η y x))
    {x x' y y' : H} (hx : x ∈ closed Q) (hy : y ∈ closed Q)
    (h1 : x - x' ∈ gauge Q) (h2 : y - y' ∈ gauge Q) :
    kform η x y = kform η x' y' := by
  obtain ⟨z, hz⟩ := h1
  obtain ⟨w, hw⟩ := h2
  have hx1 : x = x' + Q z := by rw [hz]; abel
  have hy1 : y = y' + Q w := by rw [hw]; abel
  have hzw : Q w ∈ closed Q := gauge_le_ker hQ ⟨w, rfl⟩
  have hx'c : x' ∈ closed Q := by
    have h : x' = x - Q z := by rw [hx1]; abel
    rw [h]
    exact (closed Q).sub_mem hx (gauge_le_ker hQ ⟨z, rfl⟩)
  have hy'c : y' ∈ closed Q := by
    have h : y' = y - Q w := by rw [hy1]; abel
    rw [h]
    exact (closed Q).sub_mem hy hzw
  rw [hx1, hy1, kform_add_left, kform_add_right, kform_add_right,
    kform_ghost_null_right hKrein hSymm hx'c w, kform_ghost_null hKrein z hy'c,
    kform_ghost_null hKrein z hzw]
  ring

/-! ## 3. Parity descent -/

/-- **A charge commuting with the involution preserves the closed space.** -/
theorem U_mem_closed {Q U : H →ₗ[ℂ] H} (hUQ : U ∘ₗ Q = Q ∘ₗ U) {x : H}
    (hx : x ∈ closed Q) : U x ∈ closed Q := by
  rw [closed, LinearMap.mem_ker] at hx ⊢
  have h := congrFun (congrArg DFunLike.coe hUQ) x
  simp only [LinearMap.comp_apply] at h
  rw [← h, hx, map_zero]

/-- **A charge commuting with the involution preserves the gauge orbit.** -/
theorem U_mem_gauge {Q U : H →ₗ[ℂ] H} (hUQ : U ∘ₗ Q = Q ∘ₗ U) {x : H}
    (hx : x ∈ gauge Q) : U x ∈ gauge Q := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨U z, ?_⟩
  have h := congrFun (congrArg DFunLike.coe hUQ) z
  simpa [LinearMap.comp_apply] using h.symm

/-- **The charge form respects the parity sectors**: if the metric operator commutes with the
involution, it maps each sector into itself, so the sectors stay orthogonal for the charge form
too. -/
theorem kform_eq_zero_of_mem_even_of_mem_odd {U η : H →ₗ[ℂ] H}
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η) {a b : H}
    (ha : a ∈ evenSpace U) (hb : b ∈ oddSpace U) : kform η a b = 0 := by
  have hbη : η b ∈ oddSpace U := by
    rw [mem_oddSpace_iff] at hb ⊢
    have h := congrFun (congrArg DFunLike.coe hηU) b
    simp only [LinearMap.comp_apply] at h
    rw [← h, hb, map_neg]
  exact inner_eq_zero_of_mem_even_of_mem_odd hU hUnorm ha hbη

/-- The same vanishing with the odd vector first. -/
theorem kform_eq_zero_of_mem_odd_of_mem_even {U η : H →ₗ[ℂ] H}
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η) {a b : H}
    (ha : a ∈ oddSpace U) (hb : b ∈ evenSpace U) : kform η a b = 0 := by
  have hbη : η b ∈ evenSpace U := by
    rw [mem_evenSpace_iff] at hb ⊢
    have h := congrFun (congrArg DFunLike.coe hηU) b
    simp only [LinearMap.comp_apply] at h
    rw [← h, hb]
  exact inner_eq_zero_of_mem_odd_of_mem_even hU hUnorm ha hbη

/-- **The quadratic charge form splits over the parity sectors.**  Since the cross terms vanish, the
form on a closed vector is the sum of the forms on its two parts — which is exactly what makes
non-negativity a per-sector question. -/
theorem kform_quadForm_split {U η : H →ₗ[ℂ] H}
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η) (x : H) :
    (kform η x x).re
      = (kform η (evenPart U x) (evenPart U x)).re
        + (kform η (oddPart U x) (oddPart U x)).re := by
  have hx : evenPart U x + oddPart U x = x := evenPart_add_oddPart x
  have hev : evenPart U x ∈ evenSpace U := evenPart_mem hU x
  have hod : oddPart U x ∈ oddSpace U := oddPart_mem hU x
  have hcross1 : kform η (evenPart U x) (oddPart U x) = 0 :=
    kform_eq_zero_of_mem_even_of_mem_odd hU hUnorm hηU hev hod
  have hcross2 : kform η (oddPart U x) (evenPart U x) = 0 :=
    kform_eq_zero_of_mem_odd_of_mem_even hU hUnorm hηU hod hev
  have h := hx
  conv_lhs => rw [← h]
  rw [kform_add_left, kform_add_right, kform_add_right, hcross1, hcross2]
  simp

/-- **Kugo–Ojima positivity is a sector-by-sector statement**: if the charge form is non-negative on
the even and on the odd part of the closed space, it is non-negative on the closed space, and hence
on the physical quotient, whose two sectors are mutually orthogonal for it. -/
theorem kform_quadForm_nonneg {Q U η : H →ₗ[ℂ] H}
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η) (hUQ : U ∘ₗ Q = Q ∘ₗ U)
    (hev : ∀ x : H, x ∈ closed Q → x ∈ evenSpace U → 0 ≤ (kform η x x).re)
    (hod : ∀ x : H, x ∈ closed Q → x ∈ oddSpace U → 0 ≤ (kform η x x).re)
    {x : H} (hx : x ∈ closed Q) : 0 ≤ (kform η x x).re := by
  have hDU : ∀ y ∈ closed Q, U y ∈ closed Q := fun y hy => U_mem_closed hUQ hy
  have hevC : evenPart U x ∈ closed Q := evenPart_mem_of_mem (closed Q) hDU hx
  have hodC : oddPart U x ∈ closed Q := oddPart_mem_of_mem (closed Q) hDU hx
  rw [kform_quadForm_split hU hUnorm hηU x]
  exact add_nonneg (hev _ hevC (evenPart_mem hU x)) (hod _ hodC (oddPart_mem hU x))

/-! ## 4. The named positivity input -/

/-- **The Kugo–Ojima positivity condition**, as a named input: the charge form is non-negative on
the closed space, and its radical there is exactly the gauge orbit.  Together with
`kform_well_defined` this is precisely the statement that the descended form is a genuine
*inner product* on the cohomology — derived from a quartet decomposition in §47 rather than
assumed.

It is **not proved** here — nor anywhere in the corpus — for the matter model: it needs the quartet
structure of the model's BRST charge, which has not been constructed.  It is the input a physical
smoke test must discharge, sector by sector. -/
def PhysicalPositivity (Q η : H →ₗ[ℂ] H) : Prop :=
  (∀ x : H, x ∈ closed Q → 0 ≤ (kform η x x).re) ∧
    (∀ x : H, x ∈ closed Q → (kform η x x).re = 0 → x ∈ gauge Q)

/-- **Positivity on the two sectors gives the named input's first half.**  This is the only
direction that the parity split supplies for free: the cross terms vanish, so sector positivity
assembles. -/
theorem physicalPositivity_nonneg_of_sectors {Q U η : H →ₗ[ℂ] H}
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η) (hUQ : U ∘ₗ Q = Q ∘ₗ U)
    (hev : ∀ x : H, x ∈ closed Q → x ∈ evenSpace U → 0 ≤ (kform η x x).re)
    (hod : ∀ x : H, x ∈ closed Q → x ∈ oddSpace U → 0 ≤ (kform η x x).re) :
    ∀ x : H, x ∈ closed Q → 0 ≤ (kform η x x).re :=
  fun x hx => kform_quadForm_nonneg (x := x) hU hUnorm hηU hUQ hev hod hx

/-! ## 5. Finite-window dimension bookkeeping

`unfer`'s finite `N <= 2` BRST window is a three-term graded complex
`C0 <- C1 <- C2` with `Q1 * Q2 = 0`.  The block ranks are measured in Rust; this
section is the kernel-checked arithmetic that turns those measured block ranks
into the cohomology dimensions.  It does **not** construct the 1,419- or
11,067-dimensional matrices in Lean, and it does not identify the finite
quotient with the physical Krein quotient. -/

section FiniteWindow

variable {C0 C1 C2 : Type*}
variable [AddCommGroup C0] [Module ℂ C0] [FiniteDimensional ℂ C0]
variable [AddCommGroup C1] [Module ℂ C1] [FiniteDimensional ℂ C1]
variable [AddCommGroup C2] [Module ℂ C2] [FiniteDimensional ℂ C2]

/-- **Finite-window cohomology dimensions.**  For a three-term complex with
`q1 ∘ q2 = 0`, the dimensions of `ker q1 / im q2`, `ker q2`, and `coker q1` are
`d1 - r1 - r2`, `d2 - r2`, and `d0 - r1`.  `hcomplex` is the finite-window
`Q^2 = 0` hypothesis; `r1` and `r2` are the measured block ranks. -/
theorem finiteWindow_finrank
    (q1 : C1 →ₗ[ℂ] C0) (q2 : C2 →ₗ[ℂ] C1)
    (hcomplex : q1 ∘ₗ q2 = 0)
    (d0 d1 d2 r1 r2 : ℕ)
    (hC0 : Module.finrank ℂ C0 = d0)
    (hC1 : Module.finrank ℂ C1 = d1)
    (hC2 : Module.finrank ℂ C2 = d2)
    (hr1 : Module.finrank ℂ (LinearMap.range q1) = r1)
    (hr2 : Module.finrank ℂ (LinearMap.range q2) = r2) :
    Module.finrank ℂ (C0 ⧸ LinearMap.range q1) = d0 - r1 ∧
    Module.finrank ℂ
        ((LinearMap.ker q1) ⧸ (LinearMap.range q2).comap (LinearMap.ker q1).subtype)
      = d1 - r1 - r2 ∧
    Module.finrank ℂ (LinearMap.ker q2) = d2 - r2 := by
  have hle : LinearMap.range q2 ≤ LinearMap.ker q1 := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have h := congrFun (congrArg DFunLike.coe hcomplex) x
    simpa [LinearMap.comp_apply] using h
  have hker1 : Module.finrank ℂ (LinearMap.ker q1) = d1 - r1 := by
    have h := LinearMap.finrank_range_add_finrank_ker q1
    omega
  have hker2 : Module.finrank ℂ (LinearMap.ker q2) = d2 - r2 := by
    have h := LinearMap.finrank_range_add_finrank_ker q2
    omega
  let R2 : Submodule ℂ (LinearMap.ker q1) :=
    (LinearMap.range q2).comap (LinearMap.ker q1).subtype
  have hR2 : Module.finrank ℂ R2 = r2 := by
    have e := Submodule.comapSubtypeEquivOfLe hle
    exact e.finrank_eq.trans hr2
  have hquot1 : Module.finrank ℂ (C0 ⧸ LinearMap.range q1) = d0 - r1 := by
    have h := Submodule.finrank_quotient_add_finrank (LinearMap.range q1 : Submodule ℂ C0)
    omega
  have hquot2 : Module.finrank ℂ ((LinearMap.ker q1) ⧸ R2) = d1 - r1 - r2 := by
    have h := Submodule.finrank_quotient_add_finrank R2
    omega
  exact ⟨hquot1, hquot2, hker2⟩

/-- **The matter-extended finite window.**  The Rust artifact measures
`C0 = 1`, `C1 = 148`, `C2 = 10,918`, block ranks `r1 = 0` and `r2 = 138`.
The kernel-checked conclusion is `[1, 10, 10,780]`. -/
theorem finiteWindow_matter_finrank
    (q1 : C1 →ₗ[ℂ] C0) (q2 : C2 →ₗ[ℂ] C1)
    (hcomplex : q1 ∘ₗ q2 = 0)
    (hC0 : Module.finrank ℂ C0 = 1)
    (hC1 : Module.finrank ℂ C1 = 148)
    (hC2 : Module.finrank ℂ C2 = 10918)
    (hr1 : Module.finrank ℂ (LinearMap.range q1) = 0)
    (hr2 : Module.finrank ℂ (LinearMap.range q2) = 138) :
    Module.finrank ℂ (C0 ⧸ LinearMap.range q1) = 1 ∧
    Module.finrank ℂ
        ((LinearMap.ker q1) ⧸ (LinearMap.range q2).comap (LinearMap.ker q1).subtype)
      = 10 ∧
    Module.finrank ℂ (LinearMap.ker q2) = 10780 := by
  have h := finiteWindow_finrank q1 q2 hcomplex 1 148 10918 0 138 hC0 hC1 hC2 hr1 hr2
  simpa using h

/-- **The jet-inclusive finite window.**  The Rust artifact adds all 120
independent derivative-jet coordinates to the matter window, measuring
`C0 = 1`, `C1 = 268`, `C2 = 35,938`, block ranks `r1 = 0` and `r2 = 249`.
The kernel-checked conclusion is `[1, 19, 35,689]`.  The jet coordinates are
independent E1 fields, not constrained spatial derivatives, and this remains a
finite-window statement. -/
theorem finiteWindow_jet_finrank
    (q1 : C1 →ₗ[ℂ] C0) (q2 : C2 →ₗ[ℂ] C1)
    (hcomplex : q1 ∘ₗ q2 = 0)
    (hC0 : Module.finrank ℂ C0 = 1)
    (hC1 : Module.finrank ℂ C1 = 268)
    (hC2 : Module.finrank ℂ C2 = 35938)
    (hr1 : Module.finrank ℂ (LinearMap.range q1) = 0)
    (hr2 : Module.finrank ℂ (LinearMap.range q2) = 249) :
    Module.finrank ℂ (C0 ⧸ LinearMap.range q1) = 1 ∧
    Module.finrank ℂ
        ((LinearMap.ker q1) ⧸ (LinearMap.range q2).comap (LinearMap.ker q1).subtype)
      = 19 ∧
    Module.finrank ℂ (LinearMap.ker q2) = 35689 := by
  have h := finiteWindow_finrank q1 q2 hcomplex 1 268 35938 0 249 hC0 hC1 hC2 hr1 hr2
  simpa using h

end FiniteWindow

/-! ## 6. The jet-window block charge

The jet-inclusive window is the three-term complex
`C0 <- C1 <- C2` with dimensions `1/268/35,938`.  Written in degree order,
its total charge is the block matrix

`Q = [[0, q1, 0], [0, 0, q2], [0, 0, 0]]`.

This section formalizes the matrix identity `Q * Q = 0`: it is exactly the
condition `q1 * q2 = 0`, with no additional block conditions.  The concrete
entries and their measured `q1 * q2 = 0` residual remain in the Rust artifact;
this theorem does not construct the 36,207-state matrix. -/

section JetChargeMatrix

open Matrix

/-- The total charge matrix of the jet-inclusive finite window, in degree order
`C0, C1, C2` with dimensions `1, 268, 35,938`. -/
noncomputable def jetWindowCharge
    (q1 : Matrix (Fin 1) (Fin 268) ℂ)
    (q2 : Matrix (Fin 268) (Fin 35938) ℂ) :
    Matrix ((Fin 1 ⊕ Fin 268) ⊕ Fin 35938)
      ((Fin 1 ⊕ Fin 268) ⊕ Fin 35938) ℂ :=
  Matrix.fromBlocks (Matrix.fromBlocks 0 q1 0 0)
    (Matrix.fromRows 0 q2) 0 0

lemma fromBlocks_zero_q1_mul_fromRows
    (q1 : Matrix (Fin 1) (Fin 268) ℂ)
    (q2 : Matrix (Fin 268) (Fin 35938) ℂ) :
    (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℂ) q1
      (0 : Matrix (Fin 268) (Fin 1) ℂ) (0 : Matrix (Fin 268) (Fin 268) ℂ)) *
      (Matrix.fromRows (0 : Matrix (Fin 1) (Fin 35938) ℂ) q2) =
      Matrix.fromRows (q1 * q2) (0 : Matrix (Fin 268) (Fin 35938) ℂ) := by
  ext i j
  rcases i with i0 | i1 <;>
    simp [Matrix.mul_apply, Matrix.fromBlocks, Matrix.fromRows, Fintype.sum_sum_type]

/-- **The jet-window Q² = 0 matrix identity.**  The block total charge squares
to zero exactly when its degree-two-to-one block is annihilated by its
degree-one-to-zero block. -/
theorem jetWindowCharge_sq
    (q1 : Matrix (Fin 1) (Fin 268) ℂ)
    (q2 : Matrix (Fin 268) (Fin 35938) ℂ)
    (hcomplex : q1 * q2 = 0) :
    jetWindowCharge q1 q2 * jetWindowCharge q1 q2 = 0 := by
  ext i j
  rcases i with (i0 | i1) | i2 <;> rcases j with (j0 | j1) | j2 <;>
    simp [jetWindowCharge, Matrix.fromBlocks_multiply,
      fromBlocks_zero_q1_mul_fromRows, hcomplex]

end JetChargeMatrix

end

end BookProof.SmBrstQuotient
