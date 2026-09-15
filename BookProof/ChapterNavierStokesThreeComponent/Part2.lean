import Mathlib
import BookProof.ChapterNavierStokesSignedShift
import BookProof.ChapterNavierStokesThreeComponent.Part1

/-!
# The three coupled velocity components

The Navier–Stokes fiber analysis carried out in
`BookProof.ChapterNavierStokesAffineFiberEsa` and
`BookProof.ChapterNavierStokesAffineBlockEsa` carries **one** velocity
component: the fiber Hilbert space is `ℓ²(ℕ)`, the Hermite representation of a
single degree of freedom `u`, and the fiber field is the affine
`V(u) = κ u + c`.  The recorded boundary was the coupling of the three velocity
components.

This module removes it.  At one fiber the velocity is now the vector
`u = (u₁, u₂, u₃)`, the Hermite basis is indexed by `Vel = Fin 3 → ℕ`, the fiber
fields are the affine

`V_i(u) = ∑_k A_{ik} u_k + c_i`,

with `A` an **arbitrary real** `3 × 3` matrix (the negative velocity gradient at
the fiber, with no symmetry, positivity or sign assumption) and `c` an arbitrary
real vector, and the fiber Hamiltonian is

`H = ∑_i ½(π_i V_i + V_i π_i)`.

## The Hermite matrix of `H`

Writing `u_i = (a_i + a_i†)/√2` and `π_i = i(a_i† − a_i)/√2`, the terms are

* `A_{ii} ½(π_i u_i + u_i π_i) = (i A_{ii}/2)(a_i†² − a_i²)` — a `±2`-hopping in
  the coordinate `i`, amplitude `(A_{ii}/2)√((β_i+1)(β_i+2))`;
* for `i ≠ k`, `A_{ik} π_i u_k + A_{ki} π_k u_i = i S_{ik}(a_i†a_k† − a_i a_k)
  + i D_{ik}(a_i† a_k − a_i a_k†)` with `S = (A_{ik}+A_{ki})/2` and
  `D = (A_{ik}−A_{ki})/2` — a **double-raising** hopping `β ↦ β + e_i + e_k` of
  amplitude `S√((β_i+1)(β_k+1))` (the strain part) and a **number-conserving**
  hopping `β ↦ β + e_i − e_k` of amplitude `D√((β_i+1)β_k)` (the vorticity
  part);
* `c_i π_i = (i c_i/√2)(a_i† − a_i)` — a `±1`-hopping, amplitude
  `(c_i/√2)√(β_i+1)`.

The vorticity hopping has an amplitude that is *not* monotone along its shift,
and the strain rates and constants have arbitrary signs, so neither
`ShiftHamiltonian.ShiftData` nor its two-shift version applies.  The instrument
used here is `SignedShift.listH_essentiallySelfAdjointOn_core`, which needs
neither positivity nor monotonicity.

## What is proved

* `velH` — the coupled three-component fiber Hamiltonian on the maximal domain
  of the comparison symbol `N = μ(2|β| + 3) + 1` in `ℓ²(Vel)`;
* `velH_symmetricOn` — it is symmetric;
* `velH_essentiallySelfAdjointOn_core` — **the headline**: it is essentially
  self-adjoint on the finite-mode core of `ℓ²(Vel)`, for every real matrix `A`
  and every real vector `c`;
* `velH_coord_pair`, `velH_coord_rot`, `velH_coord_shear`, `velH_coord_diag` —
  the matrix entries: the coupling between distinct components really is
  present;
* `velH_not_bounded` — the operator is unbounded.

## Honest boundary

The setting is the abstract sequence space `ℓ²(Vel)` with the operator given by
its matrix in the Hermite basis of the fiber.  The canonical reading of that
matrix — the ladder pairs, the canonical commutation relations, and the identity
`∑_i ½(π_i V_i + V_i π_i) = velH A c` — is supplied by
`BookProof.ChapterNavierStokesCanonicalVector`; the unitary transport of that
picture to `L²(du₁du₂du₃)` is not built here, and nothing here claims global
regularity for the classical Navier–Stokes equation.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace ThreeComponent

open LpNat FarisLavine IkebeKato ShiftHamiltonian SignedShift

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
/-! ## The twenty-four hopping terms -/

/-- The diagonal (self-advection) hop of the component `i`. -/
noncomputable def diagHop (i : Fin 3) : SignedHop Vel (velSym (velMu A c)) where
  shift := shDiag i
  amp := ampDiag A i
  K := velMu A c
  step := 4 * velMu A c
  shift_injective := shDiag_injective i
  K_nonneg := velMu_nonneg A c
  step_nonneg := by have := velMu_nonneg A c; linarith
  sym_ge_one := velSym_ge_one (velMu_nonneg A c)
  abs_amp_le := abs_ampDiag_le A c i
  sym_step := fun β => by
    simp only [velSym, total_shDiag]
    push_cast
    ring

/-- The strain (symmetric cross) hop of the ordered pair `(i, k)`. -/
noncomputable def pairHop (i k : Fin 3) : SignedHop Vel (velSym (velMu A c)) where
  shift := shPair i k
  amp := ampPair A i k
  K := velMu A c
  step := 4 * velMu A c
  shift_injective := shPair_injective i k
  K_nonneg := velMu_nonneg A c
  step_nonneg := by have := velMu_nonneg A c; linarith
  sym_ge_one := velSym_ge_one (velMu_nonneg A c)
  abs_amp_le := abs_ampPair_le A c i k
  sym_step := fun β => by
    simp only [velSym, total_shPair]
    push_cast
    ring

/-- The vorticity (antisymmetric cross) hop of the ordered pair `(i, k)`: the
number-conserving one, whose amplitude is not monotone along its shift. -/
noncomputable def rotHop (i k : Fin 3) : SignedHop Vel (velSym (velMu A c)) where
  shift := shRot i k
  amp := ampRot A i k
  K := velMu A c
  step := 0
  shift_injective := shRot_injective i k
  K_nonneg := velMu_nonneg A c
  step_nonneg := le_rfl
  sym_ge_one := velSym_ge_one (velMu_nonneg A c)
  abs_amp_le := abs_ampRot_le A c i k
  sym_step := fun β => by
    simp only [velSym, total_shRot]
    ring

/-- The `±1`-hop of the constant part of the component `i`. -/
noncomputable def shearHop (i : Fin 3) : SignedHop Vel (velSym (velMu A c)) where
  shift := shShear i
  amp := ampShear c i
  K := velMu A c
  step := 2 * velMu A c
  shift_injective := shShear_injective i
  K_nonneg := velMu_nonneg A c
  step_nonneg := by have := velMu_nonneg A c; linarith
  sym_ge_one := velSym_ge_one (velMu_nonneg A c)
  abs_amp_le := abs_ampShear_le A c i
  sym_step := fun β => by
    simp only [velSym, total_shShear]
    push_cast
    ring

/-- The full family of hopping terms of the coupled three-component fiber
Hamiltonian: for each component a diagonal and a shear hop, and for each ordered
pair of components a strain and a vorticity hop. -/
noncomputable def hopList : List (SignedHop Vel (velSym (velMu A c))) :=
  (List.finRange 3).flatMap fun i =>
    diagHop A c i :: shearHop A c i ::
      (List.finRange 3).flatMap fun k => [pairHop A c i k, rotHop A c i k]

/-! ## The coupled three-component fiber Hamiltonian -/

/-- **The coupled three-component fiber Hamiltonian**
`H = ∑_i ½(π_i V_i + V_i π_i)` with `V_i(u) = ∑_k A_{ik} u_k + c_i`, written in
the Hermite basis of the three modes, on the maximal domain of the comparison
symbol. -/
noncomputable def velH : maxDom (velSym (velMu A c)) →ₗ[ℂ] L2I Vel :=
  SignedShift.listH (hopList A c)

theorem velH_symmetricOn : SymmetricOn (maxDom (velSym (velMu A c))) (velH A c) :=
  SignedShift.listH_symmetricOn _

/-- **The three coupled velocity components are essentially self-adjoint.**  For
every real `3 × 3` matrix `A` — no symmetry, no positivity, no sign condition —
and every real vector `c`, the coupled fiber Hamiltonian is essentially
self-adjoint on the finite-mode core of `ℓ²(Vel)`. -/
theorem velH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes Vel)
      ((velH A c).comp (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))))) :=
  SignedShift.listH_essentiallySelfAdjointOn_core _ (velSym_ge_one (velMu_nonneg A c))

/-! ## Matrix entries: the coupling really is present -/

/-- The Hermite basis vector `e_β` of the three-component fiber, as an element
of the maximal domain of the comparison operator. -/
noncomputable def velState (β : Vel) : maxDom (velSym (velMu A c)) :=
  ⟨lp.single 2 β 1, finiteModes_le_maxDom _ (lpSingle_mem_lpFiniteModes _ _)⟩

theorem velState_coe (β α : Vel) :
    ((velState A c β : L2I Vel) : Vel → ℂ) α = if α = β then 1 else 0 := by
  simp [velState, lp.single_apply, Pi.single_apply, eq_comm]

theorem norm_velState (β : Vel) : ‖(velState A c β : L2I Vel)‖ = 1 := by
  simp [velState]

/-- The coordinates of the coupled Hamiltonian on a Hermite basis vector: each
member of the family contributes its amplitude at the coordinate it hops to, and
minus its amplitude at the coordinate it hops from. -/
theorem velH_coe_single (β γ : Vel) :
    ((velH A c (velState A c β) : L2I Vel) : Vel → ℂ) γ
      = ((hopList A c).map (fun S => Complex.I *
          ((if γ = S.shift β then (S.amp β : ℂ) else 0)
            - (if S.shift γ = β then (S.amp γ : ℂ) else 0)))).sum := by
  rw [velH, SignedShift.listH_coe]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro S _
  exact S.hFun_single (velState_coe A c β) γ

/-- The family, written out. -/
theorem hopList_eq : hopList A c =
    [diagHop A c 0, shearHop A c 0,
      pairHop A c 0 0, rotHop A c 0 0, pairHop A c 0 1, rotHop A c 0 1,
      pairHop A c 0 2, rotHop A c 0 2,
     diagHop A c 1, shearHop A c 1,
      pairHop A c 1 0, rotHop A c 1 0, pairHop A c 1 1, rotHop A c 1 1,
      pairHop A c 1 2, rotHop A c 1 2,
     diagHop A c 2, shearHop A c 2,
      pairHop A c 2 0, rotHop A c 2 0, pairHop A c 2 1, rotHop A c 2 1,
      pairHop A c 2 2, rotHop A c 2 2] := rfl

@[simp] theorem diagHop_shift (i : Fin 3) : (diagHop A c i).shift = shDiag i := rfl
@[simp] theorem diagHop_amp (i : Fin 3) : (diagHop A c i).amp = ampDiag A i := rfl
@[simp] theorem shearHop_shift (i : Fin 3) : (shearHop A c i).shift = shShear i := rfl
@[simp] theorem shearHop_amp (i : Fin 3) : (shearHop A c i).amp = ampShear c i := rfl
@[simp] theorem pairHop_shift (i k : Fin 3) : (pairHop A c i k).shift = shPair i k := rfl
@[simp] theorem pairHop_amp (i k : Fin 3) : (pairHop A c i k).amp = ampPair A i k := rfl
@[simp] theorem rotHop_shift (i k : Fin 3) : (rotHop A c i k).shift = shRot i k := rfl
@[simp] theorem rotHop_amp (i k : Fin 3) : (rotHop A c i k).amp = ampRot A i k := rfl

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- **The strain coupling of two distinct components.**  The matrix entry of `H`
between the ground state and the doubly excited state `e₁ + e₂` is the symmetric
part `(A₁₂ + A₂₁)/2` of the velocity gradient: the two components really are
coupled. -/
theorem velH_coord_pair :
    ((velH A c (velState A c ![0, 0, 0]) : L2I Vel) : Vel → ℂ) ![1, 1, 0]
      = Complex.I * (((A 0 1 + A 1 0) / 2 : ℝ) : ℂ) := by
  rw [velH_coe_single, hopList_eq]
  simp +decide [ampPair, coefPair]
  ring

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- **The vorticity coupling of two distinct components.**  The matrix entry of
`H` between the state `e₂` and the state `e₁` is the antisymmetric part
`(A₁₂ − A₂₁)/2` of the velocity gradient: the number-conserving hopping, the one
whose amplitude is not monotone, really is present. -/
theorem velH_coord_rot :
    ((velH A c (velState A c ![0, 1, 0]) : L2I Vel) : Vel → ℂ) ![1, 0, 0]
      = Complex.I * (((A 0 1 - A 1 0) / 2 : ℝ) : ℂ) := by
  rw [velH_coe_single, hopList_eq]
  simp +decide [ampRot, coefRot]
  ring

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- The matrix entry carried by the constant part `c₁` of the first fiber field:
the `±1`-hopping out of the ground state. -/
theorem velH_coord_shear :
    ((velH A c (velState A c ![0, 0, 0]) : L2I Vel) : Vel → ℂ) ![1, 0, 0]
      = Complex.I * ((c 0 / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [velH_coe_single, hopList_eq]
  simp +decide [ampShear]

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- The matrix entry carried by the diagonal (self-advection) rate `A₁₁`: the
`±2`-hopping out of the ground state. -/
theorem velH_coord_diag :
    ((velH A c (velState A c ![0, 0, 0]) : L2I Vel) : Vel → ℂ) ![2, 0, 0]
      = Complex.I * ((A 0 0 * Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  rw [velH_coe_single, hopList_eq]
  simp +decide [ampDiag, ampPair, coefPair]
  ring

/-- With a non-zero symmetric part the two components are genuinely coupled. -/
theorem velH_ne_zero_of_strain (h : A 0 1 + A 1 0 ≠ 0) :
    velH A c (velState A c ![0, 0, 0]) ≠ 0 := by
  intro h0
  have hco := velH_coord_pair A c
  rw [h0] at hco
  simp only [lp.coeFn_zero, Pi.zero_apply] at hco
  have : ((A 0 1 + A 1 0) / 2 : ℝ) = 0 := by
    have h1 : (((A 0 1 + A 1 0) / 2 : ℝ) : ℂ) = 0 := by
      have := hco.symm
      simpa [Complex.ext_iff] using this
    exact_mod_cast h1
  exact h (by linarith)

/-- With a non-zero antisymmetric part the vorticity coupling is genuinely
present. -/
theorem velH_ne_zero_of_vorticity (h : A 0 1 - A 1 0 ≠ 0) :
    velH A c (velState A c ![0, 1, 0]) ≠ 0 := by
  intro h0
  have hco := velH_coord_rot A c
  rw [h0] at hco
  simp only [lp.coeFn_zero, Pi.zero_apply] at hco
  have : ((A 0 1 - A 1 0) / 2 : ℝ) = 0 := by
    have h1 : (((A 0 1 - A 1 0) / 2 : ℝ) : ℂ) = 0 := by
      have := hco.symm
      simpa [Complex.ext_iff] using this
    exact_mod_cast h1
  exact h (by linarith)

/-! ## Unboundedness -/

theorem vel_eq_iff (x y : Vel) : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    funext j
    fin_cases j <;> assumption

theorem raise_apply (i : Fin 3) (β : Vel) (j : Fin 3) :
    raise i β j = β j + (if j = i then 1 else 0) := by
  by_cases h : j = i
  · subst h; simp [raise]
  · simp [raise_of_ne h, h]

theorem shDiag_apply (i : Fin 3) (β : Vel) (j : Fin 3) :
    shDiag i β j = β j + (if j = i then 2 else 0) := by
  by_cases h : j = i
  · subst h; simp [shDiag, raise]
  · simp [shDiag, raise_of_ne h, h]

theorem shPair_apply (i k : Fin 3) (β : Vel) (j : Fin 3) :
    shPair i k β j = β j + (if j = k then 1 else 0) + (if j = i then 1 else 0) := by
  rw [shPair, raise_apply, raise_apply]

theorem shShear_apply (i : Fin 3) (β : Vel) (j : Fin 3) :
    shShear i β j = β j + (if j = i then 1 else 0) := raise_apply i β j

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one
/-- The `±2`-hopping entry of the first component along the whole tower of
excited states: its amplitude grows like the Hermite level. -/
theorem velH_coord_diag_tower (n : ℕ) :
    ((velH A c (velState A c ![n + 1, 0, 0]) : L2I Vel) : Vel → ℂ) ![n + 3, 0, 0]
      = Complex.I * ((A 0 0 / 2 * Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) : ℝ) : ℂ) := by
  have hne : ¬ (n + 3 + 1 = n) := by omega
  rw [velH_coe_single, hopList_eq]
  simp [vel_eq_iff, shDiag_apply, shPair_apply, shShear_apply, shRot, swapVel, lower,
    raise_apply, Equiv.swap_apply_def, hne, ampDiag, ampPair, coefPair]

/-- **The coupled Hamiltonian is unbounded**: essential self-adjointness above
is not a boundedness phenomenon. -/
theorem velH_not_bounded (hA : A 0 0 ≠ 0) (C : ℝ) :
    ∃ β : Vel, ‖(velState A c β : L2I Vel)‖ = 1
      ∧ C < ‖(velH A c (velState A c β) : L2I Vel)‖ := by
  have hpos : 0 < |A 0 0| := abs_pos.mpr hA
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (|C| + 1) / |A 0 0|)
  refine ⟨![n + 1, 0, 0], norm_velState A c _, ?_⟩
  have hb : ‖((velH A c (velState A c ![n + 1, 0, 0]) : L2I Vel) : Vel → ℂ) ![n + 3, 0, 0]‖
      ≤ ‖(velH A c (velState A c ![n + 1, 0, 0]) : L2I Vel)‖ :=
    lp.norm_apply_le_norm (by norm_num) _ _
  rw [velH_coord_diag_tower] at hb
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : ((n : ℝ) + 2) ≤ Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) := by
    have h := Real.sqrt_le_sqrt
      (show ((n : ℝ) + 2) ^ 2 ≤ ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2) by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  have hnorm : ‖Complex.I * ((A 0 0 / 2 * Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) :
        ℝ) : ℂ)‖
      = |A 0 0| / 2 * Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num
  rw [hnorm] at hb
  have hmul : 2 * (|C| + 1) < |A 0 0| * (n : ℝ) := by
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hC : C ≤ |C| := le_abs_self C
  nlinarith [hsq, hpos.le]

/-- The finite-mode core is dense, so the coupled Hamiltonian is a densely
defined operator and its essential self-adjointness is the statement it should
be. -/
theorem velH_domain_dense :
    Dense ((lpFiniteModes Vel : Submodule ℂ (L2I Vel)) : Set (L2I Vel)) :=
  lpFiniteModes_dense

end ThreeComponent

end BookProof.NavierStokesFlow
