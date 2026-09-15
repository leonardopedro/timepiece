import Mathlib
import BookProof.ChapterNavierStokesShiftHamiltonian
import BookProof.ChapterNavierStokesHermiteFarisLavine

/-!
# The **affine** Navier–Stokes fiber field: a `±1`-shift on top of the `±2`-shift

`BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine
inequalities, and hence essential self-adjointness on the finite-mode core, for
the Navier–Stokes fiber Hamiltonian `H = ½(π V + V π)` with a **linear**
advection field `V(u) = κ u`.  `BookProof.ChapterNavierStokesBilinearEsa` lifts
that to the genuinely bilinear (quadratic-symbol) advection term by decomposing
`ℓ²(ℕ × J)` into blocks, one for each eigenvalue `κ_j` of the derivative field.

The boundary recorded there was the **affine** fiber field

`V(u) = κ u + c`,

which is what the viscous term `−ν u_{i,jj}` and the cross terms `u_j u_{i,j}`
with `j ≠ i` produce: they contribute a term that is *constant* in the velocity
mode `u_i` being differentiated.  In the Hermite basis of the fiber,
`½(π V + V π) = κ · ½(π u + u π) + c · π`, and while `½(π u + u π) =
(i/2)(a†² − a²)` is a `±2`-shift (the operator of `ChapterNavierStokes‐
HermiteFarisLavine`), the extra term `c · π = (i c/√2)(a† − a)` is a **`±1`
shift**.  This module removes that boundary.

## The instrument: sums of shift Hamiltonians

The Faris–Lavine hypotheses used in this project
(`BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`) are

* `H` symmetric, `N ≥ 0` with `N + 1` surjective,
* a **relative bound** `‖Hx‖² ≤ a‖Nx‖² + b‖x‖²` — with *no* smallness
  requirement on `a`, and
* a **commutator bound** `|⟪x, i[H, N]x⟫| ≤ c ⟪x, Nx⟫`.

All three are stable under sums: `‖(H₁+H₂)x‖² ≤ 2‖H₁x‖² + 2‖H₂x‖²` and the
commutator form is additive in `H`.  So two shift Hamiltonians sharing one
comparison operator may simply be added.  That is the content of `PairShift`
below: a single symbol `σ` carrying two shifts at once.

## What is proved

* `PairShift.pairH` — the sum of two shift Hamiltonians with a common comparison
  symbol, on the maximal domain of that symbol;
* `PairShift.pairH_symmetricOn`, `PairShift.pairH_relative_bound`,
  `PairShift.pairH_commForm_bound` — the two Faris–Lavine inequalities for the
  sum, with explicit constants;
* `PairShift.pairH_essentiallySelfAdjointOn_core` — the sum is essentially
  self-adjoint on the finite-mode core;
* `affH` — the affine Navier–Stokes fiber Hamiltonian `½(π V + V π)` for
  `V(u) = κ u + c`, in the Hermite basis of `ℓ²(ℕ)`;
* `affH_symmetricOn`, `affH_essentiallySelfAdjointOn_core` — **the headline**:
  the affine fiber Hamiltonian is symmetric and essentially self-adjoint on the
  finite-mode core, for all `κ ≥ 0` and `c ≥ 0`;
* `affH_coord_succ` and `affH_coord_succ_succ` — the two matrix entries of `H`
  on a Hermite basis vector: the `±1`-hopping `(c/√2)√(n+1)` of the constant
  part and the `±2`-hopping `(κ/2)√((n+1)(n+2))` of the linear part;
* `affH_ne_zero_of_pos_shear` and `affH_not_bounded` — the `±1`-hopping really
  is present when `c > 0`, and the operator is genuinely unbounded when
  `κ > 0`.

## Honest boundary

`c ≥ 0` is assumed, only because a `ShiftData` amplitude is required to be
non-negative; the case `c < 0` is the conjugate of the case `|c|` by the
sign-flip unitary `x_n ↦ (−1)ⁿ x_n`, which reverses the sign of a `±1`-hopping
and preserves a `±2`-hopping — that unitary equivalence is *not* formalized
here, so nothing below is claimed for `c < 0`.  The comparison operator used is
`N = μ(2n+1) + 1` with `μ = κ + c + 1`, i.e. the harmonic-oscillator number
operator rescaled so as to dominate both amplitudes.  As in the modules quoted
above, everything is stated on the abstract sequence space `ℓ²(ℕ)` with the
operator given by its matrix in the Hermite basis; the differential realization
on `L²(du)` is not built here.  Only one velocity component is carried, and
nothing here claims global regularity for the classical Navier–Stokes equation.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace AffineFiber

open LpNat FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

/-! ## Additivity of the commutator form -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- The commutator form `⟪x, i[H, N]x⟫` is additive in `H`. -/
theorem commForm_add (H₁ H₂ N : D →ₗ[ℂ] F) (x : D) :
    commForm (H₁ + H₂) N x = commForm H₁ N x + commForm H₂ N x := by
  simp only [commForm, LinearMap.add_apply, inner_add_left, inner_add_right]
  have : Complex.I * (inner ℂ (H₁ x) (N x) + inner ℂ (H₂ x) (N x)
      - (inner ℂ (N x) (H₁ x) + inner ℂ (N x) (H₂ x)))
      = Complex.I * (inner ℂ (H₁ x) (N x) - inner ℂ (N x) (H₁ x))
        + Complex.I * (inner ℂ (H₂ x) (N x) - inner ℂ (N x) (H₂ x)) := by ring
  rw [this, Complex.add_re]

/-! ## Two matrix entries of a shift Hamiltonian -/

open ShiftHamiltonian in
/-- The `s o`-th coordinate of `H x` when `x` is the basis vector at `o`: the
hopping amplitude `w(o)`, times `i`. -/
theorem hFun_shift_of_single (S : ShiftData ι) {X : ι → ℂ} {o : ι}
    (hXo : X o = 1) (hnext : X (S.shift (S.shift o)) = 0) :
    S.hFun X (S.shift o) = Complex.I * ((S.amp o : ℝ) : ℂ) := by
  unfold ShiftData.hFun
  rw [ShiftData.hop_shift, hXo, mul_one, hnext, mul_zero, sub_zero]

open ShiftHamiltonian in
/-- A coordinate at which the state vanishes both one step back and one step
forward along the shift carries no matrix entry. -/
theorem hFun_eq_zero (S : ShiftData ι) {X : ι → ℂ} {β : ι}
    (hpre : ∀ α, S.shift α = β → X α = 0) (hX : X (S.shift β) = 0) : S.hFun X β = 0 := by
  unfold ShiftData.hFun
  have hhop : S.hop (fun α => (S.amp α : ℂ) * X α) β = 0 := by
    by_cases hb : ∃ α, S.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      rw [ShiftData.hop_shift, hpre α rfl, mul_zero]
    · exact ShiftData.hop_eq_zero S _ hb
  rw [hhop, hX, mul_zero, sub_zero, mul_zero]

open ShiftHamiltonian in
/-- The coordinates of a shift Hamiltonian are additive in the state. -/
theorem hFun_add (S : ShiftData ι) (X Y : ι → ℂ) (β : ι) :
    S.hFun (fun α => X α + Y α) β = S.hFun X β + S.hFun Y β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    simp only [ShiftData.hFun, ShiftData.hop_shift]
    ring
  · have hz : ∀ g : ι → ℂ, S.hop g β = 0 := fun g => ShiftData.hop_eq_zero S g hb
    simp only [ShiftData.hFun, hz]
    ring

open ShiftHamiltonian in
/-- A shift Hamiltonian kills the zero state. -/
theorem hFun_zero (S : ShiftData ι) (β : ι) : S.hFun (fun _ : ι => (0 : ℂ)) β = 0 := by
  refine hFun_eq_zero S (fun α _ => rfl) rfl

open ShiftHamiltonian in
/-- The coordinates of a shift Hamiltonian are homogeneous in the state. -/
theorem hFun_smul (S : ShiftData ι) (a : ℂ) (X : ι → ℂ) (β : ι) :
    S.hFun (fun α => a * X α) β = a * S.hFun X β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    simp only [ShiftData.hFun, ShiftData.hop_shift]
    ring
  · have hz : ∀ g : ι → ℂ, S.hop g β = 0 := fun g => ShiftData.hop_eq_zero S g hb
    simp only [ShiftData.hFun, hz]
    ring

open ShiftHamiltonian in
/-- A shift Hamiltonian moves the support of a state at most one step along the
shift, in either direction. -/
theorem support_hFun (S : ShiftData ι) (X : ι → ℂ) :
    Function.support (S.hFun X)
      ⊆ S.shift '' Function.support X ∪ S.shift ⁻¹' Function.support X := by
  intro β hβ
  rw [Set.mem_union]
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hX : X (S.shift β) = 0 := by
    by_contra h
    exact h2 h
  refine hβ (hFun_eq_zero S (fun α hα => ?_) hX)
  by_contra hXα
  exact h1 ⟨α, hXα, hα⟩

/-! ## Two shifts sharing one comparison symbol -/

/-- The data of two shift Hamiltonians sharing a single comparison symbol `σ ≥ 1`:
two injective shifts, two amplitudes dominated by `σ`, and constant symbol
increments along each shift. -/
structure PairShift (ι : Type*) where
  /-- The symbol of the common comparison operator `N`. -/
  sym : ι → ℝ
  /-- The first shift. -/
  shift₁ : ι → ι
  /-- The second shift. -/
  shift₂ : ι → ι
  /-- The hopping amplitude along the first shift. -/
  amp₁ : ι → ℝ
  /-- The hopping amplitude along the second shift. -/
  amp₂ : ι → ℝ
  /-- The additive constant in the domination of the amplitudes by the symbol. -/
  K : ℝ
  /-- The increment of the symbol along the first shift. -/
  step₁ : ℝ
  /-- The increment of the symbol along the second shift. -/
  step₂ : ℝ
  shift₁_injective : Function.Injective shift₁
  shift₂_injective : Function.Injective shift₂
  amp₁_nonneg : ∀ β, 0 ≤ amp₁ β
  amp₂_nonneg : ∀ β, 0 ≤ amp₂ β
  amp₁_mono : ∀ β, amp₁ β ≤ amp₁ (shift₁ β)
  amp₂_mono : ∀ β, amp₂ β ≤ amp₂ (shift₂ β)
  K_nonneg : 0 ≤ K
  step₁_nonneg : 0 ≤ step₁
  step₂_nonneg : 0 ≤ step₂
  sym_ge_one : ∀ β, 1 ≤ sym β
  amp₁_le : ∀ β, amp₁ β ≤ (1 / 4) * sym β + K
  amp₂_le : ∀ β, amp₂ β ≤ (1 / 4) * sym β + K
  sym_step₁ : ∀ β, sym (shift₁ β) = sym β + step₁
  sym_step₂ : ∀ β, sym (shift₂ β) = sym β + step₂

namespace PairShift

variable (P : PairShift ι)

/-- The first of the two shift Hamiltonians packaged by `P`. -/
@[reducible] def fst : ShiftData ι where
  sym := P.sym
  shift := P.shift₁
  amp := P.amp₁
  K := P.K
  step := P.step₁
  shift_injective := P.shift₁_injective
  amp_nonneg := P.amp₁_nonneg
  amp_mono := P.amp₁_mono
  K_nonneg := P.K_nonneg
  step_nonneg := P.step₁_nonneg
  sym_ge_one := P.sym_ge_one
  amp_le := P.amp₁_le
  sym_step := P.sym_step₁

/-- The second of the two shift Hamiltonians packaged by `P`. -/
@[reducible] def snd : ShiftData ι where
  sym := P.sym
  shift := P.shift₂
  amp := P.amp₂
  K := P.K
  step := P.step₂
  shift_injective := P.shift₂_injective
  amp_nonneg := P.amp₂_nonneg
  amp_mono := P.amp₂_mono
  K_nonneg := P.K_nonneg
  step_nonneg := P.step₂_nonneg
  sym_ge_one := P.sym_ge_one
  amp_le := P.amp₂_le
  sym_step := P.sym_step₂

@[simp] theorem fst_sym : P.fst.sym = P.sym := rfl
@[simp] theorem snd_sym : P.snd.sym = P.sym := rfl
@[simp] theorem fst_shift : P.fst.shift = P.shift₁ := rfl
@[simp] theorem snd_shift : P.snd.shift = P.shift₂ := rfl
@[simp] theorem fst_amp : P.fst.amp = P.amp₁ := rfl
@[simp] theorem snd_amp : P.snd.amp = P.amp₂ := rfl

/-- **The two-shift Hamiltonian**: the sum of the two shift Hamiltonians, on the
maximal domain of the common comparison symbol. -/
noncomputable def pairH : maxDom P.sym →ₗ[ℂ] L2I ι :=
  ShiftData.shiftH P.fst + ShiftData.shiftH P.snd

theorem pairH_apply (x : maxDom P.sym) :
    (pairH P x : L2I ι) = (ShiftData.shiftH P.fst x : L2I ι)
      + (ShiftData.shiftH P.snd x : L2I ι) := rfl

theorem pairH_coe (x : maxDom P.sym) (β : ι) :
    ((pairH P x : L2I ι) : ι → ℂ) β
      = P.fst.hFun ((x : L2I ι) : ι → ℂ) β + P.snd.hFun ((x : L2I ι) : ι → ℂ) β := by
  rw [pairH_apply, lp.coeFn_add]
  rfl

/-- The two-shift Hamiltonian is symmetric on the maximal domain. -/
theorem pairH_symmetricOn : SymmetricOn (maxDom P.sym) (pairH P) := by
  intro x y
  have h₁ : (inner ℂ (ShiftData.shiftH P.fst x : L2I ι) (y : L2I ι) : ℂ)
      = inner ℂ (x : L2I ι) (ShiftData.shiftH P.fst y : L2I ι) :=
    ShiftData.shiftH_symmetricOn P.fst x y
  have h₂ : (inner ℂ (ShiftData.shiftH P.snd x : L2I ι) (y : L2I ι) : ℂ)
      = inner ℂ (x : L2I ι) (ShiftData.shiftH P.snd y : L2I ι) :=
    ShiftData.shiftH_symmetricOn P.snd x y
  change (inner ℂ (pairH P x : L2I ι) (y : L2I ι) : ℂ) = inner ℂ (x : L2I ι) (pairH P y : L2I ι)
  rw [pairH_apply, pairH_apply, inner_add_left, inner_add_right, h₁, h₂]

/-- **The first Faris–Lavine inequality for a two-shift Hamiltonian**:
`‖Hx‖² ≤ 2‖Nx‖² + 32K²‖x‖²`.  (No smallness of the coefficient of `‖Nx‖²` is
needed: the Faris–Lavine criterion only uses the relative bound to transport the
conclusion from the maximal domain to a core.) -/
theorem pairH_relative_bound (x : maxDom P.sym) :
    ‖(pairH P x : L2I ι)‖ ^ 2
      ≤ 2 * ‖(diagMax P.sym x : L2I ι)‖ ^ 2 + (32 * P.K ^ 2) * ‖(x : L2I ι)‖ ^ 2 := by
  have h₁ := ShiftData.shiftH_relative_bound P.fst x
  have h₂ := ShiftData.shiftH_relative_bound P.snd x
  have htri : ‖(pairH P x : L2I ι)‖
      ≤ ‖(ShiftData.shiftH P.fst x : L2I ι)‖ + ‖(ShiftData.shiftH P.snd x : L2I ι)‖ := by
    rw [pairH_apply]; exact norm_add_le _ _
  have hsq : ‖(pairH P x : L2I ι)‖ ^ 2
      ≤ 2 * ‖(ShiftData.shiftH P.fst x : L2I ι)‖ ^ 2
        + 2 * ‖(ShiftData.shiftH P.snd x : L2I ι)‖ ^ 2 := by
    nlinarith [norm_nonneg (pairH P x : L2I ι), norm_nonneg (ShiftData.shiftH P.fst x : L2I ι),
      norm_nonneg (ShiftData.shiftH P.snd x : L2I ι),
      sq_nonneg (‖(ShiftData.shiftH P.fst x : L2I ι)‖
        - ‖(ShiftData.shiftH P.snd x : L2I ι)‖)]
  have hK : P.fst.K = P.K := rfl
  have hK' : P.snd.K = P.K := rfl
  rw [hK] at h₁
  rw [hK'] at h₂
  have hsym : (diagMax P.fst.sym x : L2I ι) = (diagMax P.sym x : L2I ι) := rfl
  have hsym' : (diagMax P.snd.sym x : L2I ι) = (diagMax P.sym x : L2I ι) := rfl
  rw [hsym] at h₁
  rw [hsym'] at h₂
  linarith

/-- **The second Faris–Lavine inequality for a two-shift Hamiltonian**:
`|⟪x, i[H,N]x⟫| ≤ (2Δ₁ + 2Δ₂)(¼ + K) ⟪x, Nx⟫`. -/
theorem pairH_commForm_bound (x : maxDom P.sym) :
    |commForm (pairH P) (diagMax P.sym) x|
      ≤ (2 * P.step₁ * (1 / 4 + P.K) + 2 * P.step₂ * (1 / 4 + P.K))
        * quadForm (diagMax P.sym) x := by
  have h₁ := ShiftData.shiftH_commForm_bound P.fst x
  have h₂ := ShiftData.shiftH_commForm_bound P.snd x
  have hadd : commForm (pairH P) (diagMax P.sym) x
      = commForm (ShiftData.shiftH P.fst) (diagMax P.sym) x
        + commForm (ShiftData.shiftH P.snd) (diagMax P.sym) x :=
    commForm_add _ _ _ x
  have e₁ : commForm (ShiftData.shiftH P.fst) (diagMax P.fst.sym) x
      = commForm (ShiftData.shiftH P.fst) (diagMax P.sym) x := rfl
  have e₂ : commForm (ShiftData.shiftH P.snd) (diagMax P.snd.sym) x
      = commForm (ShiftData.shiftH P.snd) (diagMax P.sym) x := rfl
  have q₁ : quadForm (diagMax P.fst.sym) x = quadForm (diagMax P.sym) x := rfl
  have q₂ : quadForm (diagMax P.snd.sym) x = quadForm (diagMax P.sym) x := rfl
  rw [e₁, q₁] at h₁
  rw [e₂, q₂] at h₂
  have hK₁ : P.fst.K = P.K := rfl
  have hK₂ : P.snd.K = P.K := rfl
  have hs₁ : P.fst.step = P.step₁ := rfl
  have hs₂ : P.snd.step = P.step₂ := rfl
  rw [hK₁, hs₁] at h₁
  rw [hK₂, hs₂] at h₂
  rw [hadd]
  refine le_trans (abs_add_le _ _) ?_
  linarith

/-- **A two-shift Hamiltonian is essentially self-adjoint on the finite-mode
core.** -/
theorem pairH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((pairH P).comp (Submodule.inclusion (finiteModes_le_maxDom P.sym))) :=
  essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds P.sym
    (fun β => le_trans zero_le_one (P.sym_ge_one β))
    (pairH P) 2 (32 * P.K ^ 2)
    (2 * P.step₁ * (1 / 4 + P.K) + 2 * P.step₂ * (1 / 4 + P.K))
    (pairH_symmetricOn P)
    (by nlinarith [P.step₁_nonneg, P.step₂_nonneg, P.K_nonneg])
    (pairH_relative_bound P) (pairH_commForm_bound P)

end PairShift

end AffineFiber

end BookProof.NavierStokesFlow
