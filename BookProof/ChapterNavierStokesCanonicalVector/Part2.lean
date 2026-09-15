import Mathlib
import BookProof.ChapterNavierStokesThreeComponent
import BookProof.ChapterNavierStokesCanonicalVector.Part1

/-!
# The canonical (differential) form of the full quadratic Navier–Stokes symbol

`BookProof.ChapterNavierStokesThreeComponent` proves that the coupled
three-component fiber Hamiltonian

`H = ∑_i ½(π_i V_i + V_i π_i)`,  `V_i(u) = ∑_k A_{ik} u_k + c_i`,

is essentially self-adjoint on the finite-mode core of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`,
for an arbitrary real matrix `A` and an arbitrary real vector `c` — but it does so by
*writing down the Hermite matrix* of that operator, and the module records as an honest
boundary that "the differential realization on `L²(du₁du₂du₃)` is not built here".

This module removes that boundary, in the same way that
`BookProof.ChapterNavierStokesHermiteCanonical` removed it for the single linear fiber:
it builds the three canonical pairs `(u_i, π_i)` out of the Hermite ladder operators and
proves that the matrix `velH` **is** the canonically written operator.

## The Navier–Stokes symbol

In the Eulerian derivatives-as-fields picture the quadratic symbol of the Navier–Stokes
generator at one fiber is

`A_i(u) = u_j u_{i,j} − ν u_{i,jj}`,

which is an **affine** function of the velocity `u = (u₁,u₂,u₃)`: its linear part is the
velocity-gradient matrix `G_{ij} = u_{i,j}` and its constant part is `−ν u_{i,jj}` (the
derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical coordinates, constants
of the motion at the fiber).  So the full quadratic symbol is exactly the affine field
`V_i` above with `A = G` and `c_i = −ν u_{i,jj}`, and the canonical quantization of the
symbol is the Weyl-ordered `∑_i ½(π_i A_i + A_i π_i)`.

## Contents

* `ann i`, `cre i` — the annihilation and creation operators of the `i`-th mode on the
  finite-mode core of `ℓ²(Vel)`, with the full canonical commutation relations
  `comm_ann_cre` (`[a_i, a_i†] = 1`), `comm_ann_cre_of_ne` (`[a_i, a_k†] = 0`, `i ≠ k`),
  `ann_comm`, `cre_comm`;
* `pos i = (a_i + a_i†)/√2`, `mom i = i(a_i† − a_i)/√2` — the three canonical pairs, with
  `comm_mom_pos` (`[π_i, u_i] = −i`) and `comm_mom_pos_of_ne` (`[π_i, u_k] = 0`);
* `fieldV A c i = ∑_k A_{ik} u_k + c_i` — the affine fiber field, and
  `canH A c = ∑_i ½(π_i V_i + V_i π_i)` — the Weyl-ordered canonical Hamiltonian;
* `canH_eq_velH` — **the identification**: `canH A c` is exactly the Hermite matrix
  `velH A c` of `ChapterNavierStokesThreeComponent`;
* `canH_essentiallySelfAdjointOn_core` — hence the canonically written full
  quadratic-symbol Hamiltonian is essentially self-adjoint on the finite-mode core;
* `nsQuadraticH`, `nsQuadraticH_essentiallySelfAdjointOn_core` — the same statement with
  the coefficients spelled out as the Navier–Stokes data `(ν, u_{i,j}, u_{i,jj})`.

## Honest boundary

The Hilbert space is the Hermite (occupation-number) realization `ℓ²(Fin 3 → ℕ)` of
`L²(du₁du₂du₃)` for the three velocity components at one fiber; `pos i` and `mom i` are
the canonical pair in that realization, and the operator is the Weyl quantization of the
affine symbol.  Nothing here claims global regularity of the classical Navier–Stokes
equation (Contention D5, the deliberate scope cut).
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace CanonicalVector

open LpNat FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
/-! ### The strain (symmetric cross) hop -/

theorem pairHop_hFun (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (pairHop A c i k).hFun X γ
      = Complex.I * (((coefPair A i k : ℝ) : ℂ)
        * (cFun i (cFun k X) γ - aFun i (aFun k X) γ)) := by
  by_cases hik : i = k
  · subst hik
    have hz : coefPair A i i = 0 := by simp [coefPair]
    have hamp : ∀ β, ampPair A i i β = 0 := by intro β; simp [ampPair, hz]
    have key := hFun_eq_of_incoming (pairHop A c i i) X (fun _ => 0)
      (by intro β; simp only [pairHop_amp, hamp]; simp)
      (by intro δ _; rfl) γ
    rw [key, hz]
    simp [pairHop_amp, hamp]
  · have key := hFun_eq_of_incoming (pairHop A c i k) X
      (fun δ => ((coefPair A i k : ℝ) : ℂ) * cFun i (cFun k X) δ) ?_ ?_ γ
    · rw [key]
      congr 1
      have hout : ((pairHop A c i k).amp γ : ℂ) * X ((pairHop A c i k).shift γ)
          = ((coefPair A i k : ℝ) : ℂ) * aFun i (aFun k X) γ := by
        simp only [pairHop_amp, pairHop_shift, ampPair, aFun, shPair,
          raise_of_ne (Ne.symm hik), raise_comm k i γ]
        rw [Real.sqrt_mul (by positivity)]
        push_cast
        ring
      rw [hout]
      ring
    · intro β
      simp only [pairHop_amp, pairHop_shift, ampPair, cFun, shPair, raise_self,
        raise_of_ne hik, lower_raise]
      rw [Real.sqrt_mul (by positivity)]
      push_cast
      ring
    · intro δ hno
      have hz : δ i = 0 ∨ δ k = 0 := by
        by_contra hcon
        push_neg at hcon
        refine hno ⟨lower k (lower i δ), ?_⟩
        have hik1 : 1 ≤ δ i := Nat.one_le_iff_ne_zero.mpr hcon.1
        have hkk1 : 1 ≤ δ k := Nat.one_le_iff_ne_zero.mpr hcon.2
        have h1 : 1 ≤ (lower i δ) k := by
          rw [lower_of_ne (Ne.symm hik)]; omega
        simp only [pairHop_shift, shPair]
        rw [raise_lower k h1, raise_lower i hik1]
      rcases hz with h0 | h0
      · simp [cFun, h0]
      · simp [cFun, lower_of_ne (Ne.symm hik), h0]

/-! ### The vorticity (antisymmetric cross) hop -/

theorem rotHop_hFun (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (rotHop A c i k).hFun X γ
      = Complex.I * (((coefRot A i k : ℝ) : ℂ)
        * (cFun i (aFun k X) γ - aFun i (cFun k X) γ)) := by
  by_cases hik : i = k
  · subst hik
    have hz : coefRot A i i = 0 := by simp [coefRot]
    have hamp : ∀ β, ampRot A i i β = 0 := by intro β; simp [ampRot, hz]
    have key := hFun_eq_of_incoming (rotHop A c i i) X (fun _ => 0)
      (by intro β; simp only [rotHop_amp, hamp]; simp)
      (by intro δ _; rfl) γ
    rw [key, hz]
    simp [rotHop_amp, hamp]
  · have key := hFun_eq_of_incoming (rotHop A c i k) X
      (fun δ => ((coefRot A i k : ℝ) : ℂ) * cFun i (aFun k X) δ) ?_ ?_ γ
    · rw [key]
      congr 1
      have hout : ((rotHop A c i k).amp γ : ℂ) * X ((rotHop A c i k).shift γ)
          = ((coefRot A i k : ℝ) : ℂ) * aFun i (cFun k X) γ := by
        rcases Nat.eq_zero_or_pos (γ k) with h0 | hpos
        · simp [rotHop_amp, ampRot, aFun, cFun, raise_of_ne (Ne.symm hik), h0]
        · have hne : γ k ≠ 0 := by omega
          simp only [rotHop_amp, rotHop_shift, ampRot, aFun, cFun, shRot, if_neg hne,
            raise_of_ne (Ne.symm hik), lower_raise_of_ne hik]
          rw [Real.sqrt_mul (by positivity)]
          push_cast
          ring
      rw [hout]
      ring
    · intro β
      rcases Nat.eq_zero_or_pos (β k) with h0 | hpos
      · have hswap : (swapVel i k β) i = 0 := by
          rw [swapVel_apply, Equiv.swap_apply_left]; exact h0
        have hL : cFun i (aFun k X) (shRot i k β) = 0 := by
          simp only [shRot, if_pos h0, cFun, hswap]
          simp
        have hR : ampRot A i k β = 0 := by
          simp only [ampRot, h0]
          simp
        simp only [rotHop_amp, rotHop_shift]
        rw [hL, hR]
        simp
      · have hne : β k ≠ 0 := by omega
        have hcast : (((β k - 1 : ℕ) : ℝ) + 1) = ((β k : ℝ)) := by
          have h1 : (1 : ℕ) ≤ β k := hpos
          push_cast [Nat.cast_sub h1]
          ring
        simp only [rotHop_amp, rotHop_shift, ampRot, cFun, aFun, shRot, if_neg hne,
          raise_self, lower_raise, lower_of_ne hik, lower_self, hcast,
          raise_lower k hpos]
        rw [Real.sqrt_mul (by positivity)]
        push_cast
        ring
    · intro δ hno
      have hz : δ i = 0 := by
        by_contra hcon
        have hik1 : 1 ≤ δ i := Nat.one_le_iff_ne_zero.mpr hcon
        refine hno ⟨raise k (lower i δ), ?_⟩
        have hk : (raise k (lower i δ)) k ≠ 0 := by rw [raise_self]; omega
        simp only [rotHop_shift, shRot, if_neg hk]
        rw [lower_raise, raise_lower i hik1]
      simp [cFun, hz]

/-! ### The `±1`-hop of the constant part -/

theorem shearHop_hFun (i : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (shearHop A c i).hFun X γ
      = Complex.I * (((c i / Real.sqrt 2 : ℝ) : ℂ) * (cFun i X γ - aFun i X γ)) := by
  have key := hFun_eq_of_incoming (shearHop A c i) X
    (fun δ => ((c i / Real.sqrt 2 : ℝ) : ℂ) * cFun i X δ) ?_ ?_ γ
  · rw [key]
    congr 1
    have hout : ((shearHop A c i).amp γ : ℂ) * X ((shearHop A c i).shift γ)
        = ((c i / Real.sqrt 2 : ℝ) : ℂ) * aFun i X γ := by
      simp only [shearHop_amp, shearHop_shift, ampShear, aFun, shShear]
      push_cast
      ring
    rw [hout]
    ring
  · intro β
    simp only [shearHop_amp, shearHop_shift, ampShear, cFun, shShear, raise_self, lower_raise]
    push_cast
    ring
  · intro δ hno
    have hz : δ i = 0 := by
      by_contra hcon
      exact hno ⟨lower i δ, by
        simp only [shearHop_shift, shShear]
        exact raise_lower i (Nat.one_le_iff_ne_zero.mpr hcon)⟩
    simp [cFun, hz]

/-! ## The ladder normal form

Both the Hermite matrix `velH` and the canonically written operator reduce to the same
explicit combination of ladder expressions; `ladFun` is that combination. -/

/-- The ladder normal form of the coupled three-component fiber Hamiltonian. -/
noncomputable def ladFun (X : Vel → ℂ) (γ : Vel) : ℂ :=
  Complex.I * ((∑ i, ((A i i / 2 : ℝ) : ℂ) * (cFun i (cFun i X) γ - aFun i (aFun i X) γ))
    + (∑ i, ((c i / Real.sqrt 2 : ℝ) : ℂ) * (cFun i X γ - aFun i X γ))
    + (∑ i, ∑ k, ((coefPair A i k : ℝ) : ℂ) * (cFun i (cFun k X) γ - aFun i (aFun k X) γ))
    + (∑ i, ∑ k, ((coefRot A i k : ℝ) : ℂ) * (cFun i (aFun k X) γ - aFun i (cFun k X) γ)))

@[simp] theorem coe_inclusion_finiteModes (sym : Vel → ℝ) (x : lpFiniteModes Vel) :
    ((Submodule.inclusion (finiteModes_le_maxDom sym) x : maxDom sym) : L2I Vel)
      = (x : L2I Vel) := rfl

set_option maxHeartbeats 2000000 in
-- The four hopping families expand into twenty-odd ladder terms whose coordinatewise
-- matching is a single large `ring` normalisation; the default budget is not enough.
/-- **The Hermite matrix in ladder normal form.** -/
theorem velH_crd (x : lpFiniteModes Vel) (γ : Vel) :
    ((velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x) :
        L2I Vel) : Vel → ℂ) γ
      = ladFun A c (crd x) γ := by
  rw [velH, SignedShift.listH_coe]
  simp only [hopList_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    diagHop_hFun, shearHop_hFun, pairHop_hFun, rotHop_hFun, ladFun, Fin.sum_univ_three,
    coe_inclusion_finiteModes, crd]
  push_cast
  ring

/-! ## The canonically written Hamiltonian -/

/-- The coordinates of `u_i x`. -/
noncomputable def pFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (cFun i X + aFun i X)

/-- The coordinates of `π_i x`. -/
noncomputable def mFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)) • (cFun i X - aFun i X)

@[simp] theorem pFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    pFun i (X + Y) = pFun i X + pFun i Y := by
  funext δ; simp only [pFun, cFun_add, aFun_add, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]; ring

@[simp] theorem pFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    pFun i (a • X) = a • pFun i X := by
  funext δ; simp only [pFun, cFun_smul, aFun_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]; ring

@[simp] theorem crd_pos (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (pos i x) = pFun i (crd x) := by
  simp only [pos, pFun, LinearMap.smul_apply, LinearMap.add_apply, crd_smul, crd_add,
    crd_cre, crd_ann]

@[simp] theorem crd_mom (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (mom i x) = mFun i (crd x) := by
  simp only [mom, mFun, LinearMap.smul_apply, LinearMap.sub_apply, crd_smul, crd_sub,
    crd_cre, crd_ann]

/-- **The affine fiber field** `V_i(u) = ∑_k A_{ik} u_k + c_i`. -/
noncomputable def fieldV (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  (∑ k, ((A i k : ℝ) : ℂ) • pos k) + (((c i : ℝ) : ℂ) • LinearMap.id)

/-- **The Weyl-ordered canonical Hamiltonian** `∑_i ½(π_i V_i + V_i π_i)`. -/
noncomputable def canH : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  ∑ i, ((1 : ℂ) / 2) • ((mom i).comp (fieldV A c i) + (fieldV A c i).comp (mom i))

/-- The coordinates of the affine fiber field. -/
noncomputable def vFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  (∑ k, ((A i k : ℝ) : ℂ) • pFun k X) + (((c i : ℝ) : ℂ) • X)

/-- The coordinates of the canonical Hamiltonian. -/
noncomputable def canFun (X : Vel → ℂ) (γ : Vel) : ℂ :=
  ∑ i, ((1 : ℂ) / 2) * (mFun i (vFun A c i X) γ + vFun A c i (mFun i X) γ)

theorem crd_fieldV (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (fieldV A c i x) = vFun A c i (crd x) := by
  funext γ
  simp only [fieldV, vFun, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Fin.sum_univ_three, crd_add, crd_smul, crd_pos, Pi.add_apply, Pi.smul_apply]

theorem canH_crd (x : lpFiniteModes Vel) (γ : Vel) :
    crd (canH A c x) γ = canFun A c (crd x) γ := by
  simp only [canH, canFun, Fin.sum_univ_three, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, crd_smul, crd_add, crd_mom, crd_fieldV,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-! ### The Weyl-ordered product of one momentum and one coordinate -/

@[simp] theorem mFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    mFun i (X + Y) = mFun i X + mFun i Y := by
  funext δ; simp only [mFun, cFun_add, aFun_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]; ring

@[simp] theorem mFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    mFun i (a • X) = a • mFun i X := by
  funext δ; simp only [mFun, cFun_smul, aFun_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]; ring

/-- The Weyl-ordered product `½(π_i u_k + u_k π_i)`, in coordinates. -/
noncomputable def symProdFun (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) : ℂ :=
  ((1 : ℂ) / 2) * (mFun i (pFun k X) γ + pFun k (mFun i X) γ)

/-- The Weyl-ordered product, expanded in the ladder operators.  The two factors of
`1/√2` combine into the `¼` of the Hermite amplitudes. -/
theorem symProdFun_eq (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    symProdFun i k X γ
      = (Complex.I / 4) * (cFun i (cFun k X) γ + cFun i (aFun k X) γ
          - aFun i (cFun k X) γ - aFun i (aFun k X) γ
          + cFun k (cFun i X) γ - cFun k (aFun i X) γ
          + aFun k (cFun i X) γ - aFun k (aFun i X) γ) := by
  have hs2 : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [inv_sqrt_two_sq]; norm_num
  simp only [symProdFun, mFun, pFun, cFun_add, aFun_add, cFun_sub, aFun_sub, cFun_smul,
    aFun_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (Complex.I / 2 * (cFun i (cFun k X) γ + cFun i (aFun k X) γ
      - aFun i (cFun k X) γ - aFun i (aFun k X) γ
      + cFun k (cFun i X) γ - cFun k (aFun i X) γ
      + aFun k (cFun i X) γ - aFun k (aFun i X) γ)) * hs2

/-- The canonical Hamiltonian, regrouped: each entry of the velocity gradient multiplies a
Weyl-ordered product, each constant a momentum. -/
theorem canFun_eq_sum (X : Vel → ℂ) (γ : Vel) :
    canFun A c X γ
      = ∑ i, ((∑ k, ((A i k : ℝ) : ℂ) * symProdFun i k X γ) + ((c i : ℝ) : ℂ) * mFun i X γ) := by
  simp only [canFun, vFun, symProdFun, Fin.sum_univ_three, mFun_add, mFun_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 4000000 in
-- Both sides expand into the same several-dozen-term ladder polynomial; normalising it
-- with `ring` exceeds the default heartbeat budget.
/-- **The canonically written Hamiltonian in ladder normal form.**  This is the algebraic
heart of the identification: the Weyl-ordered product `½(π_i V_i + V_i π_i)` expands, by the
canonical commutation relations, into exactly the four hopping families of the Hermite
matrix. -/
theorem canFun_eq_ladFun (X : Vel → ℂ) (γ : Vel) :
    canFun A c X γ = ladFun A c X γ := by
  rw [canFun_eq_sum]
  simp +decide only [ladFun, mFun, symProdFun_eq, Fin.sum_univ_three,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coefPair, coefRot,
    aFun_cFun_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    aFun_cFun_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    aFun_cFun_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    aFun_cFun_of_ne (show (1 : Fin 3) ≠ 2 by decide),
    aFun_cFun_of_ne (show (2 : Fin 3) ≠ 0 by decide),
    aFun_cFun_of_ne (show (2 : Fin 3) ≠ 1 by decide),
    cFun_comm 1 0, cFun_comm 2 0, cFun_comm 2 1,
    aFun_comm 1 0, aFun_comm 2 0, aFun_comm 2 1]
  push_cast
  ring

/-! ## The identification, and essential self-adjointness of the canonical operator -/

/-- **The Hermite matrix of `ChapterNavierStokesThreeComponent` *is* the canonically
written operator** `∑_i ½(π_i V_i + V_i π_i)` with `V_i(u) = ∑_k A_{ik} u_k + c_i`,
`u_i = (a_i + a_i†)/√2`, `π_i = i(a_i† − a_i)/√2`. -/
theorem canH_eq_velH :
    (lpFiniteModes Vel).subtype.comp (canH A c)
      = (velH A c).comp (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c)))) := by
  refine LinearMap.ext fun x => lp.ext (funext fun γ => ?_)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [velH_crd]
  exact (canH_crd A c x γ).trans (canFun_eq_ladFun A c (crd x) γ)

/-- **The canonically written full quadratic-symbol Hamiltonian is essentially
self-adjoint on the finite-mode core** of `ℓ²(Vel)`, for an arbitrary real velocity
gradient `A` and an arbitrary real constant part `c`. -/
theorem canH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes Vel)
      ((lpFiniteModes Vel).subtype.comp (canH A c)) := by
  rw [canH_eq_velH]
  exact velH_essentiallySelfAdjointOn_core A c

/-- A Hermite basis state of the three-mode core. -/
noncomputable def coreState (β : Vel) : lpFiniteModes Vel :=
  ⟨lp.single 2 β 1, lpSingle_mem_lpFiniteModes β 1⟩

/-- **The canonical operator is unbounded**: essential self-adjointness above is not a
boundedness phenomenon. -/
theorem canH_not_bounded (hA : A 0 0 ≠ 0) (C : ℝ) :
    ∃ x : lpFiniteModes Vel, ‖(x : L2I Vel)‖ = 1
      ∧ C < ‖((canH A c x : lpFiniteModes Vel) : L2I Vel)‖ := by
  obtain ⟨β, h1, h2⟩ := velH_not_bounded A c hA C
  refine ⟨coreState β, h1, ?_⟩
  have hEq : ((canH A c (coreState β) : lpFiniteModes Vel) : L2I Vel)
      = (velH A c (velState A c β) : L2I Vel) := by
    have h := congrArg (fun T : lpFiniteModes Vel →ₗ[ℂ] L2I Vel => T (coreState β))
      (canH_eq_velH A c)
    simpa using h
  rw [hEq]
  exact h2

/-! ## The Navier–Stokes reading of the coefficients

At one Eulerian fiber the quadratic symbol of the Navier–Stokes generator is
`A_i(u) = u_j u_{i,j} − ν u_{i,jj}`, an affine function of the velocity whose linear part
is the velocity gradient `u_{i,j}` and whose constant part is `−ν u_{i,jj}` (the derivative
fields are independent canonical coordinates at the fiber).  The following is the theorem
above with the coefficients spelled out that way. -/

/-- **The quantized Navier–Stokes quadratic symbol** `∑_i ½(π_i A_i + A_i π_i)` with
`A_i(u) = ∑_j (grad i j) u_j − ν (lap i)`, on the three-mode Hermite core. -/
noncomputable def nsQuadraticH (nu : ℝ) (grad : Matrix (Fin 3) (Fin 3) ℝ) (lap : Fin 3 → ℝ) :
    lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  canH grad (fun i => -(nu * lap i))

/-- **The quantized full quadratic Navier–Stokes symbol is essentially self-adjoint on the
Hermite core of the three velocity components**, for every viscosity, every velocity
gradient and every velocity Laplacian at the fiber. -/
theorem nsQuadraticH_essentiallySelfAdjointOn_core
    (nu : ℝ) (grad : Matrix (Fin 3) (Fin 3) ℝ) (lap : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes Vel)
      ((lpFiniteModes Vel).subtype.comp (nsQuadraticH nu grad lap)) :=
  canH_essentiallySelfAdjointOn_core grad _

/-- The finite-mode core is dense, so the canonical operator is densely defined and its
essential self-adjointness is the statement it should be. -/
theorem canH_domain_dense :
    Dense ((lpFiniteModes Vel : Submodule ℂ (L2I Vel)) : Set (L2I Vel)) :=
  lpFiniteModes_dense

end CanonicalVector

end BookProof.NavierStokesFlow
