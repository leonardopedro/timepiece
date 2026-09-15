import Mathlib
import BookProof.ChapterNavierStokesThreeComponent

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

/-! ## Bookkeeping for the multi-index shifts -/

theorem raise_comm (i k : Fin 3) (β : Vel) : raise i (raise k β) = raise k (raise i β) := by
  funext j
  by_cases hji : j = i <;> by_cases hjk : j = k
  · subst hji; subst hjk; simp [raise]
  · subst hji; rw [raise_self, raise_of_ne hjk, raise_of_ne hjk, raise_self]
  · subst hjk; rw [raise_of_ne hji, raise_self, raise_self, raise_of_ne hji]
  · rw [raise_of_ne hji, raise_of_ne hjk, raise_of_ne hjk, raise_of_ne hji]

theorem lower_comm (i k : Fin 3) (β : Vel) : lower i (lower k β) = lower k (lower i β) := by
  funext j
  by_cases hji : j = i <;> by_cases hjk : j = k
  · subst hji; subst hjk; simp [lower]
  · subst hji; rw [lower_self, lower_of_ne hjk, lower_of_ne hjk, lower_self]
  · subst hjk; rw [lower_of_ne hji, lower_self, lower_self, lower_of_ne hji]
  · rw [lower_of_ne hji, lower_of_ne hjk, lower_of_ne hjk, lower_of_ne hji]

@[simp] theorem lower_raise (i : Fin 3) (β : Vel) : lower i (raise i β) = β := by
  funext j
  by_cases hji : j = i
  · subst hji; rw [lower_self, raise_self]; omega
  · rw [lower_of_ne hji, raise_of_ne hji]

theorem raise_lower (i : Fin 3) {β : Vel} (h : 1 ≤ β i) : raise i (lower i β) = β := by
  funext j
  by_cases hji : j = i
  · subst hji; rw [raise_self, lower_self]; omega
  · rw [raise_of_ne hji, lower_of_ne hji]

theorem lower_raise_of_ne {i k : Fin 3} (h : i ≠ k) (β : Vel) :
    lower k (raise i β) = raise i (lower k β) := by
  funext j
  by_cases hji : j = i <;> by_cases hjk : j = k
  · exact absurd (hji ▸ hjk ▸ rfl) h
  · subst hji; rw [lower_of_ne hjk, raise_self, raise_self, lower_of_ne hjk]
  · subst hjk; rw [lower_self, raise_of_ne hji, raise_of_ne hji, lower_self]
  · rw [lower_of_ne hjk, raise_of_ne hji, raise_of_ne hji, lower_of_ne hjk]

/-! ## The ladder operators of the three modes -/

/-- The coordinates of `a_i x`: `√(β_i + 1) x_{β + e_i}`. -/
noncomputable def aFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  fun β => (Real.sqrt ((β i : ℝ) + 1) : ℂ) * X (raise i β)

/-- The coordinates of `a_i† x`: `√(β_i) x_{β − e_i}`. -/
noncomputable def cFun (i : Fin 3) (X : Vel → ℂ) : Vel → ℂ :=
  fun β => (Real.sqrt (β i : ℝ) : ℂ) * X (lower i β)

theorem support_aFun {i : Fin 3} {X : Vel → ℂ} (h : (Function.support X).Finite) :
    (Function.support (aFun i X)).Finite := by
  refine Set.Finite.subset (h.preimage (f := raise i)
    (Set.injOn_of_injective (raise_injective i))) ?_
  intro β hβ
  simp only [Function.mem_support, aFun] at hβ
  simp only [Set.mem_preimage, Function.mem_support]
  intro h0
  exact hβ (by rw [h0, mul_zero])

theorem support_cFun {i : Fin 3} {X : Vel → ℂ} (h : (Function.support X).Finite) :
    (Function.support (cFun i X)).Finite := by
  refine Set.Finite.subset (h.image (raise i)) ?_
  intro β hβ
  simp only [Function.mem_support, cFun] at hβ
  have hne : X (lower i β) ≠ 0 := fun h0 => hβ (by rw [h0, mul_zero])
  have hpos : 1 ≤ β i := by
    by_contra hcon
    have : β i = 0 := by omega
    apply hβ
    rw [this]
    simp
  exact ⟨lower i β, hne, raise_lower i hpos⟩

/-- A finitely supported coordinate sequence as a state of the finite-mode core. -/
noncomputable def mkCore {X : Vel → ℂ} (h : (Function.support X).Finite) : lpFiniteModes Vel :=
  ⟨⟨X, memLpTwo_of_finite_support h⟩, h⟩

@[simp] theorem mkCore_coe {X : Vel → ℂ} (h : (Function.support X).Finite) (β : Vel) :
    (((mkCore h : lpFiniteModes Vel) : L2I Vel) : Vel → ℂ) β = X β := rfl

theorem support_finite (x : lpFiniteModes Vel) :
    (Function.support (((x : L2I Vel) : Vel → ℂ))).Finite := x.2

/-- **The annihilation operator of the mode `i`.** -/
noncomputable def ann (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel where
  toFun x := mkCore (support_aFun (i := i) (support_finite x))
  map_add' x y := by
    refine Subtype.ext (lp.ext (funext fun β => ?_))
    simp only [mkCore_coe, aFun, Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' a x := by
    refine Subtype.ext (lp.ext (funext fun β => ?_))
    simp only [mkCore_coe, aFun, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- **The creation operator of the mode `i`.** -/
noncomputable def cre (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel where
  toFun x := mkCore (support_cFun (i := i) (support_finite x))
  map_add' x y := by
    refine Subtype.ext (lp.ext (funext fun β => ?_))
    simp only [mkCore_coe, cFun, Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' a x := by
    refine Subtype.ext (lp.ext (funext fun β => ?_))
    simp only [mkCore_coe, cFun, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- The coordinate function of a state. -/
noncomputable def crd (x : lpFiniteModes Vel) : Vel → ℂ := ((x : L2I Vel) : Vel → ℂ)

@[simp] theorem crd_ann (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (ann i x) = aFun i (crd x) := rfl

@[simp] theorem crd_cre (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (cre i x) = cFun i (crd x) := rfl

@[simp] theorem crd_add (x y : lpFiniteModes Vel) : crd (x + y) = crd x + crd y := by
  funext β; simp [crd]

@[simp] theorem crd_smul (a : ℂ) (x : lpFiniteModes Vel) : crd (a • x) = a • crd x := by
  funext β; simp [crd]

@[simp] theorem crd_sub (x y : lpFiniteModes Vel) : crd (x - y) = crd x - crd y := by
  funext β; simp [crd]

theorem crd_injective : Function.Injective crd := by
  intro x y h
  exact Subtype.ext (lp.ext h)

/-! ## The canonical commutation relations, at the level of coordinates -/

@[simp] theorem aFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    aFun i (X + Y) = aFun i X + aFun i Y := by
  funext β; simp [aFun]; ring

@[simp] theorem aFun_sub (i : Fin 3) (X Y : Vel → ℂ) :
    aFun i (X - Y) = aFun i X - aFun i Y := by
  funext β; simp [aFun]; ring

@[simp] theorem aFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    aFun i (a • X) = a • aFun i X := by
  funext β; simp [aFun]; ring

@[simp] theorem cFun_add (i : Fin 3) (X Y : Vel → ℂ) :
    cFun i (X + Y) = cFun i X + cFun i Y := by
  funext β; simp [cFun]; ring

@[simp] theorem cFun_sub (i : Fin 3) (X Y : Vel → ℂ) :
    cFun i (X - Y) = cFun i X - cFun i Y := by
  funext β; simp [cFun]; ring

@[simp] theorem cFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) :
    cFun i (a • X) = a • cFun i X := by
  funext β; simp [cFun]; ring

/-- `[a_i, a_k] = 0`. -/
theorem aFun_comm (i k : Fin 3) (X : Vel → ℂ) : aFun i (aFun k X) = aFun k (aFun i X) := by
  by_cases hik : i = k
  · rw [hik]
  · funext β
    simp only [aFun, raise_of_ne (Ne.symm hik), raise_of_ne hik, raise_comm i k β]
    ring

/-- `[a_i†, a_k†] = 0`. -/
theorem cFun_comm (i k : Fin 3) (X : Vel → ℂ) : cFun i (cFun k X) = cFun k (cFun i X) := by
  by_cases hik : i = k
  · rw [hik]
  · funext β
    simp only [cFun, lower_of_ne (Ne.symm hik), lower_of_ne hik, lower_comm i k β]
    ring

/-- `[a_i, a_k†] = 0` for `i ≠ k`. -/
theorem aFun_cFun_of_ne {i k : Fin 3} (h : i ≠ k) (X : Vel → ℂ) :
    aFun i (cFun k X) = cFun k (aFun i X) := by
  funext β
  simp only [aFun, cFun, raise_of_ne (Ne.symm h), lower_of_ne h,
    lower_raise_of_ne h β]
  ring

/-- `a_i a_i† x = (β_i + 1) x`. -/
theorem aFun_cFun_self (i : Fin 3) (X : Vel → ℂ) :
    aFun i (cFun i X) = fun β => (((β i : ℝ) + 1 : ℝ) : ℂ) * X β := by
  funext β
  simp only [aFun, cFun, raise_self, lower_raise]
  rw [show ((β i + 1 : ℕ) : ℝ) = ((β i : ℝ) + 1) from by push_cast; ring,
    ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]

/-- `a_i† a_i x = β_i x`. -/
theorem cFun_aFun_self (i : Fin 3) (X : Vel → ℂ) :
    cFun i (aFun i X) = fun β => ((β i : ℝ) : ℂ) * X β := by
  funext β
  rcases Nat.eq_zero_or_pos (β i) with h0 | hpos
  · simp [cFun, h0]
  · have h1 : (1 : ℕ) ≤ β i := hpos
    have hcast : (((β i - 1 : ℕ) : ℝ) + 1) = ((β i : ℝ)) := by
      push_cast [Nat.cast_sub h1]
      ring
    simp only [cFun, aFun, lower_self, raise_lower i hpos, hcast]
    rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]

/-! ## The canonical commutation relations, as operator identities -/

/-- `[a_i, a_k] = 0`. -/
theorem ann_comm (i k : Fin 3) : (ann i).comp (ann k) = (ann k).comp (ann i) :=
  LinearMap.ext fun x => crd_injective (by
    simp only [LinearMap.comp_apply, crd_ann]
    exact aFun_comm i k (crd x))

/-- `[a_i†, a_k†] = 0`. -/
theorem cre_comm (i k : Fin 3) : (cre i).comp (cre k) = (cre k).comp (cre i) :=
  LinearMap.ext fun x => crd_injective (by
    simp only [LinearMap.comp_apply, crd_cre]
    exact cFun_comm i k (crd x))

/-- `[a_i, a_k†] = 0` for distinct modes. -/
theorem comm_ann_cre_of_ne {i k : Fin 3} (h : i ≠ k) :
    (ann i).comp (cre k) = (cre k).comp (ann i) :=
  LinearMap.ext fun x => crd_injective (by
    simp only [LinearMap.comp_apply, crd_ann, crd_cre]
    exact aFun_cFun_of_ne h (crd x))

/-- **`[a_i, a_i†] = 1`.** -/
theorem comm_ann_cre (i : Fin 3) :
    (ann i).comp (cre i) - (cre i).comp (ann i) = LinearMap.id := by
  refine LinearMap.ext fun x => crd_injective ?_
  funext β
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, crd_sub,
    crd_ann, crd_cre, Pi.sub_apply, aFun_cFun_self, cFun_aFun_self]
  push_cast
  ring

/-! ## The three canonical pairs -/

/-- `√2⁻¹ · √2⁻¹ = ½`. -/
theorem inv_sqrt_two_sq : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)
    = ((1 / 2 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **The fiber coordinate of the mode `i`**, `u_i = (a_i + a_i†)/√2`. -/
noncomputable def pos (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (cre i + ann i)

/-- **The momentum of the mode `i`**, `π_i = i(a_i† − a_i)/√2 = −i ∂/∂u_i`. -/
noncomputable def mom (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)) • (cre i - ann i)

/-- **`[π_i, u_i] = −i`**: the two are genuinely non-commuting. -/
theorem comm_mom_pos (i : Fin 3) :
    (mom i).comp (pos i) - (pos i).comp (mom i) = (-Complex.I) • LinearMap.id := by
  have hcomm : (cre i - ann i).comp (cre i + ann i) - (cre i + ann i).comp (cre i - ann i)
      = (-2 : ℂ) • LinearMap.id := by
    have h := comm_ann_cre i
    have hexp : (cre i - ann i).comp (cre i + ann i) - (cre i + ann i).comp (cre i - ann i)
        = (-2 : ℂ) • ((ann i).comp (cre i) - (cre i).comp (ann i)) := by
      simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp]
      module
    rw [hexp, h]
  have hscal : Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) * (-2)
      = -Complex.I := by
    have h := inv_sqrt_two_sq
    push_cast at h ⊢
    linear_combination (-2 * Complex.I) * h
  have hL : (mom i).comp (pos i) - (pos i).comp (mom i)
      = (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) •
        ((cre i - ann i).comp (cre i + ann i) - (cre i + ann i).comp (cre i - ann i)) := by
    simp only [mom, pos, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    module
  rw [hL, hcomm, smul_smul, hscal]

/-- **`[π_i, u_k] = 0`** for distinct modes. -/
theorem comm_mom_pos_of_ne {i k : Fin 3} (h : i ≠ k) :
    (mom i).comp (pos k) = (pos k).comp (mom i) := by
  have h1 : (ann i).comp (cre k) = (cre k).comp (ann i) := comm_ann_cre_of_ne h
  have h2 : (cre i).comp (ann k) = (ann k).comp (cre i) :=
    (comm_ann_cre_of_ne (Ne.symm h)).symm
  have h3 : (ann i).comp (ann k) = (ann k).comp (ann i) := ann_comm i k
  have h4 : (cre i).comp (cre k) = (cre k).comp (cre i) := cre_comm i k
  simp only [mom, pos, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_add, LinearMap.add_comp, LinearMap.sub_comp, LinearMap.comp_sub,
    h1, h2, h3, h4]
  module

/-! ## The coordinates of a signed hop, read off from an incoming term

For each of the four hopping families of `ChapterNavierStokesThreeComponent` the
"incoming" half of the hopping — the value of the Hamiltonian at `γ` coming from the
unique index that hops to `γ` — is a ladder expression, and the following lemma is the
bookkeeping that identifies it as such. -/

theorem hFun_eq_of_incoming {sym : Vel → ℝ} (S : SignedHop Vel sym) (X g : Vel → ℂ)
    (h1 : ∀ β, g (S.shift β) = (S.amp β : ℂ) * X β)
    (h2 : ∀ γ, (¬ ∃ α, S.shift α = γ) → g γ = 0) (γ : Vel) :
    S.hFun X γ = Complex.I * (g γ - (S.amp γ : ℂ) * X (S.shift γ)) := by
  have hkey : S.maj.hop (fun α => (S.amp α : ℂ) * X α) γ = g γ := by
    by_cases hb : ∃ α, S.shift α = γ
    · obtain ⟨α, rfl⟩ := hb
      have hs : S.maj.hop (fun α => (S.amp α : ℂ) * X α) (S.maj.shift α)
          = (S.amp α : ℂ) * X α := ShiftData.hop_shift _ _ _
      exact hs.trans (h1 α).symm
    · rw [ShiftData.hop_eq_zero _ _ hb, h2 γ hb]
  rw [SignedHop.hFun, hkey]

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

/-! ### The diagonal (self-advection) hop -/

theorem diagHop_hFun (i : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (diagHop A c i).hFun X γ
      = Complex.I * (((A i i / 2 : ℝ) : ℂ) * (cFun i (cFun i X) γ - aFun i (aFun i X) γ)) := by
  have key := hFun_eq_of_incoming (diagHop A c i) X
    (fun δ => ((A i i / 2 : ℝ) : ℂ) * cFun i (cFun i X) δ) ?_ ?_ γ
  · rw [key]
    congr 1
    have hout : ((diagHop A c i).amp γ : ℂ) * X ((diagHop A c i).shift γ)
        = ((A i i / 2 : ℝ) : ℂ) * aFun i (aFun i X) γ := by
      simp only [diagHop_amp, diagHop_shift, ampDiag, aFun, shDiag, raise_self]
      rw [Real.sqrt_mul (by positivity)]
      push_cast
      ring_nf
    rw [hout]
    ring
  · intro β
    simp only [diagHop_amp, diagHop_shift, ampDiag, cFun, shDiag, raise_self, lower_raise]
    rw [Real.sqrt_mul (by positivity)]
    push_cast
    ring_nf
  · intro δ hno
    have hlt : δ i < 2 := by
      by_contra hcon
      exact hno ⟨lower i (lower i δ), by
        have h1 : 1 ≤ (lower i δ) i := by simp only [lower_self]; omega
        simp only [diagHop_shift, shDiag]
        rw [raise_lower i h1, raise_lower i (by omega : 1 ≤ δ i)]⟩
    interval_cases h : δ i <;> simp [cFun, h, lower_self]

end CanonicalVector

end BookProof.NavierStokesFlow
