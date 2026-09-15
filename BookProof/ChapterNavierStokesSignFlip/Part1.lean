import Mathlib
import BookProof.ChapterNavierStokesAffineBlockEsa

/-!
# The sign-flip unitary: removing the `c ≥ 0` hypothesis

`BookProof.ChapterNavierStokesAffineFiberEsa` proves that the affine
Navier–Stokes fiber Hamiltonian `H = ½(π V + V π)` with `V(u) = κ u + c` is
essentially self-adjoint on the finite-mode core of `ℓ²(ℕ)`, but only for
`c ≥ 0`: the `±1`-hopping amplitude `(c/√2)√(n+1)` of a `ShiftData` is required
to be non-negative.  The recorded remedy was the **sign-flip unitary**
`(U x)_n = (−1)ⁿ x_n`, which reverses the sign of a `±1`-hopping and preserves a
`±2`-hopping.  This module formalizes it and removes the hypothesis.

## What is proved

* `deficiencyTrivialAt_of_intertwine`, `essentiallySelfAdjointOn_of_intertwine` —
  essential self-adjointness is a unitary invariant: if a unitary `U` of the
  ambient Hilbert space preserves the core and intertwines two operators on it,
  `U ∘ T = T' ∘ U`, then `T` is essentially self-adjoint iff `T'` is;
* `flipU` — the sign-flip unitary `(U x)_β = (−1)^{p β} x_β` attached to a parity
  function `p : ι → ℕ`, a `LinearIsometryEquiv` of `ℓ²(ι)` preserving the
  finite-mode core and every maximal domain;
* `hFun_flip`, `shiftH_flip` — the conjugation rule: a shift Hamiltonian whose
  shift changes the parity by `k` is conjugated by `U` into `(−1)^k` times
  itself;
* `saffH` — the affine fiber Hamiltonian for an **arbitrary real** constant `c`
  (the `±1`-hopping amplitude is the signed `(c/√2)√(n+1)`);
* `saffH_conj_flip` — the unitary equivalence `U (affH κ |c|) U = saffH κ c` for
  `c < 0`;
* `saffH_essentiallySelfAdjointOn_core` — **the headline for one fiber**: for
  every `κ ≥ 0` and **every** `c ∈ ℝ`, the affine fiber Hamiltonian is
  essentially self-adjoint on the finite-mode core;
* `saffBlockH_essentiallySelfAdjointOn_core` — the same over the strain-rate
  spectrum: on `ℓ²(ℕ × J)`, for arbitrary families `κ ≥ 0` and `c : J → ℝ` of
  **arbitrary sign**.

## Honest boundary

`κ ≥ 0` is still assumed (the sign-flip unitary preserves the `±2`-hopping, so
it cannot remove that one; it is removed instead in
`BookProof.ChapterNavierStokesSignedShift`).  As in the modules quoted above,
everything is stated on the abstract sequence space with the operator given by
its matrix in the Hermite basis, and nothing here claims global regularity for
the classical Navier–Stokes equation.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace SignFlip

open LpNat FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

/-! ## Essential self-adjointness is a unitary invariant -/

section Transfer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- **Unitary transfer of the deficiency condition.**  If the unitary `U`
preserves the domain `D` and intertwines `T` with `T'`, then triviality of the
deficiency space of `T` at `z` implies that of `T'`. -/
theorem deficiencyTrivialAt_of_intertwine (U : F ≃ₗᵢ[ℂ] F) (T T' : D →ₗ[ℂ] F)
    (hU : ∀ v : D, U (v : F) ∈ D)
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩) (z : ℂ)
    (hT : DeficiencyTrivialAt D T z) : DeficiencyTrivialAt D T' z := by
  intro w hw
  have hw' : ∀ v : D, (inner ℂ (T v) (U.symm w) : ℂ) = z * inner ℂ (v : F) (U.symm w) := by
    intro v
    have h1 : (inner ℂ (T v) (U.symm w) : ℂ) = inner ℂ (U (T v)) w := by
      rw [← U.inner_map_map (T v) (U.symm w), U.apply_symm_apply]
    have h2 : (inner ℂ ((v : F)) (U.symm w) : ℂ) = inner ℂ (U (v : F)) w := by
      rw [← U.inner_map_map (v : F) (U.symm w), U.apply_symm_apply]
    rw [h1, h2, hcomm v]
    exact hw ⟨U (v : F), hU v⟩
  have hzero : U.symm w = 0 := hT _ hw'
  have := congrArg U hzero
  rwa [U.apply_symm_apply, map_zero] at this

/-- **Essential self-adjointness is a unitary invariant.** -/
theorem essentiallySelfAdjointOn_of_intertwine (U : F ≃ₗᵢ[ℂ] F) (T T' : D →ₗ[ℂ] F)
    (hU : ∀ v : D, U (v : F) ∈ D)
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩)
    (hT : EssentiallySelfAdjointOn D T) : EssentiallySelfAdjointOn D T' :=
  ⟨deficiencyTrivialAt_of_intertwine U T T' hU hcomm Complex.I hT.1,
   deficiencyTrivialAt_of_intertwine U T T' hU hcomm (-Complex.I) hT.2⟩

/-- **Unitary transfer of symmetry.** -/
theorem symmetricOn_of_intertwine (U : F ≃ₗᵢ[ℂ] F) (T T' : D →ₗ[ℂ] F)
    (hU : ∀ v : D, U (v : F) ∈ D) (hUsurj : ∀ v : D, ∃ u : D, U (u : F) = (v : F))
    (hcomm : ∀ v : D, U (T v) = T' ⟨U (v : F), hU v⟩)
    (hT : SymmetricOn D T) : SymmetricOn D T' := by
  intro x y
  obtain ⟨a, ha⟩ := hUsurj x
  obtain ⟨b, hb⟩ := hUsurj y
  have hx : x = ⟨U (a : F), hU a⟩ := Subtype.ext ha.symm
  have hy : y = ⟨U (b : F), hU b⟩ := Subtype.ext hb.symm
  subst hx
  subst hy
  rw [← hcomm a, ← hcomm b]
  simpa [U.inner_map_map] using hT a b

end Transfer

/-! ## The sign-flip unitary -/

variable {ι : Type*}

/-- The coordinates of the sign-flip: multiplication by `(−1)^{p β}`. -/
noncomputable def flipFun (p : ι → ℕ) (X : ι → ℂ) : ι → ℂ := fun β => (-1 : ℂ) ^ p β * X β

@[simp] theorem norm_flipFun (p : ι → ℕ) (X : ι → ℂ) (β : ι) :
    ‖flipFun p X β‖ = ‖X β‖ := by
  simp [flipFun]

theorem flipFun_flipFun (p : ι → ℕ) (X : ι → ℂ) : flipFun p (flipFun p X) = X := by
  funext β
  simp only [flipFun, ← mul_assoc, ← pow_add]
  rw [show p β + p β = 2 * p β by ring, pow_mul]
  norm_num

/-- **The sign-flip map** on `ℓ²(ι)`, as a linear map. -/
noncomputable def flipMap (p : ι → ℕ) : L2I ι →ₗ[ℂ] L2I ι where
  toFun x := ⟨flipFun p ((x : L2I ι) : ι → ℂ),
    memLpTwo_of_le x fun k => le_of_eq (norm_flipFun p _ k)⟩
  map_add' x y := by
    refine lp.ext (funext fun β => ?_)
    simp only [flipFun, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' a x := by
    refine lp.ext (funext fun β => ?_)
    simp only [flipFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem flipMap_coe (p : ι → ℕ) (x : L2I ι) (β : ι) :
    ((flipMap p x : L2I ι) : ι → ℂ) β = (-1 : ℂ) ^ p β * ((x : ι → ℂ) β) := rfl

theorem flipMap_flipMap (p : ι → ℕ) (x : L2I ι) : flipMap p (flipMap p x) = x := by
  refine lp.ext (funext fun β => ?_)
  have := congrFun (flipFun_flipFun p ((x : L2I ι) : ι → ℂ)) β
  simpa [flipMap_coe, flipFun] using this

theorem norm_flipMap (p : ι → ℕ) (x : L2I ι) : ‖flipMap p x‖ = ‖x‖ := by
  have h1 : HasSum (fun k => ‖((flipMap p x : L2I ι) : ι → ℂ) k‖ ^ 2) (‖flipMap p x‖ ^ 2) :=
    ShiftData.hasSum_normSq _
  have h2 : HasSum (fun k => ‖((flipMap p x : L2I ι) : ι → ℂ) k‖ ^ 2) (‖x‖ ^ 2) := by
    have := ShiftData.hasSum_normSq x
    refine this.congr_fun fun k => ?_
    simp [flipMap_coe]
  have hsq : ‖flipMap p x‖ ^ 2 = ‖x‖ ^ 2 := h1.unique h2
  have := abs_eq_abs.mpr (Or.inl (by nlinarith [norm_nonneg (flipMap p x), norm_nonneg x] :
    ‖flipMap p x‖ = ‖x‖))
  nlinarith [norm_nonneg (flipMap p x), norm_nonneg x, hsq]

/-- **The sign-flip unitary** `(U x)_β = (−1)^{p β} x_β` of `ℓ²(ι)`. -/
noncomputable def flipU (p : ι → ℕ) : L2I ι ≃ₗᵢ[ℂ] L2I ι where
  toLinearEquiv :=
    LinearEquiv.ofLinear (flipMap p) (flipMap p)
      (LinearMap.ext fun x => flipMap_flipMap p x) (LinearMap.ext fun x => flipMap_flipMap p x)
  norm_map' := norm_flipMap p

@[simp] theorem flipU_coe (p : ι → ℕ) (x : L2I ι) (β : ι) :
    ((flipU p x : L2I ι) : ι → ℂ) β = (-1 : ℂ) ^ p β * ((x : ι → ℂ) β) := rfl

theorem flipU_apply (p : ι → ℕ) (x : L2I ι) : flipU p x = flipMap p x := rfl

/-- The sign-flip unitary preserves the finite-mode core. -/
theorem flipU_mem_finiteModes (p : ι → ℕ) {x : L2I ι} (hx : x ∈ lpFiniteModes ι) :
    flipU p x ∈ lpFiniteModes ι := by
  refine mem_lpFiniteModes.mpr (Set.Finite.subset (mem_lpFiniteModes.mp hx) fun β hβ => ?_)
  simp only [Function.mem_support, flipU_coe, ne_eq, mul_eq_zero, not_or] at hβ
  exact hβ.2

/-- The sign-flip unitary preserves every maximal domain. -/
theorem flipU_mem_maxDom (p : ι → ℕ) (s : ι → ℝ) {x : L2I ι} (hx : x ∈ maxDom s) :
    flipU p x ∈ maxDom s := by
  refine memLpTwo_of_le (⟨fun k => (s k : ℂ) * (x : ι → ℂ) k, hx⟩ : L2I ι) fun k => ?_
  simp [flipU_coe]

/-! ## Conjugating a shift Hamiltonian -/

/-- The sign of a parity shift is `±1`. -/
theorem negOne_pow_eq (k : ℕ) : (-1 : ℂ) ^ k = 1 ∨ (-1 : ℂ) ^ k = -1 := by
  rcases Nat.even_or_odd k with hk | hk
  · exact Or.inl hk.neg_one_pow
  · exact Or.inr hk.neg_one_pow

/-- **The conjugation rule.**  If the shift raises the parity by `k`, the
sign-flip unitary conjugates the shift Hamiltonian into `(−1)^k` times
itself. -/
theorem hFun_flip (S : ShiftData ι) (p : ι → ℕ) (k : ℕ)
    (hp : ∀ β, p (S.shift β) = p β + k) (X : ι → ℂ) (β : ι) :
    S.hFun (flipFun p X) β = (-1 : ℂ) ^ k * ((-1 : ℂ) ^ p β * S.hFun X β) := by
  rcases negOne_pow_eq k with hB | hB <;>
  · by_cases hb : ∃ α, S.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      simp only [ShiftData.hFun, ShiftData.hop_shift, flipFun, hp α, hp (S.shift α),
        pow_add, hB]
      ring
    · have hz : ∀ g : ι → ℂ, S.hop g β = 0 := fun g => ShiftData.hop_eq_zero S g hb
      simp only [ShiftData.hFun, hz, flipFun, hp β, pow_add, hB]
      ring

/-- The operator form of the conjugation rule. -/
theorem shiftH_flip (S : ShiftData ι) (p : ι → ℕ) (k : ℕ)
    (hp : ∀ β, p (S.shift β) = p β + k) (x : maxDom S.sym) :
    (flipU p (ShiftData.shiftH S x) : L2I ι)
      = (-1 : ℂ) ^ k • (ShiftData.shiftH S ⟨flipU p (x : L2I ι),
          flipU_mem_maxDom p S.sym x.2⟩ : L2I ι) := by
  refine lp.ext (funext fun β => ?_)
  have hX : ((⟨flipU p (x : L2I ι), flipU_mem_maxDom p S.sym x.2⟩ :
      maxDom S.sym) : L2I ι) = flipU p (x : L2I ι) := rfl
  simp only [flipU_coe, ShiftData.shiftH_coe, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hfun : ((flipU p (x : L2I ι) : L2I ι) : ι → ℂ) = flipFun p ((x : L2I ι) : ι → ℂ) := rfl
  rw [hfun, hFun_flip S p k hp]
  rcases negOne_pow_eq k with hB | hB <;> rw [hB] <;> ring

/-! ## The affine fiber Hamiltonian with a constant of arbitrary sign -/

/-- The sign of the constant part of the fiber field, as a scalar. -/
noncomputable def esgn (c : ℝ) : ℂ := if c < 0 then -1 else 1

@[simp] theorem esgn_of_nonneg {c : ℝ} (hc : 0 ≤ c) : esgn c = 1 := by
  simp [esgn, not_lt.mpr hc]

@[simp] theorem esgn_of_neg {c : ℝ} (hc : c < 0) : esgn c = -1 := by simp [esgn, hc]

theorem esgn_eq (c : ℝ) : esgn c = 1 ∨ esgn c = -1 := by
  rcases lt_or_ge c 0 with h | h
  · exact Or.inr (esgn_of_neg h)
  · exact Or.inl (esgn_of_nonneg h)

theorem conj_esgn (c : ℝ) : (starRingEnd ℂ) (esgn c) = esgn c := by
  rcases esgn_eq c with h | h <;> simp [h]

/-- The signed `±1`-hopping amplitude: `esgn c` times the amplitude of `|c|` is
the amplitude of `c` itself. -/
theorem esgn_mul_shear (c : ℝ) (n : ℕ) :
    esgn c * ((shear |c| n : ℝ) : ℂ) = ((shear c n : ℝ) : ℂ) := by
  rcases lt_or_ge c 0 with h | h
  · rw [esgn_of_neg h, abs_of_neg h]
    simp only [shear]
    push_cast
    ring
  · rw [esgn_of_nonneg h, abs_of_nonneg h, one_mul]

/-- **The affine Navier–Stokes fiber Hamiltonian for an arbitrary real
constant** `c`: the `±2`-hopping `(κ/2)√((n+1)(n+2))` of the linear part plus the
signed `±1`-hopping `(c/√2)√(n+1)` of the constant part.  For `c ≥ 0` it is
`AffineFiber.affH`; for `c < 0` it is its conjugate by the sign-flip unitary. -/
noncomputable def saffH {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) :
    maxDom (oscSymbol (affMu κ |c|)) →ₗ[ℂ] L2I ℕ :=
  ShiftData.shiftH (affData hκ (abs_nonneg c)).fst
    + esgn c • ShiftData.shiftH (affData hκ (abs_nonneg c)).snd

theorem saffH_coe {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) (x : maxDom (oscSymbol (affMu κ |c|)))
    (β : ℕ) :
    ((saffH hκ c x : L2I ℕ) : ℕ → ℂ) β
      = (affData hκ (abs_nonneg c)).fst.hFun ((x : L2I ℕ) : ℕ → ℂ) β
        + esgn c * (affData hκ (abs_nonneg c)).snd.hFun ((x : L2I ℕ) : ℕ → ℂ) β := by
  simp only [saffH, LinearMap.add_apply, LinearMap.smul_apply, lp.coeFn_add, lp.coeFn_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- For a non-negative constant the signed Hamiltonian is the one of
`ChapterNavierStokesAffineFiberEsa`. -/
theorem saffH_eq_affH {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : 0 ≤ c) :
    saffH hκ c = affH hκ (abs_nonneg c) := by
  simp only [saffH, esgn_of_nonneg hc, one_smul]
  rfl

/-- **The affine fiber Hamiltonian is symmetric for every real constant.** -/
theorem saffH_symmetricOn {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) :
    SymmetricOn (maxDom (oscSymbol (affMu κ |c|))) (saffH hκ c) := by
  intro x y
  have h₁ := ShiftData.shiftH_symmetricOn (affData hκ (abs_nonneg c)).fst x y
  have h₂ := ShiftData.shiftH_symmetricOn (affData hκ (abs_nonneg c)).snd x y
  change (inner ℂ (saffH hκ c x : L2I ℕ) (y : L2I ℕ) : ℂ)
    = inner ℂ (x : L2I ℕ) (saffH hκ c y : L2I ℕ)
  simp only [saffH, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_esgn]
  linear_combination h₁ + esgn c * h₂

/-- **The sign-flip unitary conjugates the `|c|` fiber Hamiltonian into the `c`
fiber Hamiltonian**, for `c < 0`: it preserves the `±2`-hopping of the linear
part and reverses the `±1`-hopping of the constant part. -/
theorem saffH_conj_flip {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : c < 0)
    (x : maxDom (oscSymbol (affMu κ |c|))) :
    (flipU (fun n : ℕ => n) (affH hκ (abs_nonneg c) x) : L2I ℕ)
      = (saffH hκ c ⟨flipU (fun n : ℕ => n) (x : L2I ℕ),
          flipU_mem_maxDom _ (oscSymbol (affMu κ |c|)) x.2⟩ : L2I ℕ) := by
  refine lp.ext (funext fun β => ?_)
  have hx : ((⟨flipU (fun n : ℕ => n) (x : L2I ℕ),
      flipU_mem_maxDom _ (oscSymbol (affMu κ |c|)) x.2⟩ :
        maxDom (oscSymbol (affMu κ |c|))) : L2I ℕ) = flipU (fun n : ℕ => n) (x : L2I ℕ) := rfl
  have hfun : ((flipU (fun n : ℕ => n) (x : L2I ℕ) : L2I ℕ) : ℕ → ℂ)
      = flipFun (fun n : ℕ => n) ((x : L2I ℕ) : ℕ → ℂ) := rfl
  have hp₁ : ∀ β : ℕ, (affData hκ (abs_nonneg c)).fst.shift β = β + 2 := fun _ => rfl
  have hp₂ : ∀ β : ℕ, (affData hκ (abs_nonneg c)).snd.shift β = β + 1 := fun _ => rfl
  rw [saffH_coe, hx, hfun, hFun_flip _ (fun n : ℕ => n) 2 hp₁,
    hFun_flip _ (fun n : ℕ => n) 1 hp₂]
  have hcoord : ((affH hκ (abs_nonneg c) x : L2I ℕ) : ℕ → ℂ) β
      = (affData hκ (abs_nonneg c)).fst.hFun ((x : L2I ℕ) : ℕ → ℂ) β
        + (affData hκ (abs_nonneg c)).snd.hFun ((x : L2I ℕ) : ℕ → ℂ) β :=
    PairShift.pairH_coe (affData hκ (abs_nonneg c)) x β
  rw [flipU_coe, hcoord, esgn_of_neg hc]
  ring

/-- **The headline for one fiber.**  For every `κ ≥ 0` and **every real** `c`,
the affine Navier–Stokes fiber Hamiltonian `½(π V + V π)` with `V(u) = κ u + c`
is essentially self-adjoint on the finite-mode core of `ℓ²(ℕ)`.  The hypothesis
`c ≥ 0` of `AffineFiber.affH_essentiallySelfAdjointOn_core` is gone: for `c < 0`
the operator is the conjugate of the one for `|c|` by the sign-flip unitary. -/
theorem saffH_essentiallySelfAdjointOn_core {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((saffH hκ c).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ |c|))))) := by
  rcases lt_or_ge c 0 with hc | hc
  · refine essentiallySelfAdjointOn_of_intertwine (flipU (fun n : ℕ => n))
      ((affH hκ (abs_nonneg c)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ |c|))))) _
      (fun v => flipU_mem_finiteModes _ v.2) (fun v => ?_)
      (affH_essentiallySelfAdjointOn_core hκ (abs_nonneg c))
    exact saffH_conj_flip hκ hc _
  · rw [saffH_eq_affH hκ hc]
    exact affH_essentiallySelfAdjointOn_core hκ (abs_nonneg c)

end SignFlip

end BookProof.NavierStokesFlow
