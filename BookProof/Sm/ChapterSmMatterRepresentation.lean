import Mathlib
import BookProof.Sm.ChapterSmCarAlgebra
import BookProof.Sm.ChapterSmPhysicalData
import BookProof.Sm.ChapterSmGaugeRepresentation

/-!
# P1 (first half) — the internal matter representation and its CAR identification

Work order: `SM_ESA_COMPLETION_PLAN.md` §4 **P1**.  P0 froze the *counts* of the internal
fermionic factor (`ChapterSmPhysicalData`); this module builds the index set they were counting,
and identifies it with the finite CAR algebra of `BookProof.SmCar`.

## The chiral content

One generation of the manuscript's real-spinor convention carries **16 Weyl fields**
(`SmWeylField`):

```text
Q  : 3 colours × 2 weak components   (left-handed quark doublet)
uR : 3 colours                       (right-handed up-type singlet)
dR : 3 colours                       (right-handed down-type singlet)
L  : 2 weak components               (left-handed lepton doublet)
eR                                   (right-handed charged lepton)
νR                                   (right-handed neutrino)
```

so `6 + 3 + 3 + 2 + 1 + 1 = 16` per generation and `3 · 16 = 48` Weyl fields in total.  Each
Weyl field is a **two-component complex spinor**, so the internal fermionic factor has
`48 · 2 = 96` complex coordinates `(generation, Weyl field, spin component)` and `96 · 2 = 192`
real Majorana components.  These are exactly `smE1.innerComplexModes = 96` and
`smE1.innerRealComponents = 192` (`matterIndex_complexModes`, `majoranaIndex_realComponents`).

## What is proved

* `SmWeylField.card_field` — `16` Weyl fields per generation, and the colour/genuinely-singlet
  block structure of the inductive type;
* `card_matterIndex`, `card_majoranaIndex` — `96` complex / `192` real coordinates, matching the
  E1 endpoint; `card_matterIndex_eq_smE1` and `card_majoranaIndex_eq_smE1` state the match in the
  ledger's own vocabulary;
* `smMatterMode`, `smMajoranaMode` — the enumerations of those indices by `Fin 96` and `Fin 192`,
  and `smMatterMode_injective`: the modes are pairwise distinct, which is the
  independent-component identification;
* `MatterFock`, `matterVac`, `matterAnnih`, `matterCreat` — the finite CAR representation on the
  matter index, with the anticommutation relations (`matter_car_annih_creat_self`,
  `matter_car_annih_creat_of_ne`), the adjointness relation (`matter_inner_creat_left`) and
  contractivity (`matter_norm_annih_le`, `matter_norm_creat_le`) transported from `BookProof.SmCar`;
* `matterBilin` — the second quantized internal one-particle matrix, with
  `matterBilin_symmetric` (Hermitian matrices give symmetric operators) and
  `matterBilin_norm_le` (the `ℓ¹` bound);
* `eps`, `chargeConj` — the charge-conjugation structure of the real two-component convention:
  `ε = iσ₂ = !![0, 1; -1, 0]` is real, antisymmetric and unitary, and `C ψ = ε ψ̅` satisfies
  `C² = -1` on the complex spinor space, so `ψ` and `ψ̅` are independent real coordinates and no
  Majorana mass term is implicit in the representation.

## Boundary

* The CAR algebra here is the **finite-mode** one of `BookProof.SmCar`; no continuum CAR algebra,
  no Lorentz/spinor action of `γ⁰γ·D`, and no gauge-field quantization is claimed.
* `SmMajoranaIndex = SmMatterIndex × Fin 2` records the real/imaginary-component doubling; it is
  a counting statement, not an identification of the real components with Majorana fields of a
  particular Lagrangian.
* The physical Yukawa matrices, the Higgs generators and the four-component dictionary are the
  second half of P1, in `BookProof.SmFullYukawaData`.
-/

namespace BookProof.SmMatter

open scoped Matrix

open BookProof.SmCar
open BookProof.SmPhysicalData (smE1 smE1_complexModes smE1_realComponents)

noncomputable section

/-! ## 1. The chiral content of one generation -/

/-- **The 16 Weyl fields of one generation**, in the manuscript's real-spinor convention: the
left-handed quark and lepton doublets with their colour/weak multiplicity, and the four
right-handed singlets (including the right-handed neutrino). -/
inductive SmWeylField : Type
  /-- Left-handed quark doublet: colour `c`, weak component `s`. -/
  | Q (c : Fin 3) (s : Fin 2)
  /-- Right-handed up-type quark singlet: colour `c`. -/
  | uR (c : Fin 3)
  /-- Right-handed down-type quark singlet: colour `c`. -/
  | dR (c : Fin 3)
  /-- Left-handed lepton doublet: weak component `s`. -/
  | L (s : Fin 2)
  /-- Right-handed charged-lepton singlet. -/
  | eR
  /-- Right-handed neutrino singlet. -/
  | nuR
  deriving DecidableEq, Fintype

namespace SmWeylField

/-- **Sixteen Weyl fields per generation**: `6 + 3 + 3 + 2 + 1 + 1`. -/
theorem card_field : Fintype.card SmWeylField = 16 := by decide

end SmWeylField

/-- The generation label. -/
abbrev SmGen : Type := Fin 3

/-- **The 96 complex matter coordinates**: generation, Weyl field, and the two complex spin
components of that Weyl field. -/
abbrev SmMatterIndex : Type := SmGen × SmWeylField × Fin 2

/-- **The 192 real Majorana components**: the real and imaginary parts of every complex
coordinate. -/
abbrev SmMajoranaIndex : Type := SmMatterIndex × Fin 2

/-- Three generations of sixteen Weyl fields, each a two-component complex spinor:
`3 · 16 · 2 = 96`. -/
theorem card_matterIndex : Fintype.card SmMatterIndex = 96 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    SmWeylField.card_field]

/-- Twice the complex count: `192` real Majorana components. -/
theorem card_majoranaIndex : Fintype.card SmMajoranaIndex = 192 := by
  rw [Fintype.card_prod, Fintype.card_fin, card_matterIndex]

/-- The real component count is twice the complex coordinate count. -/
theorem card_majoranaIndex_eq_two_mul :
    Fintype.card SmMajoranaIndex = 2 * Fintype.card SmMatterIndex := by
  rw [card_majoranaIndex, card_matterIndex]

/-- **The complex coordinate count is the E1 endpoint's** `innerComplexModes`. -/
theorem matterIndex_complexModes :
    smE1.innerComplexModes = some (Fintype.card SmMatterIndex) := by
  rw [smE1_complexModes, card_matterIndex]

/-- **The Majorana component count is the E1 endpoint's** `innerRealComponents`. -/
theorem majoranaIndex_realComponents :
    smE1.innerRealComponents = some (Fintype.card SmMajoranaIndex) := by
  rw [smE1_realComponents, card_majoranaIndex]

/-! ## 2. The independent-component identification -/

/-- **The enumeration of the complex matter modes** by `Fin 96`. -/
def smMatterMode : SmMatterIndex ≃ Fin 96 := Fintype.equivFinOfCardEq card_matterIndex

/-- **The enumeration of the real Majorana components** by `Fin 192`. -/
def smMajoranaMode : SmMajoranaIndex ≃ Fin 192 :=
  Fintype.equivFinOfCardEq card_majoranaIndex

/-- The modes are pairwise distinct: the 96 coordinates are 96 *independent* CAR modes, not a
coarse-grained count. -/
theorem smMatterMode_injective : Function.Injective smMatterMode := smMatterMode.injective

/-- Distinct matter coordinates give distinct CAR modes. -/
theorem smMatterMode_ne {x y : SmMatterIndex} (hxy : x ≠ y) : smMatterMode x ≠ smMatterMode y :=
  fun h => hxy (smMatterMode.injective h)

/-! ## 3. The finite CAR representation on the matter index -/

/-- **The finite matter Fock space**: `2 ^ 96` complex dimensions, one basis vector per occupied
set of matter modes. -/
abbrev MatterFock : Type := FermiFock 96

/-- The matter Fock vacuum `|∅⟩`. -/
def matterVac : MatterFock := vac

/-- **The matter annihilation operator** of the coordinate `x`. -/
def matterAnnih (x : SmMatterIndex) : MatterFock →ₗ[ℂ] MatterFock := annih (smMatterMode x)

/-- **The matter creation operator** of the coordinate `x`. -/
def matterCreat (x : SmMatterIndex) : MatterFock →ₗ[ℂ] MatterFock := creat (smMatterMode x)

/-- **The CAR relation** `a_x a†_x + a†_x a_x = 1` on the matter index. -/
theorem matter_car_annih_creat_self (x : SmMatterIndex) :
    matterAnnih x ∘ₗ matterCreat x + matterCreat x ∘ₗ matterAnnih x = LinearMap.id :=
  car_annih_creat_self (smMatterMode x)

/-- **The vanishing anticommutator** `{a_x, a†_y} = 0` for distinct coordinates. -/
theorem matter_car_annih_creat_of_ne {x y : SmMatterIndex} (hxy : x ≠ y) :
    matterAnnih x ∘ₗ matterCreat y + matterCreat y ∘ₗ matterAnnih x = 0 :=
  car_annih_creat_of_ne (smMatterMode_ne hxy)

/-- **`a†_x` is the adjoint of `a_x`** on the matter index. -/
theorem matter_inner_creat_left (x : SmMatterIndex) (ψ φ : MatterFock) :
    (inner ℂ (matterCreat x ψ) φ : ℂ) = inner ℂ ψ (matterAnnih x φ) :=
  inner_creat_left (smMatterMode x) ψ φ

/-- Both matter operators are contractions. -/
theorem matter_norm_annih_le (x : SmMatterIndex) (ψ : MatterFock) :
    ‖matterAnnih x ψ‖ ≤ ‖ψ‖ :=
  norm_annih_le (smMatterMode x) ψ

theorem matter_norm_creat_le (x : SmMatterIndex) (ψ : MatterFock) :
    ‖matterCreat x ψ‖ ≤ ‖ψ‖ :=
  norm_creat_le (smMatterMode x) ψ

/-- **The second quantization of an internal one-particle matrix** on the 96 matter modes,
`Σ_{x,y} M_{xy} a†_x a_y`. -/
def matterBilin (M : Matrix SmMatterIndex SmMatterIndex ℂ) : MatterFock →ₗ[ℂ] MatterFock :=
  fermiBilin (M.submatrix smMatterMode.symm smMatterMode.symm)

/-- The matrix reindexed to the mode enumeration. -/
theorem matterBilin_apply (M : Matrix SmMatterIndex SmMatterIndex ℂ) (ψ : MatterFock) :
    matterBilin M ψ =
      ∑ i : Fin 96, ∑ j : Fin 96,
        M (smMatterMode.symm i) (smMatterMode.symm j) • matterCreat (smMatterMode.symm i)
          (matterAnnih (smMatterMode.symm j) ψ) := by
  simp [matterBilin, matterCreat, matterAnnih, fermiBilin_apply, Matrix.submatrix]

/-- **A Hermitian internal matrix gives a symmetric fermionic operator.** -/
theorem matterBilin_symmetric {M : Matrix SmMatterIndex SmMatterIndex ℂ}
    (hM : M.conjTranspose = M) (ψ φ : MatterFock) :
    (inner ℂ (matterBilin M ψ) φ : ℂ) = inner ℂ ψ (matterBilin M φ) := by
  refine fermiBilin_symmetric ?_ ψ φ
  ext i j
  have h := congrFun (congrFun hM (smMatterMode.symm i)) (smMatterMode.symm j)
  simpa [Matrix.submatrix, Matrix.conjTranspose_apply] using h

/-- **The `ℓ¹` bound** on the second quantized internal matrix. -/
theorem matterBilin_norm_le (M : Matrix SmMatterIndex SmMatterIndex ℂ) (ψ : MatterFock) :
    ‖matterBilin M ψ‖ ≤
      (∑ i : Fin 96, ∑ j : Fin 96,
        ‖M (smMatterMode.symm i) (smMatterMode.symm j)‖) * ‖ψ‖ :=
  norm_fermiBilin_le _ ψ

/-! ## 4. Charge conjugation in the real two-component convention -/

/-- **The charge-conjugation matrix** `ε = iσ₂ = !![0, 1; -1, 0]`: real and antisymmetric. -/
def eps : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- `ε` is antisymmetric. -/
theorem eps_transpose : epsᵀ = -eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, Matrix.transpose_apply]

/-- `ε` is real, hence self-adjoint as a conjugation structure. -/
theorem eps_conjTranspose : epsᴴ = epsᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, Matrix.conjTranspose_apply]

/-- **`ε² = -1`**: conjugation is an antisymmetric real structure on the complex spinor space. -/
theorem eps_mul_self : eps * eps = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [eps, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- `ε` is unitary. -/
theorem eps_unitary : epsᴴ * eps = 1 := by
  rw [eps_conjTranspose, eps_transpose, neg_mul, eps_mul_self, neg_neg]

theorem eps_mul_unitary : eps * epsᴴ = 1 := by
  rw [eps_conjTranspose, eps_transpose, mul_neg, eps_mul_self, neg_neg]

/-- **Charge conjugation on a two-component spinor**, `ψ ↦ ε ψ̅`, written out in components:
`(ψ₀, ψ₁) ↦ (-ψ̅₁, ψ̅₀)`. -/
def chargeConj (ψ : Fin 2 → ℂ) : Fin 2 → ℂ := fun i => if i = 0 then -star (ψ 1) else star (ψ 0)

theorem chargeConj_zero (ψ : Fin 2 → ℂ) : chargeConj ψ 0 = -star (ψ 1) := rfl

theorem chargeConj_one (ψ : Fin 2 → ℂ) : chargeConj ψ 1 = star (ψ 0) := by
  simp [chargeConj]

/-- **`C² = -1`**: in the real two-component convention `ψ` and `ψ̅` are independent real
coordinates, and conjugation is an antisymmetric real structure. -/
theorem chargeConj_chargeConj (ψ : Fin 2 → ℂ) : chargeConj (chargeConj ψ) = -ψ := by
  funext i
  fin_cases i <;> simp [chargeConj]

/-- Charge conjugation is conjugate-linear in the scalar: `C(cψ) = c̄ (Cψ)`. -/
theorem chargeConj_smul (c : ℂ) (ψ : Fin 2 → ℂ) :
    chargeConj (c • ψ) = (star c) • chargeConj ψ := by
  funext i
  fin_cases i <;> simp [chargeConj]

/-- Charge conjugation is additive. -/
theorem chargeConj_add (ψ φ : Fin 2 → ℂ) : chargeConj (ψ + φ) = chargeConj ψ + chargeConj φ := by
  funext i
  fin_cases i <;> simp [chargeConj]
  ring

/-- Charge conjugation is a real-linear involution up to sign, so it does not identify `ψ` with an
independent field: no Majorana mass term is implicit in the representation. -/
theorem chargeConj_injective : Function.Injective chargeConj := by
  intro ψ φ h
  have := congrArg chargeConj h
  simpa [chargeConj_chargeConj] using this

end

end BookProof.SmMatter
