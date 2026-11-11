import Mathlib
import BookProof.Sm.ChapterSmMatterRepresentation
import BookProof.Sm.ChapterSmDiracYukawa
import BookProof.Sm.ChapterSmGaugeRepresentation

/-!
# P1 (second half) — the Higgs realification and the four-component Yukawa dictionary

Work order: `SM_ESA_COMPLETION_PLAN.md` §4 **P1**.  `BookProof.SmMatterRepresentation` builds the
internal fermionic index set and its CAR algebra; this module completes P1's *operator data*: the
Higgs generators, their realification, and the hermitianized Yukawa dictionary the internal
matter block is built from.

## The realification of the Higgs generators

The manuscript writes the Higgs as a complex `su(2)` doublet, equivalently as **four real
components** `φ : Fin 4 → ℝ`.  The dictionary is fixed by

```text
higgsGen = ![1, σ₁, σ₂, σ₃],        higgsField φ = Σ_a φ_a · higgsGen a .
```

* `higgsGen_hermitian` — every generator is Hermitian;
* `higgsField_hermitian` — so every real combination is Hermitian, real combinations being the
  **realification** of the complex `2 × 2` matrix algebra into its Hermitian part;
* `higgsField_apply` — the entries of `Φ = φ₀ + φ₃`, `φ₁ + iφ₂`, `φ₁ - iφ₂`, `φ₀ - φ₃`; in
  particular `higgsCharged φ = φ₁ - i φ₂` is the **charged-doublet component**, which is nonzero
  for generic `φ`;
* `higgsField_injective`, `higgsField_surjective` (and hence `higgsField_existsUnique`) — the four
  real components coordinatize *exactly* the Hermitian `2 × 2` matrices: no real component is
  redundant, none is missing.

## The Yukawa dictionary

`yukawaPair A Y = A Y + (A Y)ᴴ` is the hermitianized Yukawa insertion, i.e. the Yukawa term
together with its Hermitian conjugate (`h.c.`).

* `yukawaPair_hermitian` — every insertion is Hermitian;
* `yukawaPair_sum_higgs` — **the full h.c. expression is the sum over the four real Higgs
  components**: `yukawaPair (higgsField φ) Y = Σ_a φ_a · yukawaPair (higgsGen a) Y`, with every
  summand Hermitian (`yukawaPair_higgs_gen_hermitian`);
* `yukawaPair_fixed_background`, `yukawaPair_one_pauli` — the fixed-background (`φ = e₀`) and
  single-Pauli-component models as labelled specializations; with Hermitian `Y` the
  fixed-background insertion is the mass term `2 • Y`;
* `yukawaPair_gauge` — gauge covariance: for unitary `U` (in the convention `Uᴴ U = 1`),
  `yukawaPair (U A Uᴴ) (U Y Uᴴ) = U · yukawaPair A Y · Uᴴ`;
* `yukawaPair_charge` — charge conservation: a Hermitian charge `T` commuting with `A` and `Y`
  commutes with the insertion, so its charge is conserved;
* `SmYukawaData` — the four mass/Yukawa matrices `Yu`, `Yd`, `Ye`, `Yν` together with their
  complex phases (each of unit modulus), with a nontrivial complex-mixing example
  (`exampleYukawa`) whose off-diagonal entry is `I` and whose up-type matrix is *not* Hermitian;
* `pauli_conjTranspose`, `su2gen_hermitian` — the weak generators reused from
  `BookProof.SmGaugeRepresentation` are Hermitian, so `higgsGen` is built from physical matrices
  and not arbitrary ones;
* `gaugeCurrent_bounded`, `yukawaCurrent_bounded` — the finite CAR bilinear bound
  (`BookProof.SmCar.norm_fermiBilin_le`) makes every internal one-particle operator bounded, which
  is what P2 needs for the term-by-term comparison.

## Boundary

* The dictionary is the internal `2 × 2` weak-doublet block at a fixed generation and momentum.
  It does **not** assemble the 96 matter modes into the full `Σ_{x,y} M_{xy} a†_x a_y`
  Hamiltonian, and it does not act on spinor indices: `h_Dirac = γ·∂`, the spatial derivative and
  the spinor action of `γ⁰γ·D` are P2's (and remain unformalized).
* No Majorana mass term is added: `SmYukawaData` carries only the four Dirac-Yukawa blocks.  The
  spinor representation is the real one (`C² = -1`, `BookProof.SmMatter.chargeConj_chargeConj`),
  where right-handed neutrinos are Dirac partners, not Majorana fields.
* Gauge covariance is proved for the *free* internal unitary `U` on the doublet block; the
  statement that this `U` is the exponential of the P0/P1 gauge generators (`smGen`) is not made
  here, since that needs the gauge-field sector of P2.
-/

namespace BookProof.SmFullYukawa

open scoped Matrix

open BookProof.SmCar
open BookProof.SmGaugeRep (pauli su2gen)

noncomputable section

/-! ## 1. The Higgs generators -/

/-- The Pauli matrices are Hermitian. -/
theorem pauli_conjTranspose (k : Fin 3) : (pauli k)ᴴ = pauli k := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.conjTranspose_apply]

/-- The weak generators `τ_k / 2` are Hermitian. -/
theorem su2gen_hermitian (k : Fin 3) : (su2gen k)ᴴ = su2gen k := by
  rw [su2gen, Matrix.conjTranspose_smul, pauli_conjTranspose]
  norm_num

/-- **The four Hermitian Higgs generators** `1, σ₁, σ₂, σ₃`: the realification basis of the
Hermitian `2 × 2` matrices. -/
def higgsGen : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1, pauli 0, pauli 1, pauli 2]

theorem higgsGen_hermitian (a : Fin 4) : (higgsGen a)ᴴ = higgsGen a := by
  fin_cases a
  · rw [higgsGen]
    simp
  · rw [higgsGen]
    exact pauli_conjTranspose 0
  · rw [higgsGen]
    exact pauli_conjTranspose 1
  · rw [higgsGen]
    exact pauli_conjTranspose 2

/-- **The Higgs doublet as a matrix**: the real combination `Σ_a φ_a · higgsGen a`. -/
def higgsField (φ : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ a : Fin 4, ((φ a : ℂ)) • higgsGen a

/-- **The realification is Hermitian**: real combinations of the Hermitian generators are
Hermitian. -/
theorem higgsField_hermitian (φ : Fin 4 → ℝ) : (higgsField φ)ᴴ = higgsField φ := by
  rw [higgsField, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_smul, higgsGen_hermitian]
  norm_num

/-- The explicit entries of the doublet: `Φ = φ₀ + φ₃σ₃ + φ₁σ₁ + φ₂σ₂`. -/
theorem higgsField_apply (φ : Fin 4 → ℝ) :
    higgsField φ = !![((φ 0 + φ 3 : ℝ) : ℂ), ((φ 1 : ℝ) : ℂ) - Complex.I * ((φ 2 : ℝ) : ℂ);
      ((φ 1 : ℝ) : ℂ) + Complex.I * ((φ 2 : ℝ) : ℂ), ((φ 0 - φ 3 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higgsField, higgsGen, pauli, Fin.sum_univ_four, Complex.ext_iff]
  ring

/-- **The charged-doublet component** `φ₁ - iφ₂`, the `(0,1)` entry of the doublet. -/
def higgsCharged (φ : Fin 4 → ℝ) : ℂ := ((φ 1 : ℝ) : ℂ) - Complex.I * ((φ 2 : ℝ) : ℂ)

theorem higgsField_charged (φ : Fin 4 → ℝ) : higgsField φ 0 1 = higgsCharged φ := by
  rw [higgsField_apply]
  simp [higgsCharged]

/-- The neutral component `φ₀ + φ₃`. -/
def higgsNeutral (φ : Fin 4 → ℝ) : ℂ := ((φ 0 + φ 3 : ℝ) : ℂ)

theorem higgsField_neutral (φ : Fin 4 → ℝ) : higgsField φ 0 0 = higgsNeutral φ := by
  rw [higgsField_apply]
  simp [higgsNeutral]

/-- **A nonzero charged-doublet component** at a generic point of the real four-component
space. -/
theorem higgsCharged_nonzero : higgsCharged ![0, 1, 0, 0] = 1 := by
  simp [higgsCharged]

theorem higgsCharged_ne_zero : higgsCharged ![0, 1, 0, 0] ≠ 0 := by
  rw [higgsCharged_nonzero]
  norm_num

/-- **The four real components are independent**: `higgsField` is injective. -/
theorem higgsField_injective : Function.Injective higgsField := by
  intro φ ψ h
  rw [higgsField_apply, higgsField_apply] at h
  have h00 : (φ 0 + φ 3 : ℝ) = ψ 0 + ψ 3 := by
    have := congrArg (fun M => (M 0 0).re) h
    simpa using this
  have h11 : (φ 0 - φ 3 : ℝ) = ψ 0 - ψ 3 := by
    have := congrArg (fun M => (M 1 1).re) h
    simpa using this
  have h01 : (φ 1 : ℝ) = ψ 1 := by
    have := congrArg (fun M => (M 0 1).re) h
    simpa [Complex.sub_re, Complex.mul_re, Complex.mul_im] using this
  have h02 : (φ 2 : ℝ) = ψ 2 := by
    have := congrArg (fun M => (M 0 1).im) h
    simpa [Complex.sub_im, Complex.mul_re, Complex.mul_im] using this
  have h0 : φ 0 = ψ 0 := by linarith
  have h3 : φ 3 = ψ 3 := by linarith
  funext a
  fin_cases a
  · exact h0
  · exact h01
  · exact h02
  · exact h3

/-- The coefficients of a Hermitian matrix in the realification basis. -/
def higgsCoeff (H : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![(H 0 0).re / 2 + (H 1 1).re / 2, (H 0 1).re, -(H 0 1).im,
    (H 0 0).re / 2 - (H 1 1).re / 2]

/-- A Hermitian entry of the diagonal is real. -/
theorem eq_ofReal_re_of_conjTranspose_eq {z : ℂ} (h : star z = z) : z = ((z.re : ℝ) : ℂ) := by
  have him : z.im = 0 := by
    have := congrArg Complex.im h
    simp [Complex.conj_im] at this
    linarith
  exact Complex.ext rfl (by simp [him])

/-- **Surjectivity onto the Hermitian matrices**: every Hermitian `2 × 2` matrix is a real
combination of the four generators. -/
theorem higgsField_surjective {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : Hᴴ = H) :
    higgsField (higgsCoeff H) = H := by
  have h00 : H 0 0 = ((H 0 0).re : ℂ) := by
    have h := congrFun (congrFun hH 0) 0
    simpa [Matrix.conjTranspose_apply] using eq_ofReal_re_of_conjTranspose_eq h
  have h11 : H 1 1 = ((H 1 1).re : ℂ) := by
    have h := congrFun (congrFun hH 1) 1
    simpa [Matrix.conjTranspose_apply] using eq_ofReal_re_of_conjTranspose_eq h
  have h01 : H 0 1 = ((H 0 1).re : ℂ) + Complex.I * ((H 0 1).im : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im (H 0 1)]
    ring
  have h10 : H 1 0 = ((H 0 1).re : ℂ) - Complex.I * ((H 0 1).im : ℂ) := by
    have h := congrFun (congrFun hH 1) 0
    rw [Matrix.conjTranspose_apply] at h
    rw [← h]
    conv_lhs => rw [h01]
    simp
    ring
  have hHlit : H = !![((H 0 0).re : ℂ), ((H 0 1).re : ℂ) + Complex.I * ((H 0 1).im : ℂ);
      ((H 0 1).re : ℂ) - Complex.I * ((H 0 1).im : ℂ), ((H 1 1).re : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h00
    · simpa using h01
    · simpa using h10
    · simpa using h11
  have hFlit : higgsField (higgsCoeff H) = !![((H 0 0).re : ℂ),
      ((H 0 1).re : ℂ) + Complex.I * ((H 0 1).im : ℂ);
      ((H 0 1).re : ℂ) - Complex.I * ((H 0 1).im : ℂ), ((H 1 1).re : ℂ)] := by
    rw [higgsField_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [higgsCoeff]
    all_goals ring
  rw [hFlit]
  exact hHlit.symm

/-- **The four real Higgs components coordinatize the Hermitian matrices**: existence and
uniqueness. -/
theorem higgsField_existsUnique {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : Hᴴ = H) :
    ∃! φ : Fin 4 → ℝ, higgsField φ = H := by
  refine ⟨higgsCoeff H, higgsField_surjective hH, ?_⟩
  intro φ hφ
  exact higgsField_injective (hφ.trans (higgsField_surjective hH).symm)

/-! ## 2. The Yukawa dictionary -/

/-- **The hermitianized Yukawa insertion** `A Y + (A Y)ᴴ`: the Yukawa term together with its
Hermitian conjugate. -/
def yukawaPair (A Y : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A * Y + (A * Y)ᴴ

/-- **Every Yukawa insertion is Hermitian.** -/
theorem yukawaPair_hermitian (A Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (yukawaPair A Y)ᴴ = yukawaPair A Y := by
  rw [yukawaPair, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  exact add_comm _ _

/-- A real rescaling of a Higgs generator contributes its real scalar. -/
theorem yukawaPair_ofReal_smul_higgs (c : ℝ) (a : Fin 4) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    yukawaPair (((c : ℝ) : ℂ) • higgsGen a) Y = ((c : ℝ) : ℂ) • yukawaPair (higgsGen a) Y := by
  rw [yukawaPair, yukawaPair, Matrix.smul_mul, Matrix.conjTranspose_smul, smul_add]
  simp

/-- **The full h.c. expression is the sum over the four real Higgs components.** -/
theorem yukawaPair_sum_higgs (φ : Fin 4 → ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    yukawaPair (higgsField φ) Y = ∑ a : Fin 4, ((φ a : ℂ)) • yukawaPair (higgsGen a) Y := by
  rw [higgsField, yukawaPair, Finset.sum_mul, Matrix.conjTranspose_sum]
  simp only [yukawaPair, Matrix.smul_mul, Matrix.conjTranspose_smul, smul_add,
    Finset.sum_add_distrib]
  simp

/-- Each real Higgs component contributes a Hermitian insertion. -/
theorem yukawaPair_higgs_gen_hermitian (a : Fin 4) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (yukawaPair (higgsGen a) Y)ᴴ = yukawaPair (higgsGen a) Y :=
  yukawaPair_hermitian _ _

theorem yukawaPair_zero (Y : Matrix (Fin 2) (Fin 2) ℂ) : yukawaPair 0 Y = 0 := by
  simp [yukawaPair]

/-- The unit background: `yukawaPair 1 Y = Y + Yᴴ`. -/
theorem yukawaPair_one (Y : Matrix (Fin 2) (Fin 2) ℂ) : yukawaPair 1 Y = Y + Yᴴ := by
  simp [yukawaPair]

/-- **Fixed-background specialization**: `φ = e₀` gives the unit background, so for Hermitian `Y`
the insertion is the mass term `2 • Y`. -/
theorem yukawaPair_fixed_background {Y : Matrix (Fin 2) (Fin 2) ℂ} (hY : Yᴴ = Y) :
    yukawaPair (higgsField ![1, 0, 0, 0]) Y = 2 • Y := by
  have h1 : higgsField (![1, 0, 0, 0] : Fin 4 → ℝ) = 1 := by
    rw [higgsField_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h1, yukawaPair_one, hY, two_smul]

/-- **Single-Pauli-component specialization**: a background with only `φ₁` nonzero is the
`σ₁` channel. -/
theorem yukawaPair_one_pauli (φ1 : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    yukawaPair (higgsField ![0, φ1, 0, 0]) Y = yukawaPair (((φ1 : ℝ) : ℂ) • pauli 0) Y := by
  have h1 : higgsField (![0, φ1, 0, 0] : Fin 4 → ℝ) = ((φ1 : ℝ) : ℂ) • pauli 0 := by
    rw [higgsField_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauli, Matrix.smul_apply]
  rw [h1]

/-- **Gauge covariance.** For a unitary `U` (in the convention `Uᴴ U = 1`), a gauge rotation of
both the background and the Yukawa matrix rotates the insertion: the Yukawa term is a gauge
singlet. -/
theorem yukawaPair_gauge (U A Y : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    yukawaPair (U * A * Uᴴ) (U * Y * Uᴴ) = U * yukawaPair A Y * Uᴴ := by
  have h1 : (U * A * Uᴴ) * (U * Y * Uᴴ) = U * (A * Y) * Uᴴ := by
    calc (U * A * Uᴴ) * (U * Y * Uᴴ)
        = U * (A * (Uᴴ * (U * (Y * Uᴴ)))) := by noncomm_ring
      _ = U * (A * (Y * Uᴴ)) := by
            rw [← Matrix.mul_assoc Uᴴ U (Y * Uᴴ), hU, Matrix.one_mul]
      _ = U * (A * Y) * Uᴴ := by noncomm_ring
  have h2 : (U * (A * Y) * Uᴴ)ᴴ = U * (A * Y)ᴴ * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  rw [yukawaPair, h1, h2, yukawaPair, Matrix.mul_add, Matrix.add_mul]

/-- **Charge conservation.** If a Hermitian charge `T` commutes with both the background and the
Yukawa matrix, it commutes with the insertion: the Yukawa term carries zero charge. -/
theorem yukawaPair_charge (T A Y : Matrix (Fin 2) (Fin 2) ℂ) (hT : Tᴴ = T)
    (hA : T * A = A * T) (hY : T * Y = Y * T) :
    T * yukawaPair A Y = yukawaPair A Y * T := by
  have hM : T * (A * Y) = A * Y * T := by
    calc T * (A * Y) = (T * A) * Y := by noncomm_ring
      _ = (A * T) * Y := by rw [hA]
      _ = A * (T * Y) := by noncomm_ring
      _ = A * (Y * T) := by rw [hY]
      _ = A * Y * T := by noncomm_ring
  have hMh : T * (A * Y)ᴴ = (A * Y)ᴴ * T := by
    have h1 : ((A * Y) * T)ᴴ = (T * (A * Y))ᴴ := by rw [hM]
    simp only [Matrix.conjTranspose_mul, hT] at h1
    simpa [Matrix.conjTranspose_mul] using h1
  rw [yukawaPair, Matrix.mul_add, Matrix.add_mul, hM, hMh]

/-! ## 3. The four mass/Yukawa matrices and their phases -/

/-- **The internal Yukawa data**: the four Dirac-Yukawa blocks, one per up-type quark, down-type
quark, charged lepton and neutrino, together with the complex phase of each.  There is no
right-handed Majorana block: the spinor representation here is a real one with independent
`ψ`, `ψ̅`. -/
structure SmYukawaData where
  /-- Up-type quark Yukawa matrix, in generation space. -/
  Yu : Matrix (Fin 3) (Fin 3) ℂ
  /-- Down-type quark Yukawa matrix. -/
  Yd : Matrix (Fin 3) (Fin 3) ℂ
  /-- Charged-lepton Yukawa matrix. -/
  Ye : Matrix (Fin 3) (Fin 3) ℂ
  /-- Neutrino (Dirac) Yukawa matrix. -/
  Ynu : Matrix (Fin 3) (Fin 3) ℂ
  /-- The complex phase of the up-type block. -/
  phaseU : ℂ
  /-- The complex phase of the down-type block. -/
  phaseD : ℂ
  /-- The complex phase of the charged-lepton block. -/
  phaseE : ℂ
  /-- The complex phase of the neutrino block. -/
  phaseNu : ℂ
  phaseU_unit : phaseU * star phaseU = 1
  phaseD_unit : phaseD * star phaseD = 1
  phaseE_unit : phaseE * star phaseE = 1
  phaseNu_unit : phaseNu * star phaseNu = 1

/-- The phases of the data are units: `c · c̄ = 1`. -/
theorem SmYukawaData.phaseU_unit' (d : SmYukawaData) : d.phaseU * star d.phaseU = 1 :=
  d.phaseU_unit

/-- The physical up-type Yukawa block: matrix times phase. -/
def SmYukawaData.upBlock (d : SmYukawaData) : Matrix (Fin 3) (Fin 3) ℂ := d.phaseU • d.Yu

/-- The up-type block carries a unit phase, so it is a phase rotation of the Yukawa matrix. -/
theorem SmYukawaData.upBlock_phase_unit (d : SmYukawaData) :
    d.phaseU * star d.phaseU = 1 :=
  d.phaseU_unit

/-- **A nontrivial complex-mixing example**: an up-type Yukawa matrix whose `(0,1)` entry is
`I`, i.e. maximal complex phase in one generation off-diagonal, with real diagonal. -/
def exampleYukawa : SmYukawaData where
  Yu := !![1, Complex.I, 0; 0, 1, 0; 0, 0, 1]
  Yd := !![0, 0, 0; 0, 0, 0; 0, 0, 1]
  Ye := !![0, 0, 0; 0, 0, 0; 0, 0, 1]
  Ynu := !![0, 0, 0; 0, 0, 0; 0, 0, 1]
  phaseU := 1
  phaseD := 1
  phaseE := 1
  phaseNu := 1
  phaseU_unit := by norm_num
  phaseD_unit := by norm_num
  phaseE_unit := by norm_num
  phaseNu_unit := by norm_num

/-- The example has a nonzero mixing entry. -/
theorem exampleYukawa_mixing : exampleYukawa.Yu 0 1 = Complex.I := by
  simp [exampleYukawa]

theorem exampleYukawa_mixing_ne_zero : exampleYukawa.Yu 0 1 ≠ 0 := by
  rw [exampleYukawa_mixing]
  exact Complex.I_ne_zero

/-- **Independent Hermiticity check**: the example's up-type matrix is *not* Hermitian, so the
insertion `yukawaPair` is what makes the term Hermitian, not an assumption on `Y`. -/
theorem exampleYukawa_not_hermitian : exampleYukawa.Yuᴴ ≠ exampleYukawa.Yu := by
  have hYu : exampleYukawa.Yu = !![1, Complex.I, 0; 0, 1, 0; 0, 0, 1] := rfl
  intro heq
  have h01 : (exampleYukawa.Yuᴴ) 0 1 = exampleYukawa.Yu 0 1 := congrFun (congrFun heq 0) 1
  rw [hYu] at h01
  norm_num at h01
  exact Complex.I_ne_zero h01.symm

/-- The example's insertion is nevertheless Hermitian. -/
theorem exampleYukawa_pair_hermitian (A : Matrix (Fin 2) (Fin 2) ℂ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (yukawaPair A Y)ᴴ = yukawaPair A Y :=
  yukawaPair_hermitian A Y

/-! ## 4. Bounded internal currents -/

/-- **The second quantized gauge generator is bounded**, uniformly in the state: this is the
finite-dimensional bound P2's term-by-term comparison uses. -/
theorem gaugeCurrent_bounded (S3 : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ) (y : ℝ) (a : Fin 12) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : FermiFock 6,
      ‖fermiBilin (BookProof.SmGaugeRep.smGen S3 y a) ψ‖ ≤ C * ‖ψ‖ := by
  refine ⟨∑ i : Fin 6, ∑ j : Fin 6,
    ‖BookProof.SmGaugeRep.smGen S3 y a i j‖, ?_, ?_⟩
  · positivity
  · intro ψ
    exact norm_fermiBilin_le _ ψ

/-- **The second quantized Yukawa matrix is bounded**, with the same `ℓ¹` constant. -/
theorem yukawaCurrent_bounded (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : FermiFock n, ‖fermiBilin M ψ‖ ≤ C * ‖ψ‖ := by
  refine ⟨∑ i : Fin n, ∑ j : Fin n, ‖M i j‖, ?_, ?_⟩
  · positivity
  · intro ψ
    exact norm_fermiBilin_le _ ψ

end

end BookProof.SmFullYukawa
