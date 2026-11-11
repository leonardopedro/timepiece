import Mathlib
import BookProof.Sm.ChapterSmFarisLavine
import BookProof.Sm.ChapterSmMatterRepresentation
import BookProof.Sm.ChapterSmFullYukawaData
import BookProof.Qym.ChapterYangMillsHermite

/-!
# P2 — the exact coupled inner operator on a common Mehler core

Work order: `SM_ESA_COMPLETION_PLAN.md` §4 **P2**, "construct the exact coupled inner operator
on a common Mehler core".  The object is the E1 inner operator of `ChapterSmPhysicalData`

```text
h_SM = h_B ⊗ 1
     + Σⱼ p_xⱼ ⊗ Aⱼ          -- spatial derivative, internal Hermitian coefficient
     + Σ_(field coordinates r) qᵣ ⊗ Jᵣ
     + Σ_(a : Fin 4) φₐ ⊗ Yₐ   -- the four real Higgs components
     + 1 ⊗ M₀,
```

on the **common core** `D_SM = polyGaussCore 163 ⊗ F_internal`, where `F_internal` is the matter
Fock space of P1 (`MatterFock = FermiFock 96`, one basis vector per occupied set of the 96 complex
CAR coordinates).

## What this module builds

1. **The coupled space** `L²(ℝ¹⁶³) ⊗ F_internal`, modelled as the finite `ℓ²` direct sum
   `PiLp 2 (fun _ : Finset (Fin 96) => L2d 163)` over the occupation basis — the tensor product
   with a finite-dimensional factor, whose inner product is `Σ_S ⟪f_S, g_S⟫` by
   `PiLp.inner_apply`.  The index is the occupation basis `Finset (Fin 96)` rather than
   `MatterFock` because the latter is the type synonym `Finset (Fin 96) → ℂ` and carries no
   `Fintype` instance; the two are the same direct sum.
2. **The common core** `SmCoupledCore` (every internal component in the Gauss–polynomial core),
   with **`coupledSpace_norm_sq`** (`‖f‖² = Σ_S ‖f_S‖²`) and **`coupledCore_dense`**: the core is
   dense in the coupled space.  Density is the finite-`ℓ²` reassembly of the one-particle density
   `polyGaussCore_dense`, not a new analytic input.
3. **Fermion parity** `fockParity = (-1)^N` on `MatterFock`: the sign, the operator, its
   involution, its symmetry and norm preservation, and the anticommutation
   `P a_i = −a_i P`, `P a†_i = −a†_i P`, whence **`matterBilin` preserves parity**
   (`matterBilin_parity`).
4. The **elementary tensor** `smTensorCore T M` (`T ⊗ M`) on the coupled core: core-invariant by
   construction (the bosonic factor is core-to-core), with symmetry `smTensorCore_symmetricOn'`
   from the one-particle symmetry `SymmetricOn` and Hermiticity of the internal matrix, closed
   under addition (`symmetricOn_add`) and finite sums (`symmetricOn_sum`).
5. The ledger factors on the core — `smMom` (`πⱼ = −i∂ⱼ` via `CoreRep.op momOp`), `smPos`
   (`uⱼ`), `smKinetic` (`πⱼ²`) — their symmetries (`smMom_symmetricOn`, `smPos_symmetricOn`,
   `smKinetic_symmetricOn` via `symmetricOn_comp_self`), the **normal form** `smNormalForm` with
   its elementary-tensor action `smNormalForm_apply` (term by term), its symmetry
   `smNormalForm_symmetricOn` under `HermitianCoeffs`, and its commutation with fermion parity
   `smNormalForm_parity` under `ParityGradedCoeffs`.

## The Mehler dictionary used here

`polyGaussCore 163` is `range pgMap`, i.e. the vectors `p(x)·e^{-‖x‖²/4}` in **Lebesgue** `L²`,
with the Hermite variance and coordinate scale fixed by `pgFun`/`pgLp`.  The multiplication
operator `mulOp (X j)` and the momentum `momOp j = −i(∂_j − ½x_j)` are the transport of the
coordinate and derivative on that core, so the Gaussian weight `e^{-‖x‖²/4}` is the
*representation* weight, not a physical Higgs or gauge background, and its vacuum is not the
physical outer vacuum.

## Honest boundary

This module does **not** claim that the block embedding of the four real Higgs components (and of
the gauge generators) into the 96-mode internal factor is derived from the manuscript: the
coefficient matrices are the data `SmNormalFormData` carries.  The P1 dictionary
(`yukawaPair`, `SmYukawaData`) *is* the four-component h.c. expression, but it acts on the doublet
`2 × 2` factor, not yet on all 96 modes; the embedding of those doublets into the 96-mode internal
matrix data of `SmNormalFormData` is not derived here.  Nor does it claim the spinor action of
`γ·∂` (`h_Dirac` is still not an operator, so the `p_x ⊗ A` term is proved for a declared
Hermitian coefficient matrix `Aⱼ`), the gauge-field sector (the `q_r ⊗ J_r` generators are data,
as P5's gauge action is not built), or any common-core graph statement, essential self-adjointness
or Faris–Lavine comparison — those are P3/P4, and nothing here assumes them.
-/

namespace BookProof.SmFullMatter

open MeasureTheory BookProof.HermiteProductCore BookProof.SmCar BookProof.SmMatter
open BookProof.FarisLavine BookProof.YangMillsHermite

noncomputable section

/-! ## 1. Fermion parity on the matter Fock space -/

/-- The parity sign `(-1)^{#S}` of an occupation state `S`. -/
def fockSign (S : Finset (Fin 96)) : ℂ := (-1) ^ S.card

theorem fockSign_mul_self (S : Finset (Fin 96)) : fockSign S * fockSign S = 1 := by
  simp [fockSign, ← pow_add, ← two_mul, pow_mul]

@[simp] theorem conj_fockSign (S : Finset (Fin 96)) :
    (starRingEnd ℂ) (fockSign S) = fockSign S := by
  simp [fockSign]

@[simp] theorem norm_fockSign (S : Finset (Fin 96)) : ‖fockSign S‖ = 1 := by
  simp [fockSign]

/-- **The fermion-parity operator** `(-1)^N`: diagonal in the occupation basis. -/
def fockParity : MatterFock →ₗ[ℂ] MatterFock where
  toFun ψ := WithLp.toLp 2 (fun S => fockSign S * ψ S)
  map_add' x y := by
    ext S
    simp [mul_add]
  map_smul' c x := by
    ext S
    simp [mul_left_comm]

@[simp] theorem fockParity_apply (ψ : MatterFock) (S : Finset (Fin 96)) :
    fockParity ψ S = fockSign S * ψ S := rfl

/-- The parity operator is an involution. -/
theorem fockParity_involutive : fockParity ∘ₗ fockParity = LinearMap.id := by
  refine LinearMap.ext fun ψ => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  ext S
  rw [fockParity_apply, fockParity_apply, ← mul_assoc, fockSign_mul_self, one_mul]

/-- **Parity is symmetric** for the occupation-basis inner product. -/
theorem fockParity_symmetric (ψ φ : MatterFock) :
    (inner ℂ (fockParity ψ) φ : ℂ) = inner ℂ ψ (fockParity φ) := by
  rw [inner_eq_sum, inner_eq_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [fockParity_apply, fockParity_apply, map_mul, conj_fockSign]
  ring

/-- Parity preserves the norm: it is a real diagonal sign. -/
theorem fockParity_norm (ψ : MatterFock) : ‖fockParity ψ‖ = ‖ψ‖ := by
  have h2 : ‖fockParity ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [normSq_eq_sum, normSq_eq_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [fockParity_apply, norm_mul, norm_fockSign, one_mul]
  calc ‖fockParity ψ‖ = Real.sqrt (‖fockParity ψ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖ψ‖ ^ 2) := by rw [h2]
    _ = ‖ψ‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Parity anticommutes with annihilation**: `P a_i = −a_i P`. -/
theorem fockParity_annih_apply (i : Fin 96) (ψ : MatterFock) :
    fockParity (annih i ψ) = -(annih i (fockParity ψ)) := by
  ext S
  by_cases h : i ∈ S
  · simp [annih_apply, h]
  · have hcard : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem h
    simp only [annih_apply, h, if_false, fockParity_apply, PiLp.neg_apply, hcard, pow_succ,
      fockSign]
    ring

theorem fockParity_annih (i : Fin 96) : fockParity ∘ₗ annih i = -(annih i ∘ₗ fockParity) :=
  LinearMap.ext fun ψ => fockParity_annih_apply i ψ

/-- **Parity anticommutes with creation**: `P a†_i = −a†_i P`. -/
theorem fockParity_creat_apply (i : Fin 96) (ψ : MatterFock) :
    fockParity (creat i ψ) = -(creat i (fockParity ψ)) := by
  ext S
  by_cases h : i ∈ S
  · have hcard := Finset.card_erase_of_mem h
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, h⟩
    have hsign : fockSign S = -(fockSign (S.erase i)) := by
      have hsucc : S.card = (S.erase i).card + 1 := by
        rw [hcard]
        exact (Nat.sub_add_cancel hpos).symm
      simp only [fockSign, hsucc, pow_succ]
      ring
    rw [fockParity_apply, creat_apply, if_pos h, PiLp.neg_apply, creat_apply, if_pos h,
      fockParity_apply, hsign]
    ring
  · rw [fockParity_apply, creat_apply, if_neg h, mul_zero, PiLp.neg_apply, creat_apply, if_neg h,
      neg_zero]

theorem fockParity_creat (i : Fin 96) : fockParity ∘ₗ creat i = -(creat i ∘ₗ fockParity) :=
  LinearMap.ext fun ψ => fockParity_creat_apply i ψ

/-- **A bilinear fermionic operator preserves parity** — the composition of one creation and
one annihilation carries two anticommuting signs, hence is parity-even. -/
theorem fockParity_fermiBilin (h : Matrix (Fin 96) (Fin 96) ℂ) :
    fockParity ∘ₗ fermiBilin h = fermiBilin h ∘ₗ fockParity := by
  have hterm : ∀ (i j : Fin 96) (ψ : MatterFock),
      fockParity (creat i (annih j ψ)) = creat i (annih j (fockParity ψ)) := by
    intro i j ψ
    rw [fockParity_creat_apply i (annih j ψ), fockParity_annih_apply j ψ]
    simp only [map_neg, neg_neg]
  refine LinearMap.ext fun ψ => ?_
  simp only [LinearMap.comp_apply, fermiBilin_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hterm]

/-- **The second-quantized internal matrix preserves fermion parity.** -/
theorem matterBilin_parity (M : Matrix SmMatterIndex SmMatterIndex ℂ) :
    fockParity ∘ₗ matterBilin M = matterBilin M ∘ₗ fockParity := by
  have := fockParity_fermiBilin (M.submatrix smMatterMode.symm smMatterMode.symm)
  simpa only [matterBilin] using this

/-! ## 2. The coupled space and the common core -/

/-- The bosonic one-particle space `L²(ℝ¹⁶³)`. -/
abbrev SmBosSpace : Type := L2d 163

/-- **The coupled space** `L²(ℝ¹⁶³) ⊗ F_internal` with the finite internal factor, realized as
the finite `ℓ²` direct sum over the occupation basis `Finset (Fin 96)` of `MatterFock`. -/
abbrev SmCoupledSpace : Type := PiLp 2 (fun _ : Finset (Fin 96) => SmBosSpace)

/-- **The common core** `D_SM = polyGaussCore 163 ⊗ F_internal`: the coupled vectors whose every
internal component is a polynomial times `e^{-‖x‖²/4}`. -/
def SmCoupledCore : Submodule ℂ SmCoupledSpace where
  carrier :=
    {f | ∀ S : Finset (Fin 96), f.ofLp S ∈ (polyGaussCore (d := 163) : Set SmBosSpace)}
  add_mem' := by
    intro f g hf hg S
    rw [PiLp.add_apply]
    exact (polyGaussCore (d := 163)).add_mem (hf S) (hg S)
  zero_mem' := by
    intro S
    rw [PiLp.zero_apply]
    exact (polyGaussCore (d := 163)).zero_mem
  smul_mem' := by
    intro c f hf S
    rw [PiLp.smul_apply]
    exact (polyGaussCore (d := 163)).smul_mem c (hf S)

/-- Extensionality on the coupled core, componentwise. -/
theorem coupledCore_ext {f g : SmCoupledCore}
    (h : ∀ S : Finset (Fin 96), (f : SmCoupledSpace).ofLp S = (g : SmCoupledSpace).ofLp S) :
    f = g :=
  Subtype.ext (WithLp.ofLp_injective 2 (funext h))

set_option maxRecDepth 2000 in
/-- **The `ℓ²` norm identity of the coupled space**: `‖f‖² = Σ_S ‖f_S‖²`. -/
theorem coupledSpace_norm_sq (f : SmCoupledSpace) :
    ‖f‖ ^ 2 = ∑ S, ‖f.ofLp S‖ ^ 2 := by
  have hE : (2 : ENNReal).toReal = 2 := by norm_num
  rw [PiLp.norm_eq_sum (p := 2) (β := fun _ : Finset (Fin 96) => SmBosSpace)
    (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) f, hE, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_ofNat]
  exact Real.sq_sqrt (Finset.sum_nonneg (fun S _ => sq_nonneg (‖f.ofLp S‖)))

/-- **The common core is dense in the coupled space.**  The proof is the finite-`ℓ²` reassembly
of the one-particle density `polyGaussCore_dense`: each of the finitely many internal components
is approximated in its own Gauss–polynomial core, and the errors add in `ℓ²`. -/
theorem coupledCore_dense : Dense (SmCoupledCore : Set SmCoupledSpace) := by
  classical
  rw [Metric.dense_iff]
  intro g r hr
  set N : ℝ := (Fintype.card (Finset (Fin 96)) : ℝ) with hN
  set n : ℝ := N + 1 with hn
  have hNpos : 0 < N := by
    rw [hN]
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨∅⟩)
  have hnpos : 0 < n := by rw [hn]; linarith
  set δ : ℝ := r / n with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hex : ∀ S : Finset (Fin 96), ∃ f : SmBosSpace,
      f ∈ (polyGaussCore (d := 163) : Set SmBosSpace) ∧ dist f (g.ofLp S) < δ := by
    intro S
    obtain ⟨f, hf⟩ :=
      Metric.dense_iff.mp (polyGaussCore_dense (d := 163)) (g.ofLp S) δ hδpos
    rw [Set.mem_inter_iff, Metric.mem_ball] at hf
    exact ⟨f, hf.2, hf.1⟩
  choose f hfmem hfdist using hex
  have hcore : (WithLp.toLp 2 (fun S => f S) : SmCoupledSpace) ∈
      (SmCoupledCore : Set SmCoupledSpace) := by
    intro S
    simpa using hfmem S
  have hball : (WithLp.toLp 2 (fun S => f S) : SmCoupledSpace) ∈ Metric.ball g r := by
    rw [Metric.mem_ball, dist_eq_norm]
    set e : SmCoupledSpace := WithLp.toLp 2 (fun S => f S) - g with he
    have hcomp : ∀ S : Finset (Fin 96), ‖e.ofLp S‖ < δ := by
      intro S
      rw [he, PiLp.sub_apply]
      simpa [dist_eq_norm] using hfdist S
    have hle : ∑ S, ‖e.ofLp S‖ ^ 2 ≤ ∑ _S : Finset (Fin 96), δ ^ 2 :=
      Finset.sum_le_sum fun S _ => by
        nlinarith [norm_nonneg (e.ofLp S), hcomp S, hδpos]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN] at hle
    have hNn : N < n := by rw [hn]; linarith
    have hprod : N * δ ^ 2 < n * δ ^ 2 :=
      mul_lt_mul_of_pos_right hNn (by rw [hδ]; positivity)
    have hn0 : n ≠ 0 := ne_of_gt hnpos
    have hdiv : n * δ ^ 2 = r ^ 2 / n := by
      rw [hδ]
      field_simp
    have hn1 : 1 < n := by rw [hn]; linarith
    have hlt : n * δ ^ 2 < r ^ 2 := by
      rw [hdiv, div_lt_iff₀ hnpos]
      nlinarith [sq_pos_of_pos hnpos, sq_pos_of_pos hr]
    have hsum : ∑ S, ‖e.ofLp S‖ ^ 2 < r ^ 2 := by linarith
    have hsq : ‖e‖ ^ 2 < r ^ 2 := by
      rw [coupledSpace_norm_sq]
      exact hsum
    have hpos : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
    have hnlt : ‖e‖ < r := by nlinarith
    rw [he] at hnlt
    exact hnlt
  refine ⟨WithLp.toLp 2 (fun S => f S), ?_⟩
  rw [Set.mem_inter_iff]
  exact ⟨hball, hcore⟩

/-! ## 3. The tensor factors on the common core

Every term of the ledger is an elementary tensor `T ⊗ M`: a bosonic one-particle operator `T` on
the Gauss–polynomial core tensored with an internal coefficient matrix `M` on the occupation
basis.  Because `T` is taken *core to core* (the output of `CoreRep.op`), the core is invariant
under every term by construction, not by a new definition. -/

/-- **The `B`-th internal component of a coupled core vector**, as an element of the core. -/
def coreComp (f : SmCoupledCore) (B : Finset (Fin 96)) : polyGaussCore (d := 163) :=
  ⟨(f : SmCoupledSpace).ofLp B, f.2 B⟩

@[simp] theorem coe_coreComp (f : SmCoupledCore) (B : Finset (Fin 96)) :
    ((coreComp f B : polyGaussCore (d := 163)) : L2d 163) = (f : SmCoupledSpace).ofLp B := rfl

theorem coreComp_add (f g : SmCoupledCore) (B : Finset (Fin 96)) :
    coreComp (f + g) B = coreComp f B + coreComp g B :=
  Subtype.ext (PiLp.add_apply (fun _ : Finset (Fin 96) => SmBosSpace)
    (f : SmCoupledSpace) (g : SmCoupledSpace) B)

theorem coreComp_smul (c : ℂ) (f : SmCoupledCore) (B : Finset (Fin 96)) :
    coreComp (c • f) B = c • coreComp f B :=
  Subtype.ext (PiLp.smul_apply (fun _ : Finset (Fin 96) => SmBosSpace) c
    (f : SmCoupledSpace) B)

/-- The bosonic factor applied to a core vector, as an `L²` vector. -/
def tensorCompOf (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (x : polyGaussCore (d := 163)) : L2d 163 :=
  (polyGaussCore (d := 163)).subtype (T x)

/-- The bosonic factor applied to the `B`-th component, as an `L²` vector. -/
def tensorComp (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (f : SmCoupledCore) (B : Finset (Fin 96)) : L2d 163 :=
  tensorCompOf T (coreComp f B)

@[simp] theorem tensorComp_apply (T : polyGaussCore (d := 163) →ₗ[ℂ]
      polyGaussCore (d := 163)) (f : SmCoupledCore) (B : Finset (Fin 96)) :
    tensorComp T f B = tensorCompOf T (coreComp f B) := rfl

theorem tensorComp_add (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (f g : SmCoupledCore) (B : Finset (Fin 96)) :
    tensorComp T (f + g) B = tensorComp T f B + tensorComp T g B := by
  rw [tensorComp, tensorComp, tensorComp, tensorCompOf, tensorCompOf, tensorCompOf, coreComp_add,
    map_add, map_add]

theorem tensorComp_smul (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (c : ℂ) (f : SmCoupledCore) (B : Finset (Fin 96)) :
    tensorComp T (c • f) B = c • tensorComp T f B := by
  rw [tensorComp, tensorComp, tensorCompOf, tensorCompOf, coreComp_smul, map_smul, map_smul]

/-- **The elementary tensor `T ⊗ M`**, as a function on the common core: the internal matrix acts
on the occupation components and the bosonic operator `T` on every component.  Because `T` maps
the Gauss–polynomial core to itself, every component of the output is again a core vector, so the
common core is invariant by construction. -/
def smTensorFun (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) (f : SmCoupledCore) : SmCoupledSpace :=
  WithLp.toLp 2 (fun A => ∑ B, M A B • tensorComp T f B)

set_option maxHeartbeats 1000000 in
-- The `map_add'`/`map_smul'` fields of a map out of the finite-`ℓ²` core need many `isDefEq`
-- checks through `PiLp`/`WithLp`, which exceed the default heartbeat budget.
/-- **The elementary tensor `T ⊗ M`** as a linear map out of the common core. -/
def smTensorCore (T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ) : SmCoupledCore →ₗ[ℂ] SmCoupledSpace where
  toFun := smTensorFun T M
  map_add' f g := by
    refine WithLp.ofLp_injective 2 (funext fun A => ?_)
    simp only [smTensorFun, WithLp.ofLp_toLp, PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [tensorComp_add, smul_add]
  map_smul' c f := by
    refine WithLp.ofLp_injective 2 (funext fun A => ?_)
    simp only [smTensorFun, WithLp.ofLp_toLp, PiLp.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [tensorComp_smul, smul_comm]

/-- **The elementary-tensor action**: the `A`-th component is `Σ_B M A B • (T f_B)`. -/
@[simp] theorem smTensorCore_apply (T : polyGaussCore (d := 163) →ₗ[ℂ]
      polyGaussCore (d := 163)) (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (f : SmCoupledCore) (A : Finset (Fin 96)) :
    (smTensorCore T M f).ofLp A = ∑ B, M A B • tensorComp T f B := by
  have h : smTensorCore T M f = smTensorFun T M f := rfl
  rw [h, smTensorFun, WithLp.ofLp_toLp]

/-- The transpose identity behind every symmetry statement: a Hermitian coefficient matrix lets
the double sum be transposed. -/
theorem star_transpose_sum (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (x : Finset (Fin 96) → Finset (Fin 96) → ℂ) (hM : ∀ A B, star (M A B) = M B A) :
    (∑ A, ∑ B, star (M A B) * x B A) = ∑ A, ∑ B, M A B * x A B := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  rw [hM B A]

set_option maxHeartbeats 1000000 in
-- Unfolding `smTensorFun` twice (once per inner product argument) plus the double `Finset.sum`
-- rearrangement is what the default heartbeat budget cannot do.
/-- **Each elementary tensor is symmetric on the common core** when the bosonic factor is
symmetric on the Gauss–polynomial core and the internal matrix is Hermitian. -/
theorem smTensorCore_symmetricOn (T : polyGaussCore (d := 163) →ₗ[ℂ]
      polyGaussCore (d := 163)) (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (hT : ∀ x y : polyGaussCore (d := 163),
      (inner ℂ (tensorCompOf T x) (y : L2d 163) : ℂ)
        = inner ℂ (x : L2d 163) (tensorCompOf T y))
    (hM : ∀ A B, star (M A B) = M B A) :
    SymmetricOn SmCoupledCore (smTensorCore T M) := by
  intro f g
  have hL : (inner ℂ (smTensorCore T M f) (g : SmCoupledSpace) : ℂ) =
      ∑ A, ∑ B, star (M A B) * inner ℂ ((f : SmCoupledSpace).ofLp B) (tensorComp T g A) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [smTensorCore_apply, sum_inner]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [inner_smul_left]
    have hstep : (inner ℂ (tensorComp T f B) ((g : SmCoupledSpace).ofLp A) : ℂ)
        = inner ℂ ((f : SmCoupledSpace).ofLp B) (tensorComp T g A) := by
      simpa only [tensorComp, tensorCompOf, coe_coreComp] using hT (coreComp f B) (coreComp g A)
    rw [hstep, starRingEnd_apply]
  have hR : (inner ℂ (f : SmCoupledSpace) (smTensorCore T M g) : ℂ) =
      ∑ A, ∑ B, M A B * inner ℂ ((f : SmCoupledSpace).ofLp A) (tensorComp T g B) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [smTensorCore_apply, inner_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [inner_smul_right]
  rw [hL, hR]
  exact star_transpose_sum M (fun A B => inner ℂ ((f : SmCoupledSpace).ofLp A)
    (tensorComp T g B)) hM

set_option maxHeartbeats 1000000 in
-- Same double unfolding of `smTensorFun` as in `smTensorCore_symmetricOn`.
/-- The symmetry statement in the `SymmetricOn` form of the Faris–Lavine core: a factor that is
symmetric on the Gauss–polynomial core gives a symmetric elementary tensor. -/
theorem smTensorCore_symmetricOn' (T : polyGaussCore (d := 163) →ₗ[ℂ]
      polyGaussCore (d := 163)) (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (hT : SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp T)) (hM : ∀ A B, star (M A B) = M B A) :
    SymmetricOn SmCoupledCore (smTensorCore T M) := by
  refine smTensorCore_symmetricOn T M (fun x y => ?_) hM
  have h := hT x y
  simpa only [LinearMap.comp_apply, Submodule.coe_subtype, tensorCompOf] using h

/-- The sum of two symmetric operators is symmetric on the same domain. -/
theorem symmetricOn_add {T T' : SmCoupledCore →ₗ[ℂ] SmCoupledSpace}
    (h : SymmetricOn SmCoupledCore T) (h' : SymmetricOn SmCoupledCore T') :
    SymmetricOn SmCoupledCore (T + T') := by
  intro x y
  rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_right, h x y, h' x y]

/-- A finite sum of symmetric operators is symmetric. -/
theorem symmetricOn_sum {ι : Type*} (s : Finset ι) (T : ι → SmCoupledCore →ₗ[ℂ] SmCoupledSpace)
    (h : ∀ i ∈ s, SymmetricOn SmCoupledCore (T i)) :
    SymmetricOn SmCoupledCore (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro x y; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact symmetricOn_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## 4. Fermion parity on the coupled space -/

/-- **Fermion parity on the coupled space**: diagonal in the occupation basis. -/
def coupledParityFun (f : SmCoupledSpace) : SmCoupledSpace :=
  WithLp.toLp 2 (fun A => fockSign A • f.ofLp A)

/-- **Fermion parity** as a linear operator on the coupled space. -/
def coupledParity : SmCoupledSpace →ₗ[ℂ] SmCoupledSpace where
  toFun := coupledParityFun
  map_add' f g := by
    refine WithLp.ofLp_injective 2 (funext fun A => ?_)
    simp only [coupledParityFun, WithLp.ofLp_toLp, PiLp.add_apply, smul_add]
  map_smul' c f := by
    refine WithLp.ofLp_injective 2 (funext fun A => ?_)
    simp only [coupledParityFun, WithLp.ofLp_toLp, PiLp.smul_apply, RingHom.id_apply]
    rw [smul_comm]

@[simp] theorem coupledParity_apply (f : SmCoupledSpace) (A : Finset (Fin 96)) :
    (coupledParity f).ofLp A = fockSign A • f.ofLp A := by
  have h : coupledParity f = coupledParityFun f := rfl
  rw [h, coupledParityFun, WithLp.ofLp_toLp]

/-- **Parity preserves the common core**, componentwise multiplication by `±1`. -/
theorem coupledParity_mem_core (f : SmCoupledSpace) (hf : f ∈ SmCoupledCore) :
    coupledParity f ∈ SmCoupledCore := fun A => by
  rw [coupledParity_apply]
  exact (polyGaussCore (d := 163)).smul_mem (fockSign A) (hf A)

/-- **Parity restricted to the common core.** -/
def coupledParityCore : SmCoupledCore →ₗ[ℂ] SmCoupledCore :=
  (coupledParity.comp SmCoupledCore.subtype).codRestrict SmCoupledCore fun f =>
    coupledParity_mem_core (f : SmCoupledSpace) f.2

theorem coe_coupledParityCore (f : SmCoupledCore) :
    ((coupledParityCore f : SmCoupledCore) : SmCoupledSpace)
      = coupledParity (f : SmCoupledSpace) := by
  rw [coupledParityCore, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.coe_subtype]

theorem coreComp_coupledParityCore (f : SmCoupledCore) (B : Finset (Fin 96)) :
    coreComp (coupledParityCore f) B = fockSign B • coreComp f B := by
  refine Subtype.ext ?_
  rw [coe_coreComp, coe_coupledParityCore, coupledParity_apply]
  simp only [coe_coreComp, Submodule.coe_smul]

theorem tensorComp_coupledParityCore (T : polyGaussCore (d := 163) →ₗ[ℂ]
      polyGaussCore (d := 163)) (f : SmCoupledCore) (B : Finset (Fin 96)) :
    tensorComp T (coupledParityCore f) B = fockSign B • tensorComp T f B := by
  rw [tensorComp, tensorComp, tensorCompOf, tensorCompOf, coreComp_coupledParityCore, map_smul,
    map_smul]

set_option maxHeartbeats 1000000 in
-- The `PiLp` fiber-by-fiber unfold of both sides needs more heartbeats than the default budget.
/-- **An elementary tensor with a parity-graded coefficient matrix commutes with parity.** -/
theorem coupledParity_smTensorCore (T : polyGaussCore (d := 163) →ₗ[ℂ]
      polyGaussCore (d := 163)) (M : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (hM : ∀ A B, fockSign A * M A B = M A B * fockSign B) (f : SmCoupledCore) :
    coupledParity (smTensorCore T M f) = smTensorCore T M (coupledParityCore f) := by
  refine WithLp.ofLp_injective 2 (funext fun A => ?_)
  rw [coupledParity_apply, smTensorCore_apply, Finset.smul_sum, smTensorCore_apply]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [tensorComp_coupledParityCore, smul_smul, smul_smul, hM A B]

/-! ## 5. The full normal form of the coupled inner operator -/

/-- **The spatial momentum** `πⱼ = −i∂ⱼ` transported to the Gauss–polynomial core of `L²(ℝ¹⁶³)`.
This is the actual Gaussian-polynomial momentum of the Mehler dictionary (`CoreRep.op` of `momOp`),
not a plane-wave parameter substituted for the derivative. -/
def smMom (j : Fin 163) : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163) :=
  (coreRepPoly 163).op (momOp j)

/-- **Multiplication by the spatial coordinate** `uⱼ` on the core. -/
def smPos (j : Fin 163) : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163) :=
  (coreRepPoly 163).op (mulOp (MvPolynomial.X j))

/-- **The kinetic factor** `−∂ⱼ² = πⱼ²`, built from the momentum operator. -/
def smKinetic (j : Fin 163) : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163) :=
  (smMom j).comp (smMom j)

theorem smMom_symmetricOn (j : Fin 163) : SymmetricOn (polyGaussCore (d := 163))
    ((polyGaussCore (d := 163)).subtype.comp (smMom j)) :=
  CoreRep.symmetricOn_op (coreRepPoly 163) (momOp_polySym j)

theorem smPos_symmetricOn (j : Fin 163) : SymmetricOn (polyGaussCore (d := 163))
    ((polyGaussCore (d := 163)).subtype.comp (smPos j)) :=
  CoreRep.symmetricOn_op (coreRepPoly 163) (mulOp_polySym (realCoeff_X j))

/-- **The square of a core-symmetric operator is core-symmetric**: `⟪T²x, y⟫ = ⟪Tx, Ty⟫ =
⟪x, T²y⟫`. -/
theorem symmetricOn_comp_self {T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163)}
    (hT : SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp T)) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp (T.comp T)) := by
  intro x y
  have h1 := hT (T x) y
  have h2 := hT x (T y)
  simp only [LinearMap.comp_apply] at h1 h2 ⊢
  exact h1.trans h2

theorem smKinetic_symmetricOn (j : Fin 163) : SymmetricOn (polyGaussCore (d := 163))
    ((polyGaussCore (d := 163)).subtype.comp (smKinetic j)) :=
  symmetricOn_comp_self (smMom_symmetricOn j)

/-- The identity factor is core-symmetric. -/
theorem symmetricOn_id : SymmetricOn (polyGaussCore (d := 163))
    ((polyGaussCore (d := 163)).subtype.comp LinearMap.id) :=
  fun _ _ => rfl

/-- The internal coefficient data that the ledger's elementary tensors carry: the matrices
multiplying the kinetic terms `−∂ⱼ²`, the coordinate terms `uⱼ` (the four Higgs components are
four of these coordinates) and the constant term `1 ⊗ M₀`. -/
structure SmNormalFormData where
  /-- the coefficient matrices of the spatial derivatives `πⱼ` -/
  mom : Fin 163 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ
  /-- the coefficient matrices of the squared momenta `πⱼ²` -/
  kinetic : Fin 163 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ
  /-- the coefficient matrices of the coordinate multiplications `uⱼ` -/
  coord : Fin 163 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ
  /-- the coefficient matrix of the constant `1 ⊗ M₀` term -/
  mass : Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ

/-- **Hermiticity of the coefficient data** — the symmetry hypothesis of the normal form. -/
def HermitianCoeffs (D : SmNormalFormData) : Prop :=
  (∀ j A B, star (D.mom j A B) = D.mom j B A) ∧
  (∀ j A B, star (D.kinetic j A B) = D.kinetic j B A) ∧
  (∀ j A B, star (D.coord j A B) = D.coord j B A) ∧
  (∀ A B, star (D.mass A B) = D.mass B A)

/-- **Parity grading of the coefficient data** — each coefficient matrix maps the parity-`A` sector
into the parity-`B` sector, so that the internal factor preserves fermion parity. -/
def ParityGradedCoeffs (D : SmNormalFormData) : Prop :=
  (∀ j A B, fockSign A * D.mom j A B = D.mom j A B * fockSign B) ∧
  (∀ j A B, fockSign A * D.kinetic j A B = D.kinetic j A B * fockSign B) ∧
  (∀ j A B, fockSign A * D.coord j A B = D.coord j A B * fockSign B) ∧
  (∀ A B, fockSign A * D.mass A B = D.mass A B * fockSign B)

/-- **The full normal form** of the coupled inner operator on the common core:

```text
h_SM = Σⱼ πⱼ ⊗ Aⱼ + Σⱼ πⱼ² ⊗ Bⱼ + Σⱼ uⱼ ⊗ Jⱼ + 1 ⊗ M₀,
```

every term being an elementary tensor: the bosonic factor acts on each internal component and the
coefficient matrix `M` on the occupation basis.  The four real Higgs components are the coordinate
terms `uⱼ` for the four Higgs directions, and the `p_x ⊗ A` ledger term is the momentum-squared
(kinetic) family, whose derivative is the genuine Gaussian-polynomial `πⱼ`, not a plane wave. -/
def smNormalForm (D : SmNormalFormData) : SmCoupledCore →ₗ[ℂ] SmCoupledSpace :=
  (((∑ j ∈ (Finset.univ : Finset (Fin 163)), smTensorCore (smMom j) (D.mom j))
    + ∑ j ∈ (Finset.univ : Finset (Fin 163)), smTensorCore (smKinetic j) (D.kinetic j))
    + ∑ j ∈ (Finset.univ : Finset (Fin 163)), smTensorCore (smPos j) (D.coord j))
    + smTensorCore LinearMap.id D.mass

/-- **The elementary-tensor action of the full normal form**, term by term. -/
theorem smNormalForm_apply (D : SmNormalFormData) (f : SmCoupledCore) (A : Finset (Fin 96)) :
    (smNormalForm D f).ofLp A
      = (∑ j ∈ (Finset.univ : Finset (Fin 163)),
          ∑ B, D.mom j A B • tensorComp (smMom j) f B)
        + (∑ j ∈ (Finset.univ : Finset (Fin 163)),
            ∑ B, D.kinetic j A B • tensorComp (smKinetic j) f B)
        + (∑ j ∈ (Finset.univ : Finset (Fin 163)),
            ∑ B, D.coord j A B • tensorComp (smPos j) f B)
        + ∑ B, D.mass A B • tensorComp LinearMap.id f B := by
  simp only [smNormalForm, LinearMap.add_apply, LinearMap.sum_apply, PiLp.add_apply,
    WithLp.ofLp_sum, Finset.sum_apply, smTensorCore_apply]

/-- **The full normal form is symmetric on the common core.** -/
theorem smNormalForm_symmetricOn (D : SmNormalFormData) (hD : HermitianCoeffs D) :
    SymmetricOn SmCoupledCore (smNormalForm D) := by
  obtain ⟨hmom, hk, hq, hm⟩ := hD
  refine symmetricOn_add (symmetricOn_add (symmetricOn_add ?_ ?_) ?_) ?_
  · exact symmetricOn_sum _ _ fun j _ =>
      smTensorCore_symmetricOn' _ _ (smMom_symmetricOn j) (hmom j)
  · exact symmetricOn_sum _ _ fun j _ =>
      smTensorCore_symmetricOn' _ _ (smKinetic_symmetricOn j) (hk j)
  · exact symmetricOn_sum _ _ fun j _ =>
      smTensorCore_symmetricOn' _ _ (smPos_symmetricOn j) (hq j)
  · exact smTensorCore_symmetricOn' _ _ symmetricOn_id hm

/-- **A finite sum of parity-graded elementary tensors commutes with parity.** -/
theorem coupledParity_sum (s : Finset (Fin 163))
    (T : Fin 163 → polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163))
    (M : Fin 163 → Matrix (Finset (Fin 96)) (Finset (Fin 96)) ℂ)
    (hM : ∀ j A B, fockSign A * M j A B = M j A B * fockSign B) (f : SmCoupledCore) :
    coupledParity ((∑ j ∈ s, smTensorCore (T j) (M j)) f)
      = (∑ j ∈ s, smTensorCore (T j) (M j)) (coupledParityCore f) := by
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => coupledParity_smTensorCore _ _ (fun A B => hM j A B) f

/-- **The full normal form preserves fermion parity.** -/
theorem smNormalForm_parity (D : SmNormalFormData) (hD : ParityGradedCoeffs D)
    (f : SmCoupledCore) :
    coupledParity (smNormalForm D f) = smNormalForm D (coupledParityCore f) := by
  obtain ⟨hmom, hk, hq, hm⟩ := hD
  rw [smNormalForm]
  simp only [LinearMap.add_apply, coupledParity.map_add]
  rw [coupledParity_sum _ _ _ hmom f, coupledParity_sum _ _ _ hk f,
    coupledParity_sum _ _ _ hq f, coupledParity_smTensorCore _ _ hm f]

end

end BookProof.SmFullMatter
