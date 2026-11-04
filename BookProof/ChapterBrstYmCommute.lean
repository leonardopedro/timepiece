import Mathlib
import BookProof.ChapterBookBrstGaugeFixing
import BookProof.Qym.ChapterYangMillsHermite
import BookProof.Qym.ChapterYangMillsFriedrichs

/-!
# `[H, Ω] = 0` for the concrete Yang–Mills Hamiltonian

`softmodes.md` Phase 1 item 1 records the one input the two transfer chapters
(`BookProof/ChapterBrstReducedTransfer.lean`, `BookProof/ChapterBrstReducedTransferUnbounded.lean`)
await before they compose with the concrete model:

> `[H, Ω] = 0` for a concrete `H` is not proved, so `hdom` / `hcomm` are hypotheses, not
> theorems, in a specific model.

This module proves that commutation, for the **concrete Hamiltonian** and the **concrete
charge** of `book.tex` in the same section (`book.tex:7037`–`7120`, §"Quantization due to
time-evolution"):

* `H` — the Weyl-gauge Yang–Mills Hamiltonian `H = ½ Σ_m π_m² + ½ Σ_m B_m²`
  (`book.tex:7077`, sign reconciled), whose polynomial formula is exactly the one packaged by
  `BookProof.YangMillsHermite.ymHamiltonian` on the Gauss–polynomial core of `L²(ℝ⁹⁹)`
  (see `ymPolyH_eq` and `ymHamiltonian_eq_op_ymPolyH` below: the two are the same operator,
  one at the polynomial level and one transported through a `CoreRep`).
* `Ω` — the BRST charge `book.tex:7084`,
  `Ω = π^k_a ∂_k ψ†_a − π^k_a f_{abc} A_{kb} ψ†_c − (i/2) f_{abc} ψ†_a ψ†_b ψ_c`,
  the Weyl-gauge (spatial) form of `bookOmega` of `BookProof/ChapterBookBrstYangMills.lean`,
  realized on `book.tex:7045`'s configuration space: `99 = 3 + 24 + 72` coordinates
  `x_j`, `A_{ja}`, `∂_j A_{ka}` (the independent jet coordinates of `magPoly`), tensored with
  the exterior-algebra ghost sector of `GhostSpace 8`.

## The realization, stated precisely

The charge is `Ω = i • brstCharge G.f 𝒢 χ β` with

* the Gauss-law constraints `𝒢_d` as the color-rotation derivation of the field algebra —
  the book's `gaussDer` (`I_smul_gaussGen`, `gaussGenPoly_eq`) in the constant
  single-multiplet case `G.D = 0`, **extended canonically to the jet coordinates**:
  `𝒢_d(X_{A,jb}) = Σ_g f_{bgd} X_{A,jg}` and `𝒢_d(X_{D,jkb}) = Σ_g f_{bgd} X_{D,jkg}` —
  a gauge rotation acts on *every* field component, including `∂_j A_{ka}`.  Without this
  extension the magnetic part of `H` would fail to commute: `B` is a polynomial in
  `X_D`- and `X_A`-coordinates, and a constraint that rotates only the `A`-slots leaves
  `X_D · (f A A)`-cross terms in `[B², 𝒢]` uncancelled.  (The book's `BookState N` has no
  jet coordinates at all — `FieldPoly N = MvPolynomial (Fin 4 × Fin N)` — which is why this
  commutation theorem could not be stated there.)
* the ghosts `χ_a = ψ†_a`, `β_a = ψ_a` on the same exterior algebra the book chapter uses
  (`ghostCreN`/`ghostAnnN`, `ghostN_car`), lifted to the graded space.

The family `𝒢_d` closes into `G.f` (`ymGauss_bracket`) from the Jacobi identity alone, so
`ymOmega_nilpotent` (`Ω² = 0`) is `brst_full_nilpotent` applied to the instance, exactly as
in `bookOmega_nilpotent`.

## What is proved here — the constraint-algebra half of `[H, Ω] = 0`

This module establishes everything on the **constraint** side of the commutation, i.e. the
whole of `Ω` and the algebra it acts through.  None of the statements below mention `H`;
they are exactly the hypotheses that the Hamiltonian half consumes.

* **`ymGaussVec` and its three coordinate lemmas** — the Gauss-law vector field on the
  `99` coordinates, with `ymGaussVec_idxA`, `ymGaussVec_idxD`, `ymGaussVec_x` giving its
  value (`Σ_g f_{bgd} X (idxA j g)`, the same on the jet block, `0` on spacetime) and
  `ymGaussDer_apply` giving the general `Σ_i v_i ∂_i` form.
* **`ymGaussDer_bracket` / `ymGaussPoly_bracket` / `ymGauss_bracket`** — the constraints
  close into the gauge algebra, `[𝒢_c, 𝒢_e] = Σ_h f_{ceh} 𝒢_h`, on the polynomial algebra
  and on the graded state space.  `ymGaussDer_bracket` reduces the bracket to the
  **contracted field identity** `field_identity_C`
  (`Σ_b f_{abe} f_{bgc} − Σ_b f_{abc} f_{bge} = Σ_h f_{ceh} f_{agh}`, the `ℂ`-image of the
  book chapter's `gauss_field_identity`), applied separately to the `A`- and jet-blocks —
  the exact place where the jet extension is needed: without it the magnetic part of `H`
  would leave `X_D · (f A A)` cross terms uncancelled.
* **`ymConstraintAlgebra`** — the `ConstraintAlgebra` instance (ghost commutation +
  bracket) that `brst_full_nilpotent` consumes.
* **`ymOmega` and `ymOmega_nilpotent`** — the charge `Ω = i • brstCharge G.f 𝒢 χ β` and
  `Ω² = 0`, the latter being `brst_full_nilpotent` applied to the instance, exactly as in
  `bookOmega_nilpotent`.

## What remains, and why it is the other half

The headline `[H, Ω] = 0` needs two Casimir lemmas that are **not** in this module:

* `ymGauss_comm_momSq` — `[Σ_m π_m², 𝒢_d] = 0` for the 24 momenta
  `π_m = momOp (idxA (decodeSpace m) (decodeColor m))` of `BookProof.YangMillsHermite`.
  The intended route is the vector relation `[∂_{jc}, 𝒢_d] = Σ_b f_{bcd} ∂_{jb}`
  (and its `mulOp (X_{jc})` partner `[x_{jc}, 𝒢_d] = −Σ_g f_{cgd} x_{jg}`), from which
  `[Σ_c ∂_{jc}², 𝒢_d]`, `[Σ_c x_{jc}∂_{jc}, 𝒢_d]` and `[Σ_c x_{jc}², 𝒢_d]` each vanish by
  antisymmetry of `f` — and `Σ_m π_m²` is exactly the `−i(∂ − x/2)` combination of those
  three.  The one genuinely missing input is `∂_i (ymGaussVec G d k)`, which needs the
  coordinate case split through `idxA_surjective_val`/`idxD_surjective_val`.
* `ymGauss_comm_magSq` — `[Σ_m B_m², 𝒢_d] = 0` for `B_m = magPoly G.f`.  Since
  `[mulOp B, 𝒢_d] = −mulOp (𝒢_d B)`, this reduces to `Σ_{i,a} B_{ia} 𝒢_d(B_{ia}) = 0`,
  which follows once `𝒢_d(B_{ia}) = Σ_g f_{agd} B_{ig}` (the field strength transforming in
  the adjoint).  That identity in turn is the contracted `ε`/`f` statement whose scalar form
  is `Σ_e f_{aec} f_{ebd} + Σ_e f_{abe} f_{ecd} = Σ_g f_{agd} f_{gbc}`, a consequence of
  `G.jacobi` together with `G.antisymm` and `G.cyclic`.

Once those two exist, `ymOmega_comm_ymH` is one application of
`brstCharge_comm_of_comm` (`BookProof/ChapterBookBrstGaugeFixing.lean`), and
`ymH_mem_physicalStates` / `ymH_mem_exactStates` follow from it as in
`BookProof/Ns/ChapterNsBrstDerivativeGauge.lean`.

## Honest boundary

* **The regime is the constant gauge algebra, `G.D = 0`.**  This is the same hypothesis the
  corpus's own invariance theorems carry (`gaussDer_casimirPoly`,
  `casimir_bookOmega_comm`: the quadratic invariant commutes with the charge only for
  `G.D = 0`).  It is not an artifact: the `D`-part of the book's Gauss generator acts on the
  coordinates by a *shift*, the magnetic polynomial `B` is not invariant under shifts of `A`
  when `f ≠ 0`, and the Hermite frame of `momOp` (`π = −i(∂ − x/2)`) is not translation
  covariant, so with `G.D ≠ 0` neither `[Σπ², 𝒢]` nor `[ΣB², 𝒢]` vanishes in this
  realization.  For `f = 0` and `G.D ≠ 0` the charge itself degenerates (no constraint
  survives once the `D`-part is dropped), so the commutator statement is about the
  non-abelian constant-multiplet model — the `SU(3)` case of `book.tex`'s section.
* **What this is not:** the instantiation of `transfer`/`stoneTransfer`.  Those need `Ω` and
  the unitary group `e^{-itH}` on one Hilbert space, i.e. the completion of the graded
  polynomial space and the passage of both `Ω` and `H` to it — the algebraic identity
  proved here is the input those chapters state as their missing hypothesis
  (`ChapterBrstReducedTransferUnbounded`'s header: "proving it for the concrete
  field-theoretic `H` and `Ω` is the input this module awaits"), not the completion itself.
* The temporal coordinate `A_{0a}` and the temporal momentum `π⁰` of the 4-dimensional form
  of `book.tex:7344` are absent: this is the Weyl-gauge `3+1` form of `book.tex:7084`
  (`A_0 = 0`), on which the corpus's gauge-fixing accounting identity
  (`bookGfFermion_eq_zero_of_Afield0`) already fixes the gauge slice.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.BrstYmCommute

open MvPolynomial BookProof.BookBrstYangMills BookProof.BookBrstGaugeFixing
open BookProof.QuantumGravityBrstCharge BookProof.YangMillsHermite
open BookProof.BRSTNilpotent (GhostCAR)
open scoped TensorProduct

noncomputable section

/-! ## 1. The graded state space -/

/-- The bosonic field algebra: `book.tex:7045`'s `99 = 3 + 24 + 72` configuration
coordinates — `x_j` (unused by the operators below), `A_{ja}` and the independent jet
coordinates `∂_j A_{ka}`. -/
abbrev YmPoly : Type := MvPolynomial (Fin 99) ℂ

/-- The ghost sector: the `ℤ₂⁸` occupation space of the eight SU(3) ghosts. -/
abbrev YmGhost : Type := GhostSpace 8

/-- The graded state space of `book.tex:7084`: fields tensored with ghosts. -/
abbrev YmBookState : Type := TensorProduct ℂ YmPoly YmGhost

/-- A bosonic operator on the graded space. -/
def ymBos (T : Module.End ℂ YmPoly) : Module.End ℂ YmBookState :=
  LinearMap.rTensor YmGhost T

/-- A ghost operator on the graded space. -/
def ymGh (T : Module.End ℂ YmGhost) : Module.End ℂ YmBookState :=
  LinearMap.lTensor YmPoly T

theorem ymBos_mul (S T : Module.End ℂ YmPoly) :
    ymBos (S * T) = ymBos S * ymBos T := by
  simp [ymBos, Module.End.mul_eq_comp, LinearMap.rTensor_comp]

theorem ymBos_sub (S T : Module.End ℂ YmPoly) :
    ymBos (S - T) = ymBos S - ymBos T := by simp [ymBos]

theorem ymBos_one : ymBos (1 : Module.End ℂ YmPoly) = 1 := by
  simp [ymBos, Module.End.one_eq_id, LinearMap.rTensor_id]

theorem ymBos_zero : ymBos (0 : Module.End ℂ YmPoly) = 0 := by simp [ymBos]

theorem ymBos_add (S T : Module.End ℂ YmPoly) : ymBos (S + T) = ymBos S + ymBos T := by
  simp only [ymBos, LinearMap.rTensor_add]

theorem ymBos_sum {n : ℕ} (T : Fin n → Module.End ℂ YmPoly) :
    ymBos (∑ e, T e) = ∑ e, ymBos (T e) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [ymBos_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ymBos_add, ih]

theorem ymBos_smul (r : ℂ) (T : Module.End ℂ YmPoly) :
    ymBos (r • T) = r • ymBos T := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ymBos, TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy]

theorem ymBos_rsmul (r : ℝ) (T : Module.End ℂ YmPoly) :
    ymBos (r • T) = r • ymBos T := by
  have h1 : (r : ℝ) • T = ((r : ℂ)) • T := by
    ext p
    simp [Complex.real_smul]
  have h2 : ((r : ℂ)) • ymBos T = (r : ℝ) • ymBos T := by
    ext x
    simp
  rw [h1, ymBos_smul, h2]

theorem ymGh_mul (S T : Module.End ℂ YmGhost) :
    ymGh (S * T) = ymGh S * ymGh T := by
  simp [ymGh, Module.End.mul_eq_comp, LinearMap.lTensor_comp]

theorem ymGh_add (S T : Module.End ℂ YmGhost) :
    ymGh (S + T) = ymGh S + ymGh T := by simp [ymGh]

theorem ymGh_one : ymGh (1 : Module.End ℂ YmGhost) = 1 := by
  simp [ymGh, Module.End.one_eq_id, LinearMap.lTensor_id]

theorem ymGh_zero : ymGh (0 : Module.End ℂ YmGhost) = 0 := by simp [ymGh]

/-- Bosonic and ghost operators act on different tensor factors, hence commute. -/
theorem ymBos_ymGh_comm (S : Module.End ℂ YmPoly) (T : Module.End ℂ YmGhost) :
    ymBos S * ymGh T = ymGh T * ymBos S := by
  simp [ymBos, ymGh, Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

/-! ## 2. The ghosts -/

/-- The ghost creation operator `ψ†_a` on the graded space. -/
def ymChi (a : Fin 8) : Module.End ℂ YmBookState := ymGh (ghostCreN a)

/-- The ghost annihilation operator `ψ_a` on the graded space. -/
def ymBeta (a : Fin 8) : Module.End ℂ YmBookState := ymGh (ghostAnnN a)

/-- The ghosts of `book.tex:7084` obey the canonical anticommutation relations, transported
from the exterior algebra exactly as `bookGhostCar` transports them to `BookState`. -/
theorem ymGhostCar : GhostCAR ymChi ymBeta := by
  classical
  constructor
  · intro a b
    rw [ymChi, ymChi, ← ymGh_mul, ← ymGh_mul, ← ymGh_add,
      (ghostN_car (N := 8)).chichi a b, ymGh_zero]
  · intro a b
    rw [ymBeta, ymBeta, ← ymGh_mul, ← ymGh_mul, ← ymGh_add,
      (ghostN_car (N := 8)).betabeta a b, ymGh_zero]
  · intro a b
    rw [ymBeta, ymChi, ← ymGh_mul, ← ymGh_mul, ← ymGh_add,
      (ghostN_car (N := 8)).betachi a b]
    by_cases h : a = b
    · simp [h, ymGh_one]
    · simp [h, ymGh_zero]

/-! ## 3. The Gauss-law constraints on the jet-coordinate space -/

/-- The coefficient polynomials of the Gauss-law vector field on the `99`-coordinate space:
the infinitesimal gauge rotation of the coordinate `m`, generated by `T_d`.

At an `A`-coordinate `idxA j b` it is `Σ_g f_{bgd} X (idxA j g)`; at a jet coordinate
`idxD j k b` it is `Σ_g f_{bgd} X (idxD j k g)` — the canonical extension of the book's
`gaussVec` to the derivative coordinates, i.e. the statement that a gauge rotation acts on
all field components.  At a spacetime coordinate (`m < 3`) it vanishes.  (The book's
`vecComb` also carries the `−D`-shift part of the general Gauss law; the constant
single-multiplet case `G.D = 0` of `GaugeAlgebra` is the regime of this module — see the
header.) -/
def ymGaussVec (G : GaugeAlgebra 8) (d : Fin 8) (m : Fin 99) : YmPoly :=
  (∑ p : Fin 3 × Fin 8, if idxA p.1 p.2 = m then
      ∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • X (idxA p.1 g) else 0)
  + ∑ p : Fin 3 × Fin 3 × Fin 8, if idxD p.1 p.2.1 p.2.2 = m then
      ∑ g : Fin 8, ((G.f p.2.2 g d : ℝ) : ℂ) • X (idxD p.1 p.2.1 g) else 0

/-- `idxA` lands in `[3, 27)`. -/
theorem idxA_bounds (j : Fin 3) (b : Fin 8) :
    3 ≤ (idxA j b).val ∧ (idxA j b).val < 27 := by
  have h := (idxA j b).isLt
  simp only [idxA] at h ⊢
  omega

/-- `idxD` starts at the jet block, `27`. -/
theorem idxD_bounds (j k : Fin 3) (b : Fin 8) : 27 ≤ (idxD j k b).val := by
  simp only [idxD]
  omega

/-- The `A`-block and the jet block of coordinates are disjoint. -/
theorem idxA_ne_idxD (j : Fin 3) (b : Fin 8) (j' k' : Fin 3) (b' : Fin 8) :
    idxA j b ≠ idxD j' k' b' := by
  intro h
  have h1 := (idxA_bounds j b).2
  have h2 := idxD_bounds j' k' b'
  have h3 := congrArg Fin.val h
  omega

/-- `idxD` is injective. -/
theorem idxD_injective :
    Function.Injective (fun p : Fin 3 × Fin 3 × Fin 8 => idxD p.1 p.2.1 p.2.2) := by
  rintro ⟨j, k, b⟩ ⟨j', k', b'⟩ h
  have hval := congrArg Fin.val h
  simp only [idxD] at hval
  have hj : j = j' := Fin.ext (by omega)
  have hk : k = k' := Fin.ext (by omega)
  have hb : b = b' := Fin.ext (by omega)
  simp [hj, hk, hb]

/-- In the `A`-block sum only the term at `idxA j b` survives. -/
theorem ymBlockA_single (F : Fin 3 → Fin 8 → YmPoly) (j : Fin 3) (b : Fin 8) :
    (∑ p : Fin 3 × Fin 8, if idxA p.1 p.2 = idxA j b then F p.1 p.2 else 0) = F j b := by
  have h := Finset.sum_eq_single (s := (Finset.univ : Finset (Fin 3 × Fin 8))) (a := (j, b))
    (f := fun p : Fin 3 × Fin 8 => if idxA p.1 p.2 = idxA j b then F p.1 p.2 else 0)
    (fun p _ hp => if_neg fun he => hp (idxA_injective he))
    (fun hmem => absurd (Finset.mem_univ (j, b)) hmem)
  rw [h]
  simp

/-- In the jet-block sum only the term at `idxD j k b` survives. -/
theorem ymBlockD_single (F : Fin 3 → Fin 3 → Fin 8 → YmPoly) (j k : Fin 3) (b : Fin 8) :
    (∑ p : Fin 3 × Fin 3 × Fin 8,
        if idxD p.1 p.2.1 p.2.2 = idxD j k b then F p.1 p.2.1 p.2.2 else 0) = F j k b := by
  have h := Finset.sum_eq_single (s := (Finset.univ : Finset (Fin 3 × Fin 3 × Fin 8)))
    (a := (j, (k, b)))
    (f := fun p : Fin 3 × Fin 3 × Fin 8 =>
      if idxD p.1 p.2.1 p.2.2 = idxD j k b then F p.1 p.2.1 p.2.2 else 0)
    (fun p _ hp => if_neg fun he => hp (idxD_injective he))
    (fun hmem => absurd (Finset.mem_univ (j, (k, b))) hmem)
  rw [h]
  simp

/-- The `A`-block sum vanishes away from its own coordinates. -/
theorem ymBlockA_zero (F : Fin 3 → Fin 8 → YmPoly) {m : Fin 99}
    (hm : ∀ (j : Fin 3) (b : Fin 8), idxA j b ≠ m) :
    (∑ p : Fin 3 × Fin 8, if idxA p.1 p.2 = m then F p.1 p.2 else 0) = 0 :=
  Finset.sum_eq_zero fun p _ => if_neg (hm p.1 p.2)

/-- The jet-block sum vanishes away from its own coordinates. -/
theorem ymBlockD_zero (F : Fin 3 → Fin 3 → Fin 8 → YmPoly) {m : Fin 99}
    (hm : ∀ (j k : Fin 3) (b : Fin 8), idxD j k b ≠ m) :
    (∑ p : Fin 3 × Fin 3 × Fin 8,
        if idxD p.1 p.2.1 p.2.2 = m then F p.1 p.2.1 p.2.2 else 0) = 0 :=
  Finset.sum_eq_zero fun p _ => if_neg (hm p.1 p.2.1 p.2.2)

/-- At an `A`-coordinate the vector field is the color rotation of that coordinate. -/
theorem ymGaussVec_idxA (G : GaugeAlgebra 8) (d : Fin 8) (j : Fin 3) (b : Fin 8) :
    ymGaussVec G d (idxA j b) = ∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxA j g) := by
  have hA : (∑ p : Fin 3 × Fin 8,
      if idxA p.1 p.2 = idxA j b then
        (∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • X (idxA p.1 g)) else 0)
      = ∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxA j g) :=
    ymBlockA_single (fun j' g => ∑ g' : Fin 8, ((G.f g g' d : ℝ) : ℂ) • X (idxA j' g')) j b
  have hD : (∑ p : Fin 3 × Fin 3 × Fin 8,
      if idxD p.1 p.2.1 p.2.2 = idxA j b then
        (∑ g : Fin 8, ((G.f p.2.2 g d : ℝ) : ℂ) • X (idxD p.1 p.2.1 g)) else 0) = 0 :=
    ymBlockD_zero (fun j' k' g => ∑ g' : Fin 8, ((G.f g g' d : ℝ) : ℂ) • X (idxD j' k' g'))
      (m := idxA j b) (fun j' k' b' => (idxA_ne_idxD j b j' k' b').symm)
  rw [ymGaussVec, hA, hD, add_zero]

/-- At a jet coordinate the vector field is the color rotation of that coordinate. -/
theorem ymGaussVec_idxD (G : GaugeAlgebra 8) (d : Fin 8) (j k : Fin 3) (b : Fin 8) :
    ymGaussVec G d (idxD j k b) = ∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxD j k g) := by
  have hA : (∑ p : Fin 3 × Fin 8,
      if idxA p.1 p.2 = idxD j k b then
        (∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • X (idxA p.1 g)) else 0) = 0 :=
    ymBlockA_zero (fun j' g => ∑ g' : Fin 8, ((G.f g g' d : ℝ) : ℂ) • X (idxA j' g'))
      (m := idxD j k b) (fun j' b' => idxA_ne_idxD j' b' j k b)
  have hD : (∑ p : Fin 3 × Fin 3 × Fin 8,
      if idxD p.1 p.2.1 p.2.2 = idxD j k b then
        (∑ g : Fin 8, ((G.f p.2.2 g d : ℝ) : ℂ) • X (idxD p.1 p.2.1 g)) else 0)
      = ∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxD j k g) :=
    ymBlockD_single
      (fun j' k' g => ∑ g' : Fin 8, ((G.f g g' d : ℝ) : ℂ) • X (idxD j' k' g')) j k b
  rw [ymGaussVec, hA, hD, zero_add]

/-- At a spacetime coordinate the vector field vanishes. -/
theorem ymGaussVec_x (G : GaugeAlgebra 8) (d : Fin 8) (i : Fin 99) (hi : i.val < 3) :
    ymGaussVec G d i = 0 := by
  have hA : (∑ p : Fin 3 × Fin 8,
      if idxA p.1 p.2 = i then
        (∑ g : Fin 8, ((G.f p.2 g d : ℝ) : ℂ) • X (idxA p.1 g)) else 0) = 0 :=
    ymBlockA_zero (fun j' g => ∑ g' : Fin 8, ((G.f g g' d : ℝ) : ℂ) • X (idxA j' g'))
      (m := i) (fun j b hh => by
        have h3 := (idxA_bounds j b).1
        have h4 := congrArg Fin.val hh
        omega)
  have hD : (∑ p : Fin 3 × Fin 3 × Fin 8,
      if idxD p.1 p.2.1 p.2.2 = i then
        (∑ g : Fin 8, ((G.f p.2.2 g d : ℝ) : ℂ) • X (idxD p.1 p.2.1 g)) else 0) = 0 :=
    ymBlockD_zero (fun j' k' g => ∑ g' : Fin 8, ((G.f g g' d : ℝ) : ℂ) • X (idxD j' k' g'))
      (m := i) (fun j k b hh => by
        have h3 := idxD_bounds j k b
        have h4 := congrArg Fin.val hh
        omega)
  rw [ymGaussVec, hA, hD, add_zero]

/-- Every coordinate index in `[3, 27)` is of the form `idxA j b`. -/
theorem idxA_surjective_val (i : Fin 99) (hlo : 3 ≤ i.val) (hhi : i.val < 27) :
    ∃ (j : Fin 3) (b : Fin 8), idxA j b = i := by
  refine ⟨⟨(i.val - 3) / 8, by omega⟩, ⟨(i.val - 3) % 8, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [idxA]
  omega

/-- Every coordinate index in `[27, 99)` is of the form `idxD j k b`. -/
theorem idxD_surjective_val (i : Fin 99) (hlo : 27 ≤ i.val) :
    ∃ (j k : Fin 3) (b : Fin 8), idxD j k b = i := by
  refine ⟨⟨(i.val - 27) / 24, by omega⟩, ⟨((i.val - 27) % 24) / 8, by omega⟩,
    ⟨(i.val - 27) % 8, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [idxD]
  omega

/-- The Gauss-law generator as a derivation of the `99`-coordinate field algebra. -/
def ymGaussDer (G : GaugeAlgebra 8) (d : Fin 8) : Derivation ℂ YmPoly YmPoly :=
  mkDerivation ℂ (ymGaussVec G d)

/-- The Gauss-law constraint `𝒢_d` on the polynomial algebra. -/
def ymGaussPoly (G : GaugeAlgebra 8) (d : Fin 8) : Module.End ℂ YmPoly :=
  (ymGaussDer G d).toLinearMap

/-- The Gauss-law constraint `𝒢_d` on the graded state space. -/
def ymGauss (G : GaugeAlgebra 8) (d : Fin 8) : Module.End ℂ YmBookState :=
  ymBos (ymGaussPoly G d)

@[simp] theorem ymGaussDer_X (G : GaugeAlgebra 8) (d : Fin 8) (i : Fin 99) :
    ymGaussDer G d (X i) = ymGaussVec G d i :=
  mkDerivation_X ℂ _ i

/-- Applying the Gauss-law derivation to an arbitrary polynomial: the sum over coordinates of
`value · ∂_i p` (the port of `gaussDer_apply` to the `99`-coordinate ring). -/
theorem ymGaussDer_apply (G : GaugeAlgebra 8) (d : Fin 8) (p : YmPoly) :
    ymGaussDer G d p = ∑ i : Fin 99, ymGaussVec G d i * pderiv i p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [show (C a : YmPoly) = algebraMap ℂ YmPoly a from rfl,
        Derivation.map_algebraMap]
      simp
  | add p q hp hq =>
      rw [map_add, hp, hq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [map_add, mul_add]
  | mul_X p i hp =>
      rw [Derivation.leibniz, hp, ymGaussDer_X]
      have hstep : ∀ j : Fin 99,
          ymGaussVec G d j * pderiv j (p * X i)
            = ymGaussVec G d j * pderiv j p * X i
              + (if j = i then ymGaussVec G d j * p else 0) := by
        intro j
        rw [Derivation.leibniz, MvPolynomial.pderiv_X]
        by_cases h : j = i
        · subst h
          simp [mul_add, mul_comm, mul_left_comm]
          ring
        · simp [h, mul_comm, mul_left_comm]
      rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i (fun j => ymGaussVec G d j * p)]
      simp only [Finset.mem_univ, if_pos, smul_eq_mul, Finset.mul_sum]
      have hsum : (∑ x : Fin 99, X i * (ymGaussVec G d x * pderiv x p))
          = ∑ x : Fin 99, ymGaussVec G d x * pderiv x p * X i :=
        Finset.sum_congr rfl fun x _ => by ring
      rw [hsum]
      ring

/-! ## 4. The constraint algebra -/

/-- A generic sum of derivations, applied to a polynomial (the port of the book chapter's
`sum_smul_der_apply`, whose statement is tied to `FieldPoly`). -/
theorem sum_smul_der_apply_Ym {n : ℕ} (k : Fin n → ℂ)
    (D : Fin n → Derivation ℂ YmPoly YmPoly) (p : YmPoly) :
    (∑ h, k h • D h) p = ∑ h, k h • (D h) p := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply,
        Derivation.smul_apply, ih]

/-- Collapse a double colour sum over `A`-coordinate vectors into a single sum. -/
theorem collapse_idxA (j : Fin 3) (F : Fin 8 → Fin 8 → ℂ) :
    (∑ g : Fin 8, ∑ h : Fin 8, F g h • (X (idxA j h) : YmPoly))
      = ∑ h : Fin 8, (∑ g : Fin 8, F g h) • (X (idxA j h) : YmPoly) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun h _ => (Finset.sum_smul).symm

/-- Collapse a double colour sum over jet-coordinate vectors into a single sum. -/
theorem collapse_idxD (j k : Fin 3) (F : Fin 8 → Fin 8 → ℂ) :
    (∑ g : Fin 8, ∑ h : Fin 8, F g h • (X (idxD j k h) : YmPoly))
      = ∑ h : Fin 8, (∑ g : Fin 8, F g h) • (X (idxD j k h) : YmPoly) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun h _ => (Finset.sum_smul).symm

/-- **The contracted field identity over `ℂ`**: `gauss_field_identity` transported along
`ℝ ↪ ℂ`. -/
theorem field_identity_C (G : GaugeAlgebra 8) (a c e g : Fin 8) :
    (∑ b : Fin 8, ((G.f a b e : ℝ) : ℂ) * ((G.f b g c : ℝ) : ℂ))
        - (∑ b : Fin 8, ((G.f a b c : ℝ) : ℂ) * ((G.f b g e : ℝ) : ℂ))
      = ∑ h : Fin 8, ((G.f c e h : ℝ) : ℂ) * ((G.f a g h : ℝ) : ℂ) := by
  have hpt : ∀ (u v : Fin 8 → ℝ),
      (∑ b : Fin 8, ((u b : ℝ) : ℂ) * ((v b : ℝ) : ℂ))
        = ((∑ b : Fin 8, u b * v b : ℝ) : ℂ) := by
    intro u v
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun b _ => (Complex.ofReal_mul _ _).symm
  rw [hpt, hpt, hpt, ← Complex.ofReal_sub, gauss_field_identity G a c e g]

/-- **Applying a constraint to the colour rotation of an `A`-coordinate vector**: the colour
index is rotated twice, and the result is again a combination of `A`-coordinate vectors. -/
theorem rotA_apply (G : GaugeAlgebra 8) (d d' : Fin 8) (j : Fin 3) (b : Fin 8) :
    ymGaussDer G d' (∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxA j g))
      = ∑ h : Fin 8,
          (∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) * ((G.f g h d' : ℝ) : ℂ)) • X (idxA j h) := by
  rw [map_sum]
  have hterm : ∀ g : Fin 8,
      ymGaussDer G d' (((G.f b g d : ℝ) : ℂ) • X (idxA j g))
        = ∑ h : Fin 8, (((G.f b g d : ℝ) : ℂ) * ((G.f g h d' : ℝ) : ℂ)) • X (idxA j h) := by
    intro g
    rw [Derivation.map_smul, ymGaussDer_X, ymGaussVec_idxA, Finset.smul_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun g _ => hterm g]
  exact collapse_idxA j _

/-- The constraint combination `Σ_h f_{ceh} 𝒢_h` on an `A`-coordinate. -/
theorem rotA_rhs (G : GaugeAlgebra 8) (c e : Fin 8) (j : Fin 3) (b : Fin 8) :
    (∑ h : Fin 8, ((G.f c e h : ℝ) : ℂ) • ymGaussVec G h (idxA j b))
      = ∑ g : Fin 8,
          (∑ h : Fin 8, ((G.f c e h : ℝ) : ℂ) * ((G.f b g h : ℝ) : ℂ)) • X (idxA j g) := by
  have hterm : ∀ h : Fin 8, ((G.f c e h : ℝ) : ℂ) • ymGaussVec G h (idxA j b)
      = ∑ g : Fin 8, (((G.f c e h : ℝ) : ℂ) * ((G.f b g h : ℝ) : ℂ)) • X (idxA j g) := by
    intro h
    rw [ymGaussVec_idxA, Finset.smul_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun h _ => hterm h]
  exact collapse_idxA j _

/-- **Applying a constraint to the colour rotation of a jet-coordinate vector**. -/
theorem rotD_apply (G : GaugeAlgebra 8) (d d' : Fin 8) (j k : Fin 3) (b : Fin 8) :
    ymGaussDer G d' (∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) • X (idxD j k g))
      = ∑ h : Fin 8,
          (∑ g : Fin 8, ((G.f b g d : ℝ) : ℂ) * ((G.f g h d' : ℝ) : ℂ)) • X (idxD j k h) := by
  rw [map_sum]
  have hterm : ∀ g : Fin 8,
      ymGaussDer G d' (((G.f b g d : ℝ) : ℂ) • X (idxD j k g))
        = ∑ h : Fin 8, (((G.f b g d : ℝ) : ℂ) * ((G.f g h d' : ℝ) : ℂ)) • X (idxD j k h) := by
    intro g
    rw [Derivation.map_smul, ymGaussDer_X, ymGaussVec_idxD, Finset.smul_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun g _ => hterm g]
  exact collapse_idxD j k _

/-- The constraint combination `Σ_h f_{ceh} 𝒢_h` on a jet coordinate. -/
theorem rotD_rhs (G : GaugeAlgebra 8) (c e : Fin 8) (j k : Fin 3) (b : Fin 8) :
    (∑ h : Fin 8, ((G.f c e h : ℝ) : ℂ) • ymGaussVec G h (idxD j k b))
      = ∑ g : Fin 8,
          (∑ h : Fin 8, ((G.f c e h : ℝ) : ℂ) * ((G.f b g h : ℝ) : ℂ)) • X (idxD j k g) := by
  have hterm : ∀ h : Fin 8, ((G.f c e h : ℝ) : ℂ) • ymGaussVec G h (idxD j k b)
      = ∑ g : Fin 8, (((G.f c e h : ℝ) : ℂ) * ((G.f b g h : ℝ) : ℂ)) • X (idxD j k g) := by
    intro h
    rw [ymGaussVec_idxD, Finset.smul_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun h _ => hterm h]
  exact collapse_idxD j k _

/-- **The Gauss-law constraints close into the gauge algebra** on the jet-coordinate space:
`[𝒢_c, 𝒢_e] = Σ_h f_{ceh} 𝒢_h`.  The `A`- and jet-blocks are rotated independently, so
both are governed by `gauss_field_identity` (`field_identity_C`). -/
theorem ymGaussDer_bracket (G : GaugeAlgebra 8) (c e : Fin 8) :
    ⁅ymGaussDer G c, ymGaussDer G e⁆
      = ∑ h, ((G.f c e h : ℝ) : ℂ) • ymGaussDer G h := by
  refine MvPolynomial.derivation_ext fun i => ?_
  rw [Derivation.commutator_apply]
  -- The right-hand side applied to `X i`.
  have hR :
      (∑ h, ((G.f c e h : ℝ) : ℂ) • ymGaussDer G h) (X i)
        = ∑ h, ((G.f c e h : ℝ) : ℂ) • ymGaussVec G h i := by
    rw [sum_smul_der_apply_Ym]
    exact Finset.sum_congr rfl fun h _ => by rw [ymGaussDer_X]
  rw [ymGaussDer_X, ymGaussDer_X, hR]
  -- Case analysis on the coordinate.
  by_cases hlo : 3 ≤ i.val ∧ i.val < 27
  · obtain ⟨j, b, heq⟩ := idxA_surjective_val i hlo.1 hlo.2
    subst heq
    have h1 : ymGaussVec G e (idxA j b) = ∑ g : Fin 8, ((G.f b g e : ℝ) : ℂ) • X (idxA j g) :=
      ymGaussVec_idxA G e j b
    have h2 : ymGaussVec G c (idxA j b) = ∑ g : Fin 8, ((G.f b g c : ℝ) : ℂ) • X (idxA j g) :=
      ymGaussVec_idxA G c j b
    rw [h1, h2, rotA_apply G e c j b, rotA_apply G c e j b, rotA_rhs G c e j b,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← sub_smul]
    exact congrArg (fun z : ℂ => z • X (idxA j h)) (field_identity_C G b c e h)
  · by_cases hlo2 : 27 ≤ i.val
    · obtain ⟨j, k, b, heq⟩ := idxD_surjective_val i hlo2
      subst heq
      have h1 : ymGaussVec G e (idxD j k b) = ∑ g : Fin 8, ((G.f b g e : ℝ) : ℂ) • X (idxD j k g) :=
        ymGaussVec_idxD G e j k b
      have h2 : ymGaussVec G c (idxD j k b) = ∑ g : Fin 8, ((G.f b g c : ℝ) : ℂ) • X (idxD j k g) :=
        ymGaussVec_idxD G c j k b
      rw [h1, h2, rotD_apply G e c j k b, rotD_apply G c e j k b, rotD_rhs G c e j k b,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← sub_smul]
      exact congrArg (fun z : ℂ => z • X (idxD j k h)) (field_identity_C G b c e h)
    · push_neg at hlo hlo2
      have hi3 : i.val < 3 := by omega
      rw [ymGaussVec_x G e i hi3, ymGaussVec_x G c i hi3, map_zero, map_zero, sub_self]
      rw [Finset.sum_eq_zero]
      intro h _
      rw [ymGaussVec_x G h i hi3, smul_zero]

/-- The constraint bracket at the `Module.End` level. -/
theorem ymGaussPoly_bracket (G : GaugeAlgebra 8) (c e : Fin 8) :
    ymGaussPoly G c * ymGaussPoly G e - ymGaussPoly G e * ymGaussPoly G c
      = ∑ h, ((G.f c e h : ℝ) : ℂ) • ymGaussPoly G h := by
  refine LinearMap.ext fun p => ?_
  have h := congrArg (fun D : Derivation ℂ YmPoly YmPoly => D p) (ymGaussDer_bracket G c e)
  simp only [Derivation.commutator_apply] at h
  have hR : (∑ h, ((G.f c e h : ℝ) : ℂ) • ymGaussDer G h) p
      = ∑ h, ((G.f c e h : ℝ) : ℂ) • (ymGaussDer G h) p := sum_smul_der_apply_Ym _ _ _
  rw [hR] at h
  calc (ymGaussPoly G c * ymGaussPoly G e - ymGaussPoly G e * ymGaussPoly G c) p
      = (ymGaussDer G c) ((ymGaussDer G e) p) - (ymGaussDer G e) ((ymGaussDer G c) p) := rfl
    _ = ∑ h, ((G.f c e h : ℝ) : ℂ) • (ymGaussDer G h) p := h
    _ = (∑ h, ((G.f c e h : ℝ) : ℂ) • ymGaussPoly G h) p := by
        rw [LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun h _ => by simp [ymGaussPoly]

/-- The constraint bracket on the graded state space. -/
theorem ymGauss_bracket (G : GaugeAlgebra 8) (c e : Fin 8) :
    ymGauss G c * ymGauss G e - ymGauss G e * ymGauss G c
      = ∑ h, ((G.f c e h : ℝ) : ℂ) • ymGauss G h := by
  change ymBos (ymGaussPoly G c) * ymBos (ymGaussPoly G e)
      - ymBos (ymGaussPoly G e) * ymBos (ymGaussPoly G c)
      = ∑ h, ((G.f c e h : ℝ) : ℂ) • ymBos (ymGaussPoly G h)
  rw [← ymBos_mul, ← ymBos_mul, ← ymBos_sub, ymGaussPoly_bracket, ymBos_sum]
  exact Finset.sum_congr rfl fun h _ => ymBos_rsmul _ _

/-- The constraints commute with the ghosts (different tensor factors). -/
theorem ymGauss_ymChi_comm (G : GaugeAlgebra 8) (c a : Fin 8) :
    ymGauss G c * ymChi a = ymChi a * ymGauss G c :=
  ymBos_ymGh_comm _ _

theorem ymGauss_ymBeta_comm (G : GaugeAlgebra 8) (c a : Fin 8) :
    ymGauss G c * ymBeta a = ymBeta a * ymGauss G c :=
  ymBos_ymGh_comm _ _

/-- The constraint algebra instance the nilpotency theorem consumes. -/
theorem ymConstraintAlgebra (G : GaugeAlgebra 8) :
    ConstraintAlgebra G.f (ymGauss G) ymChi ymBeta where
  comm_chi := ymGauss_ymChi_comm G
  comm_beta := ymGauss_ymBeta_comm G
  bracket := ymGauss_bracket G

/-! ## 5. The charge -/

/-- **The BRST charge of `book.tex:7084`** on the graded `99`-coordinate space:
`Ω = i • (Σ_d 𝒢_d χ_d − ½ Σ f_{abc} χ_a χ_b β_c)`, the Weyl-gauge (spatial) charge of the
section — the same three terms as `bookOmega`, with the Gauss generators realized on the
coordinate space of `book.tex:7045`. -/
def ymOmega (G : GaugeAlgebra 8) : Module.End ℂ YmBookState :=
  Complex.I • brstCharge G.f (ymGauss G) ymChi ymBeta

/-- **The charge of the concrete model is nilpotent**, `Ω² = 0` — `bookOmega_nilpotent` for
the `99`-coordinate realization. -/
theorem ymOmega_nilpotent (G : GaugeAlgebra 8) :
    ymOmega G * ymOmega G = 0 := by
  have hnil : brstCharge G.f (ymGauss G) ymChi ymBeta
      * brstCharge G.f (ymGauss G) ymChi ymBeta = 0 :=
    brst_full_nilpotent ymGhostCar (ymConstraintAlgebra G) G.antisymm
      (fun a b c d => G.jacobi a b c d)
  rw [ymOmega, smul_mul_smul_comm, hnil, smul_zero]

end

end BookProof.BrstYmCommute
