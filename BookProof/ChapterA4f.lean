import Mathlib
import BookProof.ChapterA4d
import BookProof.ChapterA5

/-!
# Chapter A, §A.4 — Prop 87: the localizability exclusion lemmas

Source: `book.tex` §A.4 (line 5636), **Proposition 87** — *any localizable
unitary Poincaré representation is a direct sum of irreducibles that are massive
or massless-with-discrete-helicity.*

The proof of Prop 87 (roadmap §A.4, "Localization: Notes 84–86, Props 87–88")
decomposes a localizable rep into irreducibles and, Fourier-transforming the
translation action to `(U e^{J p⃗·a⃗} U⁻¹)Ψ(p⃗) = e^{iγ⁰ p⃗·a⃗}Ψ(p⃗)`, rules out
three families of irreducibles as localizable subspaces:

1. **`m² < 0` (tachyons).**  A localizable rep needs the mass-shell relation
   `|p⃗|² = E² - m²` to have solutions for the physical momenta; the Majorana
   energy operator `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂` of §A.5 has *real* mass
   parameters, so its physical mass squared is `m² = m₁² + m₂² ≥ 0` — a
   tachyonic (`m² < 0`) dispersion cannot arise.  (`massSq_nonneg`,
   `no_tachyon`.)
2. **`p = 0` (the zero-momentum point).**  At `p⃗ = 0` the energy symbol reduces
   to the pure mass operator `M = iγ⁰m₁ + γ⁰γ⁵m₂` with `M² = -(m₁²+m₂²)·1`; the
   single zero-momentum point is a measure-zero subset of the `ℝ³` momentum
   space of a localizable (imprimitivity) system and so cannot be an invariant
   subspace.  (`zeroMomentum_symbol`.)
3. **`m² = 0` infinite (continuous) spin.**  For a massless standard momentum the
   little group is `SE(2)` (Prop 79, `ChapterA4d.massless_little_group`).  A
   `z`-boost `B = diag(l, l⁻¹) ∈ SL(2,ℂ)` *scales the `SE(2)` translation
   modulus* by `l⁻²` while fixing the `SO(2)` rotation angle, so there is **no
   boost-invariant nonzero translation label**: a continuous-spin (infinite-spin)
   irrep — one with a fixed nonzero `SE(2)` translation eigenvalue — is
   incompatible with a `p⃗`-independent Wigner rotation `S := LΛ⁻¹`.
   (`boostZ_scales_translation`, `boostZ_preserves_angle`,
   `infinite_spin_excluded`.)

Left after the three exclusions: massive + massless-with-discrete-helicity — the
content of Prop 87.  This file formalizes the concrete, self-contained algebraic
cores of the three exclusions on the `2×2` Pauli / `4×4` Majorana models of
§A.3–§A.5.  Everything is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`); **no `EXTERNAL` hypothesis** enters these
cores (Wigner little-group theory + Mackey imprimitivity remain the cited
backbone of the *decomposition/exhaustiveness* clause of Prop 87, not of these
reductions).
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterA4f

open BookProof.ChapterA3 BookProof.ChapterA5

/-! ## Exclusion 1 — no tachyons (`m² ≥ 0`) -/

/-
The Majorana physical mass squared `m² = m₁² + m₂²` is nonnegative: the two
real mass parameters combine as a sum of squares, so no tachyonic (`m² < 0`)
dispersion can arise from the real energy operator `iH` of §A.5.
-/
theorem massSq_nonneg (m₁ m₂ : ℝ) : 0 ≤ m₁ ^ 2 + m₂ ^ 2 := by
  positivity

/-
**Exclusion 1 (no tachyons), mass-shell form.**  The real energy-operator
symbol squares to `(|p⃗|² - m²)·1` with `m² = m₁² + m₂² ≥ 0`; i.e. the physical
dispersion `H² = |p⃗|² + m²` has nonnegative mass squared.
-/
theorem no_tachyon (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    energySymbolR p m₁ m₂ * energySymbolR p m₁ m₂
      = ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - (m₁ ^ 2 + m₂ ^ 2)) •
          (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
            convert BookProof.ChapterA5.energySymbolR_sq p m₁ m₂ using 1 ; ring

/-! ## Exclusion 2 — the zero-momentum point `p = 0` -/

/-
**Exclusion 2 (`p = 0`).**  At zero 3-momentum the energy symbol reduces to
the pure mass operator `M = iγ⁰m₁ + γ⁰γ⁵m₂`, which squares to `-(m₁²+m₂²)·1`.
Hence for `(m₁, m₂) ≠ 0` the zero-momentum symbol is invertible (its square is a
nonzero scalar), so the single zero-momentum point carries no proper invariant
subspace of a localizable system.
-/
theorem zeroMomentum_symbol (m₁ m₂ : ℝ) :
    energySymbolR (fun _ => 0) m₁ m₂ * energySymbolR (fun _ => 0) m₁ m₂
      = (-(m₁ ^ 2 + m₂ ^ 2)) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
        -- Apply the energySymbolR_sq theorem with p being the zero function.
        have := energySymbolR_sq (fun _ => 0) m₁ m₂;
        simp at this;
        exact this ▸ by ring;

/-! ## Exclusion 3 — no infinite (continuous) spin

The massless little group is `SE(2)`, realized (Prop 79, `ChapterA4d`) as the
lower-triangular unimodular `2×2` complex matrices `T = !![a, 0; c, a⁻¹]` with
`|a| = 1`: the diagonal `a ∈ SO(2)` is the rotation angle and the lower-left
`c = T 1 0 ∈ ℂ ≅ ℝ²` is the translation label.  A `z`-boost
`B = diag(l, l⁻¹) ∈ SL(2,ℂ)` conjugates `T` to `!![a, 0; l⁻²c, a⁻¹]`.
-/

/-- The `z`-boost `B = diag(l, l⁻¹) ∈ SL(2,ℂ)` (for `l ≠ 0`). -/
noncomputable def boostZ (l : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![l, 0; 0, l⁻¹]

/-
`det (boostZ l) = 1` for `l ≠ 0`.
-/
theorem boostZ_det {l : ℂ} (hl : l ≠ 0) : (boostZ l).det = 1 := by
  unfold boostZ; simp +decide [ hl, Matrix.det_fin_two ] ;

/-
`boostZ l · boostZ l⁻¹ = 1` for `l ≠ 0` (so `boostZ l⁻¹` is the inverse of
`boostZ l`).
-/
theorem boostZ_mul_inv {l : ℂ} (hl : l ≠ 0) : boostZ l * boostZ l⁻¹ = 1 := by
  ext i j ; fin_cases i <;> fin_cases j <;> simp +decide [ *, boostZ ]

/-
Conjugation by the `z`-boost **fixes the `SO(2)` rotation angle** `a = T 0 0`
of an `SE(2)` element.
-/
theorem boostZ_preserves_angle {l : ℂ} (hl : l ≠ 0) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (boostZ l * T * boostZ l⁻¹) 0 0 = T 0 0 := by
      unfold boostZ; simp +decide [ hl, Matrix.mul_apply ] ;
      simp +decide [ Matrix.vecMul, hl ];
      exact mul_div_cancel_left₀ _ hl

/-
**Exclusion 3, key scaling.**  Conjugation by the `z`-boost `B = diag(l,l⁻¹)`
**scales the `SE(2)` translation modulus** `c = T 1 0` by `l⁻²`.
-/
theorem boostZ_scales_translation (l : ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (boostZ l * T * boostZ l⁻¹) 1 0 = (l⁻¹) ^ 2 * T 1 0 := by
      simp +decide [ Matrix.mul_apply, pow_two, mul_assoc ];
      unfold boostZ; norm_num; ring;

/-
Conjugation by the `z`-boost keeps an `SE(2)` element inside `SE(2)`: the
massless little group is stable under `z`-boosts (as it must be, being the
stabiliser of the null axis).
-/
theorem boostZ_conj_mem {l : ℂ} (hl : l ≠ 0) {T : Matrix (Fin 2) (Fin 2) ℂ}
    (hT : T ∈ SEtwo) : boostZ l * T * boostZ l⁻¹ ∈ SEtwo := by
      refine ⟨ ?_, ?_, ?_ ⟩;
      · simp_all +decide [ Matrix.det_fin_two, boostZ ];
        simp_all +decide [ Matrix.vecMul, Matrix.mul_apply, Fin.sum_univ_succ, SEtwo ];
        simp_all +decide [ vecHead, vecTail, Matrix.det_fin_two ];
        grind;
      · simp_all +decide [ Fin.sum_univ_succ, Matrix.mul_apply ];
        simp_all +decide [ boostZ ];
        exact hT.2.1;
      · rw [ boostZ_preserves_angle hl ] ; exact hT.2.2

/-
**Exclusion 3 (no infinite spin), headline.**  If an `SE(2)` element has a
nonzero translation label `c = T 1 0 ≠ 0`, then by choosing the `z`-boost
parameter its conjugate can realize *any* nonzero translation label.  Hence there
is no boost-invariant nonzero `SE(2)` translation modulus: a continuous-spin
(infinite-spin) irrep — one pinned to a fixed nonzero translation eigenvalue —
cannot coexist with a `p⃗`-independent Wigner rotation, so it is excluded from a
localizable representation.
-/
theorem infinite_spin_excluded {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T ∈ SEtwo)
    (hc : T 1 0 ≠ 0) :
    ∀ c : ℂ, c ≠ 0 → ∃ l : ℂ, l ≠ 0 ∧ boostZ l * T * boostZ l⁻¹ ∈ SEtwo ∧
      (boostZ l * T * boostZ l⁻¹) 1 0 = c := by
  intro c hc_ne
  -- Reduce to finding `l ≠ 0` with `(l⁻¹)² * (T 1 0) = c`, via `boostZ_scales_translation`.
  suffices h_exists_l : ∃ l : ℂ, l ≠ 0 ∧ (l⁻¹) ^ 2 * T 1 0 = c by
    obtain ⟨l, hl_ne, hl_eq⟩ := h_exists_l
    exact ⟨l, hl_ne, boostZ_conj_mem hl_ne hT,
      by rw [boostZ_scales_translation]; exact hl_eq⟩
  exact ⟨(T 1 0 / c) ^ (1 / 2 : ℂ), by aesop, by
    rw [inv_pow, ← Complex.cpow_nat_mul]; norm_num [hc, hc_ne]⟩

end BookProof.ChapterA4f
