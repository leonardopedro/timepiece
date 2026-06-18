import Mathlib
import PnpProof.Kopperman

/-!
# Part 12: The geometric truth model — P vs NP as a vector identity

This module realizes `PNP_IMPLEMENTATION_PLAN.md` Part 12: a `Π⁰₂` arithmetical
sentence `∀ x ∃ y, p x y` is encoded as a single *completed vector*
`Ψ_p = Σ_x OK_p x /(x+1) · e_x` in the separable Hilbert substrate (over an
ℕ-indexed Hilbert basis `{e_x}`), and its truth is read off as the **metric
identity** `‖Ψ_p − Ψ_true‖ = 0`.

This is a strict refinement of the trivial `interpPi02`/`arith_truth_invariant`
wrappers in `Kopperman.lean`: `interpPi02_geom_iff` proves the vector identity
*equals* `Pi02 p`, now with a concrete witness in the substrate rather than
`Iff.rfl`.

## Fences (carried over from Parts 8–11, unchanged)

* **Restatement, not decision.** `interpPi02_geom_iff` proves the identity equals
  `Pi02 p`; it does not evaluate either side. Computing `‖Ψ_p − Ψ_true‖` requires
  knowing `OK_p`, i.e. deciding the `Σ⁰₁` sub-formula. The geometry stores the
  answer; it does not compute it.
* **`okOf` / `psiOf` are noncomputable (`Classical.choice`).** The completed
  "Turing-jump" vector exists as a coordinate only via classical comprehension —
  an expressibility/definability device, not a provability one. This places this
  module in the measure/formalism tier, **not** the arithmetic tier.
* **No Clay leverage; T5 stands.** Encoding the standard sentence as a vector
  identity makes the *statement* canonical inside the model; it does not make the
  model's measure separation `σ` prove it. `model_vs_clay_disjointness` (T5) is
  untouched. Do not chain this into any `σ → P_ne_NP` argument.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

noncomputable section

namespace PnpProof
namespace Kopperman

/-! ### K12.1. The coefficient sequence lies in ℓ² -/

/-- Coefficients of `Ψ` for a truth-function `g : ℕ → Bool`:
`coeff g x = [g x] / (x+1)`. -/
def coeff (g : ℕ → Bool) : ℕ → ℝ := fun x => (if g x then (1 : ℝ) else 0) / (x + 1)

theorem coeff_memlp (g : ℕ → Bool) : Memℓp (coeff g) 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hrpow : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ 2 := fun y => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrpow]
  have hsum : Summable (fun x : ℕ => 1 / ((x : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h
    refine h2.congr (fun n => ?_)
    push_cast
    ring_nf
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) hsum
  have hb : ((if g x then (1 : ℝ) else 0)) ^ 2 ≤ 1 := by
    by_cases h : g x <;> simp [h]
  have heq : ‖coeff g x‖ ^ 2 = ((if g x then (1 : ℝ) else 0)) ^ 2 / ((x : ℝ) + 1) ^ 2 := by
    simp only [coeff, Real.norm_eq_abs, sq_abs, div_pow]
  rw [heq]
  gcongr

/-! ### K12.2. The completed vectors -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `Ψ` for a truth-function `g`: the basis-sum `Σ_x coeff(g)(x) · e_x`, realized
through `b.repr.symm`. -/
def psiOf (b : HilbertBasis ℕ ℝ H) (g : ℕ → Bool) : H :=
  b.repr.symm ⟨coeff g, coeff_memlp g⟩

/-- The "all-true" target `Ψ_true`. -/
def psiTrue (b : HilbertBasis ℕ ℝ H) : H := psiOf b (fun _ => true)

/-! ### K12.3. The geometric truth equivalence -/

omit [CompleteSpace H] in
theorem psiOf_eq_iff (b : HilbertBasis ℕ ℝ H) (g₁ g₂ : ℕ → Bool) :
    psiOf b g₁ = psiOf b g₂ ↔ ∀ x, g₁ x = g₂ x := by
  constructor;
  · intro h x; have := congr_arg ( b.repr ) h; simp +decide [ psiOf ] at this;
    replace this := congr_fun this x; unfold coeff at this; split_ifs at this <;> simp_all +decide ;
    · norm_cast at this;
    · linarith;
  · exact fun h => by unfold psiOf; congr; ext; simp +decide [ h ] ;

omit [CompleteSpace H] in
theorem norm_psiOf_sub_eq_zero_iff (b : HilbertBasis ℕ ℝ H) (g : ℕ → Bool) :
    ‖psiOf b g - psiTrue b‖ = 0 ↔ ∀ x, g x = true := by
  convert psiOf_eq_iff b g ( fun _ => true ) using 1;
  rw [ norm_eq_zero, sub_eq_zero ];
  rfl

/-! ### K12.4. The Σ⁰₁ sub-formula as a (noncomputable) truth-function -/

open Classical in
/-- `OK_p x = decide (∃ y, p x y = true)`. NONCOMPUTABLE — the honest rendering of
"completed/`ATR₀` comprehension". -/
noncomputable def okOf (p : ℕ → ℕ → Bool) : ℕ → Bool :=
  fun x => decide (∃ y, p x y = true)

theorem okOf_all_true_iff (p : ℕ → ℕ → Bool) :
    (∀ x, okOf p x = true) ↔ Pi02 p := by
  unfold okOf; aesop;

/-! ### K12.5. Geometric interpretation of a Π⁰₂ sentence -/

/-- The **geometric interpretation**: the truth of `p` is the metric identity
`‖Ψ_p − Ψ_true‖ = 0` in the substrate of the model `F`. Refines `interpPi02`. -/
noncomputable def interpPi02_geom [MeasurableSpace H]
    (b : HilbertBasis ℕ ℝ H) (p : ℕ → ℕ → Bool) (_F : Formalism H) : Prop :=
  ‖psiOf b (okOf p) - psiTrue b‖ = 0

/-- The geometric reading is faithful: it equals the plain arithmetic sentence —
the same coincidence as `interpPi02_eq`/`arith_truth_invariant`, now with a
non-trivial vector-identity witness. -/
theorem interpPi02_geom_iff [MeasurableSpace H]
    (b : HilbertBasis ℕ ℝ H) (p : ℕ → ℕ → Bool) (F : Formalism H) :
    interpPi02_geom b p F ↔ Pi02 p := by
  unfold interpPi02_geom
  rw [norm_psiOf_sub_eq_zero_iff]
  exact okOf_all_true_iff p

/-- **Geometric `T-conserv`:** the geometric truth value of a `Π⁰₂` sentence does
not depend on which model (`Formalism`) realizes it. -/
theorem interpPi02_geom_invariant [MeasurableSpace H]
    (b : HilbertBasis ℕ ℝ H) (p : ℕ → ℕ → Bool) (F₁ F₂ : Formalism H) :
    interpPi02_geom b p F₁ ↔ interpPi02_geom b p F₂ :=
  (interpPi02_geom_iff b p F₁).trans (interpPi02_geom_iff b p F₂).symm

/-- The geometric interpretation agrees with the trivial wrapper `interpPi02`. -/
theorem interpPi02_geom_eq_interp [MeasurableSpace H]
    (b : HilbertBasis ℕ ℝ H) (p : ℕ → ℕ → Bool) (F : Formalism H) (z : ZFSet) :
    interpPi02_geom b p F ↔ interpPi02 p F z :=
  (interpPi02_geom_iff b p F).trans (interpPi02_eq p F z).symm

/-! ### K12.6. The P-vs-NP instance — assembly

Inside one model of the Kopperman formalism (`F`, with separable substrate `H`),
the standard P-vs-NP sentence is the single vector identity
`‖Ψ_{P≠NP} − Ψ_true‖ = 0`. The `Π⁰₂` SAT encoding `pPNP` and its arithmetic
identity `hPNP` are exactly the Part-11 inputs (`Pi02`/`P_ne_NP_Pi20`); this
theorem does **not** produce them and gives **no Clay leverage** (T5 stands). -/
theorem p_ne_np_geometric [MeasurableSpace H]
    (b : HilbertBasis ℕ ℝ H) (F : Formalism H)
    (pPNP : ℕ → ℕ → Bool) (P_ne_NP_arith : Prop)
    (hPNP : Pi02 pPNP ↔ P_ne_NP_arith) :
    interpPi02_geom b pPNP F ↔ P_ne_NP_arith :=
  (interpPi02_geom_iff b pPNP F).trans hPNP

end Kopperman
end PnpProof
