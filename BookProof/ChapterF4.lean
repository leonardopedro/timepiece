import Mathlib
import BookProof.ChapterF3

/-!
# Chapter F4 — QFM: tomographic recovery (roadmap N14, §0 S7)

This file formalizes the tomographic-recovery half of the QFM (Quantum Flow
Matching) package (source `RiemannProof/QFM.tex` §8; reference implementation
`../unfer/qfm/`), following the N14 work-package queue (deliverables
F3.1–F3.5).  The F2.x half of N14 is on disk in
`ChapterF3.lean`/`ChapterF5.lean`/`ChapterF7.lean`.

It is the **merge (2026-07-08) of two independent Aristotle formalizations**
of the same deliverables; both are kept in full, in two sections below.

## Deliverables — first formalization (finite uniform-sign model)

* **F3.1 — Count-Sketch linearity and unbiasedness** (§8, `S₁`;
  `qfm/src/sketch.rs`).  The sketch `S₁` is linear (`csketch_add`,
  `csketch_smul`); with Rademacher signs it preserves inner products in
  expectation over the `2^d` sign patterns, `E[⟪S₁ x, S₁ y⟫] = ⟪x, y⟫`
  (`countsketch_unbiased`), via the pairwise sign identity
  `sign_pair_expectation`.
* **F3.2 — observable-matrix identity** (§8, `W_prob`; `qfm/src/observables.rs`).
  `Tr(E_{r,s}ᴴ Wᴴ Pₐ W) = conj(W_{a,r})·W_{a,s}` (`observable_matrix_identity`).
* **F3.3 — the unitary reduced flow** (§8 Phase 2; `qfm/src/potential.rs`).
  A unitary matrix preserves the Hermitian dot product
  (`unitary_preserves_dotProduct`); `e^{i H}` of a self-adjoint `H` is unitary
  (`selfAdjoint_exp_star_mul_self`).
* **F3.4 — the pseudo-inverse left-inverse** (§8, `Φ̃⁺`).  For full-column-rank
  `Φ`, `Φ⁺ = (Φᴴ Φ)⁻¹ Φᴴ` satisfies `Φ⁺ Φ = I` (`pseudoinverse_left_inverse`).

## Deliverables — second formalization (measure-theoretic model) + F3.5

* **F3.1** — Count-Sketch over an abstract probability space: linearity
  (`countSketch_add`) and unbiasedness `E[⟪S₁ x, S₁ y⟫] = ⟪x, y⟫` from the
  Rademacher hypothesis `∫ s c · s c' = δ_{cc'}` (`countSketch_unbiased`).
* **F3.2** — `Tr(E_{r,s}ᴴ Wᴴ Pₐ W) = conj(W_{a,r})·W_{a,s}`
  (`observable_matrix_entry`).
* **F3.3** — for Hermitian `H`, `e^{-i t H}` is unitary
  (`hermitian_flow_unitary`), hence norm-preserving
  (`hermitian_flow_preserves_normSq`).
* **F3.4** — Moore–Penrose left inverse via `Invertible (ΦᵀΦ)`
  (`pseudoInverse_left_inverse`).
* **F3.5 — the Misra–Gries heavy-hitter bound** (§8 Phase 4): with `k`
  counters, the estimate `f̂` of any item in a stream of length `N` satisfies
  `f − N/k ≤ f̂ ≤ f` (`misraGries_bound`; state machine `mgStep`/`mgRun`,
  conservation invariant `mgRun_sum`).  An independent formalization of F3.5
  also lives in `ChapterF6.lean` (`misra_gries_bound`).

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis, no `axiom`**.
-/

open scoped BigOperators Matrix

namespace BookProof.ChapterF4

/-! ### First formalization — finite uniform-sign model -/

noncomputable section
open Matrix

/-! ## F3.1 — Count-Sketch linearity and unbiasedness (`qfm/src/sketch.rs`) -/

/-- A Rademacher sign from a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by
  cases b <;> simp [sgn]

variable {d k : ℕ}

/-- The Count-Sketch map `S₁` with hash `h` and sign pattern `ω`:
`(S₁ x)_j = Σ_{c : h c = j} s(c)·x_c`. -/
def csketch (h : Fin d → Fin k) (ω : Fin d → Bool) (x : Fin d → ℝ) (j : Fin k) : ℝ :=
  ∑ c, (if h c = j then sgn (ω c) * x c else 0)

/-
**F3.1** (linearity in the data): `S₁ (x + y) = S₁ x + S₁ y`.
-/
theorem csketch_add (h : Fin d → Fin k) (ω : Fin d → Bool) (x y : Fin d → ℝ) :
    csketch h ω (x + y) = csketch h ω x + csketch h ω y := by
  ext j; exact (by
  unfold csketch; simp +decide [ Finset.sum_add_distrib, mul_add ] ;
  simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring;);

/-
**F3.1** (homogeneity in the data): `S₁ (a • x) = a • S₁ x`.
-/
theorem csketch_smul (h : Fin d → Fin k) (ω : Fin d → Bool) (a : ℝ) (x : Fin d → ℝ) :
    csketch h ω (a • x) = a • csketch h ω x := by
  unfold csketch;
  ext j; simp +decide [ mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] ;

/-- The uniform expectation over the `2^d` sign patterns `ω : Fin d → Bool`. -/
def expectation (f : (Fin d → Bool) → ℝ) : ℝ := (∑ ω, f ω) / (2 ^ d)

/-
**F3.1** (pairwise sign identity — the independence input): summing
`s(c)·s(c')` over all `2^d` sign patterns gives `2^d` if `c = c'` and `0`
otherwise (Rademacher signs are orthonormal in expectation).
-/
theorem sign_pair_expectation (c c' : Fin d) :
    (∑ ω : Fin d → Bool, sgn (ω c) * sgn (ω c')) = if c = c' then (2 ^ d : ℝ) else 0 := by
  by_cases h : c = c';
  · simp +decide [ ← sq, h, sgn_sq ];
  · -- For $c \ne c'$, we can pair each $\omega$ with $\omega'$ where $\omega'$ differs from $\omega$ only at position $c$.
    have h_pair : ∑ ω : Fin d → Bool, sgn (ω c) * sgn (ω c') = ∑ ω : Fin d → Bool, -sgn (ω c) * sgn (ω c') := by
      apply Finset.sum_bij (fun ω _ => Function.update ω c (¬ω c));
      · simp;
      · intro a₁ _ a₂ _ h; ext i; by_cases hi : i = c <;> replace h := congr_fun h i <;> aesop;
      · exact fun b _ => ⟨ Function.update b c ( ¬b c ), Finset.mem_univ _, by aesop ⟩;
      · simp +decide [ sgn, h ];
        grind;
    norm_num [ Finset.sum_neg_distrib, neg_mul ] at * ; split_ifs ; linarith

/-
**F3.1** (unbiasedness): `E[⟪S₁ x, S₁ y⟫] = ⟪x, y⟫` — the Count-Sketch
estimator is unbiased for the inner product.
-/
theorem countsketch_unbiased (h : Fin d → Fin k) (x y : Fin d → ℝ) :
    expectation (fun ω => ∑ j, csketch h ω x j * csketch h ω y j) = ∑ c, x c * y c := by
  -- Apply the linearity of the expectation and the fact that `sgn (ω c)` are independent Rademacher variables.
  have h_exp : ∑ ω : Fin d → Bool, (∑ j : Fin k, csketch h ω x j * csketch h ω y j) = ∑ c, ∑ c', (if h c = h c' then (∑ ω : Fin d → Bool, sgn (ω c) * sgn (ω c')) * (x c * y c') else 0) := by
    have h_exp : ∀ ω : Fin d → Bool, ∑ j : Fin k, csketch h ω x j * csketch h ω y j = ∑ c, ∑ c', (if h c = h c' then sgn (ω c) * sgn (ω c') * (x c * y c') else 0) := by
      intro ω;
      simp +decide [ csketch, Finset.sum_ite ];
      simp +decide only [mul_comm, Finset.sum_mul _ _ _, Finset.mul_sum, mul_left_comm, mul_assoc];
      simp +decide only [Finset.sum_sigma'];
      refine' Finset.sum_bij ( fun x hx => ⟨ x.snd.fst, x.snd.snd ⟩ ) _ _ _ _ <;> aesop;
    simp +decide only [h_exp, Finset.sum_mul];
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp +decide [ * ] );
  convert congr_arg ( fun x : ℝ => x / 2 ^ d ) h_exp using 1;
  rw [ Finset.sum_div _ _ _ ] ; congr ; ext c ; rw [ Finset.sum_eq_single c ] <;> simp +contextual [ Finset.sum_ite, sign_pair_expectation ] ; ring;
  grind

/-! ## F3.2 — the observable-matrix identity (`qfm/src/observables.rs`) -/

/-
**F3.2**: with one-hot projector `Pₐ = |a⟩⟨a|` (`Matrix.single a a 1`) and the
Krylov operator basis element `E_{r,s} = |e_r⟩⟨e_s|` (`Matrix.single r s 1`), the
probability-observable matrix entry is
`Tr(E_{r,s}ᴴ · Wᴴ · Pₐ · W) = conj(W_{a,r})·W_{a,s}`.
-/
theorem observable_matrix_identity {dd kk : ℕ} (W : Matrix (Fin dd) (Fin kk) ℂ)
    (a : Fin dd) (r s : Fin kk) :
    Matrix.trace ((Matrix.single r s (1 : ℂ) : Matrix (Fin kk) (Fin kk) ℂ)ᴴ * Wᴴ
        * (Matrix.single a a (1 : ℂ) : Matrix (Fin dd) (Fin dd) ℂ) * W)
      = (starRingEnd ℂ) (W a r) * W a s := by
  simp +decide [ Matrix.trace, Matrix.mul_apply ];
  rw [ Finset.sum_eq_single s ] <;> simp_all +decide [ Finset.sum_eq_single, Matrix.single, mul_comm ];
  exact fun b hb => Finset.sum_eq_zero fun x hx => if_neg <| by tauto;

/-! ## F3.3 — the unitary reduced flow (`qfm/src/potential.rs`) -/

/-
**F3.3** (inner-product preservation): a unitary matrix `U` (with `Uᴴ U = 1`)
preserves the Hermitian dot product `⟪x, y⟫ = star x ⬝ᵥ y`.  In particular
`‖U x‖ = ‖x‖` (take `y = x`): norm-preserving generation.
-/
theorem unitary_preserves_dotProduct {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) (x y : Fin n → ℂ) :
    star (U.mulVec x) ⬝ᵥ U.mulVec y = star x ⬝ᵥ y := by
  -- By the properties of the Hermitian transpose, we have:
  have h_star_mul : star (U *ᵥ x) = (star x) ᵥ* Uᴴ := by
    have h_conj : ∀ (v : Fin n → ℂ), star (U *ᵥ v) = (star v) ᵥ* Uᴴ := by
      intro v; ext i; simp +decide [ Matrix.mulVec, dotProduct, mul_comm ] ;
      simp +decide [ Matrix.vecMul, dotProduct, mul_comm ]
    exact h_conj x;
  simp_all +decide [ Matrix.vecMul_mulVec, Matrix.vecMul_vecMul ];
  simp +decide [ Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec, hU ]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-
**F3.3** (the generator is unitary): for a self-adjoint `H`, the flow
`e^{i H} = selfAdjoint.expUnitary H` is unitary: `star U · U = 1`.
-/
theorem selfAdjoint_exp_star_mul_self (h : selfAdjoint A) :
    star ((selfAdjoint.expUnitary h : A)) * (selfAdjoint.expUnitary h : A) = 1 := by
  exact Unitary.coe_star_mul_self (selfAdjoint.expUnitary h)

/-! ## F3.4 — the pseudo-inverse left-inverse -/

/-
**F3.4**: for a full-column-rank matrix `Φ` (so the Gram matrix `Φᴴ Φ` is
invertible), the Moore–Penrose pseudo-inverse `Φ⁺ = (Φᴴ Φ)⁻¹ Φᴴ` is a left
inverse, `Φ⁺ Φ = I` — the subspace-recovery guarantee.
-/
theorem pseudoinverse_left_inverse {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℂ)
    (h : IsUnit (Φᴴ * Φ).det) :
    ((Φᴴ * Φ)⁻¹ * Φᴴ) * Φ = 1 := by
  simp_all +decide [ Matrix.mul_assoc, Matrix.nonsing_inv_apply_not_isUnit ]


end

/-! ### Second formalization — measure-theoretic model, and F3.5 -/

noncomputable section
open MeasureTheory

/-! ## F3.1 — Count-Sketch linearity and unbiasedness -/

variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

/-- The Count-Sketch map `S₁ : ℝ^α → ℝ^κ` (§8): `(S₁ x)_h = Σ_{c : hash c = h} s(c) x_c`,
with hash function `hash` and per-coordinate random signs `s`. -/
def countSketch (hash : α → κ) (s : α → Ω → ℝ) (x : α → ℝ) (ω : Ω) (h : κ) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => hash c = h), s c ω * x c

/-
The Count-Sketch map is linear in the input vector `x`.
-/
theorem countSketch_add (hash : α → κ) (s : α → Ω → ℝ) (x y : α → ℝ) (ω : Ω) (h : κ) :
    countSketch hash s (x + y) ω h = countSketch hash s x ω h + countSketch hash s y ω h := by
  unfold countSketch; simp +decide [ mul_add, Finset.sum_add_distrib ] ;

/-
**F3.1** (unbiasedness): with Rademacher signs (`E[s(c) s(c')] = δ_{cc'}`), the
Count-Sketch estimator preserves inner products in expectation:
`E[⟪S₁ x, S₁ y⟫] = ⟪x, y⟫`.  The AMS/Count-Sketch estimator.
-/
theorem countSketch_unbiased (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hash : α → κ) (s : α → Ω → ℝ) (x y : α → ℝ)
    (hint : ∀ c c', Integrable (fun ω => s c ω * s c' ω) μ)
    (hs : ∀ c c', ∫ ω, s c ω * s c' ω ∂μ = if c = c' then 1 else 0) :
    ∫ ω, (∑ h, countSketch hash s x ω h * countSketch hash s y ω h) ∂μ
      = ∑ c, x c * y c := by
  rw [ MeasureTheory.integral_finset_sum ];
  · -- Expand the product inside the integral.
    have h_expand : ∀ ω h, (countSketch hash s x ω h) * (countSketch hash s y ω h) = ∑ c ∈ Finset.univ.filter (fun c => hash c = h), ∑ c' ∈ Finset.univ.filter (fun c' => hash c' = h), (x c * y c') * (s c ω * s c' ω) := by
      exact fun ω h => by rw [ countSketch, countSketch, Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by ring;
    simp +decide only [h_expand];
    rw [ Finset.sum_congr rfl fun h _ => MeasureTheory.integral_finset_sum _ fun c _ => ?_ ];
    · rw [ Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun i hi => MeasureTheory.integral_finset_sum _ fun j hj => ?_ ];
      · simp +decide only [integral_const_mul, hs];
        simp +decide [ Finset.sum_filter, Finset.sum_comm ];
      · exact MeasureTheory.Integrable.const_mul ( ‹∀ c c', Integrable ( fun ω => s c ω * s c' ω ) μ› i j ) _;
    · exact MeasureTheory.integrable_finset_sum _ fun c' _ => MeasureTheory.Integrable.const_mul ( ‹∀ c c', MeasureTheory.Integrable ( fun ω => s c ω * s c' ω ) μ› c c' ) _;
  · intro h _; simp +decide [ countSketch ] ;
    simp +decide only [Finset.sum_mul _ _ _, Finset.mul_sum];
    refine' MeasureTheory.integrable_finset_sum _ fun i hi => MeasureTheory.integrable_finset_sum _ fun j hj => _;
    convert MeasureTheory.Integrable.const_mul ( MeasureTheory.Integrable.const_mul ( ‹∀ c c', MeasureTheory.Integrable ( fun ω => s c ω * s c' ω ) μ› i j ) ( x i ) ) ( y j ) using 2 ; ring

/-! ## F3.2 — the observable-matrix identities -/

/-
**F3.2** (observable-matrix entry, outer-product-of-a-row identity): with the
one-hot projector `P_a = |a⟩⟨a|` and operator basis `E_{r,s} = |e_r⟩⟨e_s|`,
`Tr(E_{r,s}ᴴ Wᴴ P_a W) = conj(W_{a,r}) · W_{a,s}`.
-/
set_option maxHeartbeats 800000 in
theorem observable_matrix_entry {d n : ℕ} (W : Matrix (Fin d) (Fin n) ℂ)
    (a : Fin d) (r s : Fin n) :
    Matrix.trace ((Matrix.single r s (1 : ℂ))ᴴ * Wᴴ * Matrix.single a a (1 : ℂ) * W)
      = (starRingEnd ℂ) (W a r) * W a s := by
  simp +decide [ Matrix.trace, Matrix.mul_apply, Matrix.single ];
  simp +contextual [ Finset.sum_ite, Finset.filter_eq, Finset.filter_and, mul_comm ];
  rw [ Finset.sum_eq_single s ] <;> simp +contextual [ Finset.sum_ite ];
  · rw [ Finset.sum_eq_single a ] <;> aesop;
  · aesop

/-! ## F3.3 — the unitary reduced flow -/

/-
**F3.3** (unitary reduced flow): for a Hermitian matrix `H`, the reduced flow
`U = e^{-i t H}` is unitary, `Uᴴ * U = 1`.
-/
theorem hermitian_flow_unitary {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))ᴴ
        * NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) = 1 := by
  -- By definition of exponentiation, we know that $(e^{i t H})^* = e^{-i t H}$.
  have h_exp_conj : (NormedSpace.exp (-(Complex.I * t) • H))ᴴ = NormedSpace.exp ((Complex.I * t) • H) := by
    simp_all +decide [ Matrix.IsHermitian, Matrix.conjTranspose_smul ];
    rw [ ← Matrix.exp_conjTranspose ];
    simp +decide [ Matrix.conjTranspose_smul, hH ];
  convert congr_arg₂ ( fun x y => x * y ) h_exp_conj rfl using 1 ; ring;
  congr! 1;
  rw [ ← Matrix.exp_add_of_commute ];
  · norm_num [ ← add_smul ];
  · exact Commute.smul_left ( Commute.smul_right ( Commute.refl _ ) _ ) _

/-
**F3.3** (norm-preserving generation): the reduced flow `U = e^{-i t H}` of a
Hermitian generator preserves the ℓ² norm-squared of any state,
`‖U c₀‖² = ‖c₀‖²` (the rev-14 `preserves_norm` guarantee).
-/
theorem hermitian_flow_preserves_normSq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) (c : Fin n → ℂ) :
    star ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)).mulVec c)
          ⬝ᵥ (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)).mulVec c
      = star c ⬝ᵥ c := by
  have hU : (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))ᴴ * NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) = 1 := by
    convert hermitian_flow_unitary H hH t using 1;
  have hstar : star (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) *ᵥ c) = star c ᵥ* (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))ᴴ := by
    ext i; simp +decide [ Matrix.mulVec, dotProduct ] ;
    simp +decide [ Matrix.vecMul, dotProduct, mul_comm ];
  simp_all +decide [ Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec ]

/-! ## F3.4 — the pseudo-inverse left-inverse -/

/-
**F3.4** (subspace-recovery guarantee): for a full-column-rank matrix `Φ` (so
that the Gram matrix `ΦᵀΦ` is invertible), the Moore–Penrose pseudo-inverse
`Φ⁺ = (ΦᵀΦ)⁻¹Φᵀ` is a left inverse: `Φ⁺ Φ = I`.
-/
theorem pseudoInverse_left_inverse {k m : ℕ} (Φ : Matrix (Fin k) (Fin m) ℝ)
    [Invertible (Φᵀ * Φ)] :
    ⅟(Φᵀ * Φ) * Φᵀ * Φ = 1 := by
  simp +decide [ Matrix.mul_assoc ]

/-! ## F3.5 — the Misra–Gries heavy-hitter bound -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Number of currently-active Misra–Gries counters (the support size of `c`). -/
def mgSupport (c : ι → ℕ) : ℕ := (Finset.univ.filter (fun a => 0 < c a)).card

/-- One step of Misra–Gries with `k` counters on state `(c, d)` (`c` the counter
vector, `d` the number of decrement rounds so far), processing item `x`:
increment `c x` if `x` is already tracked; else open a fresh counter if fewer
than `k` are active; else decrement every counter and record one decrement
round.  (`qfm` Misra–Gries heavy-hitter stage, §8 Phase 4.) -/
def mgStep (k : ℕ) (st : (ι → ℕ) × ℕ) (x : ι) : (ι → ℕ) × ℕ :=
  if 0 < st.1 x then (Function.update st.1 x (st.1 x + 1), st.2)
  else if mgSupport st.1 < k then (Function.update st.1 x 1, st.2)
  else (fun a => st.1 a - 1, st.2 + 1)

/-- The Misra–Gries run over a stream `xs` (processed from right to left; the
error bound is order-independent).  Returns `(f̂, d)` with `f̂` the counter
estimates and `d` the number of decrement rounds. -/
def mgRun (k : ℕ) : List ι → (ι → ℕ) × ℕ
  | [] => (fun _ => 0, 0)
  | x :: xs => mgStep k (mgRun k xs) x

/-
Helper: decrementing every counter by one reduces the total by exactly the
number of active counters.  Stated additively over `ℕ` to avoid truncated
subtraction.
-/
theorem mgSum_decrement (c : ι → ℕ) :
    (∑ a, (c a - 1)) + mgSupport c = ∑ a, c a := by
      rw [ mgSupport ];
      rw [ Finset.card_filter, ← Finset.sum_add_distrib ];
      exact Finset.sum_congr rfl fun x _ => by split_ifs <;> omega;

/-
One-step preservation of the invariant "at most `k` counters are active".
-/
theorem mgStep_support_le (k : ℕ) (st : (ι → ℕ) × ℕ) (x : ι)
    (h : mgSupport st.1 ≤ k) : mgSupport (mgStep k st x).1 ≤ k := by
      unfold mgStep;
      split_ifs;
      · unfold mgSupport at *;
        convert h using 2 ; ext a ; by_cases ha : a = x <;> simp +decide [ *, Function.update_apply ];
      · refine' le_trans _ ‹_›;
        exact Finset.card_le_card ( show Finset.filter ( fun a => 0 < ( Function.update st.1 x 1 ) a ) Finset.univ ⊆ Finset.filter ( fun a => 0 < st.1 a ) Finset.univ ∪ { x } from fun a ha => by by_cases ha' : a = x <;> aesop ) |> le_trans <| Finset.card_union_le _ _;
      · refine' le_trans _ h;
        refine' Finset.card_le_card _;
        grind

/-
Invariant: at most `k` counters are ever active.
-/
theorem mgRun_support_le (k : ℕ) (xs : List ι) :
    mgSupport (mgRun k xs).1 ≤ k := by
      -- We proceed by induction on `xs`.
      induction' xs with a xs ih;
      · simp +decide [ mgRun ];
        simp +decide [ mgSupport ];
      · convert mgStep_support_le k ( mgRun k xs ) a ih using 1

/-
Master conservation invariant: the total counter mass plus `(k+1)` per
decrement round equals the stream length `N`.
-/
theorem mgRun_sum (k : ℕ) (xs : List ι) :
    (∑ a, (mgRun k xs).1 a) + (k + 1) * (mgRun k xs).2 = xs.length := by
      induction' xs with xs ih;
      · simp +decide [ mgRun ];
      · rw [ show mgRun k ( xs :: ih ) = mgStep k ( mgRun k ih ) xs from rfl ];
        unfold mgStep; split_ifs <;> simp_all +decide [ mgSupport ] ;
        · simp +decide [ *, Finset.sum_update_of_mem ];
          rw [ ← Finset.sum_sdiff ( Finset.subset_univ { xs } ) ] at * ; simp_all +decide [ Finset.sum_singleton ] ; linarith;
        · rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ xs ) ] at *;
          simp_all +decide [ Function.update_apply ];
          rw [ Finset.sum_congr rfl fun x hx => if_neg ( Finset.mem_singleton.not.mp ( Finset.mem_sdiff.mp hx |>.2 ) ) ] ; linarith;
        · have := mgSum_decrement ( mgRun k ih |>.1 ) ; simp_all +decide [ mgSupport ] ;
          linarith [ show Finset.card ( Finset.filter ( fun a => 0 < ( mgRun k ih |>.1 ) a ) Finset.univ ) = k from le_antisymm ( mgRun_support_le k ih ) ‹_› ]

/-
Decrement budget: `k · d ≤ N`.
-/
theorem mgRun_decrement_le (k : ℕ) (xs : List ι) :
    k * (mgRun k xs).2 ≤ xs.length := by
      have := mgRun_sum k xs;
      lia

/-
Undercounting: the estimate never exceeds the true frequency.
-/
theorem mgRun_undercount (k : ℕ) (xs : List ι) (x : ι) :
    (mgRun k xs).1 x ≤ xs.count x := by
      induction xs generalizing x ; simp_all +decide [ mgRun ];
      rename_i a l ih;
      by_cases h : 0 < (mgRun k l).1 a <;> simp_all +decide [ mgRun, mgStep ];
      · grind;
      · split_ifs <;> simp_all +decide [ List.count_cons ];
        · grind;
        · exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( ih x ) ( Nat.zero_le _ ) ) zero_le_one

/-
The estimation error is bounded by the number of decrement rounds.
-/
theorem mgRun_error_le (k : ℕ) (xs : List ι) (x : ι) :
    xs.count x ≤ (mgRun k xs).1 x + (mgRun k xs).2 := by
      induction' xs with a xs ih generalizing x <;> simp_all +decide [ mgRun ];
      by_cases hx : x = a <;> simp_all +decide [ List.count_cons ];
      · unfold mgStep; split_ifs <;> simp_all +decide [ mgRun ] ;
        · linarith [ ih a ];
        · grind;
        · grind;
      · unfold mgStep; split_ifs <;> simp_all +decide [ Function.update_apply ] ;
        grind

/-
**F3.5** (Misra–Gries heavy-hitter guarantee): with `k` counters, the
frequency estimate `f̂ x = (mgRun k xs).1 x` of any item `x` in a stream `xs`
of length `N = xs.length` satisfies `f - N/k ≤ f̂ ≤ f`, where `f = xs.count x`
is the true frequency.  The lower bound is stated in the equivalent
truncated-subtraction-free form `f ≤ f̂ + N/k`.
-/
theorem misraGries_bound (k : ℕ) (hk : 0 < k) (xs : List ι) (x : ι) :
    (mgRun k xs).1 x ≤ xs.count x ∧
      xs.count x ≤ (mgRun k xs).1 x + xs.length / k := by
        refine ⟨mgRun_undercount k xs x, ?_⟩
        have hd : (mgRun k xs).2 ≤ xs.length / k :=
          (Nat.le_div_iff_mul_le hk).2 (by linarith [mgRun_decrement_le k xs])
        calc xs.count x ≤ (mgRun k xs).1 x + (mgRun k xs).2 := mgRun_error_le k xs x
          _ ≤ (mgRun k xs).1 x + xs.length / k := by omega


end

end BookProof.ChapterF4
