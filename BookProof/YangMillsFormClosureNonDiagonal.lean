import Mathlib
import BookProof.YangMillsFormClosure
import BookProof.YangMillsMagneticQuartic

/-!
# Chapter YangMillsFormClosureNonDiagonal — Faris–Lavine for an off-diagonal interaction

`YangMillsFormClosure` closes the Phase-4 comparison for **diagonal** forms: every form of
`YangMillsFormDomination` reads `∑ n ∈ supp c, f n ‖c n‖²`, so its core form is a sum of one
term per multi-index and `closedForm f` is the closure of it.

Its honest boundary names what that leaves open:

> It does not claim that an arbitrary non-diagonal `q` — a genuine magnetic interaction mixing
> multi-indices — is closeable with the same constants; for those the termwise estimate that
> `closedForm_scaled_le` performs does not apply and the closure would have to be built from a
> closability (KLM) argument.

This chapter supplies the form-theoretic half of that argument — the **Faris–Lavine** comparison
— for an interaction that mixes multi-indices.  The interaction is a kernel

`K : (Fin d → ℕ) → (Fin d → ℕ) → ℂ`,  `c ↦ kernelForm K c = ∑ m, ∑ n, Re(K m n · c n · conj(c m))`,

which for `K` off the diagonal couples *distinct* multi-indices, i.e. precisely the magnetic terms
the diagonal theory cannot see.

## The Hilbert–Schmidt bound

* `abs_kernelForm_le_sum` — the triangle inequality, termwise;
* `kernelForm_sq_le` — **the two-index Cauchy–Schwarz inequality**: the kernel row is paired with
the coefficient row by Cauchy–Schwarz, then the row values are paired with the coefficients again,
so the square of the absolute form is at most `(∑ m ∑ n ‖K m n‖²) · (coreNormSq c)²`;
* **`abs_kernelForm_le_of_hs`** — a kernel whose finite-square Hilbert–Schmidt sums are bounded by
  `σ²` has `|kernelForm K c| ≤ σ · coreNormSq c` for every core state.  This is the form bound the
  interaction enters through; it is what makes the interaction *form small* uniformly in the state,
  with no support restriction.

## Faris–Lavine

* **`farisLavine_domination`** — if `q'` dominates the reference form with ratio `c₁` and shift
  `c₂`, and the off-diagonal interaction is form bounded by `|qK| ≤ a·q' + b‖·‖²` with relative
  bound `a < 1`, then the **sum form** `q' + qK` dominates with ratio `(1 − a)·c₁ > 0` and shift
  `(1 − a)·c₂ + b`.  The ratio stays strictly positive, which is what the gap argument needs: the
  certified separation `c₁ Δ_ref` degrades by the factor `1 − a` and is not destroyed.
* `farisLavine_of_bounded_interaction` — the bounded case `a = 0`, where the ratio is `c₁`
  **unchanged** and the interaction costs only the shift term `b`.

## A concrete off-diagonal interaction

`hoppingKernel m₀ n₀` is the matrix unit at `(m₀, n₀)`: it couples the two multi-indices `m₀` and
`n₀` and nothing else.

* `hoppingKernel_sq_sum_le` — its Hilbert–Schmidt sums are bounded by `1`;
* `abs_hoppingForm_le` — hence `|kernelForm (hoppingKernel m₀ n₀) c| ≤ coreNormSq c`, uniformly;
* **`hopping_farisLavine`** — the Yang–Mills certificate plus a hopping interaction still dominates
  the reference form with the **same ratio `c₁`**, the shift growing by exactly `1`.  So the
  certified separation of `softmodes.md` Phase 5 survives an off-diagonal coupling untouched in
  ratio, and this is the statement the Phase-4 open item asks for, on the same core.

## Bottom stability, on the core and on `L²`

* `diagonalForm_add_kernelForm_ge` / `sector_bottom_ge_interacting` — on the core the interacting
  form is bounded below by `θ − σ` over *any* sector of normalised states, so the elimination of
  `softmodes.md` Phase 1 cannot lower the bottom by more than the interaction's Hilbert–Schmidt
  constant; `hopping_sector_bottom` reads the constant `1` for the matrix unit;
* §5 lifts all of this to `L²`, where the diagonal closure lives: `closedKernelForm` is the
  absolutely convergent weighted double series, `abs_closedKernelForm_le` bounds it by
  `σ‖x‖²` for **every** `x ∈ ℓ²` (one Cauchy–Schwarz with exponents `2, 2` over the product index,
  replacing the two-index one of `kernelForm_sq_le`), `closedKernelForm_coreEmbed` shows it
  restricts to `kernelForm`, and `closed_diagonal_add_kernelForm_ge` /
  `closed_sector_bottom_ge_interacting` are the bottom bounds on the form domain
  (`closedForm f x ≠ ⊤`).  Boundedness is what closability needs: the interaction is a bounded
  form perturbation of the closed diagonal form, hence continuous in the `ℓ²` norm, and the sum is
  closed on the same domain.

## Honest boundary

What is *not* claimed: the Faris–Lavine **comparison** (the domination of the reference form by the
sum form) is proved on the core and, on `L²`, only through the bottom bound `θ − σ` — the
`L²`-level inequality `c₁ q_ref ≤ closedForm g + closedKernelForm` would need the finiteness of
both closed forms and is not stated.  The diagonal-side closure of `YangMillsFormClosure` is
therefore extended exactly as far as the Hilbert–Schmidt bound reaches: bounded interactions lift,
interactions that are merely form bounded with relative bound `a < 1` remain core statements.
-/

noncomputable section

namespace BookProof.YangMillsFormClosureND

open Finset
open scoped ENNReal
open BookProof.YangMillsFormClosure
open BookProof.ReferenceGap
open BookProof.YangMillsFormDomination

variable {d : ℕ}

/-! ## 1. The kernel form of an off-diagonal interaction -/

/-- The kernel form on the Gauss–polynomial core:
`∑_{m,n ∈ supp c} Re(K m n · c n · conj(c m))`.  For diagonal `K` this is the diagonal form of the
diagonal entries; for `K` supported off the diagonal it mixes distinct multi-indices, which is the
magnetic interaction that the diagonal theory of `YangMillsFormClosure` cannot represent. -/
def kernelForm (K : Idx d → Idx d → ℂ) (c : CoreCoeff d) : ℝ :=
  ∑ m ∈ c.support, ∑ n ∈ c.support, (K m n * c n * (starRingEnd ℂ) (c m)).re

/-- **Termwise bound for the kernel form.**  The real part costs at most the modulus, so the
kernel form is bounded by the absolute kernel form `∑ m ∑ n ‖K m n‖ ‖c n‖ ‖c m‖`. -/
theorem abs_kernelForm_le_sum (K : Idx d → Idx d → ℂ) (c : CoreCoeff d) :
    |kernelForm K c|
      ≤ ∑ m ∈ c.support, ∑ n ∈ c.support, ‖K m n‖ * ‖c n‖ * ‖c m‖ := by
  rw [kernelForm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun m _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun n _ => ?_
  refine (Complex.abs_re_le_norm _).trans_eq ?_
  simp

/-- **The two-index Cauchy–Schwarz inequality for the kernel form.**  The square of the absolute
kernel form is at most the Hilbert–Schmidt sum over the support times the square of the core norm:
each kernel row is paired with the coefficient row by Cauchy–Schwarz, and the resulting row values
are paired with the coefficients once more, so the cross terms of the double sum are handled in
blocks rather than termwise — which is exactly what a diagonal argument cannot do. -/
theorem kernelForm_sq_le (K : Idx d → Idx d → ℂ) (c : CoreCoeff d) :
    (∑ m ∈ c.support, ∑ n ∈ c.support, ‖K m n‖ * ‖c n‖ * ‖c m‖) ^ 2
      ≤ (∑ m ∈ c.support, ∑ n ∈ c.support, ‖K m n‖ ^ 2) * (coreNormSq c) ^ 2 := by
  classical
  have hNsum : ∑ n ∈ c.support, ‖c n‖ ^ 2 = coreNormSq c := rfl
  -- each row is the Cauchy–Schwarz pairing of the kernel row with the coefficients
  have hrow : ∑ m ∈ c.support, ∑ n ∈ c.support, ‖K m n‖ * ‖c n‖ * ‖c m‖
      = ∑ m ∈ c.support, (∑ n ∈ c.support, ‖K m n‖ * ‖c n‖) * ‖c m‖ := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
  -- Cauchy–Schwarz on each kernel row against the coefficient row
  have hrowbound : ∀ m, (∑ n ∈ c.support, ‖K m n‖ * ‖c n‖) ^ 2
      ≤ (∑ n ∈ c.support, ‖K m n‖ ^ 2) * coreNormSq c := by
    intro m
    have h := sum_mul_sq_le_sq_mul_sq c.support (fun n => ‖K m n‖) (fun n => ‖c n‖)
    rw [← hNsum]
    exact h
  -- Cauchy–Schwarz on the index set, then the row bounds
  have hCS := sum_mul_sq_le_sq_mul_sq c.support (fun m => ∑ n ∈ c.support, ‖K m n‖ * ‖c n‖)
    (fun m => ‖c m‖)
  have hsum : ∑ m ∈ c.support, (∑ n ∈ c.support, ‖K m n‖ * ‖c n‖) ^ 2
      ≤ (∑ m ∈ c.support, ∑ n ∈ c.support, ‖K m n‖ ^ 2) * coreNormSq c := by
    refine (Finset.sum_le_sum fun m _ => hrowbound m).trans ?_
    rw [Finset.sum_mul]
  rw [hrow]
  refine hCS.trans ?_
  refine (mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg fun m _ => sq_nonneg _)).trans ?_
  rw [← hNsum]
  exact le_of_eq (by ring)

/-- Nonnegative numbers are ordered as their squares are. -/
theorem le_of_sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb]
  exact Real.sqrt_le_sqrt h

/-- **The Hilbert–Schmidt form bound.**  If the finite-square Hilbert–Schmidt sums of the kernel are
bounded by `σ²` — the condition that makes `K` a Hilbert–Schmidt kernel on `ℓ²(Idx d)` — then the
kernel form is bounded by `σ` times the core norm on **every** core state.  This is the form bound
the off-diagonal interaction enters the Faris–Lavine comparison through. -/
theorem abs_kernelForm_le_of_hs {K : Idx d → Idx d → ℂ} {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) (c : CoreCoeff d) :
    |kernelForm K c| ≤ σ * coreNormSq c := by
  refine (abs_kernelForm_le_sum K c).trans ?_
  refine le_of_sq_le_sq_of_nonneg
    (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun n _ => by positivity)
    (mul_nonneg hσ0 (coreNormSq_nonneg c)) ?_
  refine (kernelForm_sq_le K c).trans ?_
  refine (mul_le_mul_of_nonneg_right (hσ c.support) (sq_nonneg _)).trans ?_
  exact le_of_eq (by ring)

/-! ## 2. Faris–Lavine: the sum form with an off-diagonal interaction -/

/-- **Faris–Lavine for the sum form.**  Let `q'` dominate the reference form with ratio `c₁ > 0` and
shift `c₂`, and let the off-diagonal interaction be form bounded with relative bound `a < 1`,

`|qK c| ≤ a · q' c + b · ‖c‖²`.

Then the **sum form** `q' + qK` dominates the reference form with ratio `(1 − a)·c₁` — still
strictly positive — and shift `(1 − a)·c₂ + b`.  The interaction can lower the form (`qK` is not
assumed nonnegative), and that is exactly what the factor `1 − a` charges for; the ratio never
reaches zero while `a < 1`, so the certified separation survives. -/
theorem farisLavine_domination {q q' qK : CoreCoeff d → ℝ} {c₁ c₂ a b : ℝ}
    (hc₁ : 0 < c₁) (ha1 : a < 1)
    (hdom : ∀ c, c₁ * q c - c₂ * coreNormSq c ≤ q' c)
    (hK : ∀ c, |qK c| ≤ a * q' c + b * coreNormSq c) :
    0 < (1 - a) * c₁ ∧
      ∀ c, (1 - a) * c₁ * q c - ((1 - a) * c₂ + b) * coreNormSq c ≤ q' c + qK c := by
  refine ⟨mul_pos (by linarith) hc₁, fun c => ?_⟩
  have h1a : 0 ≤ 1 - a := by linarith
  have hN : 0 ≤ coreNormSq c := coreNormSq_nonneg c
  have hlow : -(a * q' c + b * coreNormSq c) ≤ qK c := (abs_le.mp (hK c)).1
  have hmul : (1 - a) * (c₁ * q c - c₂ * coreNormSq c) ≤ (1 - a) * q' c :=
    mul_le_mul_of_nonneg_left (hdom c) h1a
  have hexp : (1 - a) * (c₁ * q c - c₂ * coreNormSq c)
      = (1 - a) * c₁ * q c - ((1 - a) * c₂) * coreNormSq c := by ring
  rw [hexp] at hmul
  nlinarith [hmul, hlow, hN]

/-- **The bounded case: the ratio is untouched.**  For a bounded interaction (`a = 0`, `b = σ`) the
sum form dominates with the *same* ratio `c₁`; the interaction costs only the shift term `σ`.  This
is the shape in which an off-diagonal coupling of finite Hilbert–Schmidt norm enters the Phase-4
comparison. -/
theorem farisLavine_of_bounded_interaction {q q' qK : CoreCoeff d → ℝ} {c₁ c₂ b : ℝ}
    (hdom : ∀ c, c₁ * q c - c₂ * coreNormSq c ≤ q' c)
    (hK : ∀ c, |qK c| ≤ b * coreNormSq c) :
    ∀ c, c₁ * q c - (c₂ + b) * coreNormSq c ≤ q' c + qK c := by
  intro c
  have hN : 0 ≤ coreNormSq c := coreNormSq_nonneg c
  have hlow : -(b * coreNormSq c) ≤ qK c := (abs_le.mp (hK c)).1
  linarith [hdom c]

/-! ## 3. A concrete off-diagonal interaction: a hopping matrix unit -/

/-- The matrix unit at `(m₀, n₀)`: the interaction that couples the multi-index `m₀` to `n₀`. -/
def hoppingKernel (m₀ n₀ : Idx d) : Idx d → Idx d → ℂ :=
  fun m n => if m = m₀ ∧ n = n₀ then 1 else 0

/-- The squared modulus of a hopping kernel entry is `1` at the pair and `0` elsewhere. -/
theorem norm_sq_hoppingKernel (m₀ n₀ m n : Idx d) :
    ‖hoppingKernel m₀ n₀ m n‖ ^ 2 = if m = m₀ ∧ n = n₀ then (1 : ℝ) else 0 := by
  by_cases h : m = m₀ ∧ n = n₀
  · rw [if_pos h, hoppingKernel, if_pos h]
    simp
  · rw [if_neg h, hoppingKernel, if_neg h]
    simp

/-- **The hopping kernel is Hilbert–Schmidt with norm `1`.**  Its double sums are at most the single
nonzero entry. -/
theorem hoppingKernel_sq_sum_le (m₀ n₀ : Idx d) (s : Finset (Idx d)) :
    ∑ m ∈ s, ∑ n ∈ s, ‖hoppingKernel m₀ n₀ m n‖ ^ 2 ≤ 1 := by
  classical
  simp only [norm_sq_hoppingKernel]
  have hinner : ∀ m ∈ s, ∑ n ∈ s, (if m = m₀ ∧ n = n₀ then (1 : ℝ) else 0)
      ≤ if m = m₀ then (1 : ℝ) else 0 := by
    intro m _
    by_cases hm : m = m₀
    · rw [if_pos hm]
      have hcongr : ∑ n ∈ s, (if m = m₀ ∧ n = n₀ then (1 : ℝ) else 0)
          = ∑ n ∈ s, (if n = n₀ then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hm]
        simp
      rw [hcongr, Finset.sum_ite_eq']
      split_ifs <;> norm_num
    · rw [if_neg hm]
      have hz : ∑ n ∈ s, (if m = m₀ ∧ n = n₀ then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun n _ => ?_
        have hfalse : ¬(m = m₀ ∧ n = n₀) := fun h => hm h.1
        rw [if_neg hfalse]
      rw [hz]
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [Finset.sum_ite_eq']
  split_ifs <;> norm_num

/-- **The hopping interaction is form bounded by the core norm**, uniformly in the state: an
off-diagonal coupling of two multi-indices is a bounded form perturbation with constant `1`. -/
theorem abs_hoppingForm_le (m₀ n₀ : Idx d) (c : CoreCoeff d) :
    |kernelForm (hoppingKernel m₀ n₀) c| ≤ coreNormSq c := by
  have h := abs_kernelForm_le_of_hs (d := d) (K := hoppingKernel m₀ n₀) (σ := 1)
    (by norm_num) (fun s => by simpa using hoppingKernel_sq_sum_le (d := d) m₀ n₀ s) c
  simpa using h

/-- **The Phase-4 comparison survives a hopping interaction with its ratio intact.**  The
Yang–Mills certificate `D` for the diagonal form `g`, together with the off-diagonal matrix unit at
`(m₀, n₀)`, gives domination of the reference form by the **sum form** with the unchanged ratio
`c₁` and shift `c₂ + 1`:

`c₁ · q_ref − (c₂ + 1)·‖·‖² ≤ q_g + q_hopping`

on the Gauss–polynomial core.  In particular the certified separation `c₁ Δ_ref` of
`softmodes.md` Phase 5 is *not* degraded by the off-diagonal coupling — only the level shift moves,
by the Hilbert–Schmidt constant of the interaction. -/
theorem hopping_farisLavine {ω : Fin d → ℝ} {g : Idx d → ℝ} (D : FormDomination ω (diagonalForm g))
    (m₀ n₀ : Idx d) :
    ∀ c : CoreCoeff d,
      D.c₁ * coreForm ω c - (D.c₂ + 1) * coreNormSq c
        ≤ diagonalForm g c + kernelForm (hoppingKernel m₀ n₀) c :=
  farisLavine_of_bounded_interaction D.dom
    (fun c => by simpa using abs_hoppingForm_le m₀ n₀ c)

/-- The hopping interaction genuinely mixes multi-indices: on a core state supported on the two
coupled indices it reads the *product* of the two coefficients, `Re(b₀ · conj a₀)`, whereas the
diagonal form of any symbol reads `∑ f n ‖c n‖²` — a sum of moduli.  At `a₀ = 1`, `b₀ = 1` and at
`a₀ = 1`, `b₀ = I` the two coefficients have the same moduli but the kernel form is `1` in the
first case and `0` in the second, so no diagonal form can represent it. -/
theorem hopping_couples (m₀ n₀ : Idx d) (hne : m₀ ≠ n₀) (a₀ b₀ : ℂ) :
    kernelForm (hoppingKernel m₀ n₀)
        (Finsupp.single m₀ a₀ + Finsupp.single n₀ b₀)
      = (b₀ * (starRingEnd ℂ) a₀).re := by
  classical
  set c : CoreCoeff d := Finsupp.single m₀ a₀ + Finsupp.single n₀ b₀ with hc
  have hsupp : c.support ⊆ {m₀, n₀} := by
    intro m hm
    by_contra hmem
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    rw [Finsupp.mem_support_iff] at hm
    refine hm ?_
    rw [hc, Finsupp.add_apply, Finsupp.single_eq_of_ne hmem.1,
      Finsupp.single_eq_of_ne hmem.2, add_zero]
  have hsm : c m₀ = a₀ := by
    rw [hc, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, add_zero]
  have hsn : c n₀ = b₀ := by
    rw [hc, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hne), Finsupp.single_eq_same,
      zero_add]
  have hinner : ∀ m : Idx d,
      (∑ n ∈ c.support, (hoppingKernel m₀ n₀ m n * c n * (starRingEnd ℂ) (c m)).re)
        = (hoppingKernel m₀ n₀ m m₀ * c m₀ * (starRingEnd ℂ) (c m)).re
          + (hoppingKernel m₀ n₀ m n₀ * c n₀ * (starRingEnd ℂ) (c m)).re := by
    intro m
    rw [Finset.sum_subset hsupp]
    · rw [Finset.sum_pair hne]
    · intro n _ hn
      rw [Finsupp.notMem_support_iff.mp hn]
      simp
  rw [kernelForm, Finset.sum_subset hsupp]
  · rw [Finset.sum_pair hne, hinner m₀, hinner n₀, hsm, hsn]
    simp [hoppingKernel, hne, Ne.symm hne]
  · intro m _ hm
    rw [Finsupp.notMem_support_iff.mp hm]
    simp

/-! ## 4. Bottom stability: restriction does not lower the interacting bottom

`softmodes.md` Phase 1, item 4 asks that the elimination of the longitudinal directions not lower
the bottom of the form — "the eliminated directions carry no spectral weight near the bottom".
For a diagonal form that is `YangMillsFormClosure.sector_bottom_ge_of_le_symbol`, and it is short
for the reason recorded there: the form is symbolwise, so restricting the retained states cannot
improve on a symbol bound.  An off-diagonal interaction mixes multi-indices, so the symbolwise
argument does not apply — but §1's Hilbert–Schmidt bound replaces it exactly.  An interaction that
is form bounded by `σ‖·‖²` can lower the core form by at most `σ‖·‖²`, so the bottom of
`diagonalForm f + kernelForm K` is at least `θ − σ` whenever `θ` bounds the diagonal symbol; and
because *that* bound is statewise again, the sector statement follows with no support hypothesis
and no restriction on which indices the kernel couples.  What the interaction costs the bottom is
exactly the Hilbert–Schmidt constant, which is the same constant the Faris–Lavine comparison of §2
charges to the shift. -/

/-- **An interaction that is Hilbert–Schmidt bounded can only lower the core form by its
constant.** -/
theorem kernelForm_ge_neg_of_hs {K : Idx d → Idx d → ℂ} {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) (c : CoreCoeff d) :
    -(σ * coreNormSq c) ≤ kernelForm K c := by
  have h1 : |kernelForm K c| ≤ σ * coreNormSq c := abs_kernelForm_le_of_hs hσ0 hσ c
  have h2 : -|kernelForm K c| ≤ kernelForm K c := neg_abs_le _
  linarith

/-- **Bottom stability on the core.**  If `θ` bounds the diagonal symbol and the interaction is
Hilbert–Schmidt bounded by `σ`, the interacting form is bounded below by `θ − σ` on the core. -/
theorem diagonalForm_add_kernelForm_ge {f : Idx d → ℝ} {K : Idx d → Idx d → ℂ} {θ σ : ℝ}
    (hθ : ∀ n, θ ≤ f n) (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) (c : CoreCoeff d) :
    (θ - σ) * coreNormSq c ≤ diagonalForm f c + kernelForm K c := by
  have h1 : θ * coreNormSq c ≤ diagonalForm f c := diagonalForm_ge_of_le_symbol hθ c
  have h2 : -(σ * coreNormSq c) ≤ kernelForm K c := kernelForm_ge_neg_of_hs hσ0 hσ c
  have hexp : (θ - σ) * coreNormSq c = θ * coreNormSq c - σ * coreNormSq c := by ring
  rw [hexp]
  linarith

/-- **Restriction to any sector does not lower the interacting bottom.**  This is
`sector_bottom_ge_of_le_symbol` for a form with an off-diagonal interaction: over any nonempty set
of *normalised* retained core states, the Rayleigh infimum of
diagonalForm f + kernelForm K` is at least `θ − σ`.  The set of retained states is arbitrary — no
condition on which multi-indices the interaction couples, and none on the sector — because the
estimate is statewise.  In particular the elimination of Phase 1 cannot remove the directions that
carry the bottom: what an off-diagonal interaction can do to the bottom is bounded by its
Hilbert–Schmidt constant, independently of the sector retained. -/
theorem sector_bottom_ge_interacting {f : Idx d → ℝ} {K : Idx d → Idx d → ℂ} {θ σ : ℝ}
    (hθ : ∀ n, θ ≤ f n) (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2)
    (S : Set (CoreCoeff d)) (hne : S.Nonempty) (hS : ∀ c ∈ S, coreNormSq c = 1) :
    θ - σ ≤ sInf ((fun c => diagonalForm f c + kernelForm K c) '' S) := by
  have hne' : ((fun c => diagonalForm f c + kernelForm K c) '' S).Nonempty :=
    ⟨_, ⟨hne.choose, hne.choose_spec, rfl⟩⟩
  refine le_csInf hne' ?_
  rintro _ ⟨c, hcS, rfl⟩
  have h := diagonalForm_add_kernelForm_ge hθ hσ0 hσ c
  rwa [hS c hcS, mul_one] at h

/-- **The hopping interaction's sector bottom.**  For the concrete off-diagonal coupling of §3 the
constant is `1`, so no sector of the core sees a bottom below `θ − 1` — the same `1` that
`hopping_farisLavine` charges to the shift. -/
theorem hopping_sector_bottom {f : Idx d → ℝ} {θ : ℝ} (hθ : ∀ n, θ ≤ f n) (m₀ n₀ : Idx d)
    (S : Set (CoreCoeff d)) (hne : S.Nonempty) (hS : ∀ c ∈ S, coreNormSq c = 1) :
    θ - 1 ≤ sInf ((fun c => diagonalForm f c + kernelForm (hoppingKernel m₀ n₀) c) '' S) :=
  sector_bottom_ge_interacting (K := hoppingKernel m₀ n₀) hθ (by norm_num)
    (fun s => by simpa using hoppingKernel_sq_sum_le (d := d) m₀ n₀ s) S hne hS

/-! ## 5. The `L²` lift: an off-diagonal interaction is a bounded form on all of `L²`

§1–§4 live on the Gauss–polynomial core, and `YangMillsFormClosure`'s boundary records why the
diagonal closure argument does not lift them: `closedForm f` is the supremum of its truncations,
whereas a non-diagonal kernel form is **not** monotone along truncations, so there is nothing to
take a supremum of.

A Hilbert–Schmidt kernel does not need truncations.  The weighted double series

`closedKernelForm K x = Re ∑_{m,n} K m n · x n · conj(x m)`

converges absolutely for **every** `x ∈ ℓ²`, and obeys the *same* bound as on the core,

`|closedKernelForm K x| ≤ σ · ‖x‖²`,

where the two-index Cauchy–Schwarz of `kernelForm_sq_le` is replaced by a single Cauchy–Schwarz in
`ℓ²(Idx d × Idx d)` between the kernel and the product of the two coefficient rows (Hölder with
`p = q = 2`).  What the interaction costs is therefore the Hilbert–Schmidt constant on the whole
space, not merely state by state on the core:

* `tsum_sq_kernel_le` — the core hypothesis `hσ` is the total Hilbert–Schmidt mass, not just the
  partial sums: `∑' p, ‖K p.1 p.2‖² ≤ σ²`;
* `tsum_sq_weight_le` — the coefficient weight has total mass `‖x‖⁴`;
* `abs_closedKernelForm_le` — the operator bound with the constant `σ`;
* `closedKernelForm_coreEmbed` — on the core it *is* `kernelForm`, so this is a genuine extension
  and not a different form;
* `closed_diagonal_add_kernelForm_ge` — on the form domain (`closedForm f x ≠ ⊤`) the interacting
  form is bounded below by `θ − σ` with no core hypothesis and no truncation;
* `closed_sector_bottom_ge_interacting` / `closed_hopping_sector_bottom` — the Phase-1 sector
  statement of §4 now holds on `L²`.

That is also what closability needs: `abs_closedKernelForm_le` says the interaction is a *bounded*
form perturbation of the closed diagonal form, so it is continuous in the `ℓ²` norm and the sum is
closed on the diagonal form's domain. -/

/-- **The kernel form on `L²`**: the absolutely convergent weighted double series, read as one
sum over the product of the index type.  Every term is the pairing of the kernel entry `K m n` with
the coefficient `x n` and the conjugate coefficient `x m`, exactly as on the core. -/
def closedKernelForm (K : Idx d → Idx d → ℂ) (x : L2 d) : ℝ :=
  (∑' p : Idx d × Idx d, K p.1 p.2 * x p.2 * (starRingEnd ℂ) (x p.1)).re

/-- **The Hilbert–Schmidt mass is total.**  A kernel whose square sums over every pair of finite
index sets are bounded by `σ²` has `∑' p, ‖K p.1 p.2‖² ≤ σ²`: a finite set of *pairs* is contained
in the product of its two coordinate sets. -/
theorem sq_kernel_finset_le {K : Idx d → Idx d → ℂ} {σ : ℝ}
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2)
    (u : Finset (Idx d × Idx d)) : ∑ p ∈ u, ‖K p.1 p.2‖ ^ 2 ≤ σ ^ 2 := by
  classical
  set A := u.image Prod.fst ∪ u.image Prod.snd with hA
  have hsub : u ⊆ A ×ˢ A := fun p hp =>
    Finset.mem_product.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  calc ∑ p ∈ u, ‖K p.1 p.2‖ ^ 2
      ≤ ∑ p ∈ A ×ˢ A, ‖K p.1 p.2‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ m ∈ A, ∑ n ∈ A, ‖K m n‖ ^ 2 := by rw [Finset.sum_product]
    _ ≤ σ ^ 2 := hσ A

/-- The squared kernel entries are summable with total mass at most `σ²`. -/
theorem summable_sq_kernel {K : Idx d → Idx d → ℂ} {σ : ℝ}
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) :
    Summable (fun p : Idx d × Idx d => ‖K p.1 p.2‖ ^ 2) :=
  summable_of_sum_le (fun _ => by positivity) fun u => sq_kernel_finset_le hσ u

/-- The total Hilbert–Schmidt mass is at most `σ²`. -/
theorem tsum_sq_kernel_le {K : Idx d → Idx d → ℂ} {σ : ℝ}
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) :
    (∑' p : Idx d × Idx d, ‖K p.1 p.2‖ ^ 2) ≤ σ ^ 2 :=
  Real.tsum_le_of_sum_le (fun _ => by positivity) fun u => sq_kernel_finset_le hσ u

/-- **The coefficient weight has total mass `‖x‖⁴`.**  The weight of a pair `(m, n)` is
`‖x n‖ ‖x m‖`, so its square sums to `(∑ ‖x‖²)² = ‖x‖⁴`; a finite set of pairs is again contained
in the product of its coordinates, so the two factors are the two partial sums bounded by `‖x‖²`. -/
theorem sq_weight_finset_le (x : L2 d) (u : Finset (Idx d × Idx d)) :
    ∑ p ∈ u, (‖x p.2‖ * ‖x p.1‖) ^ 2 ≤ (‖x‖ ^ 2) ^ 2 := by
  classical
  set A := u.image Prod.fst ∪ u.image Prod.snd with hA
  have hsub : u ⊆ A ×ˢ A := fun p hp =>
    Finset.mem_product.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  have hrow : ∑ p ∈ A ×ˢ A, (‖x p.2‖ * ‖x p.1‖) ^ 2
      = (∑ n ∈ A, ‖x n‖ ^ 2) * (∑ m ∈ A, ‖x m‖ ^ 2) := by
    rw [Finset.sum_product]
    have hinner : ∀ m : Idx d, ∑ n ∈ A, (‖x n‖ * ‖x m‖) ^ 2 = (∑ n ∈ A, ‖x n‖ ^ 2) * ‖x m‖ ^ 2 := by
      intro m
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [Finset.sum_congr rfl fun m _ => hinner m, Finset.mul_sum]
  have hHas : HasSum (fun n : Idx d => ‖x n‖ ^ 2) (‖x‖ ^ 2) := by
    have h := lp.hasSum_norm (E := fun _ : Idx d => ℂ) (p := (2 : ℝ≥0∞)) (by norm_num) x
    simpa using h
  have hA : ∑ n ∈ A, ‖x n‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (hHas.summable.sum_le_tsum A fun _ _ => by positivity).trans hHas.tsum_eq.le
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
  refine hrow.le.trans ?_
  calc (∑ n ∈ A, ‖x n‖ ^ 2) * (∑ m ∈ A, ‖x m‖ ^ 2) ≤ (‖x‖ ^ 2) * (‖x‖ ^ 2) :=
        mul_le_mul hA hA (by positivity) (by positivity)
    _ = (‖x‖ ^ 2) ^ 2 := by ring

/-- The squared coefficient weights are summable. -/
theorem summable_sq_weight (x : L2 d) :
    Summable (fun p : Idx d × Idx d => (‖x p.2‖ * ‖x p.1‖) ^ 2) :=
  summable_of_sum_le (fun _ => by positivity) fun u => sq_weight_finset_le x u

/-- The total coefficient weight is at most `‖x‖⁴`. -/
theorem tsum_sq_weight_le (x : L2 d) :
    (∑' p : Idx d × Idx d, (‖x p.2‖ * ‖x p.1‖) ^ 2) ≤ (‖x‖ ^ 2) ^ 2 :=
  Real.tsum_le_of_sum_le (fun _ => by positivity) fun u => sq_weight_finset_le x u

/-- **The Hilbert–Schmidt form bound on `L²`.**  For every state of `ℓ²` — not merely for core
states — the kernel form is bounded by `σ` times the squared norm, with the same `σ` as the core
estimate `abs_kernelForm_le_of_hs`.  The proof is Hölder with conjugate exponents `2, 2` in
`ℓ²(Idx d × Idx d)`: the kernel is paired with the product of the two coefficient rows, whose
`ℓ²` mass is `‖x‖⁴`.  This is `K` as a bounded operator on `ℓ²`, read as a quadratic form. -/
theorem abs_closedKernelForm_le {K : Idx d → Idx d → ℂ} {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) (x : L2 d) :
    |closedKernelForm K x| ≤ σ * ‖x‖ ^ 2 := by
  have hk : Summable (fun p : Idx d × Idx d => ‖K p.1 p.2‖ ^ 2) := summable_sq_kernel hσ
  have hw : Summable (fun p : Idx d × Idx d => (‖x p.2‖ * ‖x p.1‖) ^ 2) := summable_sq_weight x
  obtain ⟨hkw, hHolder⟩ :=
    Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (f := fun p : Idx d × Idx d => ‖K p.1 p.2‖)
      (g := fun p : Idx d × Idx d => ‖x p.2‖ * ‖x p.1‖) (p := (2 : ℝ)) (q := (2 : ℝ))
      (by rw [Real.holderConjugate_iff]; norm_num) (fun _ => norm_nonneg _) (fun _ => by positivity)
      (by simpa [Real.rpow_two] using hk) (by simpa [Real.rpow_two] using hw)
  have hk_tsum : (∑' p : Idx d × Idx d, ‖K p.1 p.2‖ ^ (2 : ℝ))
      = ∑' p : Idx d × Idx d, ‖K p.1 p.2‖ ^ 2 :=
    tsum_congr fun (p : Idx d × Idx d) => Real.rpow_two (‖K p.1 p.2‖)
  have hw_tsum : (∑' p : Idx d × Idx d, (‖x p.2‖ * ‖x p.1‖) ^ (2 : ℝ))
      = ∑' p : Idx d × Idx d, (‖x p.2‖ * ‖x p.1‖) ^ 2 :=
    tsum_congr fun (p : Idx d × Idx d) => Real.rpow_two (‖x p.2‖ * ‖x p.1‖)
  have h1 : ((∑' p : Idx d × Idx d, ‖K p.1 p.2‖ ^ (2 : ℝ))) ^ (1 / 2 : ℝ) ≤ σ := by
    rw [hk_tsum]
    refine (Real.rpow_le_rpow (by positivity) (tsum_sq_kernel_le hσ) (by norm_num)).trans ?_
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hσ0]
  have h2 : ((∑' p : Idx d × Idx d, (‖x p.2‖ * ‖x p.1‖) ^ (2 : ℝ))) ^ (1 / 2 : ℝ) ≤ ‖x‖ ^ 2 := by
    rw [hw_tsum]
    refine (Real.rpow_le_rpow (by positivity) (tsum_sq_weight_le x) (by norm_num)).trans ?_
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  have hbound : (∑' p : Idx d × Idx d, ‖K p.1 p.2‖ * (‖x p.2‖ * ‖x p.1‖)) ≤ σ * ‖x‖ ^ 2 :=
    hHolder.trans (mul_le_mul h1 h2 (by positivity) hσ0)
  have hz : ∀ p : Idx d × Idx d,
      ‖K p.1 p.2 * x p.2 * (starRingEnd ℂ) (x p.1)‖
        = ‖K p.1 p.2‖ * (‖x p.2‖ * ‖x p.1‖) := by
    intro p
    rw [norm_mul, norm_mul, starRingEnd_apply, norm_star]
    ring
  have hsum_norm :
      Summable (fun p : Idx d × Idx d => ‖K p.1 p.2 * x p.2 * (starRingEnd ℂ) (x p.1)‖) := by
    rw [funext hz]
    exact hkw
  have hnorm := norm_tsum_le_tsum_norm hsum_norm
  calc |closedKernelForm K x|
      ≤ ‖∑' p : Idx d × Idx d, K p.1 p.2 * x p.2 * (starRingEnd ℂ) (x p.1)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑' p : Idx d × Idx d, ‖K p.1 p.2 * x p.2 * (starRingEnd ℂ) (x p.1)‖ := hnorm
    _ = ∑' p : Idx d × Idx d, ‖K p.1 p.2‖ * (‖x p.2‖ * ‖x p.1‖) := by rw [funext hz]
    _ ≤ σ * ‖x‖ ^ 2 := hbound

/-- **The lift extends the core form.**  On a Gauss–polynomial state the absolutely convergent
series is the finite double sum of `kernelForm`, so `closedKernelForm` is the extension of the
form §1–§4 are stated for, not a different form. -/
theorem closedKernelForm_coreEmbed (K : Idx d → Idx d → ℂ) (c : CoreCoeff d) :
    closedKernelForm K (coreEmbed c) = kernelForm K c := by
  classical
  have hzero : ∀ p : Idx d × Idx d, p ∉ c.support ×ˢ c.support →
      K p.1 p.2 * coreEmbed c p.2 * (starRingEnd ℂ) (coreEmbed c p.1) = 0 := by
    intro p hp
    rw [Finset.mem_product, not_and_or] at hp
    rcases hp with h | h
    · have hx : coreEmbed c p.1 = 0 := by
        rw [coreEmbed_apply]
        exact Finsupp.notMem_support_iff.mp h
      rw [hx]
      simp
    · have hx : coreEmbed c p.2 = 0 := by
        rw [coreEmbed_apply]
        exact Finsupp.notMem_support_iff.mp h
      rw [hx]
      simp
  rw [closedKernelForm, tsum_eq_sum hzero, Finset.sum_product]
  simp [kernelForm, coreEmbed_apply]

/-- **Bottom stability on the form domain.**  With `θ` bounding the diagonal symbol and `σ` the
Hilbert–Schmidt constant of the interaction, the interacting form is bounded below by `θ − σ` on
the *whole* `L²` form domain, with no core hypothesis: `closedForm f x ≠ ⊤` is the form-domain
condition, and `closedKernelForm` needs none at all because the kernel is Hilbert–Schmidt. -/
theorem closed_diagonal_add_kernelForm_ge {f : Idx d → ℝ} {K : Idx d → Idx d → ℂ} {θ σ : ℝ}
    (hθ : ∀ n, θ ≤ f n) (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) (x : L2 d)
    (hfin : closedForm f x ≠ ⊤) :
    (θ - σ) * ‖x‖ ^ 2 ≤ (closedForm f x).toReal + closedKernelForm K x := by
  have hdiag : ENNReal.ofReal θ * closedNormSq x ≤ closedForm f x := closedForm_ge_of_le_symbol hθ x
  have hdiagR : θ * ‖x‖ ^ 2 ≤ (closedForm f x).toReal := by
    by_cases hθ0 : 0 ≤ θ
    · have h1 : ENNReal.ofReal (θ * ‖x‖ ^ 2) ≤ closedForm f x := by
        rw [ENNReal.ofReal_mul hθ0, ← closedNormSq_eq]
        exact hdiag
      have h2 := ENNReal.toReal_mono hfin h1
      rwa [ENNReal.toReal_ofReal (mul_nonneg hθ0 (by positivity))] at h2
    · have hneg : θ * ‖x‖ ^ 2 ≤ 0 := by
        have hpos : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
        nlinarith
      exact hneg.trans ENNReal.toReal_nonneg
  have hK : -(σ * ‖x‖ ^ 2) ≤ closedKernelForm K x := by
    have h := abs_closedKernelForm_le hσ0 hσ x
    have h' := neg_abs_le (closedKernelForm K x)
    linarith
  have hexp : (θ - σ) * ‖x‖ ^ 2 = θ * ‖x‖ ^ 2 - σ * ‖x‖ ^ 2 := by ring
  rw [hexp]
  linarith

/-- **Restriction to any sector does not lower the interacting bottom, on `L²`.**  This is
`sector_bottom_ge_interacting` on the whole Hilbert space: over any nonempty set of normalised
retained states *on which the diagonal form is finite*, the Rayleigh infimum of the interacting
form is at least `θ − σ`.  No truncation, no core condition, no hypothesis on the sector. -/
theorem closed_sector_bottom_ge_interacting {f : Idx d → ℝ} {K : Idx d → Idx d → ℂ} {θ σ : ℝ}
    (hθ : ∀ n, θ ≤ f n) (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2)
    (S : Set (L2 d)) (hne : S.Nonempty) (hS : ∀ x ∈ S, closedNormSq x = 1)
    (hfin : ∀ x ∈ S, closedForm f x ≠ ⊤) :
    θ - σ ≤ sInf ((fun x => (closedForm f x).toReal + closedKernelForm K x) '' S) := by
  have hne' : ((fun x => (closedForm f x).toReal + closedKernelForm K x) '' S).Nonempty :=
    ⟨_, ⟨hne.choose, hne.choose_spec, rfl⟩⟩
  refine le_csInf hne' ?_
  rintro _ ⟨x, hxS, rfl⟩
  have h := closed_diagonal_add_kernelForm_ge hθ hσ0 hσ x (hfin x hxS)
  have hnorm : ‖x‖ ^ 2 = 1 := by
    have h := hS x hxS
    rw [closedNormSq_eq] at h
    have h' := congrArg ENNReal.toReal h
    simpa [ENNReal.toReal_ofReal (by positivity)] using h'
  rwa [hnorm, mul_one] at h

/-- **The hopping interaction's bottom on `L²`.**  The constant is `1`, as on the core. -/
theorem closed_hopping_sector_bottom {f : Idx d → ℝ} {θ : ℝ} (hθ : ∀ n, θ ≤ f n) (m₀ n₀ : Idx d)
    (S : Set (L2 d)) (hne : S.Nonempty) (hS : ∀ x ∈ S, closedNormSq x = 1)
    (hfin : ∀ x ∈ S, closedForm f x ≠ ⊤) :
    θ - 1 ≤ sInf ((fun x => (closedForm f x).toReal + closedKernelForm (hoppingKernel m₀ n₀) x)
      '' S) :=
  closed_sector_bottom_ge_interacting (K := hoppingKernel m₀ n₀) hθ (by norm_num)
    (fun s => by simpa using hoppingKernel_sq_sum_le (d := d) m₀ n₀ s) S hne hS hfin

end BookProof.YangMillsFormClosureND
