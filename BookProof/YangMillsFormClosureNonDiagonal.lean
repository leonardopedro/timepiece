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

## Honest boundary

The comparison here is on the **Gauss–polynomial core**, which is where `FormDomination` lives.
It is not yet lifted to `L²` for the interacting form: `closedForm_eq_iSup_truncate` lifts the
*diagonal* part because `closedForm` is the supremum of its truncations, but a non-diagonal
`kernelForm` is not monotone along truncations, so the lift needs the interaction to be an
operator on `L²` (a Hilbert–Schmidt kernel does define a bounded operator there) together with the
form-domain hypothesis `closedForm μ x < ⊤` under which the truncation values converge in `ℝ`.
That lift is not proved here, and the diagonal-side closure of `YangMillsFormClosure` is not
extended by this file.
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

end BookProof.YangMillsFormClosureND
