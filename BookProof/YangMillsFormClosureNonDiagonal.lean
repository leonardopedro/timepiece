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
  (`closedForm f x ≠ ⊤`).  This is a *sufficient* route to closability, not the general requirement:
  a bounded form perturbation of a closed form is continuous in the `ℓ²` norm, so the sum is closed
  on the same domain.  General closability needs only relative form boundedness with relative bound
  `a < 1` — the `farisLavine_domination` branch — and boundedness is the `a = 0` case;
* §6 states the comparison itself on `L²` **with** the relative bound:
  `closed_farisLavine_domination` gives ratio `(1 − a)c₁ > 0` and shift `(1 − a)c₂ + b`, the
  finiteness of the closed forms being the explicit hypothesis, and `closed_dom_of_scaled_symbol`
  discharges that hypothesis from a symbolwise inequality instead of assuming it;
* §7 measures the cut-off dependence: the magnetic ladder kernel has Hilbert–Schmidt mass at most
  `d² C Λ^(d+1)` (`magCutoffKernel_hs_mass`), so its constant is at most `d √C Λ^{(d+1)/2}` — a
  power of the cut-off, not a uniform bound;
* §8 separates the two halves of the cut-off question: `ladder_relative_bound_uniform` shows the
  *ratio* is uniform — `a` is a free parameter, so `a(Λ) < 1` at every cut-off — while §7 shows the
  *constant* is not, so the continuum needs the constant and not the ratio;
* §9 instantiates the finiteness hypothesis with the concrete magnetic symbol of
  `YangMillsMagneticQuartic` (`magSymbol`, `magnetic_closed_dom_of_scaled`), and
  `closed_dom_of_scaled_symbol_auto` shows that for a positive ratio the hypothesis is a
  consequence of the symbol comparison rather than an assumption.

One caveat on what §7–§9 are about, since the repository does formalize the continuum: the
derivative is an outer-Fock operator (`dGamma`, `momOp`), and a product of outer fields at a
coincident point is never formed — `dft_samePointProduct` turns it into the momentum convolution
`n⁻¹ Σ_p F̂(p) Ĝ(k−p)` and `samePointProduct_form_eq_momentum` identifies the form with the
momentum-transfer matrix (`ChapterTempleContinuumGap` §4).  But the gauge-fixed form formalized here
is diagonal (`yangMillsForm_eq_diagonalForm`), so the ladder is a model of the coupling, not the
reduced sector's magnetic slot; §7's bound does not transfer to the eliminated theory as formalized.

## Honest boundary

What the comparison needed is now stated rather than deferred: `closed_farisLavine_domination` is
the `L²` form of `c₁ q_ref ≤ q' + qK` with `a < 1`, its only extra hypothesis being the finiteness
of the closed forms, and that hypothesis is itself derived from a symbolwise inequality.  What
remains outside the statements is a *uniform-in-cut-off* version: §7 shows the Hilbert–Schmidt
constant of the magnetic ladder grows like `Λ^{(d+1)/2}`, so the `a = 0` branch is genuinely
cut-off-local, and the continuum needs the `a < 1` branch together with a proof that `a` stays
bounded away from `1` uniformly — the relative form bound of the magnetic operator, which this
repository does not yet supply.

**What the Hilbert–Schmidt hypothesis costs.**  `∑' p, ‖K p.1 p.2‖² ≤ σ²` is a hypothesis *on the
model*, not a theorem about Yang–Mills.  It holds for a kernel at a fixed cut-off — finitely many
coupled modes, hence an honest finite matrix with a finite Hilbert–Schmidt mass — but it is not
uniform as the cut-off is removed: the number of coupled multi-indices and the size of the magnetic
matrix elements both grow with the mode index, so no single `σ` survives the continuum limit.  There
the magnetic term is only form bounded with relative bound `a < 1`, which is exactly the branch of
§6.  So the `a = 0` statement of §5 is a fixed-cut-off statement, whereas §6 is cut-off-free but
conditional on the relative bound; neither supplies the uniform bound itself.  The relative bound
itself *is* uniform: `ladder_relative_bound_uniform` takes `a` as a free parameter, so `a(Λ) < 1`
at every cut-off.  That uniformity is cheap — the ladder is bounded at each fixed cut-off — and it
is the additive constant, not the ratio, that carries the cut-off dependence.
A different sufficient route to closability is operator level: `HashimotoShiftInvert`'s
`closed_of_selfAdjointCriterion` closes the graph of a symmetric operator from the self-adjointness
criterion, and the Friedrichs representation then yields a closed form.  It is not instantiated
here, and the reason is not laziness of exposition but the domains:

* on the fixed-cut-off model the magnetic term is *bounded* (§7 gives its constant), so it is
already self-adjoint on all of `ℓ²` and clause 4 of the criterion holds before anything is proved —
an instantiation would be a tautology;
* on the Gauss-polynomial core the domain is the finite-support span, and a diagonal operator with
an unbounded symbol restricted to that domain is symmetric but *not* self-adjoint: its adjoint has
the maximal domain, so the criterion's clause 4 fails exactly where it would have content.  The
domain on which the criterion can succeed is the maximal (form) domain — and there `closedForm`
already gives the closed form directly, which is what §5 and §6 use.

What the criterion would add is the continuum magnetic operator *in the coefficient model used
here*.  The caveat is about this model, not about the repository: the continuum is formalized, in
the nested-Fock / momentum representation.  The space-time derivative is an outer-Fock operator
(`dGamma`, `lagOne_dGamma_esa` in `ChapterNsLagrangianOuterFockEsa`; the momentum-space `momOp` of
`YangMillsHermite`), and the product of outer fields at a coincident point — the one place a
product of distributions would be ambiguous — is never formed: `dft_samePointProduct` turns it into
the momentum convolution `n⁻¹ Σ_p F̂(p) Ĝ(k−p)`, `momentumCol_samePointProduct` identifies the
coefficient with that convolution, and `samePointProduct_form_eq_momentum` / the four-dimensional
`samePointProductT4_form_eq_momentum` identify the form with the momentum-transfer matrix
(`ChapterTempleContinuumGap` §4).  What the coefficient model has instead is a *diagonal* magnetic
slot: `yangMillsForm_eq_diagonalForm` writes the whole `q_W` as a `diagonalForm`, so the ladder of
§7 is a model of the coupling, not the image of the momentum-representation operator under a proved
identification.  Bridging the two is a statement about `dGamma` and the reduction — not about
closedness — and it is not proved here.
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

That is enough for closability: `abs_closedKernelForm_le` says the interaction is a *bounded* form
perturbation of the closed diagonal form, so it is continuous in the `ℓ²` norm and the sum is
closed on the diagonal form's domain — sufficient, not necessary; the `a < 1` case of
`farisLavine_domination` would do with less, and is the case the continuum needs (see the
module's honest boundary). -/

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

/-! ## 6. The relative bound on `L²`: the comparison itself, not only the bottom

§5 lifts the interaction as a *bounded* form, which is the `a = 0` branch of Faris–Lavine and gives
the bottom `θ − σ`.  What Phase 5 actually consumes is the comparison

`c₁ q_ref ≤ q' + qK`

with the interaction entering through a relative bound `a < 1`, because in the continuum the
magnetic term is not Hilbert–Schmidt bounded and only its relative form bound is finite.  This
section states that comparison on `L²`, with the **finiteness of the forms** as the explicit
hypothesis — `closedForm g x ≠ ⊤` is the form-domain condition, and it is the only place where the
finiteness of the reference form enters.

* `closed_dom_of_scaled_symbol` — **the hypothesis is not assumed, it is discharged**: a symbolwise
  inequality `c₁ f ≤ g + C` plus the form-domain hypothesis `closedForm g x ≠ ⊤` (and the
  finiteness of `closedForm f`) gives the real-valued domination
  `c₁ (closedForm f x).toReal − C‖x‖² ≤ (closedForm g x).toReal`.  This is where the `ℝ≥0∞`-valued
  form is converted to real numbers, and it is exactly why finiteness cannot be dropped: the
  `toReal` of `⊤` is `0`.
* **`closed_farisLavine_domination`** — the sum form dominates with ratio `(1 − a) c₁ > 0` and shift
  `(1 − a) c₂ + b`, so the certified separation degrades by `1 − a` and is not destroyed.
* `closed_farisLavine_of_bounded_interaction` / `closed_farisLavine_of_hs` — the `a = 0` case, with
  the shift from a Hilbert–Schmidt constant `σ`, which is `§5`'s branch written as a comparison.
-/

/-- **From a symbolwise comparison to a domination on the form domain.**  If `c₁ f ≤ g + C` on the
symbols, then on states where the closed form of `g` is finite (and the closed form of `f` is), the
real-valued inequality `c₁ (closedForm f x).toReal − C‖x‖² ≤ (closedForm g x).toReal` holds.  The
finiteness of `closedForm f x` is needed only to take `toReal` of the product; the finiteness of
`closedForm g x` is the form-domain condition of the sum. -/
theorem closed_dom_of_scaled_symbol {f g : Idx d → ℝ} {c₁ C : ℝ} (hc₁ : 0 ≤ c₁)
    (hg : ∀ n, 0 ≤ g n) (hC : 0 ≤ C) (h : ∀ n, c₁ * f n ≤ g n + C)
    (hf : ∀ x : L2 d, closedForm g x ≠ ⊤ → closedForm f x ≠ ⊤) (x : L2 d)
    (hx : closedForm g x ≠ ⊤) :
    c₁ * (closedForm f x).toReal - C * ‖x‖ ^ 2 ≤ (closedForm g x).toReal := by
  have h1 : ENNReal.ofReal c₁ * closedForm f x
      ≤ closedForm g x + ENNReal.ofReal C * closedNormSq x := closedForm_scaled_le hc₁ hg hC h x
  have hsl : ENNReal.ofReal C * closedNormSq x ≠ ⊤ := by
    rw [closedNormSq_eq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hlhs : ENNReal.ofReal c₁ * closedForm f x ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf x hx)
  have hrhs : closedForm g x + ENNReal.ofReal C * closedNormSq x ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hx, hsl⟩
  have h2 : (ENNReal.ofReal c₁ * closedForm f x).toReal
      ≤ (closedForm g x + ENNReal.ofReal C * closedNormSq x).toReal :=
    (ENNReal.toReal_le_toReal hlhs hrhs).2 h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁, ENNReal.toReal_add hx hsl,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, closedNormSq_eq,
    ENNReal.toReal_ofReal (by positivity)] at h2
  linarith

/-- **The finiteness hypothesis is not a hypothesis when the ratio is positive.**  If `c₁ > 0` and
the symbols satisfy `c₁ f ≤ g + C`, then `closedForm f x` is automatically finite wherever
`closedForm g x` is: `ofReal c₁ * ⊤ = ⊤` would violate the comparison.  So for every symbolwise
comparison with a positive ratio the form-domain condition of the next theorem comes for free, and
nothing has to be assumed about the closed forms themselves. -/
theorem closed_dom_of_scaled_symbol_auto {f g : Idx d → ℝ} {c₁ C : ℝ} (hc₁ : 0 < c₁)
    (hg : ∀ n, 0 ≤ g n) (hC : 0 ≤ C) (h : ∀ n, c₁ * f n ≤ g n + C) (x : L2 d)
    (hx : closedForm g x ≠ ⊤) :
    c₁ * (closedForm f x).toReal - C * ‖x‖ ^ 2 ≤ (closedForm g x).toReal := by
  have hle := closedForm_scaled_le hc₁.le hg hC h x
  have hsl : ENNReal.ofReal C * closedNormSq x ≠ ⊤ := by
    rw [closedNormSq_eq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hrhs : closedForm g x + ENNReal.ofReal C * closedNormSq x ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hx, hsl⟩
  refine closed_dom_of_scaled_symbol hc₁.le hg hC h (fun y hy => ?_) x hx
  intro htop
  have hle' := closedForm_scaled_le hc₁.le hg hC h y
  have hsl' : ENNReal.ofReal C * closedNormSq y ≠ ⊤ := by
    rw [closedNormSq_eq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hrhs' : closedForm g y + ENNReal.ofReal C * closedNormSq y ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hy, hsl'⟩
  have hne : ENNReal.ofReal c₁ ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc₁)
  have htopmul : ENNReal.ofReal c₁ * closedForm f y = ⊤ := by
    rw [htop, ENNReal.mul_top hne]
  rw [htopmul] at hle'
  exact hrhs' (top_le_iff.mp hle')

/-- **Faris–Lavine on the form domain.**  This is `farisLavine_domination` for the closed forms: if
the closed form of `μ` is dominated by that of `g` with ratio `c₁` and shift `c₂` on the form
domain,
and the off-diagonal interaction is form bounded there by `a · closedForm g + b‖·‖²` with `a < 1`,
then the interacting sum form dominates with ratio `(1 − a) c₁ > 0` and shift `(1 − a) c₂ + b`.  The
form-domain hypothesis `closedForm g x ≠ ⊤` appears exactly where the real-valued inequality is
stated, and nowhere else. -/
theorem closed_farisLavine_domination {μ g : Idx d → ℝ} {K : Idx d → Idx d → ℂ}
    {c₁ c₂ a b : ℝ} (hc₁ : 0 < c₁) (ha1 : a < 1)
    (hdom : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2 ≤ (closedForm g x).toReal)
    (hK : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      |closedKernelForm K x| ≤ a * (closedForm g x).toReal + b * ‖x‖ ^ 2) :
    0 < (1 - a) * c₁ ∧
      ∀ x : L2 d, closedForm g x ≠ ⊤ →
        (1 - a) * c₁ * (closedForm μ x).toReal - ((1 - a) * c₂ + b) * ‖x‖ ^ 2
          ≤ (closedForm g x).toReal + closedKernelForm K x := by
  refine ⟨mul_pos (by linarith) hc₁, fun x hfin => ?_⟩
  have h1a : 0 ≤ 1 - a := by linarith
  have hN : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
  have hlow : -(a * (closedForm g x).toReal + b * ‖x‖ ^ 2) ≤ closedKernelForm K x :=
    (abs_le.mp (hK x hfin)).1
  have hmul := mul_le_mul_of_nonneg_left (hdom x hfin) h1a
  have hexp : (1 - a) * (c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2)
      = (1 - a) * c₁ * (closedForm μ x).toReal - ((1 - a) * c₂) * ‖x‖ ^ 2 := by ring
  rw [hexp] at hmul
  nlinarith [hmul, hlow, hN]

/-- **The bounded interaction, as a comparison on `L²`.**  For `a = 0` the ratio is untouched and
the interaction costs only the shift `b`. -/
theorem closed_farisLavine_of_bounded_interaction {μ g : Idx d → ℝ} {K : Idx d → Idx d → ℂ}
    {c₁ c₂ b : ℝ}
    (hdom : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2 ≤ (closedForm g x).toReal)
    (hK : ∀ x : L2 d, |closedKernelForm K x| ≤ b * ‖x‖ ^ 2) :
    ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - (c₂ + b) * ‖x‖ ^ 2
        ≤ (closedForm g x).toReal + closedKernelForm K x := by
  intro x hfin
  have hN : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
  have hlow : -(b * ‖x‖ ^ 2) ≤ closedKernelForm K x := (abs_le.mp (hK x)).1
  linarith [hdom x hfin]

/-- **A Hilbert–Schmidt interaction in the comparison.**  The relative bound is discharged from the
Hilbert–Schmidt constant `σ` of `§5`, so the shift grows by exactly `σ` and the ratio stays `c₁`. -/
theorem closed_farisLavine_of_hs {μ g : Idx d → ℝ} {K : Idx d → Idx d → ℂ} {c₁ c₂ σ : ℝ}
    (hdom : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2 ≤ (closedForm g x).toReal)
    (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) :
    ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - (c₂ + σ) * ‖x‖ ^ 2
        ≤ (closedForm g x).toReal + closedKernelForm K x :=
  closed_farisLavine_of_bounded_interaction hdom (fun x => abs_closedKernelForm_le hσ0 hσ x)

/-! ## 7. How fast the Hilbert–Schmidt constant grows at cut-off

§5 and §6 are statements at a fixed cut-off, and the honest boundary records that no single `σ`
survives the removal of the cut-off.  This section makes that quantitative on a model of the
magnetic coupling: a ladder term, raising one occupation number by one, with the matrix element
`Aᵢ·√(nᵢ + 1)` that a Weyl-gauge magnetic potential produces.

At cut-off `Λ` the modes are `Fin d → Fin Λ` (occupation numbers below `Λ`), and the kernel is

`magCutoffKernel A m n = ∑ i, [m = n + eᵢ] · Aᵢ √(nᵢ + 1)`   (the raise only if `nᵢ + 1 < Λ`).

Two facts give the growth, and nothing else is used:

* `norm_sum_sq_le_card_mul` — `‖∑ᵢ xᵢ‖² ≤ d · ∑ᵢ ‖xᵢ‖²`, so a row costs a factor `d`;
* `sum_norm_sq_ite` — a single matrix element in its row has square norm `‖c‖²`, so a row of the
  ladder is exactly the sum over the `d` directions.

Hence the row of the kernel is at most `d · d · CΛ` (`C` bounding `Aᵢ²`, `Λ` bounding `nᵢ + 1`), and
`hs_mass_le_of_entry_row` multiplies by the number of modes `Λ^d`:

**`magCutoffKernel_hs_mass` — `∑ m ∑ n ‖K m n‖² ≤ d² C Λ^(d+1)`.**  So the Hilbert–Schmidt
constant of the magnetic term is at most `d √C Λ^{(d+1)/2}`: a power of the cut-off, with the
exponent `(d+1)/2`, which is exactly why it is *not* uniform in `Λ` and why the continuum statement
has to go through the relative-bound branch of §6 rather than the bounded branch of §5.

Two caveats about what this bound applies to.  The ladder is the momentum-representation shape of
the coupling: a coincident-point product of outer fields is the convolution
`momentumCol (F·G) k i = n⁻² Σ_{p+q=k−i} F̂(p) Ĝ(q)`, and raising one occupation number by one is
what that convolution does to a one-particle matrix.  But the *gauge-fixed / BRST-reduced* form of
this repository is diagonal — `yangMillsForm_eq_diagonalForm` — and `gaugeReduce` acts on linear
(torsion) forms, so the reduced theory's magnetic slot carries no off-diagonal ladder: the bound
below is a bound on the coupling, not on the eliminated form as formalized.  Transferring it would
need the off-diagonal part of the reduced second-quantized Hamiltonian to be identified with
`magCutoffKernel`, which is not done here. -/

/-- **A row bound from an entry bound, on a finite index set.**  Summing a matrix by rows costs one
row bound per column, i.e. `card ι` times `r`. -/
theorem hs_mass_le_of_entry_row {ι : Type*} [Fintype ι] {K : ι → ι → ℂ} {r : ℝ}
    (hrow : ∀ n, ∑ m, ‖K m n‖ ^ 2 ≤ r) :
    ∑ m, ∑ n, ‖K m n‖ ^ 2 ≤ r * (Fintype.card ι : ℝ) := by
  rw [Finset.sum_comm]
  have hsum : ∑ n : ι, ∑ m, ‖K m n‖ ^ 2 ≤ ∑ n : ι, r :=
    Finset.sum_le_sum fun n _ => hrow n
  have hconst : ∑ n : ι, r = (Fintype.card ι : ℝ) * r := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith

/-- **The norm of a finite sum is at most `√d` times the `ℓ²` norm of its terms.**  Cauchy–Schwarz
for a sum of `d` vectors, in the one form used below. -/
theorem norm_sum_sq_le_card_mul {ι' : Type*} [Fintype ι'] (x : ι' → ℂ) :
    ‖∑ i, x i‖ ^ 2 ≤ (Fintype.card ι' : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
  have h1 : ‖∑ i, x i‖ ≤ ∑ i, ‖x i‖ := norm_sum_le (s := Finset.univ) (f := x)
  have h2 : (∑ i, ‖x i‖) ^ 2 ≤ (Fintype.card ι' : ℝ) * ∑ i, ‖x i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖x i‖)
  have h3 : ‖∑ i, x i‖ ^ 2 ≤ (∑ i, ‖x i‖) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self (norm_nonneg _) h1
  exact h3.trans h2

/-- **One matrix element fills its whole row.**  The sum over `m` of `‖[m = r]·c‖²` is `‖c‖²`: only
the entry at `r` survives. -/
theorem sum_norm_sq_ite {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (r : ι') (c : ℂ) :
    ∑ m, ‖(if m = r then c else 0 : ℂ)‖ ^ 2 = ‖c‖ ^ 2 := by
  have h := Finset.sum_eq_single (s := Finset.univ)
    (f := fun m : ι' => ‖(if m = r then c else 0 : ℂ)‖ ^ 2) r
    (fun m _ hm => by simp [hm])
    (fun h => absurd (Finset.mem_univ r) h)
  simpa using h

/-- One direction's contribution to the ladder: the entry at `n + eᵢ`, with the Weyl-gauge matrix
element `Aᵢ·√(nᵢ + 1)`, and zero when the raise would leave the cut-off. -/
def magShiftTerm {Λ : ℕ} (A : Fin d → ℝ) (n : Fin d → Fin Λ) (i : Fin d)
    (m : Fin d → Fin Λ) : ℂ :=
  if h : (n i).val + 1 < Λ then
    (if m = Function.update n i ⟨(n i).val + 1, h⟩ then
      ((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ) else 0)
  else 0

/-- **The magnetic ladder kernel at cut-off `Λ`.**  Mode `n` couples to the modes obtained by
raising `nᵢ` by one, with the Weyl-gauge matrix element `Aᵢ·√(nᵢ + 1)`; the raise is dropped when
it would leave the cut-off. -/
def magCutoffKernel {Λ : ℕ} (A : Fin d → ℝ) (m n : Fin d → Fin Λ) : ℂ :=
  ∑ i, magShiftTerm A n i m

/-- The matrix element of the ladder, as a real number bound: `‖Aᵢ√(nᵢ+1)‖² = Aᵢ²(nᵢ+1)`. -/
theorem norm_sq_coeff (A : Fin d → ℝ) {Λ : ℕ} (n : Fin d → Fin Λ) (i : Fin d) :
    ‖((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)‖ ^ 2
      = A i ^ 2 * ((n i).val + 1 : ℝ) := by
  have hsq : ‖((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)‖ ^ 2
      = (A i * Real.sqrt ((n i).val + 1) : ℝ) ^ 2 := by
    rw [Complex.norm_real]
    exact sq_abs _
  rw [hsq, mul_pow, Real.sq_sqrt (by positivity)]

/-- **The row of the ladder kernel.**  A row is the sum over the `d` directions of one matrix
element each, so `∑ m ‖K m n‖² ≤ d · ∑ i ‖Aᵢ√(nᵢ+1)‖²`. -/
theorem row_norm_sq_magCutoffKernel {Λ : ℕ} (A : Fin d → ℝ) (n : Fin d → Fin Λ) :
    ∑ m : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2
      ≤ (d : ℝ) * ∑ i : Fin d, A i ^ 2 * ((n i).val + 1 : ℝ) := by
  classical
  have hpt : ∀ m : Fin d → Fin Λ,
      ‖magCutoffKernel A m n‖ ^ 2
        ≤ (d : ℝ) * ∑ i : Fin d, ‖magShiftTerm A n i m‖ ^ 2 :=
    fun m => by
      have hcd : (Fintype.card (Fin d) : ℝ) = (d : ℝ) := by simp
      simpa [hcd, magCutoffKernel] using
        norm_sum_sq_le_card_mul (fun i : Fin d => magShiftTerm A n i m)
  calc ∑ m : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2
      ≤ ∑ m : Fin d → Fin Λ, (d : ℝ) * ∑ i : Fin d, ‖magShiftTerm A n i m‖ ^ 2 :=
        Finset.sum_le_sum fun m _ => hpt m
    _ = (d : ℝ) * ∑ i : Fin d, ∑ m : Fin d → Fin Λ, ‖magShiftTerm A n i m‖ ^ 2 := by
        conv_lhs => rw [← Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ (d : ℝ) * ∑ i : Fin d, A i ^ 2 * ((n i).val + 1 : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
        by_cases h : (n i).val + 1 < Λ
        · have hstep : ∑ m : Fin d → Fin Λ, ‖magShiftTerm A n i m‖ ^ 2
              = A i ^ 2 * ((n i).val + 1 : ℝ) := by
            simp only [magShiftTerm, dif_pos h]
            rw [sum_norm_sq_ite (Function.update n i ⟨(n i).val + 1, h⟩)
              ((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)]
            exact norm_sq_coeff A n i
          exact le_of_eq hstep
        · have hzero : ∀ m : Fin d → Fin Λ, magShiftTerm A n i m = 0 := by
            intro m
            simp only [magShiftTerm, dif_neg h]
          simp only [hzero, norm_zero]
          have hA : (0 : ℝ) ≤ A i ^ 2 := sq_nonneg _
          have hn : (0 : ℝ) ≤ ((n i).val + 1 : ℝ) := by positivity
          simpa using mul_nonneg hA hn

/-- **The Hilbert–Schmidt mass of the magnetic ladder at cut-off `Λ`.**  With `Aᵢ² ≤ C`, the mass is
at most `d² C Λ^(d+1)`, hence the Hilbert–Schmidt constant is at most `d √C Λ^{(d+1)/2}`: a power
of the cut-off with exponent `(d+1)/2`, and in particular not uniform in `Λ`. -/
theorem magCutoffKernel_hs_mass {Λ : ℕ} {A : Fin d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i, A i ^ 2 ≤ C) :
    ∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2
      ≤ (d : ℝ) ^ 2 * C * (Λ : ℝ) ^ (d + 1) := by
  classical
  have hrow : ∀ n : Fin d → Fin Λ,
      ∑ m : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2 ≤ (d : ℝ) ^ 2 * C * (Λ : ℝ) := by
    intro n
    refine (row_norm_sq_magCutoffKernel A n).trans ?_
    have hterm : ∀ i : Fin d, A i ^ 2 * ((n i).val + 1 : ℝ) ≤ C * (Λ : ℝ) := by
      intro i
      have h1 : ((n i).val + 1 : ℝ) ≤ (Λ : ℝ) := by
        have := (n i).isLt
        have : (n i).val + 1 ≤ Λ := by omega
        exact_mod_cast this
      have h0 : (0 : ℝ) ≤ ((n i).val + 1 : ℝ) := by positivity
      calc A i ^ 2 * ((n i).val + 1 : ℝ) ≤ C * ((n i).val + 1 : ℝ) :=
            mul_le_mul_of_nonneg_right (hA i) h0
        _ ≤ C * (Λ : ℝ) := mul_le_mul_of_nonneg_left h1 hC
    calc (d : ℝ) * ∑ i : Fin d, A i ^ 2 * ((n i).val + 1 : ℝ)
        ≤ (d : ℝ) * ∑ _i : Fin d, C * (Λ : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by positivity)
      _ = (d : ℝ) ^ 2 * C * (Λ : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hmass := hs_mass_le_of_entry_row (K := magCutoffKernel A) hrow
  have hcard : (Fintype.card (Fin d → Fin Λ) : ℝ) = (Λ : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
  rw [hcard] at hmass
  calc ∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2
      ≤ (d : ℝ) ^ 2 * C * (Λ : ℝ) * (Λ : ℝ) ^ d := hmass
    _ = (d : ℝ) ^ 2 * C * (Λ : ℝ) ^ (d + 1) := by
        rw [pow_succ']
        ring

/-! ### The constant cannot stay bounded, and why §7 does not contradict §10

§7 bounds the mass by `d² C Λ^{d+1}`.  This is not slack in the row estimate: the ladder's matrix
elements are `Aᵢ √(nᵢ+1)`, so the entry at the raise of a mode grows with the occupation, and there
are `Λ^d` modes to sum over.  `norm_sq_magCutoffKernel_raise` records that entry exactly, and
`magCutoffKernel_hs_mass_unbounded` draws the consequence: **no** real `σ` bounds
`∑_{m,n} ‖K m n‖²` at every cut-off.  The rays below give `Aᵢ² · N(N+1)/2` at `Λ = N + 2`, so the
mass grows at least quadratically in the cut-off along that family.

That is not in tension with the uniform ratio of §8 and §10, and the reason is the one §10 names:
`Λ^{d+1}` is the price of reading the ladder as a *bounded* form perturbation of the identity
(`a = 0`, shift `σ`), where every raise must be paid for in `‖x‖²`.  As a *relative* form bound the
ladder pays in `Q(x) = Σₙ (Σᵢ (nᵢ+1)) ‖x n‖²` instead, where the same `nᵢ+1` sits on the correct
side, and there the ratio `1/2` and the constant `(Σᵢ Aᵢ²)/2` carry no `Λ`.  The cut-off dependence
is therefore a property of the *norm* of the ladder, not of its form, and the continuum needs the
relative statement — which is why §10 exists.
-/

/-- The ray mode with `n i₀ = k + 1` and every other coordinate `0`, in the box of side `N + 2`.
The raise at `i₀` stays inside the cut-off, and distinct `k` give distinct modes. -/
def rayMode (N : ℕ) (i₀ : Fin d) (k : Fin N) : Fin d → Fin (N + 2) :=
  fun j => if j = i₀ then ⟨k.val + 1, by omega⟩ else ⟨0, by omega⟩

theorem rayMode_self_val (N : ℕ) (i₀ : Fin d) (k : Fin N) :
    (rayMode N i₀ k i₀).val = k.val + 1 := by
  simp [rayMode]

theorem rayMode_ne_val (N : ℕ) (i₀ : Fin d) (k : Fin N) {j : Fin d} (hj : j ≠ i₀) :
    (rayMode N i₀ k j).val = 0 := by
  simp [rayMode, hj]

theorem rayMode_injective (N : ℕ) (i₀ : Fin d) :
    Function.Injective fun k : Fin N => rayMode N i₀ k := by
  intro k l hkl
  have hv := congrFun hkl i₀
  have hval : k.val + 1 = l.val + 1 := by
    have h2 := congrArg Fin.val hv
    rwa [rayMode_self_val, rayMode_self_val] at h2
  exact Fin.ext (by omega)

/-- **A single matrix element of the ladder.**  At `m = n + eᵢ` only the `i`-th raise contributes —
the images of the raises in different directions are distinct modes — so the entry is exactly
`Aᵢ √(nᵢ+1)` and its square is `Aᵢ² (nᵢ+1)`.  This is the growth mechanism: the entries increase
with the occupation, which is what `magCutoffKernel_hs_mass` has to pay for. -/
theorem norm_sq_magCutoffKernel_raise {Λ : ℕ} (A : Fin d → ℝ) (n : Fin d → Fin Λ) (i : Fin d)
    (h : (n i).val + 1 < Λ) :
    ‖magCutoffKernel A (Function.update n i ⟨(n i).val + 1, h⟩) n‖ ^ 2
      = A i ^ 2 * ((n i).val + 1 : ℝ) := by
  classical
  set m := Function.update n i ⟨(n i).val + 1, h⟩ with hm
  have hself : magShiftTerm A n i m = ((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ) := by
    rw [hm]
    simp [magShiftTerm, dif_pos h]
  have hother : ∀ j : Fin d, j ≠ i → magShiftTerm A n j m = 0 := by
    intro j hj
    by_cases hcj : (n j).val + 1 < Λ
    · simp only [magShiftTerm, dif_pos hcj]
      refine if_neg ?_
      intro hEq
      have hv0 : (Function.update n i ⟨(n i).val + 1, h⟩) j
          = (Function.update n j ⟨(n j).val + 1, hcj⟩) j := by
        rw [← hm, hEq]
      have hL : ((Function.update n i ⟨(n i).val + 1, h⟩) j).val = (n j).val := by
        rw [Function.update_apply, if_neg hj]
      have hR : ((Function.update n j ⟨(n j).val + 1, hcj⟩) j).val = (n j).val + 1 := by
        rw [Function.update_apply, if_pos rfl]
      have hv := congrArg Fin.val hv0
      rw [hL, hR] at hv
      exact (Nat.succ_ne_self (n j).val) hv.symm
    · simp only [magShiftTerm, dif_neg hcj]
  rw [magCutoffKernel, Finset.sum_eq_single i (fun j _ hj => hother j hj)
    (fun hc => absurd (Finset.mem_univ i) hc), hself, norm_sq_coeff A n i]

/-- A single entry is at most the whole mass: read the double sum once along `m` and once along
`n`, each time by `single_le_sum`. -/
theorem magCutoffKernel_entry_le_mass {Λ : ℕ} (A : Fin d → ℝ) (m n : Fin d → Fin Λ) :
    ‖magCutoffKernel A m n‖ ^ 2
      ≤ ∑ m' : Fin d → Fin Λ, ∑ n' : Fin d → Fin Λ, ‖magCutoffKernel A m' n'‖ ^ 2 := by
  have h1 : ‖magCutoffKernel A m n‖ ^ 2
      ≤ ∑ m' : Fin d → Fin Λ, ‖magCutoffKernel A m' n‖ ^ 2 := by
    have hsplit : ∑ m' : Fin d → Fin Λ, ‖magCutoffKernel A m' n‖ ^ 2
        = ‖magCutoffKernel A m n‖ ^ 2
          + ∑ m' ∈ (Finset.univ : Finset (Fin d → Fin Λ)).erase m,
              ‖magCutoffKernel A m' n‖ ^ 2 := by
      rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin d → Fin Λ))) (a := m)
        (f := fun m' => ‖magCutoffKernel A m' n‖ ^ 2) (Finset.mem_univ m)]
      ring
    rw [hsplit]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  have h2 : ∑ m' : Fin d → Fin Λ, ‖magCutoffKernel A m' n‖ ^ 2
      ≤ ∑ n' : Fin d → Fin Λ, ∑ m' : Fin d → Fin Λ, ‖magCutoffKernel A m' n'‖ ^ 2 := by
    have hsplit : ∑ n' : Fin d → Fin Λ, ∑ m' : Fin d → Fin Λ, ‖magCutoffKernel A m' n'‖ ^ 2
        = (∑ m' : Fin d → Fin Λ, ‖magCutoffKernel A m' n‖ ^ 2)
          + ∑ n' ∈ (Finset.univ : Finset (Fin d → Fin Λ)).erase n,
              ∑ m' : Fin d → Fin Λ, ‖magCutoffKernel A m' n'‖ ^ 2 := by
      rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin d → Fin Λ))) (a := n)
        (f := fun n' => ∑ m' : Fin d → Fin Λ, ‖magCutoffKernel A m' n'‖ ^ 2)
        (Finset.mem_univ n)]
      ring
    rw [hsplit]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => by positivity)
  exact h1.trans (h2.trans (le_of_eq Finset.sum_comm))

/-- The Gauss sum needed for the ray family: `∑_{k<N} (k+1) = N(N+1)/2`. -/
theorem sum_fin_val_add_one (N : ℕ) :
    ∑ k : Fin N, ((k.val : ℝ) + 1) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_succ]
      have hstep : ∑ i : Fin m, (((Fin.succ i).val : ℝ) + 1)
          = (∑ i : Fin m, ((i.val : ℝ) + 1)) + (m : ℝ) := by
        have h1 : ∑ i : Fin m, (((Fin.succ i).val : ℝ) + 1)
            = ∑ i : Fin m, (((i.val : ℝ) + 1) + 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Fin.val_succ]
          push_cast
          ring
        rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [hstep, ih]
      simp only [Fin.val_zero, Nat.cast_zero, zero_add]
      push_cast
      ring

/-- **The ray lower bound.**  Restricting the mass to the `N` ray modes, whose raises give entries
`Aᵢ² (k+1)` that are nonzero and distinct, bounds the whole mass below by
`Aᵢ² · N(N+1)/2` at `Λ = N + 2`.  This is the quantitative form of the growth. -/
theorem magCutoffKernel_hs_mass_ray_lower (A : Fin d → ℝ) (i₀ : Fin d) (N : ℕ) :
    A i₀ ^ 2 * ((N : ℝ) * ((N : ℝ) + 1) / 2)
      ≤ ∑ m : Fin d → Fin (N + 2), ∑ n : Fin d → Fin (N + 2), ‖magCutoffKernel A m n‖ ^ 2 := by
  classical
  have hray : ∀ k : Fin N,
      A i₀ ^ 2 * ((k.val : ℝ) + 1)
        ≤ ∑ m : Fin d → Fin (N + 2), ‖magCutoffKernel A m (rayMode N i₀ k)‖ ^ 2 := by
    intro k
    have hraise : (rayMode N i₀ k i₀).val + 1 < N + 2 := by
      rw [rayMode_self_val]
      omega
    have hentry := norm_sq_magCutoffKernel_raise A (rayMode N i₀ k) i₀ hraise
    have hle : ‖magCutoffKernel A (Function.update (rayMode N i₀ k) i₀
        ⟨(rayMode N i₀ k i₀).val + 1, hraise⟩) (rayMode N i₀ k)‖ ^ 2
        ≤ ∑ m : Fin d → Fin (N + 2), ‖magCutoffKernel A m (rayMode N i₀ k)‖ ^ 2 := by
      have hsplit : ∑ m : Fin d → Fin (N + 2), ‖magCutoffKernel A m (rayMode N i₀ k)‖ ^ 2
          = ‖magCutoffKernel A (Function.update (rayMode N i₀ k) i₀
              ⟨(rayMode N i₀ k i₀).val + 1, hraise⟩) (rayMode N i₀ k)‖ ^ 2
            + ∑ m ∈ (Finset.univ : Finset (Fin d → Fin (N + 2))).erase
                (Function.update (rayMode N i₀ k) i₀
                  ⟨(rayMode N i₀ k i₀).val + 1, hraise⟩),
                ‖magCutoffKernel A m (rayMode N i₀ k)‖ ^ 2 := by
        rw [← Finset.sum_erase_add
          (s := (Finset.univ : Finset (Fin d → Fin (N + 2))))
          (a := Function.update (rayMode N i₀ k) i₀ ⟨(rayMode N i₀ k i₀).val + 1, hraise⟩)
          (f := fun m => ‖magCutoffKernel A m (rayMode N i₀ k)‖ ^ 2)
          (Finset.mem_univ (Function.update (rayMode N i₀ k) i₀
            ⟨(rayMode N i₀ k i₀).val + 1, hraise⟩))]
        ring
      rw [hsplit]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
    rw [hentry, rayMode_self_val] at hle
    refine le_trans ?_ hle
    have hcast : ((k.val + 1 : ℕ) : ℝ) + 1 = (k.val : ℝ) + 1 + 1 := by push_cast; ring
    rw [hcast]
    nlinarith [mul_nonneg (sq_nonneg (A i₀)) (by positivity : (0:ℝ) ≤ 1)]
  have hsub : ∑ k : Fin N, ∑ m : Fin d → Fin (N + 2), ‖magCutoffKernel A m (rayMode N i₀ k)‖ ^ 2
      ≤ ∑ n : Fin d → Fin (N + 2), ∑ m : Fin d → Fin (N + 2), ‖magCutoffKernel A m n‖ ^ 2 := by
    have h : ∑ n ∈ (Finset.univ.image (fun k : Fin N => rayMode N i₀ k)),
          ∑ m : Fin d → Fin (N + 2), ‖magCutoffKernel A m n‖ ^ 2
        ≤ ∑ n : Fin d → Fin (N + 2), ∑ m : Fin d → Fin (N + 2),
            ‖magCutoffKernel A m n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ (Finset.univ.image (fun k : Fin N => rayMode N i₀ k)))
        (fun n _ _ => Finset.sum_nonneg fun m _ => by positivity)
    have hinj : Set.InjOn (fun k : Fin N => rayMode N i₀ k)
        (↑(Finset.univ : Finset (Fin N))) :=
      fun x _ y _ hxy => rayMode_injective N i₀ hxy
    rwa [Finset.sum_image hinj] at h
  calc A i₀ ^ 2 * ((N : ℝ) * ((N : ℝ) + 1) / 2)
      = ∑ k : Fin N, A i₀ ^ 2 * ((k.val : ℝ) + 1) := by
        rw [← Finset.mul_sum, sum_fin_val_add_one]
    _ ≤ ∑ k : Fin N, ∑ m : Fin d → Fin (N + 2), ‖magCutoffKernel A m (rayMode N i₀ k)‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => hray k
    _ ≤ ∑ n : Fin d → Fin (N + 2), ∑ m : Fin d → Fin (N + 2), ‖magCutoffKernel A m n‖ ^ 2 :=
        hsub
    _ = ∑ m : Fin d → Fin (N + 2), ∑ n : Fin d → Fin (N + 2), ‖magCutoffKernel A m n‖ ^ 2 :=
        Finset.sum_comm

/-- **The Hilbert–Schmidt constant of the ladder is unbounded in the cut-off.**  If the field
strength does not vanish, then for **every** `σ` there is a cut-off at which the ladder's
Hilbert–Schmidt mass exceeds `σ²`.  So the `Λ^{d+1}` of §7 is not an artefact of the row estimate:
the bounded-form reading (`a = 0`, shift `σ`) cannot survive the removal of the cut-off, and the
continuum must use the relative bound of §10, where the occupation growth is charged to `Q`. -/
theorem magCutoffKernel_hs_mass_unbounded {A : Fin d → ℝ} (hA : 0 < ∑ i, A i ^ 2) :
    ∀ σ : ℝ, ∃ Λ : ℕ, σ ^ 2
      < ∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2 := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hA)
  have hS : 0 < A i₀ ^ 2 := lt_of_le_of_ne (sq_nonneg (A i₀)) (Ne.symm hi₀)
  intro σ
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * σ ^ 2 / A i₀ ^ 2 + 1)
  refine ⟨N + 2, ?_⟩
  have hN1 : 2 * σ ^ 2 / A i₀ ^ 2 < (N : ℝ) := by linarith
  have hN2 : 2 * σ ^ 2 < (N : ℝ) * A i₀ ^ 2 := by
    rw [div_lt_iff₀ hS] at hN1
    linarith
  have hquad : σ ^ 2 < A i₀ ^ 2 * ((N : ℝ) * ((N : ℝ) + 1) / 2) := by
    have hge : (N : ℝ) / 2 ≤ (N : ℝ) * ((N : ℝ) + 1) / 2 := by
      nlinarith [sq_nonneg (N : ℝ)]
    have hstep : (N : ℝ) * A i₀ ^ 2 / 2
        ≤ A i₀ ^ 2 * ((N : ℝ) * ((N : ℝ) + 1) / 2) := by
      have h1 := mul_le_mul_of_nonneg_left hge (le_of_lt hS)
      linarith
    nlinarith [hN2, hstep]
  exact hquad.trans_le (magCutoffKernel_hs_mass_ray_lower A i₀ N)

/-! ## 8. The relative bound is uniform in the cut-off; the constant is not

§7 gives `σ(Λ) ≲ Λ^{(d+1)/2}`.  What that does and does not say about the Faris–Lavine relative
bound is worth separating, because the two halves point in opposite directions:

* **the ratio is uniform.**  `closed_farisLavine_domination` takes `a` as a *free* parameter, so for
the ladder `a(Λ) < 1` holds at every cut-off, with the same `a` (`ladder_relative_bound_uniform`).
  The reason is that at a fixed cut-off the ladder is a bounded operator: `|qK| ≤ σ(Λ)‖·‖²` and
  `a q_g ≥ 0`, so any `a` will do.  This is therefore cheap and carries no cut-off information.
* **the constant is not.**  The price is the shift `σ(Λ)`, and §7 shows it grows like a power of
  the cut-off.  A Faris–Lavine inequality with `a < 1` *and* a `Λ`-independent constant would need
  the ladder's own shift structure — each rotation `a†_i a_{i'} + h.c.` moves one occupation, so the
  ratio can be made small by AM–GM without counting modes — and that is not proved here.

So the honest summary is: `a(Λ) < 1` uniformly for a trivial reason, `b(Λ) → ∞` for the structural
reason of §7, and the continuum needs the second fact, not the first.

## 9. The concrete magnetic symbol, and the finiteness hypothesis it discharges

§6 carries `closedForm g x ≠ ⊤` as an explicit hypothesis.  For the Yang–Mills symbol it is not an
extra assumption.  The magnetic weight of `YangMillsMagneticQuartic`,
`magSymbol A n = ∑_a (∑_i A_{a i} nᵢ)²`, is exactly the symbol of `magneticEnergyForm`, and when the
ratio is positive a symbolwise comparison `c₁ f ≤ g + C` already forces `closedForm f` to be finite
wherever `closedForm g` is (`closed_dom_of_scaled_symbol_auto`).  Hence the comparison of §6 applies
to the magnetic symbol with nothing left to check by hand. -/

/-- **The ratio of the comparison is uniform in the cut-off.**  For any `a ∈ [0, 1)` the §6
comparison holds with the ladder's Hilbert–Schmidt constant `σ` only in the shift.  Since `a` is not
quantified over `Λ`, `a(Λ) < 1` at every cut-off; the uniformity is cheap (see the section note) and
the cut-off dependence sits entirely in `σ`. -/
theorem ladder_relative_bound_uniform {μ g : Idx d → ℝ} {K : Idx d → Idx d → ℂ}
    {c₁ c₂ σ a : ℝ} (hc₁ : 0 < c₁) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hdom : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2 ≤ (closedForm g x).toReal)
    (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) :
    0 < (1 - a) * c₁ ∧
      ∀ x : L2 d, closedForm g x ≠ ⊤ →
        (1 - a) * c₁ * (closedForm μ x).toReal - ((1 - a) * c₂ + σ) * ‖x‖ ^ 2
          ≤ (closedForm g x).toReal + closedKernelForm K x :=
  closed_farisLavine_domination hc₁ ha1 hdom fun x _ => by
    have hb := abs_closedKernelForm_le hσ0 hσ x
    have hq : (0 : ℝ) ≤ (closedForm g x).toReal := ENNReal.toReal_nonneg
    have hsq : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
    nlinarith [mul_nonneg ha0 hq]

/-- The magnetic symbol of the Cartan background `A`: on the mode `n` it is the sum of the squares
of the field-strength components, i.e. exactly the weight of `magneticEnergyForm`. -/
def magSymbol (A : Fin d → Fin d → ℝ) : Idx d → ℝ :=
  fun n => ∑ a, (YangMillsMagneticQuartic.magComp A a n) ^ 2

/-- **The magnetic energy form is the diagonal form of the magnetic symbol**, so §5–§6's closure
statement is about the object `YangMillsMagneticQuartic` calls `q_mag`. -/
theorem magneticEnergyForm_eq_diagonalForm_magSymbol (A : Fin d → Fin d → ℝ)
    (c : CoreCoeff d) :
    YangMillsMagneticQuartic.magneticEnergyForm A c = diagonalForm (magSymbol A) c := rfl

/-- The magnetic symbol is nonnegative: it is a sum of squares. -/
theorem magSymbol_nonneg (A : Fin d → Fin d → ℝ) (n : Idx d) :
    0 ≤ magSymbol A n :=
  Finset.sum_nonneg fun a _ => sq_nonneg (YangMillsMagneticQuartic.magComp A a n)

/-- **The finiteness hypothesis holds on the core for the magnetic symbol.** -/
theorem magSymbol_closedForm_coreEmbed {A : Fin d → Fin d → ℝ} (c : CoreCoeff d) :
    closedForm (magSymbol A) (coreEmbed c) ≠ ⊤ := by
  rw [closedForm_coreEmbed _ (magSymbol_nonneg A) c]
  exact ENNReal.ofReal_ne_top

/-- **§6 with the Yang–Mills magnetic symbol as the reference, and no finiteness hypothesis left to
discharge by hand**: the symbolwise comparison supplies it. -/
theorem magnetic_closed_dom_of_scaled {A : Fin d → Fin d → ℝ} {f : Idx d → ℝ} {c₁ C : ℝ}
    (hc₁ : 0 < c₁) (hC : 0 ≤ C)
    (h : ∀ n, c₁ * f n ≤ magSymbol A n + C) (x : L2 d)
    (hx : closedForm (magSymbol A) x ≠ ⊤) :
    c₁ * (closedForm f x).toReal - C * ‖x‖ ^ 2 ≤ (closedForm (magSymbol A) x).toReal :=
  closed_dom_of_scaled_symbol_auto hc₁ (magSymbol_nonneg A) hC h x hx

/-! ## 10. The sharp relative form bound of the ladder, uniform in the cut-off

§7 treated the ladder as a *bounded* perturbation and paid `σ(Λ) ≍ Λ^{(d+1)/2}`.  As a *form*
perturbation it costs far less, because the ladder is a sum of `√(nᵢ+1)`-weighted raises and each
raise is a partial isometry:

`Sᵢ eₙ = Aᵢ √(nᵢ+1) e_{raise n i}`,  `Sᵢ^* Sᵢ = Aᵢ² diag(nᵢ+1)`,  `Sᵢ Sᵢ^* ≤ Aᵢ² · 1`.

The first identity is the occupation piece — the reference form carries it with ratio `1/2` after
AM–GM with unit weight — and the second is the shift piece, whose sum over `n` is at most
`Aᵢ²‖x‖²` because raising one occupation is *injective* (`sum_raiseIdx_le`).  Both constants below
contain no `Λ`:

`‖q_K(x)‖ ≤ ½ Q(x) + ½ (Σᵢ Aᵢ²) ‖x‖²`,  `Q(x) = Σₙ (Σᵢ (nᵢ+1)) ‖x n‖²`.

That is the sharp uniform bound: `a = 1/2` with a cut-off-independent constant `(Σᵢ Aᵢ²)/2`.
Rescaling the AM–GM weight `ε` moves along the family `(a, b) = (ε/2, (Σ Aᵢ²)/(2ε))`, so `a = 1/2`
is the unit-weight member, not a claim that no other member exists. -/

/-- Raise the `i`-th occupation by one, or leave the multi-index alone when the raise would leave
the cut-off.  Making it a total map is what allows it to be reindexed. -/
def raiseIdx {Λ : ℕ} (n : Fin d → Fin Λ) (i : Fin d) : Fin d → Fin Λ :=
  if h : (n i).val + 1 < Λ then Function.update n i ⟨(n i).val + 1, h⟩ else n

/-- **Raising one occupation by one is injective.**  Two indices that raise to the same
multi-index agree at `i` (the raised value determines `nᵢ`) and at every other coordinate (the
update leaves them alone). -/
theorem update_succ_inj {Λ : ℕ} {i : Fin d} {n n' : Fin d → Fin Λ}
    (h : (n i).val + 1 < Λ) (h' : (n' i).val + 1 < Λ)
    (heq : Function.update n i ⟨(n i).val + 1, h⟩
      = Function.update n' i ⟨(n' i).val + 1, h'⟩) : n = n' := by
  classical
  have hval : (n i).val + 1 = (n' i).val + 1 := by
    have hhead : (⟨(n i).val + 1, h⟩ : Fin Λ) = ⟨(n' i).val + 1, h'⟩ := by
      have h1 := congrFun heq i
      rw [Function.update_apply, Function.update_apply] at h1
      simpa using h1
    exact congrArg Fin.val hhead
  have hni : n i = n' i := Fin.ext (by omega)
  funext j
  by_cases hj : j = i
  · subst hj
    exact hni
  · have h1 := congrFun heq j
    have hji : ¬ (i = j) := fun hc => hj hc.symm
    rw [Function.update_apply, Function.update_apply] at h1
    simpa [hj, hji] using h1

/-- **The raise is a partial isometry**: the raised coefficients summed over all multi-indices
cost at most the whole norm.  Raising is injective on the indices where it is defined, so its image
can be reindexed inside the full index set. -/
theorem sum_raiseIdx_le {Λ : ℕ} (x : (Fin d → Fin Λ) → ℂ) (i : Fin d) :
    ∑ n ∈ (Finset.univ : Finset (Fin d → Fin Λ)).filter (fun n => (n i).val + 1 < Λ),
        ‖x (raiseIdx n i)‖ ^ 2
      ≤ ∑ n, ‖x n‖ ^ 2 := by
  classical
  have hmem : ∀ n ∈ (Finset.univ : Finset (Fin d → Fin Λ)).filter
      (fun n => (n i).val + 1 < Λ), (n i).val + 1 < Λ :=
    fun n hn => (Finset.mem_filter.mp hn).2
  have himg : ∑ n ∈ (Finset.univ : Finset (Fin d → Fin Λ)).filter
        (fun n => (n i).val + 1 < Λ), ‖x (raiseIdx n i)‖ ^ 2
      = ∑ m ∈ ((Finset.univ : Finset (Fin d → Fin Λ)).filter
          (fun n => (n i).val + 1 < Λ)).image (fun n => raiseIdx n i), ‖x m‖ ^ 2 := by
    refine Finset.sum_bij (fun n _ => raiseIdx n i) ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_image_of_mem _ ha
    · intro a₁ ha₁ a₂ ha₂ heq
      have hr1 : raiseIdx a₁ i = Function.update a₁ i ⟨(a₁ i).val + 1, hmem a₁ ha₁⟩ := by
        simp only [raiseIdx, dif_pos (hmem a₁ ha₁)]
      have hr2 : raiseIdx a₂ i = Function.update a₂ i ⟨(a₂ i).val + 1, hmem a₂ ha₂⟩ := by
        simp only [raiseIdx, dif_pos (hmem a₂ ha₂)]
      have heq' : raiseIdx a₁ i = raiseIdx a₂ i := heq
      rw [hr1, hr2] at heq'
      exact update_succ_inj (hmem a₁ ha₁) (hmem a₂ ha₂) heq'
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact ⟨a, ha, rfl⟩
    · intro a _
      rfl
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro m _ _
  rw [pow_two]
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **The shift sum in the form the AM–GM produces it**: the same reindexing, with the guard as a
plain `if` so that it matches the `dite` of the kernel definition pointwise. -/
theorem sum_raise_ite_le {Λ : ℕ} (x : (Fin d → Fin Λ) → ℂ) (i : Fin d) :
    ∑ n, (if (n i).val + 1 < Λ then ‖x (raiseIdx n i)‖ ^ 2 else 0) ≤ ∑ n, ‖x n‖ ^ 2 := by
  refine (le_of_eq ?_).trans (sum_raiseIdx_le x i)
  exact (Finset.sum_filter (s := Finset.univ)
    (p := fun n : Fin d → Fin Λ => (n i).val + 1 < Λ)
    (f := fun n => ‖x (raiseIdx n i)‖ ^ 2)).symm

/-- **The ladder's matrix element, written as a sum over raising directions.** -/
theorem ladder_form_eq_sum {Λ : ℕ} (A : Fin d → ℝ) (x : (Fin d → Fin Λ) → ℂ) :
    (∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n)
      = ∑ n, ∑ i, if h : (n i).val + 1 < Λ then
          ((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)
            * ((starRingEnd ℂ) (x (Function.update n i ⟨(n i).val + 1, h⟩)) * x n) else 0 := by
  classical
  have hstep : ∀ (m n : Fin d → Fin Λ),
      (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n
        = ∑ i, (starRingEnd ℂ) (x m) * magShiftTerm A n i m * x n := by
    intro m n
    rw [magCutoffKernel, Finset.mul_sum, Finset.sum_mul]
  simp only [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (n i).val + 1 < Λ
  · have hsingle : ∀ m : Fin d → Fin Λ,
        (starRingEnd ℂ) (x m) * magShiftTerm A n i m * x n
          = if m = Function.update n i ⟨(n i).val + 1, h⟩ then
              ((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)
                * ((starRingEnd ℂ) (x m) * x n) else 0 := by
      intro m
      rw [magShiftTerm, dif_pos h]
      by_cases hm : m = Function.update n i ⟨(n i).val + 1, h⟩
      · rw [if_pos hm, if_pos hm]
        ring
      · rw [if_neg hm, if_neg hm, mul_zero]
        ring
    rw [Finset.sum_congr rfl fun m _ => hsingle m, dif_pos h]
    rw [Finset.sum_eq_single (Function.update n i ⟨(n i).val + 1, h⟩)]
    · simp
    · intro m _ hm
      rw [if_neg hm]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [magShiftTerm, dif_neg h]
    ring

/-- **The sharp uniform form bound of the ladder.**  With `Q(x) = Σₙ (Σᵢ (nᵢ+1)) ‖x n‖²`,

`‖q_K(x)‖ ≤ ½ Q(x) + ½ (Σᵢ Aᵢ²) ‖x‖²`,

and neither `1/2` nor `(Σᵢ Aᵢ²)/2` depends on the cut-off `Λ`.  Compare §7: the *bounded* constant
grows like `Λ^{(d+1)/2}`, while this form bound does not grow at all. -/
theorem ladder_form_norm_le {Λ : ℕ} (A : Fin d → ℝ) (x : (Fin d → Fin Λ) → ℂ) :
    ‖∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n‖
      ≤ (1 / 2) * (∑ n, (∑ i, ((n i).val + 1 : ℝ)) * ‖x n‖ ^ 2)
        + (1 / 2) * (∑ i, A i ^ 2) * (∑ n, ‖x n‖ ^ 2) := by
  classical
  rw [ladder_form_eq_sum]
  -- the single-shift sums, which the reindexing lemma bounds
  have hshift : ∀ i : Fin d,
      ∑ n, (if h : (n i).val + 1 < Λ then
          ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2 else 0) ≤ ∑ n, ‖x n‖ ^ 2 := by
    intro i
    have hpt : ∀ n : Fin d → Fin Λ,
        (if h : (n i).val + 1 < Λ then
            ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2 else 0)
          = (if (n i).val + 1 < Λ then ‖x (raiseIdx n i)‖ ^ 2 else 0) := by
      intro n
      by_cases h : (n i).val + 1 < Λ
      · rw [dif_pos h, if_pos h]
        have hr : raiseIdx n i = Function.update n i ⟨(n i).val + 1, h⟩ := by
          simp only [raiseIdx, dif_pos h]
        rw [hr]
      · rw [dif_neg h, if_neg h]
    rw [Finset.sum_congr rfl fun n _ => hpt n]
    exact sum_raise_ite_le x i
  -- termwise AM–GM
  have hterm : ∀ n : Fin d → Fin Λ, ∀ i : Fin d,
      ‖(if h : (n i).val + 1 < Λ then
          ((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)
            * ((starRingEnd ℂ) (x (Function.update n i ⟨(n i).val + 1, h⟩)) * x n) else 0)‖
        ≤ (if h : (n i).val + 1 < Λ then
            (1 / 2) * (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2) else 0)
          + (if h : (n i).val + 1 < Λ then
              (1 / 2) * (A i ^ 2 * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2) else 0) := by
    intro n i
    by_cases h : (n i).val + 1 < Λ
    · rw [dif_pos h, dif_pos h, dif_pos h]
      have hc : ‖((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)‖
          = |A i| * Real.sqrt ((n i).val + 1) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [norm_mul, norm_mul, Complex.norm_conj, hc]
      have h2 : 2 * (|A i| * Real.sqrt ((n i).val + 1)
            * (‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ * ‖x n‖))
          ≤ (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2
            + A i ^ 2 * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2) := by
        have hsq : Real.sqrt ((n i).val + 1) ^ 2 = ((n i).val + 1 : ℝ) :=
          Real.sq_sqrt (by positivity)
        have habs : |A i| ^ 2 = A i ^ 2 := sq_abs _
        nlinarith [sq_nonneg (Real.sqrt ((n i).val + 1) * ‖x n‖
          - |A i| * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖), hsq, habs]
      linarith
    · rw [dif_neg h, dif_neg h, dif_neg h, norm_zero]
      positivity
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => hterm n i)).trans ?_
  simp only [Finset.sum_add_distrib]
  have hA1 : ∑ n, ∑ i, (if h : (n i).val + 1 < Λ then
        (1 / 2) * (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2) else 0)
      ≤ (1 / 2) * (∑ n, ((∑ i, ((n i).val : ℝ)) + (∑ _i : Fin d, (1 : ℝ))) * ‖x n‖ ^ 2) := by
    have hinner : ∀ n : Fin d → Fin Λ,
        ∑ i, (if h : (n i).val + 1 < Λ then
            (1 / 2) * (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2) else 0)
          ≤ (1 / 2) * (((∑ i, ((n i).val : ℝ)) + (∑ _i : Fin d, (1 : ℝ))) * ‖x n‖ ^ 2) := by
      intro n
      calc ∑ i, (if h : (n i).val + 1 < Λ then
            (1 / 2) * (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2) else 0)
          ≤ ∑ i, (1 / 2) * (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2) := by
            refine Finset.sum_le_sum fun i _ => ?_
            by_cases h : (n i).val + 1 < Λ
            · rw [dif_pos h]
            · rw [dif_neg h]
              positivity
        _ = (1 / 2) * ((∑ i, ((n i).val + 1 : ℝ)) * ‖x n‖ ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_mul]
        _ = (1 / 2) * (((∑ i, ((n i).val : ℝ)) + (∑ _i : Fin d, (1 : ℝ)))
              * ‖x n‖ ^ 2) := by
            rw [Finset.sum_add_distrib]
    refine (Finset.sum_le_sum fun n _ => hinner n).trans (le_of_eq ?_)
    rw [← Finset.mul_sum]
  have hA2 : ∑ n, ∑ i, (if h : (n i).val + 1 < Λ then
        (1 / 2) * (A i ^ 2 * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2) else 0)
      ≤ (1 / 2) * (∑ i, A i ^ 2) * (∑ n, ‖x n‖ ^ 2) := by
    rw [Finset.sum_comm]
    have hrow : ∀ i : Fin d, ∑ n, (if h : (n i).val + 1 < Λ then
          (1 / 2) * (A i ^ 2 * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2) else 0)
        ≤ (1 / 2) * A i ^ 2 * (∑ n, ‖x n‖ ^ 2) := by
      intro i
      have hfac : ∀ n : Fin d → Fin Λ,
          (if h : (n i).val + 1 < Λ then
              (1 / 2) * (A i ^ 2 * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2) else 0)
            = (1 / 2) * A i ^ 2 * (if h : (n i).val + 1 < Λ then
                ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2 else 0) := by
        intro n
        by_cases h : (n i).val + 1 < Λ
        · rw [dif_pos h, dif_pos h]
          ring
        · rw [dif_neg h, dif_neg h, mul_zero]
      rw [Finset.sum_congr rfl fun n _ => hfac n, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (hshift i) ?_
      positivity
    refine (Finset.sum_le_sum fun i _ => hrow i).trans (le_of_eq ?_)
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.mul_sum]
  exact add_le_add hA1 hA2

/-- **The sharp relative form bound, in the shape §6 consumes.**  Taking the real part of the
ladder form (which is what `closedKernelForm` reads) costs nothing: `|Re z| ≤ ‖z‖`. -/
theorem ladder_form_abs_re_le {Λ : ℕ} (A : Fin d → ℝ) (x : (Fin d → Fin Λ) → ℂ) :
    |(∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n).re|
      ≤ (1 / 2) * (∑ n, (∑ i, ((n i).val + 1 : ℝ)) * ‖x n‖ ^ 2)
        + (1 / 2) * (∑ i, A i ^ 2) * (∑ n, ‖x n‖ ^ 2) := by
  refine (Complex.abs_re_le_norm _).trans (ladder_form_norm_le A x)

/-- **The AM–GM weight family behind the sharp bound.**  For `ε > 0`, `2 s t ≤ ε s² + t²/ε`, i.e.
`s t ≤ (ε/2) s² + t²/(2ε)`.  Applied with `s = √(nᵢ+1)‖x n‖` and `t = |Aᵢ|‖x (raise n i)‖` this is
exactly the termwise step of `ladder_form_norm_le`: `ε = 1` is the unit-weight member, whose ratio
on `Q` is `1/2` and whose constant is `(Σᵢ Aᵢ²)/2`.  Every other `ε` gives another member
`(a, b) = (ε/2, (Σᵢ Aᵢ²)/(2ε))` of the same trade-off, so `1/2` is a *choice of weight* rather than
an optimal ratio: `ε → 0` makes `a` arbitrarily small and the constant grows like `1/ε`. -/
theorem amgm_weight_family {ε : ℝ} (hε : 0 < ε) (s t : ℝ) :
    2 * s * t ≤ ε * s ^ 2 + t ^ 2 / ε := by
  have h : 0 ≤ (ε * s - t) ^ 2 := sq_nonneg _
  have hmul : 0 ≤ ε * (ε * s ^ 2 + t ^ 2 / ε - 2 * s * t) := by
    have hid : ε * (ε * s ^ 2 + t ^ 2 / ε - 2 * s * t) = (ε * s - t) ^ 2 := by
      field_simp
      ring
    rw [hid]
    exact h
  have hnn : 0 ≤ ε * s ^ 2 + t ^ 2 / ε - 2 * s * t := by
    by_contra hcon
    have hlt : ε * (ε * s ^ 2 + t ^ 2 / ε - 2 * s * t) < 0 :=
      mul_neg_of_pos_of_neg hε (not_le.mp hcon)
    linarith
  linarith

/-- **A worked member of the family: `ε = 1/2`.**  Here `a = ε/2 = 1/4` and
`b = Σ Aᵢ²/(2ε) = Σ Aᵢ²`, so the *same* ladder also satisfies `|q| ≤ ¼ Q + (Σᵢ Aᵢ²)‖x‖²` — a
different point of the trade-off
from the unit-weight `½ Q + ½(Σᵢ Aᵢ²)‖x‖²`.  In particular the ratio `1/2` is not forced by the
ladder; it is the weight `ε = 1` read off the family. -/
theorem amgm_weight_half (s t : ℝ) : 2 * s * t ≤ (1 / 2) * s ^ 2 + 2 * t ^ 2 := by
  have h : 0 ≤ (s - 2 * t) ^ 2 := sq_nonneg _
  nlinarith [h]

/-- Numeric instance of the `ε = 1/2` member: at `s = 3`, `t = 1` the bound reads `6 ≤ 13/2`. -/
example : (2 : ℝ) * 3 * 1 ≤ (1 / 2) * 3 ^ 2 + 2 * 1 ^ 2 := by norm_num

/-- **The sharp ratio is a statement about the closed form on `L²`.**  `ladder_form_norm_le` gives
the cut-off ratio `a = 1/2`, and `closed_farisLavine_domination` consumes exactly that shape, so the
domination on the closed form (`closedForm` and `closedKernelForm`, i.e. on the `L²` domain rather
than on the finite core) carries the same `1/2`: with `a = 1/2`, `1 - a = 1/2` multiplies both the
diagonal reference form and its constant, and the Hilbert–Schmidt mass `σ` enters the shift
unchanged.  This is the closed-form counterpart of the cut-off bound — the finite matrix statement
is what proves the ratio, and this is where the ratio is used. -/
theorem ladder_closed_domination_sharp {μ g : Idx d → ℝ} {K : Idx d → Idx d → ℂ}
    {c₁ c₂ σ : ℝ} (hc₁ : 0 < c₁)
    (hdom : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2 ≤ (closedForm g x).toReal)
    (hσ0 : 0 ≤ σ)
    (hσ : ∀ s : Finset (Idx d), ∑ m ∈ s, ∑ n ∈ s, ‖K m n‖ ^ 2 ≤ σ ^ 2) :
    0 < (1 / 2) * c₁ ∧
      ∀ x : L2 d, closedForm g x ≠ ⊤ →
        (1 / 2) * c₁ * (closedForm μ x).toReal - ((1 / 2) * c₂ + σ) * ‖x‖ ^ 2
          ≤ (closedForm g x).toReal + closedKernelForm K x := by
  have h := ladder_relative_bound_uniform (d := d) (μ := μ) (g := g) (K := K)
    (c₁ := c₁) (c₂ := c₂) (σ := σ) (a := 1 / 2) hc₁ (by norm_num) (by norm_num) hdom hσ0 hσ
  refine ⟨by positivity, ?_⟩
  intro x hx
  have hx' := h.2 x hx
  norm_num at hx' ⊢
  linarith

/-! ## 11. The Pareto frontier of the weight family

`amgm_weight_family` writes the AM–GM step with one free weight `ε > 0`: `2st ≤ ε s² + t²/ε`.
Read in the ratio/shift coordinates of the ladder — `a = ε/2` on the occupation form and
`b = 1/(2ε)` on the vector norm, scaled by `Σᵢ Aᵢ²` in the ladder — the weight moves along the
curve `a b = 1/4`.  The theorems below make that a statement about the frontier instead of a remark:
the termwise inequality holds for **all** `s, t` exactly when `a b ≥ 1/4`, and for a fixed ratio `a`
the least admissible shift is `1/(4a)`, attained at `s = t/(2a)`.  So no weight in the family is a
weakening of another — each is sharp, and choosing `ε` is choosing the point `(ε/2, 1/(2ε))` on one
curve.  Everything here is termwise; for the ladder the sum over `i` may beat the sum of the
termwise bounds when the `Aᵢ` differ, so the frontier below is the frontier of the *weight*. -/

/-- **The square identity behind the frontier.**  For `a ≠ 0`,
`2a s² + 2(1/(4a)) t² − 2 s t = 2a (s − t/(2a))²`. -/
theorem amgm_frontier_identity {a : ℝ} (ha : a ≠ 0) (s t : ℝ) :
    2 * a * s ^ 2 + 2 * (1 / (4 * a)) * t ^ 2 - 2 * s * t
      = 2 * a * (s - t / (2 * a)) ^ 2 := by
  field_simp
  ring

/-- **The frontier: `ab ≥ 1/4` is exactly the condition for the termwise bound.**  For `a > 0`,
`2st ≤ 2a s² + 2b t²` for every real `s, t` if and only if `a b ≥ 1/4`.  (⇒) is tested at
`s = 1/(2a)`, `t = 1`; (⇐) is the square identity. -/
theorem amgm_pareto_iff {a b : ℝ} (ha : 0 < a) :
    (∀ s t : ℝ, 2 * s * t ≤ 2 * a * s ^ 2 + 2 * b * t ^ 2) ↔ 1 / 4 ≤ a * b := by
  constructor
  · intro h
    have h1 := h (1 / (2 * a)) 1
    have hval : 2 * a * (1 / (2 * a)) ^ 2 + 2 * b * 1 ^ 2 - 2 * (1 / (2 * a)) * 1
        = 2 * b - 1 / (2 * a) := by
      field_simp
      ring
    have h2 : 1 / (2 * a) ≤ 2 * b := by linarith
    have h3 : a * (1 / (2 * a)) = 1 / 2 := by
      field_simp
    have h4 : a * (2 * b) = 2 * (a * b) := by ring
    have h5 := mul_le_mul_of_nonneg_left h2 (le_of_lt ha)
    rw [h3, h4] at h5
    linarith
  · intro h s t
    have hb : 1 / (4 * a) ≤ b := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * a)]
      linarith
    have hid := amgm_frontier_identity (ne_of_gt ha) s t
    have hstep : 2 * (1 / (4 * a)) * t ^ 2 ≤ 2 * b * t ^ 2 := by
      have := mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ 2 * t ^ 2)
      linarith
    have hnn : 0 ≤ 2 * a * (s - t / (2 * a)) ^ 2 := by positivity
    linarith

/-- **Pareto: for a fixed ratio the shift `1/(4a)` is minimal.**  The termwise bound holds at
`b = 1/(4a)`, and every admissible `b` satisfies `1/(4a) ≤ b` — so `b = S/(4a)` (the ladder's shift
coefficient, with `S = Σᵢ Aᵢ²`) is the least shift the weight can charge for ratio `a`, and by
`amgm_pareto_iff` it is attained.  Together with `amgm_weight_family` this says the family
`(ε/2, Σᵢ Aᵢ²/(2ε))` *is* the frontier rather than a sufficient condition on it. -/
theorem amgm_min_shift {a : ℝ} (ha : 0 < a) :
    (∀ s t : ℝ, 2 * s * t ≤ 2 * a * s ^ 2 + 2 * (1 / (4 * a)) * t ^ 2) ∧
      ∀ b : ℝ, (∀ s t : ℝ, 2 * s * t ≤ 2 * a * s ^ 2 + 2 * b * t ^ 2) → 1 / (4 * a) ≤ b := by
  refine ⟨?_, ?_⟩
  · intro s t
    refine (amgm_pareto_iff (a := a) (b := 1 / (4 * a)) ha).mpr ?_ s t
    have hone : a * (1 / (4 * a)) = 1 / 4 := by
      field_simp
    linarith
  · intro b hb
    have h := (amgm_pareto_iff (a := a) (b := b) ha).mp hb
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * a)]
    linarith

/-- **Every member of `amgm_weight_family` is a point of the frontier.**  The bound
`2st ≤ ε s² + t²/ε` is the strength-`(ε/2, 1/(2ε))` termwise bound, and `(ε/2)·(1/(2ε)) = 1/4` for
every `ε > 0`: all weights lie on the same curve, so `amgm_weight_family` has no slack to give at
any weight, and the choice of `ε` is a choice of position, not of strength. -/
theorem amgm_weight_family_frontier {ε : ℝ} (hε : 0 < ε) (s t : ℝ) :
    2 * s * t ≤ 2 * (ε / 2) * s ^ 2 + 2 * (1 / (2 * ε)) * t ^ 2 := by
  have h := amgm_weight_family hε s t
  have hid : 2 * (ε / 2) * s ^ 2 + 2 * (1 / (2 * ε)) * t ^ 2 = ε * s ^ 2 + t ^ 2 / ε := by
    field_simp
  rw [hid]
  exact h

/-- The frontier product of the weight family: `(ε/2)·(1/(2ε)) = 1/4` at every `ε > 0`. -/
theorem amgm_weight_frontier_product {ε : ℝ} (hε : 0 < ε) :
    (ε / 2) * (1 / (2 * ε)) = 1 / 4 := by
  field_simp
  norm_num

/-- The ladder's shift coefficient in ratio coordinates: at weight `ε` the ratio is `a = ε/2` and
the shift is `S/(2ε) = S/(4a)`, i.e. the frontier of `amgm_min_shift` scaled by `S = Σᵢ Aᵢ²`. -/
theorem ladder_shift_of_ratio {S ε : ℝ} :
    S / (2 * ε) = S / (4 * (ε / 2)) := by
  have h : 4 * (ε / 2) = 2 * ε := by ring
  rw [h]

/-- **The frontier is attained, not merely approached.**  At the unit weight the ladder bound reads
`(a, b) = (1/2, 1/2)`, `ab = 1/4`, and equality holds at `s = t = 1`: `2st = 2` and
`2a s² + 2b t² = 2`.  That is the case `s = t/(2a)` of `amgm_frontier_identity`, so no weight can
lower the shift at fixed ratio, and none can lower the ratio at fixed shift. -/
example : (2 : ℝ) * 1 * 1 = 2 * ((1 : ℝ) / 2) * 1 ^ 2 + 2 * ((1 : ℝ) / 2) * 1 ^ 2 := by
  norm_num

/-- **The ladder is linear in the field strength**: one shift term scales as `c ·` the shift term
of `A`.  This is what makes the whole ratio family a *dilation* of the unit-weight ladder rather
than a separate estimate. -/
theorem magShiftTerm_smul {Λ : ℕ} (A : Fin d → ℝ) (c : ℝ) (n : Fin d → Fin Λ) (i : Fin d)
    (m : Fin d → Fin Λ) :
    magShiftTerm (fun i => c * A i) n i m = (c : ℂ) * magShiftTerm A n i m := by
  classical
  simp only [magShiftTerm]
  by_cases h : (n i).val + 1 < Λ
  · rw [dif_pos h, dif_pos h]
    by_cases hm : m = Function.update n i ⟨(n i).val + 1, h⟩
    · rw [if_pos hm, if_pos hm]
      push_cast
      ring
    · rw [if_neg hm, if_neg hm, mul_zero]
  · rw [dif_neg h, dif_neg h, mul_zero]

/-- **The ladder kernel is linear in the field strength.** -/
theorem magCutoffKernel_smul {Λ : ℕ} (A : Fin d → ℝ) (c : ℝ) (m n : Fin d → Fin Λ) :
    magCutoffKernel (fun i => c * A i) m n = (c : ℂ) * magCutoffKernel A m n := by
  rw [magCutoffKernel, magCutoffKernel, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => magShiftTerm_smul A c n i m

/-- **The ladder form is linear in the field strength.** -/
theorem ladder_form_smul {Λ : ℕ} (A : Fin d → ℝ) (c : ℝ) (x : (Fin d → Fin Λ) → ℂ) :
    (∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel (fun i => c * A i) m n * x n)
      = (c : ℂ) * ∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [magCutoffKernel_smul]
  ring

/-- **The ladder-level bound at every ratio `a > 0`.**  With `Q(x) = Σₙ (Σᵢ (nᵢ+1)) ‖x n‖²` and
`S = Σᵢ Aᵢ²`,

`‖q_K(x)‖ ≤ a Q(x) + (S/(4a)) ‖x‖²`,

which is the point `(a, S/(4a))` of the frontier `amgm_min_shift` — `a = 1/2` is
`ladder_form_norm_le`.  It is proved by dilation: `ladder_form_norm_le` applied to the field
strength `A/(2a)` reads `‖q_A(x)‖/(2a) ≤ ½Q + (S/(8a²))‖x‖²`, and multiplying by `2a` is the
statement.  So the whole frontier is one theorem and a rescaling, not one theorem per weight. -/
theorem ladder_form_norm_le_of_ratio {Λ : ℕ} (A : Fin d → ℝ) {a : ℝ} (ha : 0 < a)
    (x : (Fin d → Fin Λ) → ℂ) :
    ‖∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n‖
      ≤ a * (∑ n, (∑ i, ((n i).val + 1 : ℝ)) * ‖x n‖ ^ 2)
        + ((∑ i, A i ^ 2) / (4 * a)) * (∑ n, ‖x n‖ ^ 2) := by
  classical
  set q : ℂ := ∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n with hq
  set Q : ℝ := ∑ n, (∑ i, ((n i).val + 1 : ℝ)) * ‖x n‖ ^ 2 with hQ
  set S : ℝ := ∑ i, A i ^ 2 with hS
  set N : ℝ := ∑ n, ‖x n‖ ^ 2 with hN
  set c : ℝ := 1 / (2 * a) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have h := ladder_form_norm_le (Λ := Λ) (A := fun i => c * A i) x
  have hSs : (∑ i : Fin d, (c * A i) ^ 2) = c ^ 2 * S := by
    rw [hS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hq' : (∑ m, ∑ n, (starRingEnd ℂ) (x m)
        * magCutoffKernel (fun i => c * A i) m n * x n) = (c : ℂ) * q := by
    rw [hq]
    exact ladder_form_smul A c x
  rw [← hQ, ← hN, hSs, hq', norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hcpos] at h
  have h2a : (0 : ℝ) < 2 * a := by positivity
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt h2a)
  have e1 : 2 * a * (c * ‖q‖) = ‖q‖ := by
    rw [hc]
    field_simp
  have e2 : 2 * a * ((1 / 2) * Q + (1 / 2) * (c ^ 2 * S) * N) = a * Q + S / (4 * a) * N := by
    rw [hc]
    field_simp
    ring
  rw [e1, e2] at hmul
  exact hmul

/-! ## 11.1 The two-mode section: why the termwise shift is not the global optimum

§11 is a statement about the *weight*: it says `b = S/(4a)` is the least shift that a termwise
AM–GM at ratio `a` can charge, and it is attained term by term.  That is not the same as the sharp
constant of the ladder, because the sum over `i` in `ladder_form_eq_sum` may beat the sum of the
termwise bounds when the `Aᵢ` differ.

This subsection computes the sharp constant on the smallest section where the difference shows: the
two modes `δ_n` and `δ_{n+eᵢ}`, with every other occupation zero, so that `Q(δ_n) = d` and
`Q(δ_{n+eᵢ}) = d + 1` and the matrix element is `Aᵢ√(nᵢ+1) = Aᵢ`.  Writing the state as `(α, β)` the
form is `2Aαβ` and `Q` is `dα² + (d+1)β²`, so the sharp shift is the top eigenvalue of a `2 × 2`
problem, and it is **not** `A²/(4a)`: it is `√(A² + a²/4) − a(2d+1)/2`.  The two agree only in the
limit `a → 0`, which is exactly where the termwise constant blows up. -/

/-- The sharp shift constant of the ladder on the two-mode section: `√(A² + a²/4) − a(2d+1)/2`. -/
noncomputable def twoModeShift (A a : ℝ) (d : ℕ) : ℝ :=
  Real.sqrt (A ^ 2 + a ^ 2 / 4) - a * ((2 * (d : ℝ) + 1) / 2)

/-- The shift functional on the two-mode section, as a Rayleigh quotient in the amplitudes
`(α, β)`: `(2Aαβ − a(dα² + (d+1)β²))/(α² + β²)`.  Its supremum is `twoModeShift`. -/
noncomputable def twoModeRatio (A a : ℝ) (d : ℕ) (α β : ℝ) : ℝ :=
  (2 * A * α * β - a * ((d : ℝ) * α ^ 2 + ((d : ℝ) + 1) * β ^ 2)) / (α ^ 2 + β ^ 2)

/-- **The characteristic identity of the two-mode optimum.**  `γ = √(A² + a²/4) − a(2d+1)/2`
solves `γ² + a(2d+1)γ + a²d(d+1) = A²`, i.e. the `2 × 2` determinant condition
`(ad + γ)(a(d+1) + γ) = A²` at which the section's matrix has a kernel vector. -/
theorem twoModeShift_key (A a : ℝ) (d : ℕ) :
    twoModeShift A a d ^ 2 + a * (2 * (d : ℝ) + 1) * twoModeShift A a d
        + a ^ 2 * (d : ℝ) * ((d : ℝ) + 1) = A ^ 2 := by
  have hm : twoModeShift A a d + a * (2 * (d : ℝ) + 1) / 2
      = Real.sqrt (A ^ 2 + a ^ 2 / 4) := by
    simp only [twoModeShift]
    ring
  have hs : Real.sqrt (A ^ 2 + a ^ 2 / 4) ^ 2 = A ^ 2 + a ^ 2 / 4 :=
    Real.sq_sqrt (by positivity)
  have h2 : (twoModeShift A a d + a * (2 * (d : ℝ) + 1) / 2) ^ 2 = A ^ 2 + a ^ 2 / 4 := by
    rw [hm, hs]
  nlinarith [h2]

/-- **AM–GM with a determinant hypothesis**: `2Aαβ ≤ sα² + tβ²` whenever `s, t ≥ 0` and
`A² ≤ st`.  This is the `2 × 2` positivity used below, in the form that does not need a square root
of `s` or `t` to be nonzero. -/
theorem two_mul_le_of_sq_le_mul {A s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hA : A ^ 2 ≤ s * t)
    (α β : ℝ) : 2 * A * α * β ≤ s * α ^ 2 + t * β ^ 2 := by
  have h1 : 2 * A * α * β ≤ 2 * |A| * (|α| * |β|) := by
    have hle : A * α * β ≤ |A| * (|α| * |β|) := by
      have h2 := le_abs_self (A * α * β)
      have h3 : |A * α * β| = |A| * (|α| * |β|) := by
        rw [abs_mul, abs_mul]
        ring
      rw [h3] at h2
      exact h2
    linarith
  have h2 : 2 * |A| * (|α| * |β|) ≤ 2 * Real.sqrt (s * t) * (|α| * |β|) := by
    have hst : |A| ≤ Real.sqrt (s * t) := by
      rw [← Real.sqrt_sq (abs_nonneg A)]
      refine Real.sqrt_le_sqrt ?_
      rw [sq_abs]
      exact hA
    have h0 : 0 ≤ |α| * |β| := by positivity
    nlinarith
  have h3 : 2 * Real.sqrt (s * t) * (|α| * |β|) ≤ s * α ^ 2 + t * β ^ 2 := by
    have hmul : Real.sqrt (s * t) = Real.sqrt s * Real.sqrt t := Real.sqrt_mul hs t
    have hs' : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
    have ht' : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
    have hsq : 2 * (Real.sqrt s * |α|) * (Real.sqrt t * |β|)
        ≤ (Real.sqrt s * |α|) ^ 2 + (Real.sqrt t * |β|) ^ 2 := two_mul_le_add_sq _ _
    have e1 : 2 * (Real.sqrt s * |α|) * (Real.sqrt t * |β|)
        = 2 * (Real.sqrt s * Real.sqrt t) * (|α| * |β|) := by ring
    have e2 : (Real.sqrt s * |α|) ^ 2 + (Real.sqrt t * |β|) ^ 2 = s * α ^ 2 + t * β ^ 2 := by
      rw [mul_pow, mul_pow, hs', ht', sq_abs α, sq_abs β]
    rw [e1, e2] at hsq
    rw [hmul]
    exact hsq
  linarith

/-- **The two-mode optimum is an upper bound.**  For every nonzero amplitude pair, the ladder's
shift functional on the two-mode section is at most `√(A² + a²/4) − a(2d+1)/2`.  Note this is a
statement at a *fixed* ratio `a`, and the constant is strictly smaller than the termwise `A²/(4a)` —
see the worked comparison below. -/
theorem twoModeShift_le {A a : ℝ} {d : ℕ} (ha : 0 < a) (α β : ℝ) (hαβ : 0 < α ^ 2 + β ^ 2) :
    twoModeRatio A a d α β ≤ twoModeShift A a d := by
  set γ : ℝ := twoModeShift A a d with hγdef
  set s : ℝ := a * (d : ℝ) + γ with hsdef
  set t : ℝ := a * ((d : ℝ) + 1) + γ with htdef
  have hkey : γ ^ 2 + a * (2 * (d : ℝ) + 1) * γ + a ^ 2 * (d : ℝ) * ((d : ℝ) + 1) = A ^ 2 := by
    rw [hγdef]
    exact twoModeShift_key A a d
  have hsqrt : s = Real.sqrt (A ^ 2 + a ^ 2 / 4) - a / 2 := by
    rw [hsdef, hγdef]
    simp only [twoModeShift]
    ring
  have hs : 0 ≤ s := by
    rw [hsqrt]
    have hmono : Real.sqrt (a ^ 2 / 4) ≤ Real.sqrt (A ^ 2 + a ^ 2 / 4) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg A])
    have hval : Real.sqrt (a ^ 2 / 4) = a / 2 := by
      rw [show a ^ 2 / 4 = (a / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    linarith
  have ht : 0 ≤ t := by
    rw [htdef]
    nlinarith [hs, ha]
  have hst : A ^ 2 ≤ s * t := by
    rw [hsdef, htdef]
    nlinarith [hkey]
  have h := two_mul_le_of_sq_le_mul hs ht hst α β
  rw [twoModeRatio, div_le_iff₀ hαβ]
  nlinarith [h]

/-- **The two-mode optimum is attained**, with `A ≠ 0`: the pair `(α, β) = (A, ad + γ)` is the
kernel vector of the section's matrix, so the Rayleigh quotient is exactly `γ`.  Hence
`twoModeShift` is not merely a bound but the supremum on the section — the termwise `A²/(4a)` is a
strictly worse constant whenever the section is nontrivial. -/
theorem twoModeRatio_shift {A a : ℝ} {d : ℕ} (hA : A ≠ 0) :
    twoModeRatio A a d A (a * (d : ℝ) + twoModeShift A a d) = twoModeShift A a d := by
  set γ : ℝ := twoModeShift A a d with hγdef
  have hkey : γ ^ 2 + a * (2 * (d : ℝ) + 1) * γ + a ^ 2 * (d : ℝ) * ((d : ℝ) + 1) = A ^ 2 := by
    rw [hγdef]
    exact twoModeShift_key A a d
  have hA2 : 0 < A ^ 2 := by
    rcases lt_or_gt_of_ne hA with h | h <;> nlinarith
  have hnorm : A ^ 2 + (a * (d : ℝ) + γ) ^ 2 ≠ 0 := by positivity
  have hprod : (a * (d : ℝ) + γ) * (a * ((d : ℝ) + 1) + γ) = A ^ 2 := by
    nlinarith [hkey]
  rw [twoModeRatio, div_eq_iff hnorm]
  rw [show 2 * A * A * (a * (d : ℝ) + γ) = 2 * A ^ 2 * (a * (d : ℝ) + γ) by ring]
  rw [← hprod]
  ring

/-- **Worked comparison (the termwise shift is not the two-mode optimum).**  At `A = 1`, `a = 1/2`,
`d = 1` the two-mode optimum is `√(17)/4 − 3/4 = (√17 − 3)/4 ≈ 0.2808`, while the termwise frontier
of §11 charges `A²/(4a) = 1/2` at the same ratio.  So `amgm_min_shift`'s `S/(4a)` is the best
*termwise* shift, and the ladder's actual sharp shift at ratio `1/2` on this section is strictly
smaller — the sum over directions does beat the sum of termwise bounds. -/
example : twoModeShift 1 (1 / 2) 1 < (1 : ℝ) ^ 2 / (4 * (1 / 2)) := by
  have hval : twoModeShift 1 (1 / 2) 1 = Real.sqrt (17 / 16) - 3 / 4 := by
    simp only [twoModeShift]
    norm_num
  rw [hval]
  have h : Real.sqrt (17 / 16 : ℝ) < 5 / 4 := by
    calc Real.sqrt (17 / 16) < Real.sqrt ((5 / 4) ^ 2) :=
          Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 5 / 4 := Real.sqrt_sq (by norm_num)
  have hrhs : (1 : ℝ) ^ 2 / (4 * (1 / 2)) = 1 / 2 := by norm_num
  rw [hrhs]
  linarith

/-- **The termwise shift is beaten in every dimension `d ≥ 1`, with no condition on `A`.**  For
every `a > 0` and every `d ≥ 1` the two-mode optimum at ratio `a` is *strictly* below the
frontier's `A²/(4a)` — not only in the worked `d = 1` case.  The proof compares
`√(A² + a²/4) − a(2d+1)/2` with the smaller `√(A² + a²/4) − 3a/2` and squares, the difference of
squares being `((A² − 2a²)² + 28a⁴)/(16a²) > 0`, which is positive without any hypothesis.  So no
dimension makes the termwise shift the ladder's sharp constant: `S/(4a)` and the two-mode optimum
are separated by a strict inequality for every `d ≥ 1`. -/
theorem twoModeShift_lt_termwise {A a : ℝ} {d : ℕ} (hd : 1 ≤ d) (ha : 0 < a) :
    twoModeShift A a d < A ^ 2 / (4 * a) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hm3 : (3 : ℝ) * a / 2 ≤ a * ((2 * (d : ℝ) + 1) / 2) := by nlinarith [hd1, ha.le]
  have h16 : (0 : ℝ) < 16 * a ^ 2 := by positivity
  have hnum : (0 : ℝ) < (A ^ 2 - 2 * a ^ 2) ^ 2 + 28 * a ^ 4 :=
    by nlinarith [sq_nonneg (A ^ 2 - 2 * a ^ 2), pow_pos ha 4]
  have hdiff : (A ^ 2 / (4 * a) + 3 * a / 2) ^ 2 - (A ^ 2 + a ^ 2 / 4)
      = ((A ^ 2 - 2 * a ^ 2) ^ 2 + 28 * a ^ 4) / (16 * a ^ 2) := by
    field_simp
    ring
  have hsq : A ^ 2 + a ^ 2 / 4 < (A ^ 2 / (4 * a) + 3 * a / 2) ^ 2 := by
    have hquot : (0 : ℝ) < ((A ^ 2 - 2 * a ^ 2) ^ 2 + 28 * a ^ 4) / (16 * a ^ 2) :=
      div_pos hnum h16
    have hpos : (0 : ℝ) < (A ^ 2 / (4 * a) + 3 * a / 2) ^ 2 - (A ^ 2 + a ^ 2 / 4) := by
      rw [hdiff]
      exact hquot
    linarith
  have hroot : Real.sqrt (A ^ 2 + a ^ 2 / 4) < A ^ 2 / (4 * a) + 3 * a / 2 := by
    rw [Real.sqrt_lt (by positivity : (0 : ℝ) ≤ A ^ 2 + a ^ 2 / 4)]
    · exact hsq
    · positivity
  simp only [twoModeShift]
  linarith

/-! ## 12. The cut-off ladder as a kernel on `Idx d`: the box embedding

§10 proves the sharp bound for `x : (Fin d → Fin Λ) → ℂ`, on the cut-off box; the closed-form
theorem consumes a kernel on `Idx d = Fin d → ℕ`.  The two are connected here and nowhere else: the
componentwise embedding `boxEmbed n i = (n i).val` is injective, the finite matrix is continued by
zero off its image, and `boxKernel_hs_finset` shows the extended kernel satisfies the Finset
Hilbert–Schmidt condition with the **cut-off mass itself** as the constant.  Then
`ladder_closed_domination_box` applies `ladder_closed_domination_sharp` with nothing left to assume:
the ratio is `1/2` and the shift is `½c₂ + √(mass)`, so the sharp bound of §10 and the closed-form
domination are the same statement read on two index types. -/

/-- The cut-off box: multi-indices whose every occupation is below `Λ`. -/
def InBox {Λ : ℕ} (m : Idx d) : Prop := ∀ i, m i < Λ

instance {Λ : ℕ} : DecidablePred (InBox (Λ := Λ) (d := d)) := fun m =>
  show Decidable (∀ i, m i < Λ) from inferInstance

/-- The componentwise embedding of the cut-off box into `Idx d`. -/
def boxEmbed {Λ : ℕ} (n : Fin d → Fin Λ) : Idx d := fun i => (n i).val

theorem boxEmbed_injective {Λ : ℕ} : Function.Injective (boxEmbed (Λ := Λ) (d := d)) := by
  intro m n h
  funext i
  exact Fin.ext (congrFun h i)

theorem boxEmbed_mem {Λ : ℕ} (n : Fin d → Fin Λ) : InBox (Λ := Λ) (boxEmbed n) :=
  fun i => (n i).isLt

/-- Read a box element back out of `Idx d`. -/
def boxInv {Λ : ℕ} (m : Idx d) (h : InBox (Λ := Λ) m) : Fin d → Fin Λ :=
  fun i => ⟨m i, h i⟩

theorem boxEmbed_boxInv {Λ : ℕ} (m : Idx d) (h : InBox (Λ := Λ) m) :
    boxEmbed (boxInv m h) = m := rfl

theorem boxInv_boxEmbed {Λ : ℕ} (n : Fin d → Fin Λ) (h : InBox (Λ := Λ) (boxEmbed n)) :
    boxInv (boxEmbed n) h = n := by
  funext i
  exact Fin.ext rfl

theorem exists_boxEmbed {Λ : ℕ} {m : Idx d} (h : InBox (Λ := Λ) m) :
    ∃ n : Fin d → Fin Λ, boxEmbed n = m :=
  ⟨boxInv m h, boxEmbed_boxInv m h⟩

/-- **The cut-off ladder continued by zero off the box.**  On the box this is `magCutoffKernel`;
everywhere else it is `0`. -/
def boxKernel (Λ : ℕ) (A : Fin d → ℝ) (m n : Idx d) : ℂ :=
  if h : InBox (Λ := Λ) m ∧ InBox (Λ := Λ) n then
    magCutoffKernel A (boxInv m h.1) (boxInv n h.2)
  else 0

theorem boxKernel_eq_zero_left (Λ : ℕ) (A : Fin d → ℝ) {m n : Idx d}
    (h : ¬ InBox (Λ := Λ) m) : boxKernel Λ A m n = 0 := by
  unfold boxKernel
  exact dif_neg fun hc => h hc.1

theorem boxKernel_eq_zero_right (Λ : ℕ) (A : Fin d → ℝ) {m n : Idx d}
    (h : ¬ InBox (Λ := Λ) n) : boxKernel Λ A m n = 0 := by
  unfold boxKernel
  exact dif_neg fun hc => h hc.2

/-- On the box the extended kernel is the cut-off ladder. -/
theorem boxKernel_boxEmbed (Λ : ℕ) (A : Fin d → ℝ) (m n : Fin d → Fin Λ) :
    boxKernel Λ A (boxEmbed m) (boxEmbed n) = magCutoffKernel A m n := by
  have h1 : InBox (Λ := Λ) (boxEmbed (d := d) m) := boxEmbed_mem m
  have h2 : InBox (Λ := Λ) (boxEmbed (d := d) n) := boxEmbed_mem n
  unfold boxKernel
  rw [dif_pos ⟨h1, h2⟩, boxInv_boxEmbed, boxInv_boxEmbed]

/-- A sum equals its sum over the part where the summand can be nonzero, for a summand that
vanishes off a decidable predicate. -/
theorem sum_eq_sum_filter_of_zero {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) (hzero : ∀ x, ¬ p x → f x = 0) :
    ∑ x ∈ s, f x = ∑ x ∈ s.filter p, f x := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : p x
  · rw [if_pos h]
  · rw [if_neg h, hzero x h]

/-- **The cut-off ladder's Hilbert–Schmidt condition, with the cut-off mass as the constant.**  Off
the box every entry vanishes; on the box the mass is the finite sum `∑_{m,n} ‖K m n‖²` reindexed by
the injective `boxEmbed`.  Hence the constant is the mass itself — no bound on it is used here, so
`magCutoffKernel_hs_mass` and this lemma together give the `Λ`-dependent constant of §7 as the exact
value rather than an estimate. -/
theorem boxKernel_hs_finset (Λ : ℕ) (A : Fin d → ℝ) (s : Finset (Idx d)) :
    ∑ m ∈ s, ∑ n ∈ s, ‖boxKernel Λ A m n‖ ^ 2
      ≤ ∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2 := by
  classical
  set B : Finset (Idx d) := Finset.univ.image (boxEmbed (Λ := Λ) (d := d)) with hB
  have hmem : ∀ m : Idx d, InBox (Λ := Λ) m → m ∈ B := by
    intro m h
    obtain ⟨n, rfl⟩ := exists_boxEmbed h
    exact Finset.mem_image_of_mem _ (Finset.mem_univ n)
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin d → Fin Λ)), ∀ y ∈ Finset.univ,
      boxEmbed (Λ := Λ) (d := d) x = boxEmbed y → x = y :=
    fun x _ y _ h => boxEmbed_injective h
  have himg : ∀ G : Idx d → ℝ,
      ∑ m ∈ B, G m = ∑ m : Fin d → Fin Λ, G (boxEmbed (d := d) m) := by
    intro G
    rw [hB]
    exact Finset.sum_image hinj
  have hBB : ∑ m ∈ B, ∑ n ∈ B, ‖boxKernel Λ A m n‖ ^ 2
      = ∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2 := by
    rw [himg (fun m => ∑ n ∈ B, ‖boxKernel Λ A m n‖ ^ 2)]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact (himg (fun n => ‖boxKernel Λ A (boxEmbed (d := d) m) n‖ ^ 2)).trans
      (Finset.sum_congr rfl fun n _ => by rw [boxKernel_boxEmbed])
  have hs1 : ∑ m ∈ s, ∑ n ∈ s, ‖boxKernel Λ A m n‖ ^ 2
      = ∑ m ∈ s.filter (InBox (Λ := Λ)), ∑ n ∈ s, ‖boxKernel Λ A m n‖ ^ 2 :=
    sum_eq_sum_filter_of_zero s (InBox (Λ := Λ)) _
      (fun m hm => Finset.sum_eq_zero fun n _ => by
        rw [boxKernel_eq_zero_left Λ A hm]
        simp)
  have hs2 : ∀ m : Idx d, ∑ n ∈ s, ‖boxKernel Λ A m n‖ ^ 2
      = ∑ n ∈ s.filter (InBox (Λ := Λ)), ‖boxKernel Λ A m n‖ ^ 2 := fun m =>
    sum_eq_sum_filter_of_zero s (InBox (Λ := Λ)) _
      (fun n hn => by
        rw [boxKernel_eq_zero_right Λ A hn]
        simp)
  calc ∑ m ∈ s, ∑ n ∈ s, ‖boxKernel Λ A m n‖ ^ 2
      = ∑ m ∈ s.filter (InBox (Λ := Λ)), ∑ n ∈ s.filter (InBox (Λ := Λ)),
          ‖boxKernel Λ A m n‖ ^ 2 := by
        rw [hs1]
        exact Finset.sum_congr rfl fun m _ => hs2 m
    _ ≤ ∑ m ∈ s.filter (InBox (Λ := Λ)), ∑ n ∈ B, ‖boxKernel Λ A m n‖ ^ 2 := by
        refine Finset.sum_le_sum fun m _ => ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
        intro n hn
        exact hmem n (Finset.mem_filter.mp hn).2
    _ ≤ ∑ m ∈ B, ∑ n ∈ B, ‖boxKernel Λ A m n‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => ?_)
        · intro m hm
          exact hmem m (Finset.mem_filter.mp hm).2
        · exact Finset.sum_nonneg fun n _ => by positivity
    _ = ∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2 := hBB

/-- **The cut-off ladder feeds the closed form directly.**  `ladder_closed_domination_sharp` with
the box-extended kernel: the Hilbert–Schmidt constant is the square root of the cut-off mass, so the
`L²` form dominates with ratio `1/2` and shift `½c₂ + √(m_Λ)`.  The only inputs are the diagonal
domination of `μ` by `g` and the field strength `A`; the box, the mass and the finiteness of the
closed form are handled here. -/
theorem ladder_closed_domination_box {Λ : ℕ} {A : Fin d → ℝ} {μ g : Idx d → ℝ} {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁)
    (hdom : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2 ≤ (closedForm g x).toReal) :
    0 < (1 / 2) * c₁ ∧
      ∀ x : L2 d, closedForm g x ≠ ⊤ →
        (1 / 2) * c₁ * (closedForm μ x).toReal
            - ((1 / 2) * c₂
              + Real.sqrt (∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ,
                  ‖magCutoffKernel A m n‖ ^ 2)) * ‖x‖ ^ 2
          ≤ (closedForm g x).toReal + closedKernelForm (boxKernel Λ A) x := by
  refine ladder_closed_domination_sharp (K := boxKernel Λ A)
    (σ := Real.sqrt (∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ,
      ‖magCutoffKernel A m n‖ ^ 2)) hc₁ hdom (Real.sqrt_nonneg _) ?_
  intro s
  have hmass : (Real.sqrt (∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ,
      ‖magCutoffKernel A m n‖ ^ 2)) ^ 2
      = ∑ m : Fin d → Fin Λ, ∑ n : Fin d → Fin Λ, ‖magCutoffKernel A m n‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [hmass]
  exact boxKernel_hs_finset Λ A s

end BookProof.YangMillsFormClosureND
