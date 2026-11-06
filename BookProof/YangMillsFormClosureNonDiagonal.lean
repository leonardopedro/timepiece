import Mathlib
import BookProof.YangMillsFormClosure
import BookProof.YangMillsMagneticQuartic
import BookProof.ChapterSpectralGapStability
import BookProof.Toolbox.ChapterEsaClosureCore
import BookProof.ChapterUnboundedSpectralModel

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
  *constant* is not, so the continuum needs a ratio that is uniform *together with* a shift that is;
* §10 supplies exactly that, at the level of the box: `Sᵢᵉₙ = Aᵢ√(nᵢ+1)e_{raise n i}` has
  `Sᵢ^*Sᵢ = Aᵢ²diag(nᵢ+1)` (the occupation piece, which the reference form carries) and
  `SᵢSᵢ^* ≤ Aᵢ²` (the shift piece, because a raise is injective, `sum_raiseIdx_le`), so
  `‖q_K(x)‖ ≤ ½Q(x) + ½(ΣᵢAᵢ²)‖x‖²` with `Q(x) = Σₙ(Σᵢ(nᵢ+1))‖x n‖²` (`ladder_form_norm_le`,
  `ladder_form_abs_re_le`).  Neither constant contains `Λ`: the sharp uniform bound is `a = 1/2`;
  §11 records the trade-off `(a, b) = (ε/2, ΣAᵢ²/(2ε))` as a Pareto frontier (`amgm_pareto_iff`,
  `amgm_min_shift`), so `1/2` is the unit-weight member rather than a forced ratio;
* §12 turns the bound into what §6 consumes on `L²`: `ladder_closed_domination_sharp` runs the
  Faris–Lavine comparison at `a = 1/2`, and §12.1–12.2 replace the Hilbert–Schmidt shift by the
  *degree* symbol — `Σᵢ(dirWeight i x) = Σₙ(|n| + d)‖x n‖²` (`sum_dirWeight_eq`) — giving
  `‖q_K(x)‖ ≤ a·degree + (Σᵢ(Aᵢ²/(4a) − a))‖x‖²` for every chosen `a ∈ (0,1)`
  (`ladder_form_le_degree`), transferred to the closed form as
  `abs_closedKernelForm_boxKernel_le` and `closed_farisLavine_boxKernel`;
  `closed_farisLavine_boxKernel_half` is the unit-weight member at the closed-form level: ratio
  `1/2` and shift `max ((ΣᵢAᵢ²)/2 − d/2) 0`, the same numbers at every `Λ`.  **This is the
  cut-off-uniform relative form bound**: `a(Λ) = 1/2` is one number below `1`, not a family indexed
  by the cut-off, and the shift is a function of the field strength alone;
* §9 instantiates the finiteness hypothesis with the concrete magnetic symbol of
  `YangMillsMagneticQuartic` (`magSymbol`, `magnetic_closed_dom_of_scaled`), and
  `closed_dom_of_scaled_symbol_auto` shows that for a positive ratio the hypothesis is a
  consequence of the symbol comparison rather than an assumption;
* §13 supplies the **operator** the cut-off forms define.  `diagCLM c hM` is multiplication by a
  bounded real symbol on `L²`, self-adjoint (`diagCLM_isSelfAdjoint`), and its quadratic form is
  the closed form (`re_inner_diagCLM`); on a cut-off `s` the symbol is supported on `s` and the
  form is exactly `diagonalForm c (truncate x s)` (`re_inner_diagCLM_cutoff`) — for a *bounded*
  symbol the form is closed as it stands, so its Friedrichs extension is the operator itself, with
  no domain restriction.  `gapAt_diagCLM_of_symbol_separation` is the minimax separation: a symbol
  that is `l` or at least `l + c₁Δ` pointwise gives `GapAt A (l + c₁Δ/2) (c₁Δ/2)`, the analytic
  constant of `softmodes.md` §5.2, obtained without a spectrum computation because the Rayleigh
  quotients of a diagonal operator *are* the symbol values.  `gapAt_cutoff_uniform` and
  `cutoff_operator_uniform_gap` package the cut-off family: self-adjoint, gapped by `c₁Δ/2` at
  `c₁Δ/2`, with no cut-off in either constant.  `cutoff_operator_interacting` is the Faris–Lavine
  step in the bounded mode — adding a bounded self-adjoint interaction keeps self-adjointness and
  costs exactly `‖K‖` of the gap.  The unbounded form sum is *not* covered at the level of a
  relative bound below one: §6 gives the certificate, and §21 turns only a *bounded* symmetric
  perturbation into a self-adjoint form sum;
* §14 takes the cut-off family to its limit.  The family does **not** converge in operator norm
  (the symbol changes on an ever larger box), so the mode is strong convergence: `coordBox` is a
  monotone cofinal family of finite boxes, `tendsto_tail_coordBox` says the cut-off tail of a state
  vanishes, `tendsto_diagCLM_cutoff` assembles the strong limit, and `gapAt_of_strong_tendsto`
  transfers the gap because a lower bound on every approximant passes to a limit of norms.  Hence
  `gapAt_cutoffLimit` and `notMem_spectrum_cutoffLimit`: the constant `c₁Δ/2` of §5.2 is the gap of
  the limit operator, not only of its truncations;
* §15 removes the global bound §13 needed: `cutoffBound` (a sum of absolute values on the box)
  bounds a cut-off of an *unbounded* symbol, so `re_inner_diagCLM_cutoffSymbol` identifies the
  operator form of the §12.2 degree symbol with `diagonalForm closedDegreeSymbol (truncate x s)`,
  `gapAt_cutoffSymbol` repeats the minimax separation on such a box, and
  `gapAt_cutoffDegreeSymbol` reads it for the degree symbol itself (`≥ d` everywhere, gap `d/2`);
* §16 is Kato–Rellich at a relative bound below one: `katoRellich_gap` takes an operator bound
  `‖K x‖ ≤ a‖A x‖ + b‖x‖` with `a < 1` and returns self-adjointness plus a gap of
  `(1 − a)dd − (a|lam| + b)`, and  `cutoffLimit_interacting` applies it to §14's limit.  The
  unbounded form-sum version is **not** proved at a relative bound below one — §21 covers the
  bounded-perturbation (`a = 0`) case — see §16's note;
* §17 is the operator the cut-offs are cut-offs *of*: multiplication by the **unbounded** symbol on
  `memDom c x = Summable (‖c n · x n‖²)`.  It is symmetric on that domain (`diagUnb_symmetric`), and
  its resolvent `diagRes` is a bounded operator with `‖diagRes ξ‖ ≤ δ⁻¹‖ξ‖` whenever the symbol
  keeps the distance `δ` from `lam` — this is why the unbounded case is tractable at all.  Both
  inverse identities hold (`diagUnb_diagRes`, `diagRes_left`), so `gapAt_diagUnb` gives the gap on
  the domain,
  and `gapAt_diagUnb_degree` reads it for the §12.2 degree symbol at `d/2`.  §17 itself claims no
  self-adjointness — the domain there is a predicate with two inverse identities — but §19 proves
  it, so the operator does have an adjoint and a spectrum;
* §18 discharges §5.2's hypothesis *literally*.  The approximating resolvents are the
  reciprocal-symbol operators `diagRes`, bounded by `‖ξ‖/δ` (`norm_diagRes_le'`), and they converge
  pointwise to the limit resolvent (`tendsto_diagRes_cutoff`) because the symbols agree on the box
  and are both bounded off it — the same tail argument as §14, now on `‖ξ n‖²`.  With the limit's
  left inverse (`diagRes_left_bounded`), `gapAt_cutoffLimit_resolvent` and
  `notMem_spectrum_cutoffLimit_resolvent` are `gapAt_of_strongResolvent_limit` with **every input
  supplied**, and `tendsto_diagRes_cutoff_degree` gives the same convergence for the degree
  cut-offs, whose limit is §17's unbounded resolvent;
* §19 settles the self-adjointness §17 left open, by **Faris–Lavine**
  (`essentiallySelfAdjointOn_of_farisLavine`) rather than by a Friedrichs form: the criterion needs
  a positive `N` on the same domain and a commutator bound, no closability or semiboundedness of a
  form.  Taking `N` to be the operator itself is exactly right because the symbol is real — the
  commutator form vanishes (`commForm_diagSubLin_self`), so the bound holds with constant `0` — and
  what remains are the paper's two hypotheses: positivity of the form
  (`quadForm_diagSubLin_nonneg`, which is where the symbol is assumed nonnegative) and `T + 1` onto
  (`diagSubLin_surj_one`, the resolvent at `−1` in disguise).  `diagUnb_esa` is the conclusion,
  `dense_diagSub` the density the extension theory needs, and
  `exists_selfAdjoint_extension_diagUnb` the operator itself: a self-adjoint extension on a domain
  containing `diagSub c` and agreeing with `diagUnb` there.
  `exists_selfAdjoint_extension_degree` reads it for the degree symbol;
* §20 does not need the extension: the diagonal operator is self-adjoint on its **maximal**
  domain.  Testing the representing identity of the adjoint domain against coordinate vectors gives
  `c n · φ n = η n`, so the adjoint domain is contained in `diagSub c`
  (`memDom_of_mem_adjointDomain`), and symmetry gives the other inclusion
  (`adjointDomain_diagSubLin`): `IsSelfAdjointOn (diagSub c) (diagSubLin c)`, and the bundled
  operator `diagUnbSelfAdjoint` is an `UnboundedSelfAdjoint`.  That bundle is the input of the
  workspace's unbounded spectral theorem
  (`BookProof.ChapterUnboundedSpectralModel.unbounded_multiplication_model_general`, Cayley route),
  applied as `diagUnb_multiplication_model`.  The spectrum itself is then elementary and exact:
  `InResolventSet c lam` means bounded two-sided invertibility of `T − lam`, and
  `inResolventSet_iff_exists_gap` shows it is equivalent to a positive distance between `lam` and
  the symbol's range — `δ`-separation gives `diagRes`, and conversely `1 = ‖single n 1‖` bounds
  `‖R‖ · |c n − lam|` from below.  Hence `notMem_inResolventSet_iff` (the `∀ δ > 0` criterion) and
  `closure_range_eq_compl_resolvent`: **the spectrum is the closure of the symbol's range**, for the
  operator itself rather than for a chosen extension;
* §21 supplies the **form→operator** direction that §5–§6 recorded as missing.  For a bounded
  symmetric perturbation `K` the sum form `q_c + q_K` is the quadratic form of `T + K` on the
  maximal domain: `diagSumLin_isSelfAdjointOn` proves self-adjointness by moving `K` across the
  inner product and reusing §20's adjoint-domain computation
  (`memDom_of_mem_adjointDomain_sum`), `re_inner_diagSum` is the form identity, `formDom` is the
  sign-free form domain `∑ |c n| ‖x n‖² < ∞` containing the operator domain
  (`memDom_subset_formDom`) and dense (`dense_formDom`), and `formSum_ge` reads the lower bound
  `θ − σ`.  What §21 does not do is the `a < 1` branch of Kato–Rellich at form level, which needs
  the operator relative bound rather than a bounded perturbation;
* §22 identifies the **Yang–Mills one-particle operator**.  The form of record is diagonal
  (`yangMillsForm_eq_diagonalForm`), so it has an explicit symbol
  `yangMillsSymbol T g n = N(n) + N(n)² + rootCount T · zeroPoint g (parallelDegree T n)`, and
  `yangMillsSymbol_form_eq_inner` / `yangMillsForm_closedForm_core` say that the closed form of
  that symbol *is* `q_W` on the Gauss–polynomial core and is the quadratic form of
  `diagUnb (yangMillsSymbol T g)` on the operator domain.  The operator is therefore the diagonal
  one, not an abstract `T` that the form only dominates, and §20 gives its spectrum:
  `yangMills_spectrum_subset` puts the vacuum energy `rootCount T · g/(2√2)` in the spectrum and
  the whole spectrum in `{B} ∪ [B + 2, ∞)` (`yangMills_vacuum_mem_spectrum`,
  `yangMills_gap_mem_spectrum`), so the gap above the vacuum is exactly `2` — the barrier shifts
  the spectrum without changing its spacing.

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
of the closed forms, and that hypothesis is itself derived from a symbolwise inequality.

What is settled and what is not, in one place.  **Settled:** the relative form bound is uniform in
the cut-off — §10's sharp bound and §12.1–12.2's degree-symbol transfer give ratio `a` chosen in
`(0,1)` (the sharp member is `a = 1/2`) and shift `max (Σᵢ(Aᵢ²/(4a) − a)) 0` / 
`max ((ΣᵢAᵢ²)/2 − d/2) 0`, neither mentioning `Λ`; `closed_farisLavine_boxKernel_half` states the
unit-weight case, and `BookProof.YangMillsFormKLMN` §23 turns the resulting form sum into a
self-adjoint operator (KLMN, `formDom` invariance, lower bound `(1 − a)θ − β`, `klmn`).  **Not
settled:** the identification of the box ladder `magCutoffKernel`/`boxKernel` with the reduced or
momentum-representation magnetic operator.  So the continuum does not lack a uniform `a < 1`
relative bound; it lacks the proof that this ladder *is* the magnetic operator of the theory.

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
* **the constant is not** — *if* the ladder is read as a bounded perturbation.  The price is the
  shift `σ(Λ)`, and §7 shows it grows like a power of the cut-off.  But that is an artefact of the
  reading: §10's AM–GM pays the ladder in `Q`, not in `‖x‖²`, and §12.1–12.2 transfer the result to
  the closed form with the *degree* symbol as reference, where the shift is
  `(Σᵢ Aᵢ²/(4a) − a)` — a function of the field strength, independent of `Λ`.  So the `a < 1`
  Faris–Lavine inequality with a cut-off-free constant **is** proved, at `a = 1/2`
  (`closed_farisLavine_boxKernel_half`); what §8's negative half shows is only that the
  Hilbert–Schmidt route cannot produce it.

So the honest summary is: `a(Λ) < 1` holds non-trivially — same ratio, same shift, every cut-off
(§10, §12.2) — and the `σ(Λ)` growth of §7 is the price of the *bounded-perturbation* reading that
the form bound replaces.

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

/-! ## 11.2 The global constant on the form domain: the directional decomposition

§11 isolated the frontier of the *weight*, and the two-mode section showed that the termwise shift
is not the sharp constant on a section.  `softmodes.md` records what that leaves open as "the top
of the full spectral problem on `Q(N^{1/2})`-type domains".  The top of that problem splits, and
the split is the content of this section.

The ladder form is a sum over directions,
`q(x) = ∑ᵢ qᵢ(x)`, `qᵢ(x) = ∑ₙ Aᵢ√(nᵢ+1) · conj(x (n+eᵢ)) · x n`,

and so is its reference form, `Q(x) = ∑ᵢ Qᵢ(x)`, `Qᵢ(x) = ∑ₙ (nᵢ+1)‖x n‖²`.  Each `qᵢ` involves
*only* the `i`-th occupation: the other coordinates merely slice it.  Consequently:

* **`ladder_form_le_of_directional`** — a family of directional bounds
  `‖qᵢ(x)‖ ≤ a Qᵢ(x) + Sᵢ‖x‖²` implies the bound `a Q(x) + (∑ᵢ Sᵢ)‖x‖²` on the whole ladder.  The
  **global constant is at most the sum of the directional constants**, and a better global constant
  can only come from a better *one-dimensional* constant — never from the coupling of directions.
* **`ladderDirForm_norm_le`** — the termwise family `Sᵢ = Aᵢ²/(4a)` is admissible, so the AM–GM
  bound of §10 *is* this composition at the termwise point, and `∑ᵢ Aᵢ²/(4a)` is its shift.
* **`twoModeShift_le_of_twoModeBound`** — no admissible directional constant lies below the
  two-mode optimum: the kernel vector of `twoModeRatio_shift` sits in the directional problem.
  With `A = Aᵢ/2` and `d = 1` this is the ladder's own two-mode state `δ_n, δ_{n+eᵢ}` at `n = 0`
  (`Qᵢ = α² + 2β²`, form `Aᵢαβ`), and `twoModeShift_lt_termwise` says the bound is strict.

So the directional constant is sandwiched, for every `d`,
`twoModeShift (Aᵢ/2) a 1 ≤ Sᵢ < Aᵢ²/(4a)`,

and the one-dimensional number in the middle of that bracket is computed in §11.3: on the ray it is
`Aᵢ²/(4a) − a`, and it is sharp (`rayForm_le_sharp`, `ray_form_bound_iff`).  So the upper end
improves to `Sᵢ ≤ Aᵢ²/(4a) − a`, one mass unit below the termwise constant of §11.1; §11.4 performs
the transfer by reindexing each raised edge to its head. -/

/-- The `i`-th directional part of the ladder form: the summand that raises the `i`-th occupation.
The ladder form is the sum of these over `i` (`ladder_form_eq_sum_dir`). -/
def ladderDirForm {Λ : ℕ} (A : Fin d → ℝ) (i : Fin d) (x : (Fin d → Fin Λ) → ℂ) : ℂ :=
  ∑ n, if h : (n i).val + 1 < Λ then
    ((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)
      * ((starRingEnd ℂ) (x (Function.update n i ⟨(n i).val + 1, h⟩)) * x n) else 0

/-- The directional occupation form `Qᵢ(x) = ∑ₙ (nᵢ+1)‖x n‖²`, the reference form the `i`-th
directional part is compared with. -/
noncomputable def dirWeight {Λ : ℕ} (i : Fin d) (x : (Fin d → Fin Λ) → ℂ) : ℝ :=
  ∑ n, ((n i).val + 1 : ℝ) * ‖x n‖ ^ 2

/-- **The ladder form is the sum of its directional parts.**  Raising the `i`-th occupation is one
summand per direction, so the double sum over `(n, i)` is a sum over directions. -/
theorem ladder_form_eq_sum_dir {Λ : ℕ} (A : Fin d → ℝ) (x : (Fin d → Fin Λ) → ℂ) :
    (∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n)
      = ∑ i, ladderDirForm A i x := by
  rw [ladder_form_eq_sum, Finset.sum_comm]
  rfl

/-- **The directional AM–GM bound**: the termwise family `Sᵢ = Aᵢ²/(4a)` is an admissible
directional constant, by the same shift-and-reindex argument as §10 restricted to one direction. -/
theorem ladderDirForm_norm_le {Λ : ℕ} (A : Fin d → ℝ) (i : Fin d) {a : ℝ} (ha : 0 < a)
    (x : (Fin d → Fin Λ) → ℂ) :
    ‖ladderDirForm A i x‖
      ≤ a * dirWeight i x + (A i ^ 2 / (4 * a)) * (∑ n, ‖x n‖ ^ 2) := by
  classical
  have hterm : ∀ n : Fin d → Fin Λ,
      ‖(if h : (n i).val + 1 < Λ then
          ((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)
            * ((starRingEnd ℂ) (x (Function.update n i ⟨(n i).val + 1, h⟩)) * x n) else 0)‖
        ≤ (if h : (n i).val + 1 < Λ then a * (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2) else 0)
          + (if h : (n i).val + 1 < Λ then
              (A i ^ 2 / (4 * a)) * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2 else 0) := by
    intro n
    by_cases h : (n i).val + 1 < Λ
    · rw [dif_pos h, dif_pos h, dif_pos h]
      have hc : ‖((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)‖
          = |A i| * Real.sqrt ((n i).val + 1) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [norm_mul, norm_mul, Complex.norm_conj, hc]
      have hprod : 2 * (|A i| * Real.sqrt ((n i).val + 1)
            * (‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ * ‖x n‖))
          ≤ 2 * a * (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2)
            + 2 * ((A i ^ 2 / (4 * a))
                * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2) := by
        have ham := amgm_weight_family (ε := 2 * a) (by positivity)
          (Real.sqrt ((n i).val + 1) * ‖x n‖)
          (|A i| * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖)
        have hsq : Real.sqrt ((n i).val + 1) ^ 2 = ((n i).val + 1 : ℝ) :=
          Real.sq_sqrt (by positivity)
        have hsq2 : (Real.sqrt ((n i).val + 1) * ‖x n‖) ^ 2
            = ((n i).val + 1 : ℝ) * ‖x n‖ ^ 2 := by
          rw [mul_pow, hsq]
        have hrew : (|A i| * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖) ^ 2 / (2 * a)
            = 2 * ((A i ^ 2 / (4 * a))
                * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2) := by
          field_simp
          rw [sq_abs]
          ring
        calc 2 * (|A i| * Real.sqrt ((n i).val + 1)
              * (‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ * ‖x n‖))
            = 2 * (Real.sqrt ((n i).val + 1) * ‖x n‖)
                * (|A i| * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖) := by ring
          _ ≤ 2 * a * (Real.sqrt ((n i).val + 1) * ‖x n‖) ^ 2
                + (|A i| * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖) ^ 2 / (2 * a) := ham
          _ = 2 * a * (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2)
                + 2 * ((A i ^ 2 / (4 * a))
                    * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2) := by
            rw [hsq2, hrew]
      linarith
    · rw [dif_neg h, dif_neg h, dif_neg h, norm_zero]
      positivity
  have hshift : ∑ n, (if h : (n i).val + 1 < Λ then
        ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2 else 0) ≤ ∑ n, ‖x n‖ ^ 2 := by
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
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun n _ => hterm n).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ n, (if h : (n i).val + 1 < Λ then
        a * (((n i).val + 1 : ℝ) * ‖x n‖ ^ 2) else 0) ≤ a * dirWeight i x := by
    rw [dirWeight, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases h : (n i).val + 1 < Λ
    · rw [dif_pos h]
    · rw [dif_neg h]
      positivity
  have h2 : ∑ n, (if h : (n i).val + 1 < Λ then
        (A i ^ 2 / (4 * a)) * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2 else 0)
      ≤ (A i ^ 2 / (4 * a)) * (∑ n, ‖x n‖ ^ 2) := by
    have hfac : ∀ n : Fin d → Fin Λ,
        (if h : (n i).val + 1 < Λ then
            (A i ^ 2 / (4 * a)) * ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2 else 0)
          = (A i ^ 2 / (4 * a)) * (if h : (n i).val + 1 < Λ then
              ‖x (Function.update n i ⟨(n i).val + 1, h⟩)‖ ^ 2 else 0) := by
      intro n
      by_cases h : (n i).val + 1 < Λ
      · rw [dif_pos h, dif_pos h]
      · rw [dif_neg h, dif_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun n _ => hfac n, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hshift (by positivity)
  linarith

/-- **The global constant is at most the sum of the directional constants.**  If every directional
part satisfies its own bound `‖qᵢ‖ ≤ a Qᵢ + Sᵢ‖·‖²`, then the ladder satisfies
`‖q‖ ≤ a Q + (∑ᵢ Sᵢ)‖·‖²`.  So the multidirectional spectral problem — the "global constant on
`Q(N^{1/2})`" — decomposes into one one-dimensional problem per direction, and no improvement can
come from the coupling of directions. -/
theorem ladder_form_le_of_directional {Λ : ℕ} (A : Fin d → ℝ) {a : ℝ} {S : Fin d → ℝ}
    (hS : ∀ i : Fin d, ∀ x : (Fin d → Fin Λ) → ℂ,
      ‖ladderDirForm A i x‖ ≤ a * dirWeight i x + S i * (∑ n, ‖x n‖ ^ 2))
    (x : (Fin d → Fin Λ) → ℂ) :
    ‖∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n‖
      ≤ a * (∑ n, (∑ i, ((n i).val + 1 : ℝ)) * ‖x n‖ ^ 2)
        + (∑ i, S i) * (∑ n, ‖x n‖ ^ 2) := by
  have hQ : ∑ i : Fin d, dirWeight i x
      = ∑ n, (∑ i, ((n i).val + 1 : ℝ)) * ‖x n‖ ^ 2 := by
    unfold dirWeight
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n _ => (Finset.sum_mul ..).symm
  have hsum : ∑ i : Fin d, (a * dirWeight i x + S i * (∑ n, ‖x n‖ ^ 2))
      = a * (∑ n, (∑ i, ((n i).val + 1 : ℝ)) * ‖x n‖ ^ 2)
        + (∑ i, S i) * (∑ n, ‖x n‖ ^ 2) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.mul_sum, hQ]
    · rw [Finset.sum_mul]
  rw [ladder_form_eq_sum_dir]
  refine (norm_sum_le _ _).trans ?_
  exact (Finset.sum_le_sum fun i _ => hS i x).trans (le_of_eq hsum)

/-- **No admissible directional constant is below the two-mode optimum.**  If the two-mode
directional form `2Aαβ` is bounded by `a(α² + 2β²) + S(α² + β²)` for every amplitude pair, then
`twoModeShift A a 1 ≤ S`: evaluate at the kernel vector `(A, a + γ)` that attains the two-mode
optimum (`twoModeRatio_shift`).  With `A = Aᵢ/2` and `d = 1` this is the ladder's own two-mode
state, so the directional constant is bounded below by the two-mode optimum and above by the
termwise `Aᵢ²/(4a)` — strictly, by `twoModeShift_lt_termwise`. -/
theorem twoModeShift_le_of_twoModeBound {A a S : ℝ} (hA : A ≠ 0)
    (h : ∀ α β : ℝ, 0 < α ^ 2 + β ^ 2 →
      2 * A * α * β ≤ a * (α ^ 2 + 2 * β ^ 2) + S * (α ^ 2 + β ^ 2)) :
    twoModeShift A a 1 ≤ S := by
  have hq : 0 < A ^ 2 := by
    rcases lt_or_gt_of_ne hA with hlt | hgt
    · nlinarith
    · nlinarith
  have hnorm : 0 < A ^ 2 + (a + twoModeShift A a 1) ^ 2 := by
    linarith [sq_nonneg (a + twoModeShift A a 1)]
  have hb := h A (a + twoModeShift A a 1) hnorm
  have hratio : twoModeRatio A a 1 A (a + twoModeShift A a 1) = twoModeShift A a 1 := by
    simpa using twoModeRatio_shift (A := A) (a := a) (d := 1) hA
  rw [twoModeRatio, div_eq_iff hnorm.ne'] at hratio
  have hexp : 2 * A * A * (a + twoModeShift A a 1)
      - a * ((1 : ℕ) * A ^ 2 + ((1 : ℕ) + 1) * (a + twoModeShift A a 1) ^ 2)
        = 2 * A * A * (a + twoModeShift A a 1)
          - a * (A ^ 2 + 2 * (a + twoModeShift A a 1) ^ 2) := by norm_num
  rw [hexp] at hratio
  have hle : twoModeShift A a 1 * (A ^ 2 + (a + twoModeShift A a 1) ^ 2)
      ≤ S * (A ^ 2 + (a + twoModeShift A a 1) ^ 2) := by linarith [hb, hratio]
  by_contra hcon
  push_neg at hcon
  have hlt : S * (A ^ 2 + (a + twoModeShift A a 1) ^ 2)
      < twoModeShift A a 1 * (A ^ 2 + (a + twoModeShift A a 1) ^ 2) :=
    mul_lt_mul_of_pos_right hcon hnorm
  linarith

/-! ## 11.3 The one-dimensional ray: the sharp constant is `B²/(4a) − a`

§11.2 reduces the constant of the ladder to one number per direction: the top of the ray
`√(m+1) u_{m+1} u_m` against `a (m+1) u_m²`.  That number is computed here, and it is *not* the
termwise `B²/(4a)` of §11.1 — it is `B²/(4a) − a`.

The whole content is one sum of squares.  With `α = B/(2a)`,

`0 ≤ Σ_{m<N} (√(m+1) u_{m+1} − α u_m)² = (Q − ‖u‖²) − F/a + α² Σ_{m<N} u_m²`,

where `Q = Σ_{m≤N}(m+1)u_m²`, `F = Σ_{m<N} B √(m+1) u_{m+1}u_m` and `‖u‖² = Σ_{m≤N}u_m²`; the
shift `m ↦ m+1` in the occupation sum is `ray_sos`.  Since `Σ_{m<N}u_m² ≤ ‖u‖²`, this gives
`F ≤ a Q + (B²/(4a) − a)‖u‖²`.  The `−a` is the zero-point energy of the mode: the shift `α`
removes one mass unit from the occupation form, and `a` is exactly what one mass unit costs.

The constant is sharp.  The extremal family is the Poisson (coherent) vector `u_m = α^m/√(m!)`:
its truncations satisfy the recurrence `√(m+1)u_{m+1} = α u_m` at every term, so the sum of squares
vanishes identically, and the only uncovered piece is `(B²/(4a)) u_N²` at the cut-off, which is
`o(‖u‖²)`.  So no smaller constant is admissible (`ray_form_bound_iff`). -/

/-- Shifting a range sum by one: the raised sight of `Σ_{m<N} f(m+1)` is the full sum minus the
`m = 0` term. -/
theorem sum_range_succ_shift (f : ℕ → ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range N, f (m + 1)) = (∑ m ∈ Finset.range (N + 1), f m) - f 0 := by
  rw [Finset.sum_range_succ']
  ring

/-- The ray form `F(u) = Σ_{m<N} B √(m+1) u_{m+1} u_m`, the one-dimensional problem of §11.2. -/
noncomputable def rayForm (B : ℝ) (N : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range N, B * Real.sqrt ((m : ℝ) + 1) * u (m + 1) * u m

/-- The ray's occupation form `Q(u) = Σ_{m≤N} (m+1) u_m²`, the ray part of `dirWeight`. -/
noncomputable def rayWeight (N : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * u m ^ 2

/-- The ray's mass `‖u‖² = Σ_{m≤N} u_m²`. -/
noncomputable def rayMass (N : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (N + 1), u m ^ 2

/-- The occupation form is the mass plus the shifted mass. -/
theorem rayWeight_sub_rayMass (N : ℕ) (u : ℕ → ℝ) :
    rayWeight N u - rayMass N u = ∑ m ∈ Finset.range (N + 1), (m : ℝ) * u m ^ 2 := by
  rw [rayWeight, rayMass, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- **The sum of squares behind the ray constant, expanded.**  Expanding
`(√(m+1) u_{m+1} − α u_m)²` and summing, the occupation sum shifts down by exactly one mass unit. -/
theorem ray_sos {B a α : ℝ} (h2α : 2 * α = B / a) (N : ℕ) (u : ℕ → ℝ) :
    (∑ m ∈ Finset.range N,
        (Real.sqrt ((m : ℝ) + 1) * u (m + 1) - α * u m) ^ 2)
      = (rayWeight N u - rayMass N u) - (1 / a) * rayForm B N u
        + α ^ 2 * (∑ m ∈ Finset.range N, u m ^ 2) := by
  classical
  have hsq : ∀ m : ℕ, Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 :=
    fun m => Real.sq_sqrt (by positivity)
  have hterm : ∀ m ∈ Finset.range N,
      (Real.sqrt ((m : ℝ) + 1) * u (m + 1) - α * u m) ^ 2
        = ((m : ℝ) + 1) * u (m + 1) ^ 2
          - 2 * α * (Real.sqrt ((m : ℝ) + 1) * u (m + 1) * u m)
          + α ^ 2 * u m ^ 2 := by
    intro m _
    nlinarith [hsq m]
  have hshift : (∑ m ∈ Finset.range N, ((m : ℝ) + 1) * u (m + 1) ^ 2)
      = ∑ m ∈ Finset.range (N + 1), (m : ℝ) * u m ^ 2 := by
    have h := sum_range_succ_shift (fun m : ℕ => (m : ℝ) * u m ^ 2) N
    rw [Nat.cast_zero, zero_mul, sub_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring
  have hcross : (∑ m ∈ Finset.range N,
        2 * α * (Real.sqrt ((m : ℝ) + 1) * u (m + 1) * u m))
      = 2 * α * (∑ m ∈ Finset.range N,
          Real.sqrt ((m : ℝ) + 1) * u (m + 1) * u m) := by
    rw [Finset.mul_sum]
  have hray : rayForm B N u
      = B * (∑ m ∈ Finset.range N, Real.sqrt ((m : ℝ) + 1) * u (m + 1) * u m) := by
    rw [rayForm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hthird : (∑ m ∈ Finset.range N, α ^ 2 * u m ^ 2)
      = α ^ 2 * (∑ m ∈ Finset.range N, u m ^ 2) := by
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, hshift, hcross,
    hthird, rayWeight_sub_rayMass, hray]
  have hcoef : (1 / a) * B = 2 * α := by rw [h2α]; ring
  rw [show (1 / a) * (B * ∑ m ∈ Finset.range N,
        Real.sqrt ((m : ℝ) + 1) * u (m + 1) * u m)
      = (2 * α) * ∑ m ∈ Finset.range N,
        Real.sqrt ((m : ℝ) + 1) * u (m + 1) * u m from by rw [← hcoef]; ring]

/-- **The sharp ray bound.**  `F ≤ a Q + (B²/(4a) − a) ‖u‖²`: the termwise `B²/(4a)` improved by
the one mass unit that the shift `α = B/(2a)` removes. -/
theorem rayForm_le_sharp {B : ℝ} (hB : 0 ≤ B) {a : ℝ} (ha : 0 < a) (N : ℕ) (u : ℕ → ℝ) :
    rayForm B N u ≤ a * rayWeight N u + (B ^ 2 / (4 * a) - a) * rayMass N u := by
  classical
  have hmass : (∑ m ∈ Finset.range N, u m ^ 2) ≤ rayMass N u := by
    rw [rayMass]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ N))
      (fun m _ _ => sq_nonneg (u m))
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · subst hB0
    have hz : rayForm 0 N u = 0 := by simp [rayForm]
    have hQW : rayMass N u ≤ rayWeight N u := by
      rw [rayMass, rayWeight]
      refine Finset.sum_le_sum fun m _ => ?_
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith [sq_nonneg (u m)]
    have hc0 : (0 : ℝ) ^ 2 / (4 * a) - a = -a := by
      rw [zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_sub]
    rw [hz, hc0]
    have hprod : 0 ≤ a * (rayWeight N u - rayMass N u) :=
      mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hQW)
    nlinarith [hprod]
  · set α : ℝ := B / (2 * a) with hα
    have h2α : 2 * α = B / a := by rw [hα]; field_simp
    have hα2 : a * α ^ 2 = B ^ 2 / (4 * a) := by
      rw [hα]
      field_simp
      ring
    have hsos : 0 ≤ (∑ m ∈ Finset.range N,
        (Real.sqrt ((m : ℝ) + 1) * u (m + 1) - α * u m) ^ 2) :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    rw [ray_sos h2α N u] at hsos
    have hT : α ^ 2 * (∑ m ∈ Finset.range N, u m ^ 2) ≤ α ^ 2 * rayMass N u :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg α)
    have h1 : (1 / a) * rayForm B N u
        ≤ (rayWeight N u - rayMass N u) + α ^ 2 * rayMass N u := by
      linarith [hsos, hT]
    have h2 : rayForm B N u
        ≤ a * ((rayWeight N u - rayMass N u) + α ^ 2 * rayMass N u) := by
      have h := mul_le_mul_of_nonneg_left h1 (le_of_lt ha)
      have haa : a * (1 / a) = 1 := by field_simp
      calc rayForm B N u = a * ((1 / a) * rayForm B N u) := by
            rw [← mul_assoc, haa, one_mul]
        _ ≤ a * ((rayWeight N u - rayMass N u) + α ^ 2 * rayMass N u) := h
    have h3 : a * α ^ 2 * rayMass N u = (B ^ 2 / (4 * a)) * rayMass N u := by rw [hα2]
    nlinarith [h2, h3]

/-- **The constant is sharp.**  For every `δ > 0` some finitely supported ray vector beats
`a Q + (B²/(4a) − a − δ) ‖u‖²`: the truncations of the Poisson vector `u_m = α^m/√(m!)` leave
only `(B²/(4a)) u_N²` uncovered, and `u_N²/‖u‖² → 0`. -/
theorem rayForm_sharp {B a δ : ℝ} (hB : 0 < B) (ha : 0 < a) (hδ : 0 < δ) :
    ∃ (N : ℕ) (u : ℕ → ℝ),
      a * rayWeight N u + (B ^ 2 / (4 * a) - a - δ) * rayMass N u < rayForm B N u := by
  classical
  set α : ℝ := B / (2 * a) with hα
  have hα2 : a * α ^ 2 = B ^ 2 / (4 * a) := by
    rw [hα]
    field_simp
    ring
  have hlim : Filter.Tendsto (fun n : ℕ => (α ^ 2) ^ n / (n.factorial : ℝ)) Filter.atTop
      (nhds 0) := FloorSemiring.tendsto_pow_div_factorial_atTop (α ^ 2)
  have hpos : 0 < δ * (4 * a) / B ^ 2 := by positivity
  obtain ⟨N, hN⟩ := hlim.eventually (eventually_lt_nhds hpos) |>.exists
  refine ⟨N, fun m => α ^ m / Real.sqrt (m.factorial : ℝ), ?_⟩
  have hrec : ∀ m : ℕ,
      Real.sqrt ((m : ℝ) + 1) * (α ^ (m + 1) / Real.sqrt (((m + 1).factorial : ℝ)))
        = α * (α ^ m / Real.sqrt ((m.factorial : ℝ))) := by
    intro m
    have hfact : (((m + 1).factorial : ℕ) : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hspos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hfpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    rw [hfact, Real.sqrt_mul (le_of_lt hspos)]
    have hs : Real.sqrt ((m : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hspos)
    have hf : Real.sqrt ((m.factorial : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hfpos)
    field_simp
    ring
  have hzero : (∑ m ∈ Finset.range N,
      (Real.sqrt ((m : ℝ) + 1) * (α ^ (m + 1) / Real.sqrt (((m + 1).factorial : ℝ)))
        - α * (α ^ m / Real.sqrt ((m.factorial : ℝ)))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [hrec m]
    ring
  have hsos_id := ray_sos (B := B) (a := a) (α := α)
    (by rw [hα]; field_simp) N (fun m => α ^ m / Real.sqrt (m.factorial : ℝ))
  rw [hzero] at hsos_id
  -- the truncation misses exactly one mass unit of the occupation form
  have hsplit : rayMass N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))
      = (∑ m ∈ Finset.range N, (α ^ m / Real.sqrt ((m.factorial : ℝ))) ^ 2)
        + (α ^ N / Real.sqrt ((N.factorial : ℝ))) ^ 2 := by
    rw [rayMass, Finset.sum_range_succ]
  have hu0 : (α ^ 0 / Real.sqrt (((0).factorial : ℝ))) ^ 2 = 1 := by
    norm_num
  have hmass1 : 1 ≤ rayMass N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ))) := by
    have h := Finset.single_le_sum (f := fun m : ℕ => (α ^ m / Real.sqrt ((m.factorial : ℝ))) ^ 2)
      (fun m _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.succ_pos N) : 0 ∈ Finset.range (N + 1))
    rw [rayMass]
    simpa [hu0] using h
  have hpowN : (α ^ N / Real.sqrt ((N.factorial : ℝ))) ^ 2 = (α ^ 2) ^ N / (N.factorial : ℝ) := by
    have hfpos : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
    rw [div_pow, ← pow_mul, Real.sq_sqrt (le_of_lt hfpos), Nat.mul_comm N 2, pow_mul]
  have huN : a * α ^ 2 * (α ^ N / Real.sqrt ((N.factorial : ℝ))) ^ 2 < δ := by
    rw [hpowN]
    have hconst : a * α ^ 2 * (δ * (4 * a) / B ^ 2) = δ := by
      rw [hα2]
      field_simp
    nlinarith [hN, hconst, ha, hB]
  have hform : rayForm B N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))
      = a * ((rayWeight N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))
          - rayMass N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ))))
        + α ^ 2 * (∑ m ∈ Finset.range N,
            (α ^ m / Real.sqrt ((m.factorial : ℝ))) ^ 2)) := by
    have h1 : (1 / a) * rayForm B N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))
        = (rayWeight N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))
          - rayMass N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ))))
          + α ^ 2 * (∑ m ∈ Finset.range N,
              (α ^ m / Real.sqrt ((m.factorial : ℝ))) ^ 2) := by
      linarith [hsos_id]
    have haa : a * (1 / a) = 1 := by field_simp
    calc rayForm B N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))
        = a * ((1 / a) * rayForm B N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))) := by
          rw [← mul_assoc, haa, one_mul]
      _ = a * ((rayWeight N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))
            - rayMass N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ))))
          + α ^ 2 * (∑ m ∈ Finset.range N,
              (α ^ m / Real.sqrt ((m.factorial : ℝ))) ^ 2)) := by rw [h1]
  rw [hform]
  have hd : δ * 1 ≤ δ * rayMass N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ))) :=
    mul_le_mul_of_nonneg_left hmass1 (le_of_lt hδ)
  have hMM : (B ^ 2 / (4 * a)) * rayMass N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))
      = a * α ^ 2 * rayMass N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ))) := by rw [hα2]
  have hmul : a * α ^ 2 * rayMass N (fun m => α ^ m / Real.sqrt ((m.factorial : ℝ)))
        - a * α ^ 2 * (∑ m ∈ Finset.range N, (α ^ m / Real.sqrt ((m.factorial : ℝ))) ^ 2)
      = a * α ^ 2 * (α ^ N / Real.sqrt ((N.factorial : ℝ))) ^ 2 := by
    rw [hsplit]
    ring
  linarith [huN, hd, hMM, hmul]

/-- **The sharp constant, as a characterisation**: a constant `S` is admissible for the ray
problem on every truncation exactly when it is at least `B²/(4a) − a`. -/
theorem ray_form_bound_iff {B : ℝ} (hB : 0 < B) {a : ℝ} (ha : 0 < a) {S : ℝ} :
    (∀ (N : ℕ) (u : ℕ → ℝ), rayForm B N u ≤ a * rayWeight N u + S * rayMass N u)
      ↔ B ^ 2 / (4 * a) - a ≤ S := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨N, u, hu⟩ := rayForm_sharp hB ha (δ := B ^ 2 / (4 * a) - a - S) (by linarith)
    have hb := h N u
    have : a * rayWeight N u + (B ^ 2 / (4 * a) - a - (B ^ 2 / (4 * a) - a - S)) * rayMass N u
        = a * rayWeight N u + S * rayMass N u := by ring
    rw [this] at hu
    linarith
  · intro hS N u
    have hb := rayForm_le_sharp (le_of_lt hB) ha N u
    have hnonneg : 0 ≤ rayMass N u := by
      rw [rayMass]
      exact Finset.sum_nonneg fun m _ => sq_nonneg _
    nlinarith [hb, hnonneg]

/-! ## 11.4 The ray decomposition: the directional constant is `Aᵢ²/(4a) − a`

§11.2 proved `‖ladderDirForm A i x‖ ≤ a Qᵢ + (Aᵢ²/(4a))‖x‖²`; §11.3 settled the one-dimensional
ray at `B²/(4a) − a`.  The transfer between the two is a single reindexing.  Fix the direction `i`
and charge each raised edge `n → n + eᵢ` to its *head*: the head's occupation summed over all raised
edges is `Σ_m mᵢ‖x m‖² = Qᵢ − ‖x‖²` (`raiseWeightSum_eq`, `dirWeight_sub_mass`) — the ray identity
`Q − ‖u‖² = Σ m u_m²` read one coordinate at a time.  That missing mass unit is exactly the `a` of
the ray constant, so the directional bound improves to `a Qᵢ + (Aᵢ²/(4a) − a)‖x‖²`
(`ladderDirForm_norm_le_ray`), and summing over directions gives the global constant
`Σᵢ (Aᵢ²/(4a) − a)` (`ladder_form_norm_le_ray`).  The value is sharp because a single ray, with the
other coordinates empty, is a directional state of the box. -/

/-- The raised-edge weight: the occupation of the *head* of every raised edge. -/
noncomputable def raiseWeightSum {Λ : ℕ} (i : Fin d) (x : (Fin d → Fin Λ) → ℂ) : ℝ :=
  ∑ n, (if _h : (n i).val + 1 < Λ then ((n i).val + 1 : ℝ) * ‖x (raiseIdx n i)‖ ^ 2 else 0)

/-- The directional occupation form is the mass plus the heads' occupations. -/
theorem dirWeight_sub_mass {Λ : ℕ} (i : Fin d) (x : (Fin d → Fin Λ) → ℂ) :
    dirWeight i x - ∑ n, ‖x n‖ ^ 2 = ∑ n, ((n i).val : ℝ) * ‖x n‖ ^ 2 := by
  rw [dirWeight, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Lowering a raised head**: if the `i`-th occupation of `b` is at least one, dropping it and
then raising is the identity.  This is the inverse half of the reindexing. -/
theorem update_raise_lower {Λ : ℕ} (b : Fin d → Fin Λ) (i : Fin d) (hb : 1 ≤ (b i).val) :
    raiseIdx (Function.update b i ⟨(b i).val - 1, by omega⟩) i
      = b := by
  classical
  have hni : ((Function.update b i ⟨(b i).val - 1, by omega⟩) i).val
      = (b i).val - 1 := by
    rw [Function.update_apply]
    simp
  have hcond : ((Function.update b i ⟨(b i).val - 1, by omega⟩) i).val + 1 < Λ := by
    rw [hni]
    have := (b i).isLt
    omega
  rw [raiseIdx, dif_pos hcond]
  funext j
  apply Fin.ext
  by_cases hj : j = i
  · subst hj
    rw [Function.update_apply]
    split_ifs with hjj
    · change ((Function.update b j ⟨(b j).val - 1, by omega⟩ j).val + 1 : ℕ) = (b j).val
      rw [hni]
      omega
    · exact absurd rfl hjj
  · simp only [Function.update_apply]
    rw [if_neg hj, if_neg hj]

/-- **The reindexing**: summing the raised edges by their head gives the heads' occupations.  Each
`m` with `mᵢ ≥ 1` is the head of exactly one raised edge, namely the one based at `m − eᵢ`. -/
theorem raiseWeightSum_eq {Λ : ℕ} (i : Fin d) (x : (Fin d → Fin Λ) → ℂ) :
    raiseWeightSum i x = ∑ m, ((m i).val : ℝ) * ‖x m‖ ^ 2 := by
  classical
  have hsum : raiseWeightSum i x
      = ∑ n ∈ Finset.univ.filter (fun n : Fin d → Fin Λ => (n i).val + 1 < Λ),
          ((n i).val + 1 : ℝ) * ‖x (raiseIdx n i)‖ ^ 2 := by
    rw [raiseWeightSum, Finset.sum_filter]
    simp
  have hbij : (∑ n ∈ Finset.univ.filter (fun n : Fin d → Fin Λ => (n i).val + 1 < Λ),
          ((n i).val + 1 : ℝ) * ‖x (raiseIdx n i)‖ ^ 2)
      = ∑ m ∈ Finset.univ.filter (fun m : Fin d → Fin Λ => 1 ≤ (m i).val),
          ((m i).val : ℝ) * ‖x m‖ ^ 2 := by
    refine Finset.sum_bij (fun n _ => raiseIdx n i) ?_ ?_ ?_ ?_
    · intro a ha
      have hcond : (a i).val + 1 < Λ := (Finset.mem_filter.mp ha).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hval : ((raiseIdx a i) i).val = (a i).val + 1 := by
        rw [raiseIdx, dif_pos hcond, Function.update_apply]
        simp
      rw [hval]
      omega
    · intro a₁ ha₁ a₂ ha₂ heq
      have h1 : (a₁ i).val + 1 < Λ := (Finset.mem_filter.mp ha₁).2
      have h2 : (a₂ i).val + 1 < Λ := (Finset.mem_filter.mp ha₂).2
      have heq' : raiseIdx a₁ i = raiseIdx a₂ i := heq
      have hr1 : raiseIdx a₁ i = Function.update a₁ i ⟨(a₁ i).val + 1, h1⟩ := by
        rw [raiseIdx, dif_pos h1]
      have hr2 : raiseIdx a₂ i = Function.update a₂ i ⟨(a₂ i).val + 1, h2⟩ := by
        rw [raiseIdx, dif_pos h2]
      rw [hr1, hr2] at heq'
      exact update_succ_inj h1 h2 heq'
    · intro b hb
      have hb1 : 1 ≤ (b i).val := (Finset.mem_filter.mp hb).2
      refine ⟨Function.update b i ⟨(b i).val - 1, by omega⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hni : ((Function.update b i ⟨(b i).val - 1, by omega⟩) i).val
            = (b i).val - 1 := by
          rw [Function.update_apply]
          simp
        rw [hni]
        omega
      · exact update_raise_lower b i hb1
    · intro a ha
      have hcond : (a i).val + 1 < Λ := (Finset.mem_filter.mp ha).2
      have hval : ((raiseIdx a i) i).val = (a i).val + 1 := by
        rw [raiseIdx, dif_pos hcond, Function.update_apply]
        simp
      rw [hval]
      simp
  rw [hsum, hbij, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : 1 ≤ (m i).val
  · simp [h]
  · have h0 : (m i).val = 0 := by omega
    simp [h0]

/-- **The directional bound with the ray constant**: one mass unit of the occupation form is spent
on the shift, so the directional constant drops from `Aᵢ²/(4a)` to `Aᵢ²/(4a) − a`. -/
theorem ladderDirForm_norm_le_ray {Λ : ℕ} (A : Fin d → ℝ) (i : Fin d) {a : ℝ} (ha : 0 < a)
    (x : (Fin d → Fin Λ) → ℂ) :
    ‖ladderDirForm A i x‖
      ≤ a * dirWeight i x + (A i ^ 2 / (4 * a) - a) * (∑ n, ‖x n‖ ^ 2) := by
  classical
  have hterm : ∀ n : Fin d → Fin Λ,
      ‖(if h : (n i).val + 1 < Λ then
          ((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)
            * ((starRingEnd ℂ) (x (Function.update n i ⟨(n i).val + 1, h⟩)) * x n) else 0)‖
        ≤ a * (if h : (n i).val + 1 < Λ then
              ((n i).val + 1 : ℝ) * ‖x (raiseIdx n i)‖ ^ 2 else 0)
          + (A i ^ 2 / (4 * a)) * (if h : (n i).val + 1 < Λ then ‖x n‖ ^ 2 else 0) := by
    intro n
    by_cases h : (n i).val + 1 < Λ
    · rw [dif_pos h, dif_pos h, dif_pos h]
      have hx : raiseIdx n i = Function.update n i ⟨(n i).val + 1, h⟩ := by
        rw [raiseIdx, dif_pos h]
      rw [← hx, norm_mul, norm_mul, Complex.norm_conj]
      have hc : ‖((A i * Real.sqrt ((n i).val + 1) : ℝ) : ℂ)‖
          = |A i| * Real.sqrt ((n i).val + 1) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [hc]
      have ham := amgm_weight_family (ε := 2 * a) (by positivity)
        (Real.sqrt ((n i).val + 1) * ‖x (raiseIdx n i)‖) (|A i| * ‖x n‖)
      have hsq : Real.sqrt ((n i).val + 1) ^ 2 = ((n i).val + 1 : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hsq2 : (Real.sqrt ((n i).val + 1) * ‖x (raiseIdx n i)‖) ^ 2
          = ((n i).val + 1 : ℝ) * ‖x (raiseIdx n i)‖ ^ 2 := by
        rw [mul_pow, hsq]
      have hrew : (|A i| * ‖x n‖) ^ 2 / (2 * a)
          = 2 * ((A i ^ 2 / (4 * a)) * ‖x n‖ ^ 2) := by
        rw [mul_pow, sq_abs]
        field_simp
        ring
      rw [hsq2, hrew] at ham
      nlinarith [ham]
    · rw [dif_neg h, dif_neg h, dif_neg h, norm_zero]
      positivity
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun n _ => hterm n).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [show (∑ n, (if h : (n i).val + 1 < Λ then
        ((n i).val + 1 : ℝ) * ‖x (raiseIdx n i)‖ ^ 2 else 0)) = raiseWeightSum i x from rfl]
  have hR := raiseWeightSum_eq (i := i) x
  have hD := dirWeight_sub_mass (i := i) x
  have hmass : (∑ n, (if h : (n i).val + 1 < Λ then ‖x n‖ ^ 2 else 0)) ≤ ∑ n, ‖x n‖ ^ 2 := by
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases h : (n i).val + 1 < Λ
    · simp [h]
    · simp only [dif_neg h]
      positivity
  have hc : 0 ≤ A i ^ 2 / (4 * a) := by positivity
  have hmass' : (A i ^ 2 / (4 * a)) * (∑ n, (if h : (n i).val + 1 < Λ then ‖x n‖ ^ 2 else 0))
      ≤ (A i ^ 2 / (4 * a)) * (∑ n, ‖x n‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hmass hc
  have hB : a * raiseWeightSum i x = a * (∑ m, ((m i).val : ℝ) * ‖x m‖ ^ 2) := by rw [hR]
  have hA : a * (dirWeight i x - ∑ n, ‖x n‖ ^ 2)
      = a * (∑ n, ((n i).val : ℝ) * ‖x n‖ ^ 2) := by rw [hD]
  linarith [hB, hA, hmass']

/-- **The global constant with the ray constant per direction**: summing the improved directional
bounds gives `a ∑ᵢ Qᵢ + (∑ᵢ (Aᵢ²/(4a) − a))‖x‖²`. -/
theorem ladder_form_norm_le_ray {Λ : ℕ} (A : Fin d → ℝ) {a : ℝ} (ha : 0 < a)
    (x : (Fin d → Fin Λ) → ℂ) :
    ‖∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n‖
      ≤ a * (∑ i, dirWeight i x)
        + (∑ i, (A i ^ 2 / (4 * a) - a)) * (∑ n, ‖x n‖ ^ 2) := by
  rw [ladder_form_eq_sum_dir]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => ladderDirForm_norm_le_ray A i ha x).trans ?_
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]

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

/-! ## 12.1 The relative bound is uniform in the cut-off

§12's `ladder_closed_domination_box` takes its constant from the Hilbert–Schmidt mass, which grows
like `Λ^{(d+1)/2}`; §11.4's ray decomposition replaces it by the *degree* symbol, and the transfer
is two identities.  `dirWeight` is the mass plus the directional occupation
(`dirWeight_sub_mass`), so the sum of the directional reference forms is
`Σₙ (|n| + d)‖x n‖²` (`sum_dirWeight_eq`) — a derivative form, not a mass.  Hence for every
`a ∈ (0,1)` the ladder is `a · degree + (Σᵢ (Aᵢ²/(4a) − a)) · mass` on the box
(`ladder_form_le_degree`), and **neither constant mentions `Λ`**: the relative bound `a` is
chosen, not measured, so it stays bounded away from `1` as the cut-off grows — which is what §6's
Faris–Lavine comparison needs and what the Hilbert–Schmidt route could not supply, since there
`a = √(m_Λ)/θ` is unbounded in `Λ`.  At `a = 1/2` the shift is `(Σᵢ Aᵢ²)/2 − d/2`
(`ladder_form_le_degree_half`), the cut-off-free form of the constant. -/

/-- The directional reference form is the mass plus the directional occupation. -/
theorem dirWeight_eq {Λ : ℕ} (i : Fin d) (x : (Fin d → Fin Λ) → ℂ) :
    dirWeight i x = (∑ n, ((n i).val : ℝ) * ‖x n‖ ^ 2) + ∑ n, ‖x n‖ ^ 2 := by
  have h := dirWeight_sub_mass (i := i) x
  linarith

/-- **The directional reference forms sum to the degree form**: `Σᵢ Qᵢ(x) = Σₙ (|n| + d)‖x n‖²`,
where `|n| = Σᵢ nᵢ`.  This is why the ray constant is cut-off free: the reference object is the
degree symbol, and the only `Λ`-dependence left is the range of `n` itself. -/
theorem sum_dirWeight_eq {Λ : ℕ} (x : (Fin d → Fin Λ) → ℂ) :
    ∑ i, dirWeight i x
      = ∑ n, (((∑ i, (n i).val : ℕ) : ℝ) + (d : ℝ)) * ‖x n‖ ^ 2 := by
  classical
  have h1 : ∀ n : Fin d → Fin Λ,
      (∑ i, ((n i).val : ℝ) * ‖x n‖ ^ 2) = (((∑ i, (n i).val : ℕ) : ℝ)) * ‖x n‖ ^ 2 := by
    intro n
    rw [← Finset.sum_mul, Nat.cast_sum]
  calc ∑ i, dirWeight i x
      = ∑ i, ((∑ n, ((n i).val : ℝ) * ‖x n‖ ^ 2) + ∑ n, ‖x n‖ ^ 2) :=
        Finset.sum_congr rfl fun i _ => dirWeight_eq i x
    _ = (∑ i, ∑ n, ((n i).val : ℝ) * ‖x n‖ ^ 2) + ∑ _i : Fin d, ∑ n, ‖x n‖ ^ 2 :=
        Finset.sum_add_distrib
    _ = (∑ n, ∑ i, ((n i).val : ℝ) * ‖x n‖ ^ 2) + (d : ℝ) * ∑ n, ‖x n‖ ^ 2 := by
        rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ = (∑ n, (((∑ i, (n i).val : ℕ) : ℝ)) * ‖x n‖ ^ 2) + (d : ℝ) * ∑ n, ‖x n‖ ^ 2 := by
        rw [Finset.sum_congr rfl fun n _ => h1 n]
    _ = ∑ n, ((((∑ i, (n i).val : ℕ) : ℝ)) * ‖x n‖ ^ 2 + (d : ℝ) * ‖x n‖ ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ n, (((∑ i, (n i).val : ℕ) : ℝ) + (d : ℝ)) * ‖x n‖ ^ 2 :=
        Finset.sum_congr rfl fun n _ => by ring

/-- **The cut-off ladder is `a` times the degree form plus a `Λ`-free shift.**  The shift
`Σᵢ (Aᵢ²/(4a) − a)` is a function of the field strength and the chosen relative bound only: no
Hilbert–Schmidt mass, hence no growth in the cut-off. -/
theorem ladder_form_le_degree {Λ : ℕ} (A : Fin d → ℝ) {a : ℝ} (ha : 0 < a)
    (x : (Fin d → Fin Λ) → ℂ) :
    ‖∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n‖
      ≤ a * (∑ n, (((∑ i, (n i).val : ℕ) : ℝ) + (d : ℝ)) * ‖x n‖ ^ 2)
        + (∑ i, (A i ^ 2 / (4 * a) - a)) * (∑ n, ‖x n‖ ^ 2) := by
  simpa only [sum_dirWeight_eq] using ladder_form_norm_le_ray (d := d) A ha x

/-- **The cut-off-free constant at relative bound `a = 1/2`**: the ladder is half the degree form
plus `(Σᵢ Aᵢ²)/2 − d/2`, with no `Λ` in sight.  Since `1/2 < 1`, this is an admissible relative
bound for the Faris–Lavine comparison of §6 at *every* cut-off, which is the uniformity the
continuum argument needs. -/
theorem ladder_form_le_degree_half {Λ : ℕ} (A : Fin d → ℝ) (x : (Fin d → Fin Λ) → ℂ) :
    ‖∑ m, ∑ n, (starRingEnd ℂ) (x m) * magCutoffKernel A m n * x n‖
      ≤ (1 / 2) * (∑ n, (((∑ i, (n i).val : ℕ) : ℝ) + (d : ℝ)) * ‖x n‖ ^ 2)
        + ((∑ i, A i ^ 2) / 2 - (d : ℝ) / 2) * (∑ n, ‖x n‖ ^ 2) := by
  have h := ladder_form_le_degree (d := d) A (a := 1 / 2) (by norm_num) x
  have hterm : ∀ i : Fin d, A i ^ 2 / (4 * (1 / 2)) - 1 / 2 = A i ^ 2 / 2 - 1 / 2 := by
    intro i
    norm_num
  have hc : (∑ i, (A i ^ 2 / (4 * (1 / 2)) - 1 / 2)) = (∑ i, A i ^ 2) / 2 - (d : ℝ) / 2 := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_div,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rwa [hc] at h

/-! ### 12.2 The `L²` transfer: the closed form reads the degree symbol

§12.1 bounds the ladder on the box.  On `L²` the same statement is `closedKernelForm
(boxKernel Λ A)`, a double series over all of `Idx d × Idx d`; because `boxKernel` vanishes off
the box the series is the box series reindexed by the injective `boxEmbed`, and the two sums the
box bound produces — the degree sum and the mass — are dominated by `closedForm degree` and by
`‖x‖²`.  The result keeps the cut-off out entirely: the ratio is the chosen `a` and the shift is
`max (Σᵢ (Aᵢ²/(4a) − a)) 0`, so §6's `closed_farisLavine_domination` can run at a uniform ratio
without a Hilbert–Schmidt mass. -/

/-- The degree symbol on `Idx d`, written with the cast of the sum (the form `degreeForm` uses). -/
noncomputable def closedDegreeSymbol (d : ℕ) : Idx d → ℝ := fun n => (∑ i, (n i : ℝ)) + (d : ℝ)

/-- The degree symbol is nonnegative. -/
theorem closedDegreeSymbol_nonneg (n : Idx d) : 0 ≤ closedDegreeSymbol (d := d) n :=
  add_nonneg (Finset.sum_nonneg fun i _ => by positivity) (by positivity)

/-- **The cut-off ladder's closed form is bounded by the degree form.**  The relative bound `a` and
the shift `max (Σᵢ (Aᵢ²/(4a) − a)) 0` are the cut-off-free constants of §12.1; the only hypothesis
is that the state has finite degree form, which is the form-domain condition of §6. -/
theorem abs_closedKernelForm_boxKernel_le {Λ : ℕ} (A : Fin d → ℝ) {a : ℝ} (ha : 0 < a)
    (x : L2 d) (hfin : closedForm (closedDegreeSymbol (d := d)) x ≠ ⊤) :
    |closedKernelForm (boxKernel Λ A) x|
      ≤ a * (closedForm (closedDegreeSymbol (d := d)) x).toReal
        + max (∑ i, (A i ^ 2 / (4 * a) - a)) 0 * ‖x‖ ^ 2 := by
  classical
  set f : Idx d → ℝ := closedDegreeSymbol (d := d) with hf
  set B : Finset (Idx d) := Finset.univ.image (boxEmbed (Λ := Λ) (d := d)) with hB
  have hmem : ∀ m : Idx d, InBox (Λ := Λ) m → m ∈ B := by
    intro m h
    obtain ⟨n, rfl⟩ := exists_boxEmbed h
    exact Finset.mem_image_of_mem _ (Finset.mem_univ n)
  have hinj : ∀ x₁ ∈ (Finset.univ : Finset (Fin d → Fin Λ)), ∀ y ∈ Finset.univ,
      boxEmbed (Λ := Λ) (d := d) x₁ = boxEmbed y → x₁ = y :=
    fun x₁ _ y _ h => boxEmbed_injective h
  set y : (Fin d → Fin Λ) → ℂ := fun n => x (boxEmbed n) with hy
  -- the series is supported on the box
  have hzero : ∀ p : Idx d × Idx d, p ∉ B ×ˢ B →
      boxKernel Λ A p.1 p.2 * x p.2 * (starRingEnd ℂ) (x p.1) = 0 := by
    intro p hp
    rw [Finset.mem_product, not_and_or] at hp
    rcases hp with h | h
    · have hnb : ¬ InBox (Λ := Λ) p.1 := fun hc => h (hmem p.1 hc)
      rw [boxKernel_eq_zero_left Λ A hnb]
      simp
    · have hnb : ¬ InBox (Λ := Λ) p.2 := fun hc => h (hmem p.2 hc)
      rw [boxKernel_eq_zero_right Λ A hnb]
      simp
  -- reindexed onto the box: the series is the box ladder form
  have hbox : ∀ F : Idx d → Idx d → ℂ, (∑ m ∈ B, ∑ n ∈ B, F m n)
      = ∑ i : Fin d → Fin Λ, ∑ j : Fin d → Fin Λ, F (boxEmbed i) (boxEmbed j) := by
    intro F
    rw [hB, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_image hinj
  have hseries : (∑' p : Idx d × Idx d,
        boxKernel Λ A p.1 p.2 * x p.2 * (starRingEnd ℂ) (x p.1))
      = ∑ i : Fin d → Fin Λ, ∑ j : Fin d → Fin Λ,
          magCutoffKernel A i j * y j * (starRingEnd ℂ) (y i) := by
    rw [tsum_eq_sum hzero, Finset.sum_product,
      hbox (fun m n => boxKernel Λ A m n * x n * (starRingEnd ℂ) (x m))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [boxKernel_boxEmbed]
  -- the mass over the box is at most the norm
  have hHas : HasSum (fun n : Idx d => ‖x n‖ ^ 2) (‖x‖ ^ 2) := by
    have h := lp.hasSum_norm (E := fun _ : Idx d => ℂ) (p := (2 : ℝ≥0∞)) (by norm_num) x
    simpa using h
  have hmass : (∑ n : Fin d → Fin Λ, ‖y n‖ ^ 2) ≤ ‖x‖ ^ 2 := by
    have himg : (∑ m ∈ B, ‖x m‖ ^ 2) = ∑ n : Fin d → Fin Λ, ‖x (boxEmbed n)‖ ^ 2 := by
      rw [hB]
      exact Finset.sum_image hinj
    rw [← himg]
    exact (hHas.summable.sum_le_tsum B fun _ _ => by positivity).trans hHas.tsum_eq.le
  -- the degree sum over the box is at most the closed degree form
  have hdeg : (∑ n : Fin d → Fin Λ, ((∑ i, ((n i).val : ℝ)) + (d : ℝ)) * ‖y n‖ ^ 2)
      ≤ (closedForm f x).toReal := by
    have hBsum : (∑ n : Fin d → Fin Λ, ((∑ i, ((n i).val : ℝ)) + (d : ℝ)) * ‖y n‖ ^ 2)
        = ∑ m ∈ B, f m * ‖x m‖ ^ 2 := by
      have himg : (∑ m ∈ B, f m * ‖x m‖ ^ 2)
          = ∑ n : Fin d → Fin Λ, f (boxEmbed n) * ‖x (boxEmbed n)‖ ^ 2 := by
        rw [hB]
        exact Finset.sum_image hinj
      rw [himg]
      exact Finset.sum_congr rfl fun n _ => rfl
    have hle : ENNReal.ofReal (∑ n : Fin d → Fin Λ,
          ((∑ i, ((n i).val : ℝ)) + (d : ℝ)) * ‖y n‖ ^ 2) ≤ closedForm f x := by
      rw [hBsum, ← diagonalForm_truncate f x B]
      have h1 : ENNReal.ofReal (diagonalForm f (truncate x B))
          ≤ ⨆ s : Finset (Idx d), ENNReal.ofReal (diagonalForm f (truncate x s)) :=
        le_iSup (fun s : Finset (Idx d) => ENNReal.ofReal (diagonalForm f (truncate x s))) B
      rwa [← closedForm_eq_iSup_truncate f
        (fun n => closedDegreeSymbol_nonneg (d := d) n) x] at h1
    have hnn : 0 ≤ ∑ n : Fin d → Fin Λ, ((∑ i, ((n i).val : ℝ)) + (d : ℝ)) * ‖y n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (by positivity)
    have h2 := ENNReal.toReal_mono hfin hle
    rwa [ENNReal.toReal_ofReal hnn] at h2
  -- assemble
  have hrel : (∑ m, ∑ n, (starRingEnd ℂ) (y m) * magCutoffKernel A m n * y n)
      = ∑ i : Fin d → Fin Λ, ∑ j : Fin d → Fin Λ,
          magCutoffKernel A i j * y j * (starRingEnd ℂ) (y i) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hmain : |closedKernelForm (boxKernel Λ A) x|
      ≤ a * (∑ n : Fin d → Fin Λ, ((∑ i, ((n i).val : ℝ)) + (d : ℝ)) * ‖y n‖ ^ 2)
        + (∑ i, (A i ^ 2 / (4 * a) - a)) * (∑ n : Fin d → Fin Λ, ‖y n‖ ^ 2) := by
    rw [closedKernelForm, hseries, ← hrel]
    have hcast : (∑ n : Fin d → Fin Λ, (((∑ i, (n i).val : ℕ) : ℝ) + (d : ℝ)) * ‖y n‖ ^ 2)
        = ∑ n : Fin d → Fin Λ, ((∑ i, ((n i).val : ℝ)) + (d : ℝ)) * ‖y n‖ ^ 2 := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Nat.cast_sum]
    have hb := ladder_form_le_degree (d := d) A ha y
    rw [hcast] at hb
    exact (Complex.abs_re_le_norm _).trans hb
  have hdeg2 : a * (∑ n : Fin d → Fin Λ, ((∑ i, ((n i).val : ℝ)) + (d : ℝ)) * ‖y n‖ ^ 2)
      ≤ a * (closedForm f x).toReal :=
    mul_le_mul_of_nonneg_left hdeg ha.le
  have hmass2 : (∑ i, (A i ^ 2 / (4 * a) - a)) * (∑ n : Fin d → Fin Λ, ‖y n‖ ^ 2)
      ≤ max (∑ i, (A i ^ 2 / (4 * a) - a)) 0 * ‖x‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hmass (le_max_right _ _))
  linarith [hmain, hdeg2, hmass2]

/-- **The cut-off ladder enters §6 at a cut-off-free ratio.**  If the reference symbol `g` dominates
the degree symbol (its kinetic part does), then `closed_farisLavine_domination` applies to
`boxKernel Λ A` with ratio `a ∈ (0,1)` chosen and shift `max (Σᵢ (Aᵢ²/(4a) − a)) 0`: neither
constant mentions `Λ`, so the comparison is uniform in the cut-off — the thing the
Hilbert–Schmidt branch could not deliver. -/
theorem closed_farisLavine_boxKernel {Λ : ℕ} (A : Fin d → ℝ) {μ g : Idx d → ℝ} {c₁ c₂ a : ℝ}
    (hc₁ : 0 < c₁) (ha : 0 < a) (ha1 : a < 1)
    (hdeg : ∀ n : Idx d, closedDegreeSymbol (d := d) n ≤ g n)
    (hdom : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2 ≤ (closedForm g x).toReal) :
    0 < (1 - a) * c₁ ∧
      ∀ x : L2 d, closedForm g x ≠ ⊤ →
        (1 - a) * c₁ * (closedForm μ x).toReal
            - ((1 - a) * c₂ + max (∑ i, (A i ^ 2 / (4 * a) - a)) 0) * ‖x‖ ^ 2
          ≤ (closedForm g x).toReal + closedKernelForm (boxKernel Λ A) x := by
  refine closed_farisLavine_domination (K := boxKernel Λ A) hc₁ ha1 hdom ?_
  intro x hfin
  have hle : closedForm (closedDegreeSymbol (d := d)) x ≤ closedForm g x :=
    closedForm_mono_symbol hdeg x
  have hmono : (closedForm (closedDegreeSymbol (d := d)) x).toReal ≤ (closedForm g x).toReal :=
    ENNReal.toReal_mono hfin hle
  have hnote : closedForm (closedDegreeSymbol (d := d)) x ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  have hK := abs_closedKernelForm_boxKernel_le (Λ := Λ) (d := d) A ha x hnote
  have hscaled := mul_le_mul_of_nonneg_left hmono ha.le
  linarith [hK, hscaled]

/-- **The unit-weight member of the uniform family: relative bound `1/2` at every cut-off.**  The
same comparison as `closed_farisLavine_boxKernel`, with the ratio *fixed* at `1/2` and the shift
written as `max ((Σᵢ Aᵢ²)/2 − d/2) 0` — the function of the field strength alone, with no
Hilbert–Schmidt mass and therefore no cut-off.  This is the statement the continuum argument
consumes: for every `Λ`, the ladder is `½ · degree + (⋯)` with the *same* constants, so `a(Λ) = 1/2`
is a single number below `1` rather than a family indexed by the cut-off. -/
theorem closed_farisLavine_boxKernel_half {Λ : ℕ} (A : Fin d → ℝ) {μ g : Idx d → ℝ}
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hdeg : ∀ n : Idx d, closedDegreeSymbol (d := d) n ≤ g n)
    (hdom : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2 ≤ (closedForm g x).toReal) :
    0 < (1 / 2) * c₁ ∧
      ∀ x : L2 d, closedForm g x ≠ ⊤ →
        (1 / 2) * c₁ * (closedForm μ x).toReal
            - ((1 / 2) * c₂ + max ((∑ i, A i ^ 2) / 2 - (d : ℝ) / 2) 0) * ‖x‖ ^ 2
          ≤ (closedForm g x).toReal + closedKernelForm (boxKernel Λ A) x := by
  have h := closed_farisLavine_boxKernel (Λ := Λ) (d := d) A (a := 1 / 2) hc₁
    (by norm_num) (by norm_num) hdeg hdom
  have hterm : ∀ i : Fin d, A i ^ 2 / (4 * (1 / 2)) - 1 / 2 = A i ^ 2 / 2 - 1 / 2 := by
    intro i
    norm_num
  have hc : (∑ i, (A i ^ 2 / (4 * (1 / 2)) - 1 / 2)) = (∑ i, A i ^ 2) / 2 - (d : ℝ) / 2 := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_div,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hc] at h
  refine ⟨?_, ?_⟩
  · have h1 := h.1
    norm_num at h1
    linarith
  · intro x hx
    have hx' := h.2 x hx
    norm_num at hx' ⊢
    linarith

/-! ### 13. The cut-off operator: its form, self-adjointness, and a uniform gap

§12 proves inequalities between *forms*.  A form has a spectrum only through the operator it
defines, and the transfer chain of `softmodes.md` §5.2 consumes a bounded self-adjoint operator
with a quantitative gap (`GapAt`).  This section supplies that operator for the cut-off forms of
`YangMillsFormClosure`:

* `diagCLM c hM` — multiplication by a bounded real symbol on `L²`, the operator whose quadratic
  form is `∑ₙ c n ‖x n‖²`.  On the cut-off, `c` is supported on a finite `s`, and the form is
  `∑ₙ∈s c n ‖x n‖² = diagonalForm` of the truncated state: for a *bounded* symbol the form is
  bounded, so it is already closed and its Friedrichs extension is the operator itself (no
  domain restriction is needed, unlike the unbounded degree symbol);
* `re_inner_diagCLM` / `re_inner_diagCLM_cutoff` — **the operator's form is the closed form**: on
  the cut-off it is exactly `diagonalForm c (truncate x s)`;
* `diagCLM_isSelfAdjoint` — it is self-adjoint, from the symmetry computation against `lp`'s inner
  product;
* `gapAt_diagCLM_of_symbol_separation` — **the minimax separation**: if the symbol takes the value
  `l` or is at least `l + c₁Δ`, then the operator has a quantitative gap `c₁Δ/2` at the window
  centre `l + c₁Δ/2`.  This is the pointwise/minimax content of a spectral separation: the
  Rayleigh quotients `⟪eₙ, A eₙ⟫ = c n` are *attained*, so bounding eigenvalues from below is the
  same as bounding the symbol;
* `gapAt_cutoff_uniform` — the same for the cut-off symbol `n ↦ if n ∈ s then c n else 0` at
  `l = 0`, with **constants independent of the cut-off `s`**, which is the `c₁Δ_ref` separation
  `ChapterTempleContinuumGap.gapAt_of_form_domination` works with and the hypothesis
  `gapAt_of_tendsto` propagates to a limit. -/

section DiagonalOperator

open BookProof.SpectralGapStability Filter

open scoped Topology

/-- The `ℓ²` exponent `2` can be read as an ordinary square. -/
theorem rpow_two_eq_sq (t : ℝ) : t ^ (2 : ℝ≥0∞).toReal = t ^ 2 := by
  have h : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h, Real.rpow_two]

/-- The squared modulus of a bounded real symbol times a state is summable. -/
theorem summable_normSq_diag {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x : L2 d) :
    Summable (fun n : Idx d => ‖(c n : ℂ) * x n‖ ^ 2) := by
  have hx : Summable fun n : Idx d => ‖x n‖ ^ 2 := by
    have h := (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    simpa [rpow_two_eq_sq] using h
  have hpt : ∀ n : Idx d, ‖(c n : ℂ) * x n‖ ^ 2 ≤ M ^ 2 * ‖x n‖ ^ 2 := by
    intro n
    have h1 : ‖(c n : ℂ) * x n‖ = |c n| * ‖x n‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖(c n : ℂ) * x n‖ ^ 2 = (|c n| * ‖x n‖) ^ 2 := by rw [h1]
      _ = |c n| ^ 2 * ‖x n‖ ^ 2 := by ring
      _ ≤ M ^ 2 * ‖x n‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [abs_nonneg (c n), hM n]
  exact Summable.of_nonneg_of_le (fun n => by positivity) hpt (hx.mul_left (M ^ 2))

/-- **The multiplication map by a bounded real symbol.** -/
noncomputable def diagLin (c : Idx d → ℝ) {M : ℝ} (hM : ∀ n, |c n| ≤ M) :
    L2 d →ₗ[ℂ] L2 d where
  toFun x := ⟨fun n => (c n : ℂ) * x n, memℓp_gen (by
    have h := summable_normSq_diag hM x
    simpa [rpow_two_eq_sq] using h)⟩
  map_add' x y := by
    apply lp.ext
    funext n
    simp [mul_add]
  map_smul' a x := by
    apply lp.ext
    funext n
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem diagLin_apply {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x : L2 d)
    (n : Idx d) : ((diagLin c hM x : L2 d) : Idx d → ℂ) n = (c n : ℂ) * x n := rfl

/-- **The symbol bound is an operator bound.** -/
theorem norm_diagLin_le {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x : L2 d) :
    ‖diagLin c hM x‖ ≤ M * ‖x‖ := by
  have hM0 : 0 ≤ M := (abs_nonneg (c 0)).trans (hM 0)
  have hx : Summable fun n : Idx d => ‖x n‖ ^ 2 := by
    have h := (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    simpa [rpow_two_eq_sq] using h
  have hpt : ∀ n : Idx d, ‖(c n : ℂ) * x n‖ ^ 2 ≤ M ^ 2 * ‖x n‖ ^ 2 := by
    intro n
    have h1 : ‖(c n : ℂ) * x n‖ = |c n| * ‖x n‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖(c n : ℂ) * x n‖ ^ 2 = (|c n| * ‖x n‖) ^ 2 := by rw [h1]
      _ = |c n| ^ 2 * ‖x n‖ ^ 2 := by ring
      _ ≤ M ^ 2 * ‖x n‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [abs_nonneg (c n), hM n]
  have hleft : ∑' n : Idx d, ‖(diagLin c hM x : L2 d) n‖ ^ 2
      = ∑' n : Idx d, ‖(c n : ℂ) * x n‖ ^ 2 := by
    refine tsum_congr fun n => ?_
    rw [diagLin_apply]
  have hle : ∑' n : Idx d, ‖(c n : ℂ) * x n‖ ^ 2 ≤ M ^ 2 * ∑' n : Idx d, ‖x n‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hpt (summable_normSq_diag hM x) (hx.mul_left (M ^ 2))
  have hnorm : M ^ 2 * (∑' n : Idx d, ‖x n‖ ^ 2) = (M * ‖x‖) ^ 2 := by
    have h : (∑' n : Idx d, ‖x n‖ ^ 2) = ‖x‖ ^ 2 := by
      have h' := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x
      simpa [rpow_two_eq_sq] using h'.symm
    rw [h]
    ring
  have key : ∑' n : Idx d, ‖(c n : ℂ) * x n‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := hle.trans_eq hnorm
  refine lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg hM0 (norm_nonneg x)) ?_
  simp only [rpow_two_eq_sq]
  exact hleft.trans_le key

/-- **The cut-off operator**: multiplication by a bounded real symbol, as a bounded operator. -/
noncomputable def diagCLM (c : Idx d → ℝ) {M : ℝ} (hM : ∀ n, |c n| ≤ M) : L2 d →L[ℂ] L2 d :=
  (diagLin c hM).mkContinuous M (norm_diagLin_le hM)

@[simp] theorem diagCLM_apply {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x : L2 d)
    (n : Idx d) : ((diagCLM c hM x : L2 d) : Idx d → ℂ) n = (c n : ℂ) * x n := rfl

theorem norm_diagCLM_apply_le {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x : L2 d) :
    ‖diagCLM c hM x‖ ≤ M * ‖x‖ :=
  norm_diagLin_le hM x

/-- A bounded real symbol gives a **symmetric** operator. -/
theorem diagCLM_symmetric {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x y : L2 d) :
    (inner ℂ (diagCLM c hM x) y : ℂ) = inner ℂ x (diagCLM c hM y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [diagCLM_apply, diagCLM_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- **Self-adjointness of the cut-off operator.** -/
theorem diagCLM_isSelfAdjoint {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) :
    IsSelfAdjoint (diagCLM c hM) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (diagCLM_symmetric hM)

/-- **The operator's quadratic form is the closed form.**  The real part of `⟪x, Ax⟫` is
`∑' n, c n ‖x n‖²`, which is the `L²` form `closedForm` closes from `diagonalForm`. -/
theorem re_inner_diagCLM {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x : L2 d) :
    (inner ℂ x (diagCLM c hM x) : ℂ).re = ∑' n : Idx d, c n * ‖x n‖ ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg (c 0)).trans (hM 0)
  have hx : Summable fun n : Idx d => ‖x n‖ ^ 2 := by
    have h := (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    simpa [rpow_two_eq_sq] using h
  have hsum : Summable fun n : Idx d =>
      inner ℂ (x n) (((diagCLM c hM x : L2 d) : Idx d → ℂ) n) := by
    refine Summable.of_norm_bounded (g := fun n : Idx d => M * ‖x n‖ ^ 2)
      (hx.mul_left M) (fun n => ?_)
    rw [diagCLM_apply]
    have hle : ‖(c n : ℂ)‖ ≤ M := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hM n
    calc ‖(inner ℂ (x n) ((c n : ℂ) * x n) : ℂ)‖
        ≤ ‖x n‖ * ‖(c n : ℂ) * x n‖ := norm_inner_le_norm _ _
      _ = ‖x n‖ * (‖(c n : ℂ)‖ * ‖x n‖) := by rw [norm_mul]
      _ ≤ ‖x n‖ * (M * ‖x n‖) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle (norm_nonneg _))
            (norm_nonneg _)
      _ = M * ‖x n‖ ^ 2 := by ring
  have hpt : ∀ n : Idx d,
      (inner ℂ (x n) (((diagCLM c hM x : L2 d) : Idx d → ℂ) n)).re = c n * ‖x n‖ ^ 2 := by
    intro n
    rw [diagCLM_apply]
    have hinner : inner ℂ (x n) ((c n : ℂ) * x n)
        = (c n : ℂ) * ((‖x n‖ ^ 2 : ℝ) : ℂ) := by
      have h1 : ((c n : ℂ) * x n) = (c n : ℂ) • x n := (smul_eq_mul _ _).symm
      rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [hinner]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [lp.inner_eq_tsum, Complex.re_tsum hsum]
  exact tsum_congr hpt

/-- A symbol supported on a finite set inherits the bound. -/
theorem cutoff_abs_le {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (s : Finset (Idx d)) :
    ∀ n : Idx d, |(if n ∈ s then c n else 0 : ℝ)| ≤ M := by
  intro n
  have hM0 : 0 ≤ M := (abs_nonneg (c 0)).trans (hM 0)
  split_ifs with h
  · exact hM n
  · simpa using hM0

/-- **On the cut-off the operator's form is the truncated closed form**: with the symbol
supported on a finite `s`, the quadratic form is `∑ₙ∈s c n ‖x n‖²`, which is exactly
`diagonalForm c (truncate x s)` — the form `YangMillsFormClosure` closes. -/
theorem re_inner_diagCLM_cutoff {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M)
    (x : L2 d) (s : Finset (Idx d)) :
    (inner ℂ x (diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s) x) : ℂ).re
      = diagonalForm c (truncate x s) := by
  rw [re_inner_diagCLM, diagonalForm_truncate]
  rw [tsum_eq_sum (s := s) (fun n hn => by rw [if_neg hn, zero_mul])]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos hn]

/-- Shifting a bounded symbol by a real constant keeps it bounded. -/
theorem abs_sub_le_abs {c : Idx d → ℝ} {M lam : ℝ} (hM : ∀ n, |c n| ≤ M) (n : Idx d) :
    |c n - lam| ≤ M + |lam| :=
  (abs_sub _ _).trans (by linarith [hM n])

/-- **The `ℓ²` norm as a sum of squared coordinates.** -/
theorem norm_sq_eq_tsum (x : L2 d) : ‖x‖ ^ 2 = ∑' n : Idx d, ‖x n‖ ^ 2 := by
  simpa [rpow_two_eq_sq] using
    (lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x)

/-- The operator norm squared, read off the coordinates. -/
theorem norm_diagCLM_sq {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x : L2 d) :
    ‖diagCLM c hM x‖ ^ 2 = ∑' n : Idx d, ‖(c n : ℂ) * x n‖ ^ 2 := by
  rw [norm_sq_eq_tsum (diagCLM c hM x)]
  exact tsum_congr fun n => by rw [diagCLM_apply]

/-- **The quantitative gap of a diagonal operator from a symbol bound.**  If the symbol stays at
distance at least `dd` from `lam`, then `A − lam` moves every vector by at least `dd‖x‖`.  This is
the minimax estimate in its sharpest form: for a diagonal operator the Rayleigh quotients are the
symbol values, so a pointwise bound on the symbol *is* a bound on the whole spectrum. -/
theorem gapAt_diagCLM_of_abs_sub {c : Idx d → ℝ} {M lam dd : ℝ}
    (hM : ∀ n, |c n| ≤ M) (hd : 0 ≤ dd) (h : ∀ n, dd ≤ |c n - lam|) :
    GapAt (diagCLM c hM) lam dd := by
  intro x
  have hM' : ∀ n : Idx d, |((fun n => c n - lam) n)| ≤ M + |lam| := fun n => abs_sub_le_abs hM n
  have hshift : diagCLM c hM x - (lam : ℂ) • x
      = diagCLM (fun n => c n - lam) hM' x := by
    apply lp.ext
    funext n
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      diagCLM_apply]
    push_cast
    ring
  rw [hshift]
  have hg : Summable fun n : Idx d => ‖(((c n - lam : ℝ)) : ℂ) * x n‖ ^ 2 :=
    summable_normSq_diag hM' x
  have hx : Summable fun n : Idx d => ‖x n‖ ^ 2 := by
    have h' := (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    simpa [rpow_two_eq_sq] using h'
  have hpt : ∀ n : Idx d, dd ^ 2 * ‖x n‖ ^ 2 ≤ ‖(((c n - lam : ℝ)) : ℂ) * x n‖ ^ 2 := by
    intro n
    have hd2 : dd ^ 2 ≤ |c n - lam| ^ 2 := by
      nlinarith [abs_nonneg (c n - lam), h n]
    have h1 : ‖(((c n - lam : ℝ)) : ℂ) * x n‖ = |c n - lam| * ‖x n‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    have hsq : (|c n - lam| * ‖x n‖) ^ 2 = |c n - lam| ^ 2 * ‖x n‖ ^ 2 := by ring
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hd2 (by positivity)
  have hsum_le : dd ^ 2 * (∑' n : Idx d, ‖x n‖ ^ 2)
      ≤ ∑' n : Idx d, ‖(((c n - lam : ℝ)) : ℂ) * x n‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hpt (hx.mul_left (dd ^ 2)) hg
  have hAy := norm_diagCLM_sq hM' x
  have hxn := norm_sq_eq_tsum x
  have hsq_le : (dd * ‖x‖) ^ 2 ≤ ‖diagCLM (fun n => c n - lam) hM' x‖ ^ 2 := by
    rw [hAy]
    have hmul : (dd * ‖x‖) ^ 2 = dd ^ 2 * (∑' n : Idx d, ‖x n‖ ^ 2) := by
      rw [← hxn]
      ring
    rw [hmul]
    exact hsum_le
  have hnn : 0 ≤ dd * ‖x‖ := mul_nonneg hd (norm_nonneg x)
  have hthis := sq_le_sq.mp hsq_le
  rwa [abs_of_nonneg hnn, abs_of_nonneg (norm_nonneg _)] at hthis

/-- **The minimax separation at the analytic constant.**  If the symbol either sits at the bottom
`l` or at least `l + c₁Δ` above it, then the operator has a quantitative gap `c₁Δ/2` at the window
centre `l + c₁Δ/2` — the constant `c₁Δ` of `softmodes.md` §5.2, reached pointwise rather than
through a spectrum computation. -/
theorem gapAt_diagCLM_of_symbol_separation {c : Idx d → ℝ} {M l Δ c₁ : ℝ}
    (hM : ∀ n, |c n| ≤ M) (hc₁ : 0 < c₁) (hΔ : 0 < Δ)
    (hsep : ∀ n, c n = l ∨ l + c₁ * Δ ≤ c n) :
    GapAt (diagCLM c hM) (l + c₁ * Δ / 2) (c₁ * Δ / 2) := by
  have hpos : 0 < c₁ * Δ / 2 := by
    have : 0 < c₁ * Δ := mul_pos hc₁ hΔ
    linarith
  refine gapAt_diagCLM_of_abs_sub hM hpos.le (fun n => ?_)
  rcases hsep n with h | h
  · rw [h]
    have hz : l - (l + c₁ * Δ / 2) = -(c₁ * Δ / 2) := by ring
    rw [hz, abs_neg, abs_of_nonneg hpos.le]
  · rw [abs_of_nonneg (by linarith : 0 ≤ c n - (l + c₁ * Δ / 2))]
    linarith

/-- **The cut-off family, uniformly.**  For a symbol supported on a finite `s`, the cut-off operator
keeps the separation of the full symbol with the value `0` on the zero sector, and the constants
`c₁Δ/2` do **not** depend on `s`.  This is the form the transfer chain consumes: a uniform
`GapAt` for the truncations at the plan's constant, ready for
`SpectralGapStability.gapAt_of_tendsto` once the truncations are known to converge. -/
theorem gapAt_cutoff_uniform {c : Idx d → ℝ} {M Δ c₁ : ℝ} (hM : ∀ n, |c n| ≤ M)
    (hc₁ : 0 < c₁) (hΔ : 0 < Δ) (hsep : ∀ n, c n = 0 ∨ c₁ * Δ ≤ c n)
    (s : Finset (Idx d)) :
    GapAt (diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s))
      (c₁ * Δ / 2) (c₁ * Δ / 2) := by
  have h := gapAt_diagCLM_of_symbol_separation (c := fun n => if n ∈ s then c n else 0)
    (l := 0) (cutoff_abs_le hM s) hc₁ hΔ (fun n => ?_)
  · simpa using h
  · change (if n ∈ s then c n else 0) = 0 ∨ 0 + c₁ * Δ ≤ (if n ∈ s then c n else 0)
    by_cases hn : n ∈ s
    · rw [if_pos hn]
      simpa using hsep n
    · rw [if_neg hn]
      exact Or.inl rfl

/-- **The cut-off operator is self-adjoint and uniformly gapped.**  The Friedrichs extension of the
cut-off closed form (the bounded operator of §13, whose form is `diagonalForm c (truncate x s)`) is
self-adjoint, and its gap at `0` is the analytic constant `c₁Δ/2` for every cut-off `s`. -/
theorem cutoff_operator_uniform_gap {c : Idx d → ℝ} {M Δ c₁ : ℝ} (hM : ∀ n, |c n| ≤ M)
    (hc₁ : 0 < c₁) (hΔ : 0 < Δ) (hsep : ∀ n, c n = 0 ∨ c₁ * Δ ≤ c n)
    (s : Finset (Idx d)) :
    IsSelfAdjoint (diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s)) ∧
      GapAt (diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s))
        (c₁ * Δ / 2) (c₁ * Δ / 2) :=
  ⟨diagCLM_isSelfAdjoint (cutoff_abs_le hM s), gapAt_cutoff_uniform hM hc₁ hΔ hsep s⟩

/-- **Faris–Lavine, bounded mode: the interaction costs exactly its norm.**  Adding a bounded
self-adjoint interaction to the cut-off operator keeps it self-adjoint, and the uniform gap of
`gapAt_cutoff_uniform` degrades by `‖K‖` and no more.

This is the form-sum step of §5.2 in the mode the box actually provides: on the cut-off the
interaction is a finite matrix, hence bounded.  For an *unbounded* interaction the same conclusion
is the Faris–Lavine/Kato–Rellich theorem on the form domain; what §6 of this module proves is the
relative-bound certificate (`closed_farisLavine_boxKernel`, at a cut-off-free ratio `a < 1`), and
what the corpus does **not** provide is the self-adjointness theorem that turns such a certificate
into a self-adjoint form sum — so nothing below is claimed for unbounded `K`. -/
theorem cutoff_operator_interacting {c : Idx d → ℝ} {M Δ c₁ : ℝ} (hM : ∀ n, |c n| ≤ M)
    (hc₁ : 0 < c₁) (hΔ : 0 < Δ) (hsep : ∀ n, c n = 0 ∨ c₁ * Δ ≤ c n)
    (s : Finset (Idx d)) (K : L2 d →L[ℂ] L2 d) (hK : IsSelfAdjoint K) :
    IsSelfAdjoint (diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s) + K) ∧
      GapAt (diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s) + K)
        (c₁ * Δ / 2) (c₁ * Δ / 2 - ‖K‖) := by
  obtain ⟨hsa, hgap⟩ := cutoff_operator_uniform_gap hM hc₁ hΔ hsep s
  have hsub : diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s)
      - (diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s) + K) = -K := by
    abel
  have hpert : ‖diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s)
      - (diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s) + K)‖ ≤ ‖K‖ := by
    rw [hsub, norm_neg]
  exact ⟨hsa.add hK, gapAt_perturb hgap hpert⟩

/-! ## 14. The cut-off family converges strongly, so the uniform gap reaches the limit

`gapAt_cutoff_uniform` gives every cut-off operator the *same* gap, but `softmodes.md` §5.2 needs
the limit, not the approximants.  The cut-off family does **not** converge in operator norm: the
symbol changes on an ever larger box, and `‖A_s − A‖` is governed by the sup of the symbol outside
`s`, which does not vanish for a degree-type symbol.  The mode that applies is strong convergence,
and the gap is closed under it — the norm is continuous, so a lower bound valid for every
approximant passes to the limit (`gapAt_of_strong_tendsto`).  What has to be proved is the
convergence itself: the cut-off difference of a state is the tail of a convergent series over an
exhausting family of boxes.
-/

/-- The coordinate box `{n | ∀ i, n i ≤ m}`: the cut-off `softmodes.md` §5.2 truncates to. -/
noncomputable def coordBox (d m : ℕ) : Finset (Idx d) :=
  Fintype.piFinset fun _ : Fin d => Finset.range (m + 1)

theorem mem_coordBox {m : ℕ} {n : Idx d} : n ∈ coordBox d m ↔ ∀ i, n i ≤ m := by
  simp [coordBox, Fintype.mem_piFinset]

/-- The boxes are monotone. -/
theorem coordBox_mono {m m' : ℕ} (h : m ≤ m') : coordBox d m ⊆ coordBox d m' := by
  intro n hn
  rw [mem_coordBox] at hn ⊢
  exact fun i => (hn i).trans h

/-- Every finite set of multi-indices sits in a box: the boxes are cofinal. -/
theorem exists_coordBox_superset (t : Finset (Idx d)) : ∃ m, t ⊆ coordBox d m := by
  refine ⟨t.sup (fun n => ∑ i, n i), fun n hn => ?_⟩
  rw [mem_coordBox]
  intro i
  refine (Finset.single_le_sum (f := fun j : Fin d => n j) (fun j _ => Nat.zero_le _)
    (Finset.mem_univ i)).trans (Finset.le_sup (s := t) hn)

/-- The boxes exhaust the index set. -/
theorem tendsto_coordBox_atTop :
    Tendsto (fun m => coordBox d m) atTop (atTop : Filter (Finset (Idx d))) := by
  refine tendsto_atTop.2 fun t => ?_
  obtain ⟨m, hm⟩ := exists_coordBox_superset t
  exact eventually_atTop.2 ⟨m, fun m' hm' => hm.trans (coordBox_mono hm')⟩

/-- Summability of the coordinate squares of a state. -/
theorem summable_normSq (x : L2 d) : Summable fun n : Idx d => ‖x n‖ ^ 2 := by
  have h := (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  simpa [rpow_two_eq_sq] using h

/-- **The cut-off tail of a summable family vanishes.**  The partial sums over the boxes converge to
the whole series, so the complement converges to zero.  This is the analytic input of every cut-off
limit below: applied to `‖x n‖²` it gives the strong convergence of §14, and to `‖c n x n‖²` it
gives the convergence of the unbounded resolvents of §18. -/
theorem tendsto_tail_of_summable {f : Idx d → ℝ} (hf : Summable f) :
    Tendsto (fun m => ∑' n : Idx d, if n ∈ coordBox d m then 0 else f n) atTop (𝓝 0) := by
  have hpart : Tendsto (fun m => ∑ n ∈ coordBox d m, f n)
      atTop (𝓝 (∑' n : Idx d, f n)) :=
    hf.hasSum.comp tendsto_coordBox_atTop
  have htail : ∀ m, (∑' n : Idx d, if n ∈ coordBox d m then 0 else f n)
      = (∑' n : Idx d, f n) - ∑ n ∈ coordBox d m, f n := by
    intro m
    set s := coordBox d m with hs
    have hg : Summable fun n : Idx d => if n ∈ s then f n else 0 :=
      Summable.of_norm_bounded (g := fun n : Idx d => ‖f n‖) hf.norm (fun n => by
        by_cases hn : n ∈ s
        · simp [hn]
        · simp [hn])
    have hpt : ∀ n : Idx d, (if n ∈ s then 0 else f n)
        = f n - (if n ∈ s then f n else 0) := by
      intro n
      by_cases hn : n ∈ s
      · rw [if_pos hn, if_pos hn, sub_self]
      · rw [if_neg hn, if_neg hn, sub_zero]
    calc (∑' n : Idx d, if n ∈ s then 0 else f n)
        = ∑' n : Idx d, (f n - (if n ∈ s then f n else 0)) := tsum_congr hpt
      _ = (∑' n : Idx d, f n) - ∑' n : Idx d, (if n ∈ s then f n else 0) := hf.tsum_sub hg
      _ = (∑' n : Idx d, f n) - ∑ n ∈ s, f n := by
          have hK : (∑' n : Idx d, if n ∈ s then f n else 0) = ∑ n ∈ s, f n := by
            rw [tsum_eq_sum (s := s) (f := fun n : Idx d => if n ∈ s then f n else 0)
              (fun n hn => by simp only [if_neg hn])]
            exact Finset.sum_congr rfl fun n hn => by rw [if_pos hn]
          rw [hK]
  have htotal : Tendsto (fun _ : ℕ => ∑' n : Idx d, f n) atTop (𝓝 (∑' n : Idx d, f n)) :=
    tendsto_const_nhds
  have hsub := htotal.sub hpart
  rw [sub_self] at hsub
  simpa [htail] using hsub

/-- **The cut-off tail of a state vanishes.** -/
theorem tendsto_tail_coordBox (x : L2 d) :
    Tendsto (fun m => ∑' n : Idx d, if n ∈ coordBox d m then 0 else ‖x n‖ ^ 2)
      atTop (𝓝 0) :=
  tendsto_tail_of_summable (summable_normSq x)

/-- **The cut-off operator differs from the full one by at most `M` times the tail.**  Both are
multiplications by the same symbol, off the box by `c n` against `0`. -/
theorem norm_diagCLM_cutoff_sub_le {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M)
    (s : Finset (Idx d)) (x : L2 d) :
    ‖diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s) x - diagCLM c hM x‖ ^ 2
      ≤ M ^ 2 * ∑' n : Idx d, if n ∈ s then 0 else ‖x n‖ ^ 2 := by
  set As := diagCLM (fun n => if n ∈ s then c n else 0) (cutoff_abs_le hM s) with hAs
  have hcoord : ∀ n : Idx d, ((As x - diagCLM c hM x : L2 d) : Idx d → ℂ) n
      = (((if n ∈ s then 0 else -c n) : ℝ) : ℂ) * x n := by
    intro n
    rw [hAs, lp.coeFn_sub, Pi.sub_apply, diagCLM_apply, diagCLM_apply]
    by_cases hn : n ∈ s
    · simp [hn]
    · simp only [hn, if_false]
      push_cast
      ring
  have hpt : ∀ n : Idx d, ‖((As x - diagCLM c hM x : L2 d) : Idx d → ℂ) n‖ ^ 2
      ≤ M ^ 2 * (if n ∈ s then 0 else ‖x n‖ ^ 2) := by
    intro n
    rw [hcoord]
    by_cases hn : n ∈ s
    · simp [hn]
    · rw [if_neg hn, if_neg hn]
      have h1 : ‖(((-c n : ℝ)) : ℂ) * x n‖ = |c n| * ‖x n‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
      rw [h1]
      have hsq : (|c n| * ‖x n‖) ^ 2 = |c n| ^ 2 * ‖x n‖ ^ 2 := by ring
      rw [hsq]
      exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (c n), hM n]) (by positivity)
  have hY : Summable fun n : Idx d => ‖((As x - diagCLM c hM x : L2 d) : Idx d → ℂ) n‖ ^ 2 :=
    summable_normSq (As x - diagCLM c hM x)
  have hR : Summable fun n : Idx d => M ^ 2 * (if n ∈ s then 0 else ‖x n‖ ^ 2) := by
    refine Summable.mul_left _ ?_
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by by_cases hn : n ∈ s <;> simp [hn]) (summable_normSq x)
  rw [norm_sq_eq_tsum (As x - diagCLM c hM x)]
  calc ∑' n : Idx d, ‖((As x - diagCLM c hM x : L2 d) : Idx d → ℂ) n‖ ^ 2
      ≤ ∑' n : Idx d, M ^ 2 * (if n ∈ s then 0 else ‖x n‖ ^ 2) :=
        Summable.tsum_le_tsum hpt hY hR
    _ = M ^ 2 * ∑' n : Idx d, if n ∈ s then 0 else ‖x n‖ ^ 2 := tsum_mul_left

/-- **The cut-off family converges strongly to the full operator.**  No norm convergence is claimed
and none holds in general; the strong limit is what §5.2's hypothesis speaks about. -/
theorem tendsto_diagCLM_cutoff {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x : L2 d) :
    Tendsto (fun m => diagCLM (fun n => if n ∈ coordBox d m then c n else 0)
        (cutoff_abs_le hM (coordBox d m)) x) atTop (𝓝 (diagCLM c hM x)) := by
  have hsq : Tendsto (fun m => ‖diagCLM (fun n => if n ∈ coordBox d m then c n else 0)
      (cutoff_abs_le hM (coordBox d m)) x - diagCLM c hM x‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => by positivity)
      (fun m => norm_diagCLM_cutoff_sub_le hM (coordBox d m) x) ?_
    simpa using (tendsto_tail_coordBox x).const_mul (M ^ 2)
  have hroot : Tendsto (fun m => Real.sqrt (‖diagCLM (fun n => if n ∈ coordBox d m then c n else 0)
      (cutoff_abs_le hM (coordBox d m)) x - diagCLM c hM x‖ ^ 2)) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
    rw [Real.sqrt_zero] at hs
    exact hs
  have hnorm : Tendsto (fun m => ‖diagCLM (fun n => if n ∈ coordBox d m then c n else 0)
      (cutoff_abs_le hM (coordBox d m)) x - diagCLM c hM x‖) atTop (𝓝 0) := by
    convert hroot using 2 with m
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnorm

/-- **A uniform gap survives strong convergence.**  If every approximant moves every state by at
least `dd‖x‖`, the limit does too: `‖(B − lam)x‖` is the limit of `‖(A_m − lam)x‖`, and a limit of
numbers bounded below by `dd‖x‖` is bounded below by `dd‖x‖`. -/
theorem gapAt_of_strong_tendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {A : ℕ → H →L[ℂ] H} {B : H →L[ℂ] H} {lam dd : ℝ}
    (hconv : ∀ x, Tendsto (fun m => A m x) atTop (𝓝 (B x)))
    (hgap : ∀ m, GapAt (A m) lam dd) : GapAt B lam dd := by
  intro x
  have hlim : Tendsto (fun m => ‖A m x - (lam : ℂ) • x‖) atTop
      (𝓝 ‖B x - (lam : ℂ) • x‖) :=
    ((hconv x).sub_const ((lam : ℂ) • x)).norm
  exact ge_of_tendsto hlim (Eventually.of_forall fun m => hgap m x)

/-- **The uniform gap at the cut-off-free constant, reached through the truncations.**  Every box
operator is gapped by `c₁Δ/2` at `c₁Δ/2` with constants independent of the box, the boxes converge
strongly, and the gap passes to the limit.  The hypothesis on the symbol is the same one
`gapAt_cutoff_uniform` uses, i.e. `c₁Δ` *is* the cut-off-free constant. -/
theorem gapAt_cutoffLimit {c : Idx d → ℝ} {M Δ c₁ : ℝ} (hM : ∀ n, |c n| ≤ M)
    (hc₁ : 0 < c₁) (hΔ : 0 < Δ) (hsep : ∀ n, c n = 0 ∨ c₁ * Δ ≤ c n) :
    GapAt (diagCLM c hM) (c₁ * Δ / 2) (c₁ * Δ / 2) :=
  gapAt_of_strong_tendsto (fun x => tendsto_diagCLM_cutoff hM x)
    fun m => gapAt_cutoff_uniform hM hc₁ hΔ hsep (coordBox d m)

/-- **The window centre is not in the spectrum of the limit.** -/
theorem notMem_spectrum_cutoffLimit {c : Idx d → ℝ} {M Δ c₁ : ℝ} (hM : ∀ n, |c n| ≤ M)
    (hc₁ : 0 < c₁) (hΔ : 0 < Δ) (hsep : ∀ n, c n = 0 ∨ c₁ * Δ ≤ c n) :
    (((c₁ * Δ / 2 : ℝ)) : ℂ) ∉ spectrum ℂ (diagCLM c hM) := by
  have hpos : 0 < c₁ * Δ / 2 := by
    have : 0 < c₁ * Δ := mul_pos hc₁ hΔ
    linarith
  exact notMem_spectrum_of_gapAt (diagCLM_isSelfAdjoint hM) hpos
    (gapAt_cutoffLimit hM hc₁ hΔ hsep)

/-! ## 15. The cut-off symbol of an *unbounded* symbol: the degree symbol on a box

`cutoff_abs_le` takes a global bound, which the degree symbol of §12.2 does not have: it grows with
the multi-index.  On a finite box the cut-off is bounded all the same — by its supremum on the box
and by `0` off it — so the whole §13 chain applies to the §12.2 symbol with the bound read off the
box.  That is the identification the plan needs: the operator side sees `closedDegreeSymbol`
exactly as `YangMillsFormClosure` sees `diagonalForm closedDegreeSymbol`.
-/

/-- The box bound of a cut-off of an unbounded symbol: the sum of the absolute values on `s`.  (`ℝ`
has no bottom element, so this is a sum rather than a supremum; loose is enough, and it is what
makes the box bound available for *any* symbol.) -/
noncomputable def cutoffBound (c : Idx d → ℝ) (s : Finset (Idx d)) : ℝ :=
  ∑ n ∈ s, |c n|

/-- The box bound is a bound. -/
theorem cutoffBound_abs_le (c : Idx d → ℝ) (s : Finset (Idx d)) :
    ∀ n : Idx d, |(if n ∈ s then c n else 0 : ℝ)| ≤ cutoffBound c s := by
  intro n
  by_cases hn : n ∈ s
  · rw [if_pos hn]
    exact Finset.single_le_sum (f := fun m => |c m|) (fun m _ => abs_nonneg _) hn
  · rw [if_neg hn, abs_zero]
    exact Finset.sum_nonneg fun m _ => abs_nonneg _

/-- **On the cut-off the unbounded symbol's operator has the truncated closed form.**  The same
identity as `re_inner_diagCLM_cutoff`, with the box bound replacing the global one — this is where
the degree symbol of `YangMillsFormClosure` enters the operator picture. -/
theorem re_inner_diagCLM_cutoffSymbol {c : Idx d → ℝ} (x : L2 d)
    (s : Finset (Idx d)) :
    (inner ℂ x (diagCLM (fun n => if n ∈ s then c n else 0) (cutoffBound_abs_le c s) x) : ℂ).re
      = diagonalForm c (truncate x s) := by
  rw [re_inner_diagCLM, diagonalForm_truncate]
  rw [tsum_eq_sum (s := s)
    (f := fun n : Idx d => (if n ∈ s then c n else 0) * ‖x n‖ ^ 2)
    (fun n hn => by simp only [if_neg hn, zero_mul])]
  exact Finset.sum_congr rfl fun n hn => by rw [if_pos hn]

/-- **The minimax separation on the cut-off of an unbounded symbol.**  On `s` the symbol is `0` or
at least `c₁Δ` above it; off `s` it is `0`.  Since the window centre `c₁Δ/2` is at distance
exactly `c₁Δ/2` from *both* values, the cut-off operator is gapped by `c₁Δ/2` at `c₁Δ/2` — the
same constant as `gapAt_cutoff_uniform`, now without a global bound. -/
theorem gapAt_cutoffSymbol {c : Idx d → ℝ} {Δ c₁ : ℝ} (hc₁ : 0 < c₁) (hΔ : 0 < Δ)
    (hsep : ∀ n, c n = 0 ∨ c₁ * Δ ≤ c n) (s : Finset (Idx d)) :
    GapAt (diagCLM (fun n => if n ∈ s then c n else 0) (cutoffBound_abs_le c s))
      (c₁ * Δ / 2) (c₁ * Δ / 2) := by
  have hpos : 0 < c₁ * Δ / 2 := by
    have : 0 < c₁ * Δ := mul_pos hc₁ hΔ
    linarith
  refine gapAt_diagCLM_of_abs_sub (cutoffBound_abs_le c s) hpos.le (fun n => ?_)
  by_cases hn : n ∈ s
  · rw [if_pos hn]
    rcases hsep n with h | h
    · rw [h]
      have hz : 0 - c₁ * Δ / 2 = -(c₁ * Δ / 2) := by ring
      rw [hz, abs_neg, abs_of_nonneg hpos.le]
    · rw [abs_of_nonneg (by linarith : 0 ≤ c n - c₁ * Δ / 2)]
      linarith
  · rw [if_neg hn]
    have hz : 0 - c₁ * Δ / 2 = -(c₁ * Δ / 2) := by ring
    rw [hz, abs_neg, abs_of_nonneg hpos.le]

/-- **The degree symbol on a box is uniformly gapped.**  `closedDegreeSymbol n = ∑ᵢ nᵢ + d ≥ d` for
every multi-index, so `gapAt_cutoffSymbol` applies with `c₁ = 1` and `Δ = d`: every box operator of
the §12.2 symbol is gapped by `d/2` at `d/2`, with the bound read off the box. -/
theorem gapAt_cutoffDegreeSymbol (hd : 0 < d) (s : Finset (Idx d)) :
    GapAt (diagCLM (fun n => if n ∈ s then closedDegreeSymbol (d := d) n else 0)
      (cutoffBound_abs_le (closedDegreeSymbol (d := d)) s)) ((d : ℝ) / 2) ((d : ℝ) / 2) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h := gapAt_cutoffSymbol (c := closedDegreeSymbol (d := d)) (c₁ := 1) (Δ := (d : ℝ))
    one_pos hdR (fun n => ?_) s
  · simpa using h
  · refine Or.inr ?_
    rw [one_mul]
    have hdef : closedDegreeSymbol (d := d) n = (∑ i : Fin d, ((n i : ℝ))) + (d : ℝ) := rfl
    have hsum : 0 ≤ ∑ i : Fin d, ((n i : ℝ)) := Finset.sum_nonneg fun i _ => by positivity
    rw [hdef]
    linarith

/-! ## 16. Kato–Rellich: a relative bound below one

The form comparison of §6 is a *relative-bound certificate*: `|qK| ≤ a q' + b‖·‖²` with `a < 1`.
What the Faris–Lavine step of §13 could only do in the bounded mode, the relative bound does in
general — for the **operator** bound `‖K x‖ ≤ a‖A x‖ + b‖x‖` with `a < 1`, self-adjointness of
`A + K` is `IsSelfAdjoint.add` in the bounded mode, but the *quantitative* part is not free: the
relative bound eats into the gap exactly, and the loss is `(1 − a)dd − (a|lam| + b)` rather than the
`dd − ‖K‖` of a norm bound.

**What is not proved here.**  For an unbounded reference operator `A` the same conclusion is
Kato–Rellich's theorem on the form domain: `A + K` is defined as the form sum, `q(A) + q(K)` is
closed on `D(q(A))`, and the associated operator is self-adjoint.  This corpus has the certificate
(`closed_farisLavine_domination`) but no form→operator representation theorem, so the unbounded
statement is not available and nothing below pretends to be it.
-/

/-- The two-term bound behind Kato–Rellich: `‖A x‖ ≤ ‖(A − lam)x‖ + |lam|‖x‖`. -/
theorem norm_apply_le_norm_sub {A : L2 d →L[ℂ] L2 d} (lam : ℝ) (x : L2 d) :
    ‖A x‖ ≤ ‖A x - (lam : ℂ) • x‖ + |lam| * ‖x‖ := by
  have h := norm_add_le (A x - (lam : ℂ) • x) ((lam : ℂ) • x)
  have heq : A x - (lam : ℂ) • x + (lam : ℂ) • x = A x := by abel
  rw [heq] at h
  calc ‖A x‖ ≤ ‖A x - (lam : ℂ) • x‖ + ‖(lam : ℂ) • x‖ := h
    _ = ‖A x - (lam : ℂ) • x‖ + |lam| * ‖x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- **Kato–Rellich, with the relative bound below one.**  If the interaction is `A`-bounded with
relative bound `a < 1` and additive constant `b`, the sum is self-adjoint and its gap at `lam` is
`(1 − a)·dd − (a|lam| + b)`: the relative part of the interaction acts on `A x` itself, so it costs
the gap `a` times over, and the absolute part costs `b` plus `a|lam|` from the shift. -/
theorem katoRellich_gap {A K : L2 d →L[ℂ] L2 d} (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    {a b lam dd : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hrel : ∀ x, ‖K x‖ ≤ a * ‖A x‖ + b * ‖x‖)
    (hgap : GapAt A lam dd) :
    IsSelfAdjoint (A + K) ∧ GapAt (A + K) lam ((1 - a) * dd - (a * |lam| + b)) := by
  have h1a : 0 ≤ 1 - a := by linarith
  refine ⟨hA.add hK, fun x => ?_⟩
  have hsplit : (A + K) x - (lam : ℂ) • x = (A x - (lam : ℂ) • x) + K x := by
    rw [ContinuousLinearMap.add_apply]
    abel
  rw [hsplit]
  have htri : ‖A x - (lam : ℂ) • x‖ - ‖K x‖ ≤ ‖(A x - (lam : ℂ) • x) + K x‖ := by
    have h := norm_sub_le ((A x - (lam : ℂ) • x) + K x) (K x)
    have heq : (A x - (lam : ℂ) • x) + K x - K x = A x - (lam : ℂ) • x := by abel
    rw [heq] at h
    linarith
  have hmul : (1 - a) * (dd * ‖x‖) ≤ (1 - a) * ‖A x - (lam : ℂ) • x‖ :=
    mul_le_mul_of_nonneg_left (hgap x) h1a
  have hAx := norm_apply_le_norm_sub (A := A) lam x
  have hKx := hrel x
  nlinarith [htri, hmul, hAx, hKx, norm_nonneg x, norm_nonneg (A x - (lam : ℂ) • x),
    norm_nonneg (K x)]

/-- **The cut-off-free gap survives a relatively bounded interaction.**  Chaining §14's limit gap
(`c₁Δ/2` at `c₁Δ/2`) with Kato–Rellich: the interacting operator is self-adjoint and its gap is
`(1 − a)c₁Δ/2 − (a·c₁Δ/2 + b)`, i.e. `c₁Δ/2 − (a·c₁Δ + b)`.  No cut-off appears in any constant. -/
theorem cutoffLimit_interacting {c : Idx d → ℝ} {M Δ c₁ : ℝ} (hM : ∀ n, |c n| ≤ M)
    (hc₁ : 0 < c₁) (hΔ : 0 < Δ) (hsep : ∀ n, c n = 0 ∨ c₁ * Δ ≤ c n)
    (K : L2 d →L[ℂ] L2 d) (hK : IsSelfAdjoint K) {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hrel : ∀ x, ‖K x‖ ≤ a * ‖diagCLM c hM x‖ + b * ‖x‖) :
    IsSelfAdjoint (diagCLM c hM + K) ∧
      GapAt (diagCLM c hM + K) (c₁ * Δ / 2)
        ((1 - a) * (c₁ * Δ / 2) - (a * |c₁ * Δ / 2| + b)) :=
  katoRellich_gap (diagCLM_isSelfAdjoint hM) hK ha ha1 hrel
    (gapAt_cutoffLimit hM hc₁ hΔ hsep)

/-! ## 17. The unbounded diagonal operator

§13–§15 cut the degree symbol down to boxes because `diagCLM` needs a global bound, and the symbol
itself has none.  The operator the symbol defines is multiplication by `c` on the states where the
weighted squares are summable: that is the limit the cut-offs are cut-offs *of*.  The reason the
unbounded case is tractable at all is that the **resolvent** is bounded whenever `c` stays off the
spectral parameter by `δ` — `(c n − lam)⁻¹` is then bounded by `δ⁻¹` — so no domain is needed to
write the approximating resolvents, and the gap follows from the two inverse identities.  What is
*not* claimed: self-adjointness as a statement about `LinearPMap` (the domain is presented as a
predicate, not a closed operator), and hence no `spectrum` statement — `notMem_spectrum_of_gapAt`
needs a bounded operator.
-/

/-- The operator domain of the unbounded diagonal operator: the states on which multiplication by
`c` lands back in `L²`. -/
def memDom (c : Idx d → ℝ) (x : L2 d) : Prop :=
  Summable fun n : Idx d => ‖(c n : ℂ) * x n‖ ^ 2

theorem memDom_zero (c : Idx d → ℝ) : memDom c 0 := by
  have h : (fun n : Idx d => ‖(c n : ℂ) * (0 : L2 d) n‖ ^ 2) = fun _ => (0 : ℝ) := by
    funext n
    simp
  rw [memDom, h]
  exact summable_zero

theorem memDom_add {c : Idx d → ℝ} {x y : L2 d} (hx : memDom c x) (hy : memDom c y) :
    memDom c (x + y) := by
  have hpt : ∀ n : Idx d, ‖(c n : ℂ) * (x + y) n‖ ^ 2
      ≤ 2 * ‖(c n : ℂ) * x n‖ ^ 2 + 2 * ‖(c n : ℂ) * y n‖ ^ 2 := by
    intro n
    have he : (c n : ℂ) * (x + y) n = (c n : ℂ) * x n + (c n : ℂ) * y n := by
      rw [lp.coeFn_add, Pi.add_apply]
      ring
    have h1 := norm_add_le ((c n : ℂ) * x n) ((c n : ℂ) * y n)
    have h2 : (‖(c n : ℂ) * x n‖ + ‖(c n : ℂ) * y n‖) ^ 2
        ≤ 2 * ‖(c n : ℂ) * x n‖ ^ 2 + 2 * ‖(c n : ℂ) * y n‖ ^ 2 := by
      nlinarith [sq_nonneg (‖(c n : ℂ) * x n‖ - ‖(c n : ℂ) * y n‖)]
    rw [he]
    calc ‖(c n : ℂ) * x n + (c n : ℂ) * y n‖ ^ 2
        ≤ (‖(c n : ℂ) * x n‖ + ‖(c n : ℂ) * y n‖) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ 2 * ‖(c n : ℂ) * x n‖ ^ 2 + 2 * ‖(c n : ℂ) * y n‖ ^ 2 := h2
  refine Summable.of_nonneg_of_le (fun n => by positivity) hpt ?_
  exact (hx.mul_left 2).add (hy.mul_left 2)

theorem memDom_smul {c : Idx d → ℝ} (a : ℂ) {x : L2 d} (hx : memDom c x) :
    memDom c (a • x) := by
  have hpt : ∀ n : Idx d,
      ‖(c n : ℂ) * (a • x) n‖ ^ 2 = ‖a‖ ^ 2 * ‖(c n : ℂ) * x n‖ ^ 2 := by
    intro n
    have he : (c n : ℂ) * (a • x) n = a * ((c n : ℂ) * x n) := by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, norm_mul]
    ring
  simp only [memDom, hpt]
  exact hx.mul_left (‖a‖ ^ 2)

/-- A bounded symbol's operator has the whole space as its domain: the consistency check between
§13 and the unbounded picture. -/
theorem memDom_of_bdd {c : Idx d → ℝ} {M : ℝ} (hM : ∀ n, |c n| ≤ M) (x : L2 d) :
    memDom c x :=
  summable_normSq_diag hM x

/-- **The unbounded multiplication operator**, applied to a state of its domain. -/
noncomputable def diagUnb (c : Idx d → ℝ) (x : L2 d) (hx : memDom c x) : L2 d :=
  ⟨fun n => (c n : ℂ) * x n, memℓp_gen (by
    have h : (fun n : Idx d => ‖(c n : ℂ) * x n‖ ^ (2 : ℝ≥0∞).toReal)
        = fun n : Idx d => ‖(c n : ℂ) * x n‖ ^ 2 := by
      funext n
      rw [rpow_two_eq_sq]
    rw [h]
    exact hx)⟩

@[simp] theorem diagUnb_apply {c : Idx d → ℝ} (x : L2 d) (hx : memDom c x) (n : Idx d) :
    ((diagUnb c x hx : L2 d) : Idx d → ℂ) n = (c n : ℂ) * x n := rfl

/-- It is **symmetric** on its domain. -/
theorem diagUnb_symmetric {c : Idx d → ℝ} {x y : L2 d} (hx : memDom c x) (hy : memDom c y) :
    inner ℂ (diagUnb c x hx) y = inner ℂ x (diagUnb c y hy) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [diagUnb_apply, diagUnb_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The reciprocal symbol of `c − lam`: what makes the resolvent bounded. -/
noncomputable def resSymbol (c : Idx d → ℝ) (lam : ℝ) : Idx d → ℝ := fun n => (c n - lam)⁻¹

/-- The reciprocal symbol is bounded by `δ⁻¹` wherever the symbol keeps its distance `δ`. -/
theorem resSymbol_abs_le {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) : ∀ n, |resSymbol c lam n| ≤ δ⁻¹ := by
  intro n
  have hx0 : 0 < |c n - lam| := lt_of_lt_of_le hδ0 (hδ n)
  rw [resSymbol, abs_inv]
  exact (inv_le_inv₀ hx0 hδ0).mpr (hδ n)

/-- The real reciprocal symbol, cast: `((c n − lam)⁻¹ : ℝ) : ℂ` is the inverse of `c n − lam`. -/
theorem resSymbol_cast {c : Idx d → ℝ} {lam : ℝ} (n : Idx d) :
    (((resSymbol c lam n : ℝ)) : ℂ) = ((c n : ℂ) - (lam : ℂ))⁻¹ := by
  rw [resSymbol, Complex.ofReal_inv]
  push_cast
  ring

/-- `c n − lam` is invertible where the symbol keeps its distance from `lam`. -/
theorem resSymbol_ne {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) (n : Idx d) : (c n : ℂ) - (lam : ℂ) ≠ 0 := by
  have hner : c n - lam ≠ 0 := by
    intro h0
    have h := hδ n
    rw [h0, abs_zero] at h
    linarith
  rw [← Complex.ofReal_sub]
  exact fun h => hner (Complex.ofReal_eq_zero.mp h)

/-- **The resolvent of the unbounded diagonal operator.**  It is a bounded operator even though the
operator is not: only the distance from `lam` to the symbol's range enters. -/
noncomputable def diagRes (c : Idx d → ℝ) (lam δ : ℝ) (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) : L2 d →L[ℂ] L2 d :=
  diagCLM (resSymbol c lam) (resSymbol_abs_le hδ0 hδ)

@[simp] theorem diagRes_apply {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) (ξ : L2 d) (n : Idx d) :
    ((diagRes c lam δ hδ0 hδ ξ : L2 d) : Idx d → ℂ) n
      = ((resSymbol c lam n : ℝ) : ℂ) * ξ n := rfl

/-- The resolvent is bounded by `δ⁻¹`: the uniform bound §5.2's hypothesis asks for. -/
theorem norm_diagRes_le {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) (ξ : L2 d) :
    ‖diagRes c lam δ hδ0 hδ ξ‖ ≤ δ⁻¹ * ‖ξ‖ :=
  norm_diagCLM_apply_le _ ξ

/-- The same bound in the form `‖ξ‖/δ` used by `gapAt_of_strongResolvent_limit`. -/
theorem norm_diagRes_le' {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) (ξ : L2 d) :
    ‖diagRes c lam δ hδ0 hδ ξ‖ ≤ ‖ξ‖ / δ := by
  rw [div_eq_inv_mul]
  exact norm_diagRes_le hδ0 hδ ξ

/-- The symbol stays at distance `δ` off `lam`, so the symbol divided by `c − lam` is bounded. -/
theorem resSymbol_mul_abs_le {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) (n : Idx d) :
    |c n| * |resSymbol c lam n| ≤ 1 + |lam| * δ⁻¹ := by
  have hne : c n - lam ≠ 0 := by
    intro h0
    have h := hδ n
    rw [h0, abs_zero] at h
    linarith
  have hkey : c n * resSymbol c lam n = 1 + lam * resSymbol c lam n := by
    have hsplit : c n = (c n - lam) + lam := by ring
    rw [resSymbol]
    nth_rewrite 1 [hsplit]
    rw [add_mul, mul_inv_cancel₀ hne]
  rw [← abs_mul, hkey]
  calc |1 + lam * resSymbol c lam n| ≤ 1 + |lam * resSymbol c lam n| := by
        simpa using abs_add_le (1 : ℝ) (lam * resSymbol c lam n)
    _ = 1 + |lam| * |resSymbol c lam n| := by rw [abs_mul]
    _ ≤ 1 + |lam| * δ⁻¹ := by
        have hb := mul_le_mul_of_nonneg_left (resSymbol_abs_le hδ0 hδ n) (abs_nonneg lam)
        linarith

/-- **The resolvent lands in the domain**: that is the point of the double inverse identities. -/
theorem memDom_diagRes {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) (ξ : L2 d) :
    memDom c (diagRes c lam δ hδ0 hδ ξ) := by
  have hξ : Summable fun n : Idx d => ‖ξ n‖ ^ 2 := summable_normSq ξ
  have hpt : ∀ n : Idx d,
      ‖(c n : ℂ) * ((diagRes c lam δ hδ0 hδ ξ : L2 d) : Idx d → ℂ) n‖ ^ 2
        ≤ (1 + |lam| * δ⁻¹) ^ 2 * ‖ξ n‖ ^ 2 := by
    intro n
    rw [diagRes_apply]
    have hnorm : ‖(c n : ℂ) * ((((resSymbol c lam n : ℝ)) : ℂ) * ξ n)‖
        = |c n| * |resSymbol c lam n| * ‖ξ n‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      ring
    rw [hnorm]
    have hb : |c n| * |resSymbol c lam n| * ‖ξ n‖
        ≤ (1 + |lam| * δ⁻¹) * ‖ξ n‖ :=
      mul_le_mul_of_nonneg_right (resSymbol_mul_abs_le hδ0 hδ n) (norm_nonneg _)
    calc (|c n| * |resSymbol c lam n| * ‖ξ n‖) ^ 2
        ≤ ((1 + |lam| * δ⁻¹) * ‖ξ n‖) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
      _ = (1 + |lam| * δ⁻¹) ^ 2 * ‖ξ n‖ ^ 2 := by ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) hpt ?_
  exact hξ.mul_left ((1 + |lam| * δ⁻¹) ^ 2)

/-- **The resolvent is a right inverse on the domain of the operator**: `(T − lam) R = 1` applied to
an arbitrary state. -/
theorem diagUnb_diagRes {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) (ξ : L2 d) :
    diagUnb c (diagRes c lam δ hδ0 hδ ξ) (memDom_diagRes hδ0 hδ ξ)
        - (lam : ℂ) • diagRes c lam δ hδ0 hδ ξ = ξ := by
  apply lp.ext
  funext n
  rw [lp.coeFn_sub, Pi.sub_apply, diagUnb_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    diagRes_apply]
  rw [resSymbol_cast n]
  have hne' := resSymbol_ne hδ0 hδ n
  field_simp

/-- **The resolvent is a left inverse on the domain of the operator**: `R (T − lam) = 1`. -/
theorem diagRes_left {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) {x : L2 d} (hx : memDom c x) :
    diagRes c lam δ hδ0 hδ (diagUnb c x hx - (lam : ℂ) • x) = x := by
  apply lp.ext
  funext n
  rw [diagRes_apply, lp.coeFn_sub, Pi.sub_apply, diagUnb_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [resSymbol_cast n]
  have hne' := resSymbol_ne hδ0 hδ n
  field_simp

/-- **The gap of the unbounded operator on its domain.**  Both inverse identities give
`‖x‖ ≤ δ⁻¹‖(T − lam)x‖` on the domain, which is the separation with the *same* constant `δ` that
bounds the reciprocal symbol — no boundedness of `T` is used anywhere. -/
theorem gapAt_diagUnb {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n, δ ≤ |c n - lam|) {x : L2 d} (hx : memDom c x) :
    δ * ‖x‖ ≤ ‖diagUnb c x hx - (lam : ℂ) • x‖ := by
  have h1 : ‖x‖ ≤ δ⁻¹ * ‖diagUnb c x hx - (lam : ℂ) • x‖ := by
    have he : diagRes c lam δ hδ0 hδ (diagUnb c x hx - (lam : ℂ) • x) = x :=
      diagRes_left hδ0 hδ hx
    calc ‖x‖ = ‖diagRes c lam δ hδ0 hδ (diagUnb c x hx - (lam : ℂ) • x)‖ := by rw [he]
      _ ≤ δ⁻¹ * ‖diagUnb c x hx - (lam : ℂ) • x‖ := norm_diagRes_le hδ0 hδ _
  rw [← div_eq_inv_mul] at h1
  rw [le_div_iff₀ hδ0] at h1
  linarith

/-- The degree symbol's distance from the window centre `d/2` is exactly `d/2`. -/
theorem degreeSep (_hd : 0 < d) :
    ∀ n : Idx d, closedDegreeSymbol (d := d) n = 0
      ∨ 1 * (d : ℝ) ≤ closedDegreeSymbol (d := d) n := by
  intro n
  refine Or.inr ?_
  rw [one_mul]
  have hdef : closedDegreeSymbol (d := d) n = (∑ i : Fin d, ((n i : ℝ))) + (d : ℝ) := rfl
  have hsum : 0 ≤ ∑ i : Fin d, ((n i : ℝ)) := Finset.sum_nonneg fun i _ => by positivity
  rw [hdef]
  linarith

/-- **The degree symbol's operator is gapped on its domain by `d/2` at `d/2`** — the limit of §15's
box gaps, now for the unbounded operator itself. -/
theorem gapAt_diagUnb_degree (hd : 0 < d) {x : L2 d}
    (hx : memDom (closedDegreeSymbol (d := d)) x) :
    ((d : ℝ) / 2) * ‖x‖ ≤ ‖diagUnb (closedDegreeSymbol (d := d)) x hx
      - ((((d : ℝ) / 2 : ℝ)) : ℂ) • x‖ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hδ : ∀ n : Idx d, (d : ℝ) / 2 ≤ |closedDegreeSymbol (d := d) n - (d : ℝ) / 2| := by
    intro n
    have hval : closedDegreeSymbol (d := d) n = (∑ i : Fin d, ((n i : ℝ))) + (d : ℝ) := rfl
    have hsum : 0 ≤ ∑ i : Fin d, ((n i : ℝ)) := Finset.sum_nonneg fun i _ => by positivity
    rw [hval, abs_of_nonneg (by linarith)]
    linarith
  exact gapAt_diagUnb hpos hδ hx

/-! ## 18. The resolvent-level form: §5.2's hypothesis, discharged

`softmodes.md` §5.2 writes the uniform gap as *conditional* on a strong-resolvent limit
(`gapAt_of_strongResolvent_limit`), and §14 discharged it through strong convergence of the
operators instead.  This section proves the resolvent form itself, so that hypothesis is discharged
literally: the approximating resolvents are the reciprocal-symbol operators `diagRes`, their uniform
bound `‖ξ‖/δ` is `norm_diagRes_le'`, they converge pointwise because the symbols converge and are
uniformly bounded (the box-tail argument, now with the tail of `‖ξ n‖²`), and the limit's left
inverse is `diagRes_left_bounded`.  Every input of the transfer lemma is supplied: nothing about
strong-resolvent convergence is assumed.  And because `diagRes` makes sense for *any* symbol, the
same convergence holds for the degree cut-offs, whose limit is the resolvent of §17's unbounded
operator rather than of a bounded one.
-/

/-- A vanishing squared norm gives convergence. -/
theorem tendsto_of_tendsto_norm_sq {u : ℕ → L2 d} {v : L2 d}
    (h : Tendsto (fun m => ‖u m - v‖ ^ 2) atTop (𝓝 0)) : Tendsto u atTop (𝓝 v) := by
  have hroot : Tendsto (fun m => Real.sqrt (‖u m - v‖ ^ 2)) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h
    rwa [Real.sqrt_zero] at hs
  have hnorm : Tendsto (fun m => ‖u m - v‖) atTop (𝓝 0) := by
    convert hroot using 2 with m
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hnorm

/-- The window centre `δ` — half the gap — keeps its distance from the separated symbol. -/
theorem resSymbol_sep_ge {c : Idx d → ℝ} {δ : ℝ} (hpos : 0 < δ)
    (hsep : ∀ n, c n = 0 ∨ 2 * δ ≤ c n) : ∀ n : Idx d, δ ≤ |c n - δ| := by
  intro n
  rcases hsep n with h | h
  · rw [h, show (0 : ℝ) - δ = -δ by ring, abs_neg, abs_of_nonneg hpos.le]
  · rw [abs_of_nonneg (by linarith : 0 ≤ c n - δ)]
    linarith

/-- The same for a cut-off: the box bound does not move the symbol's distance. -/
theorem resSymbol_cutoff_sep_ge {c : Idx d → ℝ} {δ : ℝ} (hpos : 0 < δ)
    (hsep : ∀ n, c n = 0 ∨ 2 * δ ≤ c n) (s : Finset (Idx d)) :
    ∀ n : Idx d, δ ≤ |(if n ∈ s then c n else 0) - δ| := by
  intro n
  by_cases hn : n ∈ s
  · rw [if_pos hn]
    exact resSymbol_sep_ge hpos hsep n
  · rw [if_neg hn, show (0 : ℝ) - δ = -δ by ring, abs_neg, abs_of_nonneg hpos.le]

/-- Two diagonal resolvents differ by multiplication by the difference of their reciprocal
symbols. -/
theorem diagRes_sub_apply {c₁' c₂' : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (h1 : ∀ n, δ ≤ |c₁' n - lam|) (h2 : ∀ n, δ ≤ |c₂' n - lam|) (ξ : L2 d) (n : Idx d) :
    ((diagRes c₁' lam δ hδ0 h1 ξ - diagRes c₂' lam δ hδ0 h2 ξ : L2 d) : Idx d → ℂ) n
      = (((resSymbol c₁' lam n - resSymbol c₂' lam n : ℝ)) : ℂ) * ξ n := by
  rw [lp.coeFn_sub, Pi.sub_apply, diagRes_apply (c := c₁') hδ0 h1,
    diagRes_apply (c := c₂') hδ0 h2]
  push_cast
  ring

/-- **The cut-off resolvents are within `2δ⁻¹` times the state's tail of the limit resolvent.**
The symbols agree on the box; off it both are bounded by `δ⁻¹`, so the difference is too. -/
theorem norm_diagRes_cutoff_sub_le {c : Idx d → ℝ} {δ : ℝ} (hpos : 0 < δ)
    (hsep : ∀ n, c n = 0 ∨ 2 * δ ≤ c n) (s : Finset (Idx d)) (ξ : L2 d) :
    ‖diagRes (fun n => if n ∈ s then c n else 0) δ δ hpos
          (resSymbol_cutoff_sep_ge hpos hsep s) ξ
        - diagRes c δ δ hpos (resSymbol_sep_ge hpos hsep) ξ‖ ^ 2
      ≤ (2 * δ⁻¹) ^ 2 * ∑' n : Idx d, if n ∈ s then 0 else ‖ξ n‖ ^ 2 := by
  set B := diagRes c δ δ hpos (resSymbol_sep_ge hpos hsep) with hB
  have hpt : ∀ n : Idx d,
      ‖((diagRes (fun n => if n ∈ s then c n else 0) δ δ hpos
            (resSymbol_cutoff_sep_ge hpos hsep s) ξ - B ξ : L2 d) : Idx d → ℂ) n‖ ^ 2
        ≤ (2 * δ⁻¹) ^ 2 * (if n ∈ s then 0 else ‖ξ n‖ ^ 2) := by
    intro n
    rw [hB, diagRes_sub_apply hpos (resSymbol_cutoff_sep_ge hpos hsep s)
      (resSymbol_sep_ge hpos hsep) ξ n]
    by_cases hn : n ∈ s
    · have hz : resSymbol (fun m => if m ∈ s then c m else 0) δ n - resSymbol c δ n = 0 := by
        simp [resSymbol, hn]
      rw [hz, if_pos hn]
      simp
    · have hb_s := resSymbol_abs_le hpos (resSymbol_cutoff_sep_ge hpos hsep s) n
      have hb := resSymbol_abs_le hpos (resSymbol_sep_ge hpos hsep) n
      have hdiff : |resSymbol (fun m => if m ∈ s then c m else 0) δ n - resSymbol c δ n|
          ≤ 2 * δ⁻¹ := by
        have h := abs_add_le (resSymbol (fun m => if m ∈ s then c m else 0) δ n)
          (-(resSymbol c δ n))
        have h' : |resSymbol (fun m => if m ∈ s then c m else 0) δ n - resSymbol c δ n|
            ≤ |resSymbol (fun m => if m ∈ s then c m else 0) δ n| + |resSymbol c δ n| := by
          simpa [sub_eq_add_neg] using h
        linarith
      rw [if_neg hn]
      have hnorm : ‖((resSymbol (fun m => if m ∈ s then c m else 0) δ n
            - resSymbol c δ n : ℝ) : ℂ) * ξ n‖
          = |resSymbol (fun m => if m ∈ s then c m else 0) δ n - resSymbol c δ n|
              * ‖ξ n‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm]
      calc (|resSymbol (fun m => if m ∈ s then c m else 0) δ n - resSymbol c δ n|
            * ‖ξ n‖) ^ 2
          ≤ ((2 * δ⁻¹) * ‖ξ n‖) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)) 2
        _ = (2 * δ⁻¹) ^ 2 * ‖ξ n‖ ^ 2 := by ring
  have htail : Summable fun n : Idx d => if n ∈ s then 0 else ‖ξ n‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by by_cases hn : n ∈ s <;> simp [hn]) (summable_normSq ξ)
  rw [norm_sq_eq_tsum]
  calc ∑' n : Idx d,
        ‖((diagRes (fun n => if n ∈ s then c n else 0) δ δ hpos
            (resSymbol_cutoff_sep_ge hpos hsep s) ξ - B ξ : L2 d) : Idx d → ℂ) n‖ ^ 2
      ≤ ∑' n : Idx d, (2 * δ⁻¹) ^ 2 * (if n ∈ s then 0 else ‖ξ n‖ ^ 2) :=
        Summable.tsum_le_tsum hpt (summable_normSq _) (htail.mul_left _)
    _ = (2 * δ⁻¹) ^ 2 * ∑' n : Idx d, if n ∈ s then 0 else ‖ξ n‖ ^ 2 := tsum_mul_left

/-- **The cut-off resolvents converge pointwise to the limit resolvent.** -/
theorem tendsto_diagRes_cutoff {c : Idx d → ℝ} {δ : ℝ} (hpos : 0 < δ)
    (hsep : ∀ n, c n = 0 ∨ 2 * δ ≤ c n) (ξ : L2 d) :
    Tendsto (fun m => diagRes (fun n => if n ∈ coordBox d m then c n else 0) δ δ hpos
        (resSymbol_cutoff_sep_ge hpos hsep (coordBox d m)) ξ) atTop
      (𝓝 (diagRes c δ δ hpos (resSymbol_sep_ge hpos hsep) ξ)) := by
  refine tendsto_of_tendsto_norm_sq ?_
  refine squeeze_zero (fun m => by positivity)
    (fun m => norm_diagRes_cutoff_sub_le hpos hsep (coordBox d m) ξ) ?_
  have htail := tendsto_tail_of_summable (summable_normSq ξ)
  simpa using htail.const_mul ((2 * δ⁻¹) ^ 2)

/-- **The resolvent is a left inverse of the bounded operator's `T − lam`.** -/
theorem diagRes_left_bounded {c : Idx d → ℝ} {M lam δ : ℝ} (hM : ∀ n, |c n| ≤ M)
    (hδ0 : 0 < δ) (hδ : ∀ n, δ ≤ |c n - lam|) (x : L2 d) :
    diagRes c lam δ hδ0 hδ (diagCLM c hM x - (lam : ℂ) • x) = x := by
  apply lp.ext
  funext n
  rw [diagRes_apply, lp.coeFn_sub, Pi.sub_apply, diagCLM_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, resSymbol_cast n]
  have hne' := resSymbol_ne hδ0 hδ n
  field_simp

/-- **Phase 5.2's hypothesis discharged**: the uniform gap at the cut-off-free constant, proved
through the strong-resolvent mode with every hypothesis supplied — the resolvent bound, the
pointwise convergence of the cut-off resolvents, and the limit's left inverse.  The only hypothesis
left is the analytic separation of the symbol, which is what `softmodes.md` §5.2 derives from the
form bound. -/
theorem gapAt_cutoffLimit_resolvent {c : Idx d → ℝ} {Δ c₁ : ℝ} (hc₁ : 0 < c₁) (hΔ : 0 < Δ)
    (hsep : ∀ n, c n = 0 ∨ c₁ * Δ ≤ c n) {M : ℝ} (hM : ∀ n, |c n| ≤ M) :
    GapAt (diagCLM c hM) (c₁ * Δ / 2) (c₁ * Δ / 2) := by
  have hpos : 0 < c₁ * Δ / 2 := by
    have h : 0 < c₁ * Δ := mul_pos hc₁ hΔ
    linarith
  have hsep2 : ∀ n, c n = 0 ∨ 2 * (c₁ * Δ / 2) ≤ c n := by
    intro n
    rcases hsep n with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  exact gapAt_of_strongResolvent_limit (B := diagCLM c hM)
    (R := diagRes c (c₁ * Δ / 2) (c₁ * Δ / 2) hpos (resSymbol_sep_ge hpos hsep2))
    (Rm := fun m => diagRes (fun n => if n ∈ coordBox d m then c n else 0) (c₁ * Δ / 2)
      (c₁ * Δ / 2) hpos (resSymbol_cutoff_sep_ge hpos hsep2 (coordBox d m)))
    hpos
    (fun m ξ => norm_diagRes_le' hpos (resSymbol_cutoff_sep_ge hpos hsep2 (coordBox d m)) ξ)
    (fun ξ => tendsto_diagRes_cutoff hpos hsep2 ξ)
    (fun x => diagRes_left_bounded hM hpos (resSymbol_sep_ge hpos hsep2) x)

/-- The spectral hole, in the same resolvent mode. -/
theorem notMem_spectrum_cutoffLimit_resolvent {c : Idx d → ℝ} {Δ c₁ : ℝ} (hc₁ : 0 < c₁)
    (hΔ : 0 < Δ) (hsep : ∀ n, c n = 0 ∨ c₁ * Δ ≤ c n) {M : ℝ} (hM : ∀ n, |c n| ≤ M) :
    (((c₁ * Δ / 2 : ℝ)) : ℂ) ∉ spectrum ℂ (diagCLM c hM) := by
  have hpos : 0 < c₁ * Δ / 2 := by
    have h : 0 < c₁ * Δ := mul_pos hc₁ hΔ
    linarith
  exact notMem_spectrum_of_gapAt (diagCLM_isSelfAdjoint hM) hpos
    (gapAt_cutoffLimit_resolvent hc₁ hΔ hsep hM)

/-- The degree symbol separated at the *gap* `d/2`: `0` or at least `2·(d/2) = d`. -/
theorem degreeSepTwo (hd : 0 < d) :
    ∀ n : Idx d, closedDegreeSymbol (d := d) n = 0
      ∨ 2 * ((d : ℝ) / 2) ≤ closedDegreeSymbol (d := d) n := by
  intro n
  rcases degreeSep hd n with h | h
  · exact Or.inl h
  · have h' : (d : ℝ) ≤ closedDegreeSymbol (d := d) n := by simpa using h
    exact Or.inr (by linarith)

/-- **The degree cut-offs' resolvents converge to the unbounded operator's resolvent**, i.e. the
§15 box gaps have a limit at the resolvent level even though the limit operator is unbounded. -/
theorem tendsto_diagRes_cutoff_degree (hd : 0 < d) (hpos : (0 : ℝ) < (d : ℝ) / 2)
    (ξ : L2 d) :
    Tendsto (fun m => diagRes (fun n => if n ∈ coordBox d m then closedDegreeSymbol (d := d) n
        else 0) ((d : ℝ) / 2) ((d : ℝ) / 2) hpos
        (resSymbol_cutoff_sep_ge hpos (degreeSepTwo hd) (coordBox d m)) ξ) atTop
      (𝓝 (diagRes (closedDegreeSymbol (d := d)) ((d : ℝ) / 2) ((d : ℝ) / 2) hpos
        (resSymbol_sep_ge hpos (degreeSepTwo hd)) ξ)) :=
  tendsto_diagRes_cutoff hpos (degreeSepTwo hd) ξ

end DiagonalOperator

/-! ## 19. Self-adjointness of the unbounded operator

§17 claimed only what the gap needs — symmetry, a bounded resolvent and the two inverse identities —
and said so: self-adjointness as a statement about closed operators was not claimed.  This section
claims it.  The operator is `diagSubLin c`, multiplication by `c` on the subspace `diagSub c` where
the weighted squares are summable, and the route is **Faris–Lavine**
(`essentiallySelfAdjointOn_of_farisLavine`, Theorem 1 of the paper) rather than a Friedrichs form:
the criterion asks for no closability or semiboundedness of a form, only a positive `N` on the same
domain and a commutator bound.  Taking `N` to be the operator itself is exactly right here, because
the symbol is *real*: the commutator form vanishes identically (`commForm_diagSubLin_self`), so the
commutator hypothesis holds with constant `0`.  That leaves the two hypotheses the paper actually
uses: positivity of the quadratic form (`quadForm_diagSubLin_nonneg`, which is where the symbol is
assumed nonnegative) and surjectivity of `T + 1` (`diagSubLin_surj_one`, the resolvent at `−1` in
disguise — the reciprocal of `c n + 1` is bounded by `1`).  Faris–Lavine gives trivial deficiency,
`exists_isSelfAdjointExtension_of_esa` turns it into a self-adjoint operator on a domain containing
`diagSub c` and agreeing with `diagUnb` there, and `dense_diagSub` supplies the density the
extension theory needs: the finite-support states are in the domain.

The gap of §17 survives into this picture, since it is an inequality on `diagSub c` alone; what is
new is that the operator it bounds from below now *has* an adjoint and a spectrum.
-/

section SelfAdjoint

open BookProof.FarisLavine BookProof.EsaClosure

/-- The domain of the unbounded operator, as a subspace of `L²`. -/
def diagSub (c : Idx d → ℝ) : Submodule ℂ (L2 d) where
  carrier := {x | memDom c x}
  zero_mem' := memDom_zero c
  add_mem' := fun hx hy => memDom_add hx hy
  smul_mem' := fun a _ hx => memDom_smul a hx

/-- **The unbounded operator as a linear map on its domain** — the shape in which the
self-adjointness theory takes its operators. -/
noncomputable def diagSubLin (c : Idx d → ℝ) : diagSub c →ₗ[ℂ] L2 d where
  toFun x := diagUnb c x x.2
  map_add' x y := by
    apply lp.ext
    funext n
    simp only [lp.coeFn_add, Pi.add_apply, diagUnb_apply, Submodule.coe_add]
    ring
  map_smul' a x := by
    apply lp.ext
    funext n
    simp only [lp.coeFn_smul, Pi.smul_apply, diagUnb_apply, Submodule.coe_smul, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- The unbounded operator is symmetric on its domain — §17's symmetry, in the shape Faris–Lavine's
hypothesis (i) is stated in. -/
theorem diagSubLin_symmetric (c : Idx d → ℝ) : SymmetricOn (diagSub c) (diagSubLin c) :=
  fun x y => diagUnb_symmetric x.2 y.2

/-- **The quadratic form of the diagonal operator is the weighted sum of squares.** -/
theorem re_inner_diagUnb {c : Idx d → ℝ} {x : L2 d} (hx : memDom c x) :
    (inner ℂ x (diagUnb c x hx)).re = ∑' n : Idx d, c n * ‖x n‖ ^ 2 := by
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner x (diagUnb c x hx))]
  refine tsum_congr fun n => ?_
  rw [diagUnb_apply, RCLike.inner_apply]
  have h : (c n : ℂ) * x n * (starRingEnd ℂ) (x n) = ((c n * ‖x n‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
  rw [h, Complex.ofReal_re]

/-- The form is nonnegative when the symbol is. -/
theorem quadForm_diagSubLin_nonneg {c : Idx d → ℝ} (hc : ∀ n, 0 ≤ c n) (x : diagSub c) :
    0 ≤ quadForm (diagSubLin c) x := by
  rw [quadForm]
  have h : (inner ℂ (x : L2 d) ((diagSubLin c) x) : ℂ).re
      = ∑' n : Idx d, c n * ‖(x : L2 d) n‖ ^ 2 := re_inner_diagUnb x.2
  rw [h]
  exact tsum_nonneg fun n => mul_nonneg (hc n) (sq_nonneg _)

/-- **The commutator vanishes**, because the symbol is real: `i[T, T] = 0`.  This is why
Faris–Lavine is cheap here — the criterion's only nontrivial inputs are positivity and `T + 1`
onto. -/
theorem commForm_diagSubLin_self (c : Idx d → ℝ) (x : diagSub c) :
    commForm (diagSubLin c) (diagSubLin c) x = 0 := by
  have h : (inner ℂ ((diagSubLin c) x) ((diagSubLin c) x) : ℂ).im = 0 :=
    inner_self_im (𝕜 := ℂ) ((diagSubLin c) x)
  rw [commForm_eq, h]
  ring

/-- **`T + 1` is onto.**  For a nonnegative symbol the reciprocal of `c n + 1` is bounded by `1`, so
the candidate preimage is in `L²`; the symbol divided by `c n + 1` is bounded by `1` as well, so it
is in the domain too. -/
theorem diagSubLin_surj_one {c : Idx d → ℝ} (hc : ∀ n, 0 ≤ c n) (f : L2 d) :
    ∃ x : diagSub c, diagSubLin c x + (x : L2 d) = f := by
  have hb : ∀ n : Idx d, |(c n + 1)⁻¹| ≤ 1 := by
    intro n
    have hpos : (0 : ℝ) < c n + 1 := by linarith [hc n]
    rw [abs_of_pos (inv_pos.mpr hpos)]
    have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ c n + 1 by linarith [hc n])
      (inv_nonneg.mpr hpos.le)
    rwa [mul_one, inv_mul_cancel₀ (ne_of_gt hpos)] at hmul
  have hmem : memDom c (diagCLM (fun n => (c n + 1)⁻¹) hb f) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_normSq f)
    rw [diagCLM_apply]
    have hpos : (0 : ℝ) < c n + 1 := by linarith [hc n]
    have hnorm : ‖(c n : ℂ) * (((((c n + 1 : ℝ)⁻¹) : ℝ) : ℂ) * f n)‖
        = |c n| * |(c n + 1)⁻¹| * ‖f n‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      ring
    rw [hnorm]
    have hle : |c n| * |(c n + 1)⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (hc n), abs_of_pos (inv_pos.mpr hpos)]
      calc c n * (c n + 1)⁻¹ ≤ (c n + 1) * (c n + 1)⁻¹ :=
            mul_le_mul_of_nonneg_right (by linarith [hc n]) (inv_nonneg.mpr hpos.le)
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    calc (|c n| * |(c n + 1)⁻¹| * ‖f n‖) ^ 2
        ≤ (1 * ‖f n‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hle (norm_nonneg _)) 2
      _ = ‖f n‖ ^ 2 := by ring
  refine ⟨⟨diagCLM (fun n => (c n + 1)⁻¹) hb f, hmem⟩, ?_⟩
  apply lp.ext
  funext n
  have h1 : ((diagSubLin c ⟨diagCLM (fun m => (c m + 1)⁻¹) hb f, hmem⟩ : L2 d)
      : Idx d → ℂ) n
      = (c n : ℂ) * (((diagCLM (fun m => (c m + 1)⁻¹) hb f : L2 d)) : Idx d → ℂ) n := rfl
  rw [lp.coeFn_add, Pi.add_apply, h1, diagCLM_apply, Complex.ofReal_inv]
  have hpos : (0 : ℝ) < c n + 1 := by linarith [hc n]
  have hnz : (((c n + 1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  have hcast : ((c n : ℂ) + 1) = (((c n + 1 : ℝ)) : ℂ) := by push_cast; ring
  calc (c n : ℂ) * (((((c n + 1 : ℝ)) : ℂ))⁻¹ * f n) + (((((c n + 1 : ℝ)) : ℂ))⁻¹ * f n)
      = ((c n : ℂ) + 1) * (((((c n + 1 : ℝ)) : ℂ))⁻¹ * f n) := by ring
    _ = (((c n + 1 : ℝ)) : ℂ) * (((((c n + 1 : ℝ)) : ℂ))⁻¹ * f n) := by rw [hcast]
    _ = f n := by rw [← mul_assoc, mul_inv_cancel₀ hnz, one_mul]

/-- **Faris–Lavine for the diagonal operator.**  With a nonnegative symbol, `T = diagUnb c` is
essentially self-adjoint on its domain.  The criterion is applied with `N = T`: the commutator form
vanishes, the form is nonnegative, and `T + 1` is onto. -/
theorem diagUnb_esa {c : Idx d → ℝ} (hc : ∀ n, 0 ≤ c n) :
    EssentiallySelfAdjointOn (diagSub c) (diagSubLin c) :=
  essentiallySelfAdjointOn_of_farisLavine (diagSubLin c) (diagSubLin c) 0
    (diagSubLin_symmetric c) (diagSubLin_symmetric c) le_rfl
    (fun x => quadForm_diagSubLin_nonneg hc x) (diagSubLin_surj_one hc)
    (fun x => by rw [commForm_diagSubLin_self]; simp)

/-- The finite-support states are in the domain: only one term of the weighted square-sum
survives. -/
theorem memDom_single {c : Idx d → ℝ} (i : Idx d) (a : ℂ) :
    memDom c (lp.single 2 i a) := by
  refine summable_of_ne_finset_zero (s := {i}) (fun m hm => ?_)
  have hzero : ((lp.single 2 i a : L2 d) : Idx d → ℂ) m = 0 := by
    rw [lp.single_apply]
    exact Pi.single_eq_of_ne (M := fun _ : Idx d => ℂ) (by simpa using hm) a
  rw [hzero]
  simp

/-- **The domain is dense**, as the extension theory requires: every state is the limit of its
finite-support approximations, and those are in the domain. -/
theorem dense_diagSub (c : Idx d → ℝ) :
    Dense ((diagSub c : Submodule ℂ (L2 d)) : Set (L2 d)) := by
  classical
  refine Metric.dense_iff.2 (fun f ε hε => ?_)
  have hsum : HasSum (fun i : Idx d => lp.single 2 i (f i)) f := lp.hasSum_single (by simp) f
  have hev : ∀ᶠ s : Finset (Idx d) in Filter.atTop,
      (∑ i ∈ s, lp.single 2 i (f i)) ∈ Metric.ball f ε :=
    hsum (Metric.ball_mem_nhds f hε)
  obtain ⟨s, hs⟩ := hev.exists
  exact ⟨∑ i ∈ s, lp.single 2 i (f i), hs,
    Submodule.sum_mem _ (fun i _ => memDom_single i (f i))⟩

/-- **Self-adjointness of the unbounded diagonal operator.**  The closure of `diagUnb c` — for a
nonnegative symbol — is a self-adjoint operator on a domain containing `diagSub c`, and on that
domain it *is* `diagUnb`.  This is the statement §17 left open; it is von Neumann's theorem applied
through Faris–Lavine, and it is what gives the operator a spectrum at all. -/
theorem exists_selfAdjoint_extension_diagUnb {c : Idx d → ℝ} (hc : ∀ n, 0 ≤ c n) :
    ∃ (Dom : Submodule ℂ (L2 d)) (A : Dom →ₗ[ℂ] L2 d),
      IsSelfAdjointExtension (diagSubLin c) A :=
  exists_isSelfAdjointExtension_of_esa (diagSubLin c) (dense_diagSub c) (diagSubLin_symmetric c)
    (diagUnb_esa hc)

/-- **The degree symbol's operator is self-adjoint under closure** — the unbounded case of §15, with
no cut-off and no boundedness of the symbol.  The symbol is nonnegative
(`closedDegreeSymbol_nonneg`), so Faris–Lavine applies as it does for any nonnegative symbol. -/
theorem exists_selfAdjoint_extension_degree :
    ∃ (Dom : Submodule ℂ (L2 d)) (A : Dom →ₗ[ℂ] L2 d),
      IsSelfAdjointExtension (diagSubLin (closedDegreeSymbol (d := d))) A :=
  exists_selfAdjoint_extension_diagUnb fun n => closedDegreeSymbol_nonneg (d := d) n

end SelfAdjoint

/-! ## 20. The spectrum of the unbounded diagonal operator

§19 gave `diagUnb c` a self-adjoint extension; §17–§18 computed the spectrum of the *bounded*
cut-offs.  This section does the unbounded case with no extension theory at all: the diagonal
operator is self-adjoint on its **maximal** domain, so the operator whose resolvent and spectrum one
computes is `diagUnb c` itself, with no ambiguity about which extension is meant.

Maximality is a coordinate computation (`memDom_of_mem_adjointDomain`): if `ψ ↦ ⟪diagUnb c ψ, φ⟫` is
represented by `η`, then testing against `ψ = lp.single 2 n 1` reads off `c n · φ n = η n`, so `φ`
lies in the domain *because* `η` is in `L²`.  With the symmetry of §17 this gives
`adjointDomain (diagSub c) (diagSubLin c) = diagSub c` (`adjointDomain_diagSubLin`), i.e.
`IsSelfAdjointOn` on the largest possible domain, and bundles the operator as an
`UnboundedSelfAdjoint` (`diagUnbSelfAdjoint`).

That bundle is exactly the input of the workspace's spectral theorem for unbounded self-adjoint
operators, `BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general` (the Cayley
route: bounded model of the resolvent `resOp`, then `A = R⁻¹ + i`).  Applying it is
`diagUnb_multiplication_model`.  For a diagonal operator the model is degenerate — it *is*
multiplication by `c` on `ℓ²` — so the concrete spectral statement needs no measures, and it is an
identity rather than a bound: `lam` is in the resolvent set exactly when the symbol keeps a positive
distance from `lam` (`inResolventSet_iff_exists_gap`).  Hence the spectrum is the closure of the
range of the symbol (`closure_range_eq_compl_resolvent`).

Both directions are elementary.  `δ`-separation gives the §17 resolvent `diagRes`.  Conversely a
bounded two-sided inverse `R` moves a coordinate vector by at most `‖R‖ · |c n − lam|` while keeping
its norm `1`, so `1 ≤ ‖R‖ · |c n − lam|` and therefore `(‖R‖ + 1)⁻¹ ≤ |c n − lam|` for every `n`.
§19 stays consistent: the operator is already self-adjoint, so Faris–Lavine's closure is the
operator itself.
-/

section Spectrum

open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.UnboundedSpectralModel BookProof.ChapterSpectralDirectSum
open BookProof.ChapterSpectralMultiplication BookProof.ChapterAbelianGelfandModel
open MeasureTheory

open scoped BookProof.ChapterSpectralMultiplication

/-- **The coordinate vectors are eigenvectors**, in the norm one states them in: the operator sends
`lp.single 2 n 1` to `c n` times itself. -/
theorem diagUnb_single {c : Idx d → ℝ} (n : Idx d) :
    diagUnb c (lp.single 2 n 1) (memDom_single n 1) = (c n : ℂ) • lp.single 2 n 1 := by
  apply lp.ext
  funext m
  rw [diagUnb_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hm : m = n
  · subst hm
    rw [lp.single_apply_self]
  · rw [lp.single_apply_ne 2 n 1 hm]
    simp

/-- **The adjoint domain is contained in the maximal domain.**  Testing the representing identity
against coordinate vectors turns it into `c n · φ n = η n`; the weighted square-sum of `φ` is then
the square-sum of `η`, which is finite because `η` is in `L²`.  This is the only place the diagonal
structure enters, and it is what makes the operator self-adjoint on the largest domain it can have.
-/
theorem memDom_of_mem_adjointDomain {c : Idx d → ℝ} {phi : L2 d}
    (hphi : phi ∈ adjointDomain (diagSub c) (diagSubLin c)) : memDom c phi := by
  obtain ⟨eta, heta⟩ := hphi
  have hL : ∀ n : Idx d,
      (inner ℂ (diagSubLin c ⟨lp.single 2 n 1, memDom_single n 1⟩) phi : ℂ)
        = (c n : ℂ) * phi n := by
    intro n
    have hsub : (diagSubLin c ⟨lp.single 2 n 1, memDom_single n 1⟩ : L2 d)
        = diagUnb c (lp.single 2 n 1) (memDom_single n 1) := rfl
    rw [hsub, diagUnb_single n, inner_smul_left, lp.inner_single_left, RCLike.inner_apply]
    simp
  have hcoord : ∀ n : Idx d, (c n : ℂ) * phi n = eta n := by
    intro n
    have h : (inner ℂ (diagSubLin c ⟨lp.single 2 n 1, memDom_single n 1⟩) phi : ℂ)
        = inner ℂ (lp.single 2 n 1 : L2 d) eta := by
      simpa using heta ⟨lp.single 2 n 1, memDom_single n 1⟩
    rw [hL n, lp.inner_single_left, RCLike.inner_apply] at h
    simpa using h
  rw [memDom]
  have heq : (fun n : Idx d => ‖(c n : ℂ) * phi n‖ ^ 2) = fun n => ‖eta n‖ ^ 2 := by
    funext n
    rw [hcoord n]
  rw [heq]
  exact summable_normSq eta

/-- **The diagonal operator is self-adjoint on its maximal domain**: the adjoint domain is not
merely contained in the domain, it *is* the domain.  The forward inclusion is
`memDom_of_mem_adjointDomain`, the reverse is symmetry (§17). -/
theorem adjointDomain_diagSubLin (c : Idx d → ℝ) :
    adjointDomain (diagSub c) (diagSubLin c) = ((diagSub c : Submodule ℂ (L2 d)) : Set (L2 d)) := by
  ext phi
  refine ⟨fun hphi => memDom_of_mem_adjointDomain hphi, fun hphi => ?_⟩
  exact ⟨diagUnb c phi hphi, fun psi => diagUnb_symmetric psi.2 hphi⟩

/-- `diagUnb c` is self-adjoint on `diagSub c`, in the shape the spectral theory consumes. -/
theorem diagSubLin_isSelfAdjointOn (c : Idx d → ℝ) :
    IsSelfAdjointOn (diagSub c) (diagSubLin c) :=
  adjointDomain_diagSubLin c

/-- **The unbounded diagonal operator, bundled.**  No nonnegativity, no closure, no choice of
extension: `diagUnb c` is self-adjoint on the domain of all states whose symbol-weighted square-sum
is finite. -/
def diagUnbSelfAdjoint (c : Idx d → ℝ) : UnboundedSelfAdjoint (L2 d) where
  domain := diagSub c
  op := diagSubLin c
  denseDomain := dense_diagSub c
  symmetric := diagSubLin_symmetric c
  selfAdjoint := diagSubLin_isSelfAdjointOn c

@[simp] theorem diagUnbSelfAdjoint_domain (c : Idx d → ℝ) :
    (diagUnbSelfAdjoint c).domain = diagSub c := rfl

@[simp] theorem diagUnbSelfAdjoint_op (c : Idx d → ℝ) :
    (diagUnbSelfAdjoint c).op = diagSubLin c := rfl

/-- **The workspace's unbounded spectral theorem applies to the diagonal operator.**  This is
`unbounded_multiplication_model_general` — proved in `BookProof.ChapterUnboundedSpectralModel`
by the Cayley route — instantiated at `diagUnbSelfAdjoint c`: the operator is unitarily a
multiplication operator on a Hilbert sum of `L²` spaces over probability measures on the spectrum
of its resolvent.  The concrete spectral statement below is sharper only because for a diagonal
symbol the measures are read off the coordinates, so no model is needed to locate the spectrum. -/
theorem diagUnb_multiplication_model (c : Idx d → ℝ) :
    ∃ (S : Set (L2 d)) (mu : S → Measure (spectrum ℂ (resOp (diagUnbSelfAdjoint c))))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] L2 d),
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ x : S, ∀ᵐ z ∂(mu x), z.1 ≠ 0 ∧ ‖z.1‖ ^ 2 = z.1.im) ∧
      (∀ (x : S) (u : Lp ℂ 2 (mu x)),
        ∃ h : V x (mulRep (mu x) (coordFn (resOp (diagUnbSelfAdjoint c))) u)
            ∈ (diagUnbSelfAdjoint c).domain,
          (diagUnbSelfAdjoint c).op
              ⟨V x (mulRep (mu x) (coordFn (resOp (diagUnbSelfAdjoint c))) u), h⟩
            = V x (u + Complex.I • mulRep (mu x) (coordFn (resOp (diagUnbSelfAdjoint c))) u)) :=
  unbounded_multiplication_model_general (diagUnbSelfAdjoint c)

/-- **The resolvent set of the unbounded diagonal operator**, as a predicate: a bounded operator
that is a two-sided inverse for `T − lam`.  Stated directly for `diagUnb` on `memDom c` (not for the
bundle) so that the inverse identities are exactly §17's. -/
def InResolventSet (c : Idx d → ℝ) (lam : ℝ) : Prop :=
  ∃ R : L2 d →L[ℂ] L2 d,
    (∀ f : L2 d, ∃ h : memDom c (R f), diagUnb c (R f) h - (lam : ℂ) • R f = f) ∧
    (∀ (x : L2 d) (hx : memDom c x), R (diagUnb c x hx - (lam : ℂ) • x) = x)

/-- **A positive distance from the symbol gives a resolvent.**  This is §17's `diagRes` packaged as
the resolvent-set predicate. -/
theorem inResolventSet_of_gap {c : Idx d → ℝ} {lam δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ n : Idx d, δ ≤ |c n - lam|) : InResolventSet c lam :=
  ⟨diagRes c lam δ hδ0 hδ,
    fun f => ⟨memDom_diagRes hδ0 hδ f, diagUnb_diagRes hδ0 hδ f⟩,
    fun _ hx => diagRes_left hδ0 hδ hx⟩

/-- **The resolvent set forces a positive distance from the symbol.**  A coordinate vector is moved
by the factor `|c n − lam|` and recovered with norm `1` by a bounded inverse, so
`(‖R‖ + 1)⁻¹` is a lower bound for the distance of the symbol's range from `lam`.  This is the
harder half of "spectrum = closure of the range", and it is where boundedness of the inverse is
used. -/
theorem exists_gap_of_inResolventSet {c : Idx d → ℝ} {lam : ℝ} (h : InResolventSet c lam) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : Idx d, δ ≤ |c n - lam| := by
  obtain ⟨R, -, hleft⟩ := h
  have hsingleNorm : ∀ i : Idx d, ‖(lp.single 2 i 1 : L2 d)‖ = 1 := by
    intro i
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    simp
  have hnorm : ∀ n : Idx d,
      ‖diagUnb c (lp.single 2 n 1) (memDom_single n 1)
        - (lam : ℂ) • lp.single 2 n 1‖ = |c n - lam| := by
    intro m
    rw [diagUnb_single m, ← sub_smul, norm_smul, lp.norm_single (by norm_num)]
    rw [norm_one, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hmove : ∀ m : Idx d, (1 : ℝ) ≤ ‖R‖ * |c m - lam| := by
    intro m
    have hrec : ‖(lp.single 2 m 1 : L2 d)‖
        = ‖R (diagUnb c (lp.single 2 m 1) (memDom_single m 1)
            - (lam : ℂ) • lp.single 2 m 1)‖ := by
      rw [hleft _ (memDom_single m 1)]
    calc (1 : ℝ) = ‖(lp.single 2 m 1 : L2 d)‖ := (hsingleNorm m).symm
      _ = ‖R (diagUnb c (lp.single 2 m 1) (memDom_single m 1)
              - (lam : ℂ) • lp.single 2 m 1)‖ := hrec
      _ ≤ ‖R‖ * ‖diagUnb c (lp.single 2 m 1) (memDom_single m 1)
              - (lam : ℂ) • lp.single 2 m 1‖ := R.le_opNorm _
      _ = ‖R‖ * |c m - lam| := by rw [hnorm m]
  refine ⟨(‖R‖ + 1)⁻¹, by positivity, fun n => ?_⟩
  have hpos : (0 : ℝ) < ‖R‖ + 1 := by positivity
  refine (inv_le_iff_one_le_mul₀ hpos).2 ?_
  have hstep : ‖R‖ * |c n - lam| ≤ (‖R‖ + 1) * |c n - lam| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hle := hmove n
  nlinarith [hle, hstep]

/-- **`lam` is in the resolvent set exactly when the symbol stays a positive distance away.** -/
theorem inResolventSet_iff_exists_gap {c : Idx d → ℝ} {lam : ℝ} :
    InResolventSet c lam ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ n : Idx d, δ ≤ |c n - lam| :=
  ⟨exists_gap_of_inResolventSet, fun ⟨_, hδ0, hδ⟩ => inResolventSet_of_gap hδ0 hδ⟩

/-- **`lam` is in the spectrum exactly when it is a limit point of the symbol's range** — the
negation of the resolvent-set criterion, in the `∀ δ > 0` form. -/
theorem notMem_inResolventSet_iff {c : Idx d → ℝ} {lam : ℝ} :
    ¬ InResolventSet c lam ↔ ∀ δ : ℝ, 0 < δ → ∃ n : Idx d, |c n - lam| < δ := by
  rw [inResolventSet_iff_exists_gap]
  constructor
  · intro h δ hδ
    by_contra hcon
    push_neg at hcon
    exact h ⟨δ, hδ, hcon⟩
  · rintro h ⟨δ, hδ0, hδ⟩
    obtain ⟨n, hn⟩ := h δ hδ0
    linarith [hδ n]

/-- **The spectrum of the unbounded diagonal operator is the closure of the symbol's range.**
`diagUnbSelfAdjoint c` is self-adjoint on the maximal domain, so this is a statement about the
operator itself and not about a chosen extension; the bounded cut-offs of §17–§18 have the same
spectral hole, approached at the resolvent level by `tendsto_diagRes_cutoff_degree`. -/
theorem closure_range_eq_compl_resolvent (c : Idx d → ℝ) :
    closure (Set.range c) = {lam : ℝ | ¬ InResolventSet c lam} := by
  ext lam
  rw [Set.mem_setOf_eq, notMem_inResolventSet_iff, Metric.mem_closure_iff]
  constructor
  · intro h δ hδ
    obtain ⟨y, ⟨n, rfl⟩, hy⟩ := h δ hδ
    refine ⟨n, ?_⟩
    rw [Real.dist_eq] at hy
    rwa [abs_sub_comm]
  · intro h ε hε
    obtain ⟨n, hn⟩ := h ε hε
    refine ⟨c n, ⟨n, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact hn

end Spectrum

/-! ## 21. The form of the operator: the unbounded form sum

§20 went from the operator to its spectrum.  This section goes the other way, from a *form* to the
operator that represents it — the step §6 of this chapter and the honest boundary of
`OSSReconstruction`-style clustering both record as missing: the corpus has the relative-bound
certificate `closed_farisLavine_domination` and no theorem turning it into a self-adjoint form
sum.

The form is the sum `q_c + q_K` of the diagonal form of the symbol `c` and a **bounded symmetric
perturbation** `K` — exactly the shape a Faris–Lavine comparison produces.  The operator is
`T + K` on the domain of `T`, because a bounded perturbation does not change the domain:

* `diagSumLin_apply`, `diagSumLin_symmetric` — the operator and its symmetry;
* **`diagSumLin_isSelfAdjointOn`** — it is self-adjoint on the *maximal* domain.  The
  adjoint-domain computation of §20 repeats verbatim once `K` is moved across the inner product;
* **`re_inner_diagSum`** — the quadratic form of the operator is the sum of the two forms, so the
  operator *is* the form sum and not merely a form bound for it;
* `formTsum`, `memDom_subset_formDom` — the operator's form is defined by a real (not `ℝ≥0∞`)
  series on the **form domain** `∑ |c n| ‖x n‖² < ∞`, which contains the operator domain, is
  dense there (`dense_formDom`), and is where §5's interacting form lives;
* `formTsum_ge_of_le_symbol` and `formSum_ge` — the resulting form is bounded below by
  `θ − σ`, the constant §5's bottom estimate produces.

What §21 does not do by itself: closedness of `q_c + q_K` on the form domain, and the statement that
the operator domain is a form *core* in the form norm.  Closedness for diagonal forms — for any
symbol, with the `a < 1` relative bound — is `BookProof.YangMillsFormKLMN` §23
(`formTsum_lsc`, `formDom_of_tendsto`, `klmn`); a bounded `K` is norm-continuous (`|q_K| ≤ ‖K‖‖x‖²`)
and so cannot disturb it.  The form-*core* statement is still only ambient-norm density
(`dense_formDom`); it is not used by §22 or §23, because both read the form off the operator on the
maximal domain directly.
-/

section FormSum

open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {c : Idx d → ℝ} {K : L2 d →L[ℂ] L2 d}

/-- **The operator of the form sum**: `T + K` on the domain of `T`.  A bounded perturbation does not
change the domain, which is why the sum form is represented on the maximal domain. -/
noncomputable def diagSumLin (c : Idx d → ℝ) (K : L2 d →L[ℂ] L2 d) : diagSub c →ₗ[ℂ] L2 d :=
  diagSubLin c + K.toLinearMap.comp (diagSub c).subtype

@[simp] theorem diagSumLin_apply (K : L2 d →L[ℂ] L2 d) (x : diagSub c) :
    diagSumLin c K x = diagUnb c x x.2 + K (x : L2 d) := rfl

/-- **The form-sum operator is symmetric** — both terms are, and the cross terms agree because the
sum is a sum of symmetric operators, not because of any commutator hypothesis. -/
theorem diagSumLin_symmetric (K : L2 d →L[ℂ] L2 d)
    (hK : ∀ x y : L2 d, inner ℂ (K x) y = inner ℂ x (K y)) :
    IsSymmetricOn (diagSub c) (diagSumLin c K) := by
  have hincl : ∀ x : diagSub c, diagSumLin c K x = diagUnb c x x.2 + K (x : L2 d) := fun _ => rfl
  intro x y
  rw [hincl x, hincl y, inner_add_left, inner_add_right, diagUnb_symmetric x.2 y.2,
    hK (x : L2 d) (y : L2 d)]

/-- **A bounded symmetric perturbation does not enlarge the adjoint domain.**  Moving `K` across the
inner product turns the representing identity of the sum into the representing identity of `T` with
the representing vector shifted by `K φ`; §20 then puts `φ` in the maximal domain.  This is the
whole content of Kato–Rellich at relative bound `0`, read off the adjoint rather than off a
resolvent. -/
theorem memDom_of_mem_adjointDomain_sum (K : L2 d →L[ℂ] L2 d)
    (hK : ∀ x y : L2 d, inner ℂ (K x) y = inner ℂ x (K y)) {phi : L2 d}
    (hphi : phi ∈ adjointDomain (diagSub c) (diagSumLin c K)) : memDom c phi := by
  obtain ⟨eta, heta⟩ := hphi
  refine memDom_of_mem_adjointDomain ⟨eta - K phi, fun psi => ?_⟩
  have hbase : ((diagSubLin c) psi : L2 d) = diagUnb c psi psi.2 := rfl
  have h : inner ℂ (diagSumLin c K psi) phi = inner ℂ (psi : L2 d) eta := heta psi
  have hexp : diagSumLin c K psi = diagUnb c psi psi.2 + K (psi : L2 d) := rfl
  rw [hexp, inner_add_left, hK (psi : L2 d) phi] at h
  rw [hbase, inner_sub_right]
  linear_combination h

/-- **The unbounded form sum is represented by a self-adjoint operator on the maximal domain.**
`T + K` with `K` bounded and symmetric is self-adjoint on `diagSub c`, with no gap hypothesis, no
relative bound below one, and no choice of extension.  The two inclusions are
`memDom_of_mem_adjointDomain_sum` and the symmetry of `diagSumLin_symmetric`. -/
theorem adjointDomain_diagSumLin (K : L2 d →L[ℂ] L2 d)
    (hK : ∀ x y : L2 d, inner ℂ (K x) y = inner ℂ x (K y)) :
    adjointDomain (diagSub c) (diagSumLin c K)
      = ((diagSub c : Submodule ℂ (L2 d)) : Set (L2 d)) := by
  ext phi
  refine ⟨fun hphi => memDom_of_mem_adjointDomain_sum K hK hphi, fun hphi => ?_⟩
  refine ⟨diagUnb c phi hphi + K phi, fun psi => ?_⟩
  have hexp : diagSumLin c K psi = diagUnb c psi psi.2 + K (psi : L2 d) := rfl
  rw [hexp, inner_add_left, hK (psi : L2 d) phi, diagUnb_symmetric psi.2 hphi, inner_add_right]

theorem diagSumLin_isSelfAdjointOn (K : L2 d →L[ℂ] L2 d)
    (hK : ∀ x y : L2 d, inner ℂ (K x) y = inner ℂ x (K y)) :
    IsSelfAdjointOn (diagSub c) (diagSumLin c K) :=
  adjointDomain_diagSumLin K hK

/-- **The form-sum operator, bundled** — the input shape of the workspace's unbounded spectral
theorem, as `diagUnbSelfAdjoint` is for §20. -/
def diagSumSelfAdjoint (c : Idx d → ℝ) (K : L2 d →L[ℂ] L2 d)
    (hK : ∀ x y : L2 d, inner ℂ (K x) y = inner ℂ x (K y)) : UnboundedSelfAdjoint (L2 d) where
  domain := diagSub c
  op := diagSumLin c K
  denseDomain := dense_diagSub c
  symmetric := diagSumLin_symmetric K hK
  selfAdjoint := diagSumLin_isSelfAdjointOn K hK

/-- **The quadratic form of the operator is the sum of the two forms.**  This is the identity that
makes the self-adjoint operator a *representation* of the form sum rather than one more form bound
for it. -/
theorem re_inner_diagSum (x : diagSub c) :
    (inner ℂ (x : L2 d) (diagSumLin c K x)).re
      = (inner ℂ (x : L2 d) (diagUnb c x x.2)).re + (inner ℂ (x : L2 d) (K (x : L2 d))).re := by
  rw [diagSumLin_apply, inner_add_right, Complex.add_re]

/-- The diagonal form of the symbol as a real series: the left summand of the sum form.  It is
finite on the operator domain (`summable_formTsum`) and signed, which is why the form cannot be read
as an `ℝ≥0∞`-valued series once the interaction is subtracted. -/
noncomputable def formTsum (c : Idx d → ℝ) (x : L2 d) : ℝ :=
  ∑' n : Idx d, c n * ‖x n‖ ^ 2

/-- **The operator's form is the diagonal series**: `re_inner_diagUnb` in the notation of the sum
form. -/
theorem formTsum_eq_re_inner_diagUnb {x : L2 d} (hx : memDom c x) :
    formTsum c x = (inner ℂ x (diagUnb c x hx)).re := (re_inner_diagUnb hx).symm

/-- **The weighted square-sum of the operator domain dominates the sign-free form series.**  For a
state of the operator domain the weighted squares are summable, and `|c n|‖x n‖²` is controlled by
`(|c n|‖x n‖)² + ‖x n‖²` — so the form series converges absolutely and the form is finite without
any boundedness of the symbol. -/
theorem summable_abs_symbol_mul {x : L2 d} (hx : memDom c x) :
    Summable fun n : Idx d => |c n| * ‖x n‖ ^ 2 := by
  have hnorm : Summable fun n : Idx d => ‖x n‖ ^ 2 := summable_normSq x
  have hterm : ∀ n : Idx d,
      |c n| * ‖x n‖ ^ 2 ≤ (1 / 2) * (‖(c n : ℂ) * x n‖ ^ 2 + ‖x n‖ ^ 2) := by
    intro n
    have hcm : ‖(c n : ℂ)‖ = |c n| := by simp
    have hsq : ‖(c n : ℂ) * x n‖ ^ 2 = |c n| ^ 2 * ‖x n‖ ^ 2 := by
      rw [norm_mul, hcm]
      ring
    have h2 : 2 * (|c n| * ‖x n‖) * ‖x n‖ ≤ (|c n| * ‖x n‖) ^ 2 + ‖x n‖ ^ 2 :=
      two_mul_le_add_sq _ _
    rw [hsq]
    nlinarith [h2, norm_nonneg (x n), abs_nonneg (c n)]
  exact Summable.of_nonneg_of_le (fun n => by positivity) hterm
    ((hx.add hnorm).mul_left (1 / 2))

/-- **The form series is summable on the operator domain.**  Absolute convergence gives it: the
real form of an unbounded symbol is finite exactly on the domain where the operator is defined. -/
theorem summable_formTsum {x : L2 d} (hx : memDom c x) :
    Summable fun n : Idx d => c n * ‖x n‖ ^ 2 :=
  Summable.of_norm_bounded (g := fun n => |c n| * ‖x n‖ ^ 2) (summable_abs_symbol_mul hx)
    (fun n => by
      have hnorm : ‖c n * ‖x n‖ ^ 2‖ = |c n| * ‖x n‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (‖x n‖))]
      rw [hnorm])

/-- **The form domain**: the states on which the diagonal form of the symbol is finite, stated
sign-free (`∑ |c n| ‖x n‖² < ∞`).  This is the domain the KLMN representation theorem attaches to a
closed form; for a diagonal symbol it contains the operator domain. -/
def formDom (c : Idx d → ℝ) (x : L2 d) : Prop :=
  Summable fun n : Idx d => |c n| * ‖x n‖ ^ 2

/-- **The operator domain is contained in the form domain** — the first half of the KLMN domain
inclusion, and the reason §5's interacting form is finite on every state it is evaluated on. -/
theorem memDom_subset_formDom {x : L2 d} (hx : memDom c x) : formDom c x :=
  summable_abs_symbol_mul hx

/-- Finite-support states are in the form domain, so the form domain is dense: it contains the
dense operator domain. -/
theorem dense_formDom (c : Idx d → ℝ) : Dense {x : L2 d | formDom c x} :=
  Dense.mono (fun _ hx => memDom_subset_formDom hx) (dense_diagSub c)

/-- **The diagonal form is bounded below by `θ` wherever the symbol is**: the form series of a
symbol bounded below is bounded below by `θ‖x‖²`, with no summability hypothesis beyond the
domain. -/
theorem formTsum_ge_of_le_symbol {θ : ℝ} (hle : ∀ n, θ ≤ c n) {x : L2 d} (hx : memDom c x) :
    θ * ‖x‖ ^ 2 ≤ formTsum c x := by
  have hsum : HasSum (fun n : Idx d => ‖x n‖ ^ 2) (‖x‖ ^ 2) := by
    have h := lp.hasSum_norm (E := fun _ : Idx d => ℂ) (p := (2 : ℝ≥0∞)) (by norm_num) x
    simpa using h
  have hshift : HasSum (fun n : Idx d => θ * ‖x n‖ ^ 2) (θ * ‖x‖ ^ 2) := hsum.mul_left θ
  have hcmp : (∑' n : Idx d, θ * ‖x n‖ ^ 2) ≤ ∑' n : Idx d, c n * ‖x n‖ ^ 2 := by
    refine hshift.summable.tsum_le_tsum (fun n => ?_) (summable_formTsum hx)
    have hn := mul_le_mul_of_nonneg_right (hle n) (sq_nonneg (‖x n‖))
    nlinarith [hn]
  rwa [hshift.tsum_eq] at hcmp

/-- **The form sum of a symbol bounded below by `θ` and a perturbation bounded below by `−σ` is
bounded below by `θ − σ`** on the operator domain.  This is the form-level version of §16's
gap, with the operator supplying the domain: the form sum is represented by a self-adjoint operator
*and* is bounded below on it. -/
theorem formSum_ge {θ σ : ℝ} (hθ : ∀ n, θ ≤ c n)
    (hK : ∀ x : L2 d, -(σ * ‖x‖ ^ 2) ≤ (inner ℂ x (K x)).re) (x : diagSub c) :
    (θ - σ) * ‖(x : L2 d)‖ ^ 2
      ≤ (inner ℂ (x : L2 d) (diagSumLin c K x)).re := by
  have h1 : θ * ‖(x : L2 d)‖ ^ 2 ≤ (inner ℂ (x : L2 d) (diagUnb c x x.2)).re := by
    have h := formTsum_ge_of_le_symbol hθ x.2
    rwa [formTsum_eq_re_inner_diagUnb x.2] at h
  have h2 := hK (x : L2 d)
  rw [re_inner_diagSum]
  have hexp : (θ - σ) * ‖(x : L2 d)‖ ^ 2 = θ * ‖(x : L2 d)‖ ^ 2 - σ * ‖(x : L2 d)‖ ^ 2 :=
    by ring
  rw [hexp]
  linarith

end FormSum

/-! ## 22. The Yang–Mills one-particle operator

§21 represented a form sum by a self-adjoint operator; this section does that for the form the
chapter is about.  The form of record is diagonal (`yangMillsForm_eq_diagonalForm`), so its symbol
is explicit:

`yangMillsSymbol T g n = N(n) + N(n)² + rootCount T · zeroPoint g (parallelDegree T n)`,

the occupation (kinetic degree), its square (the magnetic quartic) and Simon's transverse
zero-point barrier in the Cartan background.

* `yangMillsForm_eq_diagonalForm_symbol` — the form of record *is* the diagonal form of this
  symbol;
* **`yangMillsSymbol_form_eq_inner`** — the closed form of the symbol is the quadratic form of
  `diagUnb (yangMillsSymbol T g)` on the operator domain, and `yangMillsForm_closedForm_core` says
  the same on the Gauss–polynomial core, where that closed form *is* `q_W`.  This is the
  identification: the one-particle operator of the form of record is the diagonal operator, not
  merely one that dominates it formwise;
* `yangMillsSymbol_vacuum`, `yangMillsSymbol_ge`, `yangMillsSymbol_transverse` — the symbol's
  values: `rootCount T · zeroPoint g 0` at the vacuum, at least `2` more elsewhere, with equality at
  any transverse single excitation;
* **`yangMills_spectrum_subset`** — by §20 the spectrum is the closure of the symbol's range, so it
  holds no point strictly between the vacuum energy `rootCount T · g/(2√2)` and that value plus
  `2`, and `yangMills_vacuum_mem_spectrum` / `yangMills_gap_mem_spectrum` put both endpoints *in*
  the spectrum.  **The gap above the vacuum is exactly `2`**: the kinetic and magnetic degrees each
  contribute one, and the barrier shifts the whole spectrum, its vacuum value included, without
  touching the spacing — which is the spectral reading of `yangMillsForm_ge_gap`.

What this does **not** claim: that the coefficient-model form is the reduced Yang–Mills theory's
form, i.e. the BRST quotient `H/(exact ⊕ harmonic)`.  What is claimed, and proved in
`BookProof.YangMillsFormKLMN` §24, is the model-level statement that the **transverse sector's
magnetic slot is this diagonal one**: the sector is invariant under `diagUnb`
(`diagUnb_mem_reducedSector`), the barrier is the constant vacuum value there
(`yangMillsSymbol_on_sector`), and the gap `2` survives the restriction (`sector_gap`).  The
corresponding `a < 1` branch is §23 of the same file (`klmn`), which is the form-level
Kato–Rellich theorem this section's `T + K` (bounded `K`) is the `a = 0` case of.
-/

section YangMillsOperator

open BookProof.YangMillsEffectiveBarrier BookProof.ChapterUnitaryTransport

/-- **The symbol of the Yang–Mills form of record.** -/
noncomputable def yangMillsSymbol (T : Finset (Fin d)) (g : ℝ) (n : Idx d) : ℝ :=
  (∑ i, (n i : ℝ)) + (∑ i, (n i : ℝ)) ^ 2
    + rootCount T * zeroPoint g (parallelDegree T n)

/-- **The form of record is the diagonal form of its symbol** — `yangMillsForm_eq_diagonalForm`
with the symbol named, so that the operator and its spectrum can be written down. -/
theorem yangMillsForm_eq_diagonalForm_symbol (T : Finset (Fin d)) (g : ℝ) :
    yangMillsForm T g = diagonalForm (yangMillsSymbol T g) :=
  Barrier.yangMillsForm_eq_diagonalForm T g

theorem yangMillsSymbol_nonneg {g : ℝ} (hg : 0 ≤ g) (T : Finset (Fin d)) (n : Idx d) :
    0 ≤ yangMillsSymbol T g n := by
  have h1 : 0 ≤ ∑ i, (n i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg (n i)
  have h2 : 0 ≤ rootCount T * zeroPoint g (parallelDegree T n) :=
    mul_nonneg (rootCount_nonneg T) (zeroPoint_nonneg hg (parallelDegree_nonneg T n))
  simp only [yangMillsSymbol]
  nlinarith [sq_nonneg (∑ i, (n i : ℝ))]

/-- The transverse zero-point energy is monotone in the background occupation. -/
theorem zeroPoint_mono {g N N' : ℝ} (hg : 0 ≤ g) (h : N ≤ N') :
    zeroPoint g N ≤ zeroPoint g N' := by
  have hs : Real.sqrt (N + 1 / 2) ≤ Real.sqrt (N' + 1 / 2) := Real.sqrt_le_sqrt (by linarith)
  simp only [zeroPoint, transFreq]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hg) (by norm_num)

/-- A nonzero multi-index has positive occupation — the degree is the total number of
oscillator quanta. -/
theorem degree_pos_of_ne_zero {n : Idx d} (hn : n ≠ 0) : 1 ≤ ∑ i, (n i : ℝ) := by
  have hne : (∑ i, n i) ≠ 0 := by
    intro h
    refine hn (funext fun i => ?_)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le _)).mp h i
      (Finset.mem_univ i)
  have hpos : 1 ≤ ∑ i, n i := Nat.one_le_iff_ne_zero.mpr hne
  calc (1 : ℝ) ≤ ((∑ i, n i : ℕ) : ℝ) := by exact_mod_cast hpos
    _ = ∑ i, (n i : ℝ) := by rw [Nat.cast_sum]

/-- **The vacuum energy**: at the zero multi-index the occupation and the magnetic quartic vanish
and only the transverse barrier survives. -/
theorem yangMillsSymbol_vacuum (T : Finset (Fin d)) {g : ℝ} :
    yangMillsSymbol T g 0 = rootCount T * zeroPoint g 0 := by
  rw [yangMillsSymbol, parallelDegree]
  simp

/-- **Every non-vacuum mode costs at least the gap above the vacuum**: the kinetic and magnetic
degrees give `2`, and the barrier only adds to it. -/
theorem yangMillsSymbol_ge {g : ℝ} (hg : 0 ≤ g) {T : Finset (Fin d)} {n : Idx d} (hn : n ≠ 0) :
    rootCount T * zeroPoint g 0 + 2 ≤ yangMillsSymbol T g n := by
  have hdeg := degree_pos_of_ne_zero hn
  have hsq : (1 : ℝ) ≤ (∑ i, (n i : ℝ)) ^ 2 := by nlinarith [hdeg]
  have hbar : rootCount T * zeroPoint g 0 ≤ rootCount T * zeroPoint g (parallelDegree T n) :=
    mul_le_mul_of_nonneg_left (zeroPoint_mono hg (parallelDegree_nonneg T n)) (rootCount_nonneg T)
  simp only [yangMillsSymbol]
  linarith

/-- **A transverse single excitation attains the gap**: its occupation is one in the kinetic and
magnetic slots and zero in the Cartan background, so its barrier is the vacuum barrier. -/
theorem yangMillsSymbol_transverse {T : Finset (Fin d)} {i : Fin d} (hi : i ∉ T) {g : ℝ} :
    yangMillsSymbol T g (Function.update 0 i 1) = rootCount T * zeroPoint g 0 + 2 := by
  have hpar : parallelDegree T (Function.update (0 : Idx d) i 1) = 0 := by
    rw [parallelDegree]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    rw [Function.update_of_ne hji 1 (0 : Idx d)]
    simp
  have hdeg : ∑ j, ((Function.update (0 : Idx d) i 1) j : ℝ) = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Function.update_of_ne hji 1 (0 : Idx d)]
      simp
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  simp only [yangMillsSymbol, hpar, hdeg]
  ring

/-- **The vacuum energy is in the spectrum** — the symbol attains it at the zero multi-index. -/
theorem yangMills_vacuum_mem_spectrum (T : Finset (Fin d)) {g : ℝ} :
    (rootCount T * zeroPoint g 0) ∈ closure (Set.range (yangMillsSymbol T g)) :=
  subset_closure ⟨0, yangMillsSymbol_vacuum T⟩

/-- **The bottom of the excited spectrum is in the spectrum**: a transverse single excitation has
symbol value `rootCount T · zeroPoint g 0 + 2`, so the closure contains it. -/
theorem yangMills_gap_mem_spectrum {T : Finset (Fin d)} {i : Fin d} (hi : i ∉ T) {g : ℝ} :
    (rootCount T * zeroPoint g 0 + 2) ∈ closure (Set.range (yangMillsSymbol T g)) :=
  subset_closure ⟨Function.update 0 i 1, yangMillsSymbol_transverse (T := T) (g := g) hi⟩

/-- **The spectrum of the Yang–Mills one-particle operator has no point below the gap.**  §20 makes
the spectrum the closure of the symbol's range; the vacuum value is `rootCount T · zeroPoint g 0`,
every nonzero value is at least `2` above it, and `{B} ∪ [B + 2, ∞)` is closed, so the closure stays
inside it. -/
theorem yangMills_spectrum_subset {g : ℝ} (hg : 0 ≤ g) (T : Finset (Fin d)) :
    closure (Set.range (yangMillsSymbol T g))
      ⊆ ({(rootCount T * zeroPoint g 0)} ∪ Set.Ici (rootCount T * zeroPoint g 0 + 2)) := by
  refine closure_minimal ?_ (isClosed_singleton.union isClosed_Ici)
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst hn
    exact Or.inl (yangMillsSymbol_vacuum T)
  · exact Or.inr (yangMillsSymbol_ge hg hn)

/-- **The closed form of a nonnegative symbol is the `ofReal` of its real series** — the bridge
between the `ℝ≥0∞`-valued form of §5–§6 and the real form the operator supplies. -/
theorem closedForm_eq_ofReal_formTsum {f : Idx d → ℝ} (hf : ∀ n, 0 ≤ f n) {x : L2 d}
    (hfin : Summable fun n => f n * ‖x n‖ ^ 2) :
    closedForm f x = ENNReal.ofReal (formTsum f x) := by
  rw [closedForm, formTsum]
  symm
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hf n) (by positivity)) hfin]
  refine tsum_congr fun n => ?_
  rw [ENNReal.ofReal_mul (hf n)]

/-- **The Yang–Mills form of record is the quadratic form of the diagonal operator.**  On the
operator domain the closed form of `yangMillsSymbol` is `⟪x, diagUnb (yangMillsSymbol T g) x⟫`;
that operator is self-adjoint there (`diagSubLin_isSelfAdjointOn`).  This is the identification the
chapter's boundary recorded as missing: the one-particle operator is not an abstract `T` that the
form merely dominates — it is `diagUnb` of the form's own symbol. -/
theorem yangMillsSymbol_form_eq_inner {g : ℝ} (hg : 0 ≤ g) {x : L2 d}
    (hx : memDom (yangMillsSymbol T g) x) :
    closedForm (yangMillsSymbol T g) x
      = ENNReal.ofReal (inner ℂ x (diagUnb (yangMillsSymbol T g) x hx)).re := by
  rw [closedForm_eq_ofReal_formTsum (yangMillsSymbol_nonneg hg T) (summable_formTsum hx),
    formTsum_eq_re_inner_diagUnb hx]

/-- **On the Gauss–polynomial core the closed form *is* `q_W`**, so the identification above is an
identification of the chapter's form and not of a different one. -/
theorem yangMillsForm_closedForm_core {g : ℝ} (hg : 0 ≤ g) (T : Finset (Fin d))
    (c₀ : CoreCoeff d) :
    closedForm (yangMillsSymbol T g) (coreEmbed c₀) = ENNReal.ofReal (yangMillsForm T g c₀) := by
  rw [closedForm_coreEmbed (yangMillsSymbol T g) (yangMillsSymbol_nonneg hg T) c₀,
    ← yangMillsForm_eq_diagonalForm_symbol]

/-- **The Yang–Mills one-particle operator, in one statement.**  It is `diagUnb` of the form's
symbol, self-adjoint on the maximal domain; its spectrum — the closure of the symbol's range —
attains the vacuum energy `rootCount T · g/(2√2)` and has nothing in `(B, B + 2)`, with `B + 2`
attained at a transverse excitation.  The gap above the vacuum is `2`. -/
theorem yangMills_oneParticle {g : ℝ} (hg : 0 ≤ g) (T : Finset (Fin d)) :
    IsSelfAdjointOn (diagSub (yangMillsSymbol T g)) (diagSubLin (yangMillsSymbol T g)) ∧
      (rootCount T * zeroPoint g 0) ∈ closure (Set.range (yangMillsSymbol T g)) ∧
      closure (Set.range (yangMillsSymbol T g))
        ⊆ ({(rootCount T * zeroPoint g 0)} ∪
          Set.Ici (rootCount T * zeroPoint g 0 + 2)) :=
  ⟨diagSubLin_isSelfAdjointOn (yangMillsSymbol T g), yangMills_vacuum_mem_spectrum T,
    yangMills_spectrum_subset hg T⟩

end YangMillsOperator

end BookProof.YangMillsFormClosureND
