# PLAN_LEAN_SPECIALIST_QYM_FLOW.md — Quantum Yang–Mills: the Friedrichs route

This is the plan item requested by `CONSOLIDATED_PLAN.md` §11.3 ("Suggested next
step"), in the style of `PLAN_LEAN_SPECIALIST_NS_FLOW.md`: Part A the Weyl-gauge
fiber, Part B the quadratic form and its closure, Part C the Friedrichs extension
as a **named theorem, never an axiom**, Part D the Hashimoto/SIRK limit.

**Status (2026-08-17, second pass): Parts A–C executed; Part C is now also
*discharged by construction* in the bounded regime, and Part D.4 is proved there
rather than left as prose.  See the new rows C.5–C.7 and D.5–D.8 below, in
`BookProof/ChapterYangMillsFriedrichsLimit.lean`.**

**Status (2026-08-17): executed, with one item deliberately left unstated.**
Parts A–C and the proved half of Part D are in
`BookProof/ChapterYangMillsFriedrichs.lean`, `sorry`-free and `axiom`-free,
registered in `BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`
and cited from `Book/YangMillsQuantization.lean`.  The Part D *identification of
the SIRK limit with the Friedrichs extension* remains a research conjecture and is
recorded in prose only (see the note at the end of Part D).

## The setting

The 3D gauge-fixed Yang–Mills Hamiltonian (`book.tex` ~7037–7120) is, in the Weyl
gauge and the Hermite basis, a **sum of squares** of the self-adjoint electric- and
magnetic-field operators,

```
H = ½ Σ (πⁱ_a)² + ½ Σ (B_{i a})²,
```

hence symmetric and bounded below by `0`.  `BookProof/ChapterWeylHamiltonian.lean`
already proves this for *bounded* fields (`weylHamiltonian_isPositive`); the
Friedrichs route needs the densely defined version.

## Part A — the Weyl-gauge Hamiltonian on a domain

| Item | Lean name | Status |
| :-- | :-- | :--: |
| A.1 `H = ½Σπᵢ² + ½ΣBₐ²` as an operator on an invariant domain | `weylOpDom`, `weylOp`, `weylOp_apply` | PROVED |
| A.2 symmetry on the domain | `weylOpDom_symmetricOn` | PROVED |
| A.3 the quadratic form is the sum of squares `½Σ‖πᵢx‖² + ½Σ‖Bₐx‖²` | `weylOpDom_quadForm` | PROVED |
| A.4 semi-boundedness (`H ≥ 0`), the hypothesis of Friedrichs | `weylOpDom_quadForm_nonneg` | PROVED |
| A.5 (already in the repository) the bounded case | `BookProof.WeylHamiltonian.weylHamiltonian_isPositive` | PROVED |

## Part B — the quadratic form and its closure

For an arbitrary symmetric positive `H` on a domain `D`:

| Item | Lean name | Status |
| :-- | :-- | :--: |
| B.1 the form `⟪x,y⟫_H = ⟪x,y⟫ + ⟪x,Hy⟫` and the form norm | `formInner`, `formNormSq`, `formNormSq_eq` | PROVED |
| B.2 the form is Hermitian | `formInner_conj_symm`, `re_formInner_swap` | PROVED |
| B.3 it dominates the ambient norm (`‖x‖² ≤ ‖x‖_H²`), hence is an inner product | `formNormSq_ge_normSq`, `formNormSq_nonneg` | PROVED |
| B.4 the expansions `‖x+y‖_H²`, `‖x−y‖_H²`, `‖x+ty‖_H²` | `formNormSq_add`, `formNormSq_sub`, `formNormSq_add_smul` | PROVED |
| B.5 **Cauchy–Schwarz** for the form | `re_formInner_sq_le` | PROVED |
| B.6 **closability of the form** — the analytic heart of the Friedrichs construction | `form_closable` | PROVED |
| B.7 the Weyl-gauge form is closable | `weylForm_closable` | PROVED |

B.6 says: if `xₙ` is Cauchy in the form norm and `xₙ → 0` in the ambient space,
then `‖xₙ‖_H → 0`.  Symmetry and positivity of `H` are exactly what the proof
uses; without closability the "closed form" of the Friedrichs construction would
not be well defined.

## Part C — the Friedrichs extension as a named theorem

| Item | Lean name | Status |
| :-- | :-- | :--: |
| C.1 what a positive self-adjoint extension *is* (domain, agreement, symmetry, positivity, adjoint condition) | `IsPositiveSelfAdjointExtension` | DEFINED |
| C.2 the Friedrichs theorem as an explicit hypothesis, applied | `friedrichs_extension_of_semibounded` | PROVED (hypothesis named) |
| C.3 the hypothesis is satisfiable (everywhere-defined case) | `friedrichs_hypothesis_satisfiable` | PROVED |
| C.4 the conclusion for the Weyl-gauge Hamiltonian, conditional on C.2 | `weyl_friedrichs_extension` | PROVED |
| C.5 the Friedrichs hypothesis **discharged by construction** for bounded operators on a dense domain | `friedrichs_of_bounded` | PROVED |
| C.6 symmetry and positivity pass from a dense domain to the whole space | `symmetricOn_top_of_dense`, `quadForm_top_nonneg_of_dense` | PROVED |
| C.7 the construction applies to a genuinely **proper** dense domain (in `ℓ²(ℕ,ℂ)`) | `friedrichs_bounded_proper_domain_example`, `not_mem_span_of_repr_ne_zero` | PROVED |

C.5–C.7 live in `BookProof/ChapterYangMillsFriedrichsLimit.lean`.  They do not
remove the named hypothesis of C.2 for *unbounded* operators — that remains the
honest boundary — but they show it is not an empty assumption: on the bounded
class the extension is built, not assumed, and the domain may be a proper dense
subspace.

References for C.2: K. Friedrichs, *Spektraltheorie halbbeschränkter Operatoren*,
Math. Ann. **109** (1934) 465–487; M. Reed & B. Simon, *Methods of Modern
Mathematical Physics*, Thm X.23.  It is a hypothesis, never an `axiom`.

## Part D — the Hashimoto/SIRK limit

| Item | Lean name | Status |
| :-- | :-- | :--: |
| D.1 the order-`n` Krylov best-approximation error is antitone in the order | `weylKrylov_bestApprox_antitone` | PROVED |
| D.2 for a cyclic seed the error tends to `0` | `weylKrylov_bestApprox_tendsto_zero` | PROVED |
| D.3 the numerical ranges of the SIRK orders nest (already in the repository) | `BookProof.ChapterH9.sirk_numRange_nested_orders` | PROVED |
| D.4 *the infinite Hashimoto limit selects the Friedrichs extension* | — | **CONJECTURE in general; PROVED in the bounded regime, D.8** |
| D.5 the Krylov projections converge strongly to the identity for a cyclic seed | `krylov_starProjection_tendsto` | PROVED |
| D.6 the SIRK compressions `Pₙ A Pₙ` of a bounded operator converge strongly to `A` | `sirkCompression`, `sirk_compression_tendsto` | PROVED |
| D.7 the limit is unique: no other bounded operator agrees with it on the Krylov flag | `sirk_limit_unique` | PROVED |
| D.8 **D.4 in the bounded regime**: the Hashimoto limit *is* the positive self-adjoint extension | `sirk_limit_eq_positive_selfadjoint_extension`, `weyl_friedrichs_bounded` | PROVED |

D.5–D.8 (also in `BookProof/ChapterYangMillsFriedrichsLimit.lean`) construct the
missing limit operator under a boundedness hypothesis and identify it with the
extension of C.5, so D.4 is a theorem there.  The unbounded continuum case is
still open.

On D.4: the identification of the limit operator requires the limit of the Krylov
flag as an operator, which is not constructed here (it *is* constructed in the
bounded regime, D.5–D.8).  Every naive Lean rendering of
the sentence is either trivially true (any two extensions agree on the original
domain by definition) or presupposes that missing construction, so the item is
recorded in prose in the module docstring rather than written as a theorem.

## Honest boundary (unchanged from `CONSOLIDATED_PLAN.md` §11.3)

* **Not claimed:** self-adjointness of the continuum Yang–Mills operator on
  `L²(ℝ⁹⁹ × ℤ₂³¹)`, the mass gap, or global existence.  The Yang–Mills existence
  and mass-gap Millennium problem is out of scope; the book's own statement is a
  conditional ("if the Hamiltonian is positive-definite then … with or without a
  mass gap").
* The Friedrichs theorem for the continuum operator is a *named* theorem, in the
  same honesty class as Strichartz (§10) and the continuum Faris–Lavine
  inequalities of the Navier–Stokes thread.
* D.4 is a research item, not a plan deliverable.
