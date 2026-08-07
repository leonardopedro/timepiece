# Plan for the LLM–Lean 4 Specialist: Formalizing `Book/CoherentState.lean` and the Project

This is an execution plan for an LLM–Lean-4-specialist agent. It has two goals:

1. **Prove the claims of the new chapter `Book/CoherentState.lean`** (adapted from
   `coherent.md`, "The Coherent State of Attention") in `BookProof/`, keeping every
   theorem `sorry`-free and `axiom`-free.
2. **Improve the formalization of the whole project** by closing the remaining
   `EXTERNAL` named hypotheses and `True` placeholders that are realistic to prove
   in Mathlib v4.28.0.

Every new theorem must remain `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).

## Provenance of the new chapter (read before starting)

`Book/CoherentState.lean` is **original content**: unlike every other curated
chapter, it is **not** derived from a `book.tex` chapter. It is an *addition* of the
kind the project already records in `Contention.md` §"Additions" (A1–A8). Two
consequences:

- **The new mathematical claims are not author-supplied manuscript claims.** They
  come from `coherent.md` and standard physics. Treat the coherent-state overlap,
  the Softmax=Born-rule identity, the expectation-value packaging, and the
  temperature identity as claims to be **vetted as original mathematics**, not
  transcribed. Cross-check each against the physics literature (Bargmann–Fock
  reproducing kernel; quantum fidelity of displaced thermal states) before
  formalizing, and record any disparity between the claim and the proved theorem in
  `BookProof/STATUS.md` (the same honesty discipline `Issues.md` §3 applies to
  `newproof.md`).
- **The chapter is a new part of the curated narrative.** It sits in Part
  "Consciousness, Deep Learning, and the Bayesian Prior" alongside
  `AlignedDeepLearning`; it extends the deep-learning thread
  (`book.tex:9606-10535`, which `Contention.md` S9 records as absent from the prose
  until now). The `BookProof` anchors it reuses are already proved; the new
  deliverables (Part A) are the only genuinely new formal content.

## Toolchain and scope constraints (from `Issues.md`)

- **Do NOT attempt the verso-blueprint migration.** `Issues.md` §0 records it as a
  `[BLOCKER]`: verso-blueprint requires Lean ≥ v4.29.0 while this project, Mathlib,
  Verso, and the whole `BookProof` library are pinned to **v4.28.0**. Keep the
  working Verso v4.28.0 manual as the deliverable. New chapters use the existing
  `:::paragraph` prose + plain `#check` code-block convention (they do **not**
  elaborate, so they do not slow the book build).
- **Keep `#check` types short.** `Issues.md` §4 records a `[CRITIQUE]` that some
  headline `#check` types render unwieldily. For the new coherent-state theorems,
  prefer a short prose paraphrase directly above each `#check` block, and state clean
  `example`s (not only `#check`) where the elaborated type is long.
- **Do not edit `lakefile.toml` `[leanOptions]`** (the book build is sensitive).
- **Do not touch P≠NP / Riemann-Hypothesis work** (`PnpProof/`, `RiemannProof/`).

## Environment (do not change without coordination)

- Toolchain: `leanprover/lean4:v4.28.0`; Mathlib `v4.28.0` (see `lean-toolchain`).
- Adding `EXTERNAL` named *hypotheses* is allowed by design (never `axiom`). A
  named `EXTERNAL` hypothesis is a genuine, documented gap; proving it *within*
  Mathlib upgrades it to a theorem.
- Verify with:
  ```bash
  export PATH="/home/leo/.elan/bin:$PATH"
  cd /home/leo/Projects/timepiece
  lake build BookProof
  lake build book
  grep -rn "sorry" BookProof/           # expect only RandomMap/SchoenfeldPRA.lean:162,176
  grep -rn "^axiom" BookProof/ PnpProof/ # expect empty
  ```
- Register new files in `BookProof.lean`. Do **not** edit `lakefile.toml`
  `[leanOptions]` (the book build is sensitive to `experimental.module` /
  `autoImplicit` / `maxSynthPendingDepth`).
- Do not touch P≠NP / Riemann-Hypothesis work (`PnpProof/`, `RiemannProof/`) —
  out of scope by the author.
- Every new headline needs a `#check` block added to the corresponding `Book/*.lean`
  chapter, and a dated wave note in `BookProof/STATUS.md`.

---

## Part A — Formalize `Book/CoherentState.lean` (the new chapter)

The chapter `Book/CoherentState.lean` (adapted from `coherent.md`) argues that
Softmax attention is the Born rule applied to coherent states. Most of the chapter
is *already* backed by existing `BookProof` theorems (Gaussian, Born rule, kernel
transport, Bayesian update, hierarchical collapse). The **new, unproved** content
is the coherent-state identities. These are the deliverables of this part, in
priority order. Each is a self-contained, finite/complex-analytic statement.

### A.1 — The coherent overlap is the Gaussian reproducing kernel `ChapterCoherentOverlap`

**Claim (chapter §"The Geometry of the Wave-packet"):** for two vectors
$`q, k \in \mathbb{C}^n` (or `\mathbb{R}^n`), the coherent-state overlap is

$$`\langle q | k \rangle = \exp\!\Big(-\tfrac12\|q\|^2 - \tfrac12\|k\|^2 + q \cdot k\Big),`$$

the reproducing kernel of the Bargmann–Fock space.

**Prove (real case first):** over `EuclideanSpace ℝ (Fin n)` (reusing the
`WithLp 2` structure of `BookProof/ChapterFreeFieldGaussian.lean`), define
`coherentOverlap q k : ℝ := Real.exp (-‖q‖²/2 - ‖k‖²/2 + inner q k)` and prove
the multi-dim law `inner`/`‖·‖²` identities:
`‖q‖² = ∑ i, q i * q i`, `inner q k = ∑ i, q i * k i`, and the identity
$`\|q - k\|^2 = \|q\|^2 + \|k\|^2 - 2\,q\cdot k` (`norm_sub_sq_real`). The
overlap is then the Gaussian $`e^{-\frac12\|q-k\|^2 - q\cdot k}` form or the
flagged form above; give whichever is cleanest and state the equivalence.

**Deliverables:**
- `coherentOverlap_eq` (the explicit sum formula);
- `coherentOverlap_pos` ($`\langle q|k\rangle > 0` for real vectors);
- `coherentOverlap_unit` ($`\langle q|q\rangle = 1` when $`\|q\|=1`).

**Definition of done:** theorems `sorry`-free, `axiom`-free; `lake build BookProof`
green; `#check` added to `Book/CoherentState.lean` §"The Geometry of the
Wave-packet".

### A.2 — Softmax is the Born rule on coherent states `ChapterSoftmaxBorn` (HEADLINE)

**Claim (chapter §"Softmax Is the Born Rule on Coherent States"):**

$$`|\langle q | k_j \rangle|^2 = \exp(-\|q\|^2)\cdot\exp(-\|k_j\|^2)\cdot\exp(2\,q\cdot k_j),`$$

and, after normalizing across the keys and cancelling the $`q`- and (normalized)
$`k_j`-norm factors,

$$`\text{Attention Weight}(j) = \frac{\exp(2\,q \cdot k_j)}{\sum_l \exp(2\,q \cdot k_l)}.`$$

**Prove,** over real vectors, as a finite `Finset` identity:
- `coherentBorn_j = expOverlap j / ∑ l, expOverlap l` where
  `expOverlap j = exp(-‖q‖² - ‖k_j‖² + 2 * inner q (k_j))` (real numbers, indices
  `Fin m`).
- Prove the normalization identity: because $`\exp(-\|q\|^2)` is independent of
  $`j`, it factors out of the sum and cancels:
  `coherentBorn_eq_softmax` — if every key is normalized
  ($`\|k_j\|^2 = \|k\|^2` constant, e.g. all equal norm), then
  `coherentBorn j = softmax 2 q k j := exp (2 * inner q (k_j)) / ∑ l, exp (2 * inner q (k_l))`.
- The algebra is `Finset.sum_div` / factoring a constant out of a sum
  (`Finset.mul_sum`, `Finset.sum_mul`, `Real.exp_zero`, `Real.exp_add`,
  `Real.exp_mul`). No analysis needed — it is a finite identity with a fixed
  constant norm assumption.

**Deliverables:**
- `coherentBorn_sq_eq` (the three-factor split $`|\langle q|k\rangle|^2`);
- `coherentBorn_cancel_q` (the $`\exp(-\|q\|^2)` factor cancels);
- HEADLINE `coherentBorn_eq_softmax` — **Softmax = Born rule**, under constant key
  norm.

**Definition of done:** headline `coherentBorn_eq_softmax` `sorry`-free,
`axiom`-free; `#check` added to the chapter's headline section.

### A.3 — The expectation value of the observable is the attention output `ChapterObservableExpectation`

**Claim (chapter §"The Posterior: Observable Operators and Expectation Values"):**
the attention output $`\mathbf{o}_i = \sum_j a_{ij}\mathbf{v}_j` equals the
expectation value of the observable operator $`\hat V = \sum_j \mathbf{v}_j
|k_j\rangle\langle k_j|` over the posterior distribution $`a_{ij}`.

**Prove** the finite core: for a probability distribution $`p_j \ge 0` with
$`\sum_j p_j = 1` and arbitrary values $`\mathbf{v}_j : \mathbb{R}^d` (or `ℂ`),
define the weighted mean $`\sum_j p_j \mathbf{v}_j` and prove:
- `prob_weighted_sum_eq` — it is a convex combination lying in the convex hull of
  the $`\mathbf{v}_j`;
- it reduces to the ordinary expectation when $`\mathbf{v}` is scalar-valued
  (`Finset.sum` of $`p_j v_j`), matching `BookProof/ChapterBayesInference`'s
  `posterior` and `ChapterConditional`'s $`pMarg`-weighted identities.

This is mostly a *re-framing* of already-proved facts; the new content is packaging
the output as an expectation value. Deliverable `attention_eq_expectation`.

### A.4 — The temperature identity `ChapterCoherentTemperature` (documented, optional)

**Claim (chapter §"Temperature and the Thermal Bath"):** $`\tau = \bar n + \tfrac12`,
with $`\bar n` the mean occupation of a displaced thermal state and $`\tfrac12` the
zero-point energy.

**Status: PROOF-PLAN ONLY.** This is a genuine thermal/statistical-mechanics
computation (quantum fidelity of displaced thermal states). It requires a
finite-dimensional displaced thermal state model and the quantum-fidelity overlap.
Do **not** attempt a full physical derivation; instead, if attempted, prove the
*finite-core* algebraic identity: for a geometric occupation distribution
$`\mathrm{Pr}(n) \propto (\bar n/(\bar n+1))^n`, the mean
$`\sum_n n\,\mathrm{Pr}(n) = \bar n` and the variance is $`\bar n + \bar n^2`,
relating the "extra half" to the Heisenberg-floor of a coherent state. If this is
out of reach, keep the chapter's claim as a documented proof plan (it already is),
and do not `sorry` it.

---

## Part B — Improve the whole-project formalization (existing `BookProof` gaps)

These are the open items from `PLAN_LEAN_SPECIALIST_UNPROVED.md` and
`BookProof/STATUS.md` that remain realistic. Work them **after** Part A.

### B.1 — Close the Mehler tail-split `sorry` (one remaining real gap)

`BookProof/ChapterSolovayCoordinates.lean:85`, theorem `tailSplitEquiv_map`: the
infinite Mehler coordinate measure, split by `tailSplitEquiv k : (ℕ → ℝ) ≃ᵐ
(Fin k → ℝ) × (ℕ → ℝ)`, equals the product of the finite Gaussian head and the
infinite tail. Use `MeasureTheory.Measure.infinitePi` / `pi_congrLeft` and the sum
decomposition `Equiv.sumPiEquivProdPi`. **Deliverable:** no `sorry`. (This is the
*only* remaining real `sorry` in the new code; the Mehler uniqueness half
`mehler_unique_by_finite_marginals` — `Issues.md` §7's open item (i) — is already
proved in `ChapterMehlerUniqueness.lean`, so it needs only a `#check` confirmation,
not new work.)

### B.2 — `Book/AlignedDeepLearning.lean` and `Book/CoherentState.lean` cross-checks

The new chapter reuses `BookProof/ChapterKernelTransport`,
`ChapterBayesInference`, `ChapterConditional`, `ChapterHierarchicalBayes`,
`ChapterSequentialBayes`, `ChapterFreeFieldGaussian`, `ChapterEulerNState`,
`ChapterBornPhaseFiber`. Verify each `#check` in `Book/CoherentState.lean` is
`#print axioms`-clean and `sorry`-free; if any is a placeholder, prove it.

### B.3 — Promote realistic `EXTERNAL` hypotheses to theorems

From `PLAN_LEAN_SPECIALIST_UNPROVED.md` Priority 4 (Mathlib v4.28.0 has the
ingredients):
- **Schur's lemma, finite-dimensional** — `BookProof/ChapterA2`; discharge via
  `BookProof/ChapterSchurFiniteDim.schur_scalar_of_irreducible` (already proved);
  remove the `EXTERNAL` flag on that concrete instance.
- **Pauli's fundamental theorem of γ-matrices** — `BookProof/ChapterA3b`; the
  concrete `4×4` commutant-is-scalar is already proved in
  `BookProof/ChapterGammaCommutant.gamma_commutant_scalar`; remove the `EXTERNAL`
  flag on that concrete case.
- **Weyl complete reducibility, finite-dimensional** — keep `N = 2` (proved) and
  add `N = 3` as a concrete witness; stop (STOP RULE #1, `N = 6`).

Do **not** attempt (keep as named `EXTERNAL` hypotheses): Wigner/Mackey
imprimitivity, Varadarajan Thm 6.12, `levy_paths_nowhere_differentiable`,
`CrouzeixBound`.

### B.4 — `BookProof/ChapterSelectingEvents.lean`: the abstract measure-theoretic layer

This is specialist-plan Task C2 and `Issues.md` §7's second remaining non-deferred
gap: the **abstract** layer of `book.tex` §3 for arbitrary standard measure spaces,
beyond the finite-dimensional algebraic core already covered by `Book/ConditionalUnitary`.
The three `True` placeholders in `ChapterSelectingEvents` are all measure-theoretic
(Mathlib `condExpKernel` / `Measure.disintegrate` / commutative-von-Neumann
machinery), not new mathematics:
- `selecting_events_not_rewriting_history` — the regular conditional probability
  equals the quotient $`\mu(F \mid E) = \mu(E \cap F)/\mu(E)` via
  `ProbabilityTheory.cond` / `cond_apply`.
- `exists_regular_conditional_probability` — genuine existence via
  `condExpKernel` / `Measure.disintegrate` on a standard Borel space.
- `vonNeumann_abelian_classification` — the identification of a commutative von
  Neumann algebra on a separable Hilbert space with `L∞(X,μ)`; this is the deepest
  of the three (`Issues.md` notes `ChapterAbelianVonNeumannFinite` already proves the
  finite abelian case `commutant_eq_range_conjDiagonal`; extend or cite it, and keep
  the full infinite von-Neumann-algebra theorem as a documented gap if out of reach).
Also `exists_continuous_atomic_decomposition` — via
`MeasureTheory.Measure.lebesgueDecomposition` (continuous + atomic parts).

Give at least the two conditional-probability items real (non-`True`) conclusions;
keep the full von-Neumann `*`-isomorphism classification as a documented gap if it
is not reachable in Mathlib v4.28.0.

---

## Definition of done (whole wave)

1. `Book/CoherentState.lean` builds (it already does) and its new `#check` blocks
   elaborate.
2. Part A: `ChapterCoherentOverlap`, `ChapterSoftmaxBorn` (HEADLINE
   `coherentBorn_eq_softmax`), `ChapterObservableExpectation` all `sorry`-free /
   `axiom`-free, registered in `BookProof.lean`, and `#check`-ed in the chapter.
   `A.4` remains a documented proof plan (no `sorry`).
3. Part B: `tailSplitEquiv_map` has no `sorry`; the two `EXTERNAL` flags are removed
   on the concrete Gamma-commutant and finite Schur cases `BookProof/ChapterSelectingEvents`
   `selecting_events_not_rewriting_history` and `exists_regular_conditional_probability`
   (and `exists_continuous_atomic_decomposition`) get real (non-`True`) conclusions;
   the von-Neumann `*`-classification item is either proved or explicitly retained as
   a documented gap.
4. `lake build BookProof` and `lake build book` green; the only `sorry`s in the
   repository are `RandomMap/SchoenfeldPRA.lean:162,176` (intentional).
5. `#print axioms` spot-checks on every new headline show only `propext`,
   `Classical.choice`, `Quot.sound`.
6. `BookProof/STATUS.md` updated with a dated wave note, including any recorded
   disparity between each new coherent-state claim and the proved theorem (per the
   provenance note above).

## Execution guidance

- Work the queue **in order** (Part A before Part B), landing several deliverables
  per pass (author mandate: target ≥ 4 deliverable groups per pass).
- Do not add another instance of an already-general result (the dimension-count
  thread is closed at `N = 6`).
- Keep every theorem `sorry`-free / `axiom`-free. Where a full claim is out of
  reach, state the provable core precisely and record the gap in
  `BookProof/STATUS.md` / `FORMALIZATION_ROADMAP.md`; never `sorry` a strong claim.
- Prefer `EXTERNAL` named hypotheses over `axiom` for the deep external theorems.