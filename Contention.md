# Contention: Message Differences Between `book.tex` and `Book/`

This document identifies, describes, and localizes the significant differences in
*message* (thesis, scope, emphasis — not prose style) between the source manuscript
`book.tex` and the curated Lean/Verso chapters in `Book/`. Line references are given
as `book.tex:L` or `Book/Foo.lean:L`. Differences that change what is claimed are
marked **DIVERGENCE**; differences that only narrow scope are marked **SCOPE**.

## How to read the map

The curated book is not a translation of `book.tex` chapter-by-chapter. It is a
re-selection organized into parts (`Book.lean`). The mapping below shows which
`book.tex` chapters feed which curated chapters, and which are absent.

| `book.tex` chapter (line) | Curated counterpart(s) | Status |
| :--- | :--- | :--- |
| Introduction (124) | `Book/Introduction.lean` | SCOPE — heavily condensed |
| ODE `x'=x²` (932) | `Book/OdeSingularity.lean` (+ ProofPlans A) | Deliberately expanded/reframed |
| Wave-function parametrization (1238) | DutchBook, SequentialBayes, MaxEntropy, TotalVariance, ProbabilityClock, BornReproduces, BornFiber, ConditionalUnitary | Distributed across Parts I–II |
| Gauge symmetry & dissipative dynamics (2128) | ConditionalUnitary (parametrization half only) | Mostly dropped |
| Reconstructing classical trajectory (2494) | `Book/TrajectoryReconstruction.lean`, DeterministicTransformations, TimeTranslationStochastic | Re-allocated |
| Wave-function collapse vs Euler (3229) | CollapseKeepsKolmogorov, EulerGeneric, SternGerlach, DoubleSlit, BellInequalities, EPRComplete, ClassicalLimit | Faithful (recently aligned) |
| Free field / Navier–Stokes (3699) | `Book/FreeField.lean` (measure-theoretic core only) | Physics dropped |
| Real representations / CPT / position op. (4218) | — (formalized in BookProof, unimported) | Absent from prose |
| Quantization / Yang–Mills (6486) | — | Absent |
| Timepiece & Gribov ambiguity (7125) | — | Absent |
| Physical parity & antiparticles (7522) | — (BookProof only) | Absent from prose |
| Diffeomorphisms & gravity (7881) | — | Absent |
| Selecting events (8303) | `Book/PaFreeHilbert.lean` | Deliberate replacement |
| Consciousness as Bayesian prior (9122) | `Book/NullMeasure.lean` (single lemma) | Nearly all dropped |
| Entropy & irreversible evolution (9474) | Irreversibility, BijectionProbability, BaryonAsymmetry, MeasurementLLN | Core kept, framing changed |
| Aligned deep learning (9606) | — | Absent |
| Statistical Model Theory / RH (10536) | `Book/SolovayTensor.lean`, PaFreeHilbert | Deliberate replacement |

## Divergences (the message changes)

### D1. The introduction reverses the manuscript's caveat about what QM generalizes
- `book.tex:665-667, 883-886` twice states QM "is a generalization of classical
  statistical mechanics **(but not of probability theory)**".
- `Book/Introduction.lean:250-252` states "quantum mechanics is *what probability
  theory looks like* when you parametrize the simplex by the sphere".
- The book's slogan drops the explicit caveat and reads as a claim about probability
  theory itself. The caveat is preserved *in one specific chapter*
  (`Book/DeterministicTransformations.lean:82-94`), so the introduction and that
  chapter disagree with each other about the correct slogan.

### D2. ODE chapter overclaims that both blow-up problems are resolved
- `book.tex:1213-1220` explicitly disavows a full fix: the method "solves the first
  problem … but it is **not completely satisfactory** for the second problem"
  (degenerate solutions), and "does not allow for such a choice".
- `Book/OdeSingularity.lean:45-48` says "The manuscript's central claim is that
  *both problems are resolved by admitting a finite amount of uncertainty in the
  initial condition*." The chapter lists degeneracy as a problem (29-35) but never
  reports that the manuscript itself concedes the method fails to fully fix it.

### D3. ODE essential self-adjointness strength reduced
- `book.tex:1088-1093` asserts analytic essential self-adjointness ("using `H²` as a
  positive auxiliary operator in Corollary 1.1") and that "the unitary time-evolution
  `U(t)` is uniquely defined".
- `Book/OdeSingularity.lean:116-120` proves self-adjointness only at the algebraic
  certificate layer and defers "a future analytic realization on a Hilbert space"
  (also ProofPlans A.1-A.2). The change in strength is disclosed, but the central
  claim is weakened.

### D4. "QM is the most general formalism" softened to "generalizes statistical mechanics"
- `book.tex:2213-2214`: "The quantum formalism is the most general formalism whenever
  there is a conserved probability".
- `Book/DeterministicTransformations.lean:82-94` narrows this to "quantum mechanics
  generalizes classical statistical mechanics … not of probability theory itself",
  and `ConditionalUnitary.lean:26-27` / `SymmetryRep.lean:85-87` restate it as "more
  general than Markov".

### D5. The Navier–Stokes existence/uniqueness thesis is dropped entirely
- `book.tex:4139-4216` builds the full NS Hilbert space `Γ^s ⊗ Γ^a`, graded Lie
  superalgebra, BRST charge `Ω = ∫ u_{j,j}ψ†`, and closes with "we proved the
  solution to Navier–Stokes exists and is unique".
- No `Book/` chapter carries any of it. `BookProof/ChapterNavierStokes.lean:48-52`
  explicitly declares the existence/uniqueness claim "field-theoretic modelling that
  is out of scope", formalizing only the fermionic-ghost algebra. The headline claim
  is lost, not merely deferred.

### D6. Weak holomorphicity lemma weakened to the pointwise case
- `book.tex:4104-4131` invokes the weak/distributional version: locally integrable +
  CR weakly ⇒ analytic a.e. (Weyl-like).
- `BookProof/ChapterHolomorphic.lean:15-44` states that version is "not available in
  Mathlib" and proves only the strong pointwise `cauchyRiemann_iff_analyticOn`. The
  manuscript's exact claim is weakened (this file is not imported by any `Book/`
  chapter).

### D7. The "arrow of time is due to unitarity" thesis is reframed to dissipation
- `book.tex:9476-9479, 9493-9497`: the arrow of time is "due to unitarity, not
  entropy".
- `Book/Irreversibility.lean:64-85` attributes the arrow to continuum/dissipation
  (set theory), not to unitarity; the unitary "random sampling" connection
  (`book.tex:9477, 9527-9533`) is dropped from the curated chapters.

### D8. The consciousness thesis is reduced to a single null-measure lemma
- `book.tex:9367-9437`: consciousness is "a Turing machine running a program that
  symbolically defines/manipulates a Bayesian prior"; `9439-9473` explains AI
  hallucination/misalignment as user-vs-machine prior incompatibility.
- Only the sub-claim "a point with null measure is not necessarily special"
  (`book.tex:9174-9180`) survives, formalized in `Book/NullMeasure.lean:16-18, 30-32,
  78-84`. The definition of consciousness and the hallucination thesis are absent.

### D9. The manuscript's RH claim is discarded, keeping only the metamathematical motivation
- `book.tex:10665-10673`: RH is true *relative to a prior* — "The hypothesis that the
  Möbius function is related with a random walk implies the Riemann hypothesis".
- `Book/PaFreeHilbert.lean:11, 198-207` and `Book/SolovayTensor.lean` replace it with
  the unselectability/decidability story and explicitly flag the anti-PA-leakage
  reading as interpretation, not theorem. The Möbius-iid-prior ⇒ RH construction and
  the "Statistical Model Theory" apparatus (`book.tex:10554-10616`) are absent.

## Scope selections (message narrowed, not reversed)

### S1. Infinite-dimensional parametrization theorem retracted to a finite core
- `book.tex:1468-1474, 1489-1527` state the unitary-parametrization theorem for all
  standard measure spaces (including continuous parts).
- `Book/ConditionalUnitary.lean:188-202` verifies only the finite-index core and
  records the continuous layer as proof plans. Honest, but the proven scope is
  retracted.

### S2. Gauge-as-exact-constraint apparatus dropped
- `book.tex:2130-2134, 2374-2386`: gauge symmetries implementable as exact
  constraints *without null measure* (via Haar pushforward).
- No curated chapter carries the constraint-solving half; `ConditionalUnitary.lean`
  keeps only the parametrization half, and "gauge" is reused for the phase/sign
  ambiguity (`BornFiber.lean:62-79`).

### S3. Dissipative dynamics, BRST quantization, gauge-fixing, locality all dropped
- `book.tex:2183-2220` (damped oscillators), `2291-2400` (gauge-fixing, Gribov, BRST,
  Dirac brackets), `2402-2452` (L²(ℝ²×ℤ₂) ghost/BRST worked example), `2454-2488`
  (discretization vs locality): none appear in any `Book/` chapter.

### S4. The deterministic-theory (PRNG) construction dropped
- `book.tex:2951-3041` gives an affirmative answer to "does a deterministic theory
  compatible with QM exist?" (inverse-transform sampling, seed-based generation).
  No curated counterpart exists. The manuscript partly disowns it itself
  (`book.tex:3021-3023`).

### S5. Time-metaphysics replaced by a probability statement
- `book.tex:2508-2547, 3047-3056` frame the chapter's puzzle in presentism/eternalism/
  possibilism terms; `Book/TrajectoryReconstruction.lean:145-152` translates this into
  "selecting events is not rewriting history". Deliberate reframing, narrower.

### S6. "Unitary inference" methodology pitch dropped
- `book.tex:1347-1389` proposes a *named method* ("unitary inference"), its
  basis-change advantage, and the entropy disclaimer. The curated chapters prove the
  unitary model but never present the method as a selling point.

### S7. Field-operator physics dropped from the free-field chapter
- `book.tex:3880-4010` (Fock operators, wavelets, momentum-constraint identities),
  `4000-4008` (non-polynomial Hamiltonians), `4061-4102` (mass gap / Yang–Mills),
  `4134-4216` (Navier–Stokes) are absent from `Book/FreeField.lean`, which keeps only
  the no-Lebesgue-measure obstruction → Gaussian → uniform sphere construction.

### S8. Four whole QFT/gravity chapters absent from the narrative
- Yang–Mills/CSFT quantization (`book.tex:6486-7124`), Gribov ambiguity
  (`7125-7521`), physical parity/antiparticles (`7522-7880`), diffeomorphisms and
  gravity (`7881-8302`) have **no** `Book/` prose counterpart. Formalizations of the
  CPT/parity/Lorentz/position-operator chapter exist in `BookProof/` (e.g.
  `ChapterCPTHamiltonian.lean`, `ChapterLorentzRealRepFull.lean`,
  `ChapterLocalization.lean`, `ChapterParityCustodial.lean`) but **no `Book/*.lean`
  chapter imports them**. Only the generic "symmetry ⇒ unitary representation" line
  survives (`SymmetryRep.lean:6, 90-118`); the relativistic position-operator claim
  (`book.tex:6391-6409`) is replaced by a causality-measure statement in
  `EPRComplete.lean:57-80`.

### S9. Deep-learning / alignment chapter absent
- `book.tex:9606-10535` (deep nets as random sampling, alignment, digital-first
  mathematics, negotiation) has no curated counterpart; grep for `deep|alignment|ML`
  across `Book/*.lean` yields only incidental uses.

### S10. EPR/Bell material re-allocated, completeness verdict dropped from that narrative
- `book.tex:2876-2880` ("QM is a complete statistical theory as defined by EPR") and
  `3224-3227` (Bell verdict) move to `EPRComplete.lean` / `BellInequalities.lean`;
  `TrajectoryReconstruction.lean` keeps none of it.

## Additions (content in `Book/` not in the corresponding manuscript chapter)

### A1. "No non-informative priors" strengthening
- `book.tex:1250-1252` says only "no prior which is better for all cases".
- `Book/DutchBook.lean:184-191` draws the sharper conclusion "there are no
  non-informative priors … theoretical prejudice is unavoidable"; `SequentialBayes.lean:
  90-97, 124-166` adds the reparametrization-of-any-prior-into-uniform theorem.

### A2. Law of total variance with aleatoric/epistemic framing
- `Book/TotalVariance.lean:13-27, 99-108` makes a scattered ensemble remark
  (`book.tex:1725-1731`) into an explicit, verified identity with imported vocabulary.

### A3. Gauge-fiber / "simplex is the quotient of the sphere"
- `Book/BornFiber.lean:19-73, 75-84` adds an original phase/sign-fiber reading not
  present in the manuscript chapter.

### A4. Constructive DFT/Hadamard erasure
- `Book/SternGerlach.lean:113-140` adds the explicit `U=(1/√n)e^{2πiij/n}` construction
  and the "erasure is reversible at the wave-function level; only Born's rule forgets"
  thesis; `book.tex:3454-3480` asserts erasure existence abstractly.

### A5. ABL attribution and three-instant model
- `Book/TrajectoryReconstruction.lean:14-22, 24-132` names the procedure
  Aharonov–Bergmann–Lebowitz (the manuscript, `book.tex:3064-3074`, does not) and adds
  a finite three-instant model with marginal/consistency theorems.

### A6. ODE operator-theoretic expansion
- `Book/OdeSingularity.lean:78-98` (Weyl quantization, Wick recursion),
  `100-131` (Nelson's theorem), `37-43, 174-206` (formalization inventory) go beyond
  the manuscript's Faris/corollary citation (`book.tex:1091-1093`).

### A7. Mehler/Kopperman synthesis in the free-field chapter
- `Book/FreeField.lean:37-40, 74-86, 99-119` identifies the sphere measure as the
  Mehler measure and the Kopperman–Solovay exception — material drawn from other
  chapters, not stated in `book.tex:3699-4217`.

### A8. Measurement LLN chapter
- `Book/MeasurementLLN.lean` (frequencies → probabilities) is new; the manuscript
  chapter `book.tex:9474-9605` lacks the LLN bridge.

## Known-aligned chapters (recently rewritten, expected to match)

- `Book/CollapseKeepsKolmogorov.lean` and `Book/SternGerlach.lean` were rewritten to
  match `book.tex:3229-3698` (Euler recursion of 2D collapses, Stern–Gerlach). Residual
  deltas are additive only: the "QM stays Kolmogorov / Gleason contrast" headline
  (`CollapseKeepsKolmogorov.lean:11-23, 138-200`) and the DFT erasure theorem (A4) are
  synthesized, not contradicted. The manuscript's "minimal sufficient phase-space"
  doctrine (`book.tex:3356-3369`) and the speculative black-hole-information framing
  (`book.tex:3444-3478`) are dropped in favor of the theorem-focused version.

## Conventions observed

- Nothing in `Book/` *contradicts* a claim `book.tex` asserts; the differences are
  omissions, narrowing, or strengthening.
- The dominant pattern is **deliberate scope selection** consistent with the preface
  (`Book.lean:102-105`: "selects the threads whose mathematics is both self-contained
  and already formalized"). The genuine **divergences** are D1-D9 above.
