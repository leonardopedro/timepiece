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

## Status (2026-08-10 — Parts A–G, the closing pass, and all subsequent attention waves landed; read this before starting)

Parts A, B, C, D, E and the closing pass are **complete**: the chapter
builds, all its `#check` blocks elaborate, and the new theorems are `sorry`-free
and `axiom`-free. Concretely:

- **Part A.** `ChapterCoherentOverlap`, `ChapterSoftmaxBorn` (headline
  `coherentBorn_eq_softmax`), `ChapterObservableExpectation`, and the statistical
  core of `ChapterCoherentTemperature` are all proved, registered in `BookProof.lean`,
  and `#check`-ed in `Book/CoherentState.lean`. A.4 (the physical temperature
  identity) remains a documented proof plan.
- **Part B.1.** `tailSplitEquiv_map` in `ChapterSolovayCoordinates.lean` is now
  **proved** (no `sorry`); `mehler_unique_by_finite_marginals` is proved in
  `ChapterMehlerUniqueness.lean`.
- **Part B.3.** The concrete Schur (`ChapterSchurFullFiniteDim`) and Pauli
  (`ChapterPauliCommutant`) cases, unitary complete reducibility
  (`ChapterUnitaryCompleteReducibility`) and Maschke's theorem for finite groups
  (`ChapterMaschkeFiniteGroup`) are proved; the general `EXTERNAL` flags are
  retained only where the deep general theorem is genuinely out of Mathlib.
- **Part B.4.**   `selecting_events_not_rewriting_history`,
  `exists_regular_conditional_probability`, `exists_continuous_atomic_decomposition`
  and the finite type-`Iₙ` case `vonNeumann_abelian_classification_typeI`
  (`ChapterSelectingEvents.lean`, discharging the `ChapterAbelianDiagonal` core)
  are real theorems now, not `True` placeholders. The full von Neumann
  `*`-isomorphism classification (the remaining four classes and exhaustiveness)
  is a documented gap.
- **Hygiene.** Only `UnusedRoute/SchoenfeldPRA.lean:163,178` (intentional) carry
  `sorry`; no `axiom` anywhere in `BookProof/`. `lake build BookProof`, `lake build
  book`, `lake exe book` + `./patches/postprocess-html.sh` are all green.

- **Part C — landed.** `ChapterCoherentOverlapComplex` (the complex Bargmann
  kernel, `coherentBornC_eq_softmax`, `bornWeightC_phase_invariant`),
  `ChapterObservableOperator` (the observable built as an operator, with
  `observableOp_expectation`), `ChapterAbelianDiagonalCountable` (the countable
  MASA `ℓ∞(ℕ)` on `ℓ²(ℕ)`) and the Maschke consequences (`avgProj_idempotent`,
  `avgProj_range_eq_W`, `maschke_decomposition`) are all proved and `#check`-ed in
  the chapter.
- **Part D — landed.** `lake build` (default targets) is green with **no in-scope
  warnings**: `ChapterD`, `ChapterA3h` (`bilC_ext` rewritten) and `ChapterA3m` were
  cleaned, and `RandomMap/RandomMap2InfiniteWalk.lean` was rewritten around the
  scalar-bump lemmas, taking `lake build RandomMap` from a failure with 39 warnings
  to green with none. The only remaining `sorry` notices are the two intentional
  ones in `UnusedRoute/SchoenfeldPRA.lean`.
- **Part E — landed (this wave).** The coherent-state chapter's three remaining
  structural layers are proved and cross-referenced:
  `ChapterCoherentGeometry` (the kernel as a metric readout, the Born weight as a
  Softmax over minus the squared distances, "the nearest key wins"),
  `ChapterSoftmaxOrder` (gauge invariance, order preservation, the
  temperature-independent argmax) and `ChapterAttentionEntropy` (Shannon entropy,
  Gibbs' inequality, maximal entropy at `β = 0`, and the entropy collapse to `0`
  as `β → ∞`, also for the coherent Born weights).  Earlier in the same pass,
  `ChapterCoherentOccupation` (Poisson occupation statistics, `τ` as the energy
  expectation) and `ChapterSoftmaxSharpness` (the flat-versus-sharp dichotomy)
  landed.

**Closing pass — done (same day, `PLAN_LEAN_SPECIALIST_UNPROVED.md` in queue
order).** Four further packages landed, are `#check`-ed in the chapter, and close
Priority 4 of `PLAN_LEAN_SPECIALIST_UNPROVED.md`:
`ChapterA3x` (complete reducibility at `N = 3`,
`tensorCube_complete_reducibility`: `V^{⊗3} = Sym³V ⊕ Λ³V ⊕ Mixed`, with the
mixed summand non-zero), `ChapterBoseEinstein` (the thermal law is the Gibbs law,
`τ = ½·coth(x/2)`), `ChapterThermalMaxEntropy` (thermal law maximizes entropy at
fixed mean occupation) and `ChapterLinftyMultiplication` — the **`L∞(μ)` class of
the abelian von Neumann list** (`multOp`, `multOp_comm`, `multOp_inner_adjoint`,
`multOp_mul`, `multOp_one`, `norm_multOp_le`, `unitInterval_atomless`,
`vonNeumann_abelian_class_Linfty`).

**Part F — landed (2026-08-09).** Five new packages, all `sorry`-free and
`axiom`-free, registered in `BookProof.lean` and `#check`-ed in the book:
`ChapterH5` (F.1, the inversion-free Krylov shortcut, headline
`krylov_no_inversion_eq_standard`), `ChapterH6` (F.2, the Krylov projection as a
spectral low-pass filter, `krylovRetainsDominantSpectrum` and the SIRK error
decay), `ChapterF8` (F.3, the TSR offline/online cost split, headline
`tsr_offline_compiles`), `ChapterThermalTemperatureCore` (F.4, the finite
algebraic core of the temperature identity, headline
`thermal_temperature_eq_mean_half`) and `ChapterAbelianMixture` (F.5, the mixed
atomic-plus-diffuse abelian von Neumann class, headline
`vonNeumann_abelian_class_mixture`).  Book prose and `#check` blocks were added
to `Book/FreeField.lean`, `Book/CoherentState.lean` and `Book/NullMeasure.lean`.

**Part G — landed (2026-08-09).** The shared analytic core was promoted out of
`PnpProof/` into four new Mathlib-only modules `BookProof/PhysMeasureBasis.lean`,
`BookProof/PhysFunctionalAnalysis.lean`, `BookProof/PhysHSGaussian.lean` and
`BookProof/PhysMehler.lean`; the original `PnpProof/` files are now thin `export`
aliases and **no `PnpProof` module compiles in the default build**.
 `RandomMap/SchoenfeldPRA.lean` was moved to `UnusedRoute/SchoenfeldPRA.lean`
 (taking its two intentional RH `sorry`s out of the default thread).  A style
 follow-up remains: the promoted `Phys*` modules inherit long-line and
 tactic-style lint warnings from their P≠NP origin (no linter was disabled and
 no `nolint` was added).

 > **Open item (author rule: `UnusedRoute/` may depend on the rest of the
 > project, never vice versa).**  The isolation is **not yet complete**: the
 > default-reachable `RandomMap/RandomMap2.lean` still does
 > `import UnusedRoute.SchoenfeldPRA`, and `RandomMap/RcpRandomMap2Bridge.lean`
 > is entirely RH-dependent (`RH_PRA → RectangleRH`).  Both violate the rule.
 > The fix (recorded for the specialist, not yet done):
 >
 > - **`RandomMap2.lean` needs only generic content.**  Its only
 >   `SchoenfeldPRA`-sourced identifiers are `rcpPriorOnSubstrate` and
 >   `rcpPriorOnSubstrate_isProb` (thin wrappers over
 >   `BookProof.PhysMehler.exists_atomless_prob_substrate`) plus `Substrate`
 >   (already shared in `PhysMehler`).  Move those two wrappers into
 >   `BookProof/PhysMehler.lean` (or define them locally in `RandomMap2`), and
 >   repoint `RandomMap2`'s import to `BookProof.PhysMehler` — dropping
 >   `UnusedRoute.SchoenfeldPRA` from the default thread entirely.
 > - **`RandomMap2.lean` Phase 7 (lines 844–931) is RH content** and must move to
 >   `UnusedRoute/`: `zeta_no_zeros_right_half_plane'`,
 >   `riemann_hypothesis_decoupled`, `eta_non_zero_real_axis`.  (Phases 1–6 and
 >   8+ are the generic decoupled Kopperman–Solovay framework and stay.)
 > - **`RandomMap/RcpRandomMap2Bridge.lean` is wholly RH** (the `RH_PRA →
 >   RectangleRH` bridge) and should move to `UnusedRoute/` as well.
 >
 > After the split, `grep -rlnE "import UnusedRoute" RandomMap/` returns nothing,
 > and the default build (`BookProof`, `Book`, `Singularity`, and the
 > `Book/ChapterSolovay` → `RandomMap2` edge) has no `UnusedRoute` dependency.

**Continuation pass — landed (2026-08-09, later the same day).**  The audit found
`lake build BookProof` **red** (`BookProof/PhysMehler.lean`: two stale bullets
after a `rw`); that was repaired first.  Four further packages landed, all
`sorry`-free/`axiom`-free, registered and `#check`-ed in `Book/CoherentState.lean`:
`ChapterCoherentFidelity` (the quantum fidelity of coherent states,
`fidelityC_eq_exp_neg_dist_sq`, attention as the normalized fidelity),
`ChapterSoftmaxFluctuation` (the fluctuation–response law
`d/dβ⟨s⟩_β = Var_β(s)`), `ChapterSoftmaxMaxEntropy` (Gibbs' inequality and the
maximum-entropy characterization of Softmax) and `ChapterEntropyTemperature`
(`dH/dβ = −β·Var_β(s)`, entropy antitone on `β ≥ 0`).  The **style follow-up
recorded under Part G is closed**: `BookProof/PhysHSGaussian.lean` is now
warning-free, with the Hermite derivative/polynomiality lemmas rewritten as
reusable top-level results; no linter was disabled.  Also recorded in
`BookProof/STATUS.md` for the first time: the previously undocumented
`ChapterDisplacedThermalOverlap`, `ChapterDisplacedThermalMulti` and `ChapterH7`.

**Operational-layer pass — landed (2026-08-09, latest).**  Five further packages,
all `sorry`-free/`axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean` and `#check`-ed in `Book/CoherentState.lean`:
`ChapterSoftmaxJacobian` (the score derivative of attention: `∂ log Z/∂sᵢ = β·pᵢ`,
the Jacobian `∂pⱼ/∂sᵢ = β·pⱼ(δᵢⱼ − pᵢ)`, its symmetry, zero row sums and
positive-semidefinite quadratic form `β·Var`), `ChapterAttentionOutput` (the
output as a function of the temperature: the mean at `β = 0`, winner-takes-all as
`β → ∞`, `ℓ¹` stability — building on the existing `observableExpectation` rather
than restating its convex-hull/norm bounds), `ChapterAttentionMasking` (masking is
Bayesian conditioning, `p(j | S) = p(j)/p(S)`, with odds invariance, the tower
property and the causal mask), `ChapterCoherentDynamics` (the symmetry group of
attention: unitary invariance, free-evolution invariance — attention is a constant
of the motion — and Weyl displacement covariance) and
`ChapterAttentionFactorization` (independent modes factorize; the attention
entropy is additive), plus `ChapterRotaryPosition` (the rotary positional encoding
is unitary and additive in the position, and the alignment — hence every attention
weight — depends on the two positions only through their offset).  The same pass documented four packages that had landed on
disk but were never written up in `BookProof/STATUS.md`
(`ChapterSoftmaxDivergence`, `ChapterLogPartitionConvex`,
`ChapterCoherentPositionSpace`, `ChapterSoftmaxStability`).  The two mathematical
gaps below are unchanged.

**Attention-layer pass — landed (2026-08-10, this wave).**  Four further packages,
all `sorry`-free/`axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean` and `#check`-ed in `Book/CoherentState.lean`:
`ChapterAttentionRetrieval` (the head as a *quantitative* associative memory —
under a score margin `δ` every distractor keeps at most `e^{-βδ}`, the target keeps
at least `1/(1+(m-1)e^{-βδ})`, and the output is within `2C(m-1)e^{-βδ}` of the
stored value; plus the converse `p_j ≥ e^{-βD}/m`, so at a finite temperature no key
is ever ignored, and the coherent-state form with the margin as a squared-distance
gap), `ChapterAttentionEquivariance` (attention is a set function: permutation
equivariance of the weights, invariance of the output and of the entropy — the
discrete half of the symmetry group whose continuous half is
`ChapterCoherentDynamics`), `ChapterAttentionMixture` (many heads are one mixture:
the ensemble output is the weighted mean of the head outputs, and by concavity of
`-x log x` mixing heads never destroys information) and
`ChapterCrossEntropyGradient` (the learning signal: the cross-entropy loss is the
surprisal of the observed key, its score derivative is the backpropagation rule
`β(p_i − δ_iy)`, the gradient sums to zero, and the loss is convex in the
temperature).

**The Part G.3 isolation item recorded above is now CLOSED.**
`rcpPriorOnSubstrate` and its two companions were promoted into
`BookProof/PhysMehler.lean`; `RandomMap/RandomMap2.lean` imports
`BookProof.PhysMehler` instead of `UnusedRoute.SchoenfeldPRA`; its RH Phase 7 moved
verbatim to `UnusedRoute/RandomMap2Phase7.lean`; and `RcpRandomMap2Bridge.lean`
moved to `UnusedRoute/`.  `grep -rn "import UnusedRoute" RandomMap/` is now empty
and the default build (`BookProof`, `Book`, `Singularity`, including the
`ChapterSolovay` → `RandomMap2` edge) has no `UnusedRoute` dependency.  Residue,
recorded in `BookProof/STATUS.md`: the two `#print axioms` audit scripts
`BookProof/B1_randomMap2_axioms.lean` and `BookProof/randomMap2_axioms.lean` still
import RH modules; they are in no build target.

**What remains** is a
documented mathematical gap list that is not a hygiene backlog: the physical
derivation of `τ = n̄ + 1/2` from the fidelity of displaced thermal states
(Part A.4 — Part F.4 proves its finite, algebraic core), and — of the von Neumann
list — the exhaustiveness of the `*`-isomorphism
classification (Part B.4; the finite `Iₙ`, countable `ℓ∞(ℕ)`, diffuse `L∞(μ)`
and mixed atomic-plus-diffuse classes are all landed).  **Part G, the
isolation refactor, is now closed** (see the "now CLOSED" note above): the
hyperspherical/Gegenbauer content was promoted out of `PnpProof/`, the RH
file `RandomMap/SchoenfeldPRA.lean` was moved to `UnusedRoute/`, and the
default-reachable `RandomMap/RandomMap2.lean` no longer imports
`UnusedRoute.SchoenfeldPRA` (it imports `BookProof.PhysMehler`), with the wholly
RH `RandomMap/RcpRandomMap2Bridge.lean` and the RH Phase 7 of `RandomMap2.lean`
moved to `UnusedRoute/` (`RcpRandomMap2Bridge.lean` /
`RandomMap2Phase7.lean`).  `grep -rn "import UnusedRoute" RandomMap/` is now
empty.  The remaining residue is limited to the two `#print axioms` audit
scripts `BookProof/B1_randomMap2_axioms.lean` and
`BookProof/randomMap2_axioms.lean`, which still import RH modules but are in no
build target, and the root `RiemannProof.lean`, which still imports
`RandomMap.RcpRandomMap2Bridge` (a module that now lives at
`UnusedRoute.RcpRandomMap2Bridge`); root modules are also not a default build
target, so repoint that one import when the specialist next touches
`RiemannProof.lean`.  Both remaining mathematical gaps are recorded
in `BookProof/STATUS.md`; neither is `sorry`-ed anywhere.  Parts C and D below
are kept for the record.  Future waves should continue to target ≥ 4 deliverable
groups per pass (`PnpProof/`, `UnusedRoute/`, `UsedRoute/` remain out of scope to
*edit*, but their shared content may be promoted as described in Part G).

**Information-theoretic pass — landed (2026-08-10, latest).**  Five further
packages, all `sorry`-free/`axiom`-free, registered in `BookProof.lean`, certified
in `BookProof/ChapterRoadmapAudit.lean` and `#check`-ed in
`Book/CoherentState.lean`: `ChapterAttentionCollision` (the participation ratio
`1/∑pⱼ²` as the effective number of attended keys — between `1` and `m`, exactly
`m` at `β = 0`, and bounded by `exp H` since the Rényi-2 entropy never exceeds the
Shannon entropy), `ChapterAttentionConcentration` (a Markov bound: at most `1/t`
keys can carry weight `t`; some key always carries `1/m`; the min-entropy bound
`−log pₘₐₓ ≤ H`, so a low-entropy head has a dominant key, whose reciprocal lower
bounds the participation ratio), `ChapterAttentionMarkov` (attention as a Markov
kernel: row-stochasticity, kernel composition = layer stacking, `ℓ¹`
non-expansiveness, the Doeblin contraction `1 − mε`, and the headline
`l1dist_push_attentionMatrix_le`: a layer with score spread `D` contracts by
`1 − e^{−βD}`), `ChapterScaledDotProduct` (why the scores are divided by `√d`: for
a uniform `±1` query the raw score has mean `0` and mean square `‖k‖²`, hence RMS
`√d`, and rescaling the scores is rescaling the temperature, so the `1/√d` is what
holds the temperature fixed as the width grows) and
`ChapterAttentionOutputVariance` (the bias–variance identity for the output, the
head output as the least-squares summary of the values, König–Huygens/Jensen, and
zero output variance exactly when the values agree).  The two mathematical gaps
below are unchanged.  The same pass added four more:
`ChapterAttentionLowRank` (the score table of a head has rank at most the head
dimension, so a narrow head cannot realize the identity routing pattern — sharp at
`d ≥ m`), `ChapterLayerNorm` (layer normalization as gauge fixing: the sphere of
squared length `d`, invariance under `x ↦ ax + c`, idempotence, and the resulting
attention floor `e^{−2βd}/m`), `ChapterSinusoidalPosition` (the sinusoidal
counterpart of the rotary offset property) and `ChapterAttentionMixing` (iterating
one layer: the `(1 − mε)ⁿ` mixing law, convergence, uniqueness of a stationary
belief, and the attention rate `(1 − e^{−βD})ⁿ`).

**Control-layer pass — landed (2026-08-10, latest).**  Five further packages, all
`sorry`-free/`axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean` and `#check`-ed in `Book/CoherentState.lean`:
`ChapterAttentionTemperature` (turning the temperature knob: the odds
`pᵢ = e^{β(sᵢ−sⱼ)}pⱼ`, the monotonicity of the winner's weight and the antitonicity
of the loser's, the uniform share `1/m` as the separating value at `β ≥ 0`, and the
entropy floor `H ≥ log m − βD` for scores of spread `D`), `ChapterAttentionSink`
(the attention sink is a gauge: one extra key rescales every ordinary weight by
`1 − w`, preserves all odds, gives the two-point output `w·v₀ + (1−w)·o` and the
entropy chain rule), `ChapterAttentionCoarseGrain` (regrouping the keys: the
pushforward of the attention distribution, output invariance when the values depend
only on the group, the data-processing inequality for the attention entropy, and
the multiplicity rule that duplicating a key doubles its share),
`ChapterAttentionQKCircuit` (the head sees only `W_Qᵀ W_K`: the bilinear form, the
`GL(d)` gauge freedom `(W_Q,W_K) ↦ (AW_Q,BW_K)` with `AᵀB = 1`, and the rank bound
by the head dimension) and `ChapterResidualStream` (a contractive block never
overwrites the stream: `x ↦ x + f x` is expansive by `1 − L`, hence injective, with
the `(1 + L)` companion bound and the `n·C` drift bound for a stack of `n` blocks).
The two mathematical gaps below are unchanged.

**Soft-maximum / circuit pass — landed (2026-08-10, latest).**  Five further
packages, all `sorry`-free/`axiom`-free, registered in `BookProof.lean`, certified
in `BookProof/ChapterRoadmapAudit.lean` and `#check`-ed in `Book/CoherentState.lean`:
`ChapterAttentionFreeEnergy` (the free energy is a soft maximum: `β·sⱼ ≤ log Z ≤
log m + β·max s`, hence `|log Z/β − max s| ≤ log m/β` and `max s − ⟨s⟩_β ≤ log m/β`,
with both quantities converging to the maximum as `β → ∞` — the gap between the soft
and the hard maximum is exactly the entropy of the collapse),
`ChapterAttentionSparse` (top-`k`/windowed attention: the shortlisted head differs
from the dense head by **exactly** `2(1 − P(S))` in `ℓ¹`, so a shortlist carrying
`1 − ε` of the mass is `2ε`-accurate and its output is within `2εC`, with a
`(m − |S|)ε` tail bound and the lossless characterization),
`ChapterAttentionOVCircuit` (the writing-side counterpart of the QK circuit: the
attention average commutes with every linear map, so the value and output
projections act only through `W_O W_V`, with the `GL(d)` gauge freedom
`(W_O,W_V) ↦ (W_O A, B W_V)`, the rank-`d` bound and the column-space range),
`ChapterAttentionSaturation` (the learning signal: the row of the Softmax Jacobian
has total absolute size exactly `2β·pᵢ(1 − pᵢ)`, hence at most `β/2`, and at most
`2βε` for *every* key once some key carries `1 − ε` — a confident head has a
vanishing gradient) and `ChapterAttentionPrior` (a logit bias is a Bayesian prior:
`pⱼ ∝ wⱼe^{βsⱼ}` is definitionally the Bayes posterior with prior `w` and likelihood
`e^{βs}`, its odds are prior odds × likelihood ratio, a prior is exactly the score
shift `sⱼ ↦ sⱼ + (log wⱼ)/β`, only the ratios of the weights matter, and at `β = 0`
the head returns the normalized prior).  The two mathematical gaps below are
unchanged.

**Decoding / locality pass — landed (2026-08-10, final).**  Four further packages,
all `sorry`-free/`axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean` and `#check`-ed in `Book/CoherentState.lean`:
`ChapterAttentionStreaming` (appending a key multiplies every cached weight by one
common factor `1 − w` and updates the output to `(1 − w)·o_old + w·v_new`, so the KV
cache of an autoregressive decoder is exact, and a fresh token moves the summary by
exactly `w·‖v_new − o_old‖`), `ChapterAttentionLocality` (a distance penalty
`s ↦ s − γ·d` makes a head provably local: weights decay like `e^{−βγd}`, the mass
beyond distance `R` is at most `m·e^{βΔ}e^{−βγR}`, and the sliding-window head is
within `2C` times that of the full head), `ChapterAttentionCalibration` (the
attention entropy is continuous and strictly decreasing in `β ≥ 0` whenever two
scores differ, so a target entropy level is realized by exactly one temperature —
the headline `existsUnique_beta_attentionEntropy_eq`) and `ChapterAttentionTopK`
(the heaviest-first shortlist maximizes the attended mass, hence minimizes both the
`ℓ¹` error and the output error of sparsification, and at `β > 0` it coincides with
the highest-scoring shortlist).  The two mathematical gaps below are unchanged.

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
  grep -rn "sorry" BookProof/           # expect empty (the two intentional sorries live in UnusedRoute/SchoenfeldPRA.lean)
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

## Part C — Next wave (2026-08-08): close the recorded disparities and the next von Neumann class

All of Part A and Part B are complete. The remaining work that is **realistic** in
Mathlib v4.28.0 is:

### C.1 — Complex coherent overlap and Born-weight invariance `ChapterCoherentOverlap` / `ChapterSoftmaxBorn`

Both modules record the same documented disparity: the theorems are proved for
*real* coherent-state parameters, where the Bargmann kernel is a positive real; the
general *complex* kernel carries an extra phase `exp(i·Im⟪q,k⟫)` which the Born
rule (squared modulus) discards. Close it:

- Extend `coherentOverlap` to complex parameters `q k : EuclideanSpace ℂ (Fin n)`:
  `coherentOverlap_c q k = exp(-‖q‖²/2 - ‖k‖²/2 + ⟪q,k⟫)` (complex exponent).
- Prove the phase factor: `coherentOverlap_c q k = coherentOverlap_re (q.re,k.re) ·
  exp(i·Im⟪q,k⟫)` (or the coordinate form), and hence
  `‖coherentOverlap_c q k‖² = ‖coherentOverlap_re q' k'‖²` — the Born weight is
  unchanged.
- Upgrade `coherentBorn_sq_eq` and the headline `coherentBorn_eq_softmax` to complex
  parameters (re-derive the three-factor split with `Complex.normSq`).

**Definition of done:** `coherentOverlap_c`, the phase identity, and the complex
`coherentBorn_eq_softmax` are `sorry`-free/`axiom`-free, registered, and `#check`-ed
in `Book/CoherentState.lean`; the disparity note is updated to "closed".

### C.2 — The observable as an operator `ChapterObservableExpectation`

The second recorded disparity: the chapter writes `V̂ = ∑ⱼ vⱼ |kⱼ⟩⟨kⱼ|` and appeals
to the spectral theorem, while the module uses only spectral data. Supply the
finite operator itself:

- Build `observableOp k v : Matrix (Fin m) (Fin m) ℂ` (or as an endomorphism of the
  span of the keys) with `observableOp k v = ∑ⱼ vⱼ • outer kⱼ kⱼ`.
- Prove it is **Hermitian** when the eigenvalues `vⱼ` are real
  (`(observableOp k v)ᴴ = observableOp k v`), and that its expectation in the state
  `|q⟩` with Born statistics `pⱼ` satisfies `⟨observableOp⟩ = ∑ⱼ pⱼ vⱼ`, i.e.
  `attention_eq_expectation` upgraded to a genuine operator expectation.

**Definition of done:** `observableOp`, Hermitianness, and the operator expectation
identity are `sorry`-free/`axiom`-free and `#check`-ed in `Book/CoherentState.lean`.

### C.3 — The second von Neumann class: maximal abelian `ℓ∞(ℕ)` on `ℓ²(ℕ)` `ChapterAbelianDiagonal` follow-on

`ChapterAbelianDiagonal` proves the finite (type `Iₙ`) class: `ℓ∞({1,…,n})` realized
as a MASA of `Mat(n,ℂ)`. The **countable** class `ℓ∞(ℕ)` is the natural next rung of
the five-item list and is realistic now that `ChapterRieszFischer` / `ChapterEll2Separable`
have built `ℓ²(ℕ)`:

- Define the diagonal embedding `(ℕ →₀ ℝ) → Ell2` (already have `ofCore`) and, over
  a bounded sequence, the diagonal multiplication operator on `ℓ²(ℕ)`.
- Prove the countable analog of maximal abelianness: the diagonal bounded operators
  on `ℓ²(ℕ)` form an abelian algebra that is its own commutant (commutant
  computation on `lp` / `MemLp`), giving the second isomorphism class
  `vonNeumann_abelian_class_countable`.

**Definition of done:** the `ℓ∞(ℕ)` MASA theorem `sorry`-free/`axiom`-free, and
`#check`-ed in `Book/NullMeasure.lean` next to the type-`Iₙ` case. (The `L∞([0,1])`
and mixture classes require von-Neumann-algebra machinery absent from Mathlib
v4.28.0; keep the full five-item classification a documented gap.)

> **Superseded (closing pass, same day):** the diffuse `L∞(μ)` class is now built
> too — `BookProof/ChapterLinftyMultiplication.lean` (`multOp`,
> `vonNeumann_abelian_class_Linfty`, `unitInterval_atomless`) — so of the five-item
> list only the two mixture classes and exhaustiveness remain open. See §Status.

### C.4 — Maschke consequences for the averaging package `ChapterMaschkeFiniteGroup`

The Maschke package proves existence of an invariant complement; its two structural
consequences are not yet recorded:

- `avgProj_idempotent` — the averaged projection is a genuine projection
  (`avgProj ρ pi ∘ avgProj ρ pi = avgProj ρ pi`), and `avgProj_range_eq_W` — its
  range is exactly the invariant subspace `W`.
- `maschke_decomposition` — package the full decomposition: `V = W ⊕ W'` with both
  `W` and `W'` invariant and the projection onto `W` commuting with `ρ` (the book's
  "any invariant subspace is a direct summand" phrasing).

**Definition of done:** `avgProj_idempotent`, `avgProj_range_eq_W`,
`maschke_decomposition` `sorry`-free/`axiom`-free and `#check`-ed in
`Book/PhysicalParity.lean`.

---

## Part D — Hygiene: fix warnings and build failures (whole project, except `PnpProof/`, `UnusedRoute/`, `UsedRoute/`)

Author mandate (2026-08-08): fix the linter warnings **and** the build failures in
this project, with `PnpProof/`, `UnusedRoute/`, `UsedRoute/` explicitly **out of
scope** (leave them untouched, even when their warnings show up in a shared build
log). Everything else — `BookProof/`, `RandomMap/`, `Singularity/`, `Book/`,
`Book.lean`, `BookProof.lean` — is in scope.

### Current state (surveyed 2026-08-08)

- **Default targets build green.** `lake build` (default targets `BookProof`,
  `Book`, `Singularity`) completes with 8508 jobs and no errors.
- **`lake build RandomMap` FAILS.** `RandomMap/RandomMap2Walk.lean` has ~50 errors
  (a `rewrite` that no longer finds its pattern, `Fin.cast`/`Fin N` vs `ℕ`
  application-type mismatches, an unsolved instance, etc.). This module is imported
  only by the unregistered scratch files `BookProof/randomMap2_axioms.lean` and
  `BookProof/B1_randomMap2_axioms.lean` (not registered in `BookProof.lean`), so the
  failure is invisible to the default build; it is still a real build failure in
  scope. `UnusedRoute/SchoenfeldPRA.lean` imports the excluded `UnusedRoute.RcpEuler`
  / `SchoenfeldMatrix`, so it cannot be built standalone until those are; treat
  `RandomMap2Walk` as the primary fixable target.
- **Warnings in scope:** ~1422 lines in `BookProof/` plus 2 in
  `UnusedRoute/SchoenfeldPRA.lean` (the intentional `sorry`s at 163/178) on a full
  `lake build`; `lake build RandomMap` additionally surfaces 11 in
  `RandomMap2Walk.lean` and 1 in `RandomMap2Moments.lean`; `lake build book` shows
  1 (the benign `verso: repository … has local changes` notice, no action).
  Excluded-directory warnings (~1080 lines: `UsedRoute/RectangleStrategy` 350,
  `PnpProof/SphereGaussian` 247, etc.) are **not** to be touched.
- **Worst offenders in scope** (BookProof): `ChapterParityChirality` 90,
  `ChapterTsirelson` 74, `ChapterMajoranaFourier` 57, `ChapterE` 57, `ChapterF4` 54,
  `ChapterF6` 47, `ChapterA3u` 42, `ChapterA3c` 41, `ChapterA3b` 41, `ChapterE2` 35,
  `ChapterSolovayCoordinates` 33. ~100 files carry at least one warning.

### D.1 — Fix the `RandomMap` build failure (highest priority)

`RandomMap/RandomMap2Walk.lean` (~50 errors) must build. Diagnose the errors in
order:

- `rewrite` at 61:164 no longer finds `(Measure.pi ?μ) (univ.pi ?s)` — likely the
  lemma it used (`MeasureTheory.Measure.pi_congrLeft` or a `pi`-on-`univ.pi`
  lemma) changed shape; replace with the current Mathlib v4.28.0 identity.
- The `Fin.cast hn` / `x k` mismatches at 132–184: `hn : n ≤ N` is used as if it
  were `n = N` and `k : ℕ` is applied to `x : InnerHead N = Fin N → ℝ`; introduce
  the correct index coercion (`⟨k, hk⟩` / `Fin.castLT`/`Fin.ofNat`) and the
  equality from the `Fin N` type structure. Fix the failed instance at 180.
- If a claim needs `Measure.infinitePi`-splitting that is genuinely out of Mathlib,
  keep it as an `EXTERNAL` named hypothesis (never `sorry`, never `axiom`); a
  build failure must become a *green build with a documented gap*, not a broken file.

**Definition of done:** `lake build RandomMap` completes; the only remaining
`RandomMap/` warnings are the two intentional `sorry`s in `SchoenfeldPRA.lean`.

### D.2 — Zero-warning pass on `BookProof/` (in-scope files only)

Work the ~100 in-scope files, starting with the worst offenders listed above. Fix
each warning at its source (never silence with `set_option linter.* false` at file
top, and never change `lakefile.toml` `[leanOptions]`):

- `simp`/`simp_all`/`aesop`/`omega`/`linarith` "is a flexible tactic modifying …",
  "Try this:", and "uses '⊢'!" suggestions → apply the `…?`-suggested `simp only
  [...]` / `aesop?` / `omega?` form, dropping unused simp arguments and unused
  hypotheses.
- `refine'` → `refine`/`apply` where possible; `exact`/`by congr`-style
  "uses '⊢'!" fixes.
- Long lines (> 100 chars) → wrap per the project style (AGENTS.md: no lines over
  100 chars, no trailing whitespace, no extra alignment spaces).
- Unused variable / unused-argument warnings → `_` / `omit` where appropriate.
- The five newly copied files already have recorded diagnoses if the warning pass
  resumes there: `ChapterSolovay.lean:343` (empty line inside a command),
  `ChapterPauliCommutant.lean` (flexible `simp` at 50, unused simp args at 81/89,
  unused `mgammaLin` at 192), `ChapterDensityMarginalConditional.lean` (unused
  `[Fintype n] [DecidableEq n]` at 43 and unused simp args / no-op `push_cast` at
  90–98), `ChapterRieszFischer.lean:62,84` (drop `Function.mem_support`, `ne_eq`,
  `Real.rpow_natCast`), `ChapterPaFreeCompletion.lean:72` (`simpa` → `simp`).

**Definition of done:** `lake build` (default targets) shows **no warnings from
`BookProof/`, `Book/`, `Singularity/`, or the root files** — only the excluded
directories' warnings may remain, and only `UnusedRoute/SchoenfeldPRA.lean` keeps its
two intentional `sorry` warnings. `lake build book` stays green.

### D.3 — Verification gate (do not skip)

1. `lake build` green; `lake build RandomMap` green; `lake build book` green.
2. `lake build 2>&1 | grep -E "^warning:"` must contain **only** paths under
   `PnpProof/`, `UnusedRoute/`, `UsedRoute/` and the two `SchoenfeldPRA` `sorry`
   notices.
3. `grep -rn "sorry" BookProof/ RandomMap/ Singularity/` shows only
   `UnusedRoute/SchoenfeldPRA.lean` (intentional) and any newly documented `EXTERNAL`
   gaps — never a `sorry` introduced by this pass.
4. `#print axioms` spot-checks on touched headline theorems: only `propext`,
   `Classical.choice`, `Quot.sound`.
5. If a warning is genuinely unfixable in Mathlib v4.28.0, record it (file:line +
   reason) in `BookProof/STATUS.md` under a "Known warnings (2026-08-08)" note
   rather than suppressing it.
6. Register any new `BookProof` file created during fixes in `BookProof.lean`.

---

## Part F — Next wave (2026-08-08): the QFM dimensional-reduction thread and the temperature identity

With Parts A–E and the closing pass done, the highest-value open work is the
**QFM `Krylov–Hashimoto dimensional reduction` and `Tomographic Subspace
Recovery`** thread of `FORMALIZATION_ROADMAP.md` (author-named as "very important
and can be formalized"; the `QFM.tex` §9 and §10 algorithm sections are **not yet
formalized** — nothing in `BookProof/` covers the inversion-free shortcut, spectral
low-pass filtering, offline compilation, or the four-phase online generate). This
is the natural continuation of the landed N14 package (`ChapterF1`–`F7`). Target
**≥ 4 deliverable groups** per pass.

### F.1 — The inversion-free Krylov shortcut `ChapterH5` (new, roadmap §9.1)

`QFM.tex` §9.1: the standard polynomial Krylov subspace
`Kry m(H̄, v₀) = span{v₀, H̄v₀, …, H̄^(m−1)v₀}`; the rational construction needs
`(γI − H̄)y = v` at each step, but by pre-conditioning the seed as
`v = (γI − H̄)^(m−1) v₀`, applying the resolvent merely *lowers the polynomial
degree*, recovering the standard Krylov subspace **with no inversion**. `H̄` is
bounded because the Mehler projector is rank-one and the number operators are
diagonal.

**Prove** (on a finite-dimensional Hilbert space, reusing `ChapterH1`/`ChapterH4`
φ-function and `sirkKrylov` machinery):
- `krylov_subspace_span` — `Kry m(H̄, v₀)` is exactly the span of
  `{H̄^i v₀ | i < m}` (a `Submodule` equality, `Finset.range`).
- `inversion_free_seed` — for `v = (γI − H̄)^(m−1) v₀`, the resolvent image
  `(γI − H̄)⁻¹ v = (γI − H̄)^(m−2) v₀` (the polynomial degree drops by one), so the
  rational Krylov sequence with uniform shifts `zₖ = γ` coincides with the standard
  Krylov basis (no inversion).
- `generator_bounded_of_rankOneProjector` — `H̄` is bounded (a rank-one projector
  plus diagonal operator), justifying the finite-dimensional reduction.
- `krylov_no_inversion_eq_standard` — **headline**: the inversion-free sequence
  `wₖ = (H̄ − γI) wₖ₋₁`, `w₀ = v₀`, spans the full Krylov subspace `Kry m(H̄, v₀)`.

**Definition of done:** the four theorems `sorry`-free/`axiom`-free, registered in
`BookProof.lean`, and a `#check` block added to `Book/FreeField.lean` (or the QFM
chapter that will cite them).

### F.2 — Spectral low-pass filtering `ChapterH6` (new, roadmap §9.2)

`QFM.tex` §9.2: the Krylov projection is an *exact spectral low-pass filter* — it
discards the high-frequency "spikes" and retains the `m` dominant eigenvalues; the
reduced `m×m` generator has SIRK error decaying like `e^{−hm}`
(`sirk_error_bound` in `ChapterH4.lean` already carries the exponential factor).

**Prove:**
- `sirk_error_decay_exponential` — the SIRK error bound `‖e^{−hX_m} − e^{−hH}‖`
  decays like `e^{−hm}` (reuse `ChapterH4.sirk_error_bound` /
  `sirk_error_bound_decay`).
- `krylovRetainsDominantSpectrum` — the reduced generator
  `H̄_reduced = Vᴴ H̄ V` for `V` the Krylov basis interlaces the dominant eigenvalues
  (Rayleigh–Ritz; a `spectrel_theorem` / `Matrix` eigen-decomposition argument).
- `reduce_generator_mul_m` — `H̄_reduced : Matrix (Fin m) (Fin m) ℂ` is explicitly
  `m×m` (the compression `compress_X_comp_V` in `ChapterH4.lean` is the template).
- `generation_single_exponential` — generation is a single `O(m²)` matrix
  exponential `Ψ_{t=1} = e^{−iH̄_reduced} Ψ₀` (an `exp`/`Matrix.exp` identity).

**Definition of done:** four theorems, `sorry`-free/`axiom`-free, registered, and
`#check`-ed in the citing chapter.

### F.3 — Tomographic Subspace Recovery: offline compilation `ChapterF8` (new, roadmap §10)

`QFM.tex` §10: the two-level hashing `S₁ : ℝ^d → ℝ^k` (raw→feature,
`k ≪ d`) and `S₂ : ℝ^k → ℂ^(K₂)` (feature→single-excitation Fock state,
`K₂ > k`), with the online state living in `ℂ^m` after Krylov reduction and all
raw-coordinate observables pre-projected into an `m²` operator basis.

**Prove** (finite, combinatorial core — no `M` dependence):
- `featureHash_decodes` / `twoLevelHash_total` — `S₂ ∘ S₁` is a well-defined map
  into the single-excitation subspace of `ℂ^(K₂)` (a `Finset`/`Card` dimension
  argument; reuse `ChapterF1` single-boson Fock facts).
- `offline_operatorBasis` — the `m²` pre-projected operator basis is a spanning set
  of `Hom(ℂ^m, ℂ^m)` (matrix-basis / `Fin m` `Matrix` fact).
- `online_cost_independent_of_M` — the four online cost components
  `O(d·m²) + O(K₂ log k) + O(K₂·m²)` carry **no** `M` term (an arithmetic/`Finset`
  bound, no matrix machinery).
- `tsr_offline_compiles` — **headline**: the offline stage produces the sketched
  single-excitation Fock embedding and the `m²` operator basis, ready for online
  Krylov generation.

**Definition of done:** four theorems, `sorry`-free/`axiom`-free, registered, and
`#check`-ed in a citing chapter.

### F.4 — The temperature identity, finite core `ChapterCoherentTemperature` (Part A.4)

The documented A.4 gap. Prove the *finite-core* algebraic identity (not the full
fidelity computation): for the geometric occupation distribution
`Pr(n) ∝ (n̄/(n̄+1))^n`,
- `geometricOccupancy_mean` — `Σₙ n·Pr(n) = n̄`;
- `geometricOccupancy_variance` — `var = n̄ + n̄²`;
- `half_integer_floor` — relating the "extra ½" to the Heisenberg floor of a
  coherent state (reuse `BookProof.ChapterBoseEinstein` / `ChapterBoseEinstein.mean`
  and `ChapterCoherentOccupation`).
- `thermal_temperature_eq_mean_half` — **headline**: assemble `τ = n̄ + ½` from the
  Bose–Einstein closed form `τ(x) = ½·coth(x/2)` (already proved) and the
  mean-occupation identity.

**Definition of done:** four theorems, `sorry`-free/`axiom`-free, registered, and
`#check`-ed in `Book/CoherentState.lean` next to the existing
`ChapterBoseEinstein` / `ChapterThermalMaxEntropy` blocks.

### F.5 — von Neumann mixture classes (documented gap, attempt a provable core)

The two remaining mixture classes of the abelian von Neumann list. The full
exhaustiveness theorem is out of Mathlib; attempt the provable finite core: a
finite convex combination of the atomic `ℓ∞(ℕ)` and diffuse `L∞(μ)` classes is
again an abelian, star-closed algebra on `L²`. If out of reach, record the exact
obstruction in `BookProof/STATUS.md` and move on — do **not** `sorry` it.

---

## Part G — Isolate `PnpProof/`, `UnusedRoute/`, `UsedRoute/`; promote the shared analytic content

**Author directive (2026-08-08):** the hyperspherical / Gegenbauer / Gaussian
content currently lives in `PnpProof/`, but it is **general mathematics useful
elsewhere** (it is the analytic backbone the QFM/Fork thread reuses), and
`PnpProof/`, `UnusedRoute/`, `UsedRoute/` must be **isolated from the rest of the
project** — the rest of the project (in particular `BookProof/`, `Book/`,
`Singularity/`, `RandomMap/`) must not depend on them. Today this is violated:
five `BookProof/` files import `PnpProof` directly:

| `BookProof/` file | imports `PnpProof` | uses |
| :--- | :--- | :--- |
| `ChapterSolovay.lean` | `PnpProof.Kopperman`, `PnpProof.SphereGaussian` | `Kopperman.mehler_concentrates_on_sphere`, `Kopperman.MehlerPrior` |
| `ChapterG3.lean` | `PnpProof.SphereGaussian` | `gaussianE`, `sphereUniform` (+ probabilities, rotation-invariance) |
| `ChapterSolovayCoordinates.lean` | `PnpProof.SphereGaussian` | `gammaMeasure`, `gammaMeasure_isProbability` |
| `ChapterKopperman.lean` | `PnpProof.Kopperman` | (wrapper) |
| `Substrate.lean` | `PnpProof.Kopperman` | `unitMeasure`, `squareMeasure` |

`RandomMap/SchoenfeldPRA.lean` also imports `PnpProof.Kopperman` (for
`arith_truth_invariant`, `interpPi02`). The reusable content depends only on
`PnpProof.Foundations`' `unitMeasure` / `squareMeasure` (and the null/countable
facts) — i.e. it is **not** P≠NP-specific.

### G.1 — Promote the shared analytic core to `BookProof/` (new `MathCore`-style modules)

Move the reusable content out of `PnpProof/` into `BookProof/` (or a new
in-scope `MathCore/` directory registered in `lakefile.toml` `defaultTargets`),
so it is part of the default build and importable by the QFM/Fork thread:

- **`PnpProof/FunctionSpace.lean`** → `PhysFunctionalAnalysis` (or `MathCore/FunctionSpace`):
  `l2_separable`, `linf_not_separable`, `sqrt_density_memLp`, `sqrt_density_norm`,
  `polynomial_dense_L2`, `countable_of_separated`, `exists_l2_iso`,
  `hilbert_classification`, `exists_atomless_sphere_measure`.
- **`PnpProof/SphereGaussian.lean`** → `PhysHSGaussian` (or `MathCore/SphereGaussian`):
  `physHermite`, `gegenbauer`, `gegenbauerScaled`, `gegenbauerScaled_tendsto_hermite`,
  `gaussianE`, `sphereProj`, `sphereUniform`, `weight_tendsto_gaussian`,
  `sphereUniform_rotation_invariant`, `hermite_sq_integral`, `hermite_normalization`,
  `gegenbauerScaled_rec/…_bound`, `normalization_tendsto`, `gammaMeasure`,
  `gaussian_concentration_sphere`, `poincare_borel_ae`.
- **`PnpProof/Foundations.lean`** (the `unitMeasure` / `squareMeasure` +
  null/countable/atomless fragment) → `PhysMeasureBasis` (or `MathCore/Foundations`),
  so the promoted modules have no `PnpProof` dependency at all.
- The Mehler/`Kopperman` analytic facts used by `BookProof` (`MehlerPrior`,
  `mehler_concentrates_on_sphere`, `substrate_separable`) move to a
  `PhysMehler` module (or are kept in the promoted `SphereGaussian`).

**Key rule:** the promoted modules must import **only** `Mathlib` (and each other)
— **never** `PnpProof`. This is what makes them reusable and `PnpProof` isolatable.

### G.2 — Repoint `BookProof/` and `RandomMap/` imports at the promoted modules

- `ChapterSolovay.lean`, `ChapterG3.lean`, `ChapterSolovayCoordinates.lean`,
  `ChapterKopperman.lean`, `Substrate.lean`: replace `import PnpProof.*` with the
  new `BookProof`/`MathCore` module(s), and rewrite the qualified names
  (`PnpProof.gammaMeasure` → `PhysHSGaussian.gammaMeasure`, etc.).
- `RandomMap/SchoenfeldPRA.lean` is **moved** to the RH folder (see G.3), so its
  `import PnpProof.Kopperman` is rewritten as part of that move — repointed at the
  promoted `PhysMehler` core where it uses the analytic content, with the
  P≠NP-specific `arith_truth_invariant`/`interpPi02` handled per G.3.
- **Definition of done:** after the repoint, `grep -rlnE "^import PnpProof"`
  across `BookProof/`, `Book/`, `Singularity/`, `RandomMap/` returns **nothing**.

### G.3 — Make `PnpProof/`, `UnusedRoute/`, `UsedRoute/` one-way leaves

- `PnpProof/` may import the promoted shared modules (it can *use* the general
  math), but **nothing outside** `PnpProof/`, `UnusedRoute/`, `UsedRoute/` may
  import them. Verify `PnpProof/`, `UnusedRoute/`, `UsedRoute/` do **not** import
  `BookProof` (already true — confirmed) and that the rest of the project no
  longer imports them.

- **`UnusedRoute.SchoenfeldPRA` is Riemann-Hypothesis work, not P≠NP and not
  part of the RandomMap default thread.** Its header documents it as "the
  historical PRA/Schoenfeld spine", and it imports `UnusedRoute.RcpEuler` and
  `UnusedRoute.SchoenfeldMatrix`. It was moved to the RH folder
  (`UnusedRoute/`), taking its two intentional RH `sorry`s out of the default
  thread.  The `Kopperman` `interpPi01`/`interpPi02` arithmetic-truth parts it
  reuses are the P≠NP-side of `PnpProof`; `SchoenfeldPRA` imports the promoted
  `BookProof.PhysMehler` analytic core and stays an isolated RH file.

- **Remaining isolation work (author rule: `UnusedRoute/` may depend on the
  rest of the project, never vice versa).**  The default-reachable
  `RandomMap/RandomMap2.lean` still does `import UnusedRoute.SchoenfeldPRA`, and
  `RandomMap/RcpRandomMap2Bridge.lean` is wholly RH-dependent.  Both must be
  cleaned:
  - `RandomMap2.lean` uses only `rcpPriorOnSubstrate` /
    `rcpPriorOnSubstrate_isProb` (thin wrappers over
    `BookProof.PhysMehler.exists_atomless_prob_substrate`) and `Substrate`
    (already shared).  Move those two wrappers into `BookProof/PhysMehler.lean`
    (or define them locally in `RandomMap2`), and repoint `RandomMap2`'s import
    at `BookProof.PhysMehler` — dropping `UnusedRoute.SchoenfeldPRA`.
  - `RandomMap2.lean` **Phase 7 (lines 844–931) is RH content** and must move to
    `UnusedRoute/`: `zeta_no_zeros_right_half_plane'`,
    `riemann_hypothesis_decoupled`, `eta_non_zero_real_axis`.  (Phases 1–6 and
    8+ are the generic decoupled Kopperman–Solovay framework and stay.)
  - `RandomMap/RcpRandomMap2Bridge.lean` (the `RH_PRA → RectangleRH` bridge)
    is wholly RH and should move to `UnusedRoute/`.
  - After the split, `grep -rlnE "import UnusedRoute" RandomMap/` returns
    nothing, and the default build (`BookProof`, `Book`, `Singularity`, and the
    `Book/ChapterSolovay` → `RandomMap2` edge) has no `UnusedRoute` dependency.

- **Definition of done:** `lake build` (default targets) green; the only
  cross-directory imports into `PnpProof/`, `UnusedRoute/`, `UsedRoute/` come
  from `PnpProof/` itself (or are documented, isolated `EXTERNAL`/RH cases);
  `grep -rlnE "import RandomMap.SchoenfeldPRA"` **and**
  `grep -rlnE "import UnusedRoute" RandomMap/` both return nothing.

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
   repository are `UnusedRoute/SchoenfeldPRA.lean:163,178` (intentional).
5. `#print axioms` spot-checks on every new headline show only `propext`,
   `Classical.choice`, `Quot.sound`.
6. `BookProof/STATUS.md` updated with a dated wave note, including any recorded
   disparity between each new coherent-state claim and the proved theorem (per the
   provenance note above).
7. Part D: `lake build` (default targets) green with **no in-scope warnings**
   (`BookProof/`, `Book/`, `Singularity/`, root files; the two intentional
   `UnusedRoute/SchoenfeldPRA.lean` `sorry` notices excepted); `lake build RandomMap`
   green; `lake build book` green. Excluded directories (`PnpProof/`,
   `UnusedRoute/`, `UsedRoute/`) untouched.

## Execution guidance

- Work the queue **in order** (Part A before Part B; Parts C, D, F, G may proceed
  in parallel per wave), landing several deliverables per pass (author mandate:
  target ≥ 4 deliverable groups per pass).
- **Part D scope is strict:** never edit `PnpProof/`, `UnusedRoute/`, `UsedRoute/`
  even when their warnings appear in a shared `lake build` log; only `BookProof/`,
  `RandomMap/`, `Singularity/`, `Book/`, and the root files are in scope.
- Do not add another instance of an already-general result (the dimension-count
  thread is closed at `N = 6`).
- Keep every theorem `sorry`-free / `axiom`-free. Where a full claim is out of
  reach, state the provable core precisely and record the gap in
  `BookProof/STATUS.md` / `FORMALIZATION_ROADMAP.md`; never `sorry` a strong claim.
- Prefer `EXTERNAL` named hypotheses over `axiom` for the deep external theorems.
- Fix warnings at the source (use the `…?`-suggested `simp only`/`aesop`/`omega`
  forms, drop unused args); never suppress with file-top `set_option linter.* false`
  and never edit `lakefile.toml` `[leanOptions]`.