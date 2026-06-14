# Implementation Plan: Lean 4 Formalization of `pnp.tex`

**Audience**: a Lean 4 formalization agent. The agent is assumed to be good at
translating *complete English proofs* into Lean, and **not** expected to invent
mathematical arguments. Accordingly:

- Every item marked **PROVABLE** comes with a complete English proof at
  formalization granularity. Translate it; do not redesign it.
- Every item marked **OPEN** or **MODELLING** has *no* complete proof in this
  repo or in `pnp.tex`. **Do not improvise.** Stop and report. (An earlier
  revision of this plan sanctioned explicitly-named `axiom`s in designated
  places; that escape hatch is **withdrawn** — the implemented development is
  axiom-free beyond Lean's `propext`/`Classical.choice`/`Quot.sound` and must
  stay so. The only escape hatch is stop-and-report.)
- Mathlib names below are given to the best of current knowledge and are
  marked **(search)** when not verified against the project snapshot. Before
  using any name, verify it:
  ```bash
  cd PnpProof && lake env lean --stdin <<< '#check MeasureTheory.measure_singleton'
  ```
  If a name is absent, search for the nearest equivalent (`exact?`,
  `loogle`, grepping `.lake/packages/mathlib`); if no equivalent exists, the
  English proof given here is complete enough to prove the fact from scratch.

**Source**: `pnp.tex` (this directory). **Style reference**:
`RiemannProof/IMPLEMENTATION_PLAN.md` and `AGENTS.md` (build commands, line
limits, `set`/`linarith` pitfalls all apply here too).

---

## Status (2026-06-14): implementation COMPLETE — contents re-confirmed

The development lives in `PnpProof/` as a second library of this lake project
(see deviation 1 below). It compiles **sorry-free and axiom-free** (only Lean's
standard `propext`, `Classical.choice`, `Quot.sound`). Build verified
2026-06-12 (8034 jobs, including `Comparator.lean` and the T5 theorems); file
inventory and the sorry/axiom-free status re-confirmed by inspection 2026-06-14
(the seven `PnpProof/*.lean` files below; the only `sorry` strings in the tree
are inside comments in `Main.lean`). Only style-linter warnings remain
(`linter.style.multiGoal`, `linter.style.whitespace`, `linter.style.longLine`).

**A new direction was proposed 2026-06-14** (mixed-measure "indicator
separation" + a Kopperman Hilbert-space "standard model" + a Shoenfield-style
`Π⁰₂` absoluteness transfer to the Clay statement). Its assessment is **Part 8**;
the constructive follow-through is **Part 9**. Short version: the **Kopperman
formalism itself is now formalized** in `PnpProof/Kopperman.lean` (compiles,
`sorry`-free, axiom-free) — the substrate Hilbert space, the decidable dense
skeleton, the Mehler prior, and the atomless prior, all assembled from proved
lemmas. The measure-theoretic "indicator" half (Phases 1–3) restates
already-implemented lemmas and is admissible *only* under the existing model
fence. The absoluteness-transfer half (Phases 4–5) is **rejected as an `axiom`**:
an axiom is the one construct that stops Lean from checking, so it cannot "let
Lean decide"; the bridge may instead be *stated as a theorem and attempted*
(Part 9), and it does not close — `model_vs_clay_disjointness` (T5) is the proved
reason. No axiom is added; the development stays axiom-free.

**A further maintainer directive (2026-06-14 #2), refined: the minimal
assumptions needed to *define* the P-vs-NP statement within the Kopperman
formalism are exactly the commitments of the Kopperman formalism itself — a base
that is *incomparable* with PA (it neither contains nor is contained in PA:
different language) yet *co-consistent* with both PA and ZFC.** Because the
formalism is consistent with PA and ZFC and pins down the *standard* naturals (its
decidable skeleton is indexed by genuine `ℕ`), the arithmetic P-vs-NP sentence
defined inside it is **absolute** — it is literally the standard P-vs-NP statement,
not a model-relative surrogate. This *corrects* the earlier "reduce to PA-or-weaker"
framing: the goal is **not** to weaken the base toward PA, but to take the
formalism's *own* (PA-incomparable) base as the definitional minimum and lean on
co-consistency + standard-`ℕ` absoluteness for identity with the standard
statement. Key distinction: this is a **definability** base (what you need to *write
the statement down*), not a **provability** base (what you need to *prove* it). "P ≠
NP" is a `Π⁰₂` *arithmetical* sentence (machine codes, inputs, polynomial run-time
bounds only — no reals, measures, or uncountable sets), and the formalism's
decidable skeleton supplies exactly the encoding of computation needed to express
it. The Lean-native, honest realizations: **(i)** import-level tier separation (the
arithmetic statement in a module importing neither the measure theory nor the
`Formalism` — the witness that the two bases are independent/incomparable);
**(ii)** axiom-footprint tracking via `#print axioms` (does the arithmetic tier
depend on `Classical.choice`/measure theory? — the dependency proxy); **(iii)** the
conservativity theorem **T-conserv** (Part 9/10): an arithmetic `φ : Prop` over `ℕ`
has a truth value independent of any `Formalism` and of the `ZFSet`↔Kopperman side
— the Lean witness of co-consistency + standard-`ℕ` identity (Lean's `ℕ` has *no*
nonstandard elements, so the sentence is automatically the standard one). What is
**not** available and must not be improvised: an *internal* statement of
"incomparable-with-PA / co-consistent" or `PA ⊢ P_ne_NP` — those need formalized
theories/interpretations (`FirstOrder.Language`, a provability predicate), which
mainline Mathlib lacks (a large separate meta-logic project, like the `L_{ω₁,ω₁}`
object); flag, do not build ad hoc. The identity is **not** a backdoor to the
bridge: defining the *standard* sentence inside the formalism does not prove it —
T5's disjointness stands. See **Part 11**.

Always restore the Mathlib cache before building:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get   # NEVER skip this — otherwise Mathlib compiles from source
lake build PnpProof
```

### What is DONE — do not re-implement anything in this table

| File | Items implemented |
|------|-------------------|
| `PnpProof/Foundations.lean` | Part 0 (`unitMeasure`, `squareMeasure`, probability instances) + F1–F8 |
| `PnpProof/Counting.lean` | C1–C5 (`Gate`, `Circuit`, `Circuit.eval`, `Circuit.nodeValNat_agree`, Shannon bounds for `8 ≤ n`) |
| `PnpProof/FunctionSpace.lean` | H1–H3, H5–H7 (H4 subsumed — deviation 2) |
| `PnpProof/SphereGaussian.lean` | **All of Part 3b**: G0–G4 (incl. `normalization_tendsto` and `hermite_normalization` — deviation 6), G5 incl. `sphereUniform_rotation_invariant`, G6 `poincare_borel_ae`, G7 `gaussian_concentration_sphere` (deviation 7) |
| `PnpProof/Model.lean` | M1–M4 (representation: deviation 3) |
| `PnpProof/Comparator.lean` | **N1**: the explicit `O(k)` comparator circuit — `Circuit.snoc` append API, per-bit register update `step`, MSB-first fold `buildLT`, `div_pow_succ_compare`, `bitsOf`, `fullCircuit`, `verify_circuit_cheap` |
| `PnpProof/Main.lean` | T1 `selection_not_history`, T2 `almost_all_not_computable`, M5 as `verifyBits`/`verifyBits_computable` (deviation 4), T3 `model_P_ne_NP`, `mixed_to_continuous`, **N1** `model_P_ne_NP_circuit`, **T5** `model_vs_clay_disjointness` (with `DecidesSelection`, `dense_selection_domain`, `decidesSelection_unique`, `countable_language_decided_selections`, `selection_not_language_decidable`) |
| `PnpProof/Kopperman.lean` | **The Kopperman formalism, assembled** (Part 9): `structure Formalism`, `Substrate`/`substrate_separable`, `substrate_decidable_skeleton`, `MehlerPrior`/`mehler_isProbability`/`mehler_concentrates_on_sphere`, `admits_atomless_prior`, `modelPrior_atomless`. Plus **K-model** (Part 11): `model_has_prior`, `substrate_orthonormal_pair`, `exists_atomless_prob_substrate`, `formalismOfPrior`/`prior_formalismOfPrior`/`prior_surjective_onto_atomless`, `nonempty_formalism_substrate`, `koppermanSubstrate` — "choosing a measure = choosing a model". All from proved lemmas; `sorry`/axiom-free |

The per-lemma map is `PnpProof/IMPLEMENTED.md`. No mathematical work items
remain; the only open item is optional linter housekeeping — see Part 7.

### Ratified deviations from the original plan text

The implementation deviated from the letter of this plan in the following
ways; all are **ratified** — sections below that contradict them are
superseded:

1. **Layout**: `PnpProof` is a second library of the existing `RiemannProof`
   lake project (`lakefile.toml` has
   `defaultTargets = ["RiemannProof", "PnpProof"]`), not a sibling project.
   Part 0's "create a sibling project" instructions are obsolete.
2. **H4 subsumed**: the `ratStep` family was not built separately; its
   content (a countable dense subset of `L²`) follows from H1 + H5.
3. **Representation**: `K := ↥(Icc (0:ℝ) 1)`; selection functions are
   `C(K, ℝ)`; `ComputesSelection` is stated directly on them (no `extend`);
   `prior = (volume : Measure K).map selMap` with
   `selMap t u = u^(1/(1+t))` injective.
4. **M5 / NP side of T3**: realized as **computability** of the verifier
   (`verifyBits_computable : Computable …`), with `verifyBits` on `ℕ`. **No
   axiom was introduced and none is permitted** — the plan's old "labeled
   model axiom" fallback is withdrawn. The explicit `O(k)` circuit (N1) is
   now DONE: `Comparator.lean`'s `verify_circuit_cheap` feeds the NEW theorem
   `model_P_ne_NP_circuit`, stated beside the untouched `model_P_ne_NP`.
5. **T4 resolved prose-only**: no statement and **no `sorry`** committed (the
   plan's old sorry-stub option is withdrawn). The module docstring in
   `Main.lean` records why: a purely analytic approximation statement would
   be false (polynomial density), and drafting the computational statement is
   research. Do not add any T4 statement unless the maintainer supplies a
   precise statement plus a complete English proof.
6. **G4**: `normalization_tendsto` is stated in the post-change-of-variables
   form (the `x_old = x/√λ` substitution baked into the `[-√λ, √λ]` interval),
   proved by dominated convergence with the uniform bound
   `gegenbauerScaled_bound`; `hermite_normalization` (value `√π·2ⁿ/n!`) is
   fully proved by an integration-by-parts induction — the old OPEN-API
   fallback was not needed.
7. **G6/G7**: realized on the single probability space
   `gammaMeasure := Measure.infinitePi (fun _ => gaussianReal 0 1)` via
   `ProbabilityTheory.strong_law_ae` (both names verified present in the
   Mathlib pin). The finite-`k` Chebyshev fallback G7′ and the
   bounded-continuous weak-convergence corollary `poincare_borel` were not
   needed once the a.s. forms were available; they stay unformalized and are
   **not** on the queue.

---

## Part −1: Scope — what is and is not formalizable (READ FIRST)

`pnp.tex` is a physics-style paper. It contains three kinds of content, and
the formalization must keep them strictly separated, in three tiers:

- **Tier A (mathematics)** — precise theorems of measure theory, functional
  analysis, computability and counting. All formalizable; complete proofs
  given in Parts 1–3.
- **Tier B (the model)** — the paper's computational problem: a prior measure
  on a space of selection functions, dyadic discretization, the
  inverse-transform-sampling verifier. Formalizable as *definitions* plus
  theorems *about the model*; Parts 4–5.
- **Tier C (the bridge)** — the claim that the model's separation implies the
  standard (Clay) P ≠ NP statement. This is a modelling argument about what
  counts as "the proper computer model"; `pnp.tex` itself states it "still
  needs to be reviewed by experts". **It is not a mathematical theorem and
  must not be formalized as one.** It enters the development only as an
  explicitly-named `Prop`-level definition and a clearly-labeled remark
  (Part 6). Any attempt to "close the gap" in Lean is out of scope.

### Claim inventory (paper section → disposition)

| § | Claim in `pnp.tex` | Tier | Disposition |
|---|--------------------|------|-------------|
| 1, title | Selecting events ≠ rewriting history: conditioning on `y = y₀` is well-defined though `P(y = y₀) = 0` | A | **T1**, from F1, F3, F4 |
| 2 | Almost all Boolean functions on `n` bits need circuits of size ~`2^n/n` (Shannon) | A | **C3–C5** (self-contained counting proof) |
| 2 | Computable functions are countable; countable sets are null for atomless priors | A | **C1, C2, F2** |
| 2 | Turing-machine *time* lower bound `O(2^n/(n log n))` from circuit bound | A | **OUT OF SCOPE** (needs TM↔circuit simulation theory; not needed downstream — see Part 6) |
| 2, 3 | Uniform prior on the infinite-dimensional L² sphere | A/B | **Two-track**: the main chain uses surrogate **H7** (an atomless Borel probability on the sphere); the literal "uniform = Gaussian limit" content is rigorous mathematics and is formalized independently in **Part 3b (G1–G7)**: Gegenbauer→Hermite limit (lopez99), weight→Gaussian limit, normalization limit, and the Poincaré–Borel theorem (sphere marginals → Gaussian; SLLN concentration). |
| 3 | `p ≥ 0`, `∫p = 1` ⇒ wave-function `Ψ = √p ∈ L²`, `‖Ψ‖ = 1` | A | **H3** |
| 3 | Regular conditional probabilities exist on standard spaces | A | **F3** (Mathlib disintegration) |
| 4 | Fock–Guichardet space ≅ Guichardet space ≅ `L²([0,1])` | A | **Surrogate H6**: all infinite-dimensional separable Hilbert spaces are isometrically isomorphic. The Fock apparatus itself is **OUT OF SCOPE** (adds nothing used downstream). |
| 4 | Integers ↔ rational step functions; limit lands in `L²([0,1])` | A | **H4** |
| 5 | Abelian von Neumann algebra classification (the 5-item list) | A | **OUT OF SCOPE** (huge, unused). The piece actually *used* is F5+F8: atoms are countable, conditioning on the diffuse part gives an atomless measure. |
| 5 | Continuous vs mixed CDFs differ by a fixed amount on a rational interval | A | **F7** |
| 5–6 | Continuous and atomic measures are mutually singular (no Radon–Nikodym derivative) | A | **F6** |
| 6 | Option 1: the selected indicator function is verifiable but not computable ⇒ model-P ≠ model-NP | B | **T3** (theorem *about the model*; complete proof via M1–M5) |
| 6 | Option 2: randomness in the selection excludes it from the official P vs NP formulation "by definition" | C | Definitional remark only; **no theorem** |
| 6 | "This implies P ≠ NP" (Clay statement) | C | **NOT FORMALIZABLE** — Part 6 |
| 7 | Realistic version (approximate selection still separates) | B | **T4: statement only, OPEN** — the paper's argument is a sketch; the density inputs (H4, H5) are provided |
| 8 | Random-number generation has linear time complexity | C | Empirical claim; **not formalizable** (the paper says so itself: "We cannot prove this mathematically") |
| 9 | Machine Learning consequences | C | Prose; **not formalizable** |

### The final theorems of the development

```
T1  selection_not_history     — the title fact (fully proved)
T2  almost_all_not_computable — the prior gives measure 0 to machine-computable
                                selection functions (fully proved)
T3  model_P_ne_NP             — in the paper's model: the selected function is
                                a.s. not computed by any machine, while the
                                candidate-verification predicate is computable
                                with poly(k) bit operations (proved relative to
                                the cost model chosen in M5)
T4  realistic_version         — statement only (OPEN)
```

**T3 is the strongest honest formal content of §6.** It is a theorem about
the specific model (Tier B). The development must never name any theorem
`P_ne_NP` without the `model_` prefix.

---

## Part 0: Project setup — DONE (as deviation 1: second library, not a sibling project)

Create a sibling Lean project (do not touch `RiemannProof/`):

```
PnpProof/
  lean-toolchain            -- leanprover/lean4:v4.28.0  (same as RiemannProof)
  lakefile.toml             -- copy RiemannProof/lakefile.toml, rename to PnpProof,
                               same mathlib pin (rev = "v4.28.0")
  PnpProof.lean             -- imports all files below
  PnpProof/
    Foundations.lean        -- Part 1 (F1–F8)
    Counting.lean           -- Part 2 (C1–C5)
    FunctionSpace.lean      -- Part 3 (H1–H7)
    SphereGaussian.lean     -- Part 3b (G1–G7): uniform sphere ↔ Gaussian limit
    Model.lean              -- Part 4 (M1–M5)
    Main.lean               -- Part 5 (T1–T4) + Part 6 remarks
```

Import DAG: `Foundations ← {Counting, FunctionSpace} ← Model ← Main`;
`SphereGaussian` imports `Foundations` only and nothing imports it (it is an
independent Tier-A module; see Part 3b).
Build: `export PATH="$HOME/.elan/bin:$PATH"; lake exe cache get; lake build`.

Conventions (from `AGENTS.md`): ≤100-char lines, no trailing whitespace,
verify every Mathlib identifier before use, prefer term mode for one-step
proofs, keep section variables scoped.

**Sorry policy**: `sorry` is allowed only at the explicitly-marked OPEN items
(T4) and must carry a `-- OPEN: see IMPLEMENTATION_PLAN Part 5/T4` comment.
Everything else in this plan is expected to compile sorry-free.

Throughout, abbreviations:

```lean
open MeasureTheory Set
noncomputable section

/-- The unit interval as a measure space: Lebesgue restricted to [0,1]. -/
abbrev unitMeasure : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)

/-- The unit square with Lebesgue measure. -/
abbrev squareMeasure : Measure (ℝ × ℝ) :=
  volume.restrict (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)
```

Record once: `IsProbabilityMeasure unitMeasure` and
`IsProbabilityMeasure squareMeasure` — both from
`Measure.restrict_apply_univ`-style computation: `volume (Icc 0 1) = 1`
(`Real.volume_Icc`, `sub_zero`), and `volume (Icc 0 1 ×ˢ Icc 0 1) = 1`
(`Measure.volume_eq_prod` (search) + `Measure.prod_prod` (search), or
`Real.volume_Icc` twice and `mul_one`).

---

## Part 1: Foundations (`Foundations.lean`) — measure theory — DONE

### F1. Points are null in continuous probability spaces — PROVABLE

```lean
theorem null_singleton_volume (y : ℝ) : volume ({y} : Set ℝ) = 0

theorem null_singleton {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [MeasurableSingletonClass α] [NoAtoms μ] (a : α) : μ {a} = 0
```

**Proof.** First: `Real.volume_singleton` (search; exists). Second: this is
Mathlib's `measure_singleton` (search; the `NoAtoms` class provides exactly
this). If the class instance route stalls, prove from `Real.volume_singleton`
for the only instantiation used (ℝ). Also record the restricted version:
`unitMeasure {y} = 0` by `Measure.restrict_apply` + `measure_mono` into the
unrestricted singleton, or `measure_mono_null (inter_subset_left)`. ∎

This formalizes the title's "the event `y = 0` has null probability".

### F2. Countable sets are null — PROVABLE

```lean
theorem countable_null {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [NoAtoms μ]
    {s : Set α} (hs : s.Countable) : μ s = 0
```

**Proof.** Mathlib: `Set.Countable.measure_zero` (search; exists with this
exact shape). Fallback proof: `s = ⋃ x ∈ s, {x}` over a countable index;
`measure_biUnion_null_iff` (search) or
`measure_iUnion_null_iff` after `Set.biUnion_of_singleton`; each `μ {x} = 0`
by F1. ∎

### F3. Selection exists: disintegration / regular conditional probability — PROVABLE

This is the positive half of the title fact: *selecting* events with `y = y₀`
is legitimate, via the conditional kernel.

```lean
theorem selection_exists :
    squareMeasure.fst ⊗ₘ squareMeasure.condKernel = squareMeasure
```

**Proof.** This is Mathlib's disintegration theorem for finite measures on
standard Borel product spaces:
`MeasureTheory.Measure.compProd_fst_condKernel` (search; lives near
`Mathlib/Probability/Kernel/Disintegration/`). `ℝ × ℝ` is standard Borel
(instances are automatic: `PolishSpace`, `BorelSpace`), `squareMeasure` is a
finite measure (probability, Part 0). The theorem should be `exact`-able once
the instances are found; the entire work item is instance bookkeeping. Record
the consequence in words as a docstring: *for `μ.fst`-a.e. `x`, the kernel
`μ.condKernel x` is a probability measure on the `y`-fibre — the
"deterministic selection of events" of §3.* ∎

If `condKernel` requires `[IsFiniteMeasure]` only, this is direct. If the
snapshot's API is stated for `kernel.condKernel`/`ProbabilityTheory.condDistrib`,
use whichever form exists; the *statement to keep* is "fst ⊗ₘ kernel = μ".

### F4. No complete history contains the selected event — PROVABLE

The negative half of the title fact: a complete history is a countable
sequence of samples; almost surely it never realizes `y = y₀`.

```lean
theorem no_history {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hlaw : ∀ n, ∀ y : ℝ, P {ω | Y n ω = y} = 0) (y₀ : ℝ) :
    P {ω | ∃ n, Y n ω = y₀} = 0
```

**Proof.** `{ω | ∃ n, Y n ω = y₀} = ⋃ n, {ω | Y n ω = y₀}` (`Set.ext`,
`Set.mem_iUnion`). Apply `measure_iUnion_null` (search; exists): each member
is null by `hlaw n y₀`. (Measurability of each set: `hY n` and
`measurableSet_singleton`, i.e. the set is `Y n ⁻¹' {y₀}` — only needed if
the chosen `measure_iUnion_null` variant demands it; there is a
null-set version `measure_iUnion_null` that does not.) ∎

The hypothesis `hlaw` is discharged in applications by F1 applied to the law
`P.map (Y n)` when that law has no atoms:
`P {ω | Y n ω = y} = (P.map (Y n)) {y}` by `Measure.map_apply (hY n)
(measurableSet_singleton y)`.

### F5. A finite measure has countably many point atoms — PROVABLE

Used to formalize §5's "a continuous measure is only truly continuous up to a
countable number of points" and as input to F8.

```lean
theorem countable_atoms {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] :
    {x | μ {x} ≠ 0}.Countable
```

**Proof.** Check first for a Mathlib lemma (search:
`Measure.countable_meas_pos`, `Measure.countable_meas_singleton_ne_zero`,
grep `countable` in `MeasureTheory/Measure`); if found, done. Otherwise:

1. For `n : ℕ`, let `A n := {x | 1/(n+1) < μ {x}}` (ENNReal inequality).
   Claim `A n` is finite. Suppose not; then (`Set.Infinite.exists_subset_card_eq`,
   search) for every `m : ℕ` there is a finite `F ⊆ A n` with `F.card = m`.
   Take `m` with `(m : ℝ≥0∞)/(n+1) > μ univ` — possible since `μ univ < ⊤`
   (`IsFiniteMeasure.measure_univ_lt_top`); concretely
   `m := ⌈(μ univ).toReal * (n+1)⌉₊ + 1` and convert with
   `ENNReal.div_lt_iff` / `ENNReal.lt_div_iff_mul_lt` (search exact forms,
   work in `ℝ≥0∞` throughout to avoid coercion pain; alternative: derive the
   contradiction as `(m : ℝ≥0∞) * (1/(n+1)) ≤ μ F` and bound `μ F ≤ μ univ`).
2. `μ F = ∑ x ∈ F, μ {x}` for finite `F` of points:
   `measure_biUnion_finset` (search) with pairwise-disjoint singletons
   (`Set.pairwiseDisjoint_singleton`-style; disjointness of `{x}`, `{y}` for
   `x ≠ y` is `Set.disjoint_singleton`), each measurable
   (`measurableSet_singleton`). Each term `> 1/(n+1)`, so
   `μ F > m/(n+1) > μ univ ≥ μ F` — contradiction (use
   `Finset.card_nsmul_le_sum`-style: `Finset.sum_lt_sum`/`Finset.le_sum`,
   in `ℝ≥0∞` strict inequalities are fine since everything is finite).
3. `{x | μ {x} ≠ 0} = ⋃ n, A n`: if `μ {x} ≠ 0` then `μ {x} > 0` (`pos_iff_ne_zero`,
   ENNReal), and `ENNReal.exists_inv_nat_lt` (search; or
   `ENNReal.exists_nat_gt` on the inverse) gives `n` with `1/(n+1) < μ {x}`.
4. Countable union of finite sets is countable:
   `Set.countable_iUnion` + `Set.Finite.countable`. ∎

### F6. Continuous and atomic parts are mutually singular — PROVABLE

Formalizes §6: "there is no Radon–Nikodym derivative between the two measures,
since the sets of null measure are disjoint".

```lean
theorem atomless_mutuallySingular_atomic {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [NoAtoms μ]
    {A : Set α} (hA : A.Countable) (hν : ν Aᶜ = 0) :
    μ ⟂ₘ ν
```

(`ν` is "purely atomic, carried by the countable set `A`".)

**Proof.** Unfold `Measure.MutuallySingular` (search; constructor
`⟨s, hs, h₁, h₂⟩` needs a measurable `s` with `μ s = 0` and `ν sᶜ = 0`).
Take `s := A`... but `A` need not be measurable in general σ-algebras; for the
spaces used (ℝ, Polish) countable sets are measurable:
`Set.Countable.measurableSet` (search; exists given
`MeasurableSingletonClass`). Then `μ A = 0` by F2 and `ν Aᶜ = 0` by
hypothesis. ∎

Corollary worth recording (the paper's phrasing): if `μ ⟂ₘ ν` and both are
probability measures, then `¬ μ ≪ ν` — from
`Measure.MutuallySingular` + `μ ≠ 0`: the singular set `s` has `ν s = 0`...
careful with directions: use
`Measure.MutuallySingular.absolutelyContinuous`-type lemmas if present
(search `MutuallySingular`, `AbsolutelyContinuous` interaction:
`Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular`-like); fallback:
`μ ≪ ν` and `ν s = 0` give `μ s = 0`; with `μ sᶜ = 0` get
`μ univ ≤ μ s + μ sᶜ = 0` (`measure_union_le` on `s ∪ sᶜ = univ`),
contradicting `μ univ = 1`.

### F7. A jump separates a mixed CDF from a continuous one on a rational interval — PROVABLE

Formalizes §5's conversion step: "there is an interval with rational endpoints
… where there is a finite difference between the two cumulative probability
distributions".

```lean
theorem cdf_jump_separation (F G : ℝ → ℝ) (hF : Monotone F) (hG : Monotone G)
    (x₀ : ℝ) (hFc : ContinuousAt F x₀) (ε : ℝ) (hε : 0 < ε)
    (hjump : ∀ a b : ℝ, a < x₀ → x₀ < b → G b - G a ≥ ε) :
    ∃ a b : ℚ, (a:ℝ) < b ∧ |(G b - G a) - (F b - F a)| ≥ ε / 2
```

(The hypothesis `hjump` is the clean way to say "G has an atom of mass ≥ ε at
x₀" without committing to a measure API; when `G` is the CDF of `ν` with
`ν {x₀} ≥ ε`, `hjump` holds because `G b - G a = ν (a, b] ≥ ν {x₀}` —
record that as a separate glue lemma `cdf_atom_jump` using
`ProbabilityTheory.cdf` (search) and `measure_mono` if and when the CDF API is
adopted in Part 4; it is not needed for T1–T3.)

**Proof.**
1. By `ContinuousAt F x₀` (metric form, `Metric.continuousAt_iff` (search)),
   obtain `δ > 0` with `|F x - F x₀| < ε/4` for `|x - x₀| < δ`.
2. Pick rationals `a ∈ (x₀ - δ, x₀)` and `b ∈ (x₀, x₀ + δ)`
   (`exists_rat_btwn`, applied twice). Then `(a:ℝ) < b` (`lt_trans` through
   `x₀`).
3. `F b - F a = (F b - F x₀) + (F x₀ - F a) ≤ ε/4 + ε/4 = ε/2` — each term
   `< ε/4` in absolute value by step 1 (`abs_lt`, `linarith`). Also
   `F b - F a ≥ 0` by `hF` (`sub_nonneg`, `hF (le_of_lt ...)`).
4. `G b - G a ≥ ε` by `hjump a b` (with `a < x₀ < b` from step 2).
5. `(G b - G a) - (F b - F a) ≥ ε - ε/2 = ε/2 ≥ 0`, so the absolute value is
   the value itself (`abs_of_nonneg`); `linarith` closes. ∎

### F8. Conditioning a mixed measure on its diffuse part yields an atomless measure — PROVABLE

Formalizes §5/§6: "If it is in part continuous, and in part countable, then we
can choose just the continuous part of the sample space."

```lean
theorem cond_diffuse_noAtoms {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    (hpos : μ {x | μ {x} ≠ 0}ᶜ ≠ 0) :
    NoAtoms ((μ {x | μ {x} ≠ 0}ᶜ)⁻¹ • μ.restrict {x | μ {x} ≠ 0}ᶜ)
```

**Proof.** Let `A := {x | μ {x} ≠ 0}` (countable by F5, measurable by
`Set.Countable.measurableSet` as in F6, so `Aᶜ` measurable). Build the
`NoAtoms` instance via its constructor (search the exact constructor:
`⟨fun x => ...⟩` proving `∀ x, _ {x} = 0`):
for any `x`,
`(c • μ.restrict Aᶜ) {x} = c * μ ({x} ∩ Aᶜ)` (`Measure.smul_apply`,
`Measure.restrict_apply (measurableSet_singleton x)`). Two cases:
- `x ∈ A`: `{x} ∩ Aᶜ = ∅` (`Set.singleton_inter_eq_empty.mpr`), measure 0,
  `mul_zero`.
- `x ∉ A`: then `μ {x} = 0` (definition of `A`, `not_not`), and
  `μ ({x} ∩ Aᶜ) ≤ μ {x} = 0` (`measure_mono inter_subset_left`), so the
  product is 0. ∎

The normalization constant: also record
`IsProbabilityMeasure ((μ Aᶜ)⁻¹ • μ.restrict Aᶜ)` given `hpos` and
finiteness — `Measure.smul_apply`, `Measure.restrict_apply_univ`,
`ENNReal.inv_mul_cancel hpos (measure_ne_top μ _)`.

---

## Part 2: Computability and counting (`Counting.lean`) — DONE

### C1. Computable functions are countable — PROVABLE

```lean
theorem countable_computable : {f : ℕ → ℕ | Computable f}.Countable
```

**Proof.** Every computable `f` has a code: from `Computable f` get
`Nat.Partrec ↑f` (unfold `Computable`; it is `Partrec` of the coercion —
check the definitional path: `Computable f ↔ Partrec ↑f` should be
definitional or `Computable` is defined that way), then
`Nat.Partrec.Code.exists_code` (search; exists:
`Nat.Partrec f ↔ ∃ c, c.eval = f`) yields `c : Nat.Partrec.Code` with
`c.eval = ↑f`. Define `decode : Nat.Partrec.Code → (ℕ → ℕ) :=
fun c n => ((c.eval n).toOption.getD 0)` — for a total `f` with code `c`,
`c.eval n = Part.some (f n)`, and `Part.toOption`/`getD` recovers `f n`
(lemmas: `Part.some_toOption` (search), `Option.getD_some`). Hence
`{f | Computable f} ⊆ Set.range decode`. `Nat.Partrec.Code` is countable
(`Denumerable`/`Encodable` instance exists in Mathlib — search
`Nat.Partrec.Code.instDenumerable` or the `Primcodable` instance; any of them
gives `Countable`). Conclude with `Set.countable_range` and
`Set.Countable.mono`. ∎

Variant to record (same proof, used by M-layer): for any `Primcodable` types
`α, β`: `{f : α → β | Computable f}.Countable` — via
`Computable f → Computable (encode ∘ f ∘ decode)`-style transport, **or**
simply repeat the argument with `Computable f` unfolded to a `Nat.Partrec`
statement about `encode`-conjugated functions. If this generality gets
painful, the only instantiation needed downstream is
`α = ℕ × ℕ`, `β = ℕ` — do that one concretely.

### C2. Computably-coded reals form a Lebesgue-null set — PROVABLE

Formalizes §2's "almost all numerical functions are not in P" in its sharpest
measure form (P ⊆ computable, so null for computable already gives null for P).

```lean
/-- The k-th binary digit of x ∈ [0,1). -/
def binDigit (k : ℕ) (x : ℝ) : Bool := decide (1 ≤ Int.fract (2^k * x) * 2)

theorem null_computable_digits :
    volume {x : ℝ | x ∈ Ico (0:ℝ) 1 ∧ Computable fun k => binDigit k x} = 0
```

**Proof.**
1. **Digits determine the point**: for `x y ∈ [0,1)`, if
   `binDigit k x = binDigit k y` for all `k`, then `x = y`. Proof: show by
   induction on `k` that `x` and `y` lie in the same dyadic interval
   `[i/2^k, (i+1)/2^k)`; the digit at step `k` selects the half. Concretely,
   prove the reconstruction lemma
   `x = ∑' k, (if binDigit k x then (1:ℝ) else 0) / 2^(k+1)` — by showing the
   partial sums are `⌊2^k x⌋ / 2^k` (induction on `k`, unfolding `Int.fract`
   and the floor-doubling identity `⌊2a⌋ = 2⌊a⌋ + (if 1 ≤ Int.fract a * 2
   then 1 else 0)`; search `Int.floor` API: `Int.floor_intCast`,
   `Int.fract`, `Int.floor_eq_iff`) and `|x - ⌊2^k x⌋/2^k| < 2^(-k)`
   (`Int.sub_floor_div_mul_nonneg`-style; direct from `Int.floor_le` and
   `Int.lt_floor_add_one` after dividing by `2^k`), then `tendsto` of the
   partial sums and uniqueness of limits (`tendsto_nhds_unique` with the
   geometric bound `Tendsto (fun k => (2:ℝ)^(-k)) atTop (𝓝 0)`,
   `tendsto_pow_atTop_nhds_zero_of_lt_one`-style (search)). Equality of digit
   functions then forces equality of the two tsums, hence `x = y`.
   *This is the longest single proof in Part 2; budget accordingly.*
2. **Countability**: the map `x ↦ (fun k => binDigit k x)` is injective on the
   set (step 1), and its image is contained in
   `{g : ℕ → Bool | Computable g}`, which is countable by C1's variant
   (`β = Bool` is `Primcodable`). An injection from `S` into a countable set
   makes `S` countable: `Set.Countable` via
   `Set.countable_of_injective_of_countable_image`-style (search; or:
   image countable + `Set.InjOn` ⇒ `Set.Countable` by
   `Set.Countable.preimage_of_injOn`-like; simplest available route:
   `(himage.mono image_subset).to_subtype` + `Function.Injective` on
   subtypes — if the API hunt stalls, use
   `Set.countable_iff_exists_injOn` (search) directly).
3. **Null**: F2 with `volume` (`NoAtoms volume` instance exists for ℝ). ∎

*(Optional, skip unless cheap: the Cantor-space phrasing with the fair-coin
product measure. Requires the infinite product measure
(`Measure.infinitePi`-like, search `Mathlib/Probability` for `productMeasure`
/ Ionescu–Tulcea); the [0,1] phrasing above is the one used downstream.)*

### C3. Boolean circuits — DEFINITIONS

Mathlib has no circuit theory; define from scratch. Design for easy counting:
gates are topologically ordered by construction, node `k` may only read nodes
`< n + k` (inputs occupy nodes `0..n-1`).

```lean
/-- A gate reading from `m` available nodes. `copy` enables padding. -/
inductive Gate (m : ℕ)
  | and (i j : Fin m) | or (i j : Fin m) | not (i : Fin m) | copy (i : Fin m)
  deriving DecidableEq

/-- A circuit with `n` inputs and exactly `s` gates, output = last gate. -/
structure Circuit (n s : ℕ) where
  gate : (k : Fin s) → Gate (n + k)

namespace Circuit
/-- Value of node `k` (inputs then gates), by strong recursion on `k`. -/
def nodeVal (C : Circuit n s) (x : Fin n → Bool) : (k : Fin (n + s)) → Bool
/-- The function computed (s ≥ 1; output is the last node). -/
def eval (C : Circuit n (s+1)) (x : Fin n → Bool) : Bool :=
  C.nodeVal x ⟨n + s, by omega⟩
end Circuit

/-- Functions on n bits computable by some circuit with ≤ s gates
    (padding via `copy` makes "≤ s" equal "= s"). -/
def computableBySize (n s : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ C : Circuit n (s+1), C.eval = f}
```

Implementation notes: define `nodeVal` by well-founded recursion on `k.val`
(or structurally: define `vals : (k : ℕ) → k ≤ n + s → Bool` by strong
induction with `Nat.lt_wfRel`; for `k < n` return `x ⟨k, _⟩`; else apply the
gate at `k - n`, whose wires point to nodes `< k` by the `Fin (n + (k-n))`
typing — the recursion is well-founded because wire indices are strictly
smaller). Provide the padding lemma:

```lean
theorem computableBySize_mono (n) {s t : ℕ} (h : s ≤ t) :
    computableBySize n s ⊆ computableBySize n t
```
**Proof.** Extend a circuit by `t - s` trailing `copy` gates, each copying the
previous output node (index `n + s + j - 1`, in range). Show by induction on
the padding length that `nodeVal` of old nodes is unchanged (the recursion
only looks downward) and each copy node carries the old output. ∎
*(Mildly fiddly Fin arithmetic; `omega` everywhere.)*

### C4. Circuit counting — PROVABLE

```lean
instance : ∀ m, Fintype (Gate m) := ...   -- derive or explicit equiv
theorem card_gate (m : ℕ) : Fintype.card (Gate m) = 2*m^2 + 2*m

instance : Fintype (Circuit n s) := ...    -- Pi-type of Fintypes
theorem card_circuit_le (n s : ℕ) (hns : 1 ≤ n) :
    Fintype.card (Circuit n s) ≤ (4 * (n + s)^2)^s
```

**Proof.** `Gate m ≃ (Fin m × Fin m) ⊕ (Fin m × Fin m) ⊕ Fin m ⊕ Fin m`
(explicit `Equiv`; or `derive Fintype` and compute card by `decide` for the
shape — better to do the explicit equiv and `simp [Fintype.card_sum,
Fintype.card_prod, Fintype.card_fin]`). `Circuit n s` is a dependent function
type into Fintypes: `Fintype.card (Circuit n s) = ∏ k : Fin s,
(2*(n+k)^2 + 2*(n+k))` (`Fintype.card_pi`-style after an `Equiv` between the
structure and the Pi type — `Fintype.card_congr` with
`(Equiv.refl _)`-packaged structure-eta, or define `Circuit` as a plain `def`
abbreviating the Pi type to avoid the equiv entirely — **recommended**: make
`Circuit n s := (k : Fin s) → Gate (n + k)` a `def`, not a structure).
Bound each factor: for `k < s`, `2*(n+k)^2 + 2*(n+k) ≤ 4*(n+s)^2` since
`n + k ≤ n + s` and `2m² + 2m ≤ 4m²` for `m ≥ 1` (`nlinarith`/`omega`-friendly;
`m ≥ 1` from `hns`). Product of `s` factors each ≤ B is ≤ B^s
(`Finset.prod_le_pow_card`, search). ∎

### C5. Shannon: almost all Boolean functions need > 2^n/(4n) gates — PROVABLE

```lean
theorem card_computableBySize_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (computableBySize n (2^n / (4*n))) ≤ 2^(3 * 2^n / 4)

theorem shannon_fraction (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (computableBySize n (2^n / (4*n))) * 2^(2^n / 4)
      ≤ Fintype.card ((Fin n → Bool) → Bool)
```

**Proof.** Let `s := 2^n / (4*n) + 1` (the `+1` matches the `s+1` in the
definition; adjust constants below accordingly — the slack absorbs it).
`computableBySize n _` is the image of `Circuit.eval`, so its card is ≤ the
card of the circuit type (`Nat.card_image_le`-style; with the `def`-Pi
encoding, `Set.ncard_image_le` or `Nat.card_le_card_of_surjective` from the
eval map onto the subtype — cleanest: `Nat.card (computableBySize n s) ≤
Fintype.card (Circuit n (s+1))` via `Nat.card_le_card_of_surjective` on
`fun C => ⟨C.eval, C, rfl⟩`).

Numeric chain (all in ℕ, `omega`/`Nat.pow` lemmas; do it in this order):
1. `n + s ≤ 2^n` for `n ≥ 2`: `s ≤ 2^n/(4n) + 1 ≤ 2^(n-2) + 1` and
   `n + 2^(n-2) + 1 ≤ 2^n` (induction or `Nat.lt_pow_self`-style with
   `omega` glue; provable by induction on n from the base n = 2).
2. Hence `4*(n+s)^2 ≤ 4 * 2^(2n) = 2^(2n+2)` and
   `Fintype.card (Circuit n (s+1)) ≤ (2^(2n+2))^(s+1) = 2^((2n+2)*(s+1))`
   (`pow_le_pow_left`, `pow_mul`).
3. `(2n+2)*(s+1) ≤ 3 * 2^n / 4` for `n ≥ 4`:
   `s + 1 ≤ 2^n/(4n) + 2`, so `(2n+2)*(s+1) ≤ (2n+2)*2^n/(4n) + (4n+4)`.
   First term: `(2n+2)*2^n/(4n) ≤ (n+1)*2^n/(2n) ≤ (5/8)·2^n` in ℕ-friendly
   form: `8*(n+1) ≤ 10*n` for `n ≥ 4` ⇒ `(n+1)*2^n/(2n) ≤ 5*2^n/8` — to
   avoid ℕ-division pitfalls, prove the multiplied-out inequality
   `8 * ((2*n+2)*(s+1)) ≤ 6 * 2^n` directly: substitute the bound
   `s+1 ≤ 2^n/(4*n) + 2 ≤ 2^n/(4*n) + 2`, use `Nat.div_mul_le_self` to clear
   the division (`(2^n/(4n)) * (4n) ≤ 2^n`), and `omega`/`nlinarith` with
   `2^n ≥ 16n` for `n ≥ 4` (small induction lemma `16 * n ≤ 2^n` for
   `n ≥ 7`... **careful**: `16n ≤ 2^n` first holds at n = 8; for n ∈ {4..7}
   check the target inequality numerically by `decide` on each case, or
   strengthen `hn` to `8 ≤ n` and state the small-n cases separately — the
   *recommended* simplification: state both theorems for `8 ≤ n`; nothing
   downstream needs small n).
4. `Fintype.card ((Fin n → Bool) → Bool) = 2^(2^n)`:
   `Fintype.card_fun` (search; `card (α → β) = card β ^ card α`) twice +
   `Fintype.card_bool`, `Fintype.card_fin`.
5. Combine: `card * 2^(2^n/4) ≤ 2^(3·2^n/4) * 2^(2^n/4) = 2^(3·2^n/4 + 2^n/4)
   ≤ 2^(2^n)` — last step needs `3*2^n/4 + 2^n/4 ≤ 2^n`, exact since
   `4 ∣ 2^n` for `n ≥ 2` (`Nat.div_add_div_same`-style after
   `Nat.div_mul_cancel`; or keep everything as `2^(n-2)` multiples:
   `3*2^n/4 = 3*2^(n-2)`, `2^n/4 = 2^(n-2)`, `3*2^(n-2) + 2^(n-2) = 2^n` by
   `ring_nf`/`omega` with `pow_succ`). ∎

**Numeric care flag**: ℕ-division is the main hazard in C5; whenever stuck,
multiply through and use `Nat.div_mul_le_self` / `Nat.le_div_iff_mul_le`.
It is acceptable to weaken constants (e.g. `2^n/(8n)` gates, `2^(7·2^n/8)`
bound) if that simplifies arithmetic — the downstream use (T2 narrative) only
needs *some* exponential-fraction statement.

---

## Part 3: Function space (`FunctionSpace.lean`) — DONE (H4 subsumed, deviation 2)

Fix notation: `μ₀₁ := unitMeasure`, `L2 := Lp ℝ 2 μ₀₁`,
`Linf := Lp ℝ ⊤ μ₀₁`.

### H1. `L²([0,1])` is separable — PROVABLE (instance lookup)

```lean
example : TopologicalSpace.SeparableSpace (Lp ℝ 2 unitMeasure) := inferInstance
```

Mathlib provides separability of `Lp` for `p ≠ ∞` over second-countable /
standard measure setups (search `MeasureTheory.Lp` + `SeparableSpace`
instances; `Measure.restrict` of `volume` on ℝ should satisfy the needed
`SecondCountableTopology` + `μ.SigmaFinite`-type side conditions, possibly via
`SeparableMeasureSpace`-like classes — search `Mathlib/MeasureTheory/Function/
LpSeparable` or similarly named file). If the instance genuinely does not
fire, this fact is *only narrative* (not used downstream except in H6's
instantiation) — H6 can instead be stated for an abstract separable Hilbert
space and instantiated later. Do not sink time here.

### H2. `L^∞([0,1])` is NOT separable — PROVABLE

Formalizes §1/§8: "`L^∞` is non-separable", the paper's reason why
deterministic evolutions "cannot be calculated for all practical purposes".

```lean
theorem linf_not_separable :
    ¬ TopologicalSpace.SeparableSpace (Lp ℝ ⊤ unitMeasure)
```

**Proof.**
1. **The separated family.** For `t ∈ (0,1]`, let
   `u t := indicatorConstLp ⊤ (measurableSet_Ioc) (hμ t) (1:ℝ)` with the set
   `Ioc 0 t` — `MeasureTheory.indicatorConstLp` (search; exists), side
   condition `μ₀₁ (Ioc 0 t) ≠ ∞` from finiteness.
2. **1-separation.** For `0 < s < t ≤ 1`:
   `‖u t - u s‖ = 1`. The difference is (a.e.) the indicator of `Ioc s t`
   (`indicatorConstLp_sub`-like API may not exist; work at the `eLpNorm`
   level: `Lp.norm_def`, the representative of the difference is a.e.
   `(Ioc 0 t).indicator 1 - (Ioc 0 s).indicator 1 = (Ioc s t).indicator 1`
   — prove the set identity `indicator_diff`-style (search
   `Set.indicator_diff`; here `Ioc 0 s ⊆ Ioc 0 t` and
   `Ioc 0 t \ Ioc 0 s = Ioc s t`, `Set.Ioc_diff_Ioc`-search), then
   `eLpNorm_congr_ae`).
   - Upper bound: indicator of any set with constant 1 has
     `eLpNorm ... ⊤ ≤ 1`: `eLpNorm_indicator_const_le` (search; for `p = ⊤`
     there may be `eLpNorm_exponent_top` + `eLpNormEssSup_indicator_const_le`).
   - Lower bound: `μ₀₁ (Ioc s t) = ENNReal.ofReal (t - s) > 0`
     (`Real.volume_Ioc`, restriction inside `[0,1]`:
     `Measure.restrict_apply` and `Ioc s t ∩ Icc 0 1 = Ioc s t` for
     `0 < s < t ≤ 1` — `Set.inter_eq_left`, interval inclusion by `omega`-style
     `constructor <;> intro <;> ...`/`Set.Ioc_subset_Icc_self` + endpoints).
     If `eLpNormEssSup < 1` then the set `{x | 1 ≤ |f x|} ⊇ Ioc s t` would be
     null (definition of essSup: `eLpNormEssSup_lt_iff`-search /
     `ae_lt_of_essSup_lt`), contradicting positive measure. Search first:
     `eLpNormEssSup_indicator_const_eq` (an *equality* lemma for indicators
     with nonzero constant on positive-measure sets likely exists — grep
     `indicator_const` in `MeasureTheory/Function/LpSeminorm`).
3. **Separated ⇒ not separable.** Suppose `SeparableSpace`; get a countable
   dense `D` (`TopologicalSpace.exists_countable_dense`). For each
   `t ∈ (0,1]`, density gives `d t ∈ D` with `dist (u t) (d t) < 1/2`
   (`Metric.dense_iff`-search / `Dense.exists_dist_lt`). If
   `d t = d s` for `s ≠ t`, triangle inequality gives
   `dist (u t) (u s) < 1`, contradicting step 2; so `t ↦ d t` is injective
   `(0,1] → D`. Hence `(0,1]` (as a set) is countable
   (`Set.Countable` via the injection into countable `D`:
   `Set.countable_of_injOn_of_countable_image`-search, or map through
   `Set.MapsTo` + `Set.InjOn` API as in C2 step 2). But
   `¬ (Ioc (0:ℝ) 1).Countable`: from `Cardinal.mk_Ioc_real` (search;
   `a < b → #(Ioc a b) = 𝔠`) + `Cardinal.not_countable_real`-style
   (`𝔠` is uncountable: `Cardinal.aleph0_lt_continuum`); or the
   measure-theoretic shortcut — a countable set is volume-null (F2) but
   `volume (Ioc 0 1) = 1 ≠ 0`. **Use the measure shortcut; it avoids the
   cardinal API entirely.** ∎

### H3. Wave-functions exist: `Ψ = √p` — PROVABLE

Formalizes §3: "Since `p ≥ 0` there is always a normalized wave-function
`Ψ ∈ L²` with `|Ψ|² = p`."

```lean
theorem sqrt_density_memLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → ℝ) (hp : Integrable p μ) (hp0 : 0 ≤ᵐ[μ] p) :
    MemLp (fun x => Real.sqrt (p x)) 2 μ

theorem sqrt_density_norm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → ℝ) (hp : Integrable p μ) (hp0 : 0 ≤ᵐ[μ] p)
    (hp1 : ∫ x, p x ∂μ = 1) :
    ‖(sqrt_density_memLp μ p hp hp0).toLp _‖ = 1
```

**Proof.** (First) `MemLp f 2 ↔ AEStronglyMeasurable f ∧ Integrable (f²)`
— use `memLp_two_iff_integrable_sq` (search; exists in some form, possibly
`memLp_two_iff_integrable_sq` for nonneg or via
`MemLp` + `eLpNorm`; fallback: `MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2)`
holds for a.e.-measurable f — grep `sq` in
`MeasureTheory/Function/LpSpace`). Here `(√(p x))² = p x` a.e.
(`Real.sq_sqrt` on the a.e. set `{p ≥ 0}` from `hp0`; `Filter.EventuallyEq`
manipulation), so `Integrable ((√p)²)` from `hp` by `Integrable.congr`.
Measurability: `hp.aestronglyMeasurable` composed with continuous `Real.sqrt`
(`Continuous.comp_aestronglyMeasurable`). (Second) `‖·‖` in `Lp` at `p = 2`:
`Lp.norm_def`, `eLpNorm_eq_integral`-style for `p = 2` — search
`MeasureTheory.Lp.norm_toLp`, `eLpNorm'`; the computation is
`(∫ (√p)²)^(1/2) = (∫ p)^(1/2) = 1` using the same a.e. identity and `hp1`;
`Real.sqrt_one`/`one_rpow`. Budget time for `ENNReal.toReal` plumbing. ∎

### H4. The §4 coding: rational step functions are countable and dense in L² — PROVABLE

```lean
/-- Step functions on [0,1] with rational endpoints and ±√rational weights
    (the paper's integer coding), as a set in L². -/
def ratStep : Set (Lp ℝ 2 unitMeasure) := ...

theorem ratStep_countable : ratStep.Countable
theorem ratStep_dense : Dense ratStep   -- in the L² topology
```

**Definition**: the set of (equivalence classes of) functions of the form
`∑ i < m, c i • indicator (Ico (q i) (q (i+1)))` with `q : Fin (m+1) → ℚ`
increasing in `[0,1]` and `c i = ± √(r i)`, `r i : ℚ≥0`. Encode as data:
`Σ m, (Fin (m+1) → ℚ) × (Fin m → Bool × ℚ≥0)` and a map `toLp` from it;
`ratStep := Set.range toLp`.

**Proof.** Countability: the data type is countable (`ℚ`, `Bool`, products,
sigma over ℕ — all `Countable` instances fire automatically);
`Set.countable_range`. Density: two stages.
1. Simple functions are dense in L²: `MeasureTheory.Lp.simpleFunc.dense`
   (search; exists for `p ≠ ∞` — exact namespace
   `MeasureTheory.Lp.simpleFunc.denseRange` or `.isDenseEmbedding`).
   Even better for our target: **continuous functions are dense in L²**
   (`MeasureTheory.ContinuousMap.toLp_denseRange`, search; needs compact
   space or finite measure — available on `[0,1]` with `unitMeasure`; if the
   restricted-measure form is awkward, switch the whole file to the
   measure space `(Icc (0:ℝ) 1)` as a *subtype* with `volume`, where compact
   space instances are native — **decide this representation once, in Part 0,
   and stick to it**).
2. Continuous functions on `[0,1]` are uniformly approximated by rational
   step functions: given continuous `f` and `ε`, uniform continuity
   (`IsCompact.uniformContinuousOn_of_continuous`, search) gives `δ`; take a
   rational partition of mesh `< δ` (e.g. `q i = i / m` with `1/m < δ`) and
   weights: the paper requires weights of the form `±√rational` — for a real
   value `v = f(q i)` choose a rational `r` with `|√r·sign(v) - v| < ε`
   (density of `{±√r : r ∈ ℚ≥0}` in ℝ: for `v ≥ 0`, `√` is a homeomorphism
   `[0,∞) → [0,∞)` so the preimage of `(v-ε, v+ε) ∩ [0,∞)` is a nonempty
   open interval which contains a rational by `exists_rat_btwn`; mirror for
   `v < 0`). Sup-norm closeness ⇒ L²-closeness on a probability measure:
   `eLpNorm_le_of_ae_bound`-style (search) — `‖g‖_{L²} ≤ ‖g‖_∞` when
   `μ univ = 1` (`eLpNorm_le_eLpNorm_of_exponent_le`? that's the wrong
   direction between exponents — the correct tool:
   `eLpNorm_le_of_ae_bound : (∀ᵐ x, ‖g x‖ ≤ C) → eLpNorm g 2 μ ≤
   (μ univ)^(1/2) * C`-shape; grep `ae_bound` in LpSeminorm files). ∎

This also discharges the paper's §4 claim "the limit of infinitesimal
intervals is well-defined, an element of `L²([0,1])`" — the formal content is
exactly `ratStep_dense` + completeness of `Lp` (instance).

### H5. Polynomials are dense in L²([0,1]) — PROVABLE

Used by §7 (T4 statement); formalize even though T4 stays open.

```lean
theorem polynomial_dense_L2 :
    Dense {f : Lp ℝ 2 unitMeasure | ∃ P : Polynomial ℝ,
           f =ᵐ[unitMeasure] fun x => P.eval x}   -- up to the chosen repr.
```

**Proof.** Stone–Weierstrass on `[0,1]`:
`polynomialFunctions_closure_eq_top` (search; exists —
`polynomialFunctions (Set.Icc a b)` has closure `⊤` in `C([a,b])` for
`a < b`, file `Topology/ContinuousFunction/StoneWeierstrass` or
`Analysis/SpecialFunctions/...`). Combine with density of `C([0,1])` in L²
(H4 step 1) and the sup-to-L² bound (H4 step 2): given `f ∈ L²` and `ε`,
pick continuous `g` with `‖f - g‖ < ε/2`, then polynomial `P` with
`‖g - P‖_∞ < ε/2`, conclude by triangle inequality. The statement's exact
form depends on the representation decision of H4 — phrase it as
`DenseRange` of the natural map `Polynomial ℝ → Lp` if cleaner. ∎

### H6. All infinite-dimensional separable Hilbert spaces are isometrically isomorphic — PROVABLE

The honest surrogate for §4's Fock–Guichardet ≅ Guichardet ≅ `L²([0,1])`.

```lean
theorem hilbert_classification (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    (hE : ¬ FiniteDimensional ℝ E) (hF : ¬ FiniteDimensional ℝ F) :
    Nonempty (E ≃ₗᵢ[ℝ] F)
```

**Proof.** Every Hilbert space has a Hilbert basis: `exists_hilbertBasis`
(search; exists in `Analysis/InnerProductSpace/l2Space` — gives a basis
indexed by a subset `w ⊆ E` with `b.repr : E ≃ₗᵢ[ℝ] ℓ²(w, ℝ)` via
`HilbertBasis.repr`). For separable `E`, the index set is countable: an
orthonormal family is `√2`-separated (`‖e_i - e_j‖² = 2` by the Pythagorean
identity `norm_sub_sq_real` + orthogonality), and a separated family in a
separable metric space is countable — reuse **exactly** the H2 step-3
argument (factor it out as a lemma
`countable_of_separated : (∀ i j, i ≠ j → 1/2 ≤ dist (u i) (u j)) → ...`
when writing H2; with the `1/2` threshold scaled appropriately, or state it
with a general `ε > 0`). For infinite-dimensional `E`, the index is infinite
(a finite Hilbert basis would span — `HilbertBasis` total — making `E`
finite-dimensional, contradiction; search `HilbertBasis.dense_span` /
totality lemma). Countably infinite index ⇒ `Equiv` to ℕ
(`Set.Countable.exists_eq_range`-style / `Denumerable.eqv`; from
`Set.Infinite` + `Set.Countable` get `≃ ℕ` via
`Set.Countable.to_subtype` + `Encodable`/`Denumerable` plumbing — search
`Set.Countable` + `Infinite` ⇒ `Denumerable` path:
`Denumerable.ofEncodableOfInfinite`). Reindexing `ℓ²` along an `Equiv` is an
isometric iso (search `lp.equiv`-like congruence:
`LinearIsometryEquiv.piLpCongrLeft` is the `PiLp` version; for `lp` over
infinite types search `lp_congr`-shape; if absent, build from
`HilbertBasis.reindex` — a `HilbertBasis ι ℝ E` plus `ι ≃ ι'` gives
`HilbertBasis ι' ℝ E`, search `HilbertBasis.reindex`, exists). Chain:
`E ≃ₗᵢ ℓ²(ℕ, ℝ) ≃ₗᵢ F`. ∎

*(Do not build Fock spaces, Guichardet completions, or tensor products. The
paper's own remark — "the Fock-Guichardet-space is isomorphic to the
Guichardet-space" — is fully captured by this classification theorem, and
nothing downstream uses more.)*

### H7. An atomless Borel probability measure on the unit sphere — PROVABLE

Surrogate for the "uniform prior on the infinite-dimensional sphere": an
atomless measure is all that Parts 4–5 use. The literal "uniform = Gaussian
limit" mathematics is formalized separately in Part 3b (G1–G7); the two are
deliberately decoupled so the main chain never blocks on the sphere module.

```lean
theorem exists_atomless_sphere_measure (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (e₀ e₁ : E) (h : Orthonormal ℝ ![e₀, e₁]) :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧
      (∀ x, μ {x} = 0) ∧
      ∀ᵐ v ∂μ, ‖v‖ = 1
```

**Proof.** Define `φ : ℝ → E := fun t => Real.cos (π*t/2) • e₀ +
Real.sin (π*t/2) • e₁` and `μ := unitMeasure.map φ`.
- Measurable: `φ` is continuous (`Continuous.smul`, `Real.continuous_cos`…),
  hence (Borel) measurable (`Continuous.measurable`; `E` needs
  `[MeasurableSpace E] [BorelSpace E]` — add these instance hypotheses to the
  statement, or fix `E := Lp ℝ 2 unitMeasure` concretely; **recommended**:
  state for abstract `E` with `[MeasurableSpace E] [BorelSpace E]`).
- Probability: `Measure.map_apply` at `univ`; `unitMeasure` is a probability
  (Part 0); `(Measure.map φ μ) univ = μ univ` (`Measure.map_apply` with
  `measurableSet_univ`, `preimage_univ`).
- On the sphere: `‖φ t‖ = 1` for all `t`: expand
  `‖a•e₀ + b•e₁‖² = a² + b²` (orthonormality: `norm_add_sq_real`,
  `inner_smul_left/right`, `h.inner_eq_zero`-type lemmas — search the
  `Orthonormal` API: `Orthonormal.inner_left_right`; with the `![e₀,e₁]`
  matrix-literal indexing use `h.2` for `i ≠ j` and `h.1` for norms, indices
  `0 1 : Fin 2`, `Matrix.cons_val_zero/one`), then
  `Real.cos_sq_add_sin_sq`. So the event `{v | ‖v‖ = 1}` has full measure
  (`ae_map_iff`-search / `Measure.ae_map_mem_range`-style: the preimage is
  `univ`).
- Atomless on singletons: `μ {v} = unitMeasure (φ ⁻¹' {v})`
  (`Measure.map_apply`, `measurableSet_singleton`). On `t ∈ [0,1]`,
  `φ` is injective: `π*t/2 ∈ [0, π/2]`, and on that arc
  `t ↦ (cos, sin)` is injective (`Real.cos` strictly decreasing /
  `Real.sin` strictly mono on `[0, π/2]`: `Real.strictMonoOn_sin` (search),
  and `0 ≤ π*t/2 ≤ π/2` from `t ∈ [0,1]`, `Real.pi_pos`; from
  `φ t = φ t'` deduce `sin` equal by taking inner product with `e₁`
  (`inner_add_left`, orthonormality), then `t = t'` by strict monotonicity).
  Hence `φ ⁻¹' {v} ∩ Icc 0 1` is a subsingleton, so the restricted measure of
  the preimage is `≤ unitMeasure {t₀} = 0` (F1; `Measure.restrict_apply`
  unfolds `unitMeasure`; subsingleton sets: `Set.Subsingleton.measure_zero`-
  search, or `measure_mono` into a singleton). ∎

---

## Part 3b: The uniform sphere measure and the Gaussian limit (`SphereGaussian.lean`) — DONE (G0–G7 all implemented)

**Purpose.** The paper (§§2–3) invokes "the uniform prior measure on the
infinite-dimensional sphere". The main chain (T1–T3) deliberately uses the
atomless surrogate H7. This part formalizes the *literal* mathematical
content behind the paper's phrase, following the chapter draft and the
lopez99 reference: in the limit of infinitely many dimensions, the uniform
measure on the hypersphere becomes the Gaussian measure, and the Gegenbauer
polynomials (hyperspherical harmonics' radial part) become the Hermite
polynomials. All of this is honest Tier-A mathematics with complete proofs
below. **Nothing in Parts 4–5 depends on this module**; build it
independently (it can even be done in parallel by a second agent).

**Source note**: `lopez99.md` (repo root) is the full paper J. L. López &
N. M. Temme, *Approximations of orthogonal polynomials in terms of Hermite
polynomials*, Methods Appl. Anal. 6(2) (1999) 131–146. What this plan takes
from it:
- **eq. (1.1)**: the explicit physicists' Hermite sum
  `H_n(x) = n!·Σ_{k≤n/2} (−1)^k/(k!(n−2k)!)·(2x)^{n−2k}` — fixes the
  convention of G0 (`physHermite` agrees: `H_0 = 1`, `H_1 = 2x`).
- **eq. (1.4)**: `lim_{γ→∞} γ^{−n/2} C_n^γ(x/√γ) = H_n(x)/n!` — exactly the
  statement proved in G2 (with `λ := γ = α/2`).
- **eq. (3.2)**: explicit low-order Gegenbauer values
  `C_0^γ = 1`, `C_1^γ = 2γx`, `C_2^γ = 2γ(γ+1)x² − γ` — used as
  sanity-check lemmas for G1's recurrence definition.
**Route warning (important):** the paper proves (1.4) via the finite exact
Hermite-type representation (its eq. (3.3), a Cauchy-integral construction)
plus coefficient asymptotics `c_k = O(γ^⌊k/3⌋)` (its (3.7)–(3.8), §3.1–3.2).
**G2 must NOT follow that route** — it needs contour integrals, generating
functions, and O-calculus, each a formalization project of its own. The
recurrence-induction proof below reaches the same limit (1.4) directly and
is the mandated path. Everything else in the paper — Laguerre (§4), Jacobi
(§6), Tricomi–Carlitz (§5), all zero-location asymptotics (eq. (1.3),
§§3.3/4.1/5.2, (6.14)) — is not used by the chapter and is **not a work
item**. Treat `lopez99.md` as citation/cross-check material only.

### G0. Hermite conventions — DECIDE FIRST

Mathlib's `Polynomial.hermite` (search; exists) is the **probabilists'**
family `He_n` (recurrence `He_{n+1}(x) = x·He_n(x) − n·He_{n−1}(x)`). The
chapter uses **physicists'** `H_n` (weight `e^{−x²}`, recurrence
`H_n(x) = 2x·H_{n−1}(x) − 2(n−1)·H_{n−2}(x)`). Search for
`Polynomial.physHermite` (a physicists' version may exist in recent Mathlib).
If absent, define it in this file by the recurrence above and record the
conversion `H_n(x) = 2^(n/2)·He_n(√2·x)` only if actually needed (the proofs
below use only the recurrence, so the conversion lemma is optional).

```lean
/-- Physicists' Hermite polynomials as real functions, by recurrence.
    Agrees with lopez99 eq. (1.1). -/
def physHermite : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | (n+2), x => 2*x * physHermite (n+1) x - 2*(n+1) * physHermite n x
```

*Optional cross-check lemma (cheap, nice-to-have, nothing depends on it):*
`physHermite n x = n! * ∑ k ∈ Finset.range (n/2 + 1),
(−1)^k / (k! * (n−2k)!) * (2x)^(n−2k)` — lopez99's (1.1); provable by
two-step induction matching the recurrence against the sum (index
bookkeeping only). Skip if the `Finset` reindexing fights back.

### G1. Gegenbauer polynomials — DEFINITIONS (Mathlib has none)

```lean
/-- Gegenbauer (ultraspherical) polynomials C_n^λ, by the standard
    three-term recurrence, as real functions of (λ, x). -/
def gegenbauer : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, lam, x => 2 * lam * x
  | (n+2), lam, x =>
      (2*x*(n+1+lam) * gegenbauer (n+1) lam x
        - (n+2*lam) * gegenbauer n lam x) / (n+2)
```

(Check the recurrence against the standard normalization
`n·C_n^λ = 2x(n+λ−1)·C_{n−1}^λ − (n+2λ−2)·C_{n−2}^λ`: with `n := m+2` the
coefficients are `2x(m+1+λ)` and `(m+2λ)`, divided by `m+2` — as written.)
Record the trivia lemmas `gegenbauer_zero`, `gegenbauer_one`, and the
recurrence as a `theorem` in the `n·C_n = ...` form (clears the division;
`field_simp` with `(n:ℝ)+2 ≠ 0`). Add the sanity check against lopez99
eq. (3.2):
```lean
theorem gegenbauer_two (lam x : ℝ) :
    gegenbauer 2 lam x = 2*lam*(lam+1)*x^2 - lam
```
(unfold the recurrence at `n = 0`: `(2x(1+λ)·2λx − 2λ·1)/2`; `ring`-closes.
If this lemma fails, the recurrence coefficients were transcribed wrong —
fix G1 before proceeding to G2.)

**Convention note**: lopez99 (eq. (1.2)) *defines* `C_n^γ` by the generating
function `(1 − 2xw + w²)^{−γ} = Σ C_n^γ(x)·wⁿ`. The recurrence above is the
standard equivalent and is the **definition** for this project; do not
formalize the generating-function characterization (it needs analytic
power-series-coefficient extraction — a separate project, and nothing here
uses it).

### G2. The lopez99 limit: rescaled Gegenbauer → Hermite — PROVABLE

The chapter's formula
`lim_{α→∞} (α/2)^{−n/2} C_n^{α/2}(√(2/α)·x) = H_n(x)/n!` — this is
lopez99 **eq. (1.4)** with `γ = α/2`.
Work with `λ := α/2 → ∞` (real, along `atTop`); then
`√(2/α)·x = x/√λ` and `(α/2)^{−n/2} = λ^{−n/2}`.

```lean
/-- The rescaled Gegenbauer function of the chapter. -/
def gegenbauerScaled (n : ℕ) (lam x : ℝ) : ℝ :=
  lam ^ (-(n:ℝ)/2) * gegenbauer n lam (x / Real.sqrt lam)

theorem gegenbauerScaled_tendsto_hermite (n : ℕ) (x : ℝ) :
    Filter.Tendsto (fun lam => gegenbauerScaled n lam x)
      Filter.atTop (𝓝 (physHermite n x / n.factorial))
```

**Proof.** By strong induction on `n` (two-step: prove the statement for
`n` and `n+1` simultaneously, or use `Nat.strong_induction_on` reading off
the two predecessors).
1. **Base `n = 0`**: `gegenbauerScaled 0 lam x = lam^0 * 1 = 1` for
   `lam > 0` (`Real.rpow_zero` — careful: the exponent is `-(0:ℝ)/2 = 0`,
   `neg_zero`, `zero_div`); target `physHermite 0 x / 0! = 1/1 = 1`.
   `Tendsto` of an eventually-constant function:
   `Filter.Tendsto.congr'` with `eventually_atTop` (`lam ≥ 1`).
2. **Base `n = 1`**: for `lam > 0`,
   `gegenbauerScaled 1 lam x = lam^(−1/2) · 2·lam · (x/√lam) = 2x`
   (`Real.rpow_natCast`/`Real.rpow_neg`, `Real.sqrt_eq_rpow`,
   `Real.rpow_add` for `lam > 0`; the exponents combine to
   `−1/2 + 1 − 1/2 = 0`). Target `physHermite 1 x / 1! = 2x`. Constant again.
3. **Step (`n+2` from `n+1`, `n`)**: the recurrence identity, valid for
   every `lam > 0` (pure algebra from G1's recurrence — multiply out the
   rpow's exactly as in step 2; this is the only rpow-bookkeeping-heavy
   part, isolate it as its own lemma):
   ```
   (n+2) * gegenbauerScaled (n+2) lam x
     = 2*x * (1 + (n+1)/lam) * gegenbauerScaled (n+1) lam x
       - (2 + n/lam) * gegenbauerScaled n lam x
   ```
   Derivation check (keep it in the docstring): in
   `n·C_n^λ(y) = 2y(n+λ−1)C_{n−1}^λ(y) − (n+2λ−2)C_{n−2}^λ(y)` substitute
   `y = x/√λ` and multiply by `λ^{−n/2}`; the first term contributes
   `2x·λ^{−1}·(n+λ−1) = 2x(1+(n−1)/λ)` against `gegenbauerScaled (n−1)`
   (one `λ^{−1/2}` from the rescaling mismatch, one from `y`), the second
   `λ^{−1}(n+2λ−2) = 2 + (n−2)/λ` against `gegenbauerScaled (n−2)`; with
   the shift `n ↦ n+2` this is the displayed identity.
   Now take limits (`Filter.Tendsto.mul`, `.add`, `.sub`, `.const_mul`):
   `(n+1)/lam → 0` and `n/lam → 0` (`tendsto_const_div_atTop_nhds_zero`-
   style, search), the two inductive hypotheses give the limits of the
   lower-order factors, so `(n+2) * gegenbauerScaled (n+2) lam x` tends to
   `2x · physHermite (n+1) x / (n+1)! − 2 · physHermite n x / n!`.
4. **Target value check** (pure algebra, `field_simp` + the `physHermite`
   recurrence): dividing by `n+2`, the claimed limit is
   `physHermite (n+2) x / (n+2)!`, because
   `physHermite (n+2) x = 2x·physHermite (n+1) x − 2(n+1)·physHermite n x`
   and `(n+2)! = (n+2)(n+1)·n!`:
   `[2x·H_{n+1}/(n+1)! − 2·H_n/n!] / (n+2) = [2x·H_{n+1} − 2(n+1)H_n]/(n+2)!`.
   Conclude with `Tendsto.div_const` and `Filter.Tendsto.congr` to match the
   exact function shape. ∎

**No Gamma functions, no Stirling, no asymptotics** — this is why the
recurrence route is mandatory. Do not attempt the explicit-formula route.

### G3. The weight limit — PROVABLE

The chapter's `lim_{α→∞} √(1 − 2x²/α)^{α−1} = e^{−x²}`; in `λ = α/2` form:

```lean
theorem weight_tendsto_gaussian (x : ℝ) :
    Filter.Tendsto (fun lam : ℝ => (1 - x^2/lam) ^ (lam - 1/2))
      Filter.atTop (𝓝 (Real.exp (-x^2)))
```

(`^` = `Real.rpow`; for `lam > x²` the base is positive, so eventual
well-definedness is fine — manage with `Filter.Eventually` as in G2 step 1.)

**Proof.** Split the exponent: `(1 − x²/lam)^(lam − 1/2)
= (1 − x²/lam)^lam · (1 − x²/lam)^(−1/2)` (`Real.rpow_add` on the positive
base, eventually). First factor → `exp (−x²)`: Mathlib has the
`(1 + t/x)^x → exp t` family (search `tendsto_one_plus_div_rpow_exp`;
instantiate `t := −x²`). Second factor → `1`: base → 1
(`tendsto_const_div_atTop_nhds_zero` + `Tendsto.const_sub`), `rpow`
continuous at `(1, −1/2)` (`Real.continuousAt_rpow` with base `≠ 0`),
`Real.one_rpow`. Multiply. ∎

### G4. The normalization-constant limit — PROVABLE (the chapter's displayed equation)

```lean
theorem normalization_tendsto (n : ℕ) :
    Filter.Tendsto
      (fun lam => ∫ x in (-Real.sqrt lam)..(Real.sqrt lam),
          (gegenbauerScaled n lam x)^2 * (1 - x^2/lam) ^ (lam - 1/2))
      Filter.atTop
      (𝓝 (∫ x : ℝ, (physHermite n x / n.factorial)^2 * Real.exp (-x^2)))

theorem hermite_normalization (n : ℕ) :
    ∫ x : ℝ, (physHermite n x / n.factorial)^2 * Real.exp (-x^2)
      = Real.sqrt π * 2^n / n.factorial
```

The first theorem **is** the chapter's
`lim (α/2)^{1/2−n} ∫ [C_n^{α/2}]² √(1−x²)^{α−1} dx = ∫ [H_n/n!]² e^{−x²} dx`:
the substitution `x_old = x/√λ` (change of variables —
`intervalIntegral.integral_comp_smul_deriv` or
`intervalIntegral.integral_comp_mul_left`, search) turns the chapter's left
side *exactly* into the integral displayed above. Record that substitution
as a separate equality lemma `normalization_substitution` first (pure change
of variables; the `(α/2)^{1/2−n}` prefactor is absorbed by the two
`λ^{−n/2}` rescalings and the Jacobian `λ^{−1/2}`; rpow bookkeeping as in
G2 step 2).

**Proof of the limit** (dominated convergence; use
`MeasureTheory.tendsto_integral_of_dominated_convergence` along an arbitrary
sequence `lam_k → ∞` and conclude for the filter via
`tendsto_of_seq_tendsto`-search, unless the snapshot has a filter-version of
DCT — grep `dominated_convergence`):
1. Rewrite the interval integral over `[−√λ, √λ]` as `∫ over ℝ` of the
   integrand times the set indicator (`intervalIntegral` ↔ set-integral
   conversion + `MeasureTheory.integral_indicator`, search).
2. **Pointwise convergence** at every fixed `x`: the indicator is eventually
   `1` (`√λ > |x|` eventually); G2 gives the polynomial factor; G3 the
   weight; products of limits.
3. **Domination.** Two ingredients, each its own lemma:
   - *Weight bound*: `(1−u) ≤ e^{−u}` for `0 ≤ u ≤ 1`
     (`Real.add_one_le_exp` rearranged; search `one_sub_le_exp_neg`), hence
     for `|x| ≤ √λ`, `λ ≥ 1`:
     `(1 − x²/λ)^(λ−1/2) ≤ exp(−x²·(λ−1/2)/λ) ≤ exp(−x²/2)`
     (rpow monotonicity + `(λ−1/2)/λ ≥ 1/2` for `λ ≥ 1`).
   - *Polynomial bound, uniform in λ*: there is `B n` with
     `|gegenbauerScaled n lam x| ≤ B n * (1+|x|)^n` for all `lam ≥ 1`, all
     `x`. **Proof by the same two-step induction as G2** using the rescaled
     recurrence of G2 step 3: the coefficients `2(1+(n+1)/λ)` and `(2+n/λ)`
     are bounded by `2(n+2)` for `λ ≥ 1`, so
     `B (n+2) := 2(n+2)·(B (n+1) + B n)` works after
     `(1+|x|)^(n+1)·|x| ≤ (1+|x|)^(n+2)` (`pow_le_pow_left`, `abs`-trivia).
     Bases: `B 0 = 1`, `B 1 = 2`.
   - Dominating function: `g x := (B n)²·(1+|x|)^(2n)·exp(−x²/2)`,
     integrable: polynomial × sub-Gaussian — search
     `integrable_pow_mul_exp_neg_mul_sq` (Mathlib has this family near
     `integral_gaussian`).
4. DCT applies; done. ∎

**Proof of `hermite_normalization`** (the chapter's value `√π·2^n/n!`).
Check first whether the snapshot already has Hermite–Gaussian orthogonality
(search `hermite` near `integral_gaussian`). If absent, prove the diagonal
case by induction via integration by parts:
1. Base: `∫ e^{−x²} = √π` — `integral_gaussian` (search; exists:
   `∫ exp (−b·x²) = √(π/b)`, instantiate `b = 1`).
2. Step: two standard identities (prove both by induction from G0's
   recurrence): `(physHermite (n+1))' = 2(n+1)·physHermite n`, and
   `physHermite (n+1) x · e^{−x²} = −(d/dx)(physHermite n x · e^{−x²})`
   (expand the derivative; equivalent to the recurrence). Then
   `∫ H_{n+1}²e^{−x²} = ∫ H_{n+1}·(−(H_n e^{−x²})')
   = ∫ H_{n+1}'·H_n·e^{−x²} = 2(n+1)·∫ H_n²·e^{−x²}`
   — integration by parts on ℝ with vanishing boundary terms
   (polynomial·`e^{−x²}` → 0 at ±∞; search the by-parts API:
   `MeasureTheory.integral_mul_deriv_eq_deriv_mul`-family with
   `Tendsto ... (cocompact ℝ) (𝓝 0)` side conditions, and decay lemmas
   `tendsto_pow_mul_exp_neg_atTop`-shape). Hence
   `∫ H_n² e^{−x²} = 2^n·n!·√π`; divide by `(n!)²`. ∎
   *(Longest item of Part 3b; standard and self-contained. If the
   by-parts API fights back, state `hermite_normalization` with a `sorry`
   labeled `-- OPEN-API (standard Hermite orthogonality; blocked on
   by-parts API)` and report — it is a leaf, nothing depends on it.)*

### G5. The uniform measure on the k-sphere via Gaussians — PROVABLE

```lean
/-- Standard Gaussian on EuclideanSpace ℝ (Fin k). -/
def gaussianE (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1).map
    (EuclideanSpace.measurableEquiv (Fin k)).symm   -- (search exact equiv name)

/-- Radial projection onto the sphere of radius √k (junk value at 0). -/
def sphereProj (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  if x = 0 then x else (Real.sqrt k / ‖x‖) • x

/-- THE uniform measure on the √k-sphere. -/
def sphereUniform (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (gaussianE k).map (sphereProj k)

theorem sphereUniform_isProbability (k) :
    IsProbabilityMeasure (sphereUniform k)
theorem sphereUniform_sphere (k) (hk : 0 < k) :
    sphereUniform k {x | ‖x‖ = Real.sqrt k} = 1
theorem sphereUniform_rotation_invariant (k)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (sphereUniform k).map L = sphereUniform k
```

**Proofs.**
- Probability: `Measure.map_apply` at `univ`; `gaussianReal` is a
  probability (instance exists in `Mathlib/Probability/Distributions/
  Gaussian*`, search), `Measure.pi` of probabilities is a probability
  (instance).
- Concentration on the sphere: `gaussianE k {0} = 0` — for `k ≥ 1`, bound by
  the cylinder where coordinate 0 vanishes (`measure_mono`), whose measure
  is `gaussianReal {0} = 0` (the Gaussian is `withDensity` of `volume`, so
  F1 applies — search `gaussianReal_apply`-shape lemmas). Off `0`,
  `‖sphereProj k x‖ = √k` (`norm_smul`, `div_mul_cancel₀`,
  `Real.sqrt_nonneg`), so the preimage of the sphere is conull.
- Rotation invariance, two steps:
  (a) **Gaussian invariance** `(gaussianE k).map L = gaussianE k`:
  write `gaussianE k = volume.withDensity (fun x => c k * Real.exp (−‖x‖²/2))`
  — from `gaussianReal`'s density definition, `Measure.pi` of `withDensity`
  = `withDensity` of the product density (search `Measure.pi_withDensity`;
  if missing, prove on boxes + `Measure.pi_eq` ext), the measurable-equiv
  transport, and `volume` on `EuclideanSpace` = transported pi-volume
  (`EuclideanSpace.volume_preserving_measurableEquiv`, search; exists).
  Then `Measure.map L (μ.withDensity f) = (μ.map L).withDensity (f ∘ L.symm)`
  (search `withDensity_map_equiv`-shape; provable by ext +
  `Measure.map_apply` + `withDensity_apply`), `volume.map L = volume`
  (isometries preserve Haar/volume in finite dimension — search
  `MeasurePreserving` + `LinearIsometryEquiv`; fallback chain:
  `Measure.map_linearMap_addHaar_eq_smul_addHaar` with `|det L| = 1`).
  `‖L.symm x‖ = ‖x‖` kills the density change. **If this API hunt stalls,
  postpone (a)**: nothing in G6–G7 uses it; it is only the "this really is
  THE uniform measure" certificate.
  (b) **Projection equivariance**: `sphereProj k ∘ L = L ∘ sphereProj k`
  (for `x ≠ 0`: `‖L x‖ = ‖x‖`, `L (c • x) = c • L x`; at `0`: `map_zero`,
  `if` split; `L x = 0 ↔ x = 0` by injectivity). Then
  `(sphereUniform k).map L = (gaussianE k).map (L ∘ sphereProj k)
  = (gaussianE k).map (sphereProj k ∘ L) = ((gaussianE k).map L).map (sphereProj k)`
  (`Measure.map_map`; `Measurable (sphereProj k)`: `Measurable.ite` (search)
  on the closed set `{0}` with the smul/norm formula measurable on the
  complement — built from `measurable_norm`, `.inv`, `.smul`), then (a). ∎

### G6. Poincaré–Borel: sphere marginals → Gaussian — PROVABLE (relative to the infinite product measure)

The rigorous form of "the uniform measure on the infinite-dimensional sphere
*is* the Gaussian measure". Realize everything on one probability space: let
`γ : Measure (ℕ → ℝ)` be the infinite product of standard Gaussians.
**API check first**: search `MeasureTheory.Measure.infinitePi` /
`Measure.productMeasure` / Ionescu–Tulcea (`Measure.traj`) — countable
products of probability measures landed in Mathlib (2024–25); if genuinely
absent in this snapshot, **stop this item and report** (do not hand-roll a
Kolmogorov extension); G1–G5 and the G7′ fallback remain fully buildable.

```lean
/-- Empirical squared norm of the first k coordinates. -/
def normSq (k : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range k, (ω i)^2

/-- a.s. Poincaré–Borel: the √k-sphere normalization of the first k Gaussian
    coordinates converges coordinatewise to the coordinates themselves. -/
theorem poincare_borel_ae :
    ∀ᵐ ω ∂γ, ∀ i : ℕ,
      Filter.Tendsto
        (fun k => (Real.sqrt k / Real.sqrt (normSq k ω)) * ω i)
        Filter.atTop (𝓝 (ω i))
```

**Proof.**
1. **SLLN.** The coordinates are iid standard Gaussian under `γ`
   (independence and the coordinate laws are part of the product-measure
   API: search the projection lemmas and `iIndepFun` for the chosen product
   construction). The squares `(ω i)²` are iid, integrable, mean 1:
   `∫ x² ∂(gaussianReal 0 1) = 1` — search
   `ProbabilityTheory.variance_gaussianReal` (variance 1, mean 0 ⇒ second
   moment 1); integrability from the explicit density +
   `integrable_pow_mul_exp_neg_mul_sq` as in G4. Apply the strong law
   `ProbabilityTheory.strong_law_ae` (search; exists — Etemadi, iid
   integrable): a.s. `normSq k ω / k → 1`.
2. **Algebra of limits.** On that event: eventually `normSq k ω / k > 1/2`,
   so `√k/√(normSq k ω) = 1/√(normSq k ω / k)` (positive-case `Real.sqrt`
   rewriting, `Real.sqrt_div'`-search) → `1` by continuity of `t ↦ 1/√t`
   at `1` (`Real.continuousAt_sqrt`, `ContinuousAt.inv₀`, `Real.sqrt_one`).
   `Filter.Tendsto.mul_const (ω i)`. The `∀ i` commutes with `∀ᵐ` for
   countable `i`: `MeasureTheory.ae_all_iff`. ∎

Corollary (weak-convergence form; the textbook statement — include it):

```lean
theorem poincare_borel (n : ℕ) (f : (Fin n → ℝ) →ᵇ ℝ) :
    Filter.Tendsto
      (fun k => ∫ ω, f (fun i => Real.sqrt k / Real.sqrt (normSq k ω) * ω i) ∂γ)
      Filter.atTop
      (𝓝 (∫ y, f y ∂(Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
```

**Proof.** The right side equals `∫ ω, f (fun i => ω i) ∂γ` (the first-n-
coordinates marginal of `γ` is the finite product — projection lemma of the
product construction). The integrands converge a.e. (the a.s. theorem +
continuity of `f`) and are uniformly bounded by `‖f‖`
(`BoundedContinuousFunction` bound); dominated convergence
(`tendsto_integral_of_dominated_convergence`; index already `ℕ`). ∎
Record also (cheap, if the marginal API cooperates) the identification of
the law of `fun i : Fin n => √k/√(normSq k ω)·ω i` with the `n`-marginal of
G5's `sphereUniform k` for `k ≥ n` — this is what makes the corollary a
statement *about the sphere measures*; if the marginal API is thin, keep the
corollary as stated (it already carries the full content on `γ`).

### G7. The Gaussian measure "lives on the infinite-dimensional sphere" — PROVABLE

The concentration statement justifying the chapter's identification (radius
`√k` ↔ unit-normalized L² norm):

```lean
theorem gaussian_concentration_sphere :
    ∀ᵐ ω ∂γ, Filter.Tendsto (fun k => normSq k ω / k) Filter.atTop (𝓝 1)
```

**Proof.** Exactly step 1 of G6 (SLLN); factor it out as this named theorem
and have G6 cite it. ∎

**G7′ (fallback if the infinite product measure is unavailable):** the
finite-k, in-probability version needs no infinite product:
`∀ ε > 0, Tendsto (fun k => (gaussianE k) {x | |‖x‖²/k − 1| > ε}) atTop (𝓝 0)`
— Chebyshev (`ProbabilityTheory.meas_ge_le_variance_div_sq`-search or the
`mul_meas_ge_le_integral` family): `‖x‖²/k` has mean 1 and variance `2/k → 0`
under `gaussianE k` (fourth Gaussian moment `∫x⁴ = 3` from the density +
`integrable_pow_mul_exp_neg_mul_sq`; variance additivity over independent
coordinates: `Measure.pi` independence + `ProbabilityTheory.variance_sum`-
shape, search). Moderate; only do this if G6 is blocked. ∎

### What Part 3b buys, and its fences

- It formalizes the chapter's display equations: the Gegenbauer→Hermite
  limit (G2), the weight limit (G3), the normalization limit with the value
  `√π·2^n/n!` (G4), and the "uniform on S^∞ = Gaussian" identification
  (G5–G7).
- **Interpretive sentences stay out**: "the uniform measure is the prior and
  it means we have no information" is Tier-C narrative — docstring only.
  The full hyperspherical-harmonics apparatus, Gegenbauer *orthogonality at
  finite α* (not needed: G4 only needs the *limit* of the integrals, which
  DCT gives directly), and the Fock-space reading of the Hermite basis are
  out of scope.
- The area-element formula `dσ(k) = ∏_j √(1−x_j²)^(j−1) dx_j` (chapter's
  last display) is **not** formalized: Mathlib's spherical-coordinate
  support is 2-D (`polarCoord`); a k-dimensional hyperspherical change of
  variables is a large independent project, and G5's Gaussian construction
  *replaces* it as the definition of the uniform measure, with
  `sphereUniform_rotation_invariant` as the certificate that it deserves
  the name. If the coordinate formula is later required, that is a new work
  item to negotiate, not part of this plan.
- **Optional upgrade to the main chain (only if requested):** H7's `prior`
  could be re-based on a `sphereUniform`-style construction so T2 reads
  "for the uniform-compatible prior". The current M4 prior already satisfies
  the paper's stated requirement ("a prior measure *compatible with* the
  uniform prior measure" — supported on the sphere, atomless); do not couple
  the modules without instruction.

---

## Part 4: The model (`Model.lean`) — Tier B definitions and lemmas — DONE (incl. the N1 circuit upgrade)

This part fixes the paper's computational problem as concrete mathematics.
All *choices* here (dyadic partitions, the one-parameter prior, the cost
model) are design decisions documented as docstrings; theorems about them are
in Part 5.

### M1. Dyadic discretization — DEFINITIONS + trivia

```lean
/-- The i-th dyadic interval at resolution k. -/
def dyadic (k : ℕ) (i : Fin (2^k)) : Set ℝ := Ico (i / 2^k : ℝ) ((i+1) / 2^k)

/-- The dyadic index of x ∈ [0,1) at resolution k. -/
def dyadicIndex (k : ℕ) (x : ℝ) : Fin (2^k) := ...  -- ⌊2^k x⌋, clamped

theorem dyadic_disjoint : Pairwise (Disjoint on dyadic k)        -- i ≠ j
theorem dyadic_cover : ⋃ i, dyadic k i = Ico (0:ℝ) 1
theorem mem_dyadic_index (hx : x ∈ Ico (0:ℝ) 1) : x ∈ dyadic k (dyadicIndex k x)
theorem dyadic_width (hx hy : · ∈ dyadic k i) : |x - y| < (2^k)⁻¹
```

**Proofs.** Interval arithmetic: `Set.Ico_disjoint_Ico`-search /
`Set.disjoint_left` + `linarith`; the cover via
`Set.ext` + `⌊2^k x⌋` extraction (`Int.floor` API as in C2 — **reuse the C2
floor lemmas; write them once in `Foundations.lean`**); width: both points in
an interval of length `(2^k)⁻¹`. The `binDigit` of C2 should be redefined as
the parity path of `dyadicIndex` or vice versa — keep ONE floor-based toolkit.

### M2. CDFs and the inverse-transform verifier — DEFINITIONS

```lean
/-- The verification predicate of §3: at resolution k, the candidate output
    interval i is accepted for sample u iff the conditional CDF crosses u
    inside that interval. -/
def verify (G : ℝ → ℝ) (u : ℝ) (k : ℕ) (i : Fin (2^k)) : Prop :=
  G (i / 2^k) ≤ u ∧ u ≤ G ((i+1) / 2^k)

instance : DecidablePred ... -- decidable once G-values and u are given as
                             -- rationals; see M5
```

Glue lemma (PROVABLE, short): if `G` is monotone with `G 0 ≤ u ≤ G 1`, then
`∃ i, verify G u k i` — **Proof**: the finite sequence
`j ↦ G (j / 2^k)`, `j : Fin (2^k + 1)`, starts `≤ u` and ends `≥ u`; take the
largest `j` with `G (j/2^k) ≤ u` (max of a nonempty finite set:
`Finset.exists_max_image`-search on the filtered set, nonempty since `j = 0`
qualifies); maximality gives `u < G ((j+1)/2^k)` if `j+1` in range — at the
right edge `j = 2^k` use `u ≤ G 1` directly. Case split, `omega` + `Fin`
plumbing. ∎

And uniqueness-up-to-adjacency for strictly monotone `G` (PROVABLE, used for
the "deterministic function" narrative of §3): if `G` strictly monotone and
`verify` holds at `i` and `j`, then `|i - j| ≤ 1` — from the inequalities and
strict monotonicity (`StrictMono.lt_iff_lt`), `omega`-style on indices.

### M3. Machine computation of a selection function — DEFINITIONS + uniqueness

```lean
/-- Code c computes selection f : ℝ → ℝ on [0,1) if at every resolution k it
    maps (k, dyadic index of x) to the dyadic index of f x. -/
def ComputesSelection (c : Nat.Partrec.Code) (f : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ x ∈ Ico (0:ℝ) 1, f x ∈ Ico (0:ℝ) 1 ∧
    c.eval (Nat.pair k (dyadicIndex k x)) =
      Part.some (dyadicIndex k (f x))

theorem computesSelection_unique (c : Nat.Partrec.Code) (f g : ℝ → ℝ)
    (hf : ComputesSelection c f) (hg : ComputesSelection c g) :
    EqOn f g (Ico (0:ℝ) 1)
```

**Proof.** Fix `x ∈ [0,1)`. For every `k`, the code's output at
`(k, dyadicIndex k x)` is a single value (Part.some is injective:
`Part.some_inj`), so `dyadicIndex k (f x) = dyadicIndex k (g x)`; by
`mem_dyadic_index` both `f x` and `g x` lie in the same dyadic interval, so
`|f x - g x| < (2^k)⁻¹` (M1 `dyadic_width`). True for all `k` ⇒
`f x = g x`: `eq_of_abs_sub_nonpos` after
`le_of_forall_lt'`-style — cleanest: `abs_sub_eq_zero`... do it as: the
constant `|f x - g x|` is `≤ (2^k)⁻¹ → 0`, so
`≤ 0` by `ge_of_tendsto'` (`tendsto_inv_atTop_zero` composed with
`tendsto_pow_atTop_atTop_of_one_lt` (search names) — or avoid limits:
by contradiction, `0 < |f x - g x|` gives `k` with `(2^k)⁻¹ < |f x - g x|`
(`exists_pow_lt_of_lt_one` / `Nat.exists_pow_gt`-search: `∃ k, 2^k > 1/d`
from `Nat.exists_pow_gt` or `pow_unbounded_of_one_lt`), contradiction.
**Use the contradiction route; it needs only `pow_unbounded_of_one_lt`
(search; exists, possibly as `exists_pow_gt` / `Nat.one_lt_two.pow_unbounded`).** ∎

```lean
theorem countable_computable_selections :
    {f : ℝ → ℝ | ∃ c, ComputesSelection c f}.Countable  -- as graphs on [0,1)
```
**Careful**: as stated over *all* of `ℝ → ℝ` this is false (values off
`[0,1)` are unconstrained). Two repair options; **pick (a)**:
(a) state countability for the set of *restrictions*
`{f₀ : ↥(Ico (0:ℝ) 1) → ℝ | ∃ c f, ComputesSelection c f ∧ f₀ = restrict f}`;
(b) add `∀ x ∉ Ico 0 1, f x = 0` into `ComputesSelection`.
**Proof (a).** Map each restriction to a code computing it (choice); by
`computesSelection_unique` each code yields at most one restriction, so the
assignment restriction ↦ code is injective into the countable
`Nat.Partrec.Code` (C1's instance). `Set.countable_iff_exists_injOn`-route as
in C2/H2 (the factored-out countability lemma). ∎

### M4. The prior: a concrete atomless measure on selection functions — DEFINITIONS + key lemma

Design (documented choice): the one-parameter family of §3's joint
distributions, rigged so that distinct parameters give distinct selection
functions. For `t ∈ [0,1]`, conditional CDF `G t : ℝ → ℝ := fun y =>
y^(1+t)` on `[0,1]` (density `(1+t)·y^t`, the wave-function is
`Ψ_t(y) = √((1+t)·y^t)` — tie to H3 in a docstring). The induced selection
function under inverse-transform sampling with sample `u`:

```lean
/-- The selected output for parameter t and uniform sample u. -/
def select (t : ℝ) (u : ℝ) : ℝ := u ^ (1 / (1+t))   -- G t (select t u) = u

/-- The selection functions as continuous maps on the sample square. -/
def selMap (t : ↥(Icc (0:ℝ) 1)) : C(↥(Icc (0:ℝ) 1), ℝ) := ⟨fun u => select t u, by ...⟩

/-- The prior: pushforward of Lebesgue on [0,1] under t ↦ selMap t. -/
def prior : Measure C(↥(Icc (0:ℝ) 1), ℝ) := (volume : Measure ↥(Icc (0:ℝ) 1)).map selMap
```

(Subtype `↥(Icc 0 1)` carries `volume` and `CompactSpace`; `C(K, ℝ)` for
compact `K` is a Polish normed space — instances should fire:
`ContinuousMap.metricSpace`, `SecondCountableTopology` from separability of
`C(K,ℝ)` (search; exists for compact metric `K`:
`ContinuousMap.separableSpace`-like). `BorelSpace` via `borel` instance —
search how `C(α,β)` gets its `MeasurableSpace`; if no instance exists, use
`MeasurableSpace := borel _` locally.)

Key lemmas:

```lean
theorem selMap_continuous : Continuous selMap          -- hence measurable
theorem selMap_injective : Function.Injective selMap
theorem prior_isProbability : IsProbabilityMeasure prior
theorem prior_atomless : ∀ g, prior {g} = 0
```

**Proofs.**
- `select` continuity in `(t,u)` jointly: `u ^ (1/(1+t))` =
  `Real.rpow`; continuity of `rpow` on `u ∈ [0,1]`, exponent in `[1/2, 1]`:
  `Real.continuousAt_rpow` away from `(0,0)`-type degeneracies — here base
  `u ≥ 0` and exponent `≥ 1/2 > 0`; use
  `Real.continuous_rpow`-variants (search `Real.continuousOn_rpow`,
  `Real.continuousAt_rpow_const`…; the two-variable version
  `Real.continuousAt_rpow` has hypotheses `x ≠ 0 ∨ 0 < y` — satisfied:
  exponent `1/(1+t) > 0`). For `selMap` continuity into `C(K,ℝ)` (sup
  metric): continuity of a map into `C(K,ℝ)` from joint continuity +
  compactness — `ContinuousMap.continuous_of_continuous_uncurry` (search;
  exists as the curry/uncurry API in `Topology/ContinuousFunction/Basic` or
  `Compacts`: `ContinuousMap.curry` and its continuity).
- Injectivity: evaluate at `u = 1/2`: `t ↦ (1/2)^(1/(1+t))` is strictly
  monotone in `t` (exponent `1/(1+t)` strictly decreasing; base in `(0,1)` so
  `rpow` is strictly *decreasing* in the exponent... compose signs:
  `Real.rpow_lt_rpow_of_exponent_gt` (search; for `0 < b < 1`, exponent
  comparison flips) — net: distinct `t` give distinct values at `1/2`).
  From `selMap t = selMap t'`, evaluate (`ContinuousMap.ext_iff` direction)
  at `1/2` and apply strict monotonicity's injectivity.
- Probability: `Measure.map_apply` + `volume univ = 1` on the subtype
  (search how `volume` on `↥(Icc 0 1)` is defined —
  `MeasureTheory.Measure.Subtype.measureSpace` (search); its `univ`-measure is
  `volume (Icc 0 1) = 1`; if the subtype-volume API is thin, define
  `prior` instead as `(unitMeasure.comap Subtype.val).map selMap` or push
  directly from `unitMeasure` on ℝ with `selMap` precomposed with a clamp —
  **fallback that always works**: parameterize by `t : ℝ`, define
  `selMap : ℝ → C(K,ℝ)` using `min 1 (max 0 t)` inside, push `unitMeasure`
  forward; injectivity then holds on `[0,1]` which is `unitMeasure`-conull —
  adjust `prior_atomless` to use `Measure.map` of the a.e.-injective map:
  preimage of `{g}` intersected with `[0,1]` is a subsingleton, plus the null
  complement.)
- Atomless: `prior {g} = volume (selMap ⁻¹' {g})`
  (`Measure.map_apply` — needs `Measurable selMap`
  (`Continuous.measurable`) and `MeasurableSet {g}` (singletons closed in a
  metric space: `measurableSet_singleton` via `T1Space`)). Preimage is a
  subsingleton by injectivity; null by F1/F2-style
  (`Set.Subsingleton.measure_zero`-search; else `measure_mono` into a
  singleton + F1 on the subtype/unitMeasure). ∎

### M5. The cost model and the verifier's complexity — DONE (computability route AND the N1 circuit)

> **Status.** Implemented in `PnpProof/Main.lean` as `verifyBits` (on `ℕ`) and
> `verifyBits_computable` (deviation 4). The development is **axiom-free and
> must stay so**: the old "labeled model axiom" fallback in this section is
> withdrawn. **N1 is now DONE**: the construction below is implemented in
> `PnpProof/Comparator.lean` (`verify_circuit_cheap`, with `Circuit.snoc`,
> `step`, `buildLT`, `baseSt`, `bitsOf`, `fullCircuit`; `div_pow_succ_compare`
> lives there too) and feeds `model_P_ne_NP_circuit` in `Main.lean`. The text
> below is retained as the record of the construction — do not re-implement.

**Design decision (document prominently):** Lean/Mathlib has no usable
complexity-theory library. Mathlib's `Turing.TM2ComputableInPolyTime` exists
but has near-zero API. The §6 "NP side" is therefore formalized at the level
of *bit-operation counting on dyadic data*, faithful to the paper's claim
("check whether the cumulative distribution crosses the sample").

**N1 — the `O(k)` comparator circuit (complete construction, translate
as written).** Target statement (new theorem in `Main.lean`):

```lean
theorem verify_circuit_cheap (k : ℕ) (hk : 1 ≤ k) :
    ∃ s ≤ 50 * k + 50, ∃ C : Circuit (3*k) (s+1),
      ∀ glo ghi u : Fin (2^k),
        C.eval (bitsOf k glo ghi u) = verifyBits glo ghi u
```

where `bitsOf` packs the three `k`-bit numbers little-endian:

```lean
def bitsOf (k : ℕ) (glo ghi u : Fin (2^k)) : Fin (3*k) → Bool := fun i =>
  if i.val < k then (glo : ℕ).testBit i.val
  else if i.val < 2*k then (ghi : ℕ).testBit (i.val - k)
  else (u : ℕ).testBit (i.val - 2*k)
```

- **Step 0 (constants; this is why `1 ≤ k`).** The gate set
  `{and, or, not, copy}` has no constant gates, and `Gate 0` is empty (its
  constructors take `Fin 0` arguments), so `Circuit 0 _` is uninhabited — the
  `k = 0` case is excluded by hypothesis. With at least one input node `x₀`,
  build constants in 3 gates: `n₀ := not x₀`, `TRUE := or x₀ n₀`,
  `FALSE := and x₀ n₀`.
- **Step 1 (the arithmetic driver — ALREADY PROVED, `Main.lean`).** For all
  `a b j : ℕ`:
  `a / 2^j = b / 2^j ↔ (a / 2^(j+1) = b / 2^(j+1)) ∧ (a.testBit j = b.testBit j)`
  and
  `a / 2^j < b / 2^j ↔ (a / 2^(j+1) < b / 2^(j+1)) ∨ ((a / 2^(j+1) = b / 2^(j+1)) ∧ a.testBit j = false ∧ b.testBit j = true)`.
  This is `div_pow_succ_compare`. Use it verbatim for step 4.
- **Step 2 (ripple comparator, big-endian over prefix divisions).** To compare
  `a, b < 2^k`, maintain two flag nodes per bit position `j = k, k−1, …, 0`:
  `eq_j` ("the prefixes `a / 2^j` and `b / 2^j` are equal") and `lt_j`
  ("`a / 2^j < b / 2^j`"). Initialize `eq_k := TRUE`, `lt_k := FALSE`
  (correct because `a, b < 2^k` gives `a / 2^k = 0 = b / 2^k`, by
  `Nat.div_eq_of_lt`). Step `j+1 → j`, with `aⱼ`, `bⱼ` the input nodes
  carrying `a.testBit j`, `b.testBit j`:
  - `eq_j := and eq_{j+1} (xnor aⱼ bⱼ)` where
    `xnor x y = or (and x y) (and (not x) (not y))` — 6 gates;
  - `lt_j := or lt_{j+1} (and eq_{j+1} (and (not aⱼ) bⱼ))` — 4 gates
    (reuse `not aⱼ` from the xnor if convenient).
  ≤ 10 gates per bit; after `k` steps, `eq_0`/`lt_0` decide `a = b` / `a < b`
  (divisions by `2^0` are the numbers themselves).
- **Step 3 (assembly).** `glo ≤ u` is `not (lt(u, glo))` and `u ≤ ghi` is
  `not (lt(ghi, u))`; two ripple comparators (≤ `10k + 3` gates each), two
  `not`s and a final `and` — total ≤ `20k + 10 ≤ 50k + 50` gates. The final
  node is the output (`Circuit.eval` reads node `n + s`).
- **Step 4 (correctness).** Build the circuit recursively, appending one
  bit-stage at a time, and prove by downward induction on `j` the invariant
  "node `eq_j` evaluates to `decide (a / 2^j = b / 2^j)` and node `lt_j` to
  `decide (a / 2^j < b / 2^j)`" — the induction step is exactly
  `div_pow_succ_compare`, and the base case is the `Nat.div_eq_of_lt`
  computation above. When a stage is appended, the values of earlier nodes do
  not change: this is `Circuit.nodeValNat_agree` (already proved in
  `Counting.lean`); use it exactly as `computableBySize_mono` does.
- **Step 5 (the upgraded main theorem).** Add a NEW theorem
  `model_P_ne_NP_circuit` whose NP-side conjunct is `verify_circuit_cheap`'s
  statement (∀ k ≥ 1, …) and whose P-side conjunct is T2, with the same
  mandatory docstring as T3 (see Part 5). **Do not modify or weaken the
  existing `model_P_ne_NP`.**

The "solution side" of the model needs no cost model at all: T2/T3's
impossibility is *information-theoretic* (no code computes the selection at
every resolution — regardless of time). State this clearly in docstrings: the
paper's P-side lower bound is formalized as *uncomputability w.r.t. the
prior* (stronger than "not poly-time" in the model: it rules out any
deterministic machine, fast or slow, except on a measure-zero set of priors).

---

## Part 5: Main theorems (`Main.lean`) — DONE incl. N1 `model_P_ne_NP_circuit` and T5 `model_vs_clay_disjointness` (T4 prose-only)

### T1. `selection_not_history` — PROVABLE (assembly)

```lean
theorem selection_not_history :
    -- (i) selection by conditioning is well-defined:
    (squareMeasure.fst ⊗ₘ squareMeasure.condKernel = squareMeasure) ∧
    -- (ii) every target output is a null event:
    (∀ y₀ : ℝ, squareMeasure {p : ℝ × ℝ | p.2 = y₀} = 0) ∧
    -- (iii) no countable history realizes it:
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (Y : ℕ → Ω → ℝ),
      (∀ n, Measurable (Y n)) → (∀ n y, P {ω | Y n ω = y} = 0) →
      ∀ y₀, P {ω | ∃ n, Y n ω = y₀} = 0
```

**Proof.** (i) is F3. (ii): the set is `(univ ×ˢ {y₀})`-shaped:
`{p | p.2 = y₀} = Prod.snd ⁻¹' {y₀}`; compute
`squareMeasure (Prod.snd ⁻¹' {y₀}) ≤ volume.restrict (...) (ℝ ×ˢ {y₀})`,
or directly: `volume (A ×ˢ {y₀}) = volume A * volume {y₀} = 0`
(`Measure.volume_eq_prod` (search) + `Measure.prod_prod` + F1 +
`mul_zero`; then `measure_mono_null` through the restriction —
`Measure.restrict_apply_le`-style: restricted measure ≤ unrestricted on
measurable sets... simplest: `Measure.restrict_le_self` (search) applied to
the null superset). (iii) is F4. ∎

### T2. `almost_all_not_computable` — PROVABLE (assembly)

The formal core of §2/§3/§6-option-1: with prior probability 1, the selected
function is not computed by ANY code.

```lean
theorem almost_all_not_computable :
    prior {g : C(↥(Icc (0:ℝ) 1), ℝ) |
      ∃ c : Nat.Partrec.Code, ComputesSelection c (extend g)} = 0
```

(`extend g` : the obvious extension of the continuous map on the subtype to
`ℝ → ℝ` — define once in M3/M4 and use consistently; or restate
`ComputesSelection` directly for `C(K,ℝ)` elements, which is cleaner — make
that representational choice in M3 and keep it.)

**Proof.** The set is contained in the image under restriction-inverse of the
countable set of computable selections (M3 `countable_computable_selections`);
intersecting with the (injective) range of relevant functions keeps it
countable; each singleton is `prior`-null by M4 `prior_atomless`; countable +
all-singletons-null ⇒ null by F2's union argument (note: F2 as stated needs
`NoAtoms`; either register `NoAtoms prior` as an instance from
`prior_atomless` (the class constructor takes exactly that proof) and apply
F2 verbatim, or inline the countable-union-of-nulls computation with
`measure_iUnion_null`). **Subtlety to verify when formalizing**: the set in
the statement must be a *measurable or null-coverable* set — F2's route only
needs an outer cover by countably many singletons, which is exactly what
countability gives; no measurability needed (`measure_mono_null` +
`measure_iUnion_null` on the cover). ∎

Optional corollary tying to C1/C2 (nice for the paper narrative, cheap):
`prior`-a.s., the digit function of the selected output at any fixed input is
not computable... skip unless requested; T2 is the load-bearing statement.

### T3. `model_P_ne_NP` — DONE (computability form)

> **Status.** Implemented in `PnpProof/Main.lean`: the NP-side conjunct is
> `Computable (fun p : ℕ × ℕ × ℕ => verifyBits p.1 p.2.1 p.2.2)`
> (deviation 4), the P-side conjunct is T2. The circuit-form NP side shown
> below is ALSO implemented (N1, done): `model_P_ne_NP_circuit`, beside the
> original. **Never modify the existing `model_P_ne_NP`.**

The honest formalization of §6, option 1. Final statement (shape):

```lean
theorem model_P_ne_NP :
    -- (NP side) verification is cheap: a circuit family of size O(k) decides
    -- the §3 verifier on k-bit data:
    (∀ k, ∃ s ≤ 50*k + 50, ∃ C : Circuit (3*k) (s+1),
        ∀ glo ghi u, C.eval (bitsOf glo ghi u) = verifyBits glo ghi u) ∧
    -- (P side) solution is impossible for the prior-typical instance:
    prior {g | ∃ c, ComputesSelection c (extend g)} = 0
```

**Proof.** First conjunct: M5's comparator construction (for
`model_P_ne_NP_circuit`; the implemented `model_P_ne_NP` uses
`verifyBits_computable` instead). Second conjunct: T2. ∎

**Docstring (mandatory, exact content):** *"This theorem separates
verification from solution within the model of `pnp.tex` §§3–6: verification
of a candidate output is uniformly cheap, while no deterministic machine
computes the selected function on a set of priors of positive measure. It is
a theorem about this model. It is NOT the Clay Millennium statement
`P ≠ NP`, and no claim of implication is formalized — see Part 6 of the
implementation plan."*

Also record (cheap, completes the §6 picture): the §5→§6 conversion glue —
from any "mixed" measure with nonvanishing diffuse part, F8 produces the
atomless measure required by the F1/F2/T2 chain; state as a remark-lemma:

```lean
theorem mixed_to_continuous {α} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] (h : μ {x | μ {x} ≠ 0}ᶜ ≠ 0) :
    ∃ ν : Measure α, IsProbabilityMeasure ν ∧ (∀ x, ν {x} = 0) := by
  -- F8 + the normalization remark; package the two into the ∃
```

### T5. `model_vs_clay_disjointness` — DONE (added 2026-06-12 at the maintainer's request)

The Tier-C *relationship* between the model and the Clay statement, made
checkable without defining the Clay classes. Implemented in
`PnpProof/Main.lean`:

```lean
def DecidesSelection (L : ℕ → Bool) (g : C(K, ℝ)) : Prop :=
  ∀ k : ℕ, ∀ x : K, (x : ℝ) ∈ Ico (0:ℝ) 1 → g x ∈ Ico (0:ℝ) 1 ∧
    ∀ j : Fin (2^k),
      (L (Nat.pair k (Nat.pair (dyadicIndex k (x : ℝ)) j)) = true ↔
        dyadicIndex k (g x) = j)

theorem model_vs_clay_disjointness (NP : Set (ℕ → Bool))
    (hNP : ∀ L ∈ NP, Computable L) :
    prior {g : C(K, ℝ) | ∃ L ∈ NP, DecidesSelection L g} = 0
```

**Reading**: a language `L : ℕ → Bool` (the kind of object the Clay statement
quantifies over) *decides the selection* `g` if, queried on the encoded triple
`(resolution, input index, candidate output index)`, it answers exactly
whether the candidate is the dyadic index of `g`'s output. For ANY collection
`NP` of languages all of whose members are computable — as is every faithful
formalization of the Clay classes, since `NP ⊆ EXPTIME` — prior-almost-surely
no member decides the selection: the model's hard object lies outside the
arena in which the Clay problem is played, which is why `model_P_ne_NP`
neither implies nor is implied by the Clay statement. The docstring carries
the mandatory honesty text (NOT the Clay statement; the Clay classes are not
defined; no implication in either direction is formalized).

**Proof (implemented, recorded here).** (1) *Uniqueness*
(`decidesSelection_unique`): if `L` decides both `g` and `h`, then for every
`x` with `(x:ℝ) ∈ [0,1)` and every `k`, the `j := dyadicIndex k (g x)`
instance of `g`'s iff gives `L (…) = true`, and `h`'s iff (same encoded query)
forces `dyadicIndex k (h x) = dyadicIndex k (g x)`; `mem_dyadic_index` +
`dyadic_width` then give `|g x − h x| < 2⁻ᵏ` for every `k`, so `g x = h x`;
the set `{x : K | (x:ℝ) ∈ [0,1)}` is dense in `K`
(`dense_selection_domain`: any ball around `1` contains `1 − min(r/2, 1/2)`),
so `Continuous.ext_on` extends the agreement to all of `K`. (2)
*Countability* (`countable_language_decided_selections`): the computable
languages are countable (C1 `countable_computable_bool`), and by (1) each
decides at most one selection, so the decided selections are a countable union
of subsingletons. (3) *Null* (`selection_not_language_decidable`): F2
`countable_null` (the `NoAtoms prior` instance is registered). (4) The main
theorem is `measure_mono_null` from the inclusion
`{g | ∃ L ∈ NP, …} ⊆ {g | ∃ L, Computable L ∧ …}` given `hNP`. ∎

**Fence**: this theorem is the ONLY Clay-facing statement permitted in code.
It quantifies over an abstract hypothesis-constrained class; it must never be
"upgraded" by defining the actual Clay classes or asserting any implication
between `model_P_ne_NP` and `P ≠ NP` — see Part 6.

### T4. Realistic version (§7) — OPEN; resolved as PROSE-ONLY (deviation 5)

§7's argument ("approximate selection still cannot be approximated, using the
L^∞ norm and a two-set output partition") is a sketch in the paper; no
complete proof exists to transcribe. **Resolution (ratified):** no Lean
statement and **no `sorry`** were committed — the old sorry-stub option is
withdrawn so the development stays sorry-free. A module docstring in
`Main.lean` records the situation, including why a purely *analytic*
approximation statement would be **false** (polynomials are dense in
`C([0,1])` and `L²([0,1])`, so every continuous selection function is
uniformly approximable); the §7 claim is about *computational*
(polynomial-time) approximation, and drafting that statement precisely is
research. **Standing instruction:** do not add any T4 statement unless the
maintainer supplies a precise statement plus a complete English proof.
Provable ingredients already available if that day comes: H5 (polynomial
density), H2 (L^∞ pathology), M1–M4.

---

## Part 6: Explicitly OUT OF SCOPE — do not attempt

1. **The Clay bridge** (§6 "This implies P ≠ NP", §6 option 2): the argument
   that the paper's computer model is *the* legitimate model for the official
   problem statement is epistemology, not mathematics. The paper itself
   flags it for expert review. In Lean it appears only as the docstring of
   T3. Never introduce an axiom of the form `model_P_ne_NP → P ≠ NP`.
   Never define standard `P`/`NP` here at all — a half-credible definition
   would be a bigger project than this whole plan and would invite the exact
   confusion the docstring guards against. The only Clay-facing statement
   permitted in code is T5 (`model_vs_clay_disjointness`), which proves the
   two arenas are *disjoint* — it quantifies over an abstract class of
   computable languages and must stay that way.
2. **Turing-machine time lower bounds** from circuit counting (§2's
   `O(2^n/(n log n))`): needs TM-to-circuit simulation with explicit
   overheads (Cook–Levin-grade infrastructure). Unused downstream (the chain
   uses C1-countability and C5-circuit-counting only).
3. **Abelian von Neumann algebra classification** (§5's five-item list) and
   the **standard-probability-space classification**: genuine theorems, huge
   formalization, and the only consequence used (atoms countable + diffuse
   conditioning) is F5/F8.
4. **Fock/Guichardet constructions** (§4): replaced by H6; building tensor
   algebras of Hilbert spaces is a Mathlib-sized project.
5. **The k-dimensional hyperspherical-coordinates area element** (the
   chapter's `dσ(k)` display) and **Gegenbauer orthogonality at finite α**:
   not needed — Part 3b's Gaussian construction (G5) and DCT-limit (G4)
   replace them. The infinite-dimensional sphere content itself IS in scope
   via Part 3b (G1–G7); only these two coordinate-level devices are excluded.
6. **§8 (linear-time randomness)**: the paper says "We cannot prove this
   mathematically". Take it at its word.
7. **§9 (Machine Learning)**: prose.

---

## Part 7: Status and next steps

All ten original milestones are **complete**, and so are the follow-up items
N1 (the `O(k)` comparator circuit, `Comparator.lean` + `model_P_ne_NP_circuit`)
and T5 (`model_vs_clay_disjointness`) — see the Status section at the top. The
development compiles sorry-free and axiom-free. What remains is the queue
below.

**Ground rules for every queue item:**

- Each item must land **sorry-free** on its own; partial work is reverted,
  not committed with a `sorry`.
- **No new axioms, ever.** If an item cannot be completed as specified, stop
  and report — do not improvise mathematics.
- Never modify or weaken an existing theorem; upgrades are NEW theorems
  beside the old ones (e.g. `model_P_ne_NP_circuit` beside `model_P_ne_NP`).
- Verify every Mathlib name with `lake env lean --stdin <<< '#check …'`
  before relying on it; run `lake exe cache get` before any build.
- After each item, update `PnpProof/IMPLEMENTED.md` (lemma, file, deviations).
- Translate the English proofs as written; do not redesign them.

### The queue

| # | Item | Complete English proof at | Notes |
|---|------|---------------------------|-------|
| ~~N1~~ | ~~`bitsOf`, `verify_circuit_cheap`, `model_P_ne_NP_circuit`~~ | §M5, steps 0–5 | **DONE 2026-06-12** in `Comparator.lean` + `Main.lean`; do not re-implement |
| ~~T5~~ | ~~`model_vs_clay_disjointness`~~ | §T5 | **DONE 2026-06-12** in `Main.lean`; do not re-implement |
| N2 (optional) | Style-linter housekeeping | — | the build emits `linter.style.multiGoal`, `linter.style.whitespace`, and `linter.style.longLine` warnings (the latter mainly in `SphereGaussian.lean`); fix with `·` focus dots / whitespace / line breaks only — if any proof breaks, revert that fix |
| **F-min (recommended)** | **Definitional-base witnesses**: import-tier separation + axiom-footprint audit + `T-conserv` | **Part 11** | the maintainer's 2026-06-14 #2 directive (refined): the definitional base is the *Kopperman formalism's own*, **incomparable with PA**, co-consistent with PA and ZFC; over standard `ℕ` it defines the *standard* P-vs-NP sentence. Lands as: (a) arithmetic-tier statement imports no measure theory / `Kopperman`; (b) `#print axioms` audit of C1/C5/N1 in `IMPLEMENTED.md`; (c) `T-conserv` proved. **No `PA ⊢ …` / theory-comparison predicate** — flagged, not built |

### Explicitly NOT on the queue

- **T4** (§7 realistic version): prose-only by deviation 5; needs a
  maintainer-supplied statement + complete English proof first.
- **G7′** (finite-`k` Chebyshev) and the weak-convergence corollary
  `poincare_borel`: superseded by the implemented a.s. forms
  (`gaussian_concentration_sphere`, `poincare_borel_ae`); deviation 7.
- Everything in Part 6 (Clay bridge, TM time bounds, von Neumann
  classification, Fock/Guichardet, area element, §§8–9) — permanently out of
  scope.
- **The Shoenfield `Π⁰₂` absoluteness transfer** (2026-06-14 proposal,
  Phases 4–5) — rejected as unsound; see **Part 8**. The `axiom
  shoenfield_absoluteness` + `absolute_P_ne_NP` step must NOT be added: it is a
  forbidden Clay-bridge axiom (Part 6 #1) and is refuted by T5.

**Reporting duty**: unchanged — keep `PnpProof/IMPLEMENTED.md` current
(lemma, file, any deviation). Any queue item that turns out unprovable *as
stated here* gets the RiemannProof treatment: do not force it — restate
minimally, record the diagnosis, and flag it in the report.

---

## Part 8: Assessment of the 2026-06-14 proposal (indicator separation + Kopperman/Shoenfield)

A five-phase extension was proposed: (1–3) a **mixed-measure "indicator
separation"** (condition on a constant rational output `y`, isolate the
continuous component, show `P`-solvers are null while the indicator verifier is
cheap); (4) a **Kopperman Hilbert-space "standard model"** in which *choosing a
prior* is claimed to construct a valid model of the computational axioms; and
(5) a **Shoenfield `Π⁰₂` absoluteness transfer** concluding the Clay statement
`P ≠ NP` from the model separation, via a new `axiom shoenfield_absoluteness`
and a theorem `absolute_P_ne_NP : P_ne_NP_Pi20`.

The two halves get opposite dispositions. **Read this before touching either.**

### Phases 1–3 (indicator separation) — ADMISSIBLE but mostly REDUNDANT; model-fenced

Everything in Phases 1–3 is sound measure theory, and **it is already
implemented**, under different names and the mandatory model fence:

| Proposed item | Already in `PnpProof/` |
|---|---|
| mixed prior = continuous + countable (`conditioned_measure_structure`) | **F5** (atoms are countable) + **F6** (continuous ⊥ atomic) + **F8** (conditioning on the diffuse part is atomless) |
| condition on constant rational `y` is well-defined though `P(y)=0` | **T1** `selection_not_history` (this is literally the paper's title fact) + **F7** (the rational-interval jump) |
| constant-output functions are null under a continuous prior | **F1** (points null) + **T2** `almost_all_not_computable` (computable selections null) |
| indicator verifier is cheap / in "NP" | **M5** `verifyBits_computable` and **N1** `model_P_ne_NP_circuit` (explicit `O(k)` comparator) |
| model separation `model_indicator_P_ne_NP` | **T3** `model_P_ne_NP` (+ circuit form) |

If a *literal* "indicator function" restatement is still wanted for narrative
parity with `pnp.tex` §6 option 1, it may be added **as a new theorem beside the
existing ones**, Tier-B, carrying the mandatory docstring ("a theorem about this
model; NOT the Clay statement; no implication formalized"). Constraints:

- **No new axioms** (Part 7 ground rules). The pieces above are all proved.
- **Never name it `…P_ne_NP` without the `model_` prefix** (Part −1).
- It changes nothing about the Clay relationship — that remains T5's disjointness.

Net: Phases 1–3 are at best a cosmetic restatement of done work. Worth doing only
if the maintainer wants the §6-option-1 phrasing mirrored verbatim; otherwise skip.

### Phases 4–5 (Kopperman "standard model" + Shoenfield transfer) — REJECTED (unsound)

This is the same Clay bridge the project has refused throughout (Tier C; Part 6
#1; the prior "equivalence request refused as unprovable"), now dressed in
model-theory vocabulary. It must **not** be formalized. Four independent reasons,
any one fatal:

**(a) Category error in "the prior is a standard model."** A probability measure
on a Hilbert space is an object *inside* ZFC; it is not a transitive `∈`-model
*of* ZFC. `IsStandardModel physical_prior ComputationalAxioms` does not type-check
as mathematics — "standard model" in Shoenfield's theorem means a transitive
model of (a fragment of) set theory, an entirely different notion from "a chosen
measure." `prior_is_valid_model` cannot be proved because its statement is a
confusion of two meanings of "model."

**(b) The one rigorous reading still gives ZERO leverage.** The single sense in
which "a measure yields a model" is genuine is **random forcing**: a measure
algebra `B` yields a Boolean-valued model `V^B` / random-real extension `V[G]`,
and Shoenfield absoluteness *does* hold — `Π¹₂` statements (so `Π⁰₂`, so
`P ≠ NP`) have the **same truth value** in `V` and `V[G]`. But absoluteness is a
**two-way conservativity**, not a proof shortcut:
`V[G] ⊨ (P ≠ NP)  ⟺  V ⊨ (P ≠ NP)`.
Proving the statement "in the model" is therefore *exactly as hard* as proving it
outright. Far from enabling the transfer, Shoenfield is precisely the theorem
saying **no such forcing/measure shortcut to `P ≠ NP` can exist.** "Prove it in
one prior and absoluteness does the rest" inverts what the theorem says.

**(c) The measure result is not "`P ≠ NP` holding in the model" — T5 proves
this, mechanically.** `model_P_ne_NP` is a ZFC theorem about the `prior`-measure
of subsets of `C(K, ℝ)`. The arithmetic sentence `P_ne_NP_Pi20` quantifies over
Turing machines on finite inputs. `model_vs_clay_disjointness` (T5) — a ZFC
theorem, hence equally true in `V` and in any `V[G]` — proves the model's hard
object lies **outside the arena** of any computable-language class. So
`IsTrueIn physical_prior P_ne_NP_Pi20` is exactly the unestablished (and, by T5,
unestablishable-from-this-data) bridge; the proposed final step
`exact model_indicator_P_ne_NP_true_in_prior` has no proof. The "P-solvers are a
null set ⇒ no efficient algorithm" inference is the classical non-starter:
*null ≠ empty*, and a discrete-input complexity class has no continuous prior on
`ℝ → ℝ` attached to it.

**(d) It violates the project's hard invariants.** The development is axiom-free;
Part 6 #1 states verbatim: *"Never introduce an axiom of the form
`model_P_ne_NP → P ≠ NP`."* The proposed `axiom shoenfield_absoluteness` plus
`absolute_P_ne_NP` is exactly such an axiom with extra steps — and as written it
is not even a faithful statement of Shoenfield's theorem (which has no
`IsTrueIn (measure) (arith stmt)` premise), so importing it would let a
measure-theoretic fact masquerade as arithmetic truth: an unsound extension of a
currently-consistent development.

### The "ZFC on top of Kopperman" layering variant — also fails

A follow-up defense (2026-06-14): *the probability measure defines a model of
the Kopperman theory, on top of which ZFC models are defined, so the measure is
part of an overall ZFC model and Shoenfield then applies.* Checked against the
actual `Kopperman_Tutorial.p.tex`, this does not hold.

- **What Kopperman actually provides.** The file invokes Kopperman's 1967
  *"The `L_{ω₁,ω₁}`-Theory of Hilbert Spaces"*: infinitary logic `L_{ω₁,ω₁}`
  has the expressive power to pin down the unique separable complete Hilbert
  space (the "Completeness Axiom"), while a *countable fragment* of `L_{ω₁,ω}`
  supplies a complete proof system over the **decidable dense subset** (finite
  rational combinations of basis vectors). That is a theory **of a Hilbert
  space**, whose models *are Hilbert-space structures* `(H, …)`. It is **not**
  set theory, contains **no** Turing machines or complexity classes, and its
  models are **not** models of ZFC.
- **The layering inverts the foundations (and meets Gödel II).** A Hilbert
  space with a measure `(H, μ)` is an object constructed *inside* ZFC — it
  presupposes `ℝ, ℂ, ℓ², Borel σ-algebras`, all defined in set theory. One does
  not build a universe of sets "on top of" a single separable Hilbert space:
  that space has cardinality `𝔠`, far too small to interpret ZFC, and by
  **Gödel's second incompleteness theorem** the ambient ZFC in which the
  Kopperman/Mehler apparatus is developed cannot exhibit a model of ZFC at all
  (that would prove `Con(ZFC)` internally). So "a ZFC model on top of the
  Kopperman model, with the measure inside it" is not a constructible object;
  the dependency runs the other way.
- **Granting the backward direction in Lean changes nothing — that is what
  "interpretation" *guarantees*.** Lean's type theory is strictly stronger than
  ZFC (its universe hierarchy proves `Con(ZFC)`), so Lean genuinely *can* host
  both directions: Mathlib's `ZFSet` is a bona-fide model of ZFC, and Hilbert
  structures are ordinary Lean objects, so "ZFC within Kopperman" and "Kopperman
  within ZFC" can both be written. Conceded. But a relative *interpretation*, in
  either direction, is **arithmetically conservative** by definition: it
  transports proofs, not the *difficulty* of proofs. If `Kopperman → ZFC` is a
  faithful interpretation, the two prove **exactly the same `Π⁰₂` sentences** —
  so the backward route proves `P ≠ NP` **iff** the forward route does. The net
  leverage on P vs NP is provably *zero*; you cannot discharge a hard arithmetic
  statement by re-coordinatizing the foundation it lives in. (Encoding ZFC's
  *syntax / proof system* in the Turing-complete UPL host is trivially possible
  but yields only syntax — no model, no `Con`, no leverage; a genuine *model*
  like `ZFSet` has the standard `ω`, into which the measure still does not
  enter.)
- **The decisive point needs none of the above — `ω` settles it.** `P ≠ NP` is
  `Π⁰₂`: its truth in any model is a fact about that model's **natural-number
  structure `ω` alone**. The probability measure is not part of `ω`. So no
  matter how the measure is layered into a structure, it **cannot change, and
  therefore cannot help decide,** which arithmetic sentences hold. If the
  overall model is an `ω`-model, its `P ≠ NP` value equals the real one
  (absoluteness) — established only by settling the arithmetic, which the
  measure fact (disjoint from it by **T5**) does not touch. If it is a
  non-`ω`-model, "`P ≠ NP`" there is a statement about nonstandard machines —
  a *different* claim from the Clay problem, and Shoenfield (which needs
  well-founded models) does not even apply.
- **A ZFC universe cannot have "only one prior" — that move exits the class.**
  The defense "build the universe so the chosen measure cannot be undone or
  redone; other priors do not exist by definition" is self-defeating. ZFC
  *proves* that on any measurable space many probability measures exist (Dirac
  measures, convex mixtures, pushforwards, …). So any genuine model `M ⊨ ZFC`
  **contains** those other priors — the premise "no other priors" is outright
  false in `M`. Conversely, a structure engineered to admit exactly one prior
  violates those ZFC existence theorems, so it is **not a model of ZFC**: it
  carries neither the Clay `P vs NP` (whose definition presupposes such a model)
  nor Shoenfield absoluteness (which quantifies over models of ZF). Moreover,
  defining the measure "first" creates no dependency: the definitions of Turing
  machine, `P`, `NP`, and SAT **never mention a measure**, so `P ≠ NP` is
  measure-independent regardless of authoring order — *definitional order is not
  logical dependency*, and `ω` is the canonical measure-free object of every ZFC
  model. (Tellingly, a measure-*relative* "P vs NP" — i.e. `σ` — is **decided**
  in the model: computable objects are null, full stop. A problem that turns
  trivial upon redefinition has been replaced, not solved.)
- **"Hilbert completion needs more than FOL; `P ≠ NP` is FOL" — both true, and
  jointly they *shut* the door.** Categorically axiomatizing the separable
  Hilbert space (the completeness clause "every Cauchy sequence converges") does
  require infinitary logic `L_{ω₁,ω₁}` *in the vector language* — Kopperman's
  genuine point. But that is axiomatizing the space as a standalone structure;
  it is **not** the claim that Hilbert spaces are undefinable in first-order
  ZFC. Inside ZFC, sequences are sets, the metric completion is a routine
  first-order `∈`-construction (Mathlib's `UniformSpace.Completion`), and "many
  probability measures exist" is an elementary first-order theorem — so the
  previous bullet stands. The judo: *because* `P ≠ NP` is first-order
  arithmetical, it sits in the **most absolute layer there is** — its truth is
  fixed by `ω` and is invariant under whatever infinitary/analytic superstructure
  (measures, `L_{ω₁,ω₁}` completeness axioms, C*-algebras) is erected above it.
  Strengthening the ambient logic only pins `ω` down *harder* to the standard
  model (it eliminates nonstandard `ω`); it never makes an arithmetic sentence
  read the measure. Stay first-order and `ω` may be nonstandard — but then it is
  not the Clay `ω`. Either way the measure never enters the truth value of
  `P ≠ NP`: `ω` is fixed by well-foundedness/induction, never by a prior.
- **Selecting the standard model fixes the truth *value*, never the *proof* —
  and the disjointness holds *inside* the standard model.** Conceded: FOL cannot
  select standard models, and infinitary logic (Kopperman) *can* pin down the
  standard reals and standard `ω`. But **semantic determinacy is not
  provability**. Categorically fixing *which* structure we mean fixes `P ≠ NP`
  to its unique standard truth value; it does **not** tell you that value and
  does **not** hand over a derivation — `Th(ℕ)` is not delivered by categoricity
  (it is not even arithmetically definable). And the category gap is itself a
  fact *about the standard model*: in the real `ℕ` with the real measure space,
  `σ` = "computable selections are null" is trivially true yet says nothing about
  whether the **one** function `SAT` has a polynomial-time machine. `SAT` is a
  single computable point (null regardless of the prior), and `P vs NP` is a
  *resource bound on that one machine*, not the measure of a function class. `T5`
  is exactly this disjointness, and `T5` holds of standard structures. So
  selecting standard reals removes nonstandard ambiguity — genuine, and entirely
  *orthogonal* — while leaving `σ ⇒ (P ≠ NP)` exactly as unproved, now
  demonstrably so in the very model you selected. (Aside: Lean/Mathlib
  provability is r.e. like any first-order system; `UniformSpace.Completion` is a
  *definition* and blocks no proof. Standardness of `ℝ` is not what stands
  between anyone and a SAT lower bound — the relativization / natural-proofs /
  algebrization barriers are, and a measure-zero count over a function space
  engages none of `SAT`'s structure, so it cannot separate.)
- **There are not "many incompatible standard `ω`'s" — this is the real crux,
  and it is false.** Granted: there are genuinely incompatible ways to strengthen
  FOL and discard nonstandard models — `V=L` vs forcing axioms vs large cardinals
  — and they disagree about real statements. But that incompatibility lives at
  the level of **the continuum and higher set theory** (`CH` and up: the
  `Σ¹₃`-and-beyond region where Shoenfield absoluteness stops). At the level of
  **arithmetic**, the standard model `ω` is **unique up to isomorphism**
  (Dedekind categoricity): second-order PA, `L_{ω₁,ω}`'s standardness axiom,
  Kopperman's `L_{ω₁,ω₁}`, and "the standard reals" all pin down the *same* `ω` —
  there is no rival "Kopperman `ω`." Kopperman selects the standard reals; the
  standard reals contain the standard `ω`; a first-order (`Π⁰₂`) sentence is
  evaluated against *that* `ω` with the *same* answer under every method. So the
  incompatibility you invoke is real but located precisely where `P vs NP` is
  **not**. Critically, my objection assumes **none** of the rival strengthenings:
  it grants Kopperman's standard universe wholesale and observes, *inside it*,
  that `σ` (a measure on a function space) and `P ≠ NP` (a runtime bound on the
  single machine for `SAT`) are different sentences. That observation needs no
  second-order logic, no nonstandard models, no rival discarding method — it is
  **FOL-minimal**. The bridge `σ ⇒ (P ≠ NP)` is the *only* thing here that needs
  something beyond, and no logic supplies it. (Kopperman's one genuine divergence
  from standard analysis — the **countable-additivity restriction**,
  §"Countable Additivity Caveat" — constrains `σ`'s *own* proof; it does nothing
  to connect `σ` to `P ≠ NP`.)
- **The tutorial's own framing agrees.** Its §"Probability as Political Choice"
  says the Mehler measure *fills the undecidable logical gaps* with "a weighted
  preference, transitioning from absolute truths (which may be undecidable) to
  **likely outcomes** (which are calculable)," and its §"Countable Additivity
  Caveat" restricts the measure to *definable sets of a countable fragment*.
  That is an **epistemic prior assigning a credence** `P(P ≠ NP)` to an
  undecidable proposition — explicitly *not* a proof and *not* a model that
  makes the arithmetic sentence true. Reading it as a proof inverts what the
  framework claims for itself.

The genuinely valuable Kopperman content — `L_{ω₁,ω₁}` pinning down the
separable Hilbert space, and the **decidable dense subset / computable
skeleton** — is real Tier-A mathematics and is *already* reflected in the
development (H1 separability, H4/H5 the countable dense subset, F1/F2/T2 the
null-set/computable-skeleton facts). It can be formalized further on its own
terms. None of it is a bridge to the Clay statement.

### Transport is content-preserving — it carries the statement you proved, not the one you want

The final form of the defense (2026-06-14): *interpretation transports proofs,
the measure is part of the model definition, therefore the in-model proof is a
valid proof of `P ≠ NP`.* The first clause is true and is exactly why the
argument fails. An interpretation maps a proof of `φ` to a proof of `i(φ)`: it
is **content-preserving** — what comes out is (the translation of) what went in.

What actually gets proved in the measure model is
`σ := “the computable selections are μ-null”` (`model_P_ne_NP`). Transport
therefore delivers `σ` (relabeled) on the other side — **not** the arithmetic
sentence `P ≠ NP`. Transport does not insert the missing step `σ ⟹ (P ≠ NP)`;
that step is a *mathematical implication*, not a logical translation, and it is
false here (null ≠ empty; distinct arenas; this is precisely what **T5**
proves). So a clean dichotomy closes the matter — and "the measure is part of
the model" lands on the wrong horn of it:

- **If the transported sentence is the arithmetic Clay `P ≠ NP`:** it quantifies
  over naturals/Turing machines only. Its truth in a model depends solely on
  that model's `ω`, and **not** on the measure — no matter how central the
  measure is to the model's *definition*, the sentence's quantifiers never range
  over it. The measure-null argument simply is not a derivation of this sentence
  (it concludes a measure fact). Transport is irrelevant; the arithmetic
  sentence was never proved.
- **If the transported sentence is the measure-separation `σ`:** transport works
  perfectly and hands back `σ` — which is `model_P_ne_NP`, already a ZFC
  theorem, and which **T5** shows is disjoint from Clay `P ≠ NP`. Transport
  delivered something true and something that is not P vs NP.

Either horn: no proof of the Clay statement. "The measure is part of the model
definition" is true and changes nothing, because the Clay sentence does not
mention the measure, and the sentence that does mention it is not the Clay
sentence. This is not a gap to be filled by more clever layering; it is the
fixed content of the two distinct sentences.

### "A proof of `P ≠ NP` need not live in FOL" — true, and it still does not help

Conceded without reservation: a *proof* of a first-order arithmetic statement
need **not** be first-order. Goodstein's theorem and the Paris–Harrington
principle are `Π⁰₂` facts whose proofs need transfinite/infinitary methods
unavailable in PA; the prime number theorem is an arithmetic statement classically
proved through complex analysis. So "the proof may use continuous probability
spaces / continuum-level machinery" is **not**, by itself, an objection — and I
am not raising it as one. Higher-order tools in service of an arithmetic
conclusion are completely legitimate.

But put that together with the fact you just invoked — *the incompatible
strengthenings disagree at the continuum level* — and a dichotomy forecloses the
route, cleanly, using your own premise:

- **Either** the measure/regularization argument's conclusion is **absolute**
  (identical under every continuum strengthening — `V=L`, forcing axioms, large
  cardinals). Then the choice of Kopperman did no work — any strengthening yields
  the same conclusion — and that conclusion is `σ` ("computable selections are
  null"), which `T5` shows is a *different sentence* from `P ≠ NP`. No bridge.
- **Or** the conclusion genuinely **depends on the Kopperman-specific continuum
  choice** (differs across the incompatible alternatives). Then it is a
  non-absolute, continuum-level statement, and therefore **cannot be** the
  arithmetic `P ≠ NP`, whose truth value is fixed by the unique standard `ω` and
  is identical across all those strengthenings (Shoenfield / categoricity).
  Whatever was proved, it is not the Clay statement.

This is forced *precisely because* a `Π⁰₂` truth is absolute: any continuum
machinery a **valid** proof of `P ≠ NP` employs must land on the
**choice-independent floor** — as PNT's complex analysis does for its arithmetic
conclusion. A conclusion that draws its force from a continuum-level *choice the
strengthenings disagree about* is, for that very reason, disqualified from being
an absolute arithmetic statement. So "the proof lives at the continuum, where the
choice has force" is self-defeating *for `P ≠ NP` specifically*: the more the
regularization choice matters, the less arithmetic the conclusion can be. The
genuine analytic route to `P ≠ NP` uses measure/analysis as a *tool* to force a
**circuit lower bound on `SAT`** (an absolute arithmetic fact); the
null-set-of-a-function-class argument never touches `SAT`'s complexity and
concludes `σ` instead — which is exactly why it is not that proof.

### Bottom line — the syllogism, and the single premise that fails

The defense, stripped to its logic, is a valid argument with one false premise —
and it is **not** the premise about *whose* model we use. So the "you assume your
own model of ZFC" charge misreads the objection:

- **(P1)** *If a `Π⁰₂` sentence is true in some `ω`-model of ZFC, it is true
  absolutely (in every `ω`-model).* — **GRANTED.** This is categoricity /
  absoluteness, and the model may be **yours**: `M` = the Kopperman universe,
  which selects the standard reals, hence the standard `ω`. I do **not** require
  "the same model I assume"; work entirely in `M`. (Minor precision: absoluteness
  delivers "true in all `ω`-models," which is the correct target — it need not be
  "PA-provable," and you rightly do not need PA-provability. A non-FOL proof of
  truth-in-`M` is fine.)
- **(P2)** *The measure proof establishes that `P ≠ NP` is true in `M`.* —
  **THIS is the false/unmet premise.** What the proof establishes in `M` is `σ`
  = "the computable selections are `μ`-null." Since `M ⊨ ZFC`, `M` satisfies
  `T5`; so **inside `M` itself**, `σ` does not entail `P ≠ NP`. The antecedent of
  (P1) is never discharged.

So: absoluteness — conceded; your choice of model — conceded; the proof need not
concern "my" model — conceded. The entire disagreement reduces to (P2): in `M`,
what is proved is `σ`, and `σ ≢ (P ≠ NP)` *in `M`* (that inequivalence is `T5`, a
theorem `M` satisfies). No amount of choosing `M` well repairs (P2), because the
shortfall is internal to `M`.

### Why (P2) fails, concretely — no model theory required

Two clarifications first. (i) *I am not arguing from the existence of other
models.* The objection is internal to the one model `M` you choose; the
"many measures exist" remark earlier rebutted only the separate "no other priors"
move, and is not load-bearing here. (ii) *"A model of ZFC where no function is in
`P`" does not exist* — every model of ZFC proves `P` is nonempty (the empty
language, all finite languages, constant functions are in `P`). What the prior
gives is that the computable functions are **`μ`-null**, and **null ≠ empty**: a
null set is typically nonempty (e.g. `ℚ ⊂ ℝ`). Conflating "the `P`-functions have
measure zero" with "no function is in `P`" is exactly the slip.

Now the concrete reason `σ ⇏ (P ≠ NP)`, with no models, no logic strength, no
priors-comparison:

- `σ` = "the computable functions are `μ`-null" is provable **outright** —
  computable ⇒ countable ⇒ null in an atomless prior — *without resolving P vs
  NP*. So `σ` holds in a world where `P = NP` and in a world where `P ≠ NP`
  **alike**: the countability of the computable functions does not depend on
  whether `SAT` has a fast algorithm. A statement whose truth is **independent of
  the P-vs-NP answer cannot discriminate between the two**, hence cannot prove
  either. (If `σ ⇒ (P ≠ NP)` held, then `ZFC ⊢ σ` would give `ZFC ⊢ (P ≠ NP)`
  via a one-line countability argument — the standard "too good to be true"
  tell.)
- Concretely: `SAT` is **decidable**, so `SAT` is one element of the (countable,
  null) set of computable functions **whether or not `SAT ∈ P`** — the prior puts
  it in the null set in both cases. The model's separation is therefore
  *computable-vs-uncomputable* (a measure/cardinality fact about a random real
  function), **not** *polynomial-vs-superpolynomial* (a resource bound on a fixed
  decidable language). `P vs NP` asks the second question; `σ` answers only the
  first.

- **The "it's about the infinite" reading changes nothing — and here is the
  sharpest form.** Conceded: `L ∈ P` is infinitary (`Σ⁰₂`:
  `∃ machine, ∃ poly, ∀ inputs …`), and FOL does have nonstandard models where
  unbounded arithmetic can wobble. Two responses, the second decisive. (i) *Your
  transfer needs standard `ω`.* Absoluteness only moves a `Π⁰₂` truth out of an
  **`ω`-model**, and Kopperman's standard reals supply exactly that — in which
  case every individual `L ∈ P` (SAT included) is the **standard** infinitary
  fact, fixed by SAT's real combinatorics, the prior playing no part. (Give up
  standard `ω` and the transfer dies instead.) (ii) *An atomless prior is, by
  construction, blind to every individual function.* `μ` atomless ⇒ `μ({f}) = 0`
  for **every** singleton, so `μ({SAT}) = 0` whether or not `SAT ∈ P`. But
  `SAT ∈ P` is a property of the *single* function SAT. Measure carries
  information only about positive-measure ("fat") sets; individual `P`-membership
  lives at the level of singletons, where an atomless measure is identically `0`.
  Hence **no atomless-prior statement can ever determine an individual language's
  `P`-membership** — `σ` (the class is null) and `SAT ∈ P` are fully compatible,
  because the null class *contains* SAT. That is the exact form `null ≠ empty`
  takes for the infinitary reading: the measure says the *class* is small; it
  says nothing about the *one function* the question is about.

- **The "original (continuous) functions" are not the arena — `SAT` is, and it
  is concrete, not "formal."** Splitting the world into real "original" functions
  (continuous selections `g : K → ℝ`, where the prior lives) versus
  "ZFC-functions that do not really exist" mislocates the question. `P vs NP` is
  **not about continuous selection functions** at all; it is about **languages**
  `L ⊆ {0,1}*` (decision problems on finite strings) and Turing machines. `SAT`
  is a language of finite strings — a decidable set, i.e. an algorithm — and a TM
  is a finite tuple. These are **finite, concrete combinatorial objects**, as
  real as the integers; they cannot be relegated to a "non-existent formal
  layer." So the prior's verdict on the continuous "original" functions ("null /
  not in `P`") is *compatible with `P vs NP`* only because it is **silent on it**:
  `SAT` is simply not among those functions. Conversely, *encoding* `SAT` into the
  Hilbert space (the tutorial maps syntax to basis vectors) makes it a single
  vector, on which the atomless prior is `0` — singleton-blind again. Either way
  the measure never reaches `SAT`. And `P vs NP` "avoiding most of ZFC" (being
  arithmetical, needing only PA) does **not** open room — it *fixes* the
  statement's meaning at the level of finite combinatorics / standard `ω`,
  *independent* of the Kopperman / ZFC-set / second-order superstructure, which
  is therefore disqualified from being what proves it.

That category difference — not the existence of other models, not the choice of
prior, not the logic — is the reason. It is exactly what `T5` records inside `M`.

### The honest, sound way to "invoke Shoenfield"

Absoluteness *can* be recorded — but as a remark that **reinforces** the tiers,
not one that collapses them: *"Because `P ≠ NP` is arithmetical (`Π⁰₂`), its
truth value is model-independent; consequently no model-relative or
measure-relative construction — including this prior — can establish it without
establishing the arithmetic sentence itself, which `model_vs_clay_disjointness`
shows the model's data does not."* That is a correct use of the theorem and is
already the moral of Part −1 and T5. If desired it can go in the `Main.lean`
module docstring (prose, no `Prop`, no `axiom`). That is the whole of what
Phase 5 can soundly contribute.

**Standing instruction:** do not add `IsStandardModel`, `physical_prior`-as-model,
`shoenfield_absoluteness`, `absolute_P_ne_NP`, `P_ne_NP_Pi20`, or any
`model_… → P ≠ NP` implication **as an `axiom`**. If the maintainer wants to
pursue the genuine logic, that is a separate research project (formalizing
forcing / Boolean-valued models / Shoenfield in Lean) and it would, by (b), still
not shorten a proof of `P ≠ NP`. The *theorem*-form bridge may be stated and
attempted — see Part 9.

---

## Part 9: The Kopperman formalism — FORMALIZED (`PnpProof/Kopperman.lean`), and how to test the bridge

Per the maintainer's request (2026-06-14): the Kopperman formalism is no longer
discussed only in prose — it is **defined in Lean and machine-checked**. The
module `PnpProof/Kopperman.lean` builds `sorry`-free and **axiom-free** (only
`propext`/`Classical.choice`/`Quot.sound`; verified by `#print axioms`), and is
wired into `PnpProof.lean`. It assembles the formalism of
`Kopperman_Tutorial.p.tex` (Kopperman 1967, the `L_{ω₁,ω₁}`-theory of Hilbert
spaces) from the already-proved development:

| Component of the formalism | Lean (in `namespace PnpProof.Kopperman`) | Provenance |
|---|---|---|
| abstract data of a Kopperman formalism | `structure Formalism` (separable `H`, countable dense skeleton, atomless prior) | new packaging |
| substrate = standard separable Hilbert space | `Substrate := Lp ℝ 2 unitMeasure`; `substrate_separable` | `l2_separable` (H1) |
| decidable dense skeleton (computable approximants) | `substrate_decidable_skeleton` | separability |
| Mehler prior (Gaussian limit of the uniform sphere) | `MehlerPrior := gammaMeasure`; `mehler_isProbability` | `gammaMeasure` (G-series) |
| "lives on the ∞-dim sphere" (Poincaré–Borel) | `mehler_concentrates_on_sphere` | `gaussian_concentration_sphere` (G7) |
| atomless prior on any substrate | `admits_atomless_prior` | `exists_atomless_sphere_measure` (H7) |
| realized atomless prior (the model) | `modelPrior_atomless` | `prior_atomless` (M4) |

So "put the formalism in place, then prove statements about it" is **done**, and
the statements about it are exactly the proved `model_P_ne_NP` /
`model_P_ne_NP_circuit` (the separation `σ`) and `model_vs_clay_disjointness`
(T5). **The `L_{ω₁,ω₁}` *infinitary-logic* object itself is not built**: Mathlib
has no infinitary logic, and it is not needed — the substrate it would pin down is
constructed directly, and `hilbert_classification` (H6) supplies the categoricity
content. Building `L_{ω₁,ω₁}` syntax/semantics is a large separate project; flag,
do not improvise.

### Phases 1–3 (indicator separation) — admissible, model-fenced, largely redundant

These restate proved facts (see Part 8's table: F5/F6/F8, T1/F7, F1/T2, M5/N1,
T3). They may be added as **new theorems beside** the existing ones, Tier-B, with
the mandatory "about this model; NOT the Clay statement; no implication
formalized" docstring, **no new axiom**, **`model_`-prefixed names only**. The
`ContinuousMeasure`/`IsStandardMeasure` typeclasses in the draft should be the
existing `NoAtoms`/atomless predicates. Worth doing only for §6-option-1 narrative
parity; otherwise skip.

### Phases 4–5 (the bridge) — "let Lean decide" means a THEOREM, not an `axiom`

The draft's Phase 4.3 (`prior_is_valid_model : IsStandardModel …`) and Phase 5
(`axiom shoenfield_absoluteness`, then `absolute_P_ne_NP`) cannot be added as
written, and the reason is exactly the maintainer's own principle — *implement it
and let Lean say what is true*:

- **An `axiom` is the one construct that prevents Lean from deciding.** Lean does
  not *check* an axiom; it *accepts it unproved*. Writing `axiom
  shoenfield_absoluteness …` and then `absolute_P_ne_NP := by apply …` does not
  let Lean adjudicate the bridge — it *asserts* it. To genuinely let Lean decide,
  the bridge must be a **`theorem` with a proof Lean verifies**.
- **So state it as a theorem and attempt it.** The honest Lean experiment is:
  ```lean
  -- the bridge, as a CHECKABLE obligation (do NOT axiomatize):
  theorem model_separation_implies_clay
      (hσ : prior {g : C(K, ℝ) | ∃ c, ComputesSelection c g} = 0) :
      P_ne_NP_arith := by
    sorry  -- attempt; do not commit the sorry
  ```
  where `P_ne_NP_arith` is the *genuine* arithmetical statement (quantifying over
  `Nat.Partrec.Code` / Turing machines and run-time bounds on `SAT`), **not** a
  measure-relative restatement. Attempting this is the experiment the maintainer
  asks for. It will not close — and that *is* Lean deciding: there is no term of
  this type derivable from `hσ`. `model_vs_clay_disjointness` (T5) is the proved
  statement of *why* (the hypothesis concerns a different arena; `σ` is blind to
  the individual decidable language `SAT` — Part 8).
- **`prior_is_valid_model : IsStandardModel`** is not a statable theorem (a
  measure is not a transitive ZFC model — Part 8); there is no honest Lean type
  for it. Do not introduce `IsStandardModel`, `IsTrueIn (measure) (arith)`, or
  `IsPi20` as new axiomatic predicates — they would encode the category error.
- **The standing rule is unchanged:** a `theorem`-form bridge may be *stated and
  attempted* (no committed `sorry`, no `axiom`); the `axiom`-form bridge is
  forbidden, because it is the negation of "let Lean decide" and would make a
  currently-consistent, axiom-free development unsound.

The genuinely provable positive theorem this all points at — and the one worth
formalizing next — is the **`Π⁰₂`-invariance / conservativity** statement: that
the truth value of an arithmetical sentence is unchanged across the
`ZFSet`↔Kopperman interpretation and across the choice of `Formalism.prior`. That
makes "no prior, no foundation, moves a first-order arithmetic truth"
machine-checked, and it is fully within reach of `Kopperman.lean` + Mathlib's
`ZFSet`.

---

## Part 10: Specialist task list for the 2026-06-14 Phases

Actionable tasks, in this document's idiom (exact Lean target + verdict +
instructions). Ground rules of Part 7 apply verbatim: **no committed `sorry`, no
new `axiom`, never weaken an existing theorem, `model_`-prefix any model-side
separation, verify Mathlib names before use.** Build with `lake build PnpProof`.

### Phase 4 — Kopperman formalism — **DONE** (`PnpProof/Kopperman.lean`)
Already implemented and checked (Part 9). The extension below is now also done:

- **K-ext (PROVABLE) — DONE.** A concrete witness of `Formalism` on
  `Substrate = Lp ℝ 2 unitMeasure`: `koppermanSubstrate : Formalism Substrate`
  (and `nonempty_formalism_substrate`), built from `exists_atomless_prob_substrate`
  (an atomless prior via `exists_atomless_sphere_measure` = H7) fed through
  `formalismOfPrior`. The orthonormal pair (`substrate_orthonormal_pair`) was
  realized by the `√2`-scaled indicators of `[0,½]` and `(½,1]` — **simpler than the
  planned Legendre `√3·(2x−1)` route**: `inner_indicatorConstLp_indicatorConstLp`
  (orthogonality from disjoint support) + `norm_indicatorConstLp` (unit norm),
  no nontrivial integral. Sorry-free, axiom-free. **This is the existence witness
  for K-model.1** (Part 11): "choosing a measure = choosing a model."

### Phase 1 — Mixed prior + conditioning — **PROVABLE** (assemble existing)
The draft's `IsStandardMeasure`/`ContinuousMeasure`/`Conditioned` should be the
development's existing predicates (`NoAtoms`, atomless), not new typeclasses.

- **T-mix (PROVABLE).**
  ```lean
  theorem mixed_prior_decomposition {α : Type*} [MeasurableSpace α]
      [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] :
      ∃ (μc μd : Measure α), μ = μc + μd ∧ (∀ x, μc {x} = 0) ∧
        μd {x | μ {x} = 0} = 0
  ```
  Route: this is **F5** (atoms countable) + **F6** (continuous ⟂ atomic) + **F8**
  (conditioning on the diffuse part is atomless), already in `Foundations.lean`.
  Wrap them; do not re-prove. The conditioning-on-constant-`y` content is **T1**
  `selection_not_history` (already proved) — reuse, do not restate.

### Phase 2 — Indicator decision problem — **PROVABLE** (mirror M5/N1)
- **defn + T-ind-NP (PROVABLE).**
  ```lean
  def indicatorDecide (y u : ℕ) : Bool := decide (u = y)
  theorem indicatorDecide_computable :
      Computable (fun p : ℕ × ℕ => indicatorDecide p.1 p.2)
  ```
  Route: identical shape to `verifyBits_computable` (`Main.lean`); `decide`-based
  equality is computable. The circuit-form (`O(k)` comparator) reuses
  `Comparator.lean` exactly as `model_P_ne_NP_circuit` does. Keep on `ℕ`
  (deviation 4); the `ℝ→ℝ`/`ℚ` framing of the draft is the model picture, realized
  on `ℕ` data here.

### Phase 3 — Measure-zero separation — **PROVABLE**, model-fenced
- **T-const-null (PROVABLE).** "constant-output functions are prior-null":
  ```lean
  theorem model_constant_output_null (y : ℝ) :
      prior {g : C(K, ℝ) | ∀ x : K, g x = y} = 0
  ```
  Route: this set is a subset of a single fibre of the injective `selMap`; it is
  either empty or a singleton in the range, and `prior_atomless` (M4) kills
  singletons; `measure_mono_null`. (If nonempty it is `{selMap t}` for the unique
  `t` — use `selMap_injective`.)
- **T-ind-sep (PROVABLE), `model_`-prefixed, mandatory docstring.**
  ```lean
  theorem model_indicator_separation (y : ℝ) :
      Computable (fun p : ℕ × ℕ => indicatorDecide p.1 p.2) ∧
      prior {g : C(K, ℝ) | ∃ c, ComputesSelection c g} = 0
  ```
  Route: `⟨indicatorDecide_computable, almost_all_not_computable⟩` — i.e. **T3
  with the indicator verifier**. Docstring **must** carry the standard honesty
  text ("about this model; NOT the Clay statement; no implication formalized").

### Phase 5 — The bridge — **EXPERIMENT only; `axiom` form FORBIDDEN**
This is the Tier-C bridge. Per **Part 6** the Clay classes are *not* defined here,
and per **Part 8** the implication is unsound; per Part 9, *letting Lean decide*
means a theorem, never an axiom.

- **FORBIDDEN (do not add):** `axiom shoenfield_absoluteness`, `absolute_P_ne_NP`,
  `prior_is_valid_model : IsStandardModel …`, and the predicates
  `IsStandardModel`, `IsTrueIn (measure) (sentence)`, `IsPi20`. Each either encodes
  the category error (a measure is not a transitive ZFC model) or asserts the
  conclusion unproved. Adding any makes the development non-axiom-free and, given
  T5, unsound.
- **The only Clay-facing statement permitted remains T5**
  (`model_vs_clay_disjointness`), already done.
- **If — and only if — the maintainer supplies a faithful arithmetical
  `P_ne_NP_arith`** (a real definition over `Nat.Partrec.Code` + run-time bounds
  on a fixed `NP`-complete language; itself a large task, and note Part 6's
  caution against defining the Clay classes), the bridge may be **stated as a
  theorem and attempted**:
  ```lean
  theorem model_separation_implies_clay
      (hσ : prior {g : C(K, ℝ) | ∃ c, ComputesSelection c g} = 0) :
      P_ne_NP_arith := by
    sorry   -- ATTEMPT ONLY; do not commit. Report non-closure.
  ```
  Expected outcome: **no closing term exists** — `hσ` constrains a measure on
  `C(K,ℝ)`, while `P_ne_NP_arith` constrains run-times of machines on a single
  decidable language; T5 is the proof of their disjointness. Report the
  non-closure (that is Lean deciding); do **not** rescue it with an axiom.

### Recommended positive next target (PROVABLE, genuinely new)
- **T-conserv.** `Π⁰₂`-invariance: for an arithmetical `φ : Prop` decided by `ℕ`,
  its truth is independent of any `F : Formalism H` and of the `ZFSet`↔Kopperman
  side. Formalize "no prior / no foundation moves an arithmetic truth" as a
  checked theorem. Within reach of `Kopperman.lean` + `Mathlib.SetTheory.ZFC`.
  This is the honest, machine-checkable core the whole proposal points at.
  **It is also step (c) of the foundational-minimization directive — see Part 11.**

---

## Part 11: The definitional base of the P-vs-NP statement (the Kopperman formalism's own commitments — PA-incomparable, co-consistent with PA and ZFC)

**Maintainer directive (2026-06-14 #2, as refined).** The minimal assumptions
needed to *define* the P-vs-NP statement within the Kopperman formalism are
exactly the commitments of the **Kopperman formalism itself** — *not* PA, and *not*
a weakening toward PA. That base is **incomparable** with PA and is **co-consistent**
with both PA and ZFC; because of co-consistency and the standardness of the
formalism's naturals, the statement defined inside it **is** the standard P-vs-NP
statement. This Part is the disposition; it is the recommended forward direction
(queue item **F-min**, Part 7). It **supersedes** the first draft's "reduce to
PA-or-weaker" framing, which answered the wrong question (provability base, not
definability base).

### The crucial distinction: definability base vs. provability base

"Minimal assumptions to **define** the statement" ≠ "minimal assumptions to
**prove** it." The directive is about the first. To *write the statement down* you
need exactly the apparatus that lets you express "a computation," "a verifier,"
and "a selection" — and the Kopperman formalism *is* that apparatus (its countable
decidable skeleton is the encoding of computation; the substrate and prior carry
the model's selection picture). You do **not** need PA's induction schema as a
primitive, and you do **not** need full ZFC. The earlier draft's reverse-math /
"conservative over PA" discussion is about *provability* and is therefore beside
this point; it is retained below only as the reason co-consistency holds.

### Why this is sound and not a backdoor (read first)

Four facts, none of which is improvised:

1. **"P ≠ NP" is a `Π⁰₂` arithmetical sentence.** Phrased over an NP-complete
   language (`SAT`): `∀ M ∀ c ∃ x . (M run for ≤ |x|^c + c steps disagrees with
   SAT(x))`, with a *decidable* matrix (bounded simulation + a decidable `SAT`
   check). It quantifies only over machine codes, constants, and inputs — all
   natural numbers. **No reals, no measures, no uncountable sets, no powerset.**
   The formalism's decidable skeleton supplies exactly the encoding of computation
   the sentence needs. (This matches the document's existing `P_ne_NP_Pi20` name.)
2. **The definitional minimum is the Kopperman formalism's own base** — separable
   substrate + countable decidable skeleton + atomless prior (the `structure
   Formalism` of `Kopperman.lean`). That is the least you need to even *state* the
   model's P-vs-NP picture. ZFC's extra strength (uncountable objects,
   `Classical.choice`-backed measure theory) is *expressive richness used to build
   the formalism*, not part of the statement's commitments; and **T5**
   (`model_vs_clay_disjointness`) shows that richness does *not* decide the
   arithmetic sentence.
3. **This base is incomparable with PA but co-consistent with PA and ZFC.** It does
   **not contain** PA — its language is the Hilbert substrate + skeleton + measure,
   and it does not assert arithmetic induction over its own primitives. PA does
   **not contain** it — PA cannot even express a Hilbert space or a measure. Yet
   all three are jointly realizable: inside ZFC (with the standard `ℕ` and `L²`)
   there is a single structure satisfying the Kopperman axioms while PA holds of
   `ℕ`. So they are mutually consistent while neither proves the other — exactly the
   maintainer's "different from PA, neither contains nor is contained in PA, yet
   consistent with ZFC and PA." The reverse-math conservativity results (`ACA₀`
   arithmetically conservative over `PA`; `WKL₀` `Π¹₁`-conservative over `PA`,
   Friedman; `RCA₀` over `IΣ₁`) are the standard witnesses that adding the analytic
   layer adds **no** arithmetic theorems — i.e. the layer is conservative, hence
   co-consistent, over the arithmetic base.
4. **Hence the Kopperman-defined statement IS the standard P-vs-NP statement
   (absoluteness via standard `ℕ`).** A `Π⁰₂` arithmetical sentence has the same
   meaning and truth value in any structure whose naturals are the *standard* `ℕ`.
   The formalism's skeleton is indexed by the genuine standard naturals, so the
   sentence it defines is absolute — identical to the standard statement, not a
   model-relative surrogate. **In Lean this is automatic**: Lean's `ℕ` has no
   nonstandard elements, so a sentence over `Nat.Partrec.Code` / `ℕ` literally *is*
   the standard sentence, and `T-conserv` (its truth is independent of the chosen
   `Formalism`) is the machine-checkable witness of that identity.

**This identity is not a backdoor to the bridge.** Defining the *standard* sentence
inside the formalism makes the *statement* canonical; it does not make the model
separation *prove* it. T5 is untouched: the formalism suffices to *state* P ≠ NP
and to *carry* the model facts, but the separation still does not imply the Clay
statement.

### What lands in Lean (PROVABLE / mechanical — three concrete steps)

Lean has no built-in theory-comparison or provability predicate, so "the base is
PA-incomparable but co-consistent, and the defined sentence is the standard one"
is realized by its honest, *available* proxies — **import tier + axiom footprint +
conservativity** — not by an internal meta-logical claim:

- **(a) Import-tier separation — the incomparability/independence witness.**
  Confirm (and, for any new `P_ne_NP_arith`, *ensure*) that the arithmetic
  statement lives in a module importing only the computability/finite-combinatorics
  slice of Mathlib (`Nat.Partrec.Code`, `Computable`, `Fintype` counting) and
  **neither the measure theory nor `Kopperman.lean`/`Formalism`**. This is the
  literal, machine-checkable rendering of "the arithmetic base and the Kopperman
  base are independent — neither's definitions require the other's." (The
  measure-heavy `Foundations`/`SphereGaussian`/`Model`/`Kopperman` modules stay put;
  the point is the arithmetic tier does not depend on them, and they do not depend
  on it as primitives either — that is the "incomparable" relation made concrete in
  the import DAG.)

- **(b) Axiom-footprint audit (`#print axioms`) — the dependency proxy.** For each
  load-bearing *arithmetic-tier* result, record which of Lean's axioms it actually
  uses. Target results — already in the development and already pure arithmetic /
  finite combinatorics:
  - **C1** `countable_computable` (codes are countable),
  - **C5** `shannon_fraction` (the counting lower bound — finite combinatorics),
  - **N1** `verify_circuit_cheap` / `model_P_ne_NP_circuit` (the explicit `O(k)`
    comparator — finite, decidable),
  - any future `P_ne_NP_arith` statement.
  *Document* the footprint (ideally `propext`/`Quot.sound` only; flag every
  `Classical.choice` use) in `IMPLEMENTED.md`. This shows the arithmetic content
  does **not** route through the formalism's `Classical.choice`-backed measure
  layer — the dependency-level confirmation that the statement's commitments are not
  ZFC's. It is **not** a provability claim and **not** a claim that the base "is"
  PA (it is incomparable with PA). An audit, not a refactor: **do not** rewrite
  proofs to shed choice unless trivial and still closing; record what is there.

- **(c) `T-conserv` (genuinely new theorem) — the co-consistency + standard-`ℕ`
  identity witness.** As specified in Part 9/10: for an arithmetical `φ : Prop`
  decided by `ℕ`, its truth is invariant under any `F : Formalism H` and across the
  `ZFSet`↔Kopperman interpretation. Provable because `φ` syntactically does not
  mention `F` — the statement is essentially `(φ ↔ φ)` made non-trivial by
  quantifying the irrelevant `Formalism`/foundation parameter and showing it drops
  out. This is the checked core of "the Kopperman base is co-consistent with the
  arithmetic base and, over the *standard* `ℕ`, defines the *same* arithmetic
  sentence" — no prior, no foundation moves an arithmetic truth. (Lean's `ℕ` has no
  nonstandard elements, so the standardness condition behind the identity is free.)
  Within reach of `Kopperman.lean` + `Mathlib.SetTheory.ZFC`.

### K-model: "choosing a measure = choosing a model of the formalism" — IMPLEMENTED (`PnpProof/Kopperman.lean`); deep form out of scope

**Status (2026-06-14):** K-model.0 and K-model.1 (incl. K-ext) are **implemented,
sorry-free and axiom-free** in `PnpProof/Kopperman.lean` (`#print axioms` = the
standard three). Lemma names: `model_has_prior`, `substrate_orthonormal_pair`,
`exists_atomless_prob_substrate`, `formalismOfPrior`, `prior_formalismOfPrior`,
`prior_surjective_onto_atomless`, `nonempty_formalism_substrate`,
`koppermanSubstrate`. K-model.2 remains out of scope (von Neumann/MASA).

**Maintainer claim (2026-06-14 #3):** within the Koopman/Kopperman formalism,
*choosing a probability measure is choosing a model* — equivalently, *every model
of the formalism carries (requires) a probability measure*. **Correct, and it is
the defensible reading**, sharply distinct from the **rejected** Part 8 claim:
there "model" wrongly meant *a transitive model of ZFC* (category error — a measure
is an object *in* ZFC, not a model *of* it); here "model" means *a model of the
formalism as a structure* — an inhabitant of `structure Formalism` — whose `prior`
is literally one of its fields.

**It gives no Clay leverage — for an *arithmetic*, not a foundational, reason
(maintainer correction, 2026-06-14 #4).** The earlier wording ("a model of the
formalism is not a model of set theory") was beside the point and is **withdrawn**:
we agreed P vs NP is `Π⁰₂` arithmetical and needs *neither ZFC nor PA* to state, so
nobody needs a model *of set theory* — only a model of whatever P vs NP minimally
requires, which the formalism (standard `ℕ` skeleton) supplies. The real obstruction
is arithmetic: what the measure establishes is the separation `σ` (computable
selections are prior-null), and `σ` is a *different arithmetic sentence* from
"SAT ∉ P". `σ` says a *generic/random* selection is uncomputable (a Shannon-style
counting fact); the Clay statement is the hardness of the *specific* language SAT.
**T5** (`model_vs_clay_disjointness`) proves the two are disjoint — `σ` is blind to
any individual decidable language. **T5 stands** (see Fences).

**The formalism's two computational layers (maintainer note, 2026-06-14 #5).** The
formalism is *not* "anti-computable", and the prior nulling computable selections is
only half of it. There are two layers, and `model_P_ne_NP` (T3) is their
coexistence:
- **P-side (uncomputable witness).** The atomless prior gives measure zero to
  machine-computable *selection* functions — `almost_all_not_computable` (T2). The
  selected ("hard") object is, prior-almost-surely, not computable.
- **NP-side (computable verification + computable approximations).** The formalism
  *defines computable NP functions*: the candidate *verification* is computable
  (`verifyBits_computable`, M5) and indeed an explicit `O(k)` Boolean comparator
  circuit (`model_P_ne_NP_circuit`, N1); the **decidable dense skeleton** is the
  layer of *computable approximations*, and the dyadic discretization gives
  *computable probabilities*. This is faithful to `pnp.tex`: §6 option 1 — "there is
  no function in `P` corresponding to the indicator function for `y`, which is in
  `NP`"; §10 — "verification of a candidate output is a computable (cheap)
  operation, while no deterministic machine computes the selected function"; §"we
  start by noticing" — the domain "can be defined by a dense countable basis" of a
  Hilbert space (the computable approximants). Without this layer there is **no NP
  side** to separate from P.

**Fidelity gap to fix or accept.** In `Kopperman.lean` the `Formalism.skeleton`
field currently asserts only `Countable ∧ Dense` — it does **not** itself assert
that the skeleton is *computable/decidable*. The computability of the NP layer is
carried by the *separate* `Computable`/circuit theorems (`verifyBits_computable`,
`model_P_ne_NP_circuit`, in `Main.lean`/`Comparator.lean`), and by the dyadic index
machinery — not by a field of the `Formalism` structure. Two honest options, on the
maintainer's call:
1. **Accept and document** (current state): the structure names the skeleton
   "decidable dense" in prose; its computability is realized and proved *elsewhere*
   in the development. Cheapest; nothing to build.
2. **Strengthen the structure** (enhancement, PROVABLE but real work): add a
   `skeleton_decidable`/computable-enumeration field to `Formalism` (or a companion
   structure), witnessed by the **rational step functions / rational polynomials**
   (the paper's integer coding; H4's `ratStep` content — countable, dense, and
   computably enumerable), and optionally a computable-verifier field tying
   `verifyBits_computable` into the formalism. Caveats: `Main.lean` (verifier) and
   `Kopperman.lean` are currently *parallel leaves* (neither imports the other), so
   a verifier field needs an import restructure or a new top file; and a genuinely
   *computable* dense enumeration of the substrate must be built (H4 was subsumed,
   deviation 2, not exposed as a standalone computable enumerator). Flag, do not
   force; attempt only on maintainer request.

*(Naming: the Lean file/structure is `Kopperman` after Kopperman 1967's
`L_{ω₁,ω₁}`-theory of Hilbert spaces; the maintainer's "Koopman" also evokes the
Koopman–von Neumann formulation of mechanics on `L²(phase space, μ)`. The same
`Formalism` object serves both, and — fittingly — the KvN "Hilbert space built from
a base measure" reading is exactly what makes K-model.2 below the deep version.)*

Three tiers, by increasing depth:

- **K-model.0 (trivial — projection) — DONE.** Every model carries an atomless
  probability measure, as `model_has_prior`:
  ```lean
  theorem model_has_prior {H} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H] [MeasurableSpace H] (F : Formalism H) :
      IsProbabilityMeasure F.prior ∧ ∀ x, F.prior {x} = 0 :=
    ⟨F.prior_isProb, F.prior_atomless⟩
  ```
  True by definition (`prior` is a field) — the literal "every model *has* a
  measure," by-construction, not deep.

- **K-model.1 (the genuine content — existence + correspondence) — DONE.** What
  makes "choosing the measure is a *real, required* choice" non-vacuous:
  * **existence (K-ext)** — the substrate admits a model:
    `nonempty_formalism_substrate`/`koppermanSubstrate : Formalism Substrate`. The
    orthonormal pair was realized **not** by the Legendre `√3·(2x−1)` route but by
    the `√2`-scaled indicators of the two halves `[0,½]`, `(½,1]`
    (`substrate_orthonormal_pair`) — no nontrivial integral, just
    `inner_indicatorConstLp_indicatorConstLp` + `norm_indicatorConstLp` — fed to
    `exists_atomless_sphere_measure` (H7) as `exists_atomless_prob_substrate`. The
    substrate carries its Borel σ-algebra (`local instance … := borel _`).
  * **correspondence** — `formalismOfPrior : (μ atomless prob) → Formalism Substrate`
    is the "measure ↦ model" map, with `prior_formalismOfPrior : (…).prior = μ`
    (`rfl`) its section, packaged as `prior_surjective_onto_atomless` (every
    atomless probability measure is *some* model's prior). With substrate + the
    canonical (chosen) skeleton fixed, `F ↦ F.prior` is thereby a bijection onto the
    atomless probability measures — the precise "choosing a measure = choosing a
    model."
  * **non-uniqueness** (optional, NOT done) — exhibiting ≥ 2 *provably distinct*
    atomless priors would reduce the bijection-content from "surjective with a
    section" to a literal `Equiv`; it needs a measure-distinctness lemma and was
    left out (the surjection already carries the "the choice is free" content). Add
    only if a clean distinguishing set is available.

- **K-model.2 (the deep reading — measure *forced* without baking it in) — OUT OF
  SCOPE.** The strongest "every model requires a measure" *drops* the `prior` field
  and *derives* a measure from the abstract data. By **H6**
  (`hilbert_classification`) all separable Hilbert substrates are isomorphic, so the
  measure is **not** recoverable from the Hilbert space alone — it is the invariant
  of a *maximal abelian von Neumann subalgebra* (the "observables/position"
  algebra), which by the spectral multiplicity theorem is unitarily
  `L^∞(X, μ)`-multiplication, with the measure class the complete invariant. This is
  exactly the **von Neumann algebra classification marked OUT OF SCOPE in Part −1,
  §5** ("huge, unused"). It is the genuinely non-tautological "model ⟺ measure," but
  it is a large project and **Mathlib lacks MASA/multiplicity theory** — **flag, do
  not improvise.** Attempt only on an explicit maintainer decision to take on the
  von Neumann classification.

### Fences (do NOT improvise — honesty rules)

- **No internal "PA-incomparable / co-consistent" or `PA ⊢ P_ne_NP` theorem.**
  Stating *as a Lean theorem* that the Kopperman base is incomparable with PA, or
  that the sentence is provable/consistent in any named theory, requires formalized
  first-order theories and interpretations (`FirstOrder.Language`, a provability
  predicate, a soundness/representation bridge). Mainline Mathlib has no such
  apparatus; the `FormalizedFormalLogic`/`Foundation` development is separate.
  Building it is a large meta-logic effort on the scale of the `L_{ω₁,ω₁}` object —
  **flag, do not improvise.** The import DAG / `#print axioms` / `T-conserv` are
  *proxies* for these meta-claims, not internal proofs of them; say so wherever
  reported.
- **No new axioms**, and the identity is **not** a route to the bridge: defining the
  *standard* sentence inside the formalism does not make the model separation prove
  it. T5 stands; the only Clay-facing theorem remains T5.
- **K-model gives no Clay leverage — an *arithmetic*, not foundational, obstruction.**
  Do **not** justify this with "a measure is not a model of set theory" (true but
  beside the point: P vs NP needs no set-theory model — maintainer correction
  #4). The correct reason: what the measure proves is the separation `σ`, a
  *different arithmetic sentence* from "SAT ∉ P" — `σ` is random/Shannon-style
  hardness, the Clay statement is specific-language (SAT) hardness, and **T5**
  proves them disjoint (`σ` is blind to any individual decidable language). Do not
  chain K-model into any `σ → (P ≠ NP)` argument; that resurrects the rejected
  bridge. *(Part 8b's "measure ≠ ZF-model" point still correctly rebuts the
  Shoenfield-invoking proposal there — that argument explicitly needed ZF models;
  K-model does not, so it must not lean on that rebuttal.)*
- **Do not weaken existing theorems** to chase a smaller footprint. If a choice-free
  reproof of C1/C5/N1 does not close cleanly, leave the existing proof and just
  record the footprint. Upgrades are new lemmas beside the old ones (Part 7).
- **Do not re-import the discarded "reduce to PA" goal.** PA is *not* the target
  base; it is one of the two incomparable theories the formalism is co-consistent
  with. The bounded-arithmetic remark (`IΔ₀+exp`/`S¹₂`) is only a note on where the
  *sentence* naturally lives; formalizing provability in any such theory is the same
  separate meta-logic project — flag, do not start it under this directive.
