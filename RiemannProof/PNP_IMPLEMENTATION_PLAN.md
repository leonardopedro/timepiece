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

## Status (2026-06-12, second update): implementation COMPLETE — N1 and T5 included

The development lives in `PnpProof/` as a second library of this lake project
(see deviation 1 below). It compiles **sorry-free and axiom-free** (only Lean's
standard `propext`, `Classical.choice`, `Quot.sound`). Build verified
2026-06-12 (8034 jobs, including `Comparator.lean` and the T5 theorems) — only
style-linter warnings remain (`linter.style.multiGoal`,
`linter.style.whitespace`, `linter.style.longLine`). Always restore the Mathlib
cache before building:

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

### Explicitly NOT on the queue

- **T4** (§7 realistic version): prose-only by deviation 5; needs a
  maintainer-supplied statement + complete English proof first.
- **G7′** (finite-`k` Chebyshev) and the weak-convergence corollary
  `poincare_borel`: superseded by the implemented a.s. forms
  (`gaussian_concentration_sphere`, `poincare_borel_ae`); deviation 7.
- Everything in Part 6 (Clay bridge, TM time bounds, von Neumann
  classification, Fock/Guichardet, area element, §§8–9) — permanently out of
  scope.

**Reporting duty**: unchanged — keep `PnpProof/IMPLEMENTED.md` current
(lemma, file, any deviation). Any queue item that turns out unprovable *as
stated here* gets the RiemannProof treatment: do not force it — restate
minimally, record the diagnosis, and flag it in the report.
