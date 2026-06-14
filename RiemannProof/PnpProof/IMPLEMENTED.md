# PnpProof — Implementation report

Formalization of the mathematical content of `pnp.tex`, following
`PNP_IMPLEMENTATION_PLAN.md`. All listed results compile **sorry-free** and
depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

The development lives in the `PnpProof` Lean library (added to the existing
lake project alongside `RiemannProof`). Build everything with
`lake exe cache get && lake build PnpProof` (never skip the cache step —
otherwise Mathlib compiles from source).

**Build independently verified 2026-06-12** (toolchain
`leanprover/lean4:v4.28.0`, Mathlib pin `v4.28.0`): `lake build PnpProof`
succeeds (8034 jobs, including `Comparator.lean` and the T5 theorems); a
`grep` over the sources confirms no `sorry` and no `axiom` declarations. The
only diagnostics are style-linter warnings (`linter.style.multiGoal`,
`linter.style.whitespace`, `linter.style.longLine`).

## Files and contents

### `PnpProof/Foundations.lean` — Part 1 (measure theory)

| Item | Name | Status |
|------|------|--------|
| Part 0 | `unitMeasure`, `squareMeasure`, their `IsProbabilityMeasure` instances | ✓ |
| F1 | `null_singleton_volume`, `null_singleton` | ✓ |
| F2 | `countable_null` | ✓ |
| F3 | `selection_exists` (disintegration) | ✓ |
| F4 | `no_history` | ✓ |
| F5 | `countable_atoms` | ✓ |
| F6 | `atomless_mutuallySingular_atomic` | ✓ |
| F7 | `cdf_jump_separation` | ✓ |
| F8 | `cond_diffuse_noAtoms` | ✓ |

### `PnpProof/Counting.lean` — Part 2 (computability and counting)

| Item | Name | Status |
|------|------|--------|
| C1 | `countable_computable`, `countable_computable_bool` | ✓ |
| C3 | `Gate`, `Circuit`, `Circuit.nodeValNat`, `Circuit.eval`, `computableBySize`, `computableBySize_mono` (+ `Circuit.nodeValNat_agree`) | ✓ |
| C4 | `card_gate`, `card_circuit_le` | ✓ |
| C5 | `card_computableBySize_le`, `shannon_fraction` (+ helpers `shannon_aux_base`, `shannon_aux_exp`, `card_computableBySize_le_card_circuit`) | ✓ |
| C2 | `binDigit`, `floor_two_mul`, `floor_succ`, `floor_eq_of_digits_eq`, `binDigit_injOn`, `null_computable_digits` | ✓ |

Deviation: the Shannon bounds are stated for `8 ≤ n` (as the plan permits),
which keeps the ℕ-division arithmetic clean.

### `PnpProof/FunctionSpace.lean` — Part 3 (function space)

| Item | Name | Status |
|------|------|--------|
| H1 | `l2_separable` | ✓ |
| H2 | `linf_not_separable` | ✓ |
| H3 | `sqrt_density_memLp`, `sqrt_density_norm` | ✓ |
| H5 | `polynomial_dense_L2` | ✓ |
| H6 | `hilbert_classification` (+ `countable_of_separated`, `exists_l2_iso`) | ✓ |
| H7 | `exists_atomless_sphere_measure` | ✓ |

Deviation: H4's elaborate `ratStep` family is not built separately; its
essential content (a countable dense subset of `L²`) is subsumed by H1
(separability) and the polynomial density of H5.

### `PnpProof/SphereGaussian.lean` — Part 3b (uniform sphere ↔ Gaussian limit)

| Item | Name | Status |
|------|------|--------|
| G0 | `physHermite` (+ `physHermite_succ_succ`) | ✓ |
| G1 | `gegenbauer`, `gegenbauer_two`, `gegenbauer_rec` | ✓ |
| G2 | `gegenbauerScaled`, `gegenbauerScaled_tendsto_hermite` (lopez99 eq. 1.4) | ✓ |
| G3 | `weight_tendsto_gaussian` | ✓ |
| G4 | `gegenbauerScaled_rec`, `gegenbauerScaled_bound`, `normalization_tendsto`; `physHermite_hasDerivAt`, `hermite_sq_integral`, `hermite_normalization` | ✓ |
| G5 | `gaussianE`, `sphereProj`, `sphereUniform`, `sphereUniform_isProbability`, `sphereUniform_sphere`, `sphereProj_equivariant`, `gaussianE_rotation_invariant`, `sphereUniform_rotation_invariant` (+ `gaussianE_isProbability`, `sphereProj_measurable`) | ✓ |
| G6/G7 | `gammaMeasure`, `normSq`, `gaussian_concentration_sphere` (G7, SLLN), `poincare_borel_ae` (G6) | ✓ |

The G2 limit is proved by the mandated recurrence-induction route (no
asymptotics). G4's `normalization_tendsto` is stated in the post-change-of-
variables form (the `x_old = x/√λ` substitution is baked into the `[-√λ, √λ]`
interval and the `gegenbauerScaled`/weight integrand), as permitted by the plan;
it is proved by dominated convergence with the uniform polynomial bound
`gegenbauerScaled_bound`. `hermite_normalization` (value `√π·2ⁿ/n!`) is proved
by an integration-by-parts induction (`hermite_sq_integral`). G6/G7 are realized
on the single probability space `gammaMeasure` (the infinite product of standard
Gaussians) via `Measure.infinitePi` and `ProbabilityTheory.strong_law_ae`; the
finite-`k` Chebyshev fallback G7′ and the bounded-continuous weak-convergence
corollary `poincare_borel` were not needed once the a.s. forms were available
and are left unformalized.

### `PnpProof/Model.lean` — Part 4 (the model)

| Item | Name | Status |
|------|------|--------|
| M1 | `dyadic`, `dyadicIndex`, `dyadic_disjoint`, `mem_dyadic_index`, `dyadic_width` | ✓ |
| M2 | `verify`, `verify_exists` | ✓ |
| M3 | `ComputesSelection`, `computesSelection_unique`, `countable_computable_selections` | ✓ |
| M4 | `select`, `selMap`, `prior`, `selMap_continuous`, `selMap_injective`, `prior_isProbability`, `prior_atomless` | ✓ |

Representation choice: selection functions are elements of `C(↥[0,1], ℝ)`, and
`ComputesSelection` is stated directly on them (no separate `extend`). The
prior is the pushforward of the uniform measure on `↥[0,1]` under `selMap`.

### `PnpProof/Main.lean` — Part 5 (main theorems)

| Item | Name | Status |
|------|------|--------|
| T1 | `selection_not_history` | ✓ |
| T2 | `almost_all_not_computable` | ✓ |
| M5 | `verifyBits`, `verifyBits_computable` | ✓ |
| T3 | `model_P_ne_NP` | ✓ |
| glue | `mixed_to_continuous` | ✓ |
| N1 | `model_P_ne_NP_circuit` (circuit form of T3's NP side) | ✓ |
| T5 | `DecidesSelection`, `dense_selection_domain`, `decidesSelection_unique`, `countable_language_decided_selections`, `selection_not_language_decidable`, `model_vs_clay_disjointness` | ✓ |
| T4 | `realistic_version` | documented OPEN (no theorem committed) |

T5 (`model_vs_clay_disjointness`, plan §T5) makes the Tier-C *relationship*
checkable without defining the Clay classes: for any collection `NP` of
languages (`ℕ → Bool`) all of whose members are computable — as is every
faithful formalization of the Clay classes, since `NP ⊆ EXPTIME` —
prior-almost-surely no member decides the selected function's dyadic data
(`DecidesSelection`). Proof: a language decides at most one selection
(`decidesSelection_unique`, via `dense_selection_domain` and
`Continuous.ext_on`), the computable languages are countable
(`countable_computable_bool`), hence the decided selections form a countable,
prior-null set. Its docstring carries the mandatory honesty text: it is NOT
the Clay statement, the Clay classes are not defined, and no implication in
either direction is formalized.

### `PnpProof/Comparator.lean` — Part 4 / N1 (the explicit `O(k)` comparator circuit)

| Item | Name | Status |
|------|------|--------|
| append API | `Gate.eval`, `Circuit.snoc`, `nodeValNat_input`, `nodeValNat_gate`, `snoc_nodeValNat_lt`, `snoc_nodeValNat_top`, `clampFin`, `clampFin_val` | ✓ |
| stage | `St`, `step`, `step_s`, `step_eqN`, `step_ltN`, `step_preserves`, `step_eqN_val`, `step_ltN_val` | ✓ |
| fold | `buildLT`, `buildLT_s`, `buildLT_preserves`, `div_pow_succ_compare`, `buildLT_spec` | ✓ |
| base | `Circuit.empty`, `baseSt`, `baseSt_s/eqN/ltN`, `baseSt_eqN_val`, `baseSt_ltN_val` | ✓ |
| assembly | `bitsOf`, `cmp1`, `cmp2`, `cmp1_s`, `cmp2_s`, `cmp1_ltN_val`, `cmp2_ltN_val`, `fullCircuit`, `verify_circuit_cheap` | ✓ |

N1 (the plan's old "N5") is now **complete**. `verify_circuit_cheap` builds, for
every `k ≥ 1`, an explicit big-endian ripple-comparator `Circuit (3*k) (s+1)`
with `s ≤ 50*k + 50` that decides `(glo ≤ u ∧ u ≤ ghi)` on the three `k`-bit
numbers packed by `bitsOf`. The bit recursion `div_pow_succ_compare` (relocated
here from `Main.lean`, no longer duplicated) drives the per-bit `eq`/`lt`
register update `step`, which is folded MSB-first by `buildLT`; `baseSt` seeds
the registers from `TRUE`/`FALSE` constant nodes, and `fullCircuit` chains two
comparators with a final `¬·∧¬·`. `model_P_ne_NP_circuit` (in `Main.lean`)
strengthens the NP side of `model_P_ne_NP` to this circuit family; the original
`model_P_ne_NP` is left untouched. Everything is sorry-free and depends only on
`propext`, `Classical.choice`, `Quot.sound`.

### `PnpProof/Kopperman.lean` — Part 9 (the formalism) + Part 11 (K-model)

| Item | Name | Status |
|------|------|--------|
| formalism data | `structure Formalism`, `Substrate`, `substrate_separable`, `substrate_decidable_skeleton` | ✓ |
| Mehler prior | `MehlerPrior`, `mehler_isProbability`, `mehler_concentrates_on_sphere` | ✓ |
| atomless layer | `admits_atomless_prior`, `modelPrior_atomless` | ✓ |
| K-model.0 | `model_has_prior` (every model carries an atomless probability prior) | ✓ |
| orthonormal pair | `substrate_orthonormal_pair` (`√2`·indicators of `[0,½]`, `(½,1]`) | ✓ |
| existence (K-ext) | `exists_atomless_prob_substrate`, `nonempty_formalism_substrate`, `koppermanSubstrate` | ✓ |
| correspondence | `formalismOfPrior`, `prior_formalismOfPrior`, `prior_surjective_onto_atomless` | ✓ |
| F-min (c) T-conserv | `Pi02`, `interpPi02`, `arith_truth_invariant`, `pi02_invariant_of_formalism`, `interpPi02_eq` | ✓ |

**K-model** ("choosing a measure = choosing a model of the formalism", Part 11):
`model_has_prior` projects every `Formalism` to its atomless prior;
`formalismOfPrior` is the converse "measure ↦ model" map, with
`prior_formalismOfPrior` (`rfl`) its section and `prior_surjective_onto_atomless`
packaging surjectivity onto the atomless probability measures — so with substrate
and a canonical skeleton fixed, `F ↦ F.prior` is a bijection. `koppermanSubstrate`
is a concrete model on `L²([0,1])`, built from `substrate_orthonormal_pair` (the
`√2`-scaled indicators of the two halves, orthonormal via
`inner_indicatorConstLp_indicatorConstLp` + `norm_indicatorConstLp` — no integral)
fed to `exists_atomless_sphere_measure` (H7). Sorry-free, axiom-free (`propext`,
`Classical.choice`, `Quot.sound`). **No Clay leverage:** the obstruction is
arithmetic (the measure proves `σ`, a different sentence from "SAT ∉ P"; T5
disjointness), *not* foundational — no model of set theory is needed, since P vs NP
is `Π⁰₂` arithmetic.

### Deviations on the NP side of T3 (Part 4 M5)

The plan offered an explicit `O(k)` comparator circuit *or* a labelled model
axiom for the verifier cost. Since introducing axioms is not permitted here,
the NP side of `model_P_ne_NP` is formalized as the **computability** of the
verifier predicate (`verifyBits_computable`). This is faithful to §6's claim
that candidate verification is cheap, and is established without any axiom. The
P side (`almost_all_not_computable`) is the stronger information-theoretic
statement: prior-almost-surely the selected function is computed by *no*
deterministic machine.

The plan's N1 upgrade (the explicit `O(k)`-size comparator `Circuit`) is now
**complete** as the NEW theorem `model_P_ne_NP_circuit`, built on
`Comparator.lean`'s `verify_circuit_cheap` (see the table above). As mandated,
the original `model_P_ne_NP` is left untouched; both versions coexist, and the
whole development remains sorry-free and axiom-free.

### Out of scope (Part 6 of the plan, deliberately not formalized)

The Clay bridge, Turing-machine time lower bounds, the von Neumann algebra
classification, the Fock/Guichardet construction, the hyperspherical area
element, and §§8–9. T3 is a theorem **about the model**, not the Clay
statement; no implication to standard `P ≠ NP` is asserted. The only
Clay-facing statement in code is T5 (`model_vs_clay_disjointness`), which
proves the two arenas are *disjoint*.

### F-min — definitional-base witnesses (Part 11, recommended queue item) — DONE

The three honest, machine-checkable proxies for "the definitional base is the
Kopperman formalism's own (incomparable with PA, co-consistent with PA and ZFC),
and over the standard `ℕ` it defines the *standard* P-vs-NP sentence". Per the
Part 11 fences, these are *proxies*; no internal `PA ⊢ …` / theory-comparison /
provability predicate is introduced (Mathlib has no such apparatus).

- **(a) Import-tier separation.** The arithmetic-tier results live in modules
  whose dependency closure does **not** contain `Kopperman.lean` or the
  measure-theory modules (`Foundations.lean`, `Model.lean`, `SphereGaussian.lean`):
  `Counting.lean` imports only `Mathlib`; `Comparator.lean` imports only
  `Mathlib` and `Counting.lean`. So **C1** (`countable_computable`), **C5**
  (`shannon_fraction`), and **N1** (`verify_circuit_cheap`,
  `model_P_ne_NP_circuit`'s circuit core) do not depend on the formalism. This is
  the import-DAG rendering of "the arithmetic base and the Kopperman base are
  independent — neither's definitions require the other's."

- **(b) Axiom-footprint audit (`#print axioms`).** Each load-bearing
  arithmetic-tier result depends only on the standard three axioms
  (`propext`, `Classical.choice`, `Quot.sound`) — none routes through anything
  exotic, and the finite/decidable content does not depend on the
  `Classical.choice`-backed measure layer as a *primitive* (the arithmetic
  modules do not import it at all, per (a)):
  | Result | File | Axioms |
  |--------|------|--------|
  | C1 `countable_computable` | `Counting.lean` | `propext`, `Classical.choice`, `Quot.sound` |
  | C5 `shannon_fraction` | `Counting.lean` | `propext`, `Classical.choice`, `Quot.sound` |
  | N1 `verify_circuit_cheap` | `Comparator.lean` | `propext`, `Classical.choice`, `Quot.sound` |
  | N1 `model_P_ne_NP_circuit` | `Main.lean` | `propext`, `Classical.choice`, `Quot.sound` |
  This is a dependency-level audit, **not** a provability claim and **not** a
  claim that the base "is" PA (it is incomparable with PA). No proof was
  rewritten to shed `Classical.choice`; the footprint is recorded as-is.

- **(c) `T-conserv` (genuinely new theorem).** `arith_truth_invariant`
  (`Kopperman.lean`): for a `Π⁰₂` arithmetical sentence `Pi02 p := ∀ a, ∃ b, p a b`
  over the standard `ℕ`, its truth is invariant under any choice of `Formalism H`
  *and* any `ZFSet` foundation parameter — both drop out
  (`interpPi02 p F z ↔ Pi02 p`, `interpPi02_eq`). It is the checked core of "no
  prior, no foundation moves an arithmetic truth": the parameters genuinely appear
  in the statement and are proved irrelevant. Sorry-free, axiom-free (the standard
  three). It is a proxy for, not an internal proof of, the meta-logical
  co-consistency/standardness claims (Part 11 fences).

## Next steps (queue in `PNP_IMPLEMENTATION_PLAN.md`, Part 7)

All mathematical queue items (N1, T5, **F-min**) are complete. The only open item
is optional style-linter housekeeping (`linter.style.multiGoal`,
`linter.style.whitespace`, `linter.style.longLine`): fix with focus dots /
whitespace / line breaks only, and revert any fix that breaks a proof.
Ground rules: every change lands sorry-free or not at all; **no new axioms,
ever**; never weaken an existing theorem. T4 stays prose-only unless the
maintainer supplies a precise statement plus a complete English proof.
