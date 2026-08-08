# Plan for the LLM–Lean 4 Specialist: Proving Remaining `book.tex` / `Book/` Statements

This is an execution plan for an LLM–Lean-4-specialist agent. Its goal is to
prove, in `BookProof/` (the verified, `sorry`-free / `axiom`-free library),
statements that appear in `book.tex` or in the curated `Book/*.lean` chapters but
are **not yet proved**. Every new theorem must remain `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).

## Environment (do not change without coordination)

- Toolchain: `leanprover/lean4:v4.28.0`; Mathlib `v4.28.0` (see `lean-toolchain`).
- Adding `EXTERNAL` named *hypotheses* is allowed by design (never `axiom`). A
  named `EXTERNAL` hypothesis is a genuine, documented gap that the plan lists
  separately; proving it *within* Mathlib upgrades it to a theorem.
- Verify with:
  ```bash
  export PATH="/home/leo/.elan/bin:$PATH"
  cd /home/leo/Projects/timepiece
  lake build BookProof
  grep -rn "sorry" BookProof/           # expect only RandomMap/SchoenfeldPRA.lean:162,176
  grep -rn "^axiom" BookProof/ PnpProof/ # expect empty
  ```
- Register new files in `BookProof.lean`. Do **not** edit `lakefile.toml`
  `[leanOptions]` (the book build is sensitive to `experimental.module` /
  `autoImplicit` / `maxSynthPendingDepth`).
- Do not touch P≠NP / Riemann-Hypothesis work (`PnpProof/`, `RiemannProof/`) —
  out of scope by the author.

## Current state (audit, August 2026)

> **Status refresh (2026-08-08):** most Priority items below are now proved — see
> `PLAN_LEAN_SPECIALIST_COHERENT.md` §Status. In particular `tailSplitEquiv_map`,
> `mehler_unique_by_finite_marginals`, `selecting_events_not_rewriting_history`,
> `exists_continuous_atomic_decomposition`, the finite type-`Iₙ` von Neumann case,
> the concrete Schur/Pauli/unitary/Maschke cases, and the §5 "definability / mixed
> priors / error norms / finite arithmetic prior / kernel transport" items are all
> real theorems.
>
> **Status refresh (same day, Part E wave):** Parts A–E of
> `PLAN_LEAN_SPECIALIST_COHERENT.md` are now **complete** — including the three
> structural layers just landed and synced into `Book/CoherentState.lean`:
>
> - **`ChapterCoherentOverlapComplex`** — the complex Bargmann kernel
>   (`coherentOverlapC`, `coherentBornC_eq_softmax`, `bornWeightC_phase_invariant`,
>   `coherentBornC_cancel_q`), discarding the real-parameter caveat;
> - **`ChapterObservableOperator`** — the observable built as a Hermitian operator
>   `V̂ = Σ vⱼ |kⱼ⟩⟨kⱼ|` (`observableOp_isHermitian`,
>   `observableOp_expectation`, `observableOp_expectation_mem_convexHull`,
>   `observable_expectation_born`), so the attention output is an *expectation
>   value*, not just spectral data;
> - **`ChapterAbelianDiagonalCountable`** — the countable MASA `ℓ∞(ℕ)` on `ℓ²(ℕ)`
>   (`diagOp`, `commutes_diagOp_iff`, `vonNeumann_abelian_class_countable`),
>   upgrading the `ℓ∞(ℕ)` clause of the von Neumann classification from
>   `ChapterAbelianDiagonal`'s finite (`Iₙ`) case;
> - **Maschke consequences** (`avgProj_idempotent`, `avgProj_range_eq_W`,
>   `maschke_decomposition`) and the three structural layers
>   `ChapterCoherentGeometry` ("nearest key wins"), `ChapterSoftmaxOrder`
>   (temperature-independent argmax) and `ChapterAttentionEntropy` (Shannon
>   entropy, its maximal value at `β = 0` and collapse to `0` as `β → ∞`), plus
>   `ChapterCoherentOccupation` (Poisson occupation statistics, `τ` as the energy
>   expectation) and `ChapterSoftmaxSharpness` (flat-versus-sharp dichotomy).
>
> **What remains (documented gaps, *not* a `sorry` backlog):** the physical
> derivation of `τ = n̄ + 1/2` from the quantum fidelity of displaced thermal
> states (`ChapterCoherentTemperature`), and the exhaustiveness of the five-item
> von Neumann list / the `L∞([0,1])` and mixture classes (need von-Neumann-algebra
> machinery not in this toolchain). Both live records are in
> `BookProof/STATUS.md`; neither is `sorry`-ed anywhere.
> This file's historical items remain below for provenance.

- **Actual `sorry`s:** the former real gap
  `BookProof/ChapterSolovayCoordinates.lean:85` (`tailSplitEquiv_map`) is now
  **proved**. The two in `RandomMap/SchoenfeldPRA.lean:162,176` are pre-existing
  and intentional — leave them.
- **`True` placeholders** in `BookProof/ChapterSelectingEvents.lean` — all now
  **replaced by real theorems** (kept here for provenance):
  - `selecting_events_not_rewriting_history` — now proves `μ[F | E] = μ(E∩F)/μ(E)`;
  - `exists_continuous_atomic_decomposition` — now proves a genuine atomic +
    atom-free decomposition;
  - `vonNeumann_abelian_classification_typeI` — replaces the former `True`/`sorry`
    pair with the proved finite type-`Iₙ` case (the old `True` placeholder pair is
    preserved commented out in the file).
- **Named `EXTERNAL` hypotheses** (documented, never `axiom`): Schur's lemma for
  unitary reps (`IsSchurUnitary`, `IsSchurFull`), Weyl complete reducibility
  (`WeylCompleteReducibility`), Wigner/Mackey imprimitivity exhaustiveness,
  Pauli's fundamental theorem of γ-matrices (`PauliFundamental`), Varadarajan Thm 6.12,
  `levy_paths_nowhere_differentiable`, `CrouzeixBound`. These are the deepest open
  inputs; §4 lists which are realistically provable in Mathlib. **Status (2026-08-08):**
  the concrete finite-dimensional cases are proved `EXTERNAL`-free (finite Schur
  `ChapterSchurFullFiniteDim.commutant_eq_scalars_of_irreducible`, the 4×4
  Pauli/Majorana commutant `BookProof.ChapterA3.mgamma_commutant_scalar` /
  `mgamma_irreducible`, unitary complete reducibility
  `ChapterUnitaryCompleteReducibility.unitary_complete_reducibility`, Maschke
  `ChapterMaschkeFiniteGroup.maschke_invariant_complement`); the general deep
  statements remain named hypotheses.

---

## Priority 1 — Close the one real `sorry` (Mehler tail split)

> **Status (2026-08-08): DONE.** `tailSplitEquiv_map` (then at line 85) is now
> proved with no `sorry`; the dependent Solovay structure theorems landed too.
> Kept below for provenance.

File: `BookProof/ChapterSolovayCoordinates.lean`, theorem `tailSplitEquiv_map`
(line 85). This is the only genuine `sorry` in the new code and it is the
load-bearing fact for the Solovay–Kopperman cross-dimensional embedding (the
author's "inner product is well defined across head dimensions" claim).

**Statement.** For `coordinateTailMeasure = Measure.infinitePi (fun _ : ℕ =>
gaussianReal 0 1)` and `gaussianHead k = Measure.pi (fun _ : Fin k =>
gaussianReal 0 1)`, the coordinate splitting
`tailSplitEquiv k : (ℕ → ℝ) ≃ᵐ (Fin k → ℝ) × (ℕ → ℝ)` satisfies
`Measure.map (tailSplitEquiv k) coordinateTailMeasure =
(gaussianHead k).prod coordinateTailMeasure`.

**The proof is already decomposed** in the file; only one subgoal remains open
(`h_split`): that `Measure.infinitePi` on a sum type
`Fin k ⊕ ℕ → ℝ` splits as the product of the two factors. Use:

- `MeasureTheory.Measure.infinitePi` and `Measure.pi` (Mathlib
  `MeasureTheory/Measure/Count.lean` / `Pi.lean`).
- `MeasureTheory.Measure.pi_congrLeft` (already used above the `sorry`).
- The canonical equivalence `(Fin k ⊕ ℕ → ℝ) ≃ (Fin k → ℝ) × (ℕ → ℝ)`
  (`Equiv.sumPiEquivProdPi`), and the fact that `Measure.map` along it turns
  `infinitePi`/`pi` on the sum into the product measure.
- Mathlib `MeasureTheory.Measure.Pi.piFunUnique` / `pi_of_single` helpers if needed.

**Definition of done:** `tailSplitEquiv_map` has no `sorry`; `lake build
BookProof` green; `#print axioms tailSplitEquiv_map` shows only `propext`,
`Classical.choice`, `Quot.sound`.

**Follow-on (same wave, do not stop):** once `tailSplitEquiv_map` closes, land the
three Solovay structure theorems that depend on it (they are currently stated but
may be unproved or partially proved):
- `cross_dim_embedding` (measure-preserving padding of the head from `N` to `M`);
- `inner_cross_dim_well_defined` (independence of the inner product from the
  embedding dimension `M`);
- promote `mehler_invariant_under_finite_orthogonal` from its current
  measure-preserving-interface definition to a concrete coordinate-level statement
  if the substrate model allows it.

---

## Priority 2 — `ChapterSelectingEvents` real conclusions (conditional-probability core)

> **Status (2026-08-08): DONE.** `selecting_events_not_rewriting_history` now
> proves `μ[F | E] = μ(E∩F)/μ(E)`; `exists_continuous_atomic_decomposition` has a
> real continuous+atomic conclusion; `exists_regular_conditional_probability` is
> realized via `compProd`/`condDistrib`; and the finite type-`Iₙ` case
> `vonNeumann_abelian_classification_typeI` replaces the former `True`/`sorry`
> pair. Kept below for provenance.

The chapter's *mathematical* (non-P≠NP) content is the claim that selecting a
positive-measure event does not "rewrite history": the regular conditional
probability agrees with the quotient formula. This is fully in Mathlib and should
not be a `True` placeholder.

File: `BookProof/ChapterSelectingEvents.lean`, theorem
`selecting_events_not_rewriting_history` (line 226).

Replace the `True` conclusion with the real statement: for a probability measure
$`\mu` with $`\mu(E) > 0` and $`\mu(F) \ge 0`,
$$`\mu(F \mid E) = \frac{\mu(E \cap F)}{\mu(E)},`$$
using `ProbabilityTheory.cond` / `cond_apply` / `cond_mul_eq_inter` (Mathlib
`ProbabilityTheory/ConditionalProbability/Basic.lean`).

**Sub-tasks (same wave):**
- `exists_continuous_atomic_decomposition` (line 149): give a real conclusion via
  `MeasureTheory.Measure.lebesgueDecomposition` (continuous + atomic parts) rather
  than `True`.
- `exists_regular_conditional_probability` (line 67): if it is already real, keep;
  otherwise complete it with `condExpKernel` / `ProbabilityTheory.cond`.
- Leave `vonNeumann_abelian_classification_true` (line 108) as a documented
  placeholder unless a concrete finite-dimensional abelian-classification claim is
  at hand — it is a large theorem; do not `sorry` it.

**Definition of done:** `selecting_events_not_rewriting_history` and
`exists_continuous_atomic_decomposition` have real (non-`True`) conclusions,
`sorry`-free, `axiom`-free.

---

## Priority 3 — New `Book/` chapters: prove the claims they assert without a backing theorem

The recent curated chapters (`Book/GaugeSymmetry.lean`,
`Book/RealRepresentations.lean`, `Book/YangMillsQuantization.lean`,
`Book/GribovAmbiguity.lean`, `Book/PhysicalParity.lean`,
`Book/DiffeomorphismsGravity.lean`, `Book/ConsciousnessBayesianPrior.lean`,
`Book/AlignedDeepLearning.lean`) cite existing `BookProof/` theorems via `#check`.
A few prose claims are asserted *without* a cited theorem. Prove each, in the
smallest `BookProof/` module consistent with the existing naming, and add a
`#check` to the chapter.

### 3.1 Dissipative dynamics — non-singularity across the whole interval
`Book/GaugeSymmetry.lean` asserts the halving map $`x\mapsto x/2` is *non-singular*
(it maps every positive-measure interval to positive measure). `BookProof/
ChapterIrreversibleDynamics.lean` has `dissipative_nonsingular_Icc` (for `Set.Icc`).
Add the general Lebesgue version: for measurable $`A` with $`\lambda(A) > 0`,
$`\lambda(\tfrac12 A) > 0` (or the non-singularity of the reflection/scale map),
via `MeasureTheory.MeasurePreserving` / `Measure.map` of the linear map
$`x \mapsto x/2`.

### 3.2 Real-representation sum closing a stated identity
`Book/RealRepresentations.lean` asserts the full-Lorentz projectivity and the
$`16 = 4+6+4+2` direct-sum decomposition. `BookProof/ChapterLorentzRealRepDirect.lean`
already has `WFam_isInternal` and `finrank_full_eq_add`. Add the companion fact that
conjugation by *any* element of $`\Omega` (not just the generators) preserves each
summand, i.e. promote `WFam_conj_invariant` to a full-representation statement if it
is only proved for generators. Verify by `#check`; close any missing lemma.

### 3.3 Gravity: the two projectors are orthogonal complements
`Book/DiffeomorphismsGravity.lean` asserts $`\chi\cdot\Pi = 0` and
$`\chi + \Pi = \delta`. `BookProof/ChapterGravityTimeProj.lean` has
`spatialProj_mul_timeProj` and `spatialProj_add_timeProj`. Add the missing
`timeProj_mul_spatialProj = 0` (already present) and, if not present, the
conclusion that the image of $`\chi` equals the kernel of $`\Pi` (the orthogonal
decomposition $`\mathbb{R}^{1,3} = \operatorname{im}\chi \oplus \operatorname{im}\Pi`),
packaged as a submodule direct-sum statement.

### 3.4 Yang–Mills: the two field-strength normalizations agree
`Book/YangMillsQuantization.lean` cites both `fieldStrengthMul` (abstract) and
`Fbook` (book's physical combination). Add (if not present) the bridge identity
that the two coincide up to the coupling: `commutator_eq_coupling` may already give
it; if `Fbook` and `fieldStrengthMul` are not yet related by a single theorem,
prove `fieldStrengthMul_eq_Fbook` under the connection substitution
$`a_j = -igA_j`.

### 3.5 Consciousness: no-free-lunch as a first-order statement
`Book/ConsciousnessBayesianPrior.lean` asserts `distinct_priors_each_preferred`.
`BookProof/ChapterNoBestPrior.lean` has it. Add the *uniform-prior* counterpart used
by the chapter: under a positive uniform prior, MAP ⟺ MLE
(`BookProof/ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE` exists) and the
relabeling-invariance uniqueness (`normalized_isRelabelingInvariant_eq_uniform`
exists). Verify both are `#check`-able and `sorry`-free; if any is a placeholder,
prove it.

### 3.6 Deep learning: the induced-prior expectation identity
`Book/AlignedDeepLearning.lean` asserts `inducedPrior_expectation` (expectation
under the induced prior equals the seed-average of the trained model).
`BookProof/ChapterDeepLearningEnsemble.lean` has it. Add the missing companion
`evidence_eq_seed_average` if not present, and the full posterior-as-ratio statement
`posterior_expectation_eq_seed_ratio` (both listed by the roadmap as present —
verify, and prove any that are still placeholders).

---

## Priority 4 — Upgrade selected `EXTERNAL` hypotheses to proving within Mathlib

These are documented named hypotheses. Only the ones with a realistic Mathlib proof
should be attempted; do **not** turn the deep external theorems (Wigner/Mackey
imprimitivity, Varadarajan) into `axiom`s — keep them as named hypotheses.

Realistic targets (Mathlib v4.28.0 has the ingredients):
- **Schur's lemma, finite-dimensional unitary** (`ChapterA2` `EXTERNAL`). Mathlib has
  `Module.End` / `Submodule` irreducibility and finite-dimensional endomorphism
  algebra; a self-intertwiner of an irreducible finite-dim rep being scalar is
  doable via `Module.compactness`/rank or via `Submodule.irreducibleSpace`. Prove
  `schur_scalar_of_irreducible` (finite-dimensional) and remove the `EXTERNAL` flag
  on that specific instance.
- **Weyl complete reducibility, finite-dimensional** (`ChapterA3j`–`A3v` `EXTERNAL`).
  Maschke's/the finite-dim complete-reducibility theorem for a reductive subgroup of
  `GL(n)` is close to Mathlib's `OmegaCompleteFlat`/`DirectSum`. If the general
  theorem is out of reach, keep the *already-proved* `N = 2` instance
  (`ChapterA3p`) and add `N = 3` as a concrete complete-reducibility witness, then
  stop (this thread is closed by STOP RULE #1 at `N = 6`).
- **Pauli fundamental theorem of γ-matrices** (`ChapterA3b` `EXTERNAL`). The concrete
  Clifford algebra of `Mat(4,ℝ)` is fully built (`ChapterA3`); prove the
  "any matrix commuting with all `γ^μ` is scalar" fact for the *fixed* 4×4 model,
  which is an instance of Schur's lemma for the concrete representation, and remove
  the `EXTERNAL` flag on that concrete case.

Do **not** attempt (keep as named `EXTERNAL` hypotheses): Wigner/Mackey
imprimitivity exhaustiveness, Varadarajan Thm 6.12, `levy_paths_nowhere_differentiable`
(no Brownian motion in Mathlib v4.28.0), `CrouzeixBound` (deep spectral-set estimate).

---

## Priority 5 — `book.tex` claims not yet formalized (low-risk, high-value)

From `FORMALIZATION_ROADMAP.md` "Further `book.tex` claims" (Priority 7) and the
triage table. Each has existing anchors; prove the finite/discrete core. These are
independent of the physics chapters and are all realistic.

### 5.1 Density matrix = diagonal rotated by a unitary
`book.tex` ~1796–1800: "the density matrix is a diagonal operator rotated by a
unitary operator, with the diagonal operator defining the marginal … and the
unitary defining the conditioned probability."

**Prove:** for a Hermitian matrix $`\rho`, the spectral decomposition
$`\rho = U D U^\dagger` with $`D` diagonal real and $`U` unitary. Use Mathlib's
`Matrix.PosSemidef.spectral_decomposition` / `Module.End` spectral theorem
(`LinearMap.IsSymmetric.eigenvectorBasis`). Express $`D` as the marginal and $`U`
as the conditional via `BookProof/ChapterDensitySpectral.lean` and
`ChapterConditional.lean`. Deliverable: `density_spectral_unitary_decomposition`.

**Status (2026-08-08): DONE.** `BookProof.DensitySpectral.density_spectral` proves
`ρ = U D U†` with `U` the eigenvector unitary and `D` diagonal real.

### 5.2 Average (L²) vs maximal (L^∞) error duality
`book.tex` ~8405–8414: average error = $`L^2` norm of $`\sqrt{\rho}`; maximal error
= $`L^\infty` norm.

**Prove:** for a probability density $`\rho \ge 0` with $`\int\rho = 1`,
(a) $`\|\sqrt{\rho}\|_2^2 = \int\rho = 1`; (b) the $`L^2 \le L^\infty` norm
inequality on a finite measure space. Use Mathlib `MeasureTheory.Lp` /
`MeasureTheory.lintegral`. Deliverable: `wavefunction_l2_norm_sq_eq_integral`,
`l2_le_linfty_of_finite`.

**Status (2026-08-08): DONE.** Both theorems proved in `BookProof/ChapterErrorNorms.lean`
(`BookProof.ChapterErrorNorms.wavefunction_l2_norm_sq_eq_integral`,
`l2_le_linfty_of_finite`).

### 5.3 Countable definability of the reals
`book.tex` ~8430–8434: the set of reals definable in a fixed countable language is
countable. `BookProof/ChapterDefinabilityFragment.lean` and
`ChapterCountableDefinability.lean` already prove `definable_reals_countable` and
`exists_nondefinable_real`. Verify they are `sorry`-free; if the roadmap notes any
gap, complete it. Deliverable already present — confirm and add `#check`.

**Status (2026-08-08): DONE.** `BookProof.ChapterCountableDefinability.definable_reals_countable`
and `exists_nondefinable_real` both prove; `sorry`-free.

### 5.4 Finite computation + Bayesian prior for large integers
`book.tex` ~10646–10653. `BookProof/ChapterFiniteArithmeticPrior.lean` already proves
`prior_is_probability` and `certainExtension_known`. Add the missing companion: a
finite truncation of multiplication (bounded by `B`) is consistent with the exact
arithmetic on `[0,B]`, and the extension prior is a genuine probability distribution.
Verify `#check`-able; complete any placeholder.

**Status (2026-08-08): DONE.** `BookProof.ChapterFiniteArithmeticPrior.prior_is_probability`
(`0 ≤ prior h` ∧ `Σ h, prior h = 1`) and `certainExtension_known` both prove.

### 5.5 Kopperman `L_{ω₁ω₁}`: all models separable
`book.tex` ~10630–10644. `PnpProof/Kopperman.lean` has `substrate_separable` and the
Π⁰₂-invariance facts. Add (if not present) the explicit theorem "every `Formalism H`
model carries a separable Hilbert structure" and the invariance of finitary truth
across models. Keep full infinitary completeness/compactness as a documented gap.

**Status (2026-08-08): DONE.** `PnpProof.Kopperman.substrate_separable` and the
`BookProof.ChapterKopperman` wrapper `kopperman_substrate_separable` prove.

### 5.6 Probability as a universal language (kernel transport)
`book.tex` ~8402, 8702. Prove: a Markov/conditional kernel $`X \to Y` transports any
probability measure, and the transported measure is a probability measure. Use
`MeasureTheory.Measure.map` / `ProbabilityTheory.cond`. Deliverable:
`kernel_transport_isProbability`.

**Status (2026-08-08): DONE.** `BookProof.ChapterKernelTransport.kernel_transport_isProbability`
(plus `kernel_transport_apply`, `kernel_transport_lintegral`, `kernel_transport_deterministic`)
all prove.

---

## Priority 6 — Hygiene (final wave, always do)

1. `#print axioms` spot-checks on every new headline (expect only `propext`,
   `Classical.choice`, `Quot.sound`).
2. `grep -rn "sorry" BookProof/ PnpProof/ Singularity/ RandomMap/` — must show only
   `RandomMap/SchoenfeldPRA.lean:162,176` (intentional).
3. `grep -rn "^axiom" BookProof/ PnpProof/` — must be empty.
4. Register every new file in `BookProof.lean`; `lake build BookProof` green.
5. Add a `#check` block to the corresponding `Book/*.lean` chapter for each new
   headline so the book and the proof library stay in sync.
6. Update `BookProof/STATUS.md` with a dated wave note for each landed package.

---

## Execution guidance

- Work the queue **in order**, landing several deliverables per pass (the author's
  standing mandate: a pass that lands a single package is incomplete; target ≥ 4
  deliverable groups). Re-verifying already-green files is not progress.
- Do not add another instance of an already-general result (the dimension-count
  thread is closed at `N = 6`).
- Keep every theorem `sorry`-free / `axiom`-free. Where a full claim is out of
  reach, state the provable core precisely and record the gap in
  `BookProof/STATUS.md` / `FORMALIZATION_ROADMAP.md`; never `sorry` a strong claim.
- Prefer `EXTERNAL` named hypotheses over `axiom` for the deep external theorems.