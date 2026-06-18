# Summary of changes for run 824c3415-19c4-4605-9d26-16ab1e96803b
Implemented `IMPLEMENTATION_PLAN_RCP.md` — the RCP/bounded-coefficient-prior route to RH — as two new Lean files wired into the build, following the plan's `[mech]`/`[LB]` discipline. The whole project (`RiemannProof` and `PnpProof` default targets) builds successfully, and no `axiom` or `@[implemented_by]` declarations were introduced.

New file `RiemannProof/RcpEuler.lean` (Phases 0–2):
- Phase 0.1: `Ωb`, `Xb`, the bounded-coefficient exponential Euler product `eulerB` (reusing `GaussianEuler.cCorr`), plus `bSum`/`eulerB_eq`.
- Phase 0.2: `eulerB_ne_zero` (proved — `exp` is never zero) and `eulerB_differentiableOn` (proved — mirrors `eulerG_differentiableOn`, via `Differentiable.const_cpow` + `etaEulerApprox_analyticOnNhd` + `Complex.exp_log`). The plan's "tail" item is restated honestly as `bSum_tail_small` (the true Weierstrass M-test content, since the plan's verbatim `eulerB → etaRect` is false for generic ω) and left as a `[LB]` sorry with the M-test recipe.
- Phase 0.3 (prior half): `priorBall`, its probability/ball-support facts (`[LB]` sorries).
- Phase 1: `edgeTrace`, `interiorVal`, the genuine `rcpKernel` via `ProbabilityTheory.condDistrib` (defined, not sorried), `edgeNbhd`, `priorBall_edgeNbhd_pos`, and the conditional contour-convergence lemma `rcp_recipEulerB_tendsto_recipEta` (`[LB]` sorries, recipes in docstrings).
- Phase 2: the stable `Prop`-level `rcpZeroAt` definition and the non-detectability lemma `not_rcpZeroAt` (`[LB]` sorry).

New file `RiemannProof/SchoenfeldPRA.lean` (Phases 0.3-formalism, 3–5):
- Phase 3.1: `schoenfeld`, `schoenfeld_primrec`, `RH_PRA` (the `Π⁰₁` sentence). `schoenfeld` is left opaque/`sorry` per the plan's `[LB]` flag — deliberately not a constant `Bool`, so `RH_PRA` stays faithful and non-vacuous.
- Phase 3.2: `Pi01`, `interpPi01`, `pi01_invariant`, `interpPi01_eq` (proved — `Iff.rfl`, cloning `Kopperman.interpPi02`/`arith_truth_invariant`).
- Phase 0.3 (formalism half): `rcpFormalism` via `Kopperman.formalismOfPrior` (with substrate Borel instances), plus `interp_schoenfeld_eq` (proved).
- Phase 4.1: the bridge `counterexample_iff_rcpZero` (`[LB]` sorry).
- Phase 5: `no_schoenfeld_counterexample` (proved — bridge + non-detectability), a concrete isolating rectangle `isoRect` with helper lemmas (proved, using `etaEulerApprox_ne_zero`), `RH_PRA_holds` (proved `[mech]` modulo the upstream `[LB]` sorries), and the optional `riemann_hypothesis_via_rcp` (`[LB]` sorry, Schoenfeld 1976 direction).

All load-bearing analytic/probabilistic steps remain marked `sorry` with the plan's recipes in their docstrings, exactly as the plan directs ("do not improvise"); every mechanical step is discharged. The two files are imported from `RiemannProof.lean`. Reused infrastructure (`Rect`, `rect_cauchy`, `boundary_integral_limit_eq_zero`, `reciprocal_tendstoUniformlyOn_of_nonvanishing`, `etaRect`, `etaEulerApprox`, the Kopperman formalism) was not re-derived. Note: because the route's load-bearing lemmas are unproven `sorry`s, the assembled `RH_PRA_holds`/`riemann_hypothesis_via_rcp` are scaffolding that depends on those sorries rather than a completed proof of RH.

# Summary of changes for run e95705ca-1719-49ef-94b6-b474bf6ec5c4
Completed the final outstanding item of the PnpProof formalization plan — N1, the explicit `O(k)` comparator-circuit upgrade of the model's "NP side" — leaving the whole development sorry-free and axiom-free (only `propext`, `Classical.choice`, `Quot.sound`). The pre-existing `RiemannProof` library is untouched, and `lake build` (both default targets) succeeds.

New file `PnpProof/Comparator.lean` builds the construction from scratch on top of the existing `Circuit` theory in `PnpProof/Counting.lean`:
- A clean single-gate append API: `Gate.eval`, `Circuit.snoc`, and the two evaluation lemmas `snoc_nodeValNat_lt` / `snoc_nodeValNat_top` (plus `nodeValNat_input`, `clampFin`).
- `step`, one ripple-comparator stage (9 gates) updating an eq/lt register pair, with its value lemmas `step_eqN_val` / `step_ltN_val` and `step_preserves`.
- `buildLT`, the MSB-first fold of `step` over the bit positions, with the correctness invariant `buildLT_spec` (proved by induction using the relocated bit-recursion lemma `div_pow_succ_compare`).
- `baseSt` seeding the registers from TRUE/FALSE constant nodes; `bitsOf` packing three k-bit numbers; the two chained comparators `cmp1`/`cmp2` (with `cmp1_ltN_val`/`cmp2_ltN_val`); and `fullCircuit` combining them with a final ¬·∧¬·.
- The headline theorem `verify_circuit_cheap`: for every k ≥ 1 there is an explicit `Circuit (3*k) (s+1)` of size `s ≤ 50*k + 50` deciding `(glo ≤ u ∧ u ≤ ghi)` on the packed inputs.

In `PnpProof/Main.lean` the N1-OPEN note was replaced by the NEW theorem `model_P_ne_NP_circuit`, whose NP-side conjunct is the circuit family from `verify_circuit_cheap` (phrased with `verifyBits`) and whose P-side conjunct is T2 (`almost_all_not_computable`); it carries the same "theorem about the model, not the Clay statement" docstring. As mandated by the plan, the original `model_P_ne_NP` is left exactly as it was, so both the computability form and the circuit form coexist. The bit-recursion lemma `div_pow_succ_compare` was moved from `Main.lean` to `Comparator.lean` (no longer duplicated) and `PnpProof.lean` now imports the new module.

`PnpProof/IMPLEMENTED.md` was updated with a `Comparator.lean` section and the N1-complete status. Only stylistic linter warnings (line length / whitespace / multiGoal) remain, several of them pre-existing; the build itself is clean.

# Summary of changes for run 170e5877-d03a-49ef-b371-c44798f0030a
Continued the `PnpProof` development and completed almost all of the remaining next-step queue (N1–N5 in Part 7 of the plan). The whole library still builds with `lake build PnpProof`, every new result is sorry-free, and all of them depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound` (verified with `#print axioms`). The pre-existing `RiemannProof` library is untouched.

New work, all in `PnpProof/SphereGaussian.lean` unless noted:

- N3 (G5 certificate — rotation invariance of the uniform sphere measure): `sphereProj_equivariant`, `gaussianE_rotation_invariant` (via characteristic functions), and the combined `sphereUniform_rotation_invariant`. This is the certificate that `sphereUniform` deserves the name "uniform".
- N2 (G4 second half — the Hermite normalization integral): `physHermite_hasDerivAt` (the derivative recurrence H_{n+1}'=2(n+1)H_n), `hermite_sq_integral` (∫ H_n(x)² e^{−x²} dx = √π·2ⁿ·n!, by an integration-by-parts induction with base `integral_gaussian`), and `hermite_normalization` (the chapter's value √π·2ⁿ/n!).
- N1 (G4 first half — the normalization-constant limit): `gegenbauerScaled_rec` (the rescaled three-term recurrence), `gegenbauerScaled_bound` (a uniform-in-λ polynomial bound proved by recurrence induction), and `normalization_tendsto` (the chapter's limit, proved by dominated convergence). It is stated in the post-change-of-variables form, as the plan permits.
- N4 (Poincaré–Borel): `gammaMeasure` (the infinite product of standard Gaussians, via `Measure.infinitePi`), `normSq`, `gaussian_concentration_sphere` (G7, the a.s. strong-law concentration), and `poincare_borel_ae` (G6, a.s. coordinatewise convergence of the √k-sphere normalization to the Gaussian coordinates).

N5 (the explicit O(k) comparator-circuit upgrade of T3's NP side) is the one item left OPEN. Its driving bit-recursion lemma `div_pow_succ_compare` is proved, but assembling the full explicit `Circuit (3*k) (s+1)` together with its node-by-node correctness proof is a large standalone construction that exceeded the available budget. Following the plan's standing instruction for N5, no `sorry` was committed and the existing `model_P_ne_NP` was left untouched, so the development remains sorry-free and axiom-free. The finite-k Chebyshev fallback (G7′) and the bounded-continuous weak-convergence corollary of G6 were not needed once the a.s. forms were in place.

`PnpProof/IMPLEMENTED.md` has been updated to record the new lemmas, files, deviations, and the OPEN status of N5. `ARISTOTLE_SUMMARY.md` was left unedited as requested.

# Summary of changes for run 3e124399-f441-48ea-b531-c69e452360c5
Implemented `PNP_IMPLEMENTATION_PLAN.md` as a new Lean library `PnpProof` (added alongside the existing `RiemannProof` in the lake project). Everything compiles and `lake build PnpProof` succeeds; every result is sorry-free and depends only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`. A full report is in `PnpProof/IMPLEMENTED.md`.

What was formalized (≈55 definitions/theorems across 6 files):

- `PnpProof/Foundations.lean` (Part 1, F1–F8): points/countable sets are null, the disintegration/conditional-kernel existence, no countable history realizes a target event, countability of atoms of a finite measure, mutual singularity of diffuse vs atomic parts, the CDF-jump separation, and atomlessness of the diffuse conditioning.
- `PnpProof/Counting.lean` (Part 2, C1–C5 and C2): countability of computable functions; a from-scratch Boolean-circuit theory (`Gate`, `Circuit`, evaluation, size monotonicity); circuit counting; the Shannon bound that almost all Boolean functions need many gates (stated for n ≥ 8); and the Lebesgue-null set of computably-coded reals via binary-digit reconstruction.
- `PnpProof/FunctionSpace.lean` (Part 3): L²([0,1]) is separable, L^∞([0,1]) is not, the wave-function √p ∈ L² with unit norm, polynomials are dense in L², the classification theorem that all infinite-dimensional separable real Hilbert spaces are isometric (the honest surrogate for the Fock–Guichardet isomorphism), and an atomless Borel probability measure on the unit sphere.
- `PnpProof/SphereGaussian.lean` (Part 3b): physicists' Hermite and Gegenbauer polynomials, the lopez99 limit (rescaled Gegenbauer → Hermite, proved by the mandated recurrence-induction route), the weight → Gaussian limit, and the construction of the uniform measure on the √k-sphere as a Gaussian pushforward (probability measure, concentrated on the sphere).
- `PnpProof/Model.lean` (Part 4): dyadic discretization, the inverse-transform verifier, machine computation of a selection function with a uniqueness theorem and countability of computable selections, and a concrete atomless probability prior on the space of selection functions C([0,1], ℝ).
- `PnpProof/Main.lean` (Part 5): T1 `selection_not_history`, T2 `almost_all_not_computable` (prior-probability-1 uncomputability of the selected function), T3 `model_P_ne_NP` (the in-model separation: the candidate verifier is computable while the solution is prior-a.s. uncomputable), and the §5→§6 glue `mixed_to_continuous`.

Faithfulness and deviations (all documented in the report and in docstrings):
- T3 is explicitly a theorem *about the paper's model*, not the Clay statement; no implication to standard P ≠ NP is asserted (per Part 6).
- Because adding axioms is not permitted, the NP side of T3 is formalized as the computability of the verifier (faithful to "verification is cheap") rather than via an explicit O(k) comparator circuit or a model axiom.
- T4 (the §7 "realistic version") is left genuinely open with an explanatory note rather than committing to a possibly-incorrect statement.
- A few heavy, standalone items are noted as future work: the dominated-convergence normalization limit and Hermite orthogonality value (G4), the Poincaré–Borel / infinite-product-measure concentration (G6/G7), rotation invariance of the sphere measure, and the elaborate ratStep family of H4 (whose essential "countable dense subset of L²" content is covered by separability and polynomial density).

The pre-existing `RiemannProof` library is untouched and still builds.