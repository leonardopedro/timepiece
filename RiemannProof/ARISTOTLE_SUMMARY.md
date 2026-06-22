# Summary of changes for run 9b7b06e5-0b59-4fbc-905b-465567d282dc
I implemented the 2026-06-22 redesign described in `IMPLEMENTATION_PLAN_RCP.md`, following its "Recommended next steps (priority order)". All work is in `RiemannProof/RcpEuler.lean` (plus a one-line quarantine edit in `RiemannProof.lean`), and the project builds successfully (`lake build`, 8052 jobs, no errors).

What was done, step by step:

1. **(R) Radius 1→2.** `diskLaw` is now the uniform law on `Metric.closedBall 0 2`; re-proved the dependent mechanical lemmas at the new radius — `diskLaw_isProb`, `diskLaw_ball`, `priorBall_ball` (now `‖Xb p ω‖ ≤ 2`), `diskLaw_closedBall_pos`, and the legacy `not_rcpZeroAtAll` (adjusted its `≤ 1` bounds to `≤ 2`). This puts the mean realization `X_n ≡ 1` in the interior of the prior support.

2. **(M) General non-multiplicative series.** Added `etaX s ω = ∑' n, ω n · n^{-s}` as the primary model (`eulerB` kept as legacy special case), with the convergence-assembly lemma `summable_etaXTerm` proved sorry-free (absolute convergence on `Re s > 1` via an M-test against `2 ∑ n^{-Re s}`).

3. **Shared rcp object `L`.** Defined the conditional machinery once — `edgeTraceX`, `interiorValX`, `rcpKernelX` (`condDistrib`), the mean-realization trace `eTrace`, and `L s₀ R := rcpKernelX s₀ R (eTrace R) {0}` — so both load-bearers are stated against the *same* `L` (the plan's ★ design note).

4. **(Z) ZFC-direct load-bearers and assembly.** Stated, against this shared `L`, the two deep analytic inputs as honest `[LB] sorry`s exactly as the plan directs ("do not improvise — not weaker than RH"): `transfer_equality : L s₀ R = (if riemannZeta s₀ = 0 then 1 else 0)` and `L_ne_one : L s₀ R ≠ 1`. Built the final assembly: `stripRect`/`riemannZeta_ne_zero_of_mem_strip` (the three-line `by_contra` core) and `riemann_hypothesis_via_rcp : ∀ s, riemannZeta s = 0 → 1/2 < s.re → s.re < 1 → s.re = 1/2`.

5. **Quarantined the PRA spine.** Removed `import RiemannProof.SchoenfeldPRA` from `RiemannProof.lean` (with an explanatory comment), so the dropped Π⁰₁/Schoenfeld material is no longer part of the built route; its file is left untouched as historical.

Honest status: the final theorem `riemann_hypothesis_via_rcp` and `riemannZeta_ne_zero_of_mem_strip` compile, but their proofs depend on the two load-bearing `sorry`s (`transfer_equality`, `L_ne_one`) — `#print axioms` shows `sorryAx`. These two lemmas are, by the plan's own account, the route's deep un-formalized analytic inputs (a regular-conditional-probability-at-interior-support principle and Bagchi/Voronin universality in local form) and are not weaker than RH; per the plan's explicit instruction they are left as honest, documented sorries rather than improvised. The legacy `not_rcpZeroAt` (pre-existing) remains a sorry as before. All other added content is sorry-free. The Riemann Hypothesis itself is therefore not established — the deliverable is the faithful formal scaffolding the plan requested, with the genuinely-RH-equivalent obligations clearly isolated.

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