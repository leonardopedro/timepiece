# Summary of changes for run 39f16c70-d033-44bb-adce-3aaeb02ac4a5
I implemented the new (2026-06-19) maintainer refinement of the RCP route, focusing on the one concrete, sound change it specifies, and keeping every genuinely open-problem-equivalent obligation as an honest, clearly-documented `sorry` (the plan's repeated "do not improvise" directive). The whole project still builds: `lake build` is green (8053 jobs), with only `sorry` notices and pre-existing style/long-line warnings.

What changed (in `RiemannProof/RcpEuler.lean` and `RiemannProof/SchoenfeldPRA.lean`):

- Split the rcp-zero predicate into its two honest forms, as the refinement requires:
  - `rcpZeroAtAll` — the old `∀ k` joint-mass form, now explicitly marked a placeholder. Its non-detectability `not_rcpZeroAtAll` remains genuinely proved (only `propext`/`Classical.choice`/`Quot.sound`), but only because it can be discharged trivially by selecting the fixed cutoff `k = 0`, where the finite product is bounded away from `0` — i.e. it never sees whether `η(s₀)=0`.
  - `rcpZeroAt` — the substantive limit/eventual-`k` form (`∀ r>0, ∀ᶠ k in atTop, …`), which is the object that genuinely detects a strip zero.
- Restated `not_rcpZeroAt` for the substantive limit form. This is now correctly identified as a load-bearing analytic obligation (its content is the regular-conditional-probability limit `L ≠ 1`, i.e. Bagchi/Voronin universality on a local neighborhood; `¬ rcpZeroAt` is `η(s₀)≠0` uniformly, i.e. RH itself), and is left as an honest `sorry` with the recipe. This corrects the earlier misleading "non-detectability is proved" status, which only held for the trivial placeholder form.
- Updated the bridge `counterexample_iff_rcpZero` docstring to the `eq1`/`eq2` (conditioning at the mean `X≡1` realization, Schoenfeld 1976) structure, and refreshed both files' header docstrings to reflect the corrected honest state. The bridge and the optional `riemann_hypothesis_via_rcp` (5.3) remain honest `sorry`s.

Honesty note — this is NOT a proof of the Riemann Hypothesis. Three `sorry`s remain: the limit-form `not_rcpZeroAt` (`RcpEuler.lean`), the bridge `counterexample_iff_rcpZero`, and `riemann_hypothesis_via_rcp` (`SchoenfeldPRA.lean`). Each is, by the plan's own analysis, not weaker than RH (or is RH directly) and bottoms out at un-formalized deep analytic inputs (Schoenfeld 1976 and Bagchi 1981 universality). I verified that the downstream assembly `RH_PRA_holds` depends on `sorryAx`, so the development proves nothing false — it remains an honestly-gated route, not a verified theorem. The earlier-discharged primitive-recursive Schoenfeld matrix (Phase 3.1) is untouched and still sound. No axioms or `@[implemented_by]` attributes were introduced.

# Summary of changes for run e6251121-ec93-4762-875d-225ed9079295
I implemented the actionable, sound portion of `IMPLEMENTATION_PLAN_RCP.md`, focusing on the one self-contained obligation the plan's own "Recommended next steps" flags as the priority and as genuinely dischargeable (Phase 3.1), while respecting the plan's explicit directive to leave its RH-equivalent load-bearers as honest `sorry`s.

What was done (new, sound, axiom-clean):
- Added `RiemannProof/SchoenfeldMatrix.lean`, a genuine, non-vacuous, primitive-recursive decision procedure for Schoenfeld's bound `|π(n) − li(n)| ≤ (1/(8π))·√n·ln n`:
  - exact prime counting `primePi` (sieve);
  - fixed-point natural log `lnFix`/`incr` via the `artanh` recurrence `ln(m+1) = ln m + 2·artanh(1/(2m+1))`;
  - fixed-point logarithmic integral `liInt` via the rectangle sum `Σ_{2≤k≤n} 1/ln k`;
  - the bound squared and rationalized to pure `ℕ` arithmetic (`√` removed by squaring, `(8π)² ≈ 6316547/10000`), giving `schoenfeld : ℕ → Bool`.
  - Full proof that the function is primitive recursive: `schoenfeld_primrec : Primrec schoenfeld`, built up through helper lemmas (`pow_primrec`, `prime_primrec : PrimrecPred Nat.Prime`, `sumRange_primrec`, `primePi_primrec`, `incr_primrec`, `lnFix_primrec`, `liInt_primrec`). Verified with only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Wired this into `RiemannProof/SchoenfeldPRA.lean`: the previously-opaque `schoenfeld`/`schoenfeld_primrec` sorries are replaced by the real definition and proof, so `RH_PRA` is now a faithful (non-vacuous) `Π⁰₁` sentence. Added the module to the root `RiemannProof.lean` import. Updated the docstrings to reflect completion.

The whole project builds successfully.

Important honesty note — this is NOT a proof of the Riemann Hypothesis. Two `sorry`s remain in `RiemannProof/SchoenfeldPRA.lean`, and they are intentionally left exactly as the plan directs ("do not improvise"):
- `counterexample_iff_rcpZero` (Phase 4.1, the bridge), and
- `riemann_hypothesis_via_rcp` (Phase 5.3, RH stated for `riemannZeta`).
As the plan's own status notes record, given the already-proved (placeholder) `not_rcpZeroAt`, the bridge 4.1 is equivalent to the Schoenfeld `Π⁰₁` sentence — hence to the Riemann Hypothesis itself, an open problem — and 5.3 is RH directly. The route's downstream assembly (`RH_PRA_holds`) is therefore gated behind these unproven, RH-equivalent obligations and does not constitute a verified proof of RH. I deliberately did not attempt to discharge them, both because doing so would amount to resolving an open problem and because closing them by any non-genuine means would be unsound. No axioms or `@[implemented_by]` attributes were introduced.

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