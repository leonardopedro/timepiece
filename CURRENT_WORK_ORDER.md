# Current work order — one pointer per track

> **What this file is.** A routing table, not a source of truth. Every row points at
> the section of `CONSOLIDATED_PLAN.md` that the corpus currently treats as the
> authoritative work order for that track, plus the documents that section supersedes.
> Where the corpus disagrees with itself, the row says so and names the disagreement
> rather than picking a winner — picking one would make this file a second authority,
> which is the condition it exists to end.
>
> **Why it exists.** `CONSOLIDATED_PLAN.md` is ~16,400 lines of append-only dated state
> entries. Supersession is real and well marked *inside* it, but it is marked in prose
> and the entry point is stated once, in a header that has since fallen behind its own
> file. The plan's `G-T2` finding named this exactly: *"many parallel PLAN_* and REVIEW_*
> documents plus 15k-line CONSOLIDATED_PLAN. Supersession is stated in prose, not
> machine readable."* This is the machine-readable half of that sentence, kept honest
> by pointing rather than by restating.
>
> **How to read a row.** `current` is the entry point. `superseded as a reading guide`
> means the document remains the *detail* and must not be re-read as the order;
> `superseded outright` means do not implement from it.
>
> **Citations are content-based, deliberately.** Every reference below is a section
> heading or a quoted phrase, never a line number. `CONSOLIDATED_PLAN.md` is ~16,400
> lines and is append-only, but it is also *edited at the top* — fixing the stale
> header shifted every line number below it by 13 and invalidated every positional
> citation in this file at once. Line numbers into a document that grows and whose
> head gets rewritten are not a stable interface. The project already learned this
> with the Cadabra modules, where two stale line references were converted to
> content-based ones "so future header edits cannot rot them"; this file follows
> that precedent. If you need a position, grep the quoted phrase.
>
> **No Lean code is written or compiled for this file.** Every item below is a work
> order for the LLM-Lean4-specialist.

**House conventions this table inherits** (from the 21 state entries in
`CONSOLIDATED_PLAN.md`): entries are appended, never deleted; a new entry's preamble
says which prior entry it supersedes as the reading guide; status letters are **U**
unconditional, **C** conditional (hypothesis named and unproved), **N** negative or
obstructive, **B** boundary (explicitly not covered).

---

## The table

Anchor shorthand used below: **§09-25** = `CONSOLIDATED_PLAN.md` §"State of the project —
2026-09-25 (consolidated)"; **§10-04** = §"State of the project — 2026-10-04: the mass-gap
proof in Lean4"; **§10-04b** = §"State of the project — 2026-10-04b"; **§10-06** = §"State of
the project — 2026-10-06: PLAN M (planner side) landed, and the work orders its findings
create"; **§10-06b** = §"State of the project — 2026-10-06b: the sector correction — the
campaign measured a diagnostic, and §M4.9 gates §M4.3".

| Track | Current work order | Superseded as a reading guide | Superseded outright |
|---|---|---|---|
| **NS** (Navier–Stokes) | §09-25 **§5, item 3** ("NS: discharge the standing ESA hypotheses"), baseline in §09-25 **§2** (`**NS:**` row); the Lagrangian half closed 2026-10-16 — §"State of the project — 2026-10-16: the Koopman comparison `N_L = H_L² + E` is ESA — closed-by pointers" — remaining: the Eulerian square-comparison input and energy surjectivity (§"State of the project — 2026-10-16" step 4) | the 2026-09-24a…e state entries as entry points — each preamble supersedes its predecessor in place | `PLAN_LEAN_SPECIALIST_NS_FLOW.md` — self-marked `**EXECUTED (2026-08-14→16).**`; its **E.3** is marked `SUPERSEDED by the executed wave (2026-08-16)`; demoted globally by §09 route map ("supersedes the spread of routes in §9–§12 **and the per-thread plans**") |
| **QYM** (Yang–Mills) | §09-25 **§5, item 4** ("Non-abelian QYM one-particle form gap"); restated as the programme's top analytic input in §10-04b **§N2** | `REVIEW_AND_PLAN_20260907.md` — but note §09-25 records that it *extends* `REVIEW_THREADS_20260906.md` and "supersedes nothing in" it | `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` — "the continuous flow is **not yet instantiated for QYM**"; its own §11.4 "closed" claims are superseded by its later status block |
| **QG** (quantum gravity) | §09-25 **§5, item 2** ("QG: the density as a canonical variable"); record operator pinned in §09-25 **§1**; the QG-D-C branch now closes at §"State of the project — 2026-10-17: QG-D-C.1 (`hflat`) closed" (step **2a**, the assembled-side alignment, **closed 2026-10-19b** by `BookProof/Qg/ChapterQgAssembledFlatTransfer.lean` — §"State of the project — 2026-10-19b"; stated for any unitary onto the flat core, since `halfDensityUnitary` is one-dimensional) | the 2026-08-29e QG order (`**QG-ESA-C — the reassembly …**`); §"2026-10-15b"'s R1/R2 ordering for QG-D-C.1 — superseded by the factorisation route of §"2026-10-17" | `PLAN_LEAN_SPECIALIST_QG_FLOW.md` — status `executed` (2026-08-17); its densitized subject is demoted by §09-25 §1's "separate, labeled realizations — **never the record**" |
| **SM** (Standard Model) | §09-25 **§5, item 6** ("SM refinements"), baseline in §09-25 **§2**; live boundary ledger `HONEST_BOUNDARIES_SM.md` ("Current state of record") | the 2026-09-22e "what stays open" list — "superseded 2026-09-22f by the closure wave and the state section below"; the 2026-09-23e bosonic FL item ("Read this instead of … for the bosonic FL item") | the §D6b-SM **Step 3** work order — executed; and `smComparison` as a comparison operator — **refuted** by the 09-23f wave, though still defined and proved positive because the fermionic completion needs it |
| **RandomMap** (RH) | ⚠ **no current work order exists** — see flag **F2** | — | `IMPLEMENTATION_PLAN.md` — its own text marks the conjugate-reflection route "**Legacy / off-critical-path files (the superseded …)**"; `RandomMap_old.md` (superseded by `RandomMap.md`); `RandomMap2LegacyDraft.md` — "kept as historical material because several declarations use **obsolete APIs or state invalid proposals**"; `newproof.md` (superseded per `RandomMap.md`'s "Adaptation notes (what this plan adopts from `newproof.md`, and what supersedes it)"); `IMPLEMENTATION_PLAN_RCP.md`'s C2–C4 and Phase 3 — "C2–C4 are retained below **for historical context only** — do not implement" |
| **book** (Verso / pedagogical) | §"State of the project — 2026-10-16" **steps 0 and 6** (compile/name-check the chapters its §1 and its later same-day edits touched — six from §1 plus `Book/FourierElimination.lean`; hygiene) plus its §1–§2 as the reading of the 2026-10-15c wave; the compiled scope now additionally covers `BookProof/Qg/ChapterQgFlatContinuumEsa.lean`, the `BookProof.lean` / `ChapterRoadmapAudit.lean` additions and `Book/DiffeomorphismsGravity.lean`'s QG-D-C.1 closure prose — step 0 as restated at §"State of the project — 2026-10-17: QG-D-C.1 (`hflat`) closed" supersedes this cell's earlier step 0 for that material; its steps 1 and 3 are **closed** by final 2026-10-16 entries, step 2 by the 2026-10-17 entry (residual step 2a, closed 2026-10-19b); the rest of the track stays §09-25 **§5, items 1 and 7** (prose verification; hygiene decisions), build contract in the "Build scope" section | §09-25 §5 item 1 **for the six chapters touched by §"2026-10-16"** (`Book/OdeSingularity`, `Book/ProofPlans`, `Book/NsComparisonOperator`, `Book/NsOneParticleHamiltonian`, `Book/SecondQuantizationEsa`, `Book/DiffeomorphismsGravity`) — that entry's preamble supersedes it for those chapters only; the §4 BookProof task list — "now all LANDED … kept as a record only; do not redo them" | `SPECIALIST_PLAN_REMAINING.md` — "**Plan A is fully executed.**"; `BOOK_PROOF_PLAN.md` Priorities 1–2 (COMPLETE) |
| **BookProof layout** (repo hygiene / split) | §"State of the project — 2026-10-17b: `BookProof/` split plan and the redundancy / legacy / dead-end inventory" + `BOOKPROOF_SPLIT_PLAN.md` — phases 0–4 with per-phase acceptance (orphan `PartN` deletion → foldering independent parts → folder the core after the cross-import matrix → renames → perpetual gates); execution is the LLM-Lean4-specialist, compile per phase; **2026-10-18 addendum**: Phase 1.5 (convert 91 downloaded Prove2.me proofs into `Toolbox/Prove2me/`), §6 download inventory, §7 missions our corpus can feed, §8 sibling-project imports (70 more downloads for `../unfer` + `../dynamic-arctic`; `../australVM`/`../emthin` not present in this workspace — earmarks deferred) — pointers in `CONSOLIDATED_PLAN.md` §"2026-10-17c"/§"2026-10-17d"; **executed 2026-10-18** (§"State of the project — 2026-10-18: Prove2.me downloads converted …", `BOOKPROOF_SPLIT_PLAN.md` §9): Phases 0, 1, 2 done and green; Phase 1.5 landed in `converted/` (all 161 manifest solutions compiled after the platform library was supplied, §"2026-10-19"); **2026-10-19b**: Phase 0 residue (9 empty stubs removed), Phase 2.2b (the 237-module residue foldered by reading, `BOOKPROOF_PHASE2B_MOVES.md`) and Phase 3 (Weyl `Sl2`→`SL2Algebra`; other renames declined by cite density) executed — §"State of the project — 2026-10-19b" | — (no row superseded; the plan file is the detail, the §"2026-10-17b"/§"2026-10-17c" entries are the entry points) | — |
| **mass-gap** | §10-06b (the sector correction; **M4.9 gates M4.3**) → work order **§M4.9** in `../unfer/PLAN_MASS_GAP.md` §7; the proof itself remains §10-04 **§M4** | §13 (T1–T12, "the Lean4 plan"), `MASS_GAP_CERTIFIED.md`, `unfer_contracts/MASS_GAP_SPEC.md`, `unfer_contracts/MASS_GAP_REGENERATION.md` — §10-04 consolidates and supersedes all four "as a reading guide"; they "**remain the detailed record**"; §10-06's campaign tables are read under §10-06b (diagnostics) | — (§13.1's honesty boundaries and §13.6's definition of done still stand) |
| **math28** (`math/` results as hypotheses) | §"State of the project — 2026-10-20: `math28/` — `math/` results as named hypotheses on Lean v4.28.0; BookProof import graph repaired" + `math28/README.md` — named hypotheses only, never theorems of this repo | — | the 2026-10-20 request to compile `math/` wholesale on v4.28.0 (withdrawn; copy removed) |
| **BayesianTransformer** (nGPT geometry / SG-pCNL) | §"State of the project — 2026-10-21: `BayesianTransformer/` imported (uncompiled), `Book/BayesianTransformer.lean` read pedagogically, final-Hamiltonian convention re-verified, `../unfer/pcnl` comparator milestone" — work order §4 steps 0–3 (name-level check of the import, `#check` smoke block into the Book chapter, bridge lemmas under the convention, `DOC_INDEX` regen); **plus** §"State of the project — 2026-11-08b: `K_drift` for a polynomial potential — the composition with the letter `∂ⱼ`, its ladder-word family, and the band of `polyMul` (`FockLangevinOperator` §9.6–§9.8)" — the Module 3 operator closure: `diffHermite` (the letter `∂ⱼ = (aⱼ − aⱼ†)/√2`), **`polyDrift`** as `−Σⱼ polyMul (∂ⱼ Φ) ∘ diffHermite j` with its ladder-word family (`polyDrift_eq_ladderWords`, `polyDrift_eq_hopWords`), the band of the polynomial operator (`polyMul_band`: degree `≤ K` maps `{N ≤ N₀}` into `{N ≤ N₀ + K}`), and the band of the drift itself (**`polyDrift_band`**, §7 addendum: `K_drift` has band `K`, the derivative's loss and the letter's gain cancelling); its §6 lists what stays open (the norm estimate behind `DriftFormBound`, `K_reject`); **plus** §8 of that entry — `FockLangevinOperator` §9.9–§9.10: the drift's `ℓ¹` estimate (`coreL1`, `hopStep_l1_le`, `hopWord_l1_sector`, **`polyDrift_l1_le`** with the explicit sector constant `driftL1Bound`) and the pCNL Hamiltonian built from `polyDrift` instead of `driftOpCoeff` (**`pcnlPolyHamiltonian`**, **`pcnlPolyHamiltonian_band`**, `polyDrift_linear`), plus §10 of that entry — `FockLangevinOperator` §10: the coordinates of one ladder letter (`hopStep_coord_lower`, `hopStep_coord_raise`), the letter norms (`coreNormSq_hopStep_lower`: `‖a_j c‖² = ∑ₙ n_j‖c n‖²`; `coreNormSq_hopStep_raise`: `∑ₙ (n_j+1)‖c n‖²`) with their mode sums, and the **`oscillator_identity`** `∑_j (‖a_j c‖² + ‖a_j† c‖²) = 2⟪c,Nc⟫ + d‖c‖²`, and **`driftFormBound_holds`** — `DriftFormBound` itself proved in §11 of the chapter (`driftOpCoeff_form_bound`: Cauchy–Schwarz in the core pairing `norm_corePair_le` plus the mode-index Cauchy–Schwarz `sum_coreNorm_hopStep_le`, and `two_mul_le_add_div` giving the plan's constant `B²d/(2δ) + Bd`), leaving only `K_reject` open, because §12 of the chapter now supplies the coefficient family (`driftWeight`/`driftScale`, `driftOperator β σ Φ = (β²σ²/2) • polyDrift Φ`, `driftOperator_linear`, and `driftOperator_form_bound_eps` with `M_ε = K/ε`) and §13 the semiboundedness corollary (`corePair_numberOp_re`, `semibounded_of_form_bound`, `numberOp_add_driftOpCoeff_semibounded`, `pcnlDrift_semibounded_eps`: `N + K_drift` bounded below by a constant of order `ε⁻²`), the remaining analytic input being the core-side realization of `∇Φ_ε` as `polyMul (∂ⱼΦ_ε)`; **and** §13 of that entry — the hypothesis's `M_ε = K/ε` itself: `BayesianTransformer.epsProj_fderiv_le` proves `‖∇(g ∘ Ŵ)‖ ≤ 2K/ε` on `‖W‖ ≥ ε` for the additive normalization `Ŵ = W/(‖W‖ + ε)` (`epsProj`, `epsProj_fderiv_opNorm_le`), and `driftScale_eps_arch` reads it into the drift's `B = β²σ²K/ε`; §9 of the same entry adds `scripts/test_check_links.py`, the regression tests for the `check-links` tracked-vs-ignored scope; **and** §14 of that entry — `FockLangevinOperator` §14: the gradient bound `hgrad` is a *sector* statement, not a global one (`polyMul_X_unbounded` refutes the global form, since `xⱼ` raises the occupation and `‖xⱼ eₙ‖` grows like `√n`), while `polyMul_norm_sector_le` and `gradSectorBound` prove it on `{N ≤ N₀}` with an explicit constant (`coreNorm_add_le`, the sector letter norms, `coreNorm_mulHermiteList_sector_le`), so `polyDrift_form_bound_sector`, `driftOperator_form_bound_sector` and `pcnlDrift_semibounded_sector` are §11–§13 with no hypothesis at all on each truncated sector; **and** §15 of that entry — `FockLangevinOperator` §15–§16 close the two inputs §14 still listed: the Metropolis filter `K_reject` is `rejectOp ρ`, a *diagonal* multiplication by an acceptance probability (`rejectOp_apply`, `rejectOp_single`, `rejectOp_comp`) with band `0` (`rejectOp_band`), a contraction for `ρ = metropolisReject ΔV = min 1 (exp(−ΔV))` (`coreNorm_rejectOp_le`), and nonnegative in the form (`re_corePair_rejectOp_nonneg`), so the assembled step `pcnlFull = N + K_drift + K_reject` keeps §14's band (`pcnlFull_band`) and lower bound (`pcnlFull_semibounded_sector`, `pcnlFull_metropolis_semibounded`); and the coefficient-level comparison with the architecture's `M_ε = 2K/ε` is a theorem (`coeffMass`, `coeffMass_pderiv_le`: `coeffMass (∂ⱼΦ) ≤ deg Φ · coeffMass Φ`, so `GradCoeffBound` holds for every `Φ`; `driftScale_gradSectorBound_le_eps`: `GradCoeffBound Φ_ε (2K/ε)` gives `B ≤ β²σ²K/ε` times the level factor `d·(2√(N+2+deg Φ))^{deg Φ}`, with `driftScale_gradSectorBound_le_coeffMass` the hypothesis-free case); **and** §16 of that entry — the reading closed in `BookProof/MCMC/CoeffMap` (the coefficient map `linCoeff F x j = D F(x)[eⱼ]`, `linPart`, `pderiv_linPart`, and **`gradCoeffBound_epsProj`**: `epsProj_fderiv_le`'s `‖dŴ‖ ≤ 2K/ε` gives `GradCoeffBound (linPart (g ∘ Ŵ) W) (2K/ε)` with no hypothesis, at the linear order that a first-derivative bound controls; `eval_pderiv_norm_le_coeffMass` puts the two sides in the same units), plus `FockLangevinOperator` §18–§19 — the plan's diagonal `P₀ = ρ^N` (`baseOp`, band `0`, `baseOp_vac` fixes the vacuum with `λ_0 = 1`, `coreNorm_baseOp_sector_le` contracts the rest by `ρ`), the drift's norm constant `driftStepBound`, the assembled operator **`pcnlKernel = P₀ + K_drift + K_reject`** with `pcnlKernel_band` / `coreNorm_pcnlKernel_le` / `coreNorm_pcnlKernel_sector_le`, the iterate band `pcnlKernel_iter_band` and product bound `coreNorm_pcnlKernel_iter_le`, and the convergence that holds — `tendsto_iter_baseOp`: `P₀`'s iterates converge to the invariant state at rate `ρ`; the full step's convergence is stated as needing the Markov structure (positivity, `P 1 = 1`) the core lacks  ; **and** §17 of that entry — `FockLangevinOperator` §20, the stochastic split: the Metropolis complement `rejectComplement ρ = 1 − ρ^N` makes the diagonal half the identity (**`baseOp_add_rejectOp_complement`**: `P₀ + K_reject = 1`, so `pcnlKernel = 1 + K_drift` via `pcnlKernel_complement`), which is the normalisation `P 1 = 1` exactly; the diagonal half is positive (`re_baseOp_nonneg`, `re_rejectOp_nonneg`) and `ℓ¹`-bounded (`coreL1_baseOp_le`, `coreL1_rejectOp_le`), with `coreL1_pcnlKernel_complement_le` showing it contributes no `ℓ¹` contraction — so the remaining input for a convergence theorem is the drift's *sign* (its negative part), not the normalisation; **and** §18 of that entry — `FockLangevinOperator` §21 computes that sign and finds it points the wrong way (`polyDrift_X`, `driftOperator_X`, `drift_X_single_eq`, and **`coreL1_single_lt_add_drift_X`**: the linear potential's drift *adds* mass on every basis vector, `ℓ¹(e_n + K_drift e_n) = 1 + (β²σ²/2)·2⁻¹ᐟ²·(√(nⱼ+1) + √(nⱼ))`), so a weighted `ℓ¹` is needed rather than a further norm; and `BookProof/MCMC/PositivityCone` (§22) proves the convergence in the cone model — `P 1 = 1` (`step_one`), cone and mass preservation (`step_nonneg`, `mass_step`), the Doeblin contraction `osc (P f) ≤ (1 − (m+1)δ)·osc f` (`osc_step_le`), **`tendsto_iter_step`** (every starting density converges to the invariant state `mass f / (m+1)` at rate `1 − (m+1)δ`) and its instance `tendsto_iter_uniformStep`; the Module 4–5 gap hypotheses are now cited from §18 (`module45_hypotheses_cited`, `module45_iterate_bound`); **and** §19 of that entry — §23 of the same module drops the uniform-target restriction: with a prescribed target `π` (`Target`), the Doeblin condition `ε π b ≤ Q a b` (`Minorant`) and stationarity (`Stationary`), the `ℓ¹` mass contracts by `1 − ε` (`sum_abs_sub_minorant`, `l1_apply_le`, `l1_apply_iter_le`) and **`tendsto_iter_target`** gives `‖f Qⁿ − π‖₁ ≤ (1 − ε)ⁿ‖f − π‖₁ → 0`, coordinatewise in `tendsto_iter_target_pointwise`; the concrete `targetKernel ε π` instantiates it (`targetKernel_rowStoch`, `targetKernel_minorant`, `targetKernel_stationary`, `tendsto_iter_targetKernel`) and `uniformStep_eq_targetKernel` identifies §22's kernel as the flat-target special case; **and** §20 of that entry — §24 of the same module derives §23's Doeblin condition for the Metropolis kernel: `mhKernel q π` (acceptance `mhAcc π a b = min 1 (π b/π a)`) is row stochastic by construction (`mhKernel_rowStoch`), satisfies `Minorant (mhKernel q π) π (δ/supv π)` when every proposal entry is at least `δ` (**`mhKernel_minorant`**, via `div_supv_mul_le` and `mul_mhAcc`), is reversible (`mhKernel_detailed`) and stationary (`mhKernel_stationary`), so **`tendsto_iter_mhKernel`** gives `ℓ¹` convergence to `π` at rate `1 − δ/supv π`; **and** §21 of that entry — §25 of the same module removes the target from the constant: `supv π ≤ 1` on a probability target (`target_le_one`), so the minorant is the proposal's floor `δ` (**`mhKernel_minorant_one`**) and the rate is `1 − δ` (`tendsto_iter_mhKernel_delta`, `l1_iter_mhKernel_le`), with the concrete symmetric proposal `uniformStep t` giving **`tendsto_iter_metropolis_uniformStep`** at rate `1 − t` for any probability target (`l1_iter_metropolis_uniformStep_le`); what remains is the single number `δ`  Its predecessor is the 2026-11-08 entry (`§9.3–§9.5`: the mode calculus, `polyMul_mul`, the derivative side), and the 2026-10-21 steps 0–3 are **not** superseded and remain open | `pcnl.md`'s Module 3 status prose — "the induction that *feeds*" §9.2, "the derivative polynomials `∂_j Φ` … not carried out here", and the operator composition with `∂ⱼ` — is superseded as a reading guide by the 2026-11-08 and 2026-11-08b entries for the pCNL/Module 3 track only; the rest of `pcnl.md` (Modules 1–2, 4–5, the review of the empirical claims) stands | — |

**The single most load-bearing supersession sentence for the book track** is buried inside
the 2026-08-27 wave block, not in any header: *"One plan that supersedes the per-thread
plans for future work"* — it absorbs everything still open from `BOOK_PROOF_PLAN.md`,
`PLAN_LEAN_SPECIALIST_UNPROVED.md`, `SPECIALIST_PLAN_REMAINING.md`,
`PLAN_LEAN_SPECIALIST_COHERENT.md`, `PLAN_A_BOOK_FORMALIZATION.md`,
`PLAN_B_PROSE_VERIFICATION.md`, `SINGULARITY_DETECTION_PLAN.md` and
`PLAN_A_EXECUTION_REPORT.md`. It sits inside the 2026-08-27 wave block, not in any header.

---

## Recent board entries — per track

> **What this section is.** The table above says *which document is authoritative*.
> This one says *what the shared board currently records* for the same track, so
> a specialist can see recent observations without reading the whole 16k-line plan.
> Entries are cited by **board cursor**, which is a stable monotonic id, not a line
> number — the same content-based discipline the rest of this file uses.
>
> **Where they come from.** `BOARD.ndjson`, the board's NDJSON snapshot, read by
> `scripts/board_rollup.py`. `Board::write` assigns no timestamp, deliberately: adding
> wall-clock would make the log non-deterministic, and the cursor ordering is what
> everything depends on. A month therefore comes from the snapshot's mtime unless a
> writer supplies `ts`.
>
> ⚠ **`BOARD.ndjson` is currently a seed corpus**, transcribed from the plan entries
> and flags this file already cites — not observations captured from live agent runs.
> It exists so the rollup path is exercisable and auditable before any agent writes
> to it. Treat these as restatements, not as new evidence; when real workers write
> entries they will carry the same shape and the same cursors continue.

| Track | Recent board entries |
|---|---|
| **NS** (Navier–Stokes) | cursor 2 `FACT` — `not_nsEnergy_surjective` refuted, so `nsKoopman_esa_of_energy_comparison` is vacuous as stated; cursor 3 `CLAIM` — `unfer_contracts/prob_kernel`, NS derivative fixing |
| **QYM** (Yang–Mills) | cursor 4 `FACT` — the one-particle form gap is the programme's top analytic input; cursor 5 `FAIL` — `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` §11.4 "closed" is superseded by its own later status block |
| **QG** (quantum gravity) | cursor 8 `FACT` — the density is a canonical variable; the record operator is pinned separately and is **never** the density |
| **SM** (Standard Model) | cursor 9 `CLAIM` — `HONEST_BOUNDARIES_SM.md`, fermionic completion boundary ledger; cursor 10 `FAIL` — `smComparison` as a comparison operator is refuted by the 09-23f wave though still defined and proved positive |
| **RandomMap** (RH) | cursor 1 `FAIL` — `AGENTS.md` still lists three already-proved items as next (see **F2**). No `CLAIM` recorded: this is the one track with no order and nobody has taken it |
| **book** (Verso / pedagogical) | cursor 12 `FAIL` — commit `7fa2b6c` added Orientation/Status to 48 chapters and appended no plan entry (see **F4**); cursor 6 `OBSERVED` — prose consistent with the 08-27 supersession wave |
| **mass-gap** | cursor 11 `FACT` — the order is §M4 in the 10-04 entry; §13 and `MASS_GAP_CERTIFIED.md` remain the detailed record but are superseded as a reading guide |

**Rolling up.** `python3 scripts/board_rollup.py --list-months` shows what is present;
`--month YYYY-MM --dry-run` prints the block without writing. The script **appends only**
— `CONSOLIDATED_PLAN.md` is append-only by house rule and this one never edits it — and
refuses to write a second rollup for a month that already has one, because a duplicate
would be indistinguishable from a correction. Use `--force` to append anyway; the earlier
block is kept rather than replaced. `FAIL` entries sort first, `OBSERVED` last and
usually not at all: they are conclusions-free notes, and surfacing them would bury the
entries that tell a specialist something.

---

## Flags — where the corpus contradicts itself

These are recorded, not resolved. Each names who would have to decide.

### ⚠ F1 — the `CONSOLIDATED_PLAN.md` header was stale *(fixed)*

The header read **"Start here (2026-09-25)"** and named the 09-25 entry as the newest,
while two newer entries followed it in the same file: **§10-04** (the mass-gap entry) and
**§10-04b**. The header mentioned neither. §10-04 is 11 commits of context the header never
saw, and it supersedes §13 for the mass-gap track.

*Fixed alongside this file:* the header now names the newest entry, points here, and states
that the RH track has no order. The 09-25 paragraph is **kept, not rewritten** — the house
rule is append, never delete.

**Side effect worth recording:** that edit shifted every line number below the header by 13,
which invalidated every positional citation this file had been drafted with. Hence the
content-based citation policy above. If you add a state entry to `CONSOLIDATED_PLAN.md`,
expect to re-verify any `file:line` reference elsewhere in the repo.

### ⚠ F2 — RandomMap/RH has no order, and three documents claim to have one

This is the one track with **no current work order at all**, and the only genuine hole in
the table above.

- `AGENTS.md`'s "Priority Attack Order for Next Agent" section publishes
  `uniform_variance_bound`, `jensen_bohr`, `convergent_series_has_no_poles`. All three are
  marked ***Sorry*** in its own Formalization State table. **They are already proved**:
  `FORMALIZATION_ROADMAP.md` lists them as "proved", and `CONSOLIDATED_PLAN.md` confirms
  the `RandomMap2` chain is "`sorry`-free in both trees". `AGENTS.md` is stale here, and it
  is the file an agent is most likely to read first.
- `IMPLEMENTATION_PLAN_RCP.md` declares itself, in its own first line, "**NEW STRATEGY
  (maintainer), AUTHORITATIVE. READ THIS FIRST.**" — a self-declared authority, last
  touched 2026-07-22.
- `FORMALIZATION_ROADMAP.md` says "**No UsedRoute/ or UnusedRoute/ work — RH work out of
  scope.**"

Meanwhile the open question has been on the table since August and never answered, in the
same paragraph that records the `sorry`-free chain: *"Confirm with the plan's RH section
whether the route `sorry`s are next in queue or parked behind the QG/QYM/operator thread."*
Corroborating signal: `DOC_INDEX.md` lists `RandomMap.md`, `RandomMap_old.md` and
`RandomMap2LegacyDraft.md` under **Never linked** — nothing in the corpus points at them.

*Needs an owner's decision:* is the RH route in the queue or parked? Until then this row
is deliberately empty rather than filled with a guess.

### ⚠ F3 — two `C` (conditional) NS items rest on a refuted reduction

§09-25 §5 item 3 keeps ESA of `N_NS` and of `N_L` as explicit **C** hypotheses. But §09-25
§2 records the mainstream surjectivity hypothesis as **refuted** — `not_nsEnergy_surjective`
(**N**), with `nsKoopman_esa_of_energy_comparison` "vacuous as stated" — and §3 repeats it.
The NS order was rewritten around a refutation and still names two unproved hypotheses.

Not a contradiction in the logic — an *ordering* hazard: an agent reading item 3 alone will
not see that the energy comparison it leans on was refuted. Read item 3 together with the
§2 NS row.

### ⚠ F4 — the last book wave landed with no plan entry

Commit `7fa2b6c` (2026-09-30) added Orientation and Status sections to 48 `Book/` chapters
— the most recent substantive work in the repo — and appended **no** corresponding entry to
`CONSOLIDATED_PLAN.md`. The nearest plan-facing artifact, `Book/ProofPlans.lean`, defers
elsewhere: *"A more detailed, machine-oriented version lives in `CONSOLIDATED_PLAN.md` at the
repository root."*

### ⚠ F5 — `ARISTOTLE_SUMMARY.md` claims a run whose artifacts are absent *(resolved 2026-10-16)*

The summary copied from `../internal-final_aristotle` (run `8c1a652e…`) describes
`BookProof/Ns/ChapterNsLagrangianComparisonEsa.lean` (`lagComparison_esa`, `lagKoopman_esa` —
the `N_L = H_L² + E` comparison proved ESA **with no extra hypotheses**), the
`ChapterKvnKato*` chapters newly imported from `BookProof.lean`, two added `#print axioms`
lines in `ChapterRoadmapAudit.lean`, and `§"2026-10-16"` entries in `STATUS.md` and
`CONSOLIDATED_PLAN.md`. None of these exist: no such files anywhere in the workspace, no
`§"2026-10-16"` entry in either document, and the claim contradicts the 2026-10-15c row,
which records the `N_L` hypothesis as **still explicit**.

*Search closed 2026-10-16 (negative).* The attachment `../internal-final_aristotle` was
searched exhaustively (`rg` over the whole tree, `.lake` included): no
`ChapterNsLagrangianComparison*`, no `ChapterKvnKato*`, no `lagComparison_esa`. The full
git history of all eight local repos under `/home/leo/Projects` (timepiece included —
`git log --all --diff-filter=A`, `--grep=8c1a652e`, `git stash list`, every reachable tree
via `ls-tree`) contains no commit that ever added these paths; neither do timepiece's
remote-tracking branches `origin/main` or `origin/aristotle-331`, and `git fetch
--dry-run` reports nothing new. The artifacts are therefore not restorable from anything
persisted in this workspace.

*Resolved 2026-10-16 (same day, later).*  The search above stands as a record — the
artifacts were in fact nowhere in the workspace, git history, or remotes — but the run's
contents arrived in the repo as `MISSING_FILES_CONTENTS.md`, the manifest of run
`e9b2b456`: full text of the eight modules (the seven `ChapterKvnKato*` chapters +
`ChapterNsLagrangianComparisonEsa.lean`), the `BookProof.lean` import line, the two
`#print axioms` lines for `ChapterRoadmapAudit.lean`, and the `STATUS.md` /
`CONSOLIDATED_PLAN.md` sections.  All were regenerated from it; every claim of
`ARISTOTLE_SUMMARY.md` §"2026-10-16" checks out against the restored files, the
`N_L`-hypothesis work-order step closed on the ordered route, and
`CONSOLIDATED_PLAN.md`'s final entry records the closure.  The "do not implement from
the summary" warning is lifted.

---

## Maintaining this file

1. **Append a state entry** to `CONSOLIDATED_PLAN.md`, in house style, with the
   supersession clause in its preamble.
2. **Repoint the affected row(s)** above at the new entry.
3. **Move** each predecessor from `current` to the appropriate superseded column — never
   delete a row, and never rewrite a superseded row's history.
4. **Update the header** of `CONSOLIDATED_PLAN.md` if the new entry is the newest.
5. **Cite by heading or quoted phrase, never by line number** — see the note above.
6. **Re-run** `python3 scripts/doc_index.py` — this file is indexed, and its `In`/`Out`
   counts are part of the corpus's link health.

If a row's `current` cell is empty, that is a finding, not an omission. F2 is what an
empty cell looks like when nobody has decided yet.

Related: `DOC_INDEX.md` (backlink graph, regenerated by `scripts/doc_index.py`),
`STATUS.md`, `HONEST_BOUNDARIES_SM.md` (the SM boundary ledger, the model for what an
honest track ledger should look like).