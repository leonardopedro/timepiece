# BOOKPROOF_SPLIT_PLAN.md — splitting `BookProof/` into logically independent parts, and the redundancy / legacy / dead-end inventory

Status: **plan only — nothing is moved, renamed or deleted by this document.**
Created 2026-10-17. Execution belongs to the LLM-Lean4-specialist (the house rule
stands: a phase compiles, this document does not). Pointers: `CONSOLIDATED_PLAN.md`
§"2026-10-17b" and the `BookProof layout` row of `CURRENT_WORK_ORDER.md`.

---

## 1. Measured current state (2026-10-17, all numbers from the repo itself)

| fact | value | source |
|---|---|---|
| top-level modules in `BookProof/` | **807** `.lean` files, **flat in one directory** | `ls BookProof/*.lean` |
| subdirectories | 86 directories holding **192** `X/PartN.lean` files | `find BookProof -mindepth 2 -name '*.lean'` |
| import-graph parts | **112** independent parts, **24** with more than one module | `scripts/import_components.py BookProof` |
| biggest part | `BookProofOperatorCore` — **477 modules, 119 roots** — one lake target | same report, `--check` green |
| other multi-module parts | `BookProofAttention` 75, `BookProofMeasureFoundations` 32, `BookProofFreeFieldBorn` 30, `BookProofRealification` 22, `BookProofInducedSystems` 20, `BookProofHarmonicAnalysis` 10, `BookProofGravityAlgebra` 9, 6 small parts of 2–5 modules (`Definability`, `Reconstruction`, `AtomicDecomposition`, `Holomorphic`, `Lorentz`, `WeylSL2`, `WignerOrbit`, `Bell`, `Causality`, `PauliGrover`, `Conservative`, `Density`, `EnergyBand`, `FieldStrength`, `Pauli`, `RoadmapAudit`) | same report |
| single-module parts | 88 (built individually by `lake build BookProof.Chapter<Name>`) | same report |
| orphans | **192 modules not imported by `BookProof.lean`** — "stale split copies `X/Part*.lean` of monolithic `X.lean` … not built, belong to no part. Deleting or wiring them in is a separate, deliberate decision." | plan §"2026-09-24…" Orphans bullet; `--check` note |
| scratch library | `Work/` 86 files, `Audits/` 6 files — never default targets | `lakefile.toml` comments |
| largest modules | `ChapterRoadmapAudit` 3314, `ChapterScalaronOuterFockFL` 1156, `ChapterQgOneParticleCcEsa` 1143, `ChapterFermionFock` 1063, `ChapterFockSecondQuantization` 996, `ChapterHermiteProductCore` 934, `ChapterSmBrstGhost` 932, `ChapterKvnKatoCalc` 901 … | `wc -l` |
| domain families (name-pattern counts, root files) | `ChapterNavierStokes*` 45 + `ChapterNs*` ≈ 30; `ChapterQg*` 34 + `ChapterQuantumGravity*` 5 + `ChapterScalaron*` 11 + `ChapterVielbein*` 3 + `Starobinsky`; `ChapterYangMills*` 19; `ChapterSm*` 18 + `ChapterParity*` 11; `ChapterSirk*` 26 + `ChapterHashimoto*` 6 + Ritz/Krylov/Crouzeix/Temple; toolbox names (`FarisLavine*` 18, `Stone*` 12, `Friedrichs*` 12, `Hermite*` 24, `Comparison*` 7, `Resolvent*` 6, `Carleman*` 6, `Tensor*`); `ChapterFock*` 54 (shared lift layer); `ChapterAttention*` 28 of the 75-module attention part; lettered textbook relics `ChapterA1…H9` ≈ 100 | counts above |
| junk sweep | `BookProof/faris_lavine_witness.lean`, `BookProof/ChapterYangMillsFockESA_tmp.lean`, `ScriptSketchInfo.lean`, `YNOT_IGNORED` — **absent as of 2026-10-17** (removed in the recent commits) | `ls` negative |

Ground rules this plan inherits:

* **Folder = module path in Lean 4.** `BookProof/X.lean` → `BookProof/<Area>/X.lean`
  renames the module to `BookProof.<Area>.X`. Every import, every `#check @BookProof.X…`
  in `Book/`, every `#print axioms BookProof.X…` in `ChapterRoadmapAudit.lean`, and every
  `BookProof/ChapterX.lean` path cited in `../test/*.md` (caught by
  `scripts/check-gitbook-drift`, part of `health.sh`) must move in the same step.
* **Folders do not change the import graph.** A folder is navigation, not a target.
  Independent *targets* already exist (the 112 parts). Making `Ns`, `Qg`, `Qym` … into
  separately buildable parts requires cutting **cross-domain imports**, which is a
  measurement-first job (step 2.1 below).
* **Append-only documentation.** `CONSOLIDATED_PLAN.md` gains entries; superseded rows are
  annotated, never deleted. Citations are content-based (no line numbers).
* **Honesty records are assets.** Negative theorems (refutations, vacuity proofs,
  deficiency-index witnesses) are what keep the corpus trustworthy — §4.C lists them so
  they are *classified*, never deleted.

---

## 2. Target layout

Folders under `BookProof/`, each name entering the module path exactly once. Keep the
`Chapter…` prefix inside folders so scripted renames stay mechanical:

```
BookProof/
  Toolbox/          FarisLavine*, EsaClosure*, Hermes*, Stone*, Friedrichs*,
                    Resolvent*, Carleman*, Comparison*, Kato*, Tensor*,
                    Weyl*/SL2*, Fock* (the shared lift/enclosure layer),
                    Phys*, Prelude, Substrate, Complexification,
                    Hermite/analysis cores, DegSchrodinger/KvnKato pipeline
  Ns/               ChapterNavierStokes*, ChapterNs*        (~75 modules)
  Qg/               ChapterQg*, QuantumGravity*, Scalaron*, Vielbein*,
                    Starobinsky, Gravity*, densitized/half-density transfer
  Qym/              ChapterYangMills*, YangMills* utilities
  Sm/               ChapterSm*, ChapterParity*, electroweak/yukawa/ghost
  Qed/              ChapterQed*, ChapterFreeEMField, abelian-sector reductions
  Sirk/             ChapterSirk*, Hashimoto*, Ritz, Crouzeix, Temple, Krylov,
                    Gram, band/certificate readers            (~40 modules)
  Ode/              ChapterOde*, chart/sampling/complexification chapters
  Probability/      the already-independent probability parts as folders:
                    MeasureFoundations/, FreeFieldBorn/, Realification/,
                    AtomicDecomposition/, Reconstruction/, InducedSystems/,
                    HarmonicAnalysis/, Definability/, Bell/, Causality/ …
  Attention/        the 75-module attention/ML research part (own target today)
  Textbook/         the lettered relics ChapterA1…A5, B, B3…B7, C, D, E, F1…F8,
                    G, G2, G3, H1…H9 (80 files) — old textbook-section numbering
                    (§4.B; renames optional, foldering mandatory)
  RoadmapAudit/     ChapterRoadmapAudit.lean (the #print axioms gate)
```

Two consequences stated deliberately:

1. `BookProofOperatorCore` (477 modules) keeps its name and stays one connected
   component until step 2.1's cross-import matrix says where the seams are; the folders
   above are where those seams will *fall*, not a claim that they already hold.
2. `Textbook/` and `Attention/` make the track-less material visible instead of silent:
   no `CURRENT_WORK_ORDER.md` row covers either; flagged for the plan owner either to
   adopt as a track or to move out of `BookProof.lean`'s cone (that decision is
   *outside* this document's authority).

---

## 3. Phased execution (each phase ends green or is not applied)

**Phase 0 — dead weight (no renames, no impact on the build).**
1. For each of the 86 orphan dirs `BookProof/X/Part*.lean`: diff the declarations of the
   parts against the monolithic `BookProof/X.lean`. The 2026-09-24 finding says they are
   stale *copies*; if any part still holds a declaration the monolith lacks, port it back
   first (that is the only legitimate reason the pair could differ, since
   `split_module.py` keeps the original name as a thin re-export).
2. `git rm -r` the 86 directories (git history keeps them).
3. Re-run `python3 scripts/import_components.py BookProof --check` (the stale-parts note
   must disappear) and `bash scripts/health.sh`.
   Acceptance: 807 modules unchanged, note gone, gates green. No `.lean` that
   `BookProof.lean` imports is touched.

**Phase 1 — folder the independent parts (mechanical, low risk).**
For each multi-module part except `BookProofOperatorCore` and `BookProofAttention`:
`git mv BookProof/<Chapter>.lean BookProof/<Part>/…`, then rewrite, in one commit:
* `import BookProof.<Chapter>` → `import BookProof.<Part>.<Chapter>` (whole-tree),
* fully qualified names in `Book/`, `ChapterRoadmapAudit.lean`, `Work/`, `Audits/`,
  `scripts/` fixtures, and `BookProof.lean`,
* the prose paths `BookProof/<Chapter>.lean` in `../test/` (drift gate).
Then `--write-lakefile`, `--check`, `doc_index.py`, `check_site.py` in `../test`,
`health.sh`, and the specialist's compile (`lake build` per part target).
Acceptance: every gate green in the same commit as the move; zero remaining references
to the old module paths (`rg -g '!*.md' 'BookProof\.<Chapter>\b'` empty for moved names;
`../test` drift 0 misses).

**Phase 2 — folder the core along §2, and measure the real seams.**
2.1 **Cross-import matrix first** (python: reuse `imports_of` in
`scripts/import_components.py`): for the 477 OperatorCore modules, emit
`domain × domain` counts of direct imports (Ns↔Qym↔Qg↔Sm↔Sirk↔Sirk↔Toolbox, using the
§2 name families). This is the only step that *knows* whether `Ns/`, `Qg/`, `Qym/`,
`Sm/`, `Sirk/` can become independent lake parts without moving modules — the seams are
where `Toolbox/` imports nothing from a domain.
2.2 Folderize OperatorCore per §2 (one area per commit, all gates, same recipe as
Phase 1). Order: `Toolbox/` last (every domain imports it; moving it multiplies
references) — first move the domains with zero inbound references.
2.3 Only if 2.1 shows a clean cut: introduce a `[[lean_lib]]` part per domain and let
`--check` verify roots; otherwise stop at folders and record the coupling as a finding.
Acceptance: `--check` green; `lake build BookProofToolbox` (or whatever the matrix
names it) builds the toolbox cone and nothing else; `#print axioms` audit unchanged
modulo paths.

**Phase 3 — renames and consolidations (optional, each its own PR).**
* Case-collision trio `ChapterWeylSl2` / `ChapterWeylSL2Unipotent` /
  `ChapterWeylSL2Group` — read, merge or rename to one convention (`Sl2` vs `SL2` is a
  platform hazard on macOS checkouts).
* Legacy unprefixed utilities (`FarisLavine.lean`, `EsaClosure.lean`, `HermiteCore.lean`,
  `NavierStokesFlow.lean`, `PhysHSGaussian.lean`, `Substrate.lean`, … 17 files) gain the
  `Chapter`/domain prefix so `rg 'Chapter<Domain>'` finds them; citations in `Book/` and
  `../test` updated with them.
* Lettered `Textbook/` chapters: rename only where cite-density is low; otherwise folder
  alone. Every rename is content-citation-checked (`verify-invariants` pending list).

**Phase 4 — perpetual gates.**
`health.sh` (doc index, import gate, gitbook drift), `verify-invariants`,
`check-links`, `../test` `check_site.py`, and the specialist's compile + book render
(`./patches/build-book.sh`, `check-katex.sh`) after each phase. `scripts/propose_split.py`
→ `scripts/split_module.py` for the >1000-line modules (`ChapterRoadmapAudit` is the
audit itself; the others split only in `Work/` first, per that script's contract).

---

## 4. Redundancy / legacy / dead-end inventory

### A. Redundant — delete candidates (Phase 0)

| item | count | why redundant | action |
|---|---:|---|---|
| `BookProof/X/Part*.lean` orphan dirs | 86 dirs / **192 files** | not imported, not built; stale split copies of the monolithic `X.lean` that already exists at top level (`--check` classifies them "belong to no part") | declaration-diff vs `X.lean`, then `git rm -r` |
| Worktree junk (`chapter*-tmp`, `*_witness`, `ScriptSketchInfo`, `YNOT_IGNORED`) | 0 today | already gone in the 2026-10-16/17 commits | verify-only: `git status --porcelain` stays clean of them |
| duplicated gate | 0 today | `check-mass-gap-spec-parity` fork already deleted (2026-10-12, S2) | verify-only |

### B. Legacy / superseded — keep, but out of the critical path (folder + annotate, never delete)

| item | status per the record | where |
|---|---|---|
| `ChapterNsKoopman`'s **Leray-energy comparison leg** (`nsKoopman_esa_of_energy_comparison`) | hypothesis `hsurj` unsatisfiable → "vacuous as stated"; the leg was *rebuilt* by `ChapterNsLinearKoopmanEsa` (affine/Oseen instances) and `ChapterNsNonlinearFarisLavine` (square comparison) | refutation in `ChapterNsEnergySurjectivityObstruction`; moved to `Ns/` with a legacy annotation in its header |
| QG-D-C routes **R1 (Chernoff/Strichartz) and R2 (fiberwise FL)** | superseded 2026-10-17 by the factorisation route of `ChapterQgFlatContinuumEsa`; `ChapterQgContinuumFiniteSpeed.lean` was ordered and never written — it does not exist and should not be created | plan §"2026-10-17"; no files to move |
| classical-geometry **exploration/legacy cluster** — Bianchi, field strength, SU(3) structure constants, `ChapterBRSTNilpotent`, `ChapterGhostField`, `ChapterSuperBracket`, `ChapterGaugeFixing` | "supporting vocabulary, not route items" (plan quote); the field-space differential realization "was decided against" | keep in `Qym/Vocabulary/` + `Sm/Vocabulary/`; decision recorded in plan §(2026-09-25) |
| `smComparison` as a *comparison operator* | **refuted** by the 2026-09-23f wave; the operator itself stays defined and positive because the fermionic completion needs it | `CURRENT_WORK_ORDER.md` SM row; annotate the chapter header when it moves to `Sm/` |
| lettered textbook chapters `ChapterA1…A5, B…B7, C, D, E, F…F8, G, G2, G3, H…H9` and 17 unprefixed utilities | old numbering scheme; several are live roots of parts today (`ChapterA3*` = the former `BookProofLieRep`, `ChapterA4*`, `ChapterB7`, `ChapterF2/F4/F8`, `ChapterG3`, `ChapterH2/H3`) | folder to `Textbook/` (Phase 2/3); **rename only after cite-density check** — `verify-invariants` recalls them |
| attention/ML side line (`ChapterAttention*`, `Coherent*`, `Softmax*`, `DeepLearning*`, `ThermalMax*`, `LayerNorm`, `MarkovEntropy`, `Consciousness*`, `ComputableScarcity`) — 75-module part | builds as its own target, **but no `CURRENT_WORK_ORDER` row covers it**: track-less by record, not by neglect | keep as `Attention/`; **decision needed**: adopt a track or drop it from `BookProof.lean`'s cone (not this document's call) |
| `ChapterWeylSl2` vs `ChapterWeylSL2Unipotent` / `ChapterWeylSL2Group` | case-variant naming, possible content overlap — *suspected* redundancy, unread | Phase 3 review; do not touch blind |
| `scripts/split_module.py` leftover `PartN` name blocks inside `lakefile` | none today (gate green) | verify-only |

### C. Dead ends — honest negative records: **retain, build, never consume as positive input**

107 files carry `not_` / `false_` / `*_not_*` theorem declarations; they are the boundary
the corpus is honest with. Named inventory (each is a *theorem*, i.e. load-bearing):

| theorem / chapter | what is dead (and why that is the point) |
|---|---|
| `not_nsEnergy_surjective`, `nsEnergy_hsurj` obstruction chapter | surjectivity of `N_E + 1` from the Gauss core — the energy-comparison leg's input, impossible in every `d ≥ 1` (Baire) |
| `not_farisLavine_criterion_of_relative_bound` | the pattern "commutator + relative bound without ESA" — why `N` cannot be chosen by fiat |
| `nsKoopmanOp_not_bounded_below`, `nsKoopmanOp_not_positive`, `quadP_starP` | the Hamiltonian itself can never be the positive `N` (indefinite spectrum, antiunitary symmetry about 0) |
| `nsResPoly_not_affine` | "NS is secretly an Oseen linearization" — false by computation |
| `leadCoeff_volumePoly`, `not_unit_volumePoly` | the volume monomial is not a unit → the constraint determinant cannot be eliminated by substitution (why NS carries `det F` by hand) |
| limit-circle family: `ChapterHalfLineLimitCircle`, `ChapterLimitCircleExample`, `ChapterConformalFiberDeficiency`, `ConformalSignFlip.wrongSignKinetic_esa_iff` | the opposite-sign conformal fibre: deficiency indices `(2,2)` — the theorem QG-D-C.1 needs its sign condition *for* |
| `ChapterNavierStokesDeficiency`, wall obstruction `ChapterWallDeficiencyObstruction` | where ESA fails (walls, degenerate fibres) — the datasets for boundary decisions |
| `ChapterFockCubicUnbounded` (bare cubic has no relative bound) | kills "cubic alone stabilizes the Fock space" — why the normal-ordered quartic row exists |
| `ChapterTempleSeparationNecessary` | no spectral-edge estimate without a separation hypothesis — why certified bands exist |
| `ChapterYangMillsAbelianNoGap`, `ChapterScalaronNotQuadratic`, `ChapterNoLebesgue`, `ChapterNoBestPrior`, `ChapterNoUniformCountable`, `ChapterConsciousnessNullMeasure`, … | scoped negative results for their questions |

Policy: these stay in the **default build** (they are `#print axioms`-audited like
everything else), get foldered with their domain, and are cross-listed in
`scripts/pending-lemmas.txt` style if a citation ever needs a "[boundary]" reading. A
negative record is never rewritten to make a route work; a route that needs it to be
false is the route that changes.

### D. What is *not* redundant (checked, so nobody re-props it)

* `BookProof.lean` aggregator, `ChapterRoadmapAudit` — the axiom audit itself.
* `ChapterProve2meReuse` and friends with odd names — cited by live plan rows
  (`ChapterEsaFarisLavineIndex` roots); reviewed, kept.
* Every `ChapterKvnKato*` chapter and `ChapterNsLagrangianComparisonEsa` / `Lifted` /
  `Qg*Transfer` / `QgFlatContinuumEsa` — the 2026-10-15c/16/17 closures.
* `Work/` (86 files) and `Audits/` (6) — already outside the default target by design;
  Phase 0 does not touch them.

---

## 5. Acceptance checklist (whole document)

- [ ] Phase 0: 192 orphan files declaration-diffed, then removed; `--check` note gone;
      `health.sh` green in the same commit.
- [ ] Phase 1: every independent part sits in its folder; `rg` finds no stale module
      path; `../test` drift gate 0 misses; part targets build (specialist).
- [ ] Phase 2: cross-import matrix published as an appendix of this file; folders per
      §2 exist; any new `[[lean_lib]` part is `--check`-green before it is written to
      `lakefile.toml`.
- [ ] Phase 3: each rename has its cite-density check and a `verify-invariants` run.
- [ ] §4 tables are mirrored in `CONSOLIDATED_PLAN.md` §"2026-10-17b" and the
      `BookProof layout` row of `CURRENT_WORK_ORDER.md` (done at creation).
- [ ] No phase compiles nothing: every phase lists the exact `lake` commands for the
      LLM-Lean4-specialist; this document itself was produced without compiling.