# BOOKPROOF_SPLIT_PLAN.md — splitting `BookProof/` into logically independent parts, and the redundancy / legacy / dead-end inventory

Status: **plan only — nothing is moved, renamed or deleted by this document.** (Executed 2026-10-18/19: Phases 0, 1, 1.5, 2, 3 and the runnable Phase 4 gates — see §9.)
Created 2026-10-17. Execution belongs to the LLM-Lean4-specialist (the house rule
stands: a phase compiles, this document does not). Pointers: `CONSOLIDATED_PLAN.md`
§"2026-10-17b" and the `BookProof layout` row of `CURRENT_WORK_ORDER.md`.

**2026-10-18 Prove2.me addendum** (same house rule): §6 records the exploration of
the prove2.me platform (missions + other authors' proofs), the downloaded proof
sources and where they will land after conversion; Phase 1.5 was added for that
conversion; §7 lists the platform missions/proofs this corpus can feed; §8 extends
the same treatment to the sibling projects `../unfer` and `../dynamic-arctic`
(70 more downloads in 4 sibling-earmarked groups; `../australVM` and `../emthin`
were searched for and do not exist in this workspace — earmarks deferred).
Downloads live in `Downloads/` at this repo's root (moved here from
`../prove2me_workspace/` on 2026-10-19; untracked, so no gate of this repo
sees them until they are converted on their target side). The platform import
closure for the solution sources lives in `Downloads/_deps/` (see §6.B).

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

Three consequences stated deliberately:

0. **Prove2.me imports land in `Toolbox/` as a `Prove2me/` subfolder** (namespace
   `BookProof.Toolbox.Prove2me.*`), not into domain folders: imported results are
   generic operator-theory / Wick / concentration tools until a domain chapter
   adopts one and cites it (Phase 1.5, §6). Raw, unconverted downloads stay in the
   staging area `Downloads/<group>/` (+ `Downloads/_deps/` for the platform
   import closure) and never sit inside this repo's build cone.
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

**Phase 1.5 — Prove2.me imports: convert, adopt, audit (independent of Phase 1).**
For each group of §6 (start with `operator-qm`, then `analytic-nt`, `prob-concentration`):
1. Convert the downloaded solution source to this repo's toolchain
   (`leanprover/lean4:v4.28.0` + this repo's Mathlib pin): the downloads target the
   platform's pinned Mathlib rev (`0df444a360ea`, two items on `c5ea00351c28`), so
   expect renames and lemma-name drift — the conversion diff is part of the record.
2. Rename into `BookProof/Toolbox/Prove2me/` with the namespace
   `BookProof.Toolbox.Prove2me.<Author>.<ShortName>`; keep a header block carrying
   the platform `theorem_id`, the original name, the submitting author, and the
   Apache-2.0 attribution (site terms, public contributions).
3. Wire into `BookProof.lean`, then `--write-lakefile` + `--check` (the converted
   modules join `BookProofOperatorCore` unless the cross-import matrix of step 2.1
   says they are standalone — most are).
4. `#print axioms` each new declaration in `ChapterRoadmapAudit.lean`; acceptance
   is `propext, Classical.choice, Quot.sound` only.
Do NOT convert during Phases 0–1: the folder renames of Phase 1 would invalidate
conversion diffs, and the conversion diff is the honesty record that the import
was faithful.

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

- [x] (2026-10-18, §9: 183 Part files removed; 2026-10-19b: the 9 remaining orphans were declaration-free stubs and are removed) Phase 0: 192 orphan files declaration-diffed, then removed; `--check` note gone;
      `health.sh` green in the same commit.
- [x] (2026-10-18, §9; `../test` drift not runnable here) Phase 1: every independent part sits in its folder; `rg` finds no stale module
      path; `../test` drift gate 0 misses; part targets build (specialist).
- [x] (2026-10-18, §9: matrix appended, no clean cut; 2026-10-19b: the 237-module residue foldered by reading, 1 module stays flat by decision) Phase 2: cross-import matrix published as an appendix of this file; folders per
      §2 exist; any new `[[lean_lib]` part is `--check`-green before it is written to
      `lakefile.toml`.
- [x] (2026-10-19b, §9: Weyl trio unified as `ChapterWeylSL2Algebra`; 7 utilities and the lettered chapters kept by cite density) Phase 3: each rename has its cite-density check and a `verify-invariants` run.
- [x] (verified 2026-10-19b) §4 tables are mirrored in `CONSOLIDATED_PLAN.md` §"2026-10-17b" and the
      `BookProof layout` row of `CURRENT_WORK_ORDER.md` (done at creation).
- [x] (2026-10-18/19: every executed phase ended with `lake build BookProof` green) No phase compiles nothing: every phase lists the exact `lake` commands for the
      LLM-Lean4-specialist; this document itself was produced without compiling.
- [x] (2026-10-18/19, §9: all 161 manifest solutions converted, compiled and audited in `converted/`; the one stray non-manifest file stays blocked, `converted/GAPS.md`) Phase 1.5: every imported proof converted, namespaced
      `BookProof.Toolbox.Prove2me.*`, attribution header present, `--check` green,
      `#print axioms` clean; the conversion diff archived next to the download.
- [ ] §6 downloads stay in sync with `Downloads/manifest.json` (+ `_deps/manifest.json`
      for the platform modules; regenerate both when re-running a fetcher; never edit
      by hand).
- [ ] (perpetual; `Downloads/manifest.json` unchanged since import, the fetcher was not re-run) §6 downloads stay in sync with `../prove2me_workspace/Downloads/manifest.json`
      (regenerate the manifest when re-running the fetcher; never edit by hand).

---

## 6. Prove2.me: exploration and downloads (2026-10-18, addendum)

The prove2.me platform (Lean 4 formalization platform; API
`https://prove2.me/api/v1`, release 0.12.7) was explored end-to-end with the
prove2me_workspace skill (`../prove2me_workspace/SKILL.md`). Credentials: the old
API key expired 2026-10-15 (`PIPELINE_PLAN.md` §2.54 of the workspace repo); a new
key was supplied 2026-10-18 and stored in `../prove2me_workspace/credentials.json`
(gitignored, valid ~30 days).

### 6.A What is on the platform (relevant slice)

| fact | value |
|---|---|
| missions catalogued | **4,639** (2,305 open / 2,334 completed) |
| relevant fields (mission counts) | functional-analysis 228, mathematical-physics 246, analysis 306, PDE 92, dynamical-systems 160, harmonic-analysis 52, calculus-of-variations 14, quantum-gravity 5, quantum-geometrodynamics 1, general-relativity 2, statistical-mechanics 1, condensed-matter-physics 1 |
| our footprint (`leonardopedro`) | **7,322** `BookProof.*` theorems mirrored: **6,062 proved**, 712 open, 544 definitions, 4 disproved |
| other authors with directly usable proved material | `Lucas` (QFT: Wick/Feynman/Dirac/Yukawa/Connes-RZ/Hamburger/ClassNumber…), `Shuze Chen` (OAI: DirectCrouzeix, bosonic Fock ladders, thermal generators, Markov-chain CLT), `cm_beta` (`FamousTheorems.*`: Gelfand–Naimark, spectrum, Hahn–Banach, Krein–Milman, mean ergodic), `mikedeng1` (Teschl QM & Hunter PDE series, matrix tail bounds, trace estimation), `dbenbenn` (Lawler–Sokal/Cheeger), `Grace`, `Hartmann_Psi`, `Aphrodite` (concentration), `raresbuhai` (Helfgott/Green–Tao), `wurtle` (quasi-RH 7/8), `junyihjy` (Grünbaum), `Nickrobbins95` (Rellich), `waitingintime` (Weil-defect sesquilinear), `Community (Bot)` (Courant–Fischer/interlacing) |

Selection rule for downloads: proved theorems **by other authors** that duplicate or
generalize machinery this repo either proved on its own or still lacks. Our own
`BookProof.*` mirror was excluded (already the corpus; no re-download).

### 6.B What was downloaded (sources only — nothing converted yet)

Location: `Downloads/<group>/<name>.lean` + `Downloads/manifest.json`
(93 manifest entries; **91 solution sources** + 2 statement-only; 2.2 MB; every
source `sorry`-free, verbatim platform submission). Manifest carries per item:
`theorem_id`, formal statement, natural-language statement, source paper, author,
accepted submission id/date, platform Mathlib rev.

| group | files | contents | destination after Phase 1.5 conversion |
|---|---:|---|---|
| `operator-qm` | 12 | Teschl QM series: self-adjoint extensions & defect indices, unbounded spectral theorem, Kato–Rellich, min–max/Temple, Weyl limit-circle/limit-point alternative, Herglotz–Stieltjes, RAGE, harmonic oscillator; Sturm–Liouville eigenfunction expansion; Hunter PDE: Lumer–Phillips semigroups, Rellich–Kondrachov | `Toolbox/` ESA-closure layer — feeds `ChapterKatoRellichDeficiencyCore`, limit-circle chapters, `ChapterStone*`, `ChapterResolvent*`, `ChapterTemple*` |
| `cstar-gelfand` | 10 | `FamousTheorems.*`: Gelfand transform bijective/formula/Mazur, spectrum nonempty, spectral radius = norm (self-adjoint), Banach–Alaoglu, Hahn–Banach separation, Krein–Milman, von Neumann mean ergodic, ergodic = extreme invariant | `Toolbox/` + Koopman line (`lagKoopman_esa` supports) |
| `crouzeix-convex` | 6 | `OAI.DirectCrouzeix.*` resolvent/Faber-calculus machinery, exp-level holomorphy, positive blocks; Lawler–Sokal Cheeger inequality (Dirichlet eigenvalue); Grünbaum extreme-point steps | `Sirk/` — `ChapterSirkCrouzeixNumericalRange`, `ChapterCrouzeixSelfAdjoint`, gap table |
| `fock-ladders` | 12 | `OAI.*` n-mode bosonic Fock ℓ²(ℕⁿ) ladder algebra: beam-splitter generators, weighted raising/lowering, weak-operator & dissipator pairing identities, thermal-generator / photon-number machinery | `Toolbox/Fock` — `ChapterFockSecondQuantization`, `ChapterFermionFock`, thermal/entropy chapters |
| `qft-wick` | 28 | Wick/Isserlis theorem + Gaussian moments + pairings; Feynman 1948 path-integral step & Fresnel integrals; Dirac slash²; Yukawa Fourier transform; Giddings1999 QG boundary Wronskian; QED field equations; Koch Hartree–Fock Brillouin; Chatterjee QFT one-particle spaces; Uhlenbeck gauge; graphene Dirac cone; undecidable spectral gap; BCS gap ratio; Weinberg boson spectrum; minimal-SM neutrino; high-entropy classical limit; Cl(6,0) Casimir spectrum | `Qg/`, `Sm/`, `Qed/`, `Toolbox/Fock` |
| `analytic-nt` | 12 | zero-free half-plane Re(s) > 7/8 (wurtle); Connes–Weil positivity ⇒ RH; Ramanujan–Petersson L-function functional equation & summability; Dedekind-zeta residue = coefficient average; Hamburger moment problem + Carleman-type uniqueness (factorial bound); Davenport three-primes (Siegel–Walfisz); ζ(0) port; Helfgott Möbius energy bound; ζ(5) irrationality (Zudilin / Hankel determinants) | RH analytic route — `jensen_bohr` (Bohr–Cahen), `ChapterCarleman*`, `zeta_no_zeros_right_half_plane` |
| `prob-concentration` | 7 | two-sided Azuma–Hoeffding martingale bound; Markov-chain CLT; conditional Khintchine; weighted Bernstein; Hutchinson trace estimation; Bernstein q-moment + Markov-tail concentration | probability chain — `uniform_variance_bound`, RandomMap2, `Var_X_bound` |
| `matrix-spectral` | 2 (+2 stmt) | Courant–Fischer and Cauchy interlacing (statement-only: no accepted submission source retrievable — recorded honestly in the manifest); max-degree spectral bound; A² = c·I eigenvalue lemma | RandomMap2 / SIRK Ritz |
| `misc` | 3 | Weil-defect sesquilinear Gram realization & Hermitian-form additivity; Koopman finite-dynamics eventuality | `Toolbox/` |

Known gaps (manifest `failures`, kept deliberately): `OAI.DirectCrouzeix.FaberCalculus`
is a platform Definition (no stored solution); `courant_fischer` and
`cauchy_interlacing_sorted` are Proved but expose no accepted submission source.

Conversion is **deferred by instruction**: Lean 4.28.0 conversion happens later
(Phase 1.5), never in the same step that touches the folder layout.

---

## 7. Prove2.me missions / open proofs this corpus can feed (2026-10-18)

The platform already mirrors 6,062 proved `BookProof.*` theorems under our account
(`leonardopedro`), so the corpus can be cited directly as lemmas inside
proof-sketch reductions (`POST /verify` sketches importing platform theorems;
children auto-resolve). Mechanics per the skill: connect to a mission's milestones
(`GET /missions/:id/milestones`) — orphan subtrees earn no score — and read each
milestone's history for rejected formalization paths before attacking. Mission ids
are listed so the solver session can go straight to `GET /missions/:id`.

### 7.A Open missions / theorem trees that overlap our proved assets

| mission / open theorem (id) | captain | our proved assets that map onto it | honest caveat |
|---|---|---|---|
| Formalize Navier-Stokes — `NavierStokes.existence_and_smoothness_R3` (mission 953b89b7) | korbonits | the ~45 `BookProof.NavierStokesFlow.*` / `ChapterNavierStokes*` chapters, incl. platform-proved `ns_hamiltonian_essentiallySelfAdjointOn`, `fock_ns_hamiltonian_…`, Carleman hops, Lagrangian comparison ESA | our route proves **ESA + comparison-operator structure of the Fock/enclosure Hamiltonian**, not classical ℝ³ Leray regularity; only milestone lemmas that are genuinely operator-theoretic should be attacked with our material |
| Yang–Mills mass gap (open trees `YangMillsMassGap.yang_mills_existence_and_mass_gap` and `YangMills.existence_and_mass_gap`, both by Lucas/korbonits) | (open theorems; Clay/Jaffe–Witten statements) | `ChapterYangMills*` 19 chapters (band bounds, ESA, certificate seam), the vendored QYM mass-gap contract (`unfer_contracts/MASS_GAP_SPEC.md`), `ChapterSirk*` certificate machinery — literally the same object | the platform statement demands constructive spectral gap for every compact simple G; our chain certifies the gauge-fixed one-particle lattice/enclosure Hamiltonians — feed milestones of the analytic-type sub-lemmas first |
| The complete Crouzeix theorem (missions 09579e9d, a699cf50) | wurtle | `ChapterCrouzeixSelfAdjoint`, `ChapterSirkCrouzeixNumericalRange` + the downloaded `OAI.DirectCrouzeix` machinery | matrix-numerical-range results are the finite-dim core; the Hilbert-space completion is the open part |
| Sharp one-dimensional Lieb–Thirring constants (mission 7fdd065b) | wurtle | Faris–Lavine toolbox (`ChapterFarisLavine*` 18), `ChapterFockCubicUnbounded` (the negative bound), relative-bound machinery | sharp constants need the 1D Schrödinger input we do not have |
| Teschl QM open series: OneParticle ESA & essential spectrum (397f61c5), Weyl relatively compact perturbations (99ebf092), Atomic HvZ (9795f718), TraceClass (25fc7ee6), Scattering wave operators (a5feda4a) | mikedeng1 | our ESA closure layer: `ChapterEsaClosure*`, wall-ESA/deficiency datasets, `ChapterFriedrichs*`, tensor-core ESA | each mission pins Teschl's exact statements; port faithfully rather than citing our chapter names |
| Spectral Gap Conjecture, random SU(2) (mission ca46da98) | Lucas | spectral-gap/certificate machinery (`ChapterSirkGapTable`, Cheeger download), boundary record `UndecidableSpectralGap` (already proved there) | group-random-walk input is number-theoretic, not ours |
| User-Friendly Tail Bounds for Sums of Random Matrices I–V (missions e6254467, e12ada41, 54113457, 97673b33, 28d03443) | mikedeng1 | matrix/martingale concentration downloads + RandomMap2 chain + `Var_*` toolbox; Hutchinson trace estimation already there | matrix-valued; our chain is scalar/probabilistic — use as the bridge lemmas, not wholesale |
| Bakry–Émery Curvature-Dimension series (missions 111a6f25, cdd71fd7, 5c93db1b, 858cf705, 44d5eec3, 77c7c693) | mikedeng1 | KvnKato Lyapunov comparison (`lagKoopman_esa`, `lyapunovComparison_esa_poly`), semigroup chapters | Ricci-geometry hypotheses are beyond our corpus |
| RH-adjacent open trees: Lindelöf (b41789a6), Weil Conjectures (8b573f13), Class Number Formula (cc969585), Ramanujan–Petersson (b2db41fc) | Lucas | `zeta_symm`, zero-free strip, `eta_non_zero_real_axis`, the Bohr–Cahen/`jensen_bohr` route; Connes–Weil chain (waitingintime's `ConnesGreen`/`ConnesWeilArithmetic` missions) | analytic-NT milestones are far from the probabilistic regularization route — contribute only the genuinely analytic sub-lemmas (zeta reflection, zero-free half-planes) |
| Lattice Hamiltonian simulation I/II (missions c54e7754, 5b274206) | mikedeng1 | mass-gap lattice comparison layers (marked comparison-only in our conventions) | our lattice objects are comparison models; the formalization object stays the continuum Hamiltonian |

### 7.B Gaps on the platform that only this corpus fills — mission proposals

1. **No Bohr–Cahen / Dirichlet-series continuation mission exists** (searches for
   Bohr–Cahen/Dirichlet series return only Bohr *sets* and L-function setups). Our
   RH analytic route (`jensen_bohr`, `convergent_series_has_no_poles`,
   `uniform_variance_bound` — the three recorded `sorry`s) is a ready-made mission
   proposal under the prove2me_workspace captain flow
   (`references/mission_captain.md`; milestones verbatim from the plan's own work
   order; the human audits and launches).
2. **"Fock-enclosure ESA for NS/QG/QYM" mission**: the 712 open `BookProof.*`
   platform theorems are exactly the open leaves (`dGamma_essentiallySelfAdjointOn_…`,
   `nsComparison_ikebeKato`, `wave_add_boundedPotential_…` — see
   `../test/mathematical-foundations/proof-plans.md`). A mission over them turns our
   internal work order into a public leaderboard-visible campaign, and other agents
   can attack leaves that currently sit only in `CURRENT_WORK_ORDER.md`.
3. **Full-project upload** (`references/upload_full_project.md`): the workspace
   pipeline already mirrored 7,322 theorems; the remaining step for reuse is
   publishing the shared `Definitions/` bundles so foreign reductions can import our
   operators (dΓ, comparison operator `N_L`, certificate structures) without
   re-deriving them.

Honesty rule carried over from §4.C: we contribute boundary/negative records (e.g.
the limit-circle `(2,2)` family, `not_nsEnergy_surjective`) as *boundary* lemmas on
the platform too — a mission that needs one of them false is the mission that
changes, never the record.

---

## 8. Sibling-project imports: `../unfer`, `../dynamic-arctic`, `../australVM`, `../emthin` (2026-10-18)

The same exploration was run against the needs of the sibling repositories.
Recon findings (read, not guessed): `../unfer` is the Rust probability kernel
(SIRK solver, nested-Fock CAS, QFM + HMC/Bayes, logos confluence hashes, nanoda
Lean verification via `prob_kernel::verify::verify_export`, mass-gap contract);
`../dynamic-arctic` is the Arctic threshold-Schnorr + Shine robust-VPSS authority
(`arctic_core`/`shine_core`/`lagrange`). **`../australVM` and `../emthin` do not
exist anywhere in this workspace** (unfer's AGENTS references an `australVM`
`UNFER_SYMBOLS` list, so it is real but absent here); no theorems are earmarked
for them until the plan owner supplies the paths — recorded, not papered over.

### 8.A What was downloaded (second batch: 70 sources, all `sorry`-free)

Same staging area and manifest as §6.B: `Downloads/<group>/` + `Downloads/manifest.json`
(now 163 entries / 161 solution files; a `sibling_projects_note` field records the
earmarks).  **2026-10-19:** `Downloads/_deps/` added — the 723-module verbatim import
closure (542 `Def_` + 181 `Thm_` statement stubs) for all 161 solution sources,
fetched from the API so the sources elaborate without the platform; audit in
`Downloads/_deps/README.md`.

| group | files | contents | feeds (sibling component → item in their AGENTS/README) |
|---|---:|---|---|
| `unfer-sirk` | 19 | SVD existence; nuclear-norm dual achiever + von Neumann trace duality (Candès–Recht); Danielson–Lanczos FFT split; Riccati PSD fixed point (exists+unique+convergent, closed-loop stable); Gershgorin; Hellinger–Toeplitz; Faber coefficient bounds + analytic-domain core + cross-boundary estimates (DirectCrouzeix); spectral unitary exponential `exp_spectral`; Neumann-series certificates with λ ≤ 1/8; trace-square compression & multiplicity bounds; unbounded self-adjoint domain; Liouville flow-volume | `fock_sirk` whitening/eigendecomposition (SVD, trace duality), inverse-free Neumann certificates (SIRK's whole design), Padé/unitarity (`exp_spectral`), Hashimoto band ceilings & Rayleigh–Ritz sharp tier (quadratic-form bounds, Riccati), `ode_sirk` flow |
| `unfer-bayes` | 19 | Gaussian integration-by-parts; OU semigroup commutation/invariance/entropy derivative; Gaussian log-Sobolev bounded below; Hermite moments of Gaussians (Krivine/Mehler kernel); Gaussian KL formula; `−p log p ≤ cq` cross-entropy; Gibbs attains spectral minimum; Gibbs form-energy identity; high-moment summability; Fock-spectral regularity on ℓ²(ℕⁿ); entropy ≤ thermal cross-entropy; photon-number regularizer minimum; three-state posterior score; Markov-chain α-mixing rate | QFM Mehler vacuum prior + Hermitian coupling flow (OU/Gaussian machinery), HMC posterior layer (`qfm::bayes`), Born-rule/thermal readout (Gibbs on Fock), posterior concentration |
| `logos-confluence` | 8 | Abstract Church–Rosser; Church–Rosser for free-group word reduction; Knuth–Bendix Newman's lemma; Merkle opening completeness + root binding; almost-lossless collision probability + silent-error ⇒ collision; SUBSET SUM NP-complete (Cook–Levin) | `logos` CNL→UNF confluence self-check (free-group reduction = word normal forms), `unfer_data::release` CID manifest (Merkle binding), `decide_core` |
| `arctic-crypto` | 24 | Full Schnorr σ-protocol suite (completeness, perfect HVZK, honest = simulated, special soundness w/ extractor, soundness error ≤ 1/q, ROM union bound, challenge-counting lemmas, group bridge `gexp_injective`/`orderOf`); OR-composition special soundness; Shamir: perfect privacy, reconstruct from d+1, d shares fail; Lagrange interpolation uniqueness; Byzantine interactive consistency (authenticated + oral + impossibility boundary); discrete log via HSG (Shor); unconditional Fiat–Shamir failure (boundary) | `arctic_core` (Arctic = threshold Schnorr; the σ-protocol suite is its core spec), `shine_core` robust VPSS (Shamir + Lagrange), `MintAuthority::Threshold` t-of-n (interactive consistency, incl. the impossibility boundary), `lagrange` |

### 8.B Restructure consequence (routing rule, added to Phases 1.5/2)

Sibling-earmarked groups do **not** enter `BookProof/Toolbox/Prove2me/` — that
namespace is this repo's own toolbox. Two channels, both gated:

1. **`unfer` channel (precedent: `Layout/`).** Pure-kernel-rfl certificates in
   this repo, exported through lean4export to NDJSON fixtures re-verified by
   `nanoda` inside `unfer` (`layout_bijective` is the working example). Converted
   `unfer-sirk` / `unfer-bayes` / `logos-confluence` material that wants this
   channel becomes zero-import `Layout`-style modules first; anything requiring
   Mathlib stays in this repo's `Toolbox/Prove2me/` and is cited by the vendor
   seams (`unfer_contracts/`) instead.
2. **`dynamic-arctic` channel (out of this repo's build).** The `arctic-crypto`
   group converts inside `../dynamic-arctic`'s own Lean surface when one exists;
   this plan only records the earmark and the manifest groups. If that repo later
   wants a `Layout`-style certificate folder, the §6 recipe (namespace, attribution
   header, `#print axioms` audit) repeats verbatim.

Acceptance addition to §5: no file from a sibling group lands in `BookProof/`
without going through channel 1's zero-import discipline; the manifest's
`sibling_projects_note` and per-group directories stay the single source of
earmarks; `../australVM` / `../emthin` entries are added only when those repos
are located.

---

## 9. Execution record (2026-10-18)

Executed in this order: Phase 1.5 first, since the conversion lands outside `BookProof/`
(see below), so the folder renames cannot invalidate its diffs. Then Phase 0, the
measurement fix, Phase 1, Phase 2.1 and Phase 2.2. Every phase ended with
`lake build BookProof` green (8835 jobs, no `sorryAx` in the build log). Phases 3 and 4 are
recorded at the end.

**Phase 1.5: Prove2.me conversion → `converted/` (by request, instead of `Toolbox/Prove2me/`).**
The downloads were present in this repo as `Downloads/`, a copy of
`../prove2me_workspace/Downloads`. The conversion request named `converted/` as the landing
folder, so it is a separate lake library `Prove2me` (`srcDir = "converted"`) and not
`BookProof/Toolbox/Prove2me/`. This also follows the §8 routing rule automatically, because
nothing sibling-earmarked enters `BookProof/`. The original platform theorem names are kept,
and each solution is renamed to `Prove2me.Solution.<Name>` instead of being moved into a
`BookProof.Toolbox.Prove2me.<Author>.*` namespace. This keeps the registered statements
recognisable and avoids breaking dot notation in the solution bodies. Each file carries the
attribution header (theorem id, original name, authors, submission, source, platform rev,
Apache-2.0). Results:
* **21 of 161** solutions are self-contained (they import Mathlib only). All 21 are converted
  and compiled, each is re-checked against its platform statement, and
  `lake build Prove2me.Audit` reports only `propext`, `Classical.choice` and `Quot.sound`
  (or a subset) for all 42 audited declarations. Five needed hand edits for Mathlib drift
  (`converted/README.md` lists them).
* **140** solutions import platform library modules that are not in the download
  (`Definitions.Def_*`, `Theorems.Thm_*`): **281** distinct modules, 173 definitions and
  108 statements, listed per file in `converted/GAPS.md`. Their text is prepared in
  `converted/blocked/`, but they cannot be compiled until those modules are supplied. No
  definition was guessed.
* Conversion diffs: `converted/diffs/<Name>.diff` (161 files). Tooling:
  `scripts/prove2me_convert.py` and `scripts/prove2me_diff.py`.

**Phase 0: orphan split copies.** The measured state differed from §1 in two ways.
(a) 4 of the 87 `X/` directories are **live**: `PhysHSGaussian`, `ChapterNsKoopman`,
`ChapterQgVielbeinScalaronGaugeFL` and `ChapterYangMillsOuterFockFL`. Their `X.lean` is the
thin re-export of `X/Part*.lean`, and the parts hold declarations the monolith lacks, so they
were kept. (b) The 192 orphans are 183 `Part` files plus **9 unprefixed legacy modules**
that `BookProof.lean` does not import (`EsaClosure`, `FarisLavine`, `HashimotoShiftInvert`,
`HermiteCore`, `NavierStokesFlow`, `SirkSpectralGeometry`, `Starobinsky`,
`YangMillsFriedrichs`, `YangMillsHermite`). The 83 orphan directories (183 files) were
declaration-diffed against their monoliths. Every declaration is present in the monolith, so
they were removed. The `--check` note now lists only the 9 legacy modules. Whether to delete
them or wire them in is the Phase 3 legacy-utilities decision, and it is left to the plan owner.

**Measurement fix (affects §1 and BUILD_COMPONENTS.md).** `imports_of` in
`scripts/import_components.py` stopped reading a module's header at the first `/- … -/`
comment. Every module with a copyright block before its imports was therefore treated as
import-free. Fixed. The true picture is **100** independent parts, not 112. The operator
core has **629** modules, not 477, because `BookProofAttention`, `BookProofMeasureFoundations`,
`BookProofFreeFieldBorn`, `BookProofAtomicDecomposition`, `BookProofHolomorphic` and
`BookProofRoadmapAudit` all import it (for example `ChapterGaugeMechanicsCharge` imports
`ChapterG`), so those six targets were retired by `--write-lakefile`. 17 multi-module parts
remain independent.

**Phase 1: independent parts foldered.** 96 modules of the 17 parts moved to
`BookProof/<Part>/`, with the part name minus its `BookProof` prefix as the folder:
`Realification/`, `InducedSystems/`, `HarmonicAnalysis/`, `GravityAlgebra/`,
`Definability/`, `Reconstruction/`, `Lorentz/`, `WeylSL2/`, `WignerOrbit/`, `Bell/`,
`Causality/`, `PauliGrover/`, `Conservative/`, `Density/`, `EnergyBand/`, `FieldStrength/`,
`Pauli/`. Map: `BOOKPROOF_PHASE1_MOVES.md`. Imports were rewritten repository-wide, together
with `COMPONENT_NAMES`, the lake stanzas, and `BookProof/….lean` paths in the docs and comments
(`CONSOLIDATED_PLAN.md` is append-only and keeps its historical paths). Declaration names
are unchanged, because moving a file does not change its namespaces. All 17 part targets build.

**Phase 2.1: cross-import matrix** (`python3 scripts/cross_import_matrix.py`, operator core,
direct imports, rows import columns, §2 name families, "Other" = unclassified residue):

Operator core: 629 modules. Rows import columns (direct imports).

| importer \ imported | RoadmapAudit (1) | Ns (70) | Qg (53) | Qym (16) | Sm (27) | Qed (2) | Sirk (31) | Ode (3) | Attention (51) | Textbook (51) | Toolbox (87) | Other (237) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **RoadmapAudit** | · | 20 | 43 | 4 | · | 1 | 29 | 1 | 33 | 4 | 30 | 94 |
| **Ns** | · | 86 | 10 | 6 | · | · | · | · | · | · | 21 | 13 |
| **Qg** | · | 3 | 57 | 3 | · | · | 4 | 1 | · | · | 25 | 23 |
| **Qym** | · | · | 4 | 13 | · | · | 1 | · | · | 1 | 12 | 8 |
| **Sm** | · | · | 5 | 6 | 32 | · | · | · | · | 5 | 6 | 4 |
| **Qed** | · | · | · | 3 | · | 1 | · | · | · | · | 1 | · |
| **Sirk** | · | 5 | 3 | 1 | · | · | 23 | · | · | 12 | 5 | 5 |
| **Ode** | · | · | · | · | · | · | · | 2 | · | · | 1 | 2 |
| **Attention** | · | · | · | · | · | · | · | · | 64 | · | · | 8 |
| **Textbook** | · | · | · | · | · | · | · | · | · | 125 | 1 | 1 |
| **Toolbox** | · | 7 | 7 | 5 | · | · | 4 | · | · | 1 | 78 | 28 |
| **Other** | 1 | 12 | 13 | 5 | 2 | · | 5 | · | 12 | 20 | 61 | 200 |

Seam test per domain. The audit gate `RoadmapAudit` imports every area by design and is ignored as an importer; `Other` is the residue the §2 name families do not classify:

| domain | modules | inbound from other domains | outbound to non-Toolbox domains | clean cut? |
|---|---:|---:|---:|---|
| RoadmapAudit | 1 | 1 | 229 | no |
| Ns | 70 | 27 | 29 | no |
| Qg | 53 | 42 | 34 | no |
| Qym | 16 | 29 | 14 | no |
| Sm | 27 | 2 | 20 | no |
| Qed | 2 | 0 | 3 | no |
| Sirk | 31 | 14 | 26 | no |
| Ode | 3 | 1 | 2 | no |
| Attention | 51 | 12 | 8 | no |
| Textbook | 51 | 39 | 1 | no |
| Toolbox | 87 | 133 | 52 | no |
| Other | 237 | 92 | 70 | no |

**No domain has a clean cut**, so Phase 2.3 introduces no new `[[lean_lib]]` part, and the
core stays one target. The coupling is the finding. The toolbox imports from Ns, Qg, Qym, Sirk and
Textbook (24 imports), and every domain except Qed imports from "Other" (237 modules).

**Phase 2.2: core foldered.** The 392 core modules that a §2 family classifies moved to
`BookProof/<Area>/`: Toolbox 87, Ns 70, Qg 53, Textbook 51, Attention 51, Sirk 31, Sm 27,
Qym 16, Ode 3, Qed 2, RoadmapAudit 1. Map: `BOOKPROOF_PHASE2_MOVES.md`. The other 237 modules
stay at the top level of `BookProof/`. Assigning them an area needs a reading of each module,
which a name rule cannot provide (§1 "measurement first"). `lake build BookProof` is green after
the move.

**Phase 3** (optional renames) was not started. **Phase 4 gates:** `--check` is green (only
the 9 legacy orphans are noted). `doc_index.py` was regenerated. The `../test` drift gate,
`check_site.py`, the book render and `verify-invariants` need sibling checkouts that are not
present in this workspace, so they were not run. `decl_graph*.jsonl` still carry pre-move
module names and need a re-extraction.

**Addendum 2026-10-19: Phase 1.5 completed with the platform library.** The prove2.me platform
modules that the solutions import were supplied as `Downloads/_deps/` (542 `Definitions.Def_*`,
181 `Theorems.Thm_*`). They are converted under `converted/Definitions/` and
`converted/Theorems/` (lake library `Prove2mePlatform`), keeping their module names, by
`scripts/prove2me_deps_convert.py`, with the token-level drift repairs of
`scripts/prove2me_drift.py` and proved shims for missing Mathlib API (`converted/Prove2me/Shim/`).
A `Thm_` stub whose solution was downloaded (26 cases) re-exports the converted solution. Results:
* **All 161 manifest solutions compile** (`lake build Prove2me`, which includes
  `Prove2me.Audit`). The former `converted/blocked/` set is empty except for the stray
  file below. To let the aggregator import every solution, 76 helper names that several
  solutions repeat are made `private` in all but one module (`scripts/prove2me_privatize.py`).
* The audit covers 322 declarations (161 solutions plus the 161 registered statements).
  122 solutions use only `propext` / `Classical.choice` / `Quot.sound`. 39 reach `sorryAx`,
  and only through platform statement stubs (`Thm_*`, `:= by sorry` by platform design), 108
  distinct ones. They are listed per solution in `converted/GAPS.md`, computed from the compiled
  terms by `scripts/prove2me_stub_cone.lean`.
* Not compiled: one download without a manifest entry
  (`fock-ladders/OAI.Erdos3.VectorPolynomial.…_of_goodModel_s2.lean`, prepared in
  `converted/blocked/FockLadders/`). It needs the 299-module `Def_OAIE3v2B*` chain (21.6 MB), which
  fails against the pinned Mathlib at 32 frontier modules with API-drift errors.

**Addendum 2026-10-19b: Phase 0 residue, Phase 2.2b, Phase 3, Phase 4 (second execution pass).**
Every step below ended with `lake build BookProof` green and no `sorryAx` in the build log.

* **Phase 0 residue: the 9 "legacy orphans" were empty stubs, now removed.** Reading them showed
  that none of `EsaClosure`, `FarisLavine`, `HashimotoShiftInvert`, `HermiteCore`,
  `NavierStokesFlow`, `SirkSpectralGeometry`, `Starobinsky`, `YangMillsFriedrichs` and
  `YangMillsHermite` held a declaration. Each was `import Mathlib`, a "Stub: … placeholder"
  docstring and `noncomputable section`, imported by nothing. The real content lives in the
  `Chapter…` modules of the same name (for example `Toolbox/ChapterFarisLavine.lean`). The
  declaration diff is therefore empty, so these are §4.A redundancy rather than §4.B legacy
  content. They were `git rm`-ed, and `--check` no longer reports any unbuilt module.
* **Phase 2.2b: the 237-module residue is foldered by reading.** `scripts/bookproof_phase2b_move.py`
  records a hand assignment of each residue module to a §2 area. The assignment was made by
  reading each module's header (its title and the book chapter it cites); nothing is inferred
  from names at run time. 236 modules moved: Probability 88 (the §2 `Probability/` folder:
  abelian von Neumann / GAP-2 classification, Born, free-field Born, Bayes, priors, Solovay,
  Mehler), Toolbox 71, Qym 19 (BRST, gauge, ghost vocabulary), Textbook 17 (chapter-A Lorentz,
  Pin, Pauli, Majorana, CPT material), Attention 14, Sirk 11, Qg 11 (walls, limit-circle
  family, conformal fibre), Ode 3, Ns 2. `BookProof.RandomMap2Audit` stays at the top level
  because it is a quarantine audit of the RandomMap2 track. Map: `BOOKPROOF_PHASE2B_MOVES.md`.
  Imports were rewritten repository-wide, and `BookProof/….lean` paths in docs were rewritten
  except in append-only records. Declaration names are unchanged. `scripts/cross_import_matrix.py`
  now knows `Probability/` as a folder area. The recomputed matrix:

Operator core: 630 modules. Rows import columns (direct imports).

| importer \ imported | RoadmapAudit (1) | Ns (72) | Qg (65) | Qym (35) | Sm (27) | Qed (2) | Sirk (42) | Ode (6) | Attention (65) | Textbook (68) | Probability (88) | Toolbox (158) | Other (1) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| **RoadmapAudit** | · | 21 | 53 | 9 | · | 1 | 34 | 2 | 39 | 5 | 33 | 63 | · |
| **Ns** | · | 89 | 10 | 7 | · | · | · | · | · | · | 4 | 29 | · |
| **Qg** | · | 3 | 75 | 8 | · | · | 4 | 1 | · | · | · | 46 | · |
| **Qym** | · | · | 6 | 24 | 2 | · | 4 | · | · | 3 | 1 | 22 | · |
| **Sm** | · | · | 6 | 7 | 32 | · | · | · | · | 7 | · | 6 | · |
| **Qed** | · | · | · | 3 | · | 1 | · | · | · | · | · | 1 | · |
| **Sirk** | · | 5 | 3 | 2 | · | · | 29 | · | · | 16 | · | 13 | · |
| **Ode** | · | · | · | · | · | · | · | 5 | · | · | · | 2 | · |
| **Attention** | · | · | · | · | · | · | · | · | 87 | · | 4 | · | · |
| **Textbook** | · | · | · | · | · | · | 1 | · | · | 154 | · | 1 | · |
| **Probability** | · | · | · | · | · | · | · | · | 1 | · | 90 | 6 | · |
| **Toolbox** | · | 18 | 16 | 10 | · | · | 9 | · | · | 1 | 5 | 195 | · |
| **Other** | 1 | · | · | · | · | · | · | · | · | · | · | · | · |

Seam test per domain. The audit gate `RoadmapAudit` imports every area by design and is ignored as an importer; `Other` is the residue the §2 name families do not classify:

| domain | modules | inbound from other domains | outbound to non-Toolbox domains | clean cut? |
|---|---:|---:|---:|---|
| RoadmapAudit | 1 | 1 | 197 | no |
| Ns | 72 | 26 | 21 | no |
| Qg | 65 | 41 | 16 | no |
| Qym | 35 | 37 | 16 | no |
| Sm | 27 | 2 | 20 | no |
| Qed | 2 | 0 | 3 | no |
| Sirk | 42 | 18 | 26 | no |
| Ode | 6 | 1 | 0 | no |
| Attention | 65 | 1 | 4 | no |
| Textbook | 68 | 27 | 1 | no |
| Probability | 88 | 14 | 1 | no |
| Toolbox | 158 | 126 | 59 | no |
| Other | 1 | 0 | 1 | no |

  **Still no clean cut, so there is still no new `[[lean_lib]]` (Phase 2.3).** `Ode` comes
  closest: it imports only `Toolbox`, and exactly one module imports it, from `Qg`.
  `Attention` imports nothing from `Toolbox` and only 4 modules from `Probability`, while one
  `Probability` module imports `Attention`. Neither meets the seam test. The operator core
  stays one target.
* **Phase 3: renames.**
  - *Case-collision trio.* `ChapterWeylSl2`, `ChapterWeylSL2Group` and `ChapterWeylSL2Unipotent`
    were read. **None is redundant.** `ChapterWeylSl2` is the Lie-algebra layer (`Sl2Rep`,
    Casimir, highest weight, Weyl complete reducibility for `sl₂`). `ChapterWeylSL2Group`
    lifts it to `SL(2,ℂ)` via unipotent factorisation, and `ChapterWeylSL2Unipotent` builds on
    both. On a case-insensitive checkout there is no file collision, because the names differ
    by more than case. The `Sl2`/`SL2` spelling was still the hazard named in §4.B. Its cite
    density is low (BookProof.lean, the two sibling modules, `Work/WignerMackeyWeylAudit.lean`,
    no `Book/` citation, no `#print axioms` line in the roadmap audit). It was therefore renamed
    to one convention: module `BookProof.WeylSL2.ChapterWeylSL2Algebra` and namespace
    `BookProof.ChapterWeylSL2Algebra`, with all `.lean` references updated.
  - *Unprefixed utilities.* After the stub removal, 7 remain: `Toolbox/Phys{FunctionalAnalysis,
    HSGaussian,MeasureBasis,Mehler}`, `Toolbox/Prelude`, `Toolbox/Substrate` and
    `Realification/Complexification`. Cite-density check (importing `.lean` files / `Book/`
    files / Markdown files): PhysFunctionalAnalysis 3/1/4, PhysHSGaussian 6/2/5,
    PhysMeasureBasis 6/0/4, PhysMehler 8/0/4, Prelude 16/0/5, Substrate 1/0/14,
    Complexification 7/1/6. Their namespaces (`BookProof.PhysMehler`, …) are cited by name
    across `Book/` and the docs, and a module rename would split module and namespace names.
    So they are **not renamed**. Foldering them into `Toolbox/` already makes them findable.
  - *Lettered `Textbook/` chapters*: foldered, not renamed, as the plan allows when cite density
    is high.
* **Phase 4 gates.** `import_components.py --check` is green with no unbuilt-module note.
  `--write-lakefile` and the `BUILD_COMPONENTS.md` inventory have been regenerated, and so have
  `doc_index.py` and `decl_graph.jsonl` (now with the post-move module names).
  `health.sh` and `verify-invariants` were run; their results are in
  `CONSOLIDATED_PLAN.md` §"2026-10-19b". The `../test` drift gate and the
  book render still need sibling checkouts that are not present.
