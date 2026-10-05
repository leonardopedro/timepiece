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
proof in Lean4"; **§10-04b** = §"State of the project — 2026-10-04b".

| Track | Current work order | Superseded as a reading guide | Superseded outright |
|---|---|---|---|
| **NS** (Navier–Stokes) | §09-25 **§5, item 3** ("NS: discharge the standing ESA hypotheses"), baseline in §09-25 **§2** (`**NS:**` row) | the 2026-09-24a…e state entries as entry points — each preamble supersedes its predecessor in place | `PLAN_LEAN_SPECIALIST_NS_FLOW.md` — self-marked `**EXECUTED (2026-08-14→16).**`; its **E.3** is marked `SUPERSEDED by the executed wave (2026-08-16)`; demoted globally by §09 route map ("supersedes the spread of routes in §9–§12 **and the per-thread plans**") |
| **QYM** (Yang–Mills) | §09-25 **§5, item 4** ("Non-abelian QYM one-particle form gap"); restated as the programme's top analytic input in §10-04b **§N2** | `REVIEW_AND_PLAN_20260907.md` — but note §09-25 records that it *extends* `REVIEW_THREADS_20260906.md` and "supersedes nothing in" it | `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` — "the continuous flow is **not yet instantiated for QYM**"; its own §11.4 "closed" claims are superseded by its later status block |
| **QG** (quantum gravity) | §09-25 **§5, item 2** ("QG: the density as a canonical variable"); record operator pinned in §09-25 **§1** | the 2026-08-29e QG order (`**QG-ESA-C — the reassembly …**`) | `PLAN_LEAN_SPECIALIST_QG_FLOW.md` — status `executed` (2026-08-17); its densitized subject is demoted by §09-25 §1's "separate, labeled realizations — **never the record**" |
| **SM** (Standard Model) | §09-25 **§5, item 6** ("SM refinements"), baseline in §09-25 **§2**; live boundary ledger `HONEST_BOUNDARIES_SM.md` ("Current state of record") | the 2026-09-22e "what stays open" list — "superseded 2026-09-22f by the closure wave and the state section below"; the 2026-09-23e bosonic FL item ("Read this instead of … for the bosonic FL item") | the §D6b-SM **Step 3** work order — executed; and `smComparison` as a comparison operator — **refuted** by the 09-23f wave, though still defined and proved positive because the fermionic completion needs it |
| **RandomMap** (RH) | ⚠ **no current work order exists** — see flag **F2** | — | `IMPLEMENTATION_PLAN.md` — its own text marks the conjugate-reflection route "**Legacy / off-critical-path files (the superseded …)**"; `RandomMap_old.md` (superseded by `RandomMap.md`); `RandomMap2LegacyDraft.md` — "kept as historical material because several declarations use **obsolete APIs or state invalid proposals**"; `newproof.md` (superseded per `RandomMap.md`'s "Adaptation notes (what this plan adopts from `newproof.md`, and what supersedes it)"); `IMPLEMENTATION_PLAN_RCP.md`'s C2–C4 and Phase 3 — "C2–C4 are retained below **for historical context only** — do not implement" |
| **book** (Verso / pedagogical) | §09-25 **§5, items 1 and 7** (prose verification; hygiene decisions), build contract in the "Build scope" section | the §4 BookProof task list — "now all LANDED … kept as a record only; do not redo them" | `SPECIALIST_PLAN_REMAINING.md` — "**Plan A is fully executed.**"; `BOOK_PROOF_PLAN.md` Priorities 1–2 (COMPLETE) |
| **mass-gap** | §10-04, work order **§M4** — *the newest entry in the file* | §13 (T1–T12, "the Lean4 plan"), `MASS_GAP_CERTIFIED.md`, `unfer_contracts/MASS_GAP_SPEC.md`, `unfer_contracts/MASS_GAP_REGENERATION.md` — §10-04 consolidates and supersedes all four "as a reading guide"; they "**remain the detailed record**" | — (§13.1's honesty boundaries and §13.6's definition of done still stand) |

**The single most load-bearing supersession sentence for the book track** is buried inside
the 2026-08-27 wave block, not in any header: *"One plan that supersedes the per-thread
plans for future work"* — it absorbs everything still open from `BOOK_PROOF_PLAN.md`,
`PLAN_LEAN_SPECIALIST_UNPROVED.md`, `SPECIALIST_PLAN_REMAINING.md`,
`PLAN_LEAN_SPECIALIST_COHERENT.md`, `PLAN_A_BOOK_FORMALIZATION.md`,
`PLAN_B_PROSE_VERIFICATION.md`, `SINGULARITY_DETECTION_PLAN.md` and
`PLAN_A_EXECUTION_REPORT.md`. It sits inside the 2026-08-27 wave block, not in any header.

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