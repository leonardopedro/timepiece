# Audit: the 19 `BookProof.*` nodes marked **Disproved** on prove2.me

Audited 2026-10-30 against this repository (the source of record) via
`GET /api/v1/theorems?q=BookProof&status=Disproved` (19 rows), then
`GET /api/v1/theorems/:id` for each row's `preamble`, `formal_statement` and
`GET /api/v1/theorems/:id/submissions` for the accepted counterexamples.

## Verdict in one line

All 19 statements are **textually identical** to the declarations in this repository, and
**all 19 are proved here** (`lake build BookProof`, no `sorry`, no extra axioms beyond
`propext`/`Classical.choice`/`Quot.sound`).  The `Disproved` marks are **export defects, not
proof defects**: in each case the platform's re-elaborated target is a *strictly stronger*
claim than the repo declaration, and it is that stronger claim which was refuted.

## Mechanism: three ways a binder gets lost

The platform stores a node as `preamble` (imports, `open`s, `variable`/`include` lines) plus
`formal_statement` (source text of the declaration).  The target it checks is the statement
re-elaborated in the preamble.  Lean only turns a section `variable` into an argument of a
declaration when the variable occurs in the **type** or in the **value**; the exported
statement text keeps only the type.  Hence:

* **Class A — value-only instance.**  `[CompleteSpace F]` is used by the *proof*, so Lean
  records it as an argument, but it never occurs in the statement's type.  The target then
  quantifies over incomplete inner product spaces.
* **Class B — proof-only hypothesis.**  A `variable (h : …)`, or an `include h in`, whose
  hypothesis does not occur in the type (a cyclicity, normality, invariance or frame
  hypothesis).  The target drops it and quantifies over *unhypothesised* data.
* **Class C — statement/definition mismatch.**  Two declarations with the same bare name in
  different namespaces, published against one shared definitions bundle.

Evidence, quoted from the platform's own accepted submissions:

> "The target's preamble declares only `[NormedAddCommGroup F] [InnerProductSpace ℂ F]`. It
> does not include `[CompleteSpace F]`, so the claim must hold for every complex inner product
> space, complete or not. In an incomplete space it fails." — disproof of
> `weyl_friedrichs_extension_of_complete`

and, from a *failed proof* submission on the same node, the target type printed by the
platform's own elaborator — no `[CompleteSpace F]`, while the solution has it:

```
has type   ∀ {F} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {D …}, …
expected   ∀ {F} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D …}, …
```

> "The section variables `hu hv he huv hue hve` … do not occur in the statement or its proof
> term, so Lean drops them from the theorem: the formal statement quantifies over **all**
> vectors `u, v, e` … The intended statement needs the frame hypotheses added as explicit
> binders." — disproof of `ChapterSolidHarmonic.inner_v_spherePt_frames`

## The 19 nodes

| # | node | repo file | class | what the target lost | repo |
|:-:|:--|:--|:-:|:--|:-:|
| 1 | `FriedrichsExtension.friedrichs_extension_exists_of_complete` | `Toolbox/ChapterFriedrichsExtension.lean` | A | `[CompleteSpace F]` | proved |
| 2 | `FriedrichsExtension.friedrichs_hypothesis_holds_of_complete` | same | A | `[CompleteSpace F]` | proved |
| 3 | `FriedrichsExtension.weyl_friedrichs_extension_of_complete` | same | A | `[CompleteSpace F]` | proved |
| 4 | `FriedrichsExtension.friedrichs_extension_semibounded_of_complete` | same | A | `[CompleteSpace F]` | proved |
| 5 | `ChapterSolidHarmonic.inner_v_spherePt_frames` | `HarmonicAnalysis/ChapterSolidHarmonic.lean` | B | `hu hv he huv hue hve` | proved |
| 6 | `ChapterSolidHarmonic.inner_u_spherePt_frames` | same | B | frame hypotheses | proved |
| 7 | `ChapterSolidHarmonic.inner_e_spherePt_frames` | same | B | frame hypotheses | proved |
| 8 | `ChapterSolidHarmonic.norm_spherePt_frames` | same | B | `hu hv he` (normality of the frame) | proved |
| 9 | `ChapterSolidHarmonic.solidHarmonic_spherical_frames` | same | B | frame hypotheses | proved |
| 10 | `ChapterSpectralDirectSum.spectral_multiplication_model_general_normal` | `ChapterSpectralDirectSum.lean` | B | `hT : IsStarNormal T` | proved |
| 11 | `ChapterSpectralDirectSum.spectral_multiplication_model_separable_normal` | same | B | `hT : IsStarNormal T` | proved |
| 12 | `ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative_of_cyclic` | `ChapterAbelianCyclicCommutant.lean` | B | `hcyc : DenseRange (repVec pi xi)` | proved |
| 13 | `ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_of_cyclic` | `ChapterAbelianCyclicModel.lean` | B | `hcyc` | proved |
| 14 | `ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_of_positive` | `ChapterAbelianGelfandModel.lean` | B | `hpos : ∀ g, 0 ≤ psi (star g * g)` | proved |
| 15 | `BrstReducedTransfer.infDist_exactStates_eq_of_comm` | `ChapterBrstReducedTransfer.lean` | B | `hcomm` | proved |
| 16 | `BrstReducedTransfer.infDist_exactStates_stoneU_eq_of_comm` | same | B | `include hcomm in` | proved |
| 17 | `BrstReducedTransfer.stoneU_mem_physicalStates_of_comm` | same | B | `include hcomm in` | proved |
| 18 | `BrstReducedTransfer.stoneU_sub_mem_exactStates_of_comm` | same | B | `include hcomm in` | proved |
| 19 | `FockDegreesOfFreedom.Gravity.ghostRawCard` | `ChapterFockDegreesOfFreedom.lean` | C | statement of the `NavierStokes` theorem (`= 3 + 1`) against the `Gravity` definition (`Fin 4 ⊕ (Fin 4 × Fin 4)`, card `19 + 1`) | proved |

Node 19 is a name collision, not a dropped binder: `ChapterFockDegreesOfFreedom.lean` defines
`GhostRaw`/`ghostRawCard` four times (`NavierStokes`, `YangMills3D`, `YangMills4D`,
`Gravity`, lines 119–186).  The published node is keyed `…Gravity.ghostRawCard` but carries
the `NavierStokes` statement (`3 + 1`), so against the `Gravity` bundle its own accepted
disproof computes `4 + 16 = 20`.

## Fixed here: the Friedrichs cluster (nodes 1–4)

`Toolbox/ChapterFriedrichsExtension.lean` now writes the completeness instance **in each
binder list**:

```lean
theorem friedrichs_extension_exists_of_complete_explicit (P : PosSymOp F) [CompleteSpace F]
    (hdense : Dense (P.dom : Set F)) : …
```

(The suffix was `_of_complete` when the binder was introduced and is `_of_complete_explicit`
since the 2026-10-30 rename documented below, which also dropped the `omit … in` prefix — the
section `variable [CompleteSpace F]` no longer needs omitting once every statement of the file
names the hypothesis itself.)  The four signatures are unchanged — `#check` still prints
`∀ {F} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] …`, because the
instance was already an argument of the declaration — while the exported statement text now
carries the hypothesis, so a re-export cannot lose it.  The reasoning is recorded in a comment
block in the file so the binders are not "cleaned up" again.

## Also fixed here: nodes 5–18

The same remedy was applied to the other fourteen nodes in the same pass: the dropped
hypothesis now appears in the binder list, and the per-declaration `include … in` was replaced
by it.  Signatures are unchanged in every case (`#check` before and after is identical — the
hypothesis was already an argument at the value level), so no call site moved; only the
exported statement text changed.

| file | nodes | binder now written |
|:--|:--|:--|
| `HarmonicAnalysis/ChapterSolidHarmonic.lean` | 5–9 | `(hu hv he) (huv hue hve)`; the section's `include` line was dropped (these five are the only declarations of the `Frame` section) |
| `ChapterSpectralDirectSum.lean` | 10–11 | `(hT : IsStarNormal T)` |
| `ChapterAbelianCyclicCommutant.lean` | 12 | `(hcyc : DenseRange (repVec pi xi))` |
| `ChapterAbelianCyclicModel.lean` | 13 | `(hcyc : DenseRange (repVec pi xi))` |
| `ChapterAbelianGelfandModel.lean` | 14 | `(hpos : ∀ g, 0 ≤ psi (star g * g))` |
| `ChapterBrstReducedTransfer.lean` | 15–18 | `(hcomm : ∀ t y, T.stoneU t (Om y) = Om (T.stoneU t y))` (the `U`-form for node 15) |

Each file carries a comment at the site explaining why the binder is explicit and asking that
it not be removed.

## Fixed here: node 19 (the `GhostRaw` collision)

`FockDegreesOfFreedom.Gravity.ghostRawCard` was a statement/definition mismatch, not a dropped
binder: `ChapterFockDegreesOfFreedom.lean` defined `GhostRaw`/`ghostRawCard` four times
(`NavierStokes`, `YangMills3D`, `YangMills4D`, `Gravity`), and the published node carried the
`NavierStokes` statement (`= 3 + 1`) against the `Gravity` definition
(`Fin 4 ⊕ (Fin 4 × Fin 4)`, card `19 + 1`).  The *type* names were never ambiguous (they are
namespace-qualified); the *lemma* leaf names were.

The four lemmas now have theory-suffixed names, unique across the file and therefore across any
name-keyed extraction:

| namespace | lemma | statement |
|:--|:--|:--|
| `NavierStokes` | `ghostRawCard_navierStokes` | `Fintype.card GhostRaw = 3 + 1` |
| `YangMills3D` | `ghostRawCard_yangMills3D` | `= 31 + 1` |
| `YangMills4D` | `ghostRawCard_yangMills4D` | `= 39 + 1` |
| `Gravity` | `ghostRawCard_gravity` | `= 19 + 1` |

A comment at the head of the file records why the names must stay distinct, and
`Work/FockDegreesOfFreedomAudit.lean` (the axiom audit) was updated in the same change.
`Jet`/`jetCard` repeat across the four namespaces too; they were not affected (no `Disproved`
mark), but they carry the same latent risk and should get the same treatment if they are ever
published as separate nodes.

Nothing in any *proof* needs to change — the arguments already existed at the value level;
only their visibility in the statement text was at stake.  Re-exporting alone does not repair
the published targets: their statements are stored, so a corrected statement is a new node (or
a moderator edit).

## Retired on the platform (2026-10-30)

All 19 node records were **deprecated** (`PATCH /api/v1/theorems/:id` with
`{"deprecated": true}`, HTTP 200 on every one), so they no longer surface in discovery.  A fresh
`GET /theorems?q=BookProof&status=Disproved` now reports `total: 0`.

Per `references/contribute.md` §Deprecation, this **hides** a node; it does not change its proof
status and does not delete it — which is exactly right here, since the published statements are
false as written and their replacements carry the corrected binders (and, for node 19, a
distinct name).  Fully reversible: pass `{"deprecated": false}` to restore a record.

Residual state to be aware of: the deprecated records still say `Disproved` if queried directly
by id or with `include_deprecated=true`, and a future re-export must publish the corrected
statements as **new** nodes — a published statement is never overwritten.

## Landed 2026-10-30: renamed, republished, cross-referenced

Three follow-ups were carried out on top of the audit above.

### 1. The corrected declarations were renamed to unique public names

Every corrected declaration now ends in `_explicit`, which names the fix: the hypothesis that the
platform's export dropped is an **explicit binder of the statement**, so no re-export can lose it
again.  The old identifiers stay in the retired platform records only; the source of record no
longer uses them (call sites, `Book/`'s `#check` lines and the prose that cites them were moved in
the same change, in both `timepiece/` and `timepiece331/`).

| retired node (platform) | corrected declaration (both trees) |
|:--|:--|
| `FriedrichsExtension.friedrichs_extension_exists` | `FriedrichsExtension.friedrichs_extension_exists_of_complete_explicit` |
| `FriedrichsExtension.friedrichs_hypothesis_holds` | `FriedrichsExtension.friedrichs_hypothesis_holds_of_complete_explicit` |
| `FriedrichsExtension.weyl_friedrichs_extension_unconditional` | `FriedrichsExtension.weyl_friedrichs_extension_of_complete_explicit` |
| `FriedrichsExtension.friedrichs_extension_of_semibounded_below` | `FriedrichsExtension.friedrichs_extension_semibounded_of_complete_explicit` |
| `ChapterSolidHarmonic.inner_v_spherePt` | `ChapterSolidHarmonic.inner_v_spherePt_frames_explicit` |
| `ChapterSolidHarmonic.inner_u_spherePt` | `ChapterSolidHarmonic.inner_u_spherePt_frames_explicit` |
| `ChapterSolidHarmonic.inner_e_spherePt` | `ChapterSolidHarmonic.inner_e_spherePt_frames_explicit` |
| `ChapterSolidHarmonic.norm_spherePt` | `ChapterSolidHarmonic.norm_spherePt_frames_explicit` |
| `ChapterSolidHarmonic.solidHarmonic_spherical` | `ChapterSolidHarmonic.solidHarmonic_spherical_frames_explicit` |
| `ChapterSpectralDirectSum.spectral_multiplication_model_general` | `…_general_normal_explicit` |
| `ChapterSpectralDirectSum.spectral_multiplication_model_separable` | `…_separable_normal_explicit` |
| `ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative` | `…_of_cyclic_explicit` |
| `ChapterAbelianCyclicModel.cyclic_representation_multiplication_model` | `…_of_cyclic_explicit` |
| `ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state` | `…_of_positive_explicit` |
| `BrstReducedTransfer.infDist_exactStates_eq` | `…_of_comm_explicit` |
| `BrstReducedTransfer.infDist_exactStates_stoneU_eq` | `…_of_comm_explicit` |
| `BrstReducedTransfer.stoneU_mem_physicalStates` | `…_of_comm_explicit` |
| `BrstReducedTransfer.stoneU_sub_mem_exactStates` | `…_of_comm_explicit` |
| `FockDegreesOfFreedom.Gravity.ghostRawCard` | `FockDegreesOfFreedom.Gravity.ghostRawCard_gravity` |

The last row was already renamed in the first pass (it is a name collision, not a dropped binder);
the other eighteen were renamed here.  The 4.28 and 4.33.1 signatures are byte-identical for all
eighteen declarations (`extract-and-diff` of the declaration headers), so the two trees still carry
the same statements.

### 2. The eighteen corrected statements are published as new nodes

`POST /api/v1/submit-problem`, one job per node, all `PUBLISHED` on the first attempt (no compile
failure on any of the eighteen).  Each preamble keeps the retired node's imports and `open`s and
adds a comment naming the retired node and the two source files.  The statement text carries the
hypothesis as a binder, so the published target has it — the check that the retired nodes failed
(`GET /theorems/:id` shows the binder in `formal_statement`, and the job's compile proves the
statement elaborates in the retired node's own preamble).  The nodes are `Open`: the statements are
open problems on the platform even though both trees carry a proof, so a proof submission is still
outstanding for each.

| published node | `theorem_id` |
|:--|:--|
| `BookProof.FriedrichsExtension.friedrichs_extension_exists_of_complete_explicit` | `6949e145-0049-4f65-816c-215212c4373f` |
| `BookProof.FriedrichsExtension.friedrichs_hypothesis_holds_of_complete_explicit` | `3f50b02d-74c8-46bc-ae16-32c9d60d0960` |
| `BookProof.FriedrichsExtension.weyl_friedrichs_extension_of_complete_explicit` | `95e5ffe8-30cd-4cd5-8b6e-e593d93ad714` |
| `BookProof.FriedrichsExtension.friedrichs_extension_semibounded_of_complete_explicit` | `5038444f-21b9-4112-91bf-bd9b2874a8c1` |
| `BookProof.ChapterSolidHarmonic.inner_v_spherePt_frames_explicit` | `a6510aa5-7e35-487c-833d-8d9cafa604c4` |
| `BookProof.ChapterSolidHarmonic.inner_u_spherePt_frames_explicit` | `b324961a-dc5e-4e3e-83b2-7e69629df4dd` |
| `BookProof.ChapterSolidHarmonic.inner_e_spherePt_frames_explicit` | `2a95a67d-d514-43e9-90bc-3c2f71fdba32` |
| `BookProof.ChapterSolidHarmonic.norm_spherePt_frames_explicit` | `f0d95bb9-9d4e-460f-a00e-24b3272c4186` |
| `BookProof.ChapterSolidHarmonic.solidHarmonic_spherical_frames_explicit` | `7cec10b6-01ba-4158-8501-e507184b4843` |
| `BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general_normal_explicit` | `8f775b38-363a-4b9e-a8fa-1ac14c7632b4` |
| `BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_separable_normal_explicit` | `7975db95-4961-4218-a5e8-3fa0947cc440` |
| `BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative_of_cyclic_explicit` | `610583c2-2d8e-4545-9859-7a7ad572dc43` |
| `BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_of_cyclic_explicit` | `1876efed-389f-41b2-9887-c4c40445f06d` |
| `BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state_of_positive_explicit` | `1fe6ec5d-02a6-49d7-bf1b-aec0e5a1da1b` |
| `BookProof.BrstReducedTransfer.infDist_exactStates_eq_of_comm_explicit` | `643c6427-7bc4-4cd8-94ff-fa4ab5277561` |
| `BookProof.BrstReducedTransfer.infDist_exactStates_stoneU_eq_of_comm_explicit` | `4d6c0b92-8a01-4eb7-9eea-f71df39cc80d` |
| `BookProof.BrstReducedTransfer.stoneU_mem_physicalStates_of_comm_explicit` | `8c96ad79-2407-4bd9-a962-b3b24f9ee136` |
| `BookProof.BrstReducedTransfer.stoneU_sub_mem_exactStates_of_comm_explicit` | `2b7d8cee-bc38-4e24-9411-bcb1d9b30431` |

(The ids above are transcribed for convenience; `GET /api/v1/theorems?theorem_name=…` is the
authority.)

### 3. The nineteen retired records now point at the fix

`PATCH /api/v1/theorems/<id>` with the *existing* description plus a retirement note: why the
target was wrong (class A/B/C, as above), the corrected declaration, its file in each tree, and the
name of the replacement node.  `source` was repointed from the stale `blob/61595bc/BookProof/
Chapter*.lean` link to the corrected file on `main`.  HTTP 200 on all nineteen.

## Why the corrected statements cannot be published under their own names

`POST /api/v1/submit-problem` with the corrected statement, the original preamble and the original
`theorem_name` is rejected:

```json
{"jobs":[],"errors":["A theorem with theorem_name \"BookProof.ChapterSolidHarmonic.inner_v_spherePt_frames\" already exists"]}
```

Name uniqueness is enforced **within the environment**, and a deprecated record still holds its
name — deprecation hides a node, it does not free the identifier.  `PATCH /theorems/:id` can edit
the description and the deprecation flag, never the statement.  So there is no submitter-side way
to repair a published statement in place: a corrected version must be published under a *new*
name (for node 19 the rename to `ghostRawCard_gravity` already does that), and the old record stays
`Disproved` behind the deprecation flag.

That is a naming decision for the source of record, not a mechanical step, because renaming changes
a public identifier the book cites.  It was taken on 2026-10-30 in favour of the `_explicit`
suffix (see *Landed 2026-10-30* above): no GitBook page and no `.tex` file cited any of the
eighteen, so the blast radius was the Lean trees, `Book/`'s `#check` lines and the internal prose,
all of which moved in the same change.

## Re-running this audit

```bash
TOK=$(cat /tmp/p2m_token.txt)
curl -s -G https://prove2.me/api/v1/theorems \
  -d q=BookProof -d status=Disproved -d view=compact -d limit=100 \
  -H "Authorization: Bearer $TOK" | jq -r '.total, (.theorems[] | .theorem_name)'
```
