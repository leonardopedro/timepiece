# `mm0/` — the Solovay–Kopperman conversion to MM0 (the mm0web platform)

This folder holds the first MM0 conversion of this repository's decidable-math
theory: the **Solovay–Kopperman tensor product** line of the development
(`BookProof/ChapterSolovayHilbertTensor.lean`,
`BookProof/ChapterSolovayCoordinates.lean`,
`BookProof/Toolbox/ChapterTensorCompleteness.lean`) together with the
**Kopperman/Mehler formalism layer** it rests on
(`BookProof/Toolbox/PhysMehler.lean`, `BookProof/ChapterKopperman.lean`,
`PnpProof/Kopperman.lean`). This is the tensor-product version of the
theory; the `RandomMap` line is deliberately out of scope.

The pair is written to be consumed by the mm0web publishing platform in
`../unfer/mm0web`, whose `/verify` runs exactly this checker chain:

```bash
mm0-rs compile kopperman_mehler.mm1 kopperman_mehler.mmb   # elaborate proofs
mm0-c   kopperman_mehler.mmb < kopperman_mehler.mm0        # replay against spec
```

Current state: **both exit 0, no warnings** — 12 sorts, 41 term/def,
40 ax/thm (29 axioms + 11 proved theorems).

## Files

| file | content |
|---|---|
| `kopperman_mehler.mm0` | the spec: sorts, terms, axioms (each tagged with its Lean source) and proofless theorem statements |
| `kopperman_mehler.mm1` | the same declarations plus `pub theorem … = '(...)` proofs — this is the file compiled to `.mmb` |
| `README.md` | this mapping record |

The layout follows `australVM/mm0/gap_certificate.{mm0,mm1}`: spec file +
proof file, structural glue checked step by step by `mm0-c`, deep facts
carried across as provenance-tagged axioms.

## Trust split

**Proved in mm1 (11)** — derivations `mm0-c` checks:

| theorem | source | what the proof does |
|---|---|---|
| `shuffle_apply` | `prodProdProdCommEquiv` | the four-fold shuffle computes pointwise on a literal quadruple: four projection chains reassembled by pair congruence |
| `shuffle_involution` | `prodProdProdCommEquiv` self-inverse | shuffle∘shuffle = id for *arbitrary* z: re-derive `((p₁,p₃),(p₂,p₄))` from the projection axioms, rebuild z by η, chain with `seq_trans` |
| `solo_apply` | `solovayTensorEquiv` pointwise action | the Solovay–Kopperman tensor map concatenates heads and interleaves tails; `hcat_cong`/`itlv_cong` lift the four projection chains |
| `tensor_decide_apply` | `DecidableLanguage.tensor`, `tensor_decide_apply` (there `rfl`) | the tensor language's decision procedure computes; Lean's `Prod.fst/snd` reduce definitionally, here the pair axioms do that job |
| `interpPi02_fwd` / `interpPi02_rev` | `interpPi02_eq` | definitional: the def's body is `pi02 p`, its other arguments are ignored |
| `arith_truth_invariant` | `arith_truth_invariant`, `standard_pi02_truth_invariant` (there `Iff.rfl`) | Π⁰₂ truth cannot depend on the formalism model or the foundation — chained through `interpPi02_fwd`/`rev` |
| `all_formalism_models_separable` | `ChapterKopperman.all_formalism_models_separable` | field projection restated under the Lean name |
| `kopperman_substrate_separable` | `ChapterKopperman.kopperman_substrate_separable` | alias of the substrate fact |
| `modelPrior_atomless` | `PnpProof.Kopperman.modelPrior_atomless` | the model prior's singleton masses vanish (field projection) |
| `inner_orthogonal_tensor` | `orthonormal_tensorOf`, off-diagonal instance | orthogonal factors stay orthogonal under ⊗: `inner(e₁⊗g, e₂⊗g) = inner(e₁,e₂)·inner(g,g) = 0·… = 0` |

**Analytic axioms (14)** — Lean-proved facts recorded with their source
theorem; MM0 records the statement, the proof stays in Lean:

`separable_field` (Formalism.separable), `skeleton_field`
(skeleton_countable/dense/decidable), `prior_isProb_field`
(Formalism.prior_isProb), `prior_atomless_field` (Formalism.prior_atomless),
`substrate_separable`, `substrate_decidable_skeleton`, `mehler_isProb`
(mehler_isProbability), `mehler_concentrates_on_sphere`,
`admits_atomless_prior`, `modelPrior_atomless_field` (prior_atomless at
Model.prior), `concat_prob` (concatHeadMeasure_isProb), `solovayTensor_map`
(solovayTensorEquiv_map — the transport theorem), `solovayTensor_unitary`
(solovayTensorUnitary — the Hilbert-space form), `inner_tensorLp`.

**Interface axioms (15)** — MM0-side structural glue with no Lean source:
state equality/congruence (`seq_trans`, `seq_cong_scons`, `seq_fst_cong`,
`seq_snd_cong`), pairing computation and η (`sfst_cons`, `ssnd_cons`,
`scons_eta`), component congruences (`hcat_cong`, `itlv_cong`,
`band_cong`, `beq_ldec`, `rmul_cong_l`, `rmul_zero_l`), Real equality
(`req_trans`), and the encoded-map bridge `soloFn_app`.

## What is *not* yet converted

The completeness half of `ChapterTensorCompleteness.lean`
(`tensorSpan_eq_top`, `pureTensors_dense`, `exists_tensor_approx`,
`orthonormal_tensorOf`'s full Orthonormal statement,
`tensorHilbertBasis`), the coordinate enlargements
(`enlargeEquiv`, `tailSplitEquiv` in `ChapterSolovayCoordinates.lean`), and
the internal ∀∃ structure of `Pi02` itself. They need either ε-approximation
vocabulary or Fin-indexed arithmetic that this first layer deliberately
keeps opaque; they are the natural next conversion step.

## MM0/mmr syntax notes (pinned by test, for the next conversion)

* Hypothesis-form statements are **binders**: `theorem t (h: $ A $): $ B $`
  in the spec, `pub theorem t (h: $ A $): $ B $ = '…` in the proof file.
  Writing the antecedent as `$ A $ > $ B $` in a *theorem* leaves the
  hypothesis anonymous — `'h` then fails with `unknown theorem/hypothesis`.
  (`>` chains are fine in *axioms*, which have no proofs.)
* `pub` is required on `.mm1` theorems or they never reach the `.mmb`
  (and `mm0-c` then reports `expecting a theorem`).
* In quotes, axiom parameters are instantiated by unification: write a
  **bare axiom reference** and pass only hypothesis arguments
  (`'(seq_trans h1 h2)`). Passing parameters explicitly fails
  (`unknown theorem/hypothesis` / `too many arguments`).
* Definitional equality works for unfolding a `def` when heads differ
  (`'h : interpPi02 p f z` at goal `pi02 p`), but the unifier will *not*
  unfold when both sides have the same head and the arguments mismatch —
  chain through an intermediate lemma instead.
* `def` parameters that are intentionally unused must be named `_x`
  (otherwise: `warning: Unused variable`, which fails the platform's
  no-warnings `/verify`).
* `>` is rejected inside a binder type (`term f (m: A > B)`); function
  *return* types are fine (`term f: A > B;`). Higher-order parameters
  (the pushforward `mapLaw`) therefore use an opaque sort + application
  constant + bridge axiom.

## Publishing record

Pushed through a local mm0web instance backed by the mock-Zenodo sandbox
(`unfer/mm0web/tests/mock_zenodo.py`, the debug stand-in for
`sandbox.zenodo.org`):

- platform: `unfer/mm0web`, checker `mm0-rs` + `mm0-c`, state `/tmp/mm0pub/state`
- project `timepiece`, title `solovay-kopperman-tensor`
- proof id `solovay-kopperman-tensor-d2ac1e83` (fingerprint `d2ac1e8310e1f869`)
- DOI `10.5281/zenodo.1`, sandbox record `http://127.0.0.1:8949/records/1`
- event trail: `verified` → `queued` → `published`
- extras exercised against the published record:
  - `/graph?project=timepiece&id=…` — the ProofFlow-style dependency DAG
    (HTML 97 KB; JSON `/api/v1/graph` 19 KB: 93 declarations, each with
    `deps`, `proved`, `source` — 29 axioms vs 11 proved theorems visible)
  - `/api/v1/search?q=tensor` — 5 hits over the 93-declaration corpus
    (substring arm; no embedder configured, so `embedder: null` and the
    degraded single-arm path is reported rather than failing)
  - `/search?q=shuffle` (HTML), `/api/v1/stats` (12 sorts, 37 terms,
    4 defs, 29 axioms, 11 theorems; 260 references, 0 faults),
    `/manifest`, `/events`, `/status`

The debug instance is left running for inspection: mm0web on
`http://127.0.0.1:18949` (web PID 94680), mock Zenodo on `:8949`
(PID 92402); logs in `/tmp/mm0pub/{web,mock}.log`.
