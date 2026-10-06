# Self-contained mass-gap regeneration bundle

This directory is the complete non-Lean input bundle for the mass-gap
formalization. It was copied from the current numerical implementation so the
Lean4 specialist can work from `timepiece` alone.

## Object of record

The physical object is the 3D gauge-fixed QYM one-particle Hamiltonian `h`,
including its inner pair terms. If positivity requires a shift, apply only the
allowed scalar shift. The final nested-Fock Hamiltonian is

```text
H = Σᵢⱼ hᵢⱼ C†(eᵢ) A(eⱼ).
```

The outer annihilation operator kills the outer vacuum, so the full theory has
the exact outer-vacuum ground. Squeezed inner states are one-particle
spectral diagnostics, not full-theory ground states.

Numerical approximations use the SIRK–Hashimoto algorithm. Lattice code and
occupation-parity certificates are not inputs to this formalization.

## Included inputs

- `MASS_GAP_SPEC.md`: proof-facing contract and code-to-mathematics map.
- `fock_sirk/src/`: current certificate, SIRK seam, and pure specification
  sources (reference text — the specialist never compiles Rust).
- `fock_sirk/tests/`: current QYM and certificate regression tests
  (reference text — run by the planner in `../unfer`, never by the
  specialist).
- `sirk_core_model/`: Aeneas-supported pure SIRK core, regeneration script,
  and committed generated artifacts.  The vendored `aeneas_sirk.sh` is a
  working standalone copy (regenerates end-to-end, exit 0) for the planner;
  the specialist consumes only the generated `aeneas/SirkCoreModel.lean`.
- `docs/*.cdb`: the Cadabra2 derivation notebooks (`yang_mills_hamiltonian`,
  `qg_starobinsky_hamiltonian`, `qg_starobinsky_vielbein_hamiltonian`).
  **Reference text only — never run.**  The specialist has no Cadabra2; the
  operative algebra is stated inline in `MASS_GAP_SPEC.md`.
- `prob_kernel/tests/fixtures/gap_certificate.ndjson`: the `lean4export`
  fixture, **nanoda-verified by the planner** (2026-08-29: all 12 `verify::`
  tests green).  Retained as input data until regenerated after source
  changes.

## Division of labour (who does what)

**The Lean4 specialist needs no Rust compiler and never reads `../unfer`.**
Every executable step that involves Rust — running the numerical suites,
emitting fresh NDJSON, running nanoda, regenerating the Aeneas model — is the
**planner's job**, done in `../unfer` and re-vendored here. The specialist's
surface is exactly: this bundle (spec + fixtures + generated Lean model) plus
the Lean proof modules, verified by `lake env lean` on the touched module
and `#print axioms`.

## Regeneration gate (planner — after any Rust change)

After a Rust Hamiltonian, outer-enclosure, solver, or certificate change in
`../unfer`, the planner must:

1. Run the corrected QYM/QED/QG/NS numerical suites in `../unfer` and emit
   fresh NDJSON.
2. Record source revision, Hamiltonian constructor, coupling, truncation,
   Krylov order, shifts, and a cryptographic hash of the emitted data.
3. Re-run `../unfer/sirk_core_model/scripts/aeneas_sirk.sh` (the vendored
   `sirk_core_model/aeneas_sirk.sh` is a working standalone copy of the same
   script) and inspect that the generated Lean model is complete rather than
   partial.
4. Re-export the Lean theorem instantiation using the generated certificate
   data.
5. Run nanoda through `prob_kernel::verify::verify_export` (the
   `gap_certificate_proof_verifies_in_nanoda` test) on the emitted export.
6. Replace the vendored fixture and generated artifacts, and update
   `STATUS.md`, only after both Aeneas and nanoda succeed.

The old fixture is not evidence for a corrected implementation. A successful
finite certificate still does not prove the continuum mass gap; the
one-particle positivity/edge theorem and its outer `dΓ` lift remain separate
formal obligations.

**Status 2026-08-29:** gate steps 3 and 5 are green on the current bundle —
`cargo test -p prob_kernel --lib verify::` passes all 12 tests including
`gap_certificate_proof_verifies_in_nanoda`, and the vendored
`sirk_core_model/aeneas_sirk.sh` runs end-to-end (exit 0, 7 expected f64
errors, `SirkCoreModel.lean` byte-identical to committed).

## Regeneration log

### 2026-08-29 — Aeneas model re-run (source rev `1767a52` in `../unfer`)

- Ran `sirk_core_model/aeneas_sirk.sh` against the live `../unfer` core
  (`unfer/sirk_core_model/scripts/aeneas_sirk.sh`). Charon extracted the
  pure core to `.llbc`; Aeneas emitted the partial Lean model (7 expected
  f64-arithmetic errors, `sorry` bodies — the documented honesty boundary).
- **Script bug fixed in both copies** (`aeneas_sirk.sh`): Aeneas exits
  non-zero on the expected errors, which under `set -e` aborted the script
  *before* the rename steps — the `aeneas/` outputs were never refreshed.
  The fix captures the exit status and only treats a run that produces no
  `Lib.lean` at all as fatal.
- Result: `aeneas/SirkCoreModel.lean` and `aeneas/sirk_core_model.llbc`
  regenerated; byte-identical to the vendored copies (the vendored bundle
  was already current — the *live* repo's committed artifacts were stale,
  carrying line numbers from an older `src/lib.rs`).
- **Charon `.llbc` output is byte-nondeterministic between runs**: two runs
  from the same `src/lib.rs` produce the same declaration sets (25 funs, 7
  types, 5 traits, 6 impls, 3 globals, 46 item names) but a different
  serialized `ordered_decls` key ordering, so the `.llbc` bytes differ run
  to run. This is expected; the generated `SirkCoreModel.lean` (the artifact
  the Lean specialist consumes) is byte-identical across runs. Do not treat
  a differing `.llbc` byte layout as a source change.
- Cleanup: the stale crate-root `Lib.lean`/`lib.llbc` duplicates (tracked
  since `e0dfb3d`, superseded by the `aeneas/` normalization) were removed
  by the script's own `mv`; README documents only the `aeneas/` outputs.

### 2026-10-05 — PLAN M items M1–M6 landed; gate run for the first time from one command

- Source revision at the time of the run: `a5a105f` in `../unfer`; toolchain
  `rustc 1.97.1 (8bab26f4f 2026-07-14)`.
- **M1 — the per-coupling campaign ran and produced 20 pinned fixtures**
  (`../unfer/fock_sirk/tests/fixtures/mass_gap_campaign/`, SHA-256 manifest in
  `MANIFEST.tsv`). Grid: `g ∈ {0, 0.5, 1, 2, 3}` × `m ∈ {10, 12}` × exact
  cross-check `N ≤ {6, 8}`.
- **The campaign's headline result, and it is negative: no row certifies a
  positive gap.** All 20 carry `certified_positive: false`. At `g = 1, m = 12` the
  certified window is `[-8.009312, +6.866393]` against an exact truncated gap of
  `0.0911` — roughly **87× wider than the gap it must resolve**.
- **RETRACTION, recorded twice the same day — the second supersedes the first.**
  - *First error:* this entry blamed the eigendecomposition backward error
    `c(n)·u·‖Ĝ‖`. That was inferred from `c(n) = n³` growing without measuring, and
    it is wrong: that term is `6.0e-11` at `m = 10` and `7.0e-08` at `m = 64`, i.e.
    **eight orders of magnitude below** a width of ~3–7. The width is essentially all
    Parlett residual `‖r‖`.
  - *Second error:* the entry then concluded the extraction was "unvalidated"
    because `θ₀` is bit-identical across shift sets and sits above `E₃`. **Both
    inferences were wrong.** Shift-invariance is the *expected* signature: shifts
    change the basis, not the minimal-polynomial subspace `K(H, u₀)` the Krylov
    sequence spans, so a converged `θ₀` must be shift-invariant (and the basis does
    respond — `scales`, `G`, `h_proj` all move). And the `E₃` comparison spanned two
    different Hilbert spaces: the solve is capped by `max_components = 200_000`, so
    capping it at 495 (the `N ≤ 8` dimension) makes it explode at 571 components.
    The Ritz bounds are internally consistent throughout.
- **The anomaly that does survive, and its measured mechanism.** The one-step step
  norms `τ_k = scales[k] = ‖(H − z_k I)u_{k−1}‖` grow without bound — `6.409e+1` at
  `m = 4` to `6.010e+3` at `m = 48`, ~94×, no plateau — and the width inherits them,
  because `ritz_abs_residuals` forms `e[j] = (z_j − θ)ĉ[j] + τ_{j+1}ĉ[j−1]` and
  `e[m] = τ_mĉ[m−1]`, then contracts `e†Ge`.
- **The reference method's rate is available here; its *quantity* is not.**
  `papers/Hashimoto.md` (Hashimoto–Nodera, JJIAM 2019) concludes that for SIRK "the
  decay speed of the approximation error … is similar to an **exponential order**",
  while Arnoldi/SIA/RK reach only "the polynomial order or slower", because SIRK's
  vectors are built from **resolvents** `(γI − A)⁻¹`, *which are bounded*.
  - **The inverse-free design does NOT block the rate.** With harmonic shifts
    `γ_k = γ_0 + kh` and `X = (γ_m I − H)⁻¹`, the one-step chain is
    `w_k = (−1)^k X^{−k}Π_{j=1}^{m−k}(1 − hjX)v` — a cleared-denominator form of the
    resolvent chain, differing only by scalars that the unit-norm frame removes. The
    rate is a property of the rational Krylov space, and the start vector is free.
  - **The quantity is what blocks it.** Hashimoto's rate is for the **φ-function
    approximation error** `‖φ_k(H)v − approx‖`. `certified_width` consumes the Ritz
    residual `‖Hψ − θψ‖`, and the gap needs `|E₁ − E₀|` — three different quantities.
    Exponential convergence of the first does not make the third small, and the
    regime is brutal: gap `0.091` inside a `−1.7 … +337` spectrum (~3.7e3 ratio).
    Nothing in Hashimoto bounds the gap more sharply than the a-posteriori residual
    does today.
- The `τ_k` growth and the residual growth measured above are observations about
  **this residual pipeline**, not evidence that the method lacks an exponential rate.
- **Two escapes measured, both refuted:**
  - *Fixed window width.* `shifts_for_range((0,m))` widens with `m`; pinning it to
    width 2 leaves `resid₀` climbing `2.73 → 4.82` at full rank.
  - *Window off the spectrum.* `resid₀` falls only where rank collapses
    (`R = 400`: rank 3→9, `θ₀` frozen at ≈ −1.51; `R = 3000`: rank 3→4, `θ₀` ≈ −1.04).
    That is polynomial-Krylov degeneracy once `|γ| > ‖A‖`, not convergence.
- **What this means for the existing suite.** `qcd_mass_gap_certified`'s
  "certified window contains the exact gap" assertion currently passes
  **vacuously**: a window of `±8` centred on `−0.57` contains `0.091` regardless of
  width quality. It becomes meaningful only once the residual bound is tightened.
- One encouraging observation, since it bears on whether the programme is viable:
  the exact *gap* is N-stable (`0.091073` at `N ≤ 6` → `0.091161` at `N ≤ 8`) even
  though the absolute energies are not (`E₀ = −2.025 → −2.744`). The gap is the
  well-conditioned quantity.
- **Three corrections to the plan's own framing**, all found by running it:
  - The SIRK sector-assembled `gap` (`−0.571` at `g = 1`) and the exact truncated
    gap `E₁−E₀` (`+0.091`) are **different quantities**. The "≈ 0.09 at `g = 1`"
    figure in `MASS_GAP_SPEC.md` and in `PLAN_MASS_GAP.md` §5 refers to the
    *exact* truncated gap.
  - `N` is **not** a solve parameter of the SIRK solve (the truncation knobs
    `max_components`/`adaptive` bound memory, they do not set the inner
    occupation ceiling). `N` is therefore carried as the exact-diagonalization
    cross-check axis and `m` as the solve axis.
- **M2 — the gate now exists as one command**: `bash scripts/regen_mass_gap.sh`
  (`--check` to verify wiring, `--strict` to fail on any unavailable step). Its
  first run on this host: steps 1 and 4 green, step 2 (Aeneas) and step 3
  (`lean4export`) **UNAVAILABLE** — the Aeneas release bundle is not installed
  and `lean4export` needs network. The gate therefore reported `INCOMPLETE`,
  refused to touch any vendored fixture, and said so. **This is not a green gate
  and must not be recorded as one.**
- Step 4 is worth stating on its own: **nanoda re-verification is green** over the
  pinned payloads, so the Lean-side proof artifacts still check against an
  independent kernel.
- **M3 — `MASS_GAP_SPEC.md` had already drifted** (sha `f3ebdb89…` vs `e3fe9f9d…`).
  Inspection showed the differences were *intentional* (this bundle is
  self-contained: rewritten `.cdb` paths, its own "never run the `.cdb` files"
  preamble, in-bundle pointer prose). A byte-sync would have destroyed that, so
  the gate checks **operative parity** — 22 anchors covering the Hamiltonian, the
  `B` field, each width term, the T6 statement, the `Z₂` reflection and the
  frozen API names. Verified against a planted one-term width change, which it
  caught.
- **M5 — 12 property tests** on the pure `mass_gap_spec` functions
  (`../unfer/fock_sirk/tests/mass_gap_properties.rs`): width monotonicity in the
  residual and in `‖Ĝ‖`, non-negativity, interval reflexivity, `lo ≤ hi`, the T6
  endpoint identity, `certified_positive` following `lo`, backward-error
  monotonicity in the rank, and the pinned `UNIT_ROUNDOFF`. **The Kani half of
  M5 is NOT done** — no `#[kani::proof]` harness exists and `kani` is not a
  workspace dependency.
- **M9 — the non-claim guard** (`scripts/check-non-claims`) passed on 70 documents
  with **zero false positives**, and caught a planted continuum overclaim. Its
  first version flagged four *correct* lines of prose that explain the
  truncated/lattice distinction; it was rewritten narrow rather than shipped
  crying wolf. Two bugs found while building it: `awk` does not support `\s`, and
  `.` does not match the multibyte `²` in `g²/2` — so the B2 pattern had to be
  spelled `g[^ ]{0,3}/ *2` or it silently never matched anything.
