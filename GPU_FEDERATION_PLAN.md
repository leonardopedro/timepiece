# GPU Federation Improvement Plan

Source vision: `unfer/docs/GPU.md` (edge-native AI inference stack: velysterm →
unfer → australVM → FreeToken, with WhyML-verified hardware invariants and a
deterministic AI feedback loop).

Scope: the five-repo federation — `unfer`, `australVM`, `velysterm`,
`dynamic-arctic`, and this repo (`timepiece`, Lean 4 formal verification).

Guiding rule (per request): **every item below improves existing features and
code. Nothing here creates a new standalone feature.** New-feature items from
the vision (MLIR emission, a FreeToken runtime) are analyzed at the end and
explicitly deferred, with the existing-code improvements that would need to
land first.

---

## 1. Ideas extracted from GPU.md

| # | Idea | What GPU.md says |
|---|------|------------------|
| I1 | **Comptime math engine** | velysterm computes tile sizes, unroll factors, loop polynomials at compile time |
| I2 | **Layout verification** | unfer solves bank-conflict constraints and verifies thread/warp layout bijectivity *before* codegen |
| I3 | **WhyML hardware invariants** | australVM attaches WhyML pre/postconditions to ops; Why3 proves DMA never overflows NPU SRAM, warp-sync can't deadlock |
| I4 | **MLIR emission** | emit `gpu`/`nvvm`/`linalg` (GPU) and `vector`/`llvm` (CPU) dialects instead of Cranelift |
| I5 | **FreeToken runtime** | zero-copy CPU/GPU KV-cache handoffs via linear borrows; async token pipelining with no runtime locks |
| I6 | **Deterministic AI feedback loop** | every failure is a machine-readable artifact: bank-conflict equation, linear-lifetime error, or Why3 proof rejection |

## 2. What already exists (the improvements will build on this)

| Repo | Existing feature | GPU.md idea it already half-implements |
|------|------------------|----------------------------------------|
| unfer | `fock_sirk` GPU pipeline: `StateDictionary` (registry.rs) flattens sparse Fock states → dense indices, `TensorState` (tensor_state.rs) uploads to a candle CUDA device, `whiten_gram` + `forward_sirk` run the Krylov solve | I2 (the "Linear Layout" is exactly `StateDictionary`, currently unverified) |
| unfer | `device.rs` `best_device()` + `examples/debug_cuda.rs` CUDA probe | I6 (probe prints raw candle errors, not machine-readable ones) |
| unfer | `prob_kernel/src/whyml.rs` (S36): kernel emits WhyML → `why3 prove` → extract OCaml → australVM loads it as a compiler pass | I3 (the *cycle* exists; only the authorization gate is emitted) |
| unfer | `unfer_protocol/src/codes.rs` UK-#### registry + `RepairHint` contract; S29 `verify_export` (nanoda re-checks `lean4export` proofs) | I6 + the "machine-checked" half of I2 |
| australVM | `lib/why3_plugin.ml` + `lib/why3_plugin/authorize_gate.mlw` + extracted `lib/authorize_gate.ml`; installed via `Vm_plugin.boot`; `Compiler_plugin.run_on_typed` seam | I3 (one verified pass; the seam is generic) |
| australVM | `lib/deltanet_plugin.ml` (UNF arbiter pass) — second example of the same pass pattern | I3 (proves the multi-pass pattern works) |
| velysterm | `crates/delta_algebra` + `crates/delta_sirk`: wgpu GPU Hermite-recursion evaluator for Fock spaces — **orphaned**, excluded from workspace | I1 (the comptime GPU math engine, half-built and stranded) |
| velysterm | `mathed_core` `PropKind`/`SemanticIndex` extension point + `RepairHint` diagnostics; `mathed_mini` constrained-hardware frontend | I6 (the repair-hint plumbing for the feedback loop) |
| timepiece | Lean 4 formalizations (Singularity/, BookProof/); precedent: `unfer/logos/lean/Confluence.lean` → `lean4export` 3.1.0 → pinned `prob_kernel/tests/fixtures/confluence.ndjson` → re-verified by nanoda (S29) | the *proof muscle* for I2's "verify bijectivity" claim |
| dynamic-arctic | `arctic_core`/`shine_core` threshold signatures, consumed by `unfer_consensus` as the certificate-ledger threshold mint authority | I5's trust layer (kept as-is; hardened in T0.3) |

---

## 3. Implementation plan (prioritized)

### Tier 0 — Small, existing-code hardening (highest leverage)

#### T0.1 — Verify `StateDictionary` layout bijectivity (unfer, I2)

GPU.md's core layout claim is "the layout mapping is perfectly bijective".
`StateDictionary` (`fock_sirk/src/registry.rs`) is that mapping (`OuterState ↔
index`), but nothing checks the invariant today. A single HashMap entry
mismatch would silently corrupt the Gram matrix.

- Add to `StateDictionary` (or a debug helper in `lib.rs`):
  - an invariant check that `state_to_index` and `index_to_state` are mutual
    inverses (`index_to_state[i]` re-inserts to `i`, for all `i < len`),
    invoked from `TensorState::from_quantum_state` and `solve_forward_sirk`
    under `debug_assert!` (zero cost in release);
  - a unit test that re-insertion round-trips and that the map stays bijective
    across `get_or_insert` growth (mirrors `registry.rs`'s style).
- Files: `unfer/fock_sirk/src/registry.rs`, `unfer/fock_sirk/src/tensor_state.rs`.
- Verify: `cargo test -p fock_sirk` (CPU), then `--features cuda` if a GPU is
  present.

#### T0.2 — Revive `delta_algebra`/`delta_sirk` as the comptime GPU engine (velysterm, I1+I6)

These are the only wgpu code in the federation and are excluded from the
workspace (`velysterm/Cargo.toml` `exclude = [..., "crates/delta_algebra",
"crates/delta_sirk"]`). They already implement Pass 1 of the GPU.md vision —
Hermite-recursion expansion in WGSL (`expand.wgsl`: annihilation/creation with
`sqrt(n)` factors) with `tokio::test` harnesses. Per the ENG_PLAN review rule
("start with a correctness oracle, not an optimization"), the improvement is:

- Re-add the crates to the workspace, gated so CI without a GPU still passes:
  keep them in `exclude`, but add a `--workspace-gpu`-style explicit test path
  (or a `delta-gpu` feature) instead of leaving them fully orphaned;
- Add **differential tests** against the CPU reference
  (`nested_fock_algebra`'s Hermite recursion in unfer): same input states +
  operator terms → wgpu result must match the CPU result; on machines without
  a GPU adapter, skip with a clear message (the Cadabra2 skip pattern from
  unfer's S30);
- Add a `cargo run -p delta_sirk --example` (or extend the existing harness)
  that exercises the QHO resolvent pipeline end-to-end — the code already
  exists in `delta_sirk/src/lib.rs`.
- Files: `velysterm/Cargo.toml`, `crates/delta_algebra/src/{lib.rs,types.rs,expand.wgsl}`, `crates/delta_sirk/src/lib.rs`.
- Verify: `cargo test -p delta_algebra -p delta_sirk` (skips gracefully without
  a GPU); `cargo clippy -p delta_algebra -p delta_sirk -- -D warnings`.

#### T0.3 — Harden the Arctic threshold authority (dynamic-arctic, I5 trust layer)

No GPU.md feature needs new threshold code; the existing `arctic_core` +
`shine_core` library is already the federation's authority layer via
`unfer_consensus`'s `MintAuthority::Threshold`. The improvement is to the
**tests**: add a deterministic integration test that exercises the
identifiable-abort path end-to-end (one malicious node in the coalition →
correct signature still produced and the bad share isolated), which the README
claims but no test currently pins, and assert the 64-byte aggregate signature
round-trips through `verify_arctic_threshold`.
- Files: `dynamic-arctic/src/arctic_core.rs` (tests), `dynamic-arctic/src/shine_core.rs` (tests).
- Verify: `cargo test` in `dynamic-arctic`; `cargo test -p unfer_consensus` in unfer.

### Tier 1 — GPU.md's central idea through the existing Why3 seam

#### T1.1 — Second WhyML program: the NPU SRAM/DMA invariant gate (unfer + australVM, I3)

GPU.md's headline: "WhyML Proves GPU/NPU-specific spatial invariants". The
entire cycle already exists (S36); only the *program* is missing. The GPU.md
worked example is exactly the right second program:

```whyml
val constant MAX_NPU_SRAM : int = 262144
type npu_buffer = { size: int; offset: int }
val async_tma_load (buf: npu_buffer) (bytes: int) : unit
  requires { bytes > 0 }
  requires { buf.offset + bytes <= MAX_NPU_SRAM }
```

- **unfer** (`prob_kernel/src/whyml.rs`): extend the emitter with a second
  spec variant (e.g. `WhymlSpec::NpuDma`) that renders the SRAM-bound program
  with `buf.offset + bytes <= MAX_NPU_SRAM` and a `dma_ok` postcondition.
  Reuse the existing `why3 prove` + extraction driver path; pin the emitted
  `.mlw` byte-identical (the `authorize_gate.mlw` precedent). The proof
  obligations are arithmetic — auto-provable by Why3's arithmetic provers
  (Z3/alt-ergo), same as the existing 5.
- **australVM**: add `lib/npu_dma_gate.mlw` + extracted `lib/npu_dma_gate.ml`
  (regenerate via the documented Why3 toolchain; `unfer_ocaml.drv` already
  handles the int mapping), and a `NpuDma_plugin` pass following
  `why3_plugin.ml` exactly: install it in `Vm_plugin.boot` next to
  `Why3_plugin.install`; the pass rejects any compiled module whose
  `@dma(bytes, buf)`-annotated foreign calls exceed `MAX_NPU_SRAM`. Gate the
  annotations on the typed IR (`Compiler_plugin.run_on_typed` seam) so this is
  an improvement to the existing pass infrastructure, not a new subsystem.
- Verify: `cargo test -p prob_kernel whyml` (unfer) + `dune runtest` in
  australVM (per the S36b loader note in `australVM/AGENTS.md`).
- Contract note: this adds a `uk_whyml_emit` spec variant, **not** a new
  `uk_*` symbol, so the S29 checklist (EXPECTED_SYMBOLS.txt, C header,
  UNFER_SYMBOLS, GrantSet) is untouched. If a `@dma` attribute lands on
  Austral's typed IR, update `australVM/lib/Compiler_cps.ml`'s foreign-name
  resolution only if the attribute needs lowering.

#### T1.2 — Machine-readable layout diagnostics (unfer + velysterm, I6)

GPU.md's feedback loop requires layout failures to be deterministic artifacts
("Bank conflict: 2x + 4y ≡ 0 (mod 32) has no safe swizzle"). The diagnostic
contract (UK-#### + `RepairHint`) exists; layout is just not in it.

- **unfer** (`unfer_protocol/src/codes.rs`): add a small `49xx` layout family
  (e.g. `LAYOUT_NOT_BIJECTIVE = 4905`, `BANK_CONFLICT_UNRESOLVED = 4906`,
  `SWIZZLE_IMPOSSIBLE = 4907`) — same pattern as the 480x/490x entries
  (const + the doc table at ~line 509 + the code list ~line 517). A new code
  is *not* a new `uk_*` symbol (no ABI change), but update the code's
  `REASON` doc strings so agents see them verbatim.
- **unfer** (`fock_sirk/src/registry.rs` + `linalg.rs`): when the T0.1
  invariant fails or the Gram/whitening hits a degenerate layout, return a
  `SirkError` carrying the machine-readable conflict equation instead of a
  bare panic/message.
- **velysterm** (`crates/mathed_core`): register the new codes in the
  `SemanticIndex`/diagnostic layer (extension point #3 in
  `unfer/docs/ARCHITECTURE.md` — new kernel-bearing `PropKind` for a "layout"
  statement) so `mathed`'s overlay and `unfer_agent`'s NDJSON surface the
  code + `ReplaceValue` hint exactly like every other UK error.
- Verify: `cargo test -p unfer_protocol`; `cargo test -p mathed_core`; the
  `unfer_agent` smoke test from `velysterm/AGENTS.md`.

### Tier 2 — Formal verification muscle (timepiece ↔ unfer, I2)

#### T2.1 — Lean proof of layout bijectivity + bank-conflict impossibility (timepiece + unfer)

This is the Confluence.lean precedent, applied to the layout claims of GPU.md.
`timepiece` is the federation's machine-checked-proof repo; `unfer` already
re-verifies exported Lean proofs with nanoda (S29), and the pinned
`confluence.ndjson` fixture proves the pipeline end-to-end.

- **timepiece**: add a `Layout/` (or extend the existing lake project) with:
  1. **Bijectivity lemma**: for the `StateDictionary` construction, the map
     `state ↦ index` produced by `get_or_insert` is injective (two distinct
     `OuterState`s never collide) and `index_to_state` is its inverse;
  2. **Bank-conflict theorem**: the GPU.md example — the congruence
     `2x + 4y ≡ 0 (mod 32)` admits no bijective swizzle that separates
     conflicting addresses (formalize the pigeonhole/parity argument);
  3. (optional, if cheap) tile-shape algebra associativity used by the
     comptime engine.
  Keep the proofs `rfl`/kernel-computed where possible — the S31 note says
  `native_decide`/`decide` terms break nanoda, so follow the Confluence.lean
  discipline (export with official `lean4export` 3.1.0 on the pinned
  toolchain, `rfl`-based reduction).
- **unfer**: pin the exported NDJSON as a new fixture (e.g.
  `prob_kernel/tests/fixtures/layout_bijective.ndjson`) and add a
  `verify_export` test that re-checks it — the S31 pattern verbatim.
- Verify: `lake build` in timepiece; `cargo test -p prob_kernel` in unfer.
- This is the improvement that makes T0.1's `debug_assert` a *proven* claim
  rather than a tested one.

#### T2.2 — Actionable GPU device diagnostics (unfer, I6)

`debug_cuda.rs` prints raw candle errors; `AGENTS.md` already documents the
failure modes (ARCH_MISMATCH from libcublas/libcuda version conflicts,
LD_LIBRARY_PATH guidance). Improvement: make `best_device()`/the probe emit
the documented triage steps as structured output (stderr lines the agent loop
can parse: `UK-GPU-ARCH_MISMATCH → check LD_LIBRARY_PATH vs driver`, etc.),
and have `fock_sirk` tests/benches report "skipped: no CUDA" the way S30
tests skip without cadabra2.
- Files: `unfer/fock_sirk/src/device.rs`, `unfer/fock_sirk/examples/debug_cuda.rs`.

### Tier 3 — Explicitly deferred new features (why, and what must land first)

Per the guiding rule, these are **not** in this plan:

- **I4 — MLIR emission** (australVM). Replacing/adding a Cranelift→MLIR
  backend is a new subsystem, not an improvement. The verified-lowering
  discipline it presupposes is exactly T1.1 (WhyML-checked passes on the typed
  IR). Land T1.1 first; if a GPU backend is ever wanted, the `gpu`/`nvvm`
  dialects can hang off the existing `Compiler_cps.ml` CPS IR the same way the
  Cranelift path does today.
- **I5 — FreeToken runtime**. There is no runtime crate in the federation to
  improve. The closest existing analogs — `fock_sirk`'s `TensorState` upload
  and `unfer_data`'s encrypted data plane — are the improvement targets if
  zero-copy handoff is ever pursued (e.g. reuse device tensors across SIRK
  restarts instead of re-allocating in `from_quantum_state`). Note it in
  `unfer/docs/GPU.md` as a future direction; don't build it now.

---

## 4. Execution rules (shared across repos)

1. **Ownership**: each step touches only files in its own repo; cross-repo
   *reads* are fine, cross-repo *writes* only for the documented sync points
   (T1.1's `.mlw`/`.ml` pinning is emitted from unfer and committed in
   australVM — follow the S36 two-repo cycle exactly).
2. **Frozen contract**: no changes to the 21 `uk_*`/5 `uz_*` signatures or
   `prob_kernel::Session`'s public API. T1.2 adds codes, not symbols; T1.1
   adds a spec variant, not a symbol.
3. **Style**: keep lines ≤ 100 chars, no trailing whitespace; new `uk_*`-adjacent
   surface (only T1.2 codes) must stay in the documented registry lists.
4. **Verification per step**: run the repo-local commands listed in each tier
   before moving on; keep `unfer` green at all times (both dependents read its
   working tree via path deps).
5. **Ordering**: T0.1 → T0.2 → T0.3 (independent, any order) → T1.1 → T1.2 →
   T2.1 → T2.2. T1.1 unblocks nothing downstream but is the highest-value
   GPU.md item; T2.1 is the cheapest way to make the layout claim
   machine-checked.

## 5. Expected outcome

After this plan, the GPU.md vision is realized entirely as improvements:
- I1: the wgpu comptime engine is back in the workspace and differential-tested;
- I2: the existing `StateDictionary` layout is verified (debug invariant +
  Lean proof re-checked by nanoda) and its failures are machine-readable;
- I3: the Why3 cycle emits and enforces the NPU SRAM/DMA invariant as a
  second compiler pass;
- I6: layout and GPU failures surface as UK-#### + `RepairHint` artifacts the
  agent loop can ingest.

## 6. Execution status (all items DONE)

Executed 2026-08-27; every verification command below passed.

| Item | What landed | Verified by |
| :--- | :--- | :--- |
| T0.1 | `StateDictionary::is_bijective`/`bijective_violation` + `debug_assert!` at the CPU→GPU upload point (`registry.rs`, `tensor_state.rs`); new `SirkError::LayoutNotBijective` (`linalg.rs`) with `UK-4905` diagnostic arm (`prob_kernel/src/error.rs`) | `cargo test -p fock_sirk --lib` (34), `-p prob_kernel --lib` (56), clippy clean |
| T0.2 | `delta_algebra`/`delta_sirk` revived in the workspace (`Cargo.toml` members); `engine_or_skip` graceful skip; CPU reference oracle (`reference.rs`, Hermite recursion) with differential tests; `qho_sirk` example; `scripts/test-delta-gpu.sh` | `cargo test -p delta_algebra -p delta_sirk` (ran on GPU adapter; skip path verified), clippy clean |
| T0.3 | Arctic identifiable-abort path pinned: `signature_to_bytes` wire-format helper, per-share verification, `robust_combine` honest/all-bad/one-malicious tests — caught and fixed a real `l_i_0` mis-application in `robust_combine` | `cargo test` (19 pass), clippy clean |
| T1.1 | `WhymlProgram::NpuDmaGate` (`unfer_protocol::types`); NPU SRAM/DMA gate emitter in `prob_kernel/src/whyml.rs` (byte-identical emission test); pinned `npu_dma_gate.mlw/.ml/.mli` + `npu_dma_plugin.ml` pass installed in `Vm_plugin.boot` (australVM) | `cargo test -p prob_kernel --lib whyml` (12); `dune build`; all 7 `PluginTest` cases via the host dynamic loader (S36b); 8/8 other test exes OK (JitTest 2 errors pre-existing, verified by stash) |
| T1.2 | UK-4905/4906/4907 layout codes pinned (`unfer_protocol/src/codes.rs` + `tests/protocol.rs`); velysterm `PropKind::Layout` (kernel-bearing, extension point #3: `markers.rs` → collection → `kernel_bridge` dispatch → overlay annotation + accessibility) surfacing `UK-4907` + `ReplaceValue` hint for `2x + 4y ≡ 0 (mod 32)` | `cargo test -p unfer_protocol`; `cargo test -p mathed_core -p mathed_mini` (154/125); `cargo check -p mathed`; `unfer_agent` smoke |
| T2.1 | `Layout/Layout.lean` (8 `rfl` certificates: StateDictionary bijectivity, inverse lookup, `get_or_insert` stability/append, collision pair, parity, pigeonhole image-size, 32×32 grid) registered in the lake project; exported with official lean4export 3.1.0 (revision `d065b00` backport, Lean 4.28.0) to `unfer/prob_kernel/tests/fixtures/layout_bijective.ndjson`; `layout_proof_verifies_in_nanoda` re-verifies it | `lake build Layout`; `cargo test -p prob_kernel layout` (nanoda OK); confluence test still OK |
| T2.2 | `GpuTriage` codes + `probe_cuda`/`CudaProbe` in `fock_sirk/src/device.rs` emitting parseable `UK-GPU-<CODE> → <fix>` stderr lines (NO_DEVICE / ARCH_MISMATCH / LIBRARY_MISSING / OUT_OF_MEMORY / OTHER); `debug_cuda.rs` probe example; triage unit tests | `cargo test -p fock_sirk --lib device` (2), clippy clean |

**Deferred as planned** (Tier 3): MLIR emission, FreeToken runtime — new subsystems, not improvements; the prerequisites (T1.1-style verified lowering, zero-copy handoff hooks) are noted in §3.

**Pre-existing, out of scope, left as found**: australVM `JitTest` `run`-name collisions (persistent engine — documented in unfer AGENTS.md S36b); `cargo check --features cuda` needs `nvcc` (no CUDA toolkit on this machine — CPU-only builds verified).
