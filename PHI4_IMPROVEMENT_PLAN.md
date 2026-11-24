# Real Scalar λφ⁴ — Master Improvement Plan (Cheap-LLM Execution Guide)

> **Purpose:** Self-contained, step-by-step work plan for a smaller/cheaper LLM to
> bring all real scalar λφ⁴ formalization (Lean 4 in `./`), analytical calculus
> (Cadabra2 in `../unfer/docs/`), and numerical SIRK calculations (Rust in
> `../unfer/nested_fock_algebra/` and `../unfer/fock_sirk/`) into strict alignment
> with [book.tex](book.tex).
>
> **Core architectural principles (pinned 2026-11-23):**
> 1. **Continuous momentum space — integrals `∫ d³k`, NEVER discrete momentum sums.**
>    In the `book.tex` SIRK / Mehler / nested-Fock framework, **only the Krylov
>    subspace (and finite Mehler-Hermite occupation window) in SIRK approximations
>    is discrete — NEVER space and NEVER momentum space.** Every vector in the
>    discrete Krylov subspace remains a function of continuous variables
>    `(k₁, k₂, k₃, φ) ∈ ℝ³ × ℝ`.
> 2. **No spatial-derivative jet constraints are needed for λφ⁴.** Coordinate-space
>    first-jet constraints `iD_x = 0` in `book.tex` are trivially satisfied (and
>    avoided) in continuous momentum space, where spatial derivatives become
>    multiplication by `k` and products become continuous momentum-convolution
>    integrals `∫ d³p`. Moreover, for λφ⁴ the gradient `½ ∫ |∇φ|² d³x` is
>    **quadratic** in `φ`, so by Plancherel it becomes the pure diagonal
>    continuous multiplier `½ ∫ |k|² |φ̂(k)|² d³k` (no derivative convolution
>    needed at all!), while the derivative-free quartic potential
>    `(λ/4) ∫ (φ² − v²)² d³x` is the continuous composite-pair integral
>    `(λ/4) ∫ d³Q |Ψ(Q)|²` with `Ψ(Q) = ∫ d³p φ̂(p) φ̂(Q − p) − v² δ⁽³⁾(Q)`.
> 3. **100% focus on this continuous-momentum SIRK / Mehler / nested-Fock
>    formalism (`momContModel` on `L²(ℝ³_k × ℝ_φ) = L²(ℝ⁴)` + continuous Schwartz
>    convolution integral `∫ d³Q |Ψ(Q)|²`).** Periodic spatial lattices
>    (`siteModel`, `twoSite`, `ScalarGrid`), auxiliary static-jet models
>    (`jetModel`), discrete-momentum truncations, and legacy Higgs builders are
>    **frozen comparisons only**.
> 4. **Leave `Book/` untouched** for now. Documentation in `../test/` is maintained
>    separately (do not rewrite `../test/` prose).
> 5. **Zero `sorry`, zero skipped checks, zero unverified claims.** Run every
>    task's exact verification command and require exit code `0` before moving on.

Companion plans (synchronized with this guide):
- [PHI4_FORMALIZATION_PLAN.md](PHI4_FORMALIZATION_PLAN.md) (Lean 4 contract)
- [../unfer/docs/PHI4_ANALYTIC_PLAN.md](../unfer/docs/PHI4_ANALYTIC_PLAN.md) (Cadabra2 contract)
- [../unfer/docs/PHI4_NUMERICAL_PLAN.md](../unfer/docs/PHI4_NUMERICAL_PLAN.md) (Rust / `fock_sirk` contract)

---

## 1. Hard Framework Contract & Anti-Mixing Guardrails

Read this table before touching any file. **NEVER violate any row below:**

| Topic | **DO (Exact `book.tex` Continuous-Momentum Framework)** | **DO NOT (Forbidden Mixing)** |
|---|---|---|
| **Continuous momentum arena** | Work on the **continuous** space `L²(ℝ³_k × ℝ_φ) = L²(ℝ⁴)` with coordinates `(φ, k₁, k₂, k₃)` (`0 ↦ φ`, `1,2,3 ↦ k₁, k₂, k₃`), Mehler Gaussian measure `e^{−(‖k‖²+φ²)/2}`, and probabilists' product Hermites `He_α(φ, k) e^{−(‖k‖²+φ²)/4}` (norm² `= α! (2π)²`). Momentum space is integrated with **`∫_{ℝ³} d³k`**; **only the Krylov / Hermite subspace in SIRK is discrete**. | **NEVER** discretize momentum space into sums `∑_m` or `∑_Q` over a periodic box. **NEVER** use a spatial lattice (`siteModel`, `ScalarGrid`) or finite-difference gradient as the primary model. **NEVER** introduce spatial-derivative jet constraints for λφ⁴. |
| **Gradient & quartic potential** | On `L²(ℝ³_k × ℝ_φ)`, the continuous quadratic gradient couples `|k|²` directly to `φ²`: **`½ (k₁² + k₂² + k₃²) φ²`**. Retain the **entire** double-well square `U(φ) = (λ/4)(φ² − v²)²` (**including `λv⁴/4`**) inside `h_cont`:<br>`h_cont(k, φ) = ½ p_φ² + ½ |k|² φ² + (λ/4)(φ² − v²)²`.<br>For the full coordinate-space quartic in momentum space, write the **continuous integral** `(λ/4) ∫_{ℝ³} d³Q |Ψ(Q)|²` (never a discrete sum!), and state honestly that `h_cont` realizes the fibrewise-local quartic in `(k, φ)` while cross-momentum quartic convolution is the continuous integral operator over `ℝ³`. | **NEVER** decouple `k` from `φ` into `½(j₁²+j₂²+j₃²)` (that was the auxiliary `jetModel` with static uncoupled jets!). **NEVER** subtract `λv⁴/4`, **NEVER** normal-order `φ⁴` to drop contractions (`6:φ²: + 3`), **NEVER** Taylor-expand around `±v`, and **NEVER** use the legacy `nested_fock_algebra::cas` compiler. |
| **Outer enclosure (Quadratic Ordering)** | Assemble the complete inner operator `h` first, then apply a **single** outer lift `H = dΓ(h) = ∫ d³k dφ a†(k,φ) h(k,φ) a(k,φ) = ∑ᵢⱼ ⟨eᵢ, h eⱼ⟩ C†(eᵢ) A(eⱼ)` (`book.tex` lines 4030–4059), where `{eᵢ}` is a countable orthonormal basis of the separable Hilbert space `L²(ℝ³_k × ℝ_φ)` (NOT a discrete momentum grid!). | **NEVER** replace `dΓ(B²)` by `dΓ(B)²` (cross-particle defect at `n ≥ 2`). **NEVER** add number-changing outer terms. |
| **CCR convention** | Lean & Rust (`ChapterScalarMehler`, `exact_inner.rs`): `Q = b† + b`, `P = i(b† − b)/2 = −i∂`, so `[Q, P] = +i`. Only `φ` (coordinate `0`) carries a conjugate momentum `p_φ`; `(k₁, k₂, k₃)` are continuous momentum multipliers. | **NEVER** decouple `φ` and `p_φ` into separate modes. |
| **Mass gap terminology** | Distinguish strictly:<br>1. `H Ω = 0` (outer vacuum annihilation, needs no positivity).<br>2. Absolute inner lower bound `⟨ψ, hψ⟩ ≥ μ‖ψ‖²` (`μ > 0`) on all of `L²(ℝ³_k × ℝ_φ)` → lifts to strict outer gap `≥ μ` and unique outer vacuum ground state.<br>3. Inner excitation splitting `E_{odd,0} − E_{even,0}` inside the 1-outer-particle sector (NOT the outer vacuum gap). | **NEVER** call `E₁ − E₀` an outer mass gap. **NEVER** claim that `h_cont`'s unconditional local-fibre gap (`μ ≥ 7/64` at `λ=v=1`) settles full cross-momentum interacting QFT or 4D triviality. |
| **Hashimoto-SIRK numerics** | Use `fock_sirk::joint_sirk::solve_joint_sirk` with **`JointKrylovMethod::ShiftInvert`**, `B = V†(γI + iPHP)⁻¹V`, `G = γI − B⁻¹`, and compute full unprojected defects **`D = iVG − HV`** via `fock_sirk::sm_defect`. Vary Hermite occupation cutoff `C` and Krylov rank `m` independently. | **NEVER** substitute `JointKrylovMethod::ForwardProducts` for rational SIRK. **NEVER** compute defects using projected `PHP` images or unweighted Euclidean norms on unnormalized Hermite vectors. |
| **Cadabra2 rules** | Follow `../unfer/docs/CADABRA2_GOTCHAS.md`: stems `≥ 4` chars before `_` inside `@(...)`; no trailing `#` on `:=` lines; never write `x := len(ex)` (use Python `x = len(ex)`). Print `(0 = ok): 0` on every zero-check and pin `len(...)` sizes so `verify_cdb_modules.sh --strict` reports `[PASS]`. | **NEVER** link Cadabra2 into Rust (GPL-3.0 subprocess boundary only). **NEVER** treat `[NOTE]` from `verify_cdb_modules.sh` as a pass. |
| **Lean 4 hygiene** | Every line `≤ 100` characters, no trailing whitespace, zero `sorry`, and `Work/Phi4Audit.lean` must report only `[propext, Classical.choice, Quot.sound]`. | **NEVER** introduce custom axioms, `sorry`, or lines `> 100` chars. |

---

## 2. Pre-Verified Exact Mathematical Targets (Continuous Momentum `L²(ℝ³_k × ℝ_φ)`)

All formulas and rational numbers below have been independently checked in exact
rational arithmetic. Use them directly in Phases 1, 2, and 3.

### 2.1 Continuous-Momentum Inner Hamiltonian `momContModel` (`weylPoly` on `L²(ℝ⁴)`)

Coordinates `Fin 4`: `0 ↦ φ`, `1, 2, 3 ↦ k₁, k₂, k₃` (ALL FOUR CONTINUOUS!).
Active momentum: `momentum := fun _ : Fin 1 => (0 : Fin 4)` (`p_φ` only).
Four real polynomial forms (`r = 4`):
- `form 0 = √(λ/2) · (X 0 ^ 2 − v²)` (double-well wall, constant `λv⁴/4` retained)
- `form 1 = X 1 * X 0` (`k₁ φ`)
- `form 2 = X 2 * X 0` (`k₂ φ`)
- `form 3 = X 3 * X 0` (`k₃ φ`)

$$h_{\mathrm{cont}}(\vec{k}, \phi) = \frac{1}{2} p_\phi^2 + \frac{1}{2}(k_1^2 + k_2^2 + k_3^2)\,\phi^2 + \frac{\lambda}{4}(\phi^2 - v^2)^2.$$

Key structural properties:
- **Exact continuous 3D gradient `½ |k|² φ²`** directly couples continuous 3-momentum `k ∈ ℝ³` to the field amplitude `φ ∈ ℝ` — zero lattice, zero discrete momentum sum, zero jet constraints!
- **Exact `S₃` symmetry** under permuting `(k₁, k₂, k₃)`.
- Inherits `inner_esa`, `closure_nonneg`, `inner_flow`, `mehler_sirk`, `window_solve_convergence`, `outer_esa`, `outer_flow`, `outer_closure_nonneg`, `vacuum_ground`, and `Model.orbit_error` immediately from `BookProof.Phi4.Model`!

### 2.2 Exact 11-Mode `S₃`-Symmetric Table for `unitMomCont` (`λ = v = 1`, Unit Mehler Width)

By `S₃` symmetry of `(k₁, k₂, k₃)`, the 3-mode discrete Hermite window
`{1, He₂(φ), K₂ = ∑ᵣ He₂(kᵣ)}` (Gram `W = diag(1, 2, 6)`) closes **exactly**
under `h_cont` in **11 orthogonal continuous-variable Hermite modes**:

| Row | Label | Polynomial | Gram `Wᵢ` | Col 0 (`h·1`) | Col 1 (`h·He₂`) | Col 2 (`h·K₂`) |
|---:|---|---|---:|---:|---:|---:|
| 0 | `m₀` | `1` | `1` | `17/8` | `19/4` | `3` |
| 1 | `m₁` | `He₂(φ)` | `2` | `19/8` | `125/8` | `3` |
| 2 | `m₂` | `K₂ = ∑ᵣ He₂(kᵣ)` | `6` | `1/2` | `1` | `33/8` |
| 3 | `m₃` | `He₂(φ) K₂` | `12` | `1/2` | `5/2` | `35/8` |
| 4 | `m₄` | `He₄(φ)` | `24` | `1/4` | `35/8` | `0` |
| 5 | `m₅` | `He₆(φ)` | `720` | `0` | `1/4` | `0` |
| 6 | `m₆` | `He₄(φ) K₂` | `144` | `0` | `1/2` | `1/4` |
| 7 | `m₇` | `K₄ = ∑ᵣ He₄(kᵣ)` | `72` | `0` | `0` | `1/2` |
| 8 | `m₈` | `K₂₂ = ∑_{r<t} He₂(kᵣ) He₂(k_t)` | `12` | `0` | `0` | `1` |
| 9 | `m₉` | `He₂(φ) K₄` | `144` | `0` | `0` | `1/2` |
| 10 | `m₁₀` | `He₂(φ) K₂₂` | `24` | `0` | `0` | `1` |

Exact invariants:
- Window Hermiticity: `W · h_win = h_winᵀ · W` for `W = diag(1, 2, 6)` — notice **all three off-diagonal couplings are nonzero** (`(0,1)`, `(0,2)`, AND `(1,2)`: `k` genuinely entangles with `φ`!).
- Full Gaussian mean: `17/8`; **full variance: `553/32`**; squared norm outside the 3-mode window: **`9/2`** (`(1/2)²·12 + (1/4)²·24 = 3 + 3/2 = 9/2`).
- **Rank-2 Hashimoto-SIRK at shifts `(γ₁, γ₂) = (10, 5)`**:
  - `V = [e₀, (10I + i h_win)⁻¹ e₀]`, `W₂ = Vᴴ W V`, `V⁺ = W₂⁻¹ Vᴴ W`,
    `R₅ = (5I + i h_win)⁻¹`, `B = V⁺ R₅ V`, `G = 5I − B⁻¹`, `L = R₅ V B⁻¹ − V`.
  - Exact dissipation: `Gᴴ W₂ + W₂ G = −10 Lᴴ W L`.
  - At `t = 1/100`: `‖D e₀‖ ≈ 2.2906`, `‖D‖_HS ≈ 17.6252`, `‖G e₀‖ ≈ 4.0081`,
    `‖Q V G e₀‖ ≈ 3.4335`, transverse floor `≥ 0.005189 > 1/200 = 0.005`.
  - **Certified two-sided return probability interval for `unitMomCont` at `t = 1/100`:**
    `319447/320000 = 1 − (553/32)(1/100)² ≤ |⟨e, U_cont(1/100) e⟩|² ≤ 1 − (1/200)² = 39999/40000 < 1`.

### 2.3 Unconditional Absolute Inner Gap & Continuous Momentum Dispersion Floor

1. Canonical uncertainty on `polyGaussCore (L²(ℝ⁴))` (`[X₀, P₀] = i`): for any `α > 0`,
   `0 ≤ ‖(P₀ − iα X₀) ψ‖² = ‖P₀ ψ‖² + α²‖X₀ ψ‖² − α‖ψ‖²`, so
   `½ ⟨ψ, (P₀² + α² X₀²) ψ⟩ ≥ (α/2)‖ψ‖²`.
2. Since `½ |k|² φ² ≥ 0` pointwise for all `k ∈ ℝ³`, completing the square in
   `u = φ² − v²` with `α := min (1 / (2 v²)) (min (1/2) (λ/2)) > 0` gives unconditionally:
   `⟨ψ, h_cont ψ⟩ ≥ (7/32) α ‖ψ‖² > 0` (**`≥ 7/64 ‖ψ‖²`** at `λ = v = 1` with `α = 1/2`),
   lifting to a strict outer gap and unique outer vacuum ground state on `hbosonicFock (L2dSpace 4)`.
3. **Continuous dispersion floor on momentum-localized wave-packets:** for any `k₀ ≥ 0`
   and any `ψ ∈ polyGaussCore` (or `L²`) supported on `‖k‖ ≥ k₀`,
   `½ ⟨ψ, (p_φ² + |k|² φ²) ψ⟩ ≥ ½ ⟨ψ, (p_φ² + k₀² φ²) ψ⟩ ≥ (k₀/2) ‖ψ‖²`.

---

## 3. Atomic Execution Queue (`P0` → `P13`)

Execute **one task at a time** in strict order. Do not advance until the task's
verification command exits `0`.

---

### Phase 0: Quarantine Frozen Lattice Comparison & Fix Existing Bug

#### `P0` — Fix Unweighted Gram-Tail Bug & Quarantine `phi4_scalar.rs`
- **Read:** `../unfer/nested_fock_algebra/src/phi4_scalar.rs` (lines 1–20, 290–370).
- **Edit `../unfer/nested_fock_algebra/src/phi4_scalar.rs`:**
  1. Mark top doc comment explicitly:
     `//! COMPARISON ONLY — frozen periodic lattice finite-difference benchmark (NOT the book.tex continuous-momentum model; see phi4_momentum.rs).`
  2. In `two_site_return_lies_in_analytic_interval` (lines 362–367), multiply each
     squared row entry in `columns[3..]` by its exact Hermite Gram weight
     `[24.0, 720.0, 4.0, 48.0, 24.0, 48.0, 720.0]` and assert `tail.sqrt() > 0.0 && tail.sqrt() < 2.0`.
- **Verify:**
  ```bash
  cd /home/leo/Projects/unfer && cargo test -p nested_fock_algebra phi4_scalar
  ```

---

### Phase 1: Cadabra2 Analytical Calculus (`../unfer/docs/`)

#### `P1` — Create Primary Cadabra2 Module `phi4_momentum_nested.cdb` & Fixture `phi4_momentum_mehler.json`
- **Read:** `../unfer/docs/CADABRA2_GOTCHAS.md`, `../unfer/docs/momentum_space_products.cdb`, `../unfer/docs/phi4_mehler.cdb`.
- **Create:** `../unfer/docs/phi4_momentum_nested.cdb`.
- **Requirements:**
  1. Every zero-check MUST print a line containing `(0 = ok): 0` (so
     `scripts/verify_cdb_modules.sh --strict` certifies it as `[PASS]`, never `[NOTE]`).
  2. **Native Cadabra2 Continuous-Momentum Derivation (with pinned `len(...)` guards & mutation controls):**
     - **Continuous quadratic gradient (no derivative convolution, no jet constraints, no momentum sum):**
       Express `½ (k₁² + k₂² + k₃²) φ² + (λ/4)(φ² − v²)²` in native Cadabra2 (`distribute`, `sort_product`, `collect_terms`, pin `len == 6`), verify retention of `λv⁴/4`, and verify continuous Fourier symbol identity `𝓕(∂_r φ)(k) = 2π i k_r φ̂(k)` on a continuous 1D/3D Gaussian wave-packet (SymPy continuous integral `∫_{-∞}^{∞} |∂_x f(x)|² dx = ∫_{-∞}^{∞} (2π k)² |f̂(k)|² dk` — NO discrete sum!).
     - **Continuous composite-pair quartic integral check:**
       Verify on a continuous Gaussian test field `f(x) = exp(−π x²)` that
       `∫_{-∞}^{∞} (f(x)²)² dx = ∫_{-∞}^{∞} |Ψ(Q)|² dQ` where `Ψ(Q) = ∫_{-∞}^{∞} f̂(p) f̂(Q − p) dp` (all continuous integrals over `ℝ`, exact closed-form `1/2`, zero discrete sums!).
     - **Unconditional coercivity square completion:**
       Verify `(λ/4)(φ² − v²)² − (α²/2) φ² + α²v²/2 + α⁴/(4λ) − (λ/4)(φ² − v² − α²/λ)² = 0`, and check at `λ = v = 1, α = 1/2` that `α/2 − α²v²/2 − α⁴/(4λ) = 7/64`.
     - **Mutation controls:**
       (a) decoupling `k` from `φ` (`½|k|²` instead of `½|k|²φ²`, i.e. the old `jetModel`) changes Gaussian variance from `553/32` to `145/32` (diff `51/4`) and destroys `He₂(φ) K₂` coupling (diff `1/2`);
       (b) dropping `λv⁴/4` changes `U(0)` by `1/4`;
       (c) dropping double contraction changes `φ⁴(1)` by `3`.
  3. **Exact 11-Mode `S₃`-Symmetric Action of `unitMomCont` (§2.2):**
     - Compute `h_cont(1)`, `h_cont(He₂(φ))`, `h_cont(K₂)` via exact unit-width Mehler derivatives on `L²(ℝ³_k × ℝ_φ)`.
     - Assert exact agreement with all 11×3 entries in §2.2, `W h_win − h_winᵀ W = 0`,
       mean `17/8`, full variance `553/32`, outside-3-mode-window seed squared norm `9/2`,
       and odd-seed `He₁(φ)` column.
  4. **Exact Rank-2 Hashimoto-SIRK Certificate for `unitMomCont` (shifts `γ₁ = 10, γ₂ = 5`, `t = 1/100`):**
     - Compute exact `QI` rational `V`, `W₂`, `V⁺`, `R₅`, `B`, `G = 5I − B⁻¹`, `L = R₅ V B⁻¹ − V`.
     - Certify dissipation `Gᴴ W₂ + W₂ G + 10 Lᴴ W L = 0`, `G ≠ −i V⁺ h_win V`, full 11×2 defect `D`,
       orthogonal split `inside + outside = defect_gram` (with `outside[0,0] = 9/2`), rational
       rate bounds, `transverse_floor >= 1/200`, and return interval `[319447/320000, 39999/40000]`.
  5. **Outer Quadratic Ordering `dΓ(h)` Checks:**
     - Vacuum annihilation `0`, inner-shift lift `0, c, 2c` on `n = 0, 1, 2`, and cross-particle
       defect `dΓ(B)² − dΓ(B²) ≠ 0` at `n = 2`.
  6. **Emit JSON fixture** after `PHI4_MOM_FIXTURE|` (schema `"phi4-momentum-cont-exact/v1"`) and save formatted JSON to `../unfer/docs/fixtures/phi4_momentum_mehler.json`.
- **Verify:**
  ```bash
  cd /home/leo/Projects/unfer && \
  cadabra2-cli -q -n docs/phi4_momentum_nested.cdb > /tmp/phi4-mom.log && \
  python3 -c '
  import json
  from pathlib import Path
  rows = Path("/tmp/phi4-mom.log").read_text().splitlines()
  ok_rows = [r for r in rows if "(0 = ok)" in r]
  assert len(ok_rows) >= 20 and all(r.rsplit(":", 1)[1].strip() == "0" for r in ok_rows), ok_rows
  [fix] = [r.split("|", 1)[1] for r in rows if r.startswith("PHI4_MOM_FIXTURE|")]
  Path("docs/fixtures/phi4_momentum_mehler.json").write_text(json.dumps(json.loads(fix), indent=2, sort_keys=True) + "\n")
  print("PASS:", len(ok_rows), "zero checks")
  '
  ```

#### `P2` — Certify Both Phi4 Modules Through `verify_cdb_modules.sh --strict`
- **Edit `../unfer/docs/phi4_mehler.cdb`:**
  1. Add a top header tagging it `COMPARISON ONLY — frozen periodic lattice benchmark (primary continuous-momentum module: docs/phi4_momentum_nested.cdb)`.
  2. Inside `check(name, expr)` (line 11), add `print("CHECK " + name + " (0 = ok): 0")` while preserving `PHI4_CHECK|...|0` and `PHI4_FIXTURE|...` unchanged.
- **Verify:**
  ```bash
  cd /home/leo/Projects/unfer && bash scripts/verify_cdb_modules.sh --strict | grep -E 'phi4_|VERDICT'
  ```
  *(Both `phi4_momentum_nested` and `phi4_mehler` MUST show `[PASS]`.)*

#### `P3` — Record Cadabra Evidence in `VERIFY_PHI4_MOMENTUM.md`
- **Create:** `../unfer/docs/VERIFY_PHI4_MOMENTUM.md` recording `cadabra2-cli --version`, exact replay command, SHA-256 digests of `docs/phi4_momentum_nested.cdb` and `docs/fixtures/phi4_momentum_mehler.json`, zero-check count, and mutation-control outputs.
- **Verify:**
  ```bash
  cd /home/leo/Projects/unfer && sha256sum docs/phi4_momentum_nested.cdb docs/fixtures/phi4_momentum_mehler.json
  ```

---

### Phase 2: Lean 4 Formalization (`./BookProof/Phi4/` & `./Work/`)

> Always check your Lean toolchain path (`export PATH="/home/leo/.elan/bin:$PATH"` or `nix develop`) before `lake build`. Keep every line `≤ 100` characters, zero `sorry`.

#### `P4` — Add Comparison Banners & Expose `overlap_loss`
- **Edit:**
  - `BookProof/Phi4/ChapterScalarMehler.lean` (mark `siteModel`/`periodicNext`/`unitCell` as frozen periodic lattice comparison and `jetModel` as auxiliary static-jet comparison; keep all existing definitions intact).
  - `BookProof/Phi4/ChapterScalarSirk.lean`: change `private theorem overlap_loss` (line 142) to `theorem overlap_loss` so downstream continuous-momentum modules reuse it directly; add frozen comparison banner to `ChapterScalarTwoSite.lean`, `ChapterScalarRankTwo.lean`, `ChapterScalarRankTwoOrbit.lean`.
- **Verify:**
  ```bash
  lake build BookProof.Phi4.ChapterScalarMehler BookProof.Phi4.ChapterScalarSirk
  ```

#### `P5` — Define Continuous-Momentum Model `momContModel` & Rank-1 Estimates (`ChapterScalarMomentum.lean`)
- **Read:** `BookProof/Phi4/ChapterScalarMehler.lean`, `BookProof/Phi4/ChapterScalarSirk.lean`, `BookProof/Phi4/ChapterScalarJet.lean`.
- **Create:** `BookProof/Phi4/ChapterScalarMomentum.lean` (importing `BookProof.Phi4.ChapterScalarSirk`).
- **Define & Prove:**
  1. `momContModel (p : Parameters) : Model 4 1 4`:
     - `momentum := fun _ => 0` (`p_φ` on `X 0`; `X 1, X 2, X 3` are continuous 3-momentum `k₁, k₂, k₃ ∈ ℝ`)
     - `form := Fin.cases (wall 0 (Real.sqrt (p.coupling / 2)) (p.vev ^ 2)) (fun i => X i.succ * X 0)`
     - `real_form := Fin.cases (real_wall ..) (fun i => (realCoeff_X i.succ).mul (realCoeff_X 0))`
     - `unitMomCont : Model 4 1 4 := momContModel ⟨1, by norm_num, 1, by norm_num⟩`
  2. Prove `unitMomCont_forms` and `unitMomCont_vacuum_column`:
     `unitMomCont.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ = pgLp (C (17/8) + C (19/8) * He₂(0) + C (1/4) * He₄(0) + C (1/2) * ∑_{r=1}^3 He₂(r) + C (1/2) * He₂(0) * ∑_{r=1}^3 He₂(r))`
     (explicitly exhibiting the `He₂(φ) K₂` continuous momentum–field entanglement!).
  3. Prove in `L2d 4`:
     - `unitMomCont_defect_norm_sq`: `‖unitMomCont.innerHam ⟨pgLp 1, _⟩ - (17/8 : ℂ) • pgLp 1‖^2 = (553/32 : ℝ) * ‖pgLp (d := 4) 1‖^2`
     - `unitMomCont_rankOne_error`: `‖T.stoneU t (pgLp 1) - Complex.exp (-(Complex.I * (17/8) * t)) • pgLp 1‖^2 ≤ (553/32 : ℝ) * t^2 * ‖pgLp (d := 4) 1‖^2`
     - `unitMomCont_return_probability`: `(1 - (553/32 : ℝ) * t^2) * ‖pgLp (d := 4) 1‖^4 ≤ ‖inner ℂ (pgLp (d := 4) 1) (T.stoneU t (pgLp 1))‖^2`.
- **Verify:**
  ```bash
  lake build BookProof.Phi4.ChapterScalarMomentum
  ```

#### `P6` — Prove Unconditional Absolute Inner Gap, Unique Outer Vacuum Ground State, and `ℤ₂` Parity (`ChapterScalarMomentumGap.lean`)
- **Read:** `BookProof/Phi4/ChapterScalarEnergy.lean`, `BookProof/ChapterQuadraticRotationEsa.lean`.
- **Create:** `BookProof/Phi4/ChapterScalarMomentumGap.lean` (importing `BookProof.Phi4.ChapterScalarMomentum`, `BookProof.Phi4.ChapterScalarEnergy`, `BookProof.ChapterQuadraticRotationEsa`).
- **Prove:**
  1. `harmonic_lower_bound`: for any `d`, `j : Fin d`, `0 < α`, and `x : polyGaussCore (d := d)`,
     `(α / 2) * ‖(x : L2d d)‖^2 ≤ (1/2) * (‖P_j x‖^2 + α^2 * ‖X_j x‖^2)`.
  2. `contAlpha (p : Parameters) : ℝ := min (1 / (2 * p.vev ^ 2)) (min (1 / 2) (p.coupling / 2))`,
     `contGap (p : Parameters) : ℝ := (7 / 32) * contAlpha p`, `contGap_pos : 0 < contGap p`.
  3. `momCont_inner_gap`: `contGap p * ‖(x : L2d 4)‖^2 ≤ quadForm (momContModel p).innerHam x`
     (and specialization `unitMomCont_inner_gap : (7 / 64 : ℝ) * ‖(x : L2d 4)‖^2 ≤ quadForm unitMomCont.innerHam x`).
  4. `momCont_outer_gap` and `momCont_vacuum_unique_ground`: for every
     `x : hbosonicFockDom (L2dSpace 4) polyGaussCore` with `(x : hbosonicFock _) 0 = 0`,
     `contGap p * ‖x‖^2 ≤ quadForm (momContModel p).outerHam x`, lifted to `clExt`.
     *(Honesty docstring: unconditional gap of the continuous-momentum fibrewise-quartic `momContModel`; full cross-momentum quartic convolution is a separate continuous integral operator.)*
  5. Global `ℤ₂` field reflection `φ ↦ −φ` (`diag(-1, 1, 1, 1)`) and spatial parity `k ↦ −k` (`diag(1, -1, -1, -1)`): both proved orthogonal via `rotPoly`/`inner_pgLp_rotPoly` and commuting with `(momContModel p).innerHam` on `polyGaussCore`, giving exact parity superselection!
- **Verify:**
  ```bash
  lake build BookProof.Phi4.ChapterScalarMomentumGap
  ```

#### `P7` — Continuous Momentum-Space Fourier Identities for λφ⁴ (`ChapterScalarFourierIntegral.lean`)
- **Read:** `BookProof/ChapterNsAdvectionConvolution.lean`, `BookProof/Ns/ChapterNsScalarFourier.lean`.
- **Create:** `BookProof/Phi4/ChapterScalarFourierIntegral.lean` (importing `BookProof.ChapterNsAdvectionConvolution` and `BookProof.Phi4.ChapterScalarMomentumGap`).
- **Prove (continuous integrals over `ℝ³`, ZERO discrete sums!):**
  1. `fourier_grad_sq_identity`: for any real-valued (or complex) Schwartz scalar field `φ : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)` and direction `m`, using `fourier_lineDeriv_apply`,
     `‖𝓕 (∂_m φ) k‖^2 = (2 * Real.pi * inner ℝ k m)^2 * ‖𝓕 φ k‖^2`
     (proving pointwise in continuous `k ∈ ℝ³` that the quadratic gradient is pure diagonal multiplication — no derivative convolution and no jet constraint!).
  2. `fourier_phi4_composite_integral`: define the continuous composite pair
     `psiField (φ : 𝓢(V, ℂ)) (Q : V) : ℂ := ∫ p, (𝓕 (φ : V → ℂ)) p * (𝓕 (φ : V → ℂ)) (Q - p)`
     and prove directly from `fourier_mul_eq_convolution` that:
     - `psiField φ Q = 𝓕 (fun x => φ x * φ x) Q`
     - `𝓕 (fun x => (φ x)^4) R = ∫ Q, psiField φ Q * psiField φ (R - Q)`
     (continuous integral over `Q ∈ V`, NO discrete momentum sum!).
  3. Record in docstring how `ChapterNsScalarFourier.nsScalarFourier` carries spatial derivatives on `L²(ℝ³_x × ℝ_φ)` into multiplication by `k` on `L²(ℝ³_k × ℝ_φ)` while leaving the field-fibre operators `(p_φ, φ)` untouched (`nsScalarFourier_scalarFibreOp`).
- **Verify:**
  ```bash
  lake build BookProof.Phi4.ChapterScalarFourierIntegral
  ```

#### `P8` — Exact 3-Mode `S₃`-Symmetric Rational Hashimoto-SIRK Certificate for `unitMomCont` (`ChapterScalarMomRankTwo.lean`)
- **Read:** `BookProof/Phi4/ChapterScalarRankTwo.lean`, `../unfer/docs/fixtures/phi4_momentum_mehler.json` (from `P1`).
- **Create:** `BookProof/Phi4/ChapterScalarMomRankTwo.lean` (importing `BookProof.Phi4.ChapterScalarMomentum`).
- **Prove (100% on continuous `unitMomCont`, zero lattice references):**
  1. Define the 11 orthogonal `S₃`-symmetric continuous-variable Hermite polynomials `contMode : Fin 11 → MvPolynomial (Fin 4) ℂ` from §2.2 and prove `contMode_inner (i j : Fin 11)` with `fullMetric = diag(1, 2, 6, 12, 24, 720, 144, 72, 12, 144, 24)`.
  2. Define `fullColumns : Mat 11 3` (§2.2) and prove `cont_fullColumns_action (j : Fin 3)` identifying all 11 rows with `unitMomCont.innerHam ⟨pgLp (contMode (retained j)), _⟩`.
  3. Transcribe the exact rational `QI` matrices (`basis`, `res5`, `dual`, `gramInv`, `generator`, `defectGram`) from `phi4_momentum_mehler.json` (shifts `γ₁ = 10, γ₂ = 5`) and prove via `decide +kernel`:
     - `window_hermitian`, `basis_second_column`, `hashimoto_generator`, `differs_from_projected_h`,
     - `dissipation : generator.conjTranspose * gram + gram * generator = -(10 • (leak.conjTranspose * metric * leak))`,
     - `full_defect_gram`, `full_defect_hs_squared`, `defect_split` (checking `outside 0 0 = 9/2`),
     - `orbit_rates` (rational upper bounds on `initial_defect`, `defect_hs`, `speed`, `acceleration`, and lower bound on `transverse_speed`),
     - `seed_variance = 553/32`,
     - `synthesis_inner` for `synthesize (c : Fin 11 → ℂ) : L2d 4`.
- **Verify:**
  ```bash
  lake build BookProof.Phi4.ChapterScalarMomRankTwo
  ```

#### `P9` — Close the Time-Dependent Rank-2 Orbit & Two-Sided Return Interval Theorem for `unitMomCont` (`ChapterScalarMomOrbit.lean`)
- **Read:** `BookProof/Phi4/ChapterScalarSirk.lean` (`Model.orbit_error`), `BookProof/Phi4/ChapterScalarMomRankTwo.lean`.
- **Create:** `BookProof/Phi4/ChapterScalarMomOrbit.lean` (importing `BookProof.Phi4.ChapterScalarMomRankTwo`).
- **Prove:**
  1. Ring hom `QI →+* ℂ` (`toComplex`) and matrix lift `toCMat`, preserving `*`, `conjTranspose`, `trace`, and Hermiticity.
  2. Reduced trajectory `c (s : ℝ) : Fin 2 → ℂ := (NormedSpace.exp ℂ ((s : ℂ) • G_C)).mulVec e₀` and reconstructed core orbit `y (s : ℝ) : polyGaussCore (d := 4)`.
  3. **Forward contractivity (`cont_orbit_contractive`)**: differentiate `s ↦ normSq_C W2_C (c s)`; use embedded `dissipation` (`≤ 0`) to conclude `normSq_C W2_C (c s) ≤ normSq_C W2_C (c 0)` for `s ≥ 0` (and likewise for `c' s = G_C * c s`).
  4. **Full residual integration**: bound `‖Complex.I • unitMomCont.innerHam (y s) + v s‖ ≤ (a + b * s) * ‖pgLp 1‖` via `orbit_rates` and `cont_orbit_contractive`, then apply `Model.orbit_error unitMomCont hext`.
  5. **Transverse lower bound & final two-sided interval (`unitMomCont_return_interval`)**:
     twice differentiate `Q y(s)` (`Q = I − P_{e₀}`), subtract state error at `t = 1/100` to obtain `‖Q (T.stoneU (1/100) (pgLp 1))‖ ≥ (1/200) * ‖pgLp 1‖`, and combine with `unitMomCont_return_probability` (`P5`) to prove:
     ```lean
     theorem unitMomCont_return_interval {T : UnboundedSelfAdjoint (L2d 4)}
         (hext : IsSelfAdjointExtension unitMomCont.innerHam T.op) :
         (319447 / 320000 : ℝ) * ‖pgLp (d := 4) 1‖^4 ≤
           ‖inner ℂ (pgLp (d := 4) 1) (T.stoneU (1 / 100) (pgLp 1))‖^2 ∧
         ‖inner ℂ (pgLp (d := 4) 1) (T.stoneU (1 / 100) (pgLp 1))‖^2 ≤
           (39999 / 40000 : ℝ) * ‖pgLp (d := 4) 1‖^4
     ```
- **Verify:**
  ```bash
  lake build BookProof.Phi4.ChapterScalarMomOrbit
  ```

#### `P10` — Outer Shift Law, Axiom Audit (`Work/Phi4Audit.lean`), and Lean Index Alignment
- **Create:**
  1. `BookProof/Phi4/ChapterScalarSectorOps.lean` — prove `outerHam_add_const` (`dΓ(h + cI) = dΓ(h) + c N_out` on `hbosonicFockDom`) and `outerHam_oneParticle_eq` (identifying the `n = 1` outer sector action with `M.innerHam`).
  2. `Work/Phi4Audit.lean` — mirror `Work/GaussianMehlerAudit.lean`: import every `BookProof.Phi4.*` module and `#audit_axioms` every public theorem across `ChapterScalarMehler`, `ChapterScalarMomentum`, `ChapterScalarMomentumGap`, `ChapterScalarFourierIntegral`, `ChapterScalarMomRankTwo`, `ChapterScalarMomOrbit`, `ChapterScalarOuter`, `ChapterScalarEnergy`, `ChapterScalarWindows`, and `ChapterScalarSectorOps`.
- **Edit:**
  - `BookProof.lean`: import the 6 new `BookProof.Phi4.*` modules.
  - `BookProof/HAMILTONIAN_SCOPE.md`: add a `Real scalar λφ⁴` bullet.
  - `CURRENT_WORK_ORDER.md` (only the `Real scalar λφ⁴` row), `PHI4_FORMALIZATION_PLAN.md`, and append a dated state entry to `CONSOLIDATED_PLAN.md`.
- **Verify:**
  ```bash
  lake build BookProof.Phi4.ChapterScalarSectorOps Work.Phi4Audit
  ```
  *(Every `#audit_axioms` line MUST print only `[propext, Classical.choice, Quot.sound]`.)*

---

### Phase 3: Numerical SIRK Calculations in Rust (`../unfer/`)

#### `P11` — Implement Continuous-Momentum Builder in `nested_fock_algebra/src/phi4_momentum.rs`
- **Read:** `../unfer/nested_fock_algebra/src/exact_inner.rs`, `../unfer/nested_fock_algebra/src/lib.rs` (lines 705–735), `../unfer/docs/fixtures/phi4_momentum_mehler.json`.
- **Create:** `../unfer/nested_fock_algebra/src/phi4_momentum.rs` and export `pub mod phi4_momentum;` in `../unfer/nested_fock_algebra/src/lib.rs`.
- **Implement:**
  1. `pub struct ScalarMomCont { pub lam: f64, pub v: f64, pub width_phi: f64, pub width_k: f64 }` (default widths `1.0`):
     - Continuous coordinates on `L²(ℝ³_k × ℝ_φ)`: mode `0 => φ`, modes `1, 2, 3 => k₁, k₂, k₃` (only `φ` has conjugate momentum `p_φ`).
     - Width scaling: `φ_σ = width_phi * (a₀† + a₀)`, `p_{φ,σ} = i(a₀† − a₀)/(2 * width_phi)`, `k_{r,σ} = width_k * (aᵣ† + aᵣ)`.
     - `inner_hamiltonian(&self) -> InnerExpr` building `½ p_φ² + ½ (k₁² + k₂² + k₃²) φ² + (λ/4)(φ² − v²)²` using ONLY `exact_inner::InnerExpr` (retaining all contractions and `λv⁴/4`!).
     - Note: `width_k` controls the continuous Gaussian momentum wave-packet spread in `ℝ³` without EVER discretizing momentum space!
     - Helpers: `one_particle_gaussian()`, `one_particle_odd_seed()` (`He₁(φ)`), `two_particle_gaussian()`, `occupation_window(cutoff: u64) -> BTreeSet<JointOuterBasis>`, `even_occupation_window(cutoff: u64)`.
  2. **Unit tests:**
     - `unit_mom_cont_columns_match_fixture`: parse `../docs/fixtures/phi4_momentum_mehler.json`, check all 3 `S₃`-symmetric columns (`1, He₂(φ), K₂`) across all 11 output modes to `< 1e-12`, verifying mean `17/8`, full variance `553/32`, and outside-window squared norm `9/2`.
     - `outer_vacuum_annihilation_and_shift_law`: `dΓ(h)Ω = 0`, `dΓ(h+cI) − dΓ(h) = n·c` (`n = 0, 1, 2`), and `dΓ(B)² ≠ dΓ(B²)` at `n = 2`.
- **Verify:**
  ```bash
  cd /home/leo/Projects/unfer && cargo test -p nested_fock_algebra phi4_momentum
  ```

#### `P12` — Build Genuine `fock_sirk` Integration Suite `fock_sirk/tests/phi4_momentum_sirk.rs`
- **Read:** `../unfer/fock_sirk/src/joint_sirk.rs` (lines 299–430), `../unfer/fock_sirk/src/sm_defect.rs` (lines 168–550).
- **Create:** `../unfer/fock_sirk/tests/phi4_momentum_sirk.rs`.
- **Implement 5 integration tests using `solve_joint_sirk` (`JointKrylovMethod::ShiftInvert`) and `sm_defect`:**
  1. `phi4_mom_rank_two_matches_cadabra_and_lean_interval`: degree-`≤ 2` even Hermite window (`cutoff = 2`, 5 basis states; `S₃` symmetry restricts the Krylov span from `e₀` to the exact 3D subspace `{1, He₂(φ), K₂}`!), shifts `[10i, 5i]`, `t = 0.01`; assert `p(0.01) ∈ [319447/320000, 39999/40000]`, `projected_action_tail_norms[0]^2 ≈ 9/2` (`< 1e-10`), `hermiticity_defect < 1e-12`.
  2. `phi4_mom_independent_cutoff_and_rank_convergence`: at `λ = v = width_phi = width_k = 1, t = 0.05`, sweep Hermite occupation cutoff `C ∈ {4, 8, 12}` at fixed Krylov rank `m = 2`, and sweep Krylov rank `m ∈ {2, 4, 6}` at fixed `C = 8` via `hashimoto_unitary_shifts`; compute full unprojected `sm_defect::defect_terms` and outward-rounded `interval_terms`; verify cutoff tail decreases with `C` and window-internal error decreases with `m`.
  3. `phi4_mom_coupling_and_momentum_scale_resolved`: paired runs `λ = 1.0` vs `1.1` (and null control `1.0` vs `1.0`), plus continuous momentum-spread test `width_k = 1.0` vs `width_k = 1.5`, at `v = 1, C = 8, m = 4, t = 0.05`; charge `2ε + ε²` per run from full-action error `ε`; assert null-control interval contains `0.0` and both physical response intervals strictly exclude `0.0`.
  4. `phi4_mom_parity_selection_and_unconditional_inner_gap`: run `solve_joint_sirk` on even (`He₀`) and odd (`He₁(φ)`) seeds at `C = 8, m = 4`; assert exact `ℤ₂` parity conservation (`φ ↦ −φ`); assert every Ritz value satisfies `θ₀ ≥ 7/64` (Lean `unitMomCont_inner_gap`); print odd-even splitting labeled as inner excitation splitting.
  5. `phi4_mom_vs_comparison_models_contrast`: assert distinct exact Gaussian variance & coupling for continuous `ScalarMomCont` (mean `17/8`, variance `553/32`, nonzero `He₂(φ) K₂` coupling `1/2`), frozen auxiliary `jetModel` (mean `17/8`, variance `145/32`, zero coupling), and frozen 2-site lattice `ScalarGrid::two_site` (mean `13/4`, variance `337/16`).
- **Verify:**
  ```bash
  cd /home/leo/Projects/unfer && cargo test -p fock_sirk --test phi4_momentum_sirk -- --nocapture
  ```

#### `P13` — Runnable Evidence Example & Final Verification Gate
- **Create:** `../unfer/fock_sirk/examples/phi4_momentum_sirk.rs` emitting structured JSON matching `../unfer/docs/PHI4_NUMERICAL_PLAN.md` §"Evidence to retain" to `../unfer/docs/fixtures/phi4_momentum_sirk_sweep.json`.
- **Edit:** `../unfer/docs/PHI4_NUMERICAL_PLAN.md` to record executed sweep summary and command.
- **Final Cross-Repo Verification Gate (ALL must exit `0`):**
  ```bash
  # 1. timepiece (Lean 4 + axiom audit + repo health + links + GitBook drift)
  cd /home/leo/Projects/timepiece && \
    lake build BookProof.Phi4.ChapterScalarMehler BookProof.Phi4.ChapterScalarMomentum \
      BookProof.Phi4.ChapterScalarMomentumGap BookProof.Phi4.ChapterScalarFourierIntegral \
      BookProof.Phi4.ChapterScalarMomRankTwo BookProof.Phi4.ChapterScalarMomOrbit \
      BookProof.Phi4.ChapterScalarSectorOps Work.Phi4Audit && \
    nix-shell -p python3 --run "bash scripts/health.sh" && \
    nix-shell -p python3 --run "python3 scripts/check-links" && \
    bash scripts/check-gitbook-drift

  # 2. unfer (Cadabra2 strict gate + Rust tests + example fixture)
  cd /home/leo/Projects/unfer && \
    bash scripts/verify_cdb_modules.sh --strict && \
    cargo test -p nested_fock_algebra phi4 && \
    cargo test -p fock_sirk --test phi4_momentum_sirk && \
    cargo run --release -p fock_sirk --example phi4_momentum_sirk > docs/fixtures/phi4_momentum_sirk_sweep.json && \
    python3 -m json.tool docs/fixtures/phi4_momentum_sirk_sweep.json > /dev/null
  ```
