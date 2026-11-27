# Real scalar λφ⁴ in the nested Fock formalism

**Active work order (2026-11-27):** `Q1`–`Q8` below supersede `P0`–`P13` (completed baseline summarized in §4).
Every task MUST strictly adhere to the continuous-momentum SIRK / Mehler / nested-Fock formalism of [`book.tex`](book.tex) and [`../papers/Hashimoto.md`](../papers/Hashimoto.md): **only the Krylov space in the SIRK approximations is discrete, never space and never momentum space** ($\int_{\mathbb{R}^3} d^3k$). Lattice (`siteModel`, `twoSite`, `ScalarGrid`), static-jet (`jetModel`), and legacy Higgs (`sm_higgs_mechanism_sirk.rs`) artifacts are frozen comparisons only.

## Baseline & 2026-11-27 Audit Summary

`P0`–`P13` landed the continuous-momentum fibre benchmark `h_cont(k, φ) = ½ p_φ² + ½ |k|² φ² + (λ/4)(φ² − v²)²` on `L²(ℝ³_k × ℝ_φ)` across Lean 4, Cadabra2, and Rust:

- **Lean 4 ([`BookProof/Phi4/`](BookProof/Phi4/), [`Work/Phi4Audit.lean`](Work/Phi4Audit.lean)):**
  - [`ChapterScalarMomentum.lean`](BookProof/Phi4/ChapterScalarMomentum.lean): `momContModel`, `unitMomCont_forms`, `unitMomCont_vacuum_column` (mean `17/8`, variance `553/32`, coupling `He₂(φ)K₂` = `1/2`), `unitMomCont_defect_norm_sq`, `unitMomCont_rankOne_error`, `unitMomCont_return_probability`.
  - [`ChapterScalarMomentumGap.lean`](BookProof/Phi4/ChapterScalarMomentumGap.lean): `harmonic_lower_bound`, `contGap_pos`, `unitMomCont_inner_gap` & `unitMomCont_closure_floor` (`7/64` at `λ = v = 1`), `fieldParity_inner` / `spatialParity_inner`, `shifted_well_comparison_false`.
  - [`ChapterScalarFourierIntegral.lean`](BookProof/Phi4/ChapterScalarFourierIntegral.lean): `fourier_grad_sq_identity`, `psiField_eq_fourier_mul`, `fourier_phi4_composite_integral`, `localizedWall_fourier`, `localizedWall_energy`.
  - [`ChapterScalarMomRankTwo.lean`](BookProof/Phi4/ChapterScalarMomRankTwo.lean) & [`ChapterScalarMomOrbit.lean`](BookProof/Phi4/ChapterScalarMomOrbit.lean): 11-mode `S₃` action table, exact rank-2 Hashimoto–SIRK at shifts `(10, 5)` with outside seed tail `9/2`, and `unitMomCont_return_interval` `[319447/320000, 39999/40000]` at `t = 1/100`.
  - [`ChapterScalarSectorOps.lean`](BookProof/Phi4/ChapterScalarSectorOps.lean): `outerHam_add_const` (`dΓ(h + cI) = dΓ(h) + c N_out`) and `outerHam_oneParticle_eq`.
- **Cadabra2 ([`../unfer/docs/phi4_momentum_nested.cdb`](../unfer/docs/phi4_momentum_nested.cdb)):**
  32 `(0 = ok): 0` checks passing `verify_cdb_modules.sh --strict`, producing [`../unfer/docs/fixtures/phi4_momentum_mehler.json`](../unfer/docs/fixtures/phi4_momentum_mehler.json) and the continuous classical integral check [`../unfer/docs/fixtures/phi4_localized_wall.json`](../unfer/docs/fixtures/phi4_localized_wall.json) (mixed `a²b²` coefficient `0.458627352548` vs `0.152875784183` without mixed pair; peak `2^{-3/2}`), recorded in [`../unfer/docs/VERIFY_PHI4_MOMENTUM.md`](../unfer/docs/VERIFY_PHI4_MOMENTUM.md).
- **Rust ([`../unfer/nested_fock_algebra/src/phi4_momentum.rs`](../unfer/nested_fock_algebra/src/phi4_momentum.rs), [`../unfer/fock_sirk/tests/phi4_momentum_sirk.rs`](../unfer/fock_sirk/tests/phi4_momentum_sirk.rs)):**
  `ScalarMomCont`, diagonal-phase change-of-basis null (`phase_rotated_quadratures`), classical `localized_packet_wall`, 10 passing integration tests, and [`../unfer/docs/fixtures/phi4_momentum_sirk_sweep.json`](../unfer/docs/fixtures/phi4_momentum_sirk_sweep.json) (`C = 4..44`).

### Concrete Defects Found in the 2026-11-27 Audit (Fixed by `Q1`–`Q8`)

| ID | File / Location | Defect Found | Fixed By |
|---|---|---|---|
| **A1** | [`ChapterScalarMomentumGap.lean`](BookProof/Phi4/ChapterScalarMomentumGap.lean) | Proves only unit `unitMomCont_inner_gap` (`7/64`); leaves general `(λ, v)` `momCont_inner_gap`, `momCont_closure_floor`, bosonic sectorwise lift `momCont_outer_gap`, `momCont_vacuum_unique_ground`, continuous momentum-support dispersion floor, and parity commutation (`fieldParity_comm_innerHam`, `spatialParity_comm_innerHam`) unproved. | `Q1`, `Q2`, `Q5` |
| **A2** | `BookProof/Phi4/ChapterScalarPacketForm.lean` (untracked draft) | Both **discretizes momentum space into two modes** (violating continuous momentum space) and contains four math/terminology defects (`packetKinetic` = gradient stiffness `½ Σ_m ∫ ∂_m χᵢ ∂_m χⱼ` instead of kinetic energy; `packetDualKinetic := G⁻¹ K`; `packetMixed` missing binomial factor `6` and localization weight `|χ|²`; unconjugated `L²` pairing). Retire it cleanly and extend continuous `ChapterScalarFourierIntegral.lean` instead. | `Q3` |
| **A3** | Prior plan citations to `cftproof.md` | Referenced Euclidean OS / Wilson hierarchy / six-flavour QCD calibration paths outside `book.tex`. Removed from the primary scalar track. | Plans updated |
| **A4** | [`../unfer/fock_sirk/src/sm_defect.rs`](../unfer/fock_sirk/src/sm_defect.rs) (`amplitude_terms`) & `phi4_momentum_sirk.rs` | **Conjugation bug:** `inner(&w, &r)` uses forward `w(t-s)` instead of `e^{+i(t-s)H}ψ = conj(w(t-s))` on real symmetric `(H, ψ)`. Also uses heuristic sampled trapezoid quadrature with no quadrature remainder, GMRES solve error, or `Interval` rounding, yet labels the result `"certified"`; `λ` response (`1.613e-3`) is still crossed by its charge (`1.786e-3`). | `Q6`, `Q7` |
| **A5** | [`../unfer/fock_sirk/examples/phi4_momentum_sirk.rs`](../unfer/fock_sirk/examples/phi4_momentum_sirk.rs) | Swept `C` to `44` (`151 min`, `4.24 GB` RSS) where rank-4 inside-window error plateaued flat at `2.88e-3` from `C = 8` to `44` (Krylov-rank-limited, not cutoff-limited), while skipping higher rank `m` and Hashimoto–Nodera shift tuning (`../papers/Hashimoto.md` Theorem 4.1). | `Q7`, `Q8` |

---

## 1. Hard Framework Contract & Anti-Mixing Guardrails

Read this table before touching any file. **NEVER violate any row below:**

| Topic | **DO (Exact `book.tex` Continuous-Momentum Framework)** | **DO NOT (Forbidden Mixing)** |
|---|---|---|
| **Continuous momentum arena** | Work on continuous `L²(ℝ³_k × ℝ_φ)` with coordinates `(φ, k₁, k₂, k₃)` (`0 ↦ φ`, `1..3 ↦ k₁..k₃`), Mehler measure `e^{−(‖k‖²+φ²)/2}`, and continuous-variable product Hermites. Momentum integrals are `∫_{ℝ³} d³k`; **only the Krylov space in the SIRK approximations is discrete, not the momentum space**. Any finite Hermite truncation `C` in numerical resolvents is strictly a solver-internal basis truncation converging strongly as `C → ∞` (`Model.window_solve_convergence`). | **NEVER** discretize momentum space into finite mode spans (`q₀ e₀ + q₁ e₁`) or sums `∑_m` / `∑_Q` over a box. **NEVER** use a spatial lattice (`siteModel`, `ScalarGrid`) as the primary model. **NEVER** introduce spatial-derivative jet constraints for `λφ⁴`. |
| **Gradient & quartic potential** | In `h_cont`, the continuous quadratic gradient is `½ |k|² φ²` and the wall is `(λ/4)(φ² − v²)²` (**retaining `λv⁴/4`**). For the continuous cross-momentum localized wall on `𝓢(ℝ³)`, compute continuous Plancherel/convolution integrals `∫_{ℝ³} d³Q |B_χ(Q)|² = ∫_{ℝ³} d³x |χ(x)|² (φ(x)² − v²)²` with exact factor `6` (`3λ/2`) in `(a f₀ + b f₁)⁴` and background `(λv⁴/4) ∫ |χ|²`. | **NEVER** decouple `k` from `φ` (`jetModel`), **NEVER** drop `λv⁴/4` or normal-order away contractions, **NEVER** Taylor-expand around `±v`, and **NEVER** turn classical test integrals into a discrete 2-mode momentum Hamiltonian. |
| **Outer enclosure (Quadratic Ordering)** | Assemble the complete inner operator `h` first, then apply a **single** outer lift `H = dΓ(h) = ∫ d³k dφ a†(k,φ) h(k,φ) a(k,φ) = ∑ᵢⱼ ⟨eᵢ, h eⱼ⟩ C†(eᵢ) A(eⱼ)` (`book.tex` lines 4030–4059), where `{eᵢ}` is a countable orthonormal basis of continuous functions on `ℝ³_k × ℝ_φ` (NOT discrete momentum points). | **NEVER** replace `dΓ(B²)` by `dΓ(B)²`. **NEVER** add number-changing outer terms. **NEVER** pull Euclidean OS / lattice Wilson hierarchy into this track. |
| **CCR convention** | `Q = b† + b`, `P = i(b† − b)/2 = −i∂`, so `[Q, P] = +i`. Only `φ` (`0`) carries conjugate momentum `p_φ`; `(k₁, k₂, k₃) ∈ ℝ³` are continuous momentum multipliers. | **NEVER** decouple `φ` and `p_φ` into independent modes. |
| **Mass gap terminology** | Distinguish: (1) `H Ω = 0` (outer vacuum annihilation); (2) absolute inner lower bound `⟨ψ, hψ⟩ ≥ μ‖ψ‖²` (`μ > 0`) lifting to `nμ` on the `n`-particle outer sector and unique outer vacuum ground state; (3) odd–even inner excitation splitting. | **NEVER** call `E₁ − E₀` an outer vacuum gap. **NEVER** claim `h_cont`'s fibre gap settles cross-momentum QFT or 4D triviality. |
| **Hashimoto–SIRK numerics** | Use `JointKrylovMethod::ShiftInvert`, physical shifts `γ_j = (N − j d)/t` (`Hashimoto.md` §4), `B = V†(γI + iPHP)⁻¹V`, `G = γI − B⁻¹`, and unprojected defect `D = iVG − HV`. Conjugate `w(t-s)` for `e^{+i(t-s)H}ψ` on real symmetric `(H, ψ)` and use outward `Interval` bounds before calling any interval "certified". | **NEVER** call sampled floating-point trapezoid estimates `"certified"`. **NEVER** run `C > 24` sweeps at fixed rank `m ≤ 4` when inside-window error is Krylov-rank-limited. |
| **Cadabra2 rules** | Stems `≥ 4` chars before `_` inside `@(...)`; no trailing `#` on `:=`; print `(0 = ok): 0` and pin `len(...)` guards so `scripts/verify_cdb_modules.sh --strict` reports `[PASS]`. | **NEVER** link Cadabra2 into Rust or accept `[NOTE]` as pass. |
| **Lean 4 hygiene** | Lines `≤ 100` chars, no trailing whitespace, zero `sorry`, and `Work/Phi4Audit.lean` reports only `[propext, Classical.choice, Quot.sound]`. | **NEVER** invent axioms, `sorry`, or lines `> 100` chars. |

---

## 2. Exact Mathematical Reference

### 2.1 Continuous-Momentum Inner Model `momContModel` & Continuous Convolution Integrals

- **Inner Hamiltonian on continuous `L²(ℝ³_k × ℝ_φ)`:**
  $$h_{\mathrm{cont}}(\vec{k}, \phi) = \frac{1}{2} p_\phi^2 + \frac{1}{2}(k_1^2 + k_2^2 + k_3^2)\phi^2 + \frac{\lambda}{4}(\phi^2 - v^2)^2,$$
  with general lower-bound candidate `contAlpha p := min (1/(2 v²)) (min (1/2) (λ/2))`, `contGap p := (7/32) * contAlpha p` (`7/64` at `λ = v = 1`).
- **Continuous momentum-support dispersion floor:** on any $\psi$ in the quadratic-form domain supported on $|\vec{k}| \ge k_0$, $\frac{1}{2}\langle \psi, (p_\phi^2 + |\vec{k}|^2\phi^2)\psi\rangle \ge \frac{k_0}{2}\|\psi\|^2$ directly from continuous multiplication by $|\vec{k}|^2 \ge k_0^2$ and `harmonic_lower_bound`.
- **Continuous composite-pair quartic integral on $\mathcal{S}(\mathbb{R}^3)$:**
  With $\Psi_\phi(Q) = \int_{\mathbb{R}^3} \hat{\phi}(p)\,\hat{\phi}(Q - p)\,d^3p$ (`psiField φ Q`) and $B_\chi(\phi)(Q) = (\hat{\chi} * \Psi_\phi)(Q) - v^2 \hat{\chi}(Q)$ (`localizedWall_fourier`), Plancherel (`localizedWall_energy`) gives
  $$\frac{\lambda}{4}\int_{\mathbb{R}^3} |B_\chi(\phi)(Q)|^2\,d^3Q = \frac{\lambda}{4}\int_{\mathbb{R}^3} |\chi(x)|^2 \big(\phi(x)^2 - v^2\big)^2\,d^3x \ge 0.$$
  For continuous Schwartz functions $f = a f_0 + b f_1$ (purely a continuous integral identity, NOT a 2-mode momentum discretization), polarization over $(a, \pm b)$ isolates the continuous cross-momentum $a^2 b^2$ overlap $\frac{3\lambda}{2}\int_{\mathbb{R}^3} |\chi(x)|^2 f_0(x)^2 f_1(x)^2\,d^3x$ plus the quadratic $(f_0 f_1)^2$ / constant background terms.

---

## 3. Active Atomic Work Order (`Q1`–`Q8`) for the Cheap LLM

Execute in strict numerical order `Q1 → Q8`. Every task keeps momentum space **100% continuous** ($\int_{\mathbb{R}^3} d^3k$): only the SIRK Krylov space is discrete.

### `Q1` — Close General-Parameter `momCont_inner_gap`, `momCont_closure_floor`, and Parity Commutation (`ChapterScalarMomentumGap.lean`)
- **Read:** `BookProof/Phi4/ChapterScalarMomentumGap.lean` (lines 130–498), `BookProof/Phi4/ChapterScalarMomentum.lean` (lines 27–90).
- **Edit:** `BookProof/Phi4/ChapterScalarMomentumGap.lean` (keep lines ≤ 100 chars, zero `sorry`).
- **Prove:**
  1. `wall_completion (p : Parameters) (q : MvPolynomial (Fin 4) ℂ)`: generalize `unit_wall_completion` for any `α` with `0 < α` (`α = contAlpha p`), showing the exact polynomial square-completion identity matching `phi4_momentum_nested.cdb`'s `coercivity-square-completion`.
  2. `momCont_inner_gap (p : Parameters) (ψ : polyGaussCore (d := 4))`: prove `contGap p * ‖(ψ : L2d 4)‖ ^ 2 ≤ (inner ℂ (ψ : L2d 4) ((momContModel p).innerHam ψ)).re` using `harmonic_lower_bound (d := 4) 0 hα_pos ψ`, positivity of the 3 continuous momentum–field terms `kᵣ φ`, and nonnegativity of the completed quartic square.
  3. `momCont_closure_floor (p : Parameters) (x : clDom (momContModel p).innerHam)`: lift `momCont_inner_gap` to `FarisLavine.quadForm (clExt ...)` via `floor_on_closure`.
  4. `fieldParity_comm_innerHam (p : Parameters)` and `spatialParity_comm_innerHam (p : Parameters)`: prove `rotPoly` with `fieldReflMatrix` / `spatialReflMatrix` commutes with `(momContModel p).innerHam` on `polyGaussCore (d := 4)`.
- **Verify:**
  ```bash
  export PATH="/home/leo/.elan/bin:$PATH"
  lake build BookProof.Phi4.ChapterScalarMomentumGap
  ```

### `Q2` — Close Bosonic Outer Sectorwise Gap Lift & Outer Vacuum Uniqueness (`ChapterScalarMomentumGap.lean` + `Work/Phi4Audit.lean`)
- **Read:** `BookProof/Phi4/ChapterScalarEnergy.lean`, `BookProof/Phi4/ChapterScalarOuter.lean`, `BookProof/Phi4/ChapterScalarSectorOps.lean`.
- **Edit:** `BookProof/Phi4/ChapterScalarMomentumGap.lean`, `Work/Phi4Audit.lean`.
- **Prove:**
  1. Generic sectorwise lower bound for any `M : Model d k r`: using `Model.sector_pair` (`ChapterScalarEnergy.lean`) show that if `∀ u : polyGaussCore, m * ‖(u : L2d d)‖^2 ≤ quadForm M.innerHam u` with `0 ≤ m`, then on every outer sector `n : ℕ` and vector `x : redDom (cbosonicProj (L2dSpace d) n) (fockSectorDom (L2dSpace d) polyGaussCore n)`, `(n : ℝ) * m * ‖(x : fockSector (L2dSpace d) n)‖^2 ≤ quadForm (cbosonicSectorOp (L2dSpace d) polyGaussCore M.innerHam n) x`.
  2. `outer_gap_of_inner_gap`: sum over `n ≥ 1` on `hbosonicFockDom` when `(x : hbosonicFock (L2dSpace d)) 0 = 0` to obtain `m * ‖(x : hbosonicFock _)‖^2 ≤ quadForm M.outerHam x`, and lift to `clDom M.outerHam` via `floor_on_closure`.
  3. Instantiate `momCont_outer_gap (p : Parameters)` and `momCont_outer_closure_gap (p : Parameters)` with floor `contGap p > 0`, and prove `momCont_vacuum_unique_ground`: any `ψ : clDom (momContModel p).outerHam` satisfying `quadForm (clExt ...) ψ = 0` (or `clExt ... ψ = 0`) vanishes in all `n ≥ 1` sectors, hence lies in the span of `Model.vacuum 4`.
  4. Register all new theorems from `Q1` and `Q2` in `Work/Phi4Audit.lean`.
- **Verify:**
  ```bash
  export PATH="/home/leo/.elan/bin:$PATH"
  lake build BookProof.Phi4.ChapterScalarMomentumGap Work.Phi4Audit
  ```
  *(Audit must print only `[propext, Classical.choice, Quot.sound]`.)*

### `Q3` — Retire Finite-Mode Draft `ChapterScalarPacketForm.lean` & Extend Continuous `ChapterScalarFourierIntegral.lean`
- **Read:** `BookProof/Phi4/ChapterScalarFourierIntegral.lean`, `BookProof.lean`, `Work/Phi4Audit.lean`.
- **Remove / Edit:**
  1. Remove untracked `BookProof/Phi4/ChapterScalarPacketForm.lean` and remove its import/audit lines from `BookProof.lean` and `Work/Phi4Audit.lean` (it discretized momentum space into two modes and introduced 4 math/terminology errors).
  2. Extend `BookProof/Phi4/ChapterScalarFourierIntegral.lean` **purely on continuous `V`** (`[FiniteDimensional ℝ V]` / `EuclideanSpace ℝ (Fin 3)`):
     - Prove the continuous gradient Plancherel identity `fourier_grad_energy_eq`: for any orthonormal basis `b` of `V` and `φ : 𝓢(V, ℂ)`, `½ ∑ m, ∫ x, ‖(∂_{b m} φ : 𝓢(V, ℂ)) x‖² = ½ ∫ k, (2 * Real.pi * ‖k‖)² * ‖(𝓕 (φ : V → ℂ)) k‖²` (showing on continuous `V` that gradient stiffness is a continuous `‖k‖²` multiplier — NO `G⁻¹ K`, NO finite-mode matrix!).
     - Prove `localizedWall_nonneg` (`0 ≤ (λ / 4) * ∫ k, ‖localizedWall_fourier χ φ v k‖²`) and `localizedWall_polarization`: for real `a b : ℝ` and real-valued Schwartz test fields `f₀ f₁ : 𝓢(V, ℝ)` embedded in `ℂ`, polarizing the continuous integral `(λ / 4) * ∫ x, ‖χ x * (((a • f₀ + b • f₁) x)^2 - v^2)‖^2` extracts `(3 * λ / 2) * a^2 * b^2 * ∫ x, ‖χ x‖^2 * (f₀ x)^2 * (f₁ x)^2` plus the diagonal/constant cross terms (`0` momentum discretization).
     - Add `#audit_axioms` entries in `Work/Phi4Audit.lean` for the new continuous Fourier theorems.
- **Verify:**
  ```bash
  export PATH="/home/leo/.elan/bin:$PATH"
  lake build BookProof.Phi4.ChapterScalarFourierIntegral Work.Phi4Audit
  ```

### `Q4` — Continuous Mehler–Hermite Momentum-Convolution Integrals in Cadabra2 (`../unfer/docs/`)
- **Read:** `../unfer/docs/phi4_momentum_nested.cdb` (lines 65–135), `../unfer/docs/PHI4_ANALYTIC_PLAN.md`.
- **Edit:** `../unfer/docs/phi4_momentum_nested.cdb`, `../unfer/docs/VERIFY_PHI4_MOMENTUM.md`.
- **Create:** `../unfer/docs/fixtures/phi4_momentum_convolution.json`.
- **Implement inside `phi4_momentum_nested.cdb` (keeping all existing 32 `(0 = ok): 0` checks passing!):**
  1. Using continuous integration `∫_{-∞}^{∞} dp` and `∫_{-∞}^{∞} dQ` over continuous 1D and 3D momentum variables `p, Q ∈ ℝ³` (**zero discrete momentum sums and zero finite-mode projection**), compute the closed-form continuous pair convolution
     `Ψ_{m,n}(Q) = ∫_{ℝ³} (∏_{r=1}^3 He_{m_r}(p_r) e^{-p_r^2/4}) (∏_{r=1}^3 He_{n_r}(Q_r - p_r) e^{-(Q_r-p_r)^2/4}) d³p`
     between continuous Mehler–Hermite wavefunctions (e.g. `(0,0,0) * (0,0,0)`, `(2,0,0) * (0,0,0)`, `(2,0,0) * (0,2,0)`, and cross-coordinate `k₁, k₂`), and verify Plancherel equality `∫_{ℝ³} |Ψ_{m,n}(Q)|² d³Q = ∫_{ℝ³} |f_m(x) f_n(x)|² d³x` via exact SymPy continuous integration.
  2. Print `(0 = ok): 0` checks for each exact continuous Plancherel & convolution-kernel identity plus a `distinguish` mutation control deleting the cross-coordinate factor.
  3. Keep `localized_fixture` (`phi4_localized_wall.json`) explicitly tagged as a continuous classical integral verification of `localizedWall_energy` (`schema: "phi4-localized-classical-wall/v1"`).
  4. Emit `PHI4_MOM_CONV_FIXTURE|` JSON (`schema: "phi4-momentum-convolution/v1"`) to `../unfer/docs/fixtures/phi4_momentum_convolution.json` and update `VERIFY_PHI4_MOMENTUM.md`.
- **Verify:**
  ```bash
  cd /home/leo/Projects/unfer && bash scripts/verify_cdb_modules.sh --strict | grep -E 'phi4_|VERDICT'
  ```

### `Q5` — Continuous Momentum-Support Dispersion Floor & Composite-Pair Positivity in Lean 4 (`ChapterScalarMomentumGap.lean` / `ChapterScalarFourierIntegral.lean`)
- **Read:** `BookProof/Phi4/ChapterScalarMomentumGap.lean`, `BookProof/Phi4/ChapterScalarFourierIntegral.lean`.
- **Edit:** `BookProof/Phi4/ChapterScalarMomentumGap.lean` (or `ChapterScalarFourierIntegral.lean`), `Work/Phi4Audit.lean`.
- **Prove (purely on continuous `L²(ℝ³_k × ℝ_φ)` / `𝓢(V, ℂ)`, zero discrete momentum modes):**
  1. `momCont_dispersion_floor`: formalizing the continuous `|k| ≥ k₀` dispersion statement on continuous `L²(ℝ³_k × ℝ_φ)` — whenever `ψ : polyGaussCore (d := 4)` satisfies `(1 / 2) * (k₀ ^ 2) * ‖coreX 0 ψ‖ ^ 2 ≤ (1 / 2) * ∑ r : Fin 3, ‖coreRepPoly 4 ... (X r.succ * X 0) ψ‖ ^ 2` (i.e. continuous gradient energy on the support hypothesis `‖k‖ ≥ k₀ ≥ 0`, expressed on `L²(ℝ⁴)`), `(k₀ / 2) * ‖(ψ : L2d 4)‖ ^ 2 ≤ (inner ℂ (ψ : L2d 4) ((momContModel p).innerHam ψ)).re`, and prove the sufficient continuous-support integrand criterion when `ψ` is supported on `{x : Fin 4 → ℝ | k₀ ^ 2 ≤ x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2}`!
  2. Prove `localizedWall_energy_nonneg` (`0 ≤ (lam / 4) * ∫ Q, ‖localizedWall_fourier χ φ v Q‖^2`) for `0 ≤ lam` as a clean corollary of `localizedWall_energy`, and register both in `Work/Phi4Audit.lean`.
- **Verify:**
  ```bash
  export PATH="/home/leo/.elan/bin:$PATH"
  lake build BookProof.Phi4.ChapterScalarMomentumGap BookProof.Phi4.ChapterScalarFourierIntegral Work.Phi4Audit
  ```

### `Q6` — Fix `sm_defect.rs` Conjugation Bug & Implement Rigorous Interval-Enclosed `amplitude_interval_terms`
- **Read:** `../unfer/fock_sirk/src/sm_defect.rs` (lines 460–720), `../unfer/docs/VERIFY_PHI4_MOMENTUM.md` (§6.1).
- **Edit:** `../unfer/fock_sirk/src/sm_defect.rs`, `../unfer/fock_sirk/tests/phi4_momentum_sirk.rs`.
- **Implement:**
  1. **Fix the conjugation bug in `amplitude_terms` (line 571–572):** in Duhamel's return-amplitude formula `⟨ψ, e^{-i(t-s)H} r(s)⟩ = ⟨e^{+i(t-s)H} ψ, r(s)⟩`, for a **real symmetric** `(H, ψ)` (all `H` matrix elements and `ψ` amplitudes real), time reversal gives `e^{+i(t-s)H} ψ = conj(e^{-i(t-s)H} ψ)`. Replace `inner(&w, &r)` with `inner(&conjugate_nested(&w), &r)` (asserting real symmetry on the window matrix & seed), and document why complex-conjugating `w(t-s)` fixes the dual vector time sign.
  2. **Rename heuristic estimator honestly:** stop calling the un-enclosed sampled trapezoid result `certified_cell` in `phi4_momentum_sirk.rs` (rename to `sampled_cell` / keep `"certified"` strictly for full interval enclosures).
  3. **Implement rigorous `AmplitudeIntervalBound` / `amplitude_interval_terms`:**
     - Using outward-rounded `Interval` (`down`/`up` already in `sm_defect.rs`), enclose:
       (a) `initial_leakage` in `Interval`;
       (b) Composite trapezoid integral of `|⟨conj(w(t-s)), r(s)⟩|` AND `‖r(s)‖` **plus rigorous panel second-derivative remainders** `(t³ / (12 * panels²)) * max_s |d²/ds² ·|` bounded from `‖G‖` and `‖D‖` in `Interval` arithmetic;
       (c) Triangular replacement remainder + outward rounding;
       (d) Explicit `shift_solve_error_bounds` from `JointSirkResult` (GMRES residual contribution propagated through `B` / `G`).
     - Add a unit test in `sm_defect.rs` verifying complex conjugation against a dense exact `e^{+i(t-s)H}ψ` reference on a small 3-mode system and verifying `AmplitudeIntervalBound.probability_bound.hi >= amplitude_terms.probability_bound`.
- **Verify:**
  ```bash
  cd /home/leo/Projects/unfer && cargo test -p fock_sirk sm_defect
  ```

### `Q7` — Tune Hashimoto–SIRK Krylov Rank & Shifts (`../papers/Hashimoto.md` Theorem 4.1) on Continuous `ScalarMomCont`
- **Read:** `../papers/Hashimoto.md` (§4 Eq. (10)/(11) & Theorem 4.1), `../unfer/fock_sirk/tests/phi4_momentum_sirk.rs` (lines 580–835).
- **Edit:** `../unfer/fock_sirk/tests/phi4_momentum_sirk.rs`.
- **Implement:**
  1. Keeping moderate Hermite basis truncation `C ∈ {8, 12}` (remember: only the Krylov space in SIRK is discrete; Hermite basis functions live on continuous `ℝ³_k × ℝ_φ`), sweep higher Krylov rank `m ∈ {4, 6, 8}` and Hashimoto–Nodera decreasing physical shifts `γ_j = (N − j d)/t` (`Hashimoto.md` Eq. (8)–(11), ensuring `m < N/d` and well-conditioned `W_m`).
  2. Replace `certified_cell` with `AmplitudeIntervalBound` (`Q6`).
  3. Assert that for tuned `(C=8, m=6..8)` (fast `< 5 s` runtime):
     - Both null controls (identical cell + diagonal-phase `change_of_basis`) contain `0.0` in their rigorous interval;
     - **Both** `λ: 1.0 → 1.1` (exact shift `≈ −1.613e-3`) **and** `width_k: 1.0 → 1.5` (exact shift `≈ −5.616e-2`) have rigorous `amplitude_interval_terms` paired probability charge **strictly smaller than `|response|`** (genuinely excluding `0.0` with outward `Interval` bounds!).
- **Verify:**
  ```bash
  cd /home/leo/Projects/unfer && cargo test -p fock_sirk --test phi4_momentum_sirk -- --nocapture
  ```

### `Q8` — Continuous Mehler–Hermite Convolution Test, Fast Default Evidence Runner, and Final Cross-Repo Gate
- **Read:** `../unfer/nested_fock_algebra/src/phi4_momentum.rs`, `../unfer/fock_sirk/examples/phi4_momentum_sirk.rs`, `../unfer/docs/fixtures/phi4_momentum_convolution.json` (from `Q4`).
- **Edit:** `../unfer/nested_fock_algebra/src/phi4_momentum.rs`, `../unfer/fock_sirk/examples/phi4_momentum_sirk.rs`, `../unfer/docs/PHI4_NUMERICAL_PLAN.md`, `../unfer/docs/VERIFY_PHI4_MOMENTUM.md`.
- **Implement:**
  1. In `nested_fock_algebra/src/phi4_momentum.rs`, add unit test `continuous_mehler_convolution_matches_fixture` checking the analytic closed-form **continuous** $\int_{\mathbb{R}^3} d^3p$ / $\int_{\mathbb{R}^3} d^3Q$ Plancherel and convolution identities from `docs/fixtures/phi4_momentum_convolution.json` (zero momentum discretization, zero finite-mode projection), while keeping `localized_packet_wall` tagged as a continuous classical integral test of `localizedWall_energy`.
  2. In `fock_sirk/examples/phi4_momentum_sirk.rs`, cap the default sweep at `C <= 24` (`C ∈ {4, 8, 12, 16, 20, 24}`, fast `< 60 s`) unless `PHI4_EXTENDED_CUTOFFS=1` is set in the environment, and include the tuned rank `m ∈ {6, 8}` response cells and rigorous `AmplitudeIntervalBound` fields.
  3. Update `VERIFY_PHI4_MOMENTUM.md` with new SHA-256 digests and measured runtimes.
- **Final Cross-Repo Verification Gate (ALL must exit `0`):**
  ```bash
  # 1. timepiece (Lean 4 + axiom audit + health + links + GitBook drift)
  cd /home/leo/Projects/timepiece && \
    export PATH="/home/leo/.elan/bin:$PATH" && \
    lake build BookProof.Phi4.ChapterScalarMehler BookProof.Phi4.ChapterScalarMomentum \
      BookProof.Phi4.ChapterScalarMomentumGap BookProof.Phi4.ChapterScalarFourierIntegral \
      BookProof.Phi4.ChapterScalarMomRankTwo BookProof.Phi4.ChapterScalarMomOrbit \
      BookProof.Phi4.ChapterScalarSectorOps Work.Phi4Audit && \
    nix-shell -p python3 --run "bash scripts/health.sh" && \
    nix-shell -p python3 --run "python3 scripts/check-links" && \
    bash scripts/check-gitbook-drift

  # 2. unfer (Cadabra2 strict gate + Rust tests + fast evidence fixture)
  cd /home/leo/Projects/unfer && \
    bash scripts/verify_cdb_modules.sh --strict && \
    cargo test -p nested_fock_algebra phi4 && \
    cargo test -p fock_sirk sm_defect && \
    cargo test -p fock_sirk --test phi4_momentum_sirk && \
    cargo run --release -p fock_sirk --example phi4_momentum_sirk > /tmp/phi4_sweep_check.json && \
    python3 -m json.tool /tmp/phi4_sweep_check.json > /dev/null
  ```

---

## 4. Completed Baseline Reference (`P0`–`P13`)

| Phase | Target | Outcome as of 2026-11-27 |
|---|---|---|
| `P0` | `nested_fock_algebra/src/phi4_scalar.rs` | Frozen lattice comparison quarantined; Gram tail weights fixed. |
| `P1`–`P3` | `phi4_momentum_nested.cdb`, `phi4_momentum_mehler.json`, `phi4_localized_wall.json`, `VERIFY_PHI4_MOMENTUM.md` | **PASS** (32 strict checks); classical continuous-integral localized wall fixture added (`Q4` adds continuous Mehler–Hermite convolution checks). |
| `P4`–`P5` | `ChapterScalarMehler`, `ChapterScalarSirk`, `ChapterScalarMomentum` | **PROVED**: `momContModel`, `unitMomCont_vacuum_column` (`17/8`, `553/32`), rank-1 error & return probability. |
| `P6` | `ChapterScalarMomentumGap` | **PARTIAL**: `harmonic_lower_bound`, `contGap_pos`, `unitMomCont_inner_gap` (`7/64`), `unitMomCont_closure_floor`, `shifted_well_comparison_false` proved; `Q1`, `Q2`, `Q5` close general `(λ, v)`, parity commutation, outer gap / uniqueness, and continuous `‖k‖ ≥ k₀` dispersion floor. |
| `P7`–`P10` | `ChapterScalarFourierIntegral`, `ChapterScalarMomRankTwo`, `ChapterScalarMomOrbit`, `ChapterScalarSectorOps`, `Work/Phi4Audit` | **PROVED**: Fourier gradient & `localizedWall_energy`, 11-mode `S₃` rank-2 Hashimoto–SIRK interval `[319447/320000, 39999/40000]`, `outerHam_add_const`, `outerHam_oneParticle_eq`. *(Untracked 2-mode draft `ChapterScalarPacketForm.lean` retired in `Q3` in favor of continuous `ChapterScalarFourierIntegral.lean`.)* |
| `P11`–`P13` | `phi4_momentum.rs`, `tests/phi4_momentum_sirk.rs`, `examples/phi4_momentum_sirk.rs` | **EXECUTED** (10 integration tests, change-of-basis null control); `Q6`–`Q8` fix the `sm_defect` conjugation bug, add rigorous interval enclosures, tune Krylov rank/shifts to exclude zero on `λ`, test continuous Mehler convolutions, and cap default sweeps. |
