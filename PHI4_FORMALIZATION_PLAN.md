# Real scalar λφ⁴ in nested Fock space — Lean 4 formalization plan

The implemented fibre `momContModel` acts on a wavefunction of a field amplitude
and three continuous angular momenta. Its self-adjoint dynamics, Hermite-window
convergence and unit-parameter return bounds are formalized. Its gradient term is
the multiplier $|k|²φ²/2$. A separate Schwartz identity gives the localized
double-well energy for fields whose Fourier components mix. Scalar spatial derivatives
require no jet constraints. [Fibre and packet work order](PHI4_IMPROVEMENT_PLAN.md) ·
[Analytical plan](../unfer/docs/PHI4_ANALYTIC_PLAN.md) ·
[Numerical plan](../unfer/docs/PHI4_NUMERICAL_PLAN.md)

## Model and energy convention

Use one real field in three spatial dimensions with continuous time, in units ℏ = c = 1.
The field takes values on the whole real line. For λ > 0 and v > 0 choose
U(s) = λ(s² − v²)²/4. The two classical minima are ±v, and U″(±v) = 2λv².
This is a scalar theory with a global reflection symmetry. There are no gauge,
ghost or matter coordinates. The double-well curvature gives a classical frequency
scale. A quantum mass requires a specified correlation function or spectral channel.
The constant λv⁴/4 in the potential density fixes the energy convention.
[Square completion in the SM](BookProof/Sm/ChapterSmHamiltonian.lean)

The fibre benchmark is `momContModel`. Its field and momentum product Hermites
span functions of continuous variables. A Hermite window restricts occupations,
and Krylov rank counts shifted-solve vectors within that window. The older
`jetModel` treats the three derivative coordinates as independent static variables.
Its variance and return estimates refer to that comparison alone.

The nested Hamiltonian is

$$
H=d\Gamma(h)=\sum_{i,j}\langle e_i,h e_j\rangle\,C^\dagger(e_i)A(e_j).
$$

Here i and j label one-particle basis functions. On n outer particles this is a sum of n copies
of h. An inner scalar shift cI therefore contributes c times outer particle number. The Mehler reference Gaussian
represents the inner occupation vacuum. Its image under one outer creation is a
state on which the full h acts. Empty outer space has energy zero.

## Periodic site comparison only

Take a nonempty periodic cubic grid Λ with spacing a > 0, M sites and volume Ma³.
The spatial directions are indexed by r = 1,2,3. Define canonical site coordinates
$Q_x=a^{3/2}\phi_x$ and $P_x=a^{3/2}\pi_x$, so [Qₓ,Pᵧ] = iδₓᵧ. On L²(ℝᴹ,dQ) use

$$
h=\frac12\sum_x P_x^2
  +\frac{1}{2a^2}\sum_{x,r}(Q_{x+\hat r}-Q_x)^2
  +\frac{\lambda}{4a^3}\sum_x(Q_x^2-a^3v^2)^2 .
$$

The site rule defines the gradient, and counts each positive-direction link once
per site and direction. A one-site direction has zero difference. With M = 1 and
a = 1 this recovers the double-well oscillator. This finite-difference operator acts
inside one outer excitation.
The one- and two-site return intervals below apply to this comparison. Identifying
its link variables with continuous derivative coordinates would require an explicit
map intertwining the measures and operators.

## Executed in Lean on 2026-11-20

All identifiers below are in `BookProof.Phi4`. The two parameterized realizations
are `jetModel` and `siteModel`. The latter takes a neighbor function.
`periodicNext` supplies it for any rectangular periodic grid with nonempty sides.

- **Inner domain and dynamics.** `Model.innerHam_pgLp` acts on each polynomial times
  the Mehler Gaussian. `coordinate_ladders`, `momentum_ladders` and
  `coordinate_momentum_commutator` give the same-coordinate canonical pair and the
  cross-coordinate commutator. Real wall and link polynomials and distinct active momenta
  discharge the hypotheses of the existing Weyl ESA theorem. `Model.inner_esa`,
  `Model.closure_nonneg` and `Model.inner_flow` give essential self-adjointness,
  positivity on the graph closure and a Stone group extending that core action.
  [Operator and closure](BookProof/Phi4/ChapterScalarMehler.lean)
- **Shifted solves.** `Model.mehler_sirk` supplies complex-shift resolvents bounded by
  the reciprocal of the absolute imaginary part and the multishift Krylov denominator
  identity. `Model.window_solve_convergence` separately constructs the actual
  finite Hamiltonians on the degree-ordered product Hermites. Each polynomial seed
  eventually belongs to the window. From that point its finite Hamiltonian action is
  the projection of its full image. The common-core criterion then gives strong
  convergence of the inverses at every nonzero imaginary shift and vectorwise convergence
  of the unitary groups uniformly on bounded time intervals. Window size is the
  occupation cutoff. A Krylov rank inside a fixed window is a separate parameter.
  [Complex shifts](BookProof/Phi4/ChapterScalarMehler.lean) ·
  [Finite Hamiltonian solves](BookProof/Phi4/ChapterScalarWindows.lean)
- **Outer Hamiltonian.** `Model.outerHam` is the direct sum of the sector derivations
  restricted to the symmetric parts of the completed tensor powers. `Model.outer_esa`
  reuses the general bosonic lift. Projecting the dense tensor core onto its symmetric
  part gives the dense domain for `Model.outer_flow`. Each term in the one-particle
  energy pairing contributes a squared norm at each tensor slot, including for
  entangled polynomial states. This gives `Model.outer_closure_nonneg`.
  `Model.vacuum_ground` exhibits a unit outer vacuum attaining zero energy.
  This proves existence of a ground state. Its uniqueness and a strict spectral gap
  require additional estimates on the absolute inner energy.
  [Outer domain and dynamics](BookProof/Phi4/ChapterScalarOuter.lean) ·
  [Outer energy and vacuum](BookProof/Phi4/ChapterScalarEnergy.lean)
- **A bounded observable with a full-action estimate.** At unit one-site parameters,
  `unitCell_vacuum_column` gives coefficients 5/8, 7/8 and 1/4 in the unnormalized
  Hermites at occupations 0, 2 and 4. Projecting to the Gaussian alone gives a phase
  with energy 5/8. The discarded components are orthogonal with relative squared norms
  2! and 4!, giving a full residual variance of 97/32. `unitCell_defect_norm_sq`
  proves this equality in the same Hilbert space as the closure.
  `unitCell_rankOne_error` bounds the squared state error by (97/32)t² for a normalized
  seed. `unitCell_return_probability` bounds its exact return probability below by
  1 − (97/32)t². Both statements in Lean retain the unnormalized Gaussian norm explicitly.
  At t = 1/100 the probability lies in [0.999696875, 1]. This interval expresses
  what a rank-one calculation can resolve about the full one-site dynamics.
  [Full residual and return probability](BookProof/Phi4/ChapterScalarSirk.lean)
- **Two-site binding and exact columns (executed 2026-11-20).**
  `BookProof.Phi4.twoSite` is the actual `siteModel (periodicNext 1 0 0)`. The polynomial
  substitution `fromModes` sends `u = (x₀+x₁)/√2`, `w = (x₀−x₁)/√2`; the chain rules
  `fromModes_deriv_zero`/`_one`, `fromModes_momOp_zero`/`_one` and `fromModes_kinetic`
  transport the momenta, while `twoSite_forms` evaluates the eight site forms and
  `twoSite_forms_modes` proves the mixed wall vertex after the rotation. The resulting
  identity is `twoSite_innerHam`: on every polynomial seed the site Hamiltonian equals
  the mode operator `modeHam`. The three exact fixture columns are
  `twoSite_column_00`, `twoSite_column_20` and `twoSite_column_02`, each through total
  degree six in the unnormalized product Hermites.
  [Two-site rotation and columns](BookProof/Phi4/ChapterScalarTwoSite.lean) ·
  [Exact scalar fixture](../unfer/docs/fixtures/phi4_mehler.json)

- **Rank-two certificate (2026-11-21).** In `BookProof.Phi4.RankTwo`, `site_columns`
  identifies the ten-row coefficient matrix with the actual site action. The two-site
  rotation preserves the Gaussian inner product. `rotated_mode_inner` and `synthesis_inner`
  identify its factorial Gram weights for arbitrary complex superpositions, up to the
  common squared norm of the unnormalized vacuum. `basis_second_column` identifies the
  shift-5 inverse applied to the seed. `hashimoto_generator` gives the generator from a
  shift-3 compressed inverse. `dissipation`, `full_defect_hs_squared`, `seed_variance`
  and `orbit_rates` certify exact finite matrix identities over rational complex numbers.
  `defect_split` separates the error inside the retained window from the discarded
  occupation rows, whose squared contribution on the initial seed is exactly 3.
  Using those identities in the short-time estimate gives the two-site return interval
  [159663/160000, 39991/40000] at t = 1/100 and unit parameters. The last inference,
  from the matrix rates to this time-dependent probability, is an analytic derivation.
  An independent Rust `ScalarGrid` builder constructs the site and rotated mode
  Hamiltonians and reproduces all three exact columns to `1e-8`
  (`two_site_columns_match_fixture` in
  [phi4_scalar.rs](../unfer/nested_fock_algebra/src/phi4_scalar.rs)).
  [Rank-two certificates](BookProof/Phi4/ChapterScalarRankTwo.lean) ·
  [Short-time derivation](../unfer/docs/PHI4_ANALYTIC_PLAN.md)

**Executed in Lean on 2026-11-21 (`jetModel` column).**
`BookProof/Phi4/ChapterScalarJet.lean` defines `unitJet`, proves `jet_forms` and
`unitJet_vacuum_column`, and checks the factorial weights in `jet_variance_weights`.
The residual norm equality and the rational orbit remain open.

**Verification on 2026-11-21.** Targeted Lean 4.28.0 checks covered the initial seven scalar
modules. An axiom audit of 21 endpoints, including the vacuum ground state, window
convergence, orbit estimate and two-site certificates, returned only `propext`,
`Classical.choice` and `Quot.sound`. The analytic replay passed 29 exact checks,
distinguished four deliberate mutations and reproduced the complete JSON fixture.
The aggregate project build and a dedicated scalar Rust trajectory run remain separate.

**Executed in Lean on 2026-11-25 (`P4`–`P10`, continuous momentum).**
`ChapterScalarMehler` (Mehler core, one-particle ESA, Stone flow),
`ChapterScalarMomentum` (`momContModel`: mean `17/8`, defect norm squared `553/32`,
rank-one error, `unitMomCont_return_probability`), `ChapterScalarMomentumGap`
(unit core floor `unitMomCont_inner_gap` at `7/64`, `φ ↦ −φ`
and `k ↦ −k` parity), `ChapterScalarFourierIntegral` (continuous-`k` gradient identity
and the composite-pair integral), `ChapterScalarMomRankTwo` (11-mode `S₃` certificate,
shifts `10, 5`, `defect_split` with outside-window squared norm `9/2`),
`ChapterScalarMomOrbit` (rational transport to `ℂ`, speed/acceleration and transverse
Gram certificates, `Model.orbit_error`, and the two-sided interval
`[319447/320000, 39999/40000]` at `t = 1/100`) and `ChapterScalarSectorOps`
(`dΓ(h+cI) = dΓ(h) + c·N_out`, and the `n = 1` outer sector identified with
`M.innerHam`). `Work/Phi4Audit` records the axiom checks for these endpoints.

## Next proofs for the Lean4 specialist (`Q1`, `Q2`, `Q3`, `Q5` in `PHI4_IMPROVEMENT_PLAN.md`)

As of 2026-11-27, `ChapterScalarMomentumGap` proves `harmonic_lower_bound`, `contGap_pos`,
`fieldParity_inner`/`spatialParity_inner`, `unitMomCont_inner_gap` (`7/64`), `unitMomCont_closure_floor`,
and `shifted_well_comparison_false`. Meanwhile, the untracked draft
`BookProof/Phi4/ChapterScalarPacketForm.lean` projected momentum space onto two finite packet
modes (violating the `book.tex` rule that **only the Krylov space in SIRK approximations is discrete,
never momentum space**) and also contained four math/terminology defects (`packetKinetic` used for
spatial gradient stiffness, non-symmetric `G⁻¹K`, missing factor `6` and `|χ|²` localization weight,
and unconjugated `L²` pairing). Work strictly on **continuous** `L²(ℝ³_k × ℝ_φ)` / `𝓢(V, ℂ)` inside
the Mehler / nested-Fock formalism of [`book.tex`](book.tex) in this exact order:

1. **General-parameter inner gap & parity commutation (`Q1` in [`ChapterScalarMomentumGap.lean`](BookProof/Phi4/ChapterScalarMomentumGap.lean)):**
   Prove general `wall_completion (p : Parameters)`, `momCont_inner_gap` (`contGap p * ‖ψ‖² ≤ quadForm (momContModel p).innerHam ψ`),
   `momCont_closure_floor`, and exact commutation of `fieldParity` (`φ ↦ −φ`) and `spatialParity` (`k ↦ −k`)
   with `(momContModel p).innerHam` on `polyGaussCore (d := 4)`.
2. **Bosonic outer sectorwise lift & vacuum uniqueness (`Q2` in [`ChapterScalarMomentumGap.lean`](BookProof/Phi4/ChapterScalarMomentumGap.lean) + [`Work/Phi4Audit.lean`](Work/Phi4Audit.lean)):**
   Using `Model.sector_pair` (`ChapterScalarEnergy`), prove `outer_gap_of_inner_gap` (so sector `n` carries lower bound `n * μ`),
   instantiate `momCont_outer_gap` and `momCont_outer_closure_gap`, and prove `momCont_vacuum_unique_ground`:
   every zero-energy closure state is a scalar multiple of `Model.vacuum 4`. Audit all new theorems in `Work/Phi4Audit.lean`.
3. **Retire finite-mode `ChapterScalarPacketForm.lean` & extend continuous [`ChapterScalarFourierIntegral.lean`](BookProof/Phi4/ChapterScalarFourierIntegral.lean) (`Q3`):**
   Delete the untracked two-mode draft `BookProof/Phi4/ChapterScalarPacketForm.lean` and remove its import/audit lines
   from `BookProof.lean` and `Work/Phi4Audit.lean`. Instead extend `ChapterScalarFourierIntegral.lean` purely on continuous `V`:
   - `fourier_grad_energy_eq`: Plancherel identity turning the continuous gradient energy `½ Σ_m ∫ ‖∂_{b m} φ‖²` into `½ ∫ (2π‖k‖)² ‖𝓕 φ k‖²` (pure continuous multiplier, zero finite-mode matrix);
   - `localizedWall_polarization`: exact quartic polarization of `localizedWall_energy` for real continuous Schwartz fields `a • f₀ + b • f₁` extracting `(3λ/2) a² b² ∫ ‖χ‖² f₀² f₁²` with localization weight `‖χ‖²`, factor `6`, and finite background retained — purely a continuous integral identity, NOT a discrete 2-mode momentum model.
4. **Prove continuous momentum-support dispersion floor & composite-pair form positivity (`Q5` in `ChapterScalarMomentumGap.lean` / `ChapterScalarFourierIntegral.lean`):**
   Formalize `momCont_dispersion_floor`: on continuous `L²(ℝ³_k × ℝ_φ)` wavefunctions supported on `‖k‖ ≥ k₀`,
   `½ ⟨ψ, (p_φ² + |k|² φ²) ψ⟩ ≥ (k₀/2) ‖ψ‖²`, plus nonnegativity of the continuous composite-pair Plancherel
   energy `(λ/4) ∫ |B_χ(Q)|² d³Q ≥ 0` (`localizedWall_energy_nonneg`), auditing both in `Work/Phi4Audit.lean`.
   *(Scope note: any further interacting composite-pair construction must act on continuous functions over `ℝ³_k` inside the `book.tex` Mehler / nested-Fock framework — never discretizing momentum space and never conflating it with periodic lattices or Euclidean OS / Wilson hierarchies.)*

**Executed in Lean on 2026-11-27 (item 2, finite classical half).**
`BookProof/Phi4/ChapterScalarPacketForm.lean` defines the two-packet amplitude model on a
common Schwartz arena: the spatial Gram matrix `packetGram`, the kinetic matrix
`packetKinetic`/`packetKineticMat`, the dual kinetic metric `packetDualKinetic = G⁻¹K` with
`G · (G⁻¹K) = K`, the directional gradient matrices `packetGradient`, the localized wall Gram
matrix `packetWall`, and the both-occupations-by-two element `packetMixed`, whose
Gram-normalized form is invariant under independent packet rescalings.  The ordered *quantum*
operator on those packets, the positivity/domain of the resulting inner form and the continuum
limit remain open.
