# Real scalar λφ⁴ in nested Fock space — Lean 4 formalization plan

The scalar inner operator, its positive closure and its Mehler-window convergence
are now instantiated in Lean. Each outer excitation carries the complete scalar
configuration. All active formalization work focuses **100% on the constraint-free
`book.tex` continuous-momentum SIRK / Mehler / nested-Fock formalism**:
momentum space `k ∈ ℝ³` is **continuous** (integrated with `∫ d³k`, never
discretized into a momentum sum — only the SIRK Krylov subspace / Hermite
window is discrete). The quadratic spatial gradient `½ ∫ |∇φ|² d³x` becomes the
pure diagonal continuous multiplier `½ ∫ |k|² |φ̂(k)|² d³k` (no spatial-derivative
jet constraints or derivative convolutions needed), realized on `L²(ℝ³_k × ℝ_φ)`
as `h_cont(k, φ) = ½ p_φ² + ½ |k|² φ² + (λ/4)(φ² − v²)²`, while the full
coordinate-space quartic is the continuous composite-pair integral
`(λ/4) ∫ d³Q |Ψ(Q)|²`. Periodic lattice modules (`siteModel`, `twoSite`,
`RankTwo`) and the auxiliary static-jet model (`jetModel`) are frozen comparisons.
[Master cheap-LLM plan](PHI4_IMPROVEMENT_PLAN.md) ·
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

The primary scalar operator is `jetModel` on L²(ℝ⁴). Its four coordinates are the
field value s and three independent derivative coordinates j₁, j₂, j₃. In the local
energy-density normalization h = pₛ²/2 + (j₁² + j₂² + j₃²)/2 + U(s). Position can
be carried as a continuous spectator factor. The core consists of product Hermites
in continuous variables. A window cuts off basis occupations, and the rational
Krylov rank counts shifted-solve vectors for that operator.

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

## Next proofs for the Lean4 specialist (100% continuous-momentum `book.tex` formalism)

Detailed step-by-step instructions and pre-verified rational targets live in
[PHI4_IMPROVEMENT_PLAN.md](PHI4_IMPROVEMENT_PLAN.md) (`P4`–`P10`). Do **not**
discretize momentum space into sums, do **not** extend the frozen periodic
lattice comparison (`siteModel`, `twoSite`, `ChapterScalarRankTwoOrbit`), and
do **not** introduce spatial-derivative jet constraints for λφ⁴.

1. **Continuous-momentum model `momContModel` & rank-1 bounds (`P5`).**
   Create `BookProof/Phi4/ChapterScalarMomentum.lean`: define
   `momContModel (p : Parameters) : Model 4 1 4` on `L²(ℝ³_k × ℝ_φ)` with
   `h_cont(k, φ) = ½ p_φ² + ½(k₁² + k₂² + k₃²) φ² + (λ/4)(φ² − v²)²` (`form 0`
   wall, `form 1..3 = X r * X 0`). Prove `unitMomCont_vacuum_column` (mean `17/8`,
   explicit `He₂(φ) K₂` continuous momentum–field coupling), `unitMomCont_defect_norm_sq`
   (`553/32`), `unitMomCont_rankOne_error`, and `unitMomCont_return_probability`
   (`1 − (553/32) t²`).
2. **Unconditional absolute inner gap, unique outer vacuum ground state, and `ℤ₂`
   parity (`P6`).** Create `BookProof/Phi4/ChapterScalarMomentumGap.lean`:
   combine `0 ≤ ‖(P₀ − iα X₀) ψ‖²` with square completion of `(λ/4)(φ² − v²)²`
   at `α = min (1/(2v²)) (min (1/2) (λ/2))` and pointwise `½|k|²φ² ≥ 0` to prove
   `momCont_inner_gap` (`≥ (7/32)α`; `7/64` for `unitMomCont`), lift to
   `momCont_outer_gap` and `momCont_vacuum_unique_ground`, and prove `φ ↦ −φ` and
   `k ↦ −k` symmetries via `ChapterQuadraticRotationEsa`.
3. **Continuous momentum-space Fourier integral identities (`P7`).** Create
   `BookProof/Phi4/ChapterScalarFourierIntegral.lean`: using
   `ChapterNsAdvectionConvolution`, prove `fourier_grad_sq_identity` (diagonal
   `‖𝓕(∂_m φ) k‖² = (2π ⟨k, m⟩)² ‖𝓕 φ k‖²` in continuous `k ∈ ℝ³`) and
   `fourier_phi4_composite_integral` (`𝓕(φ⁴) R = ∫ Q, Ψ(Q) Ψ(R − Q)` —
   continuous integral over `ℝ³`, zero discrete sums!).
4. **3-mode `S₃`-symmetric rank-2 Hashimoto-SIRK & closed orbit interval on
   `unitMomCont` (`P8`–`P9`).** Create `ChapterScalarMomRankTwo.lean` and
   `ChapterScalarMomOrbit.lean`: certify the 11-mode full action of `unitMomCont`
   on `{1, He₂(φ), K₂}` (Gram `diag(1, 2, 6)`), the exact rational Hashimoto
   generator and dissipation at shifts `(10, 5)` from `phi4_momentum_mehler.json`,
   forward contractivity of `e^{sG}`, and the kernel-checked two-sided return
   interval `[319447/320000, 39999/40000]` at `t = 1/100` via `Model.orbit_error`.
5. **Outer shift law & axiom audit (`P10`).** Create `ChapterScalarSectorOps.lean`
   (`dΓ(h + cI) = dΓ(h) + c N_out` and 1-particle sector agreement) and
   `Work/Phi4Audit.lean` auditing every public `BookProof.Phi4` endpoint against
   `[propext, Classical.choice, Quot.sound]`.
