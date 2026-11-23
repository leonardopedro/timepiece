# λφ⁴ bundle — timepiece with unfer and papers sources

This file is a single-file, repomix-style snapshot of the real scalar λφ⁴
material in and around the `timepiece` repository. It is intentionally narrower
than a whole-workspace pack.

## Scope

Included in full from `timepiece`:

- `PHI4_FORMALIZATION_PLAN.md` — the λφ⁴ work order and proof plan.
- Every Lean module under `BookProof/Phi4/` — the continuous `jetModel`, the
  periodic `siteModel` comparison, Mehler windows, the outer Fock lift, the
  one-site full-action estimate, and the two-site/rank-two certificate.

Included as excerpts from `timepiece`:

- `BookProof.lean` — the seven λφ⁴ aggregate imports.
- `CURRENT_WORK_ORDER.md` — the single "Real scalar λφ⁴" routing row.
- `CONSOLIDATED_PLAN.md` — the 2026-11-21 scalar λφ⁴ state entry.

Included in full from `../unfer`:

- `docs/PHI4_ANALYTIC_PLAN.md` and `docs/PHI4_NUMERICAL_PLAN.md` — the analytic
  and numerical programs.
- `docs/phi4_mehler.cdb` — the executed Cadabra2/SymPy derivation.
- `docs/fixtures/phi4_mehler.json` — its exact rational fixture.
- `nested_fock_algebra/src/phi4_scalar.rs` — the periodic lattice comparison.
- `nested_fock_algebra/src/exact_inner.rs` — the ordered inner action it calls.
- `docs/CADABRA2_GOTCHAS.md` — the Cadabra2 execution constraints.

Included as excerpts from `../unfer`:

- `fock_sirk/src/joint_sirk.rs` — options, result, solve entry points and the
  rational Krylov core with shifted GMRES.
- `fock_sirk/src/sm_defect.rs` — defect terms and the point certificate.
- `fock_sirk/examples/anharmonic_oscillator.rs` — the oscillator comparison.

Included as excerpts from `../papers`:

- `Hashimoto.md` — the SIRK convergence setting.
- `Kopperman_Tutorial.p.tex` — the generic polynomial-interaction template that
  mentions `phi^4`; it is not a λφ⁴ derivation.
- `book.tex` — the recursive second-quantization / nested-Fock passages. The
  file has no λφ⁴ section and no literal Mehler/Hermite section.

Not included:

- The non-nested-Fock chapters of `book.tex`; they are unrelated BRST/gravity
  material.
- Complete generic Hermite, Stone, SIRK and ESA modules. Only the interfaces the
  λφ⁴ proofs call are excerpted in Part II; the rest is named in the dependency
  map.
- All other proof tracks (QYM, QG, NS, SM, RandomMap, pCNL, book) and their
  plans.

## Source revision and attribution

- Repository: `timepiece`
- Commit at bundle time: `fa22e6f`
- Working tree: the λφ⁴ files and plans are present as working-tree changes.
- Format: Markdown with fenced source blocks; fenced blocks whose info string
  is `text` are excerpts, not standalone files.
- **Attribution:** every content section below starts with a `Source:` line.
  Paths are relative to the repository root. `complete file` means the whole
  file was copied; `lines A–B` identifies the exact excerpt. Line numbers refer
  to the working tree at bundle time, not to commit `fa22e6f`. Markdown headings
  that occur inside a fenced block belong to the copied file, not to this bundle.

## Part I file tree (timepiece)

**Source:** generated from the section list below; it is not a copy of a
repository file. The external tree is in Part II.

```text
timepiece/
├── PHI4_FORMALIZATION_PLAN.md
├── BookProof.lean                                  (λφ⁴ import lines only)
├── BookProof/Phi4/
│   ├── ChapterScalarEnergy.lean
│   ├── ChapterScalarJet.lean
│   ├── ChapterScalarMehler.lean
│   ├── ChapterScalarOuter.lean
│   ├── ChapterScalarRankTwo.lean
│   ├── ChapterScalarRankTwoOrbit.lean
│   ├── ChapterScalarSirk.lean
│   ├── ChapterScalarTwoSite.lean
│   └── ChapterScalarWindows.lean
├── CURRENT_WORK_ORDER.md                           (λφ⁴ row only)
└── CONSOLIDATED_PLAN.md                            (2026-11-21 λφ⁴ entry only)
```

## Part I dependency map

These modules are shared infrastructure, not λφ⁴-specific. Selected excerpts
are bundled in Part II; the map below records the remaining imported names.
Each block names its source file; only names and short descriptions are copied,
not code.

```text
Source: BookProof/Toolbox/ChapterHermiteProductCore.lean
  hermiteMv, pgLp, pgFun, pgMap, pgLp_mem_core

Source: BookProof/Toolbox/ChapterHermiteProductBasis.lean
  inner_pgLp_hermiteMv, hermiteMvNorm, hermiteMvLp, hermiteMvBasis,
  pderiv_hermiteMv, crePoly_hermiteMv

Source: BookProof/Qym/ChapterYangMillsNonAbelianEsa.lean
  momOp, momOp_momOp_d, coordinate/momentum ladders

Source: BookProof/Sirk/ChapterSirkTrotterKato.lean
  Model.orbit_error, SIRK/Trotter–Kato estimates
```

## Contents

---

### File: `PHI4_FORMALIZATION_PLAN.md`

**Source:** `PHI4_FORMALIZATION_PLAN.md` (complete file, 183 lines).

```markdown
# Real scalar λφ⁴ in nested Fock space — Lean 4 formalization plan

The scalar inner operator, its positive closure and its Mehler-window convergence
are now instantiated in Lean. Each outer excitation carries the complete scalar
configuration. Read the degree-ordered window theorem for the limit of a shifted solve,
and specialize it to `jetModel` for continuous-coordinate scalar dynamics.
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

## Next proofs for the Lean4 specialist

1. **Certify an occupied continuous-coordinate Gaussian.** The column is now
   `BookProof.Phi4.unitJet_vacuum_column`: at unit width and λ = v = 1 it derives
   the field Hermites of degrees two and four and the three degree-two jet
   components, with mean 17/8. `jet_variance_weights` checks the factorial-weighted
   sum 145/32. Remaining: prove that weighted sum as an `L²` norm equality, apply
   the rank-one phase estimate, then `Model.orbit_error` to a rational orbit using
   the full jet columns. Vary the occupation window and Krylov rank independently.
2. **Periodic comparison only. Close the rank-two time-dependent theorem in Lean.** The first transport step is
   now `BookProof.Phi4.RankTwoOrbit.twoSite_residual`: the exact fixture column minus
   the `13/4` Gaussian phase is the ten-mode residual polynomial, and
   `synthesize_eq` identifies synthesized coefficients with its Gaussian image. What
   remains is the norm bound on that residual and its integration against the Stone
   group. Transport the dissipative matrix identity through the embedding of rational
   complex coefficients into ℂ.
   Differentiate the reduced Gram norm along the matrix exponential to get forward
   contractivity. Use `synthesis_inner` for the reconstructed orbit and `site_columns`
   for its full image. Instantiate `Model.orbit_error`, which already integrates an
   affine residual bound for a differentiable core orbit, using `orbit_rates`. Prove that the normalized Gaussian return lies inside
   the rational interval above. This is a finite-time claim for one seed and one
   occupation window. Any uniform-in-rank rate needs a separate proof.
3. **Identify the sector flows.** Prove agreement of the one- and two-particle Stone
   groups with the tensor-power actions under the canonical embeddings. Transport global
   reflection through the closures to certify parity selection rules. Distinguish
   an odd-channel excitation energy from the absolute lower bound needed for an outer gap.
4. **Compare larger scalar models within this framework.** First hold the spatial model
   fixed and vary the occupation window and Krylov rank independently. For any change
   in the number of inner coordinates, supply embeddings, compatible priors and a
   common smeared observable. Prove a Cauchy estimate for that observable under those
   embeddings. The independent jets and a spatial derivative determined by site fields
   require their own comparison map. No such map is used in the fixed-model proofs.
```

---

### File: `BookProof.lean` (λφ⁴ imports only)

**Source:** `BookProof.lean`, lines 4081–4087 (the seven λφ⁴ aggregate imports).

```lean
import BookProof.Phi4.ChapterScalarJet
import BookProof.Phi4.ChapterScalarSirk
import BookProof.Phi4.ChapterScalarEnergy
import BookProof.Phi4.ChapterScalarTwoSite
import BookProof.Phi4.ChapterScalarRankTwo
import BookProof.Phi4.ChapterScalarRankTwoOrbit
import BookProof.Phi4.ChapterScalarWindows
```

---

### File: `BookProof/Phi4/ChapterScalarJet.lean`

**Source:** `BookProof/Phi4/ChapterScalarJet.lean` (complete file, 82 lines).

```lean
import BookProof.Phi4.ChapterScalarMehler

/-!
# The continuous-coordinate λφ⁴ vacuum column

The independent-jet model has one field coordinate and three jet coordinates.
At unit width and unit parameters this file computes the full action on the
Mehler Gaussian, keeping the quartic field mode and the three quadratic jet
modes. The residual weights are the factorial weights used by the one-site
rank-one estimate.
-/

namespace BookProof.Phi4

open MvPolynomial HermiteProductCore HermiteProductBasis

noncomputable section

/-- The continuous-coordinate jet model at unit width and unit parameters. -/
def unitJet : Model 4 1 4 :=
  jetModel ⟨1, by norm_num, 1, by norm_num⟩

/-- The form sum splits into the double-well wall in the field coordinate and
one quadratic potential in each of the three jet coordinates. -/
theorem jet_forms (p : MvPolynomial (Fin 4) ℂ) :
    ∑ j, unitJet.form j * (unitJet.form j * p) =
      C (1 / 2 : ℂ) * (X 0 ^ 2 - 1) * ((X 0 ^ 2 - 1) * p) +
        X 1 * (X 1 * p) + X 2 * (X 2 * p) + X 3 * (X 3 * p) := by
  have hw : unitJet.form 0 =
      C (Real.sqrt (1 / 2) : ℂ) * (X 0 * X 0 - 1) := by
    change wall 0 _ _ = _
    simp [wall, smul_eq_C_mul]
  have h1 : unitJet.form 1 = (X 1 : MvPolynomial (Fin 4) ℂ) := by
    change (jetModel ⟨1, by norm_num, 1, by norm_num⟩).form (1 : Fin 4) = _
    rfl
  have h2 : unitJet.form 2 = (X 2 : MvPolynomial (Fin 4) ℂ) := by
    change (jetModel ⟨1, by norm_num, 1, by norm_num⟩).form (2 : Fin 4) = _
    rfl
  have h3 : unitJet.form 3 = (X 3 : MvPolynomial (Fin 4) ℂ) := by
    change (jetModel ⟨1, by norm_num, 1, by norm_num⟩).form (3 : Fin 4) = _
    rfl
  rw [Fin.sum_univ_four, hw, h1, h2, h3]
  ring_nf
  simp only [← map_pow, ← Complex.ofReal_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  push_cast
  apply MvPolynomial.funext
  intro x
  simp
  ring

/-- The full action on the unnormalized Gaussian, in the unnormalized product
Hermites. The constant is 17/8, the field coefficients are 7/8 and 1/4, and
each jet coefficient is 1/2. -/
theorem unitJet_vacuum_column :
    unitJet.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ =
      pgLp (C (17 / 8 : ℂ) + C (7 / 8 : ℂ) * (X 0 ^ 2 - 1) +
        C (1 / 4 : ℂ) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3) +
        C (1 / 2 : ℂ) * (X 1 ^ 2 - 1) +
        C (1 / 2 : ℂ) * (X 2 ^ 2 - 1) +
        C (1 / 2 : ℂ) * (X 3 ^ 2 - 1)) := by
  rw [Model.innerHam_pgLp, jet_forms, Fin.sum_univ_one]
  congr 1
  have hmom : unitJet.momentum 0 = (0 : Fin 4) := rfl
  rw [hmom, BookProof.YangMillsNonAbelianEsa.momOp_momOp_d]
  simp [QgHermiteFriedrichs.coreD, smul_eq_C_mul, Derivation.leibniz]
  apply MvPolynomial.funext
  intro x
  simp
  ring

/-- Factorial-weighted squared residual of the jet vacuum column. The factors
2! and 4! are the squared norms of the unnormalized Hermites; the final factor
3 is the number of independent jet directions. -/
theorem jet_variance_weights :
    (7 / 8 : ℝ)^2 * Nat.factorial 2 + (1 / 4 : ℝ)^2 * Nat.factorial 4 +
      3 * ((1 / 2 : ℝ)^2 * Nat.factorial 2) = 145 / 32 := by
  norm_num [Nat.factorial]

end

end BookProof.Phi4
```

---

### File: `BookProof/Phi4/ChapterScalarMehler.lean`

**Source:** `BookProof/Phi4/ChapterScalarMehler.lean` (complete file, 260 lines).

```lean
import BookProof.Sm.ChapterSmFockEsa
import BookProof.Toolbox.ChapterFockStatisticsCompletion
import BookProof.Toolbox.ChapterEsaClosure
import BookProof.Toolbox.ChapterHermiteProductBasis

/-!
# A real scalar quartic on the Mehler core

A single outer quantum carries all the inner coordinates. The scalar model `jetModel`
acts on continuous field and jet variables. Its Mehler indices enumerate Hermite functions.
`siteModel` is a separate lattice comparison whose gradient uses periodic differences
when instantiated with `periodicNext`. Both reuse the bosonic SM closure and outer lift.
-/
namespace BookProof.Phi4

open MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsHermite
open BookProof.YangMillsFriedrichs BookProof.YangMillsNonAbelianEsa
open BookProof.FriedrichsExtension BookProof.TensorCore BookProof.SecondQuantizationCore
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.ChapterStoneResolvent

noncomputable section

structure Parameters where
  coupling : ℝ
  coupling_pos : 0 < coupling
  vev : ℝ
  vev_pos : 0 < vev

/-- A scalar Mehler Hamiltonian in the half-sum-of-squares normalization. -/
structure Model (d k r : ℕ) where
  momentum : Fin k → Fin d
  distinct : Function.Injective momentum
  form : Fin r → MvPolynomial (Fin d) ℂ
  real_form : ∀ j, RealCoeff (form j)

def wall {d : ℕ} (s : Fin d) (scale offset : ℝ) : MvPolynomial (Fin d) ℂ :=
  (scale : ℂ) • (X s * X s - C (offset : ℂ))

theorem real_wall {d : ℕ} (s : Fin d) (scale offset : ℝ) : RealCoeff (wall s scale offset) :=
  RealCoeff.smul (SmHamiltonian.RealCoeff.sub' ((realCoeff_X s).mul (realCoeff_X s))
    (SmHamiltonian.realCoeff_C_real offset))

/-- Unit-volume local model. Coordinate zero is the scalar, the other three are jets. -/
def jetModel (p : Parameters) : Model 4 1 4 where
  momentum := fun _ => 0
  distinct := fun _ _ _ => Subsingleton.elim _ _
  form := Fin.cases (wall 0 (Real.sqrt (p.coupling / 2)) (p.vev ^ 2)) (fun i => X i.succ)
  real_form := Fin.cases (real_wall ..) (fun i => realCoeff_X i.succ)

/-- Four forms per site: the wall, followed by the three forward links. -/
def siteForm {m : ℕ} (next : Fin m → Fin 3 → Fin m) (p : Parameters) (a : ℝ)
    (site : Fin m) : Fin 4 → MvPolynomial (Fin m) ℂ :=
  Fin.cases (wall site (Real.sqrt (p.coupling / (2 * a ^ 3))) (a ^ 3 * p.vev ^ 2))
    (fun r => ((a⁻¹ : ℝ) : ℂ) • (X (next site r) - X site))

def siteModel {m : ℕ} (next : Fin m → Fin 3 → Fin m) (p : Parameters)
    (a : ℝ) (_ha : 0 < a) : Model m m (m * 4) where
  momentum := id
  distinct := Function.injective_id
  form := fun j => let ij := finProdFinEquiv.symm j; siteForm next p a ij.1 ij.2
  real_form := by
    intro j
    let ij : Fin m × Fin 4 := finProdFinEquiv.symm j
    change RealCoeff (siteForm next p a ij.1 ij.2)
    exact Fin.cases (motive := fun i => RealCoeff (siteForm next p a ij.1 i))
      (real_wall ..) (fun _ => RealCoeff.smul
        (SmHamiltonian.RealCoeff.sub' (realCoeff_X _) (realCoeff_X _))) ij.2

/-- A rectangular periodic cell with nonempty sides of lengths nx+1, ny+1, nz+1. -/
def periodicNext (nx ny nz : ℕ) (site : Fin ((nx+1) * ((ny+1) * (nz+1)))) (r : Fin 3) :
    Fin ((nx+1) * ((ny+1) * (nz+1))) :=
  let (x, yz) := finProdFinEquiv.symm site
  let (y, z) := finProdFinEquiv.symm yz
  let pack := fun x' y' z' => finProdFinEquiv (x', finProdFinEquiv (y', z'))
  ![pack (x+1) y z, pack x (y+1) z, pack x y (z+1)] r

theorem site_wall_energy (p : Parameters) {a : ℝ} (ha : 0 < a) (q : ℝ) :
    (Real.sqrt (p.coupling / (2 * a^3)) * (q^2 - a^3 * p.vev^2))^2 / 2 =
      p.coupling / (4 * a^3) * (q^2 - a^3 * p.vev^2)^2 := by
  have hp := p.coupling_pos
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

namespace Model

variable {d k r : ℕ} (M : Model d k r)

def innerHam := weylPoly M.momentum M.form

/-- Column action before any occupation projection. Both applications of each ladder word
take place on the polynomial core. -/
theorem innerHam_pgLp (p : MvPolynomial (Fin d) ℂ) :
    M.innerHam ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (((1/2 : ℝ) : ℂ) •
      ((∑ i, momOp (M.momentum i) (momOp (M.momentum i) p)) +
        ∑ j, M.form j * (M.form j * p))) := by
  simp only [innerHam, weylPoly, weylOp_apply, op_pgLp_d, mulOp_apply]
  change _ = pgMap _
  rw [map_smul, map_add, map_sum, map_sum]
  rfl

private theorem mom_sym (i : Fin k) :
    SymmetricOn polyGaussCore (polyGaussCore.subtype.comp
      ((coreRepPoly d).op (momOp (M.momentum i)))) :=
  (coreRepPoly d).symmetricOn_op (momOp_polySym _)

private theorem field_sym (i : Fin r) :
    SymmetricOn polyGaussCore (polyGaussCore.subtype.comp
      ((coreRepPoly d).op (mulOp (M.form i)))) :=
  (coreRepPoly d).symmetricOn_op (mulOp_polySym (M.real_form i))

theorem symmetric : SymmetricOn polyGaussCore M.innerHam :=
  weylOpDom_symmetricOn M.mom_sym M.field_sym

theorem nonneg (x : polyGaussCore (d := d)) : 0 ≤ quadForm M.innerHam x :=
  weylOpDom_quadForm_nonneg M.mom_sym M.field_sym x

theorem inner_esa : EssentiallySelfAdjointOn polyGaussCore M.innerHam :=
  weylPoly_esa M.distinct M.real_form

theorem positive_extension :
    ∃ (D : Submodule ℂ (L2d d)) (A : D →ₗ[ℂ] L2d d), IsPositiveSelfAdjointExtension M.innerHam A :=
  friedrichs_extension_exists_of_complete_explicit
    ⟨polyGaussCore, M.innerHam, M.symmetric, M.nonneg⟩ polyGaussCore_dense

open EsaClosure HashimotoShiftInvert HermiteGalerkin Filter Topology FockStatistics

theorem closure_nonneg (x : clDom M.innerHam) :
    0 ≤ quadForm (clExt M.innerHam polyGaussCore_dense M.symmetric) x := by
  obtain ⟨D, A, hA⟩ := M.positive_extension
  obtain ⟨hD, hval⟩ := positiveExtension_eq_closure_of_esa polyGaussCore_dense M.symmetric
    M.inner_esa hA
  have hx : (x : L2d d) ∈ D := hD.symm ▸ x.property
  have h := hA.2.2.1 ⟨x, hx⟩
  simpa only [quadForm, hval x hx x.property] using h

theorem inner_flow :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension M.innerHam T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense M.symmetric M.inner_esa

/-- Actual complex-shift resolvents of the scalar extension, rational Krylov denominator
identity and strong convergence of compressions of those resolvents on the Mehler core basis. -/
theorem mehler_sirk (e : ℕ ≃ (Fin d →₀ ℕ)) (z : ℕ → ℂ) (hz : ∀ j, (z j).im ≠ 0) :
    ∃ (D : Submodule ℂ (L2d d)) (A : D →ₗ[ℂ] L2d d) (R : ℕ → L2d d →L[ℂ] L2d d),
      IsSelfAdjointExtension M.innerHam A ∧ (∀ j, IsShiftInvertC A (z j) (R j)) ∧
      (∀ j, ‖R j‖ ≤ |(z j).im|⁻¹) ∧
      (∀ m v n, sirkDen (R m) (fun i => z m - z i) n (rkVec R v n) = (R m ^ n) v) ∧
      (∀ j u, Tendsto (fun n => galerkinCompression (R j) (coreBasis e) n u)
        atTop (nhds (R j u))) := by
  obtain ⟨D, A, R, hext, hR, hnorm, _, _, _, _, hden, hlim, _⟩ :=
    hashimoto_multishift_selects_esa (coreBasis e) M.innerHam polyGaussCore_dense M.symmetric
      M.inner_esa z hz
  exact ⟨D, A, R, hext, hR, hnorm, hden, hlim⟩

/-- The Hilbert direct sum of completed *symmetric* tensor sectors. -/
def outerHam := hbosonicFockOp (L2dSpace d) polyGaussCore M.innerHam

theorem outer_esa : EssentiallySelfAdjointOn _ M.outerHam :=
  hbosonicFock_esa (Hs := L2dSpace d) M.innerHam polyGaussCore_dense M.symmetric M.inner_esa

end Model

open HermiteProductBasis

theorem coordinate_ladders {d : ℕ} (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulOp (X j) p = crePoly j p + annPoly j p := by
  simp

theorem momentum_ladders {d : ℕ} (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j p = (Complex.I / 2) • (crePoly j p - annPoly j p) := by
  simp only [momOp_apply, crePoly_apply, annPoly_apply, smul_eq_C_mul]
  apply MvPolynomial.funext
  intro y
  simp
  ring

/-- On the common polynomial core this gives i times the identity for equal sites
and zero for distinct sites. -/
theorem coordinate_momentum_commutator {d : ℕ} (i j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulOp (X i) (momOp j p) - momOp j (mulOp (X i) p) =
      (if i = j then Complex.I else 0) • p := by
  simp only [mulOp_apply, momOp_apply, Derivation.leibniz, smul_eq_mul, smul_eq_C_mul]
  by_cases h : i = j
  · subst i
    simp
    ring
  · simp [h, pderiv_X_of_ne h]
    ring

def unitCell : Model 1 1 (1*4) :=
  siteModel (periodicNext 0 0 0) ⟨1, by norm_num, 1, by norm_num⟩ 1 (by norm_num)

/-- The three periodic differences in the single cell vanish. The remaining squared form
is one half of (x²−1)² before the overall factor 1/2 in h. -/
private theorem unitCell_forms (p : MvPolynomial (Fin 1) ℂ) :
    ∑ j, unitCell.form j * (unitCell.form j * p) =
      C (1/2 : ℂ) * (X 0 ^ 2 - 1)^2 * p := by
  have hs : (Real.sqrt (1/2) : ℂ)^2 = 1/2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  let x : MvPolynomial (Fin 1) ℂ := X 0
  let t := C (Real.sqrt (1/2) : ℂ) * (x*x-1)
  have hw : unitCell.form 0 = t := by
    change wall (0 : Fin 1) _ _ = _
    simp [wall, t, x, smul_eq_C_mul]
  have hz (i : Fin 3) : unitCell.form i.succ = 0 := by
    have hnext (j : Fin 3) : periodicNext 0 0 0 0 j = 0 :=
      Fin.eq_zero _
    fin_cases i <;> change ((_ : ℝ) : ℂ) • (X (periodicNext 0 0 0 0 _) - X 0) = 0 <;>
      rw [hnext, sub_self, smul_zero]
  change (∑ j : Fin 4, _) = _
  rw [Fin.sum_univ_succ, hw]
  simp only [hz, zero_mul, Finset.sum_const_zero, add_zero]
  dsimp [t, x]
  apply MvPolynomial.funext
  intro y
  simp only [map_mul, map_sub, map_one, map_pow, eval_C, eval_X]
  linear_combination (y 0 * y 0 - 1)^2 * eval y p * hs

/-- Full one-site vacuum column in the unnormalized probabilists' Hermite basis.
The three summands are He₀, He₂ and He₄ with their measured coefficients. -/
theorem unitCell_vacuum_column :
    unitCell.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ =
      pgLp (C (5/8 : ℂ) + C (7/8 : ℂ) * (X 0 ^ 2 - 1)
        + C (1/4 : ℂ) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3)) := by
  rw [Model.innerHam_pgLp, unitCell_forms, Fin.sum_univ_one]
  congr 1
  change _ • (momOp 0 (momOp 0 1) + _) = _
  rw [momOp_momOp_d]
  simp [QgHermiteFriedrichs.coreD, smul_eq_C_mul, Derivation.leibniz]
  apply MvPolynomial.funext
  intro y
  simp
  ring

/-- Squared full residual of the normalized vacuum column in the rank-one window.
The factors 2! and 4! convert the probabilists’ Hermites to normalized coefficients. -/
theorem vacuum_residual_squared :
    (7/8 : ℝ)^2 * Nat.factorial 2 + (1/4 : ℝ)^2 * Nat.factorial 4 = 97/32 := by
  norm_num [Nat.factorial]

/-- Exact inverse compression in the one-column occupation window. -/
theorem vacuum_window_generator (γ : ℝ) :
    (γ : ℂ) - ((1 / ((γ : ℂ) + Complex.I * (5/8)))⁻¹) = -Complex.I * (5/8) := by
  simp only [one_div, inv_inv]
  ring

/-- Under orthonormal two-site mixing the local quartic contains a mixed term. -/
theorem two_site_vertex (u w : ℝ) :
    ((u+w) / Real.sqrt 2)^4 + ((u-w) / Real.sqrt 2)^4 =
      (u^4 + 6*u^2*w^2 + w^4)/2 := by
  have hs : (Real.sqrt 2)^4 = 4 := by
    rw [show (4 : ℕ) = 2*2 by decide, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [div_pow, div_pow, hs]
  ring

end
end BookProof.Phi4
```

---

### File: `BookProof/Phi4/ChapterScalarWindows.lean`

**Source:** `BookProof/Phi4/ChapterScalarWindows.lean` (complete file, 72 lines).

```lean
import BookProof.Phi4.ChapterScalarMehler
import BookProof.ChapterBrstUnboundedLeakage
import BookProof.ChapterFiniteSectionSingleTime
import BookProof.Toolbox.ChapterDegreeEnumeration
import BookProof.ChapterQuadraticFockEsa

/-!
# Shifted solves of finite scalar Mehler Hamiltonians

A degree-ordered Hermite window eventually contains each polynomial seed. On that
seed the compressed Hamiltonian then acts as the projection of the full column.
The common-core criterion turns this observation into convergence of the solves.
-/
namespace BookProof.Phi4.Model

open Filter Topology HermiteProductCore HermiteGalerkin DegreeEnumeration QuadFockEsa
open EsaClosure BrstUnboundedLeakage ChapterStoneResolvent ChapterSirkTrotterKato
open FiniteSectionSingleTime QgTruncationResolvent SirkSingleTime

noncomputable section

variable {d k r : ℕ} (M : Model d k r) (hd : 0 < d)

/-- Finite occupation window ordered by total Mehler degree. -/
def window (n : ℕ) := galerkinSpan (hermBasisN (degreeEnum hd)) n

instance (n : ℕ) : FiniteDimensional ℂ (window hd n) :=
  galerkinSpan_finiteDimensional _ _

variable {T : UnboundedSelfAdjoint (L2d d)} (ext : IsSelfAdjointExtension M.innerHam T.op)

include ext in
theorem window_le_domain (n : ℕ) : window hd n ≤ T.domain := by
  intro x hx
  have hm := galerkinSpan_le_finiteModeDomain _ _ hx
  rw [finiteModeDomain_hermBasisN] at hm
  exact (ext.1 ⟨x, hm⟩).choose

/-- The bounded self-adjoint P h P, extended by zero off its window. -/
def windowHam (n : ℕ) :=
  ofBounded (truncGen T (window hd n) (M.window_le_domain hd ext n))
    (truncGen_isSelfAdjoint ..)

/-- Shifted finite Hamiltonians converge at every nonzero imaginary shift.
Their unitary groups converge on each vector uniformly on compact time intervals. -/
theorem window_solve_convergence :
    (∀ (l : ℝ), l ≠ 0 → ∀ x : L2d d, Tendsto (fun n => (M.windowHam hd ext n).resCLM l x)
      atTop (𝓝 (T.resCLM l x))) ∧
    ∀ (x : L2d d) (t : ℝ), 0 ≤ t →
      TendstoUniformlyOn (fun n s => (M.windowHam hd ext n).stoneU s x)
        (fun s => T.stoneU s x) atTop (Set.Icc (-t) t) := by
  let b := hermBasisN (degreeEnum hd)
  let A := fun n => truncGen T (window hd n) (M.window_le_domain hd ext n)
  have hS n := isSelfAdjointExtension_ofBounded (A n) (truncGen_isSelfAdjoint ..) polyGaussCore
  have hconv (x : polyGaussCore (d := d)) :
      Tendsto (fun n => A n (x : L2d d)) atTop (𝓝 (M.innerHam x)) := by
    have hx : (x : L2d d) ∈ finiteModeDomain b := by
      simpa only [b, finiteModeDomain_hermBasisN] using x.property
    obtain ⟨N, hN⟩ := exists_mem_galerkinSpan b hx
    apply (galerkinProj_tendsto b (M.innerHam x)).congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hm : (x : L2d d) ∈ window hd n := galerkinSpan_mono b hn hN
    change _ = projOp (window hd n) (opProj T _ _ (x : L2d d))
    rw [opProj_apply_of_mem _ _ _ hm, (ext.1 x).choose_spec]
    rfl
  have hstrong : StrongResolventConvergence T (M.windowHam hd ext) :=
    strongResolventConvergence_of_core M.inner_esa ext hS hconv
  exact ⟨fun l hl => strongResAt_of_ne_zero one_ne_zero hl hstrong,
    fun v t ht => trotterKato_tendstoUniformlyOn _ _ hstrong v ht⟩

end
end BookProof.Phi4.Model
```

---

### File: `BookProof/Phi4/ChapterScalarOuter.lean`

**Source:** `BookProof/Phi4/ChapterScalarOuter.lean` (complete file, 124 lines).

```lean
import BookProof.Phi4.ChapterScalarMehler
import BookProof.ChapterDiagonalDGammaEsa

/-!
# Dynamics on the completed symmetric outer Fock space

Projecting a dense tensor core with the continuous bosonic symmetrizer gives
a dense core in its range. This supplies the density input for the Stone bridge.
The empty outer sector has zero Hamiltonian even with the scalar energy constant.
-/
namespace BookProof.Phi4.Model

open TensorCore SecondQuantizationCore FockStatistics ReducedEsa GraphCore DiagonalDGamma
open YangMillsNonAbelianEsa
open DirectSumEsa HermiteProductCore FarisLavine EsaClosure ChapterStoneResolvent StoneBridge

noncomputable section

private theorem symmetricCore_dense (Hs : IPSpace) (D : Submodule ℂ Hs.carrier)
    (hd : Dense (D : Set Hs.carrier)) (n : ℕ) :
    Dense (redDom (cbosonicProj Hs n) (fockSectorDom Hs D n) :
      Set (sector (cbosonicProj Hs n))) := by
  have hspan : Dense (Submodule.span ℂ (Set.range fun x : D => (x : Hs.carrier)) :
      Set Hs.carrier) := by simpa using hd
  have hfull : Dense (fockSectorDom Hs D n : Set (fockSector Hs n)) := by
    apply (dense_span_fockEigVec Hs D id hspan n).mono
    apply SetLike.coe_subset_coe.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact fockEigVec_mem Hs D id n f
  let P := cbosonicProj Hs n
  let f := fun x => (⟨P x, x, rfl⟩ : sector P)
  have hsur : Function.Surjective f := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hsym : P.IsSymmetric := (isReducingProjection_cbosonicProj Hs n).symm
  have hcont : Continuous f := hsym.continuous.subtype_mk _
  apply (hsur.denseRange.dense_image hcont hfull).mono
  rintro _ ⟨y, hy, rfl⟩
  exact (cpermRep Hs n).avgProj_mem (cpermRep_mem_fockSectorDom Hs D n) y hy

variable {d k r : ℕ} (M : Model d k r)

/-- Tensor products of the polynomial core remain total after symmetrization. -/
theorem outerCore_dense (d : ℕ) :
    Dense (hbosonicFockDom (L2dSpace d) polyGaussCore : Set (hbosonicFock (L2dSpace d))) :=
  dsCore_dense (D := fun n => redDom (cbosonicProj (L2dSpace d) n)
    (fockSectorDom (L2dSpace d) polyGaussCore n))
    (fun n => symmetricCore_dense (L2dSpace d) polyGaussCore (polyGaussCore_dense (d := d)) n)

theorem outer_symmetric : SymmetricOn _ M.outerHam :=
  hbosonicFock_symmetricOn (Hs := L2dSpace d) M.innerHam M.symmetric

theorem outer_flow :
    ∃ (T : UnboundedSelfAdjoint (hbosonicFock (L2dSpace d)))
      (U : ℝ → hbosonicFock (L2dSpace d) →L[ℂ] hbosonicFock (L2dSpace d)),
      IsSelfAdjointExtension M.outerHam T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa M.outerHam (outerCore_dense d) M.outer_symmetric M.outer_esa

/-- Restricting to zero outer particles annihilates every vector there. -/
theorem outer_zero_sector (x : hbosonicFockDom (L2dSpace d) polyGaussCore) :
    (M.outerHam x) 0 = 0 := by
  apply Subtype.ext
  let Hs := L2dSpace d
  let D := polyGaussCore (d := d)
  let v : fockSectorDom Hs D 0 := redIncl (cbosonicProj Hs 0) _
    ⟨((x : hbosonicFock Hs) 0), x.property.2 0⟩
  change fockSectorOp Hs D M.innerHam 0 v = 0
  obtain ⟨z, hz, h⟩ := v.property
  rw [show fockSectorOp Hs D M.innerHam 0 v = sectorEmb Hs 0
      (sectorOp Hs D M.innerHam 0 ⟨z, hz⟩) from pushOp_apply _ _ _ _ h.symm]
  obtain ⟨s, hs⟩ := hz
  rw [sectorOp_apply Hs D M.innerHam 0 _ s hs.symm, derPow_zero, map_zero]

theorem outer_number_conserving (x : hbosonicFockDom (L2dSpace d) polyGaussCore) {n : ℕ}
    (hx : ∀ i, i ≠ n → (x : hbosonicFock (L2dSpace d)) i = 0) (i : ℕ) (hi : i ≠ n) :
    (M.outerHam x) i = 0 :=
  Qg3DGaugeFL.dsOp_number_conserving _ x hx i hi

theorem outer_vacuum_action (x : hbosonicFockDom (L2dSpace d) polyGaussCore)
    (hx : ∀ i, i ≠ 0 → (x : hbosonicFock (L2dSpace d)) i = 0) : M.outerHam x = 0 := by
  apply lp.ext
  funext i
  by_cases h : i = 0
  · subst i
    exact M.outer_zero_sector x
  · exact M.outer_number_conserving x hx i h

/-- The unit scalar in tensor degree zero, included into the completed symmetric core. -/
private def vacuumComponent (d : ℕ) :
    redDom (cbosonicProj (L2dSpace d) 0) (fockSectorDom (L2dSpace d) polyGaussCore 0) := by
  let Hs := L2dSpace d
  let D := polyGaussCore (d := d)
  let one : ((domSpace Hs D).pow 0).carrier := (1 : ℂ)
  let z := inclPow Hs D 0 one
  have hz : z ∈ sectorDom Hs D 0 := ⟨one, rfl⟩
  refine ⟨⟨sectorEmb Hs 0 z, (mem_cbosonicSector_iff Hs 0).mpr ?_⟩,
    mem_pushDom (sectorEmb Hs 0) (⟨z, hz⟩ : sectorDom Hs D 0)⟩
  intro σ
  rw [Subsingleton.elim σ 1, (cpermRep Hs 0).act_one]

def vacuum (d : ℕ) : hbosonicFockDom (L2dSpace d) polyGaussCore :=
  ⟨lp.single (E := fun n => ↥(sector (cbosonicProj (L2dSpace d) n))) 2 0 (vacuumComponent d).val,
    single_mem_dsCore (D := fun n =>
    redDom (cbosonicProj (L2dSpace d) n) (fockSectorDom (L2dSpace d) polyGaussCore n))
    0 (vacuumComponent d)⟩

theorem vacuum_norm (d : ℕ) : ‖(vacuum d : hbosonicFock (L2dSpace d))‖ = 1 := by
  change ‖lp.single (E := fun n => ↥(sector (cbosonicProj (L2dSpace d) n))) 2 0
    (vacuumComponent d).val‖ = 1
  rw [lp.norm_single (by norm_num)]
  change ‖sectorEmb (L2dSpace d) 0 (inclPow (L2dSpace d) polyGaussCore 0 _)‖ = 1
  rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
  exact norm_one (α := ℂ)

theorem vacuum_energy_zero : M.outerHam (vacuum d) = 0 := by
  apply M.outer_vacuum_action
  intro i hi
  change (lp.single (E := fun n => ↥(sector (cbosonicProj (L2dSpace d) n))) 2 0
    (vacuumComponent d).val) i = 0
  rw [lp.single_apply, Pi.single_eq_of_ne hi]

end
end BookProof.Phi4.Model
```

---

### File: `BookProof/Phi4/ChapterScalarEnergy.lean`

**Source:** `BookProof/Phi4/ChapterScalarEnergy.lean` (complete file, 136 lines).

```lean
import BookProof.Phi4.ChapterScalarOuter

/-!
# Positivity of the scalar Hamiltonian on symmetric outer sectors

The one-particle energy pairing is a sum of inner products. Tensoring each
factor with the other particle slots gives the same identity for entangled
polynomial states. Taking a diagonal yields positivity on every outer sector.
-/
namespace BookProof.Phi4.Model

open TensorCore SecondQuantizationCore FockStatistics ReducedEsa GraphCore
open YangMillsNonAbelianEsa YangMillsHermite YangMillsFriedrichs HermiteProductCore
open FarisLavine FriedrichsExtension EsaClosure
open scoped TensorProduct InnerProductSpace

noncomputable section
variable {d k r : ℕ} (M : Model d k r)

private abbrev fieldDom (d : ℕ) := domSpace (L2dSpace d) polyGaussCore

private def factor : Fin k ⊕ Fin r → polyGaussCore (d := d) →ₗ[ℂ] L2d d :=
  Sum.elim (fun i => polyGaussCore.subtype.comp ((coreRepPoly d).op (momOp (M.momentum i))))
    (fun j => polyGaussCore.subtype.comp ((coreRepPoly d).op (mulOp (M.form j))))

private theorem inner_pair (x y : polyGaussCore (d := d)) :
    inner ℂ (x : L2d d) (M.innerHam y) = (1/2 : ℂ) *
      ∑ i, inner ℂ (factor M i x) (factor M i y) := by
  rw [innerHam, weylPoly, weylOp_apply, inner_smul_right, inner_add_right, inner_sum, inner_sum]
  conv_rhs => arg 2; rw [Fintype.sum_sum_type]
  have hpi (i : Fin k) := (coreRepPoly d).symmetricOn_op
    (momOp_polySym (M.momentum i)) x ((coreRepPoly d).op (momOp (M.momentum i)) y)
  have hf (j : Fin r) := (coreRepPoly d).symmetricOn_op
    (mulOp_polySym (M.real_form j)) x ((coreRepPoly d).op (mulOp (M.form j)) y)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hpi hf
  simp only [factor, Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, Submodule.subtype_apply,
    hpi, hf, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

private def slot : ∀ (n : ℕ), Fin n → (Fin k ⊕ Fin r) →
    ((fieldDom d).pow n).carrier →ₗ[ℂ] ((L2dSpace d).pow n).carrier
  | 0, i => i.elim0
  | n+1, i => Fin.cases
      (fun j => TensorProduct.map (factor M j) (inclPow (L2dSpace d) polyGaussCore n).toLinearMap)
      (fun s j => TensorProduct.map polyGaussCore.subtype (slot n s j)) i

private theorem sector_pair (n : ℕ) (x y : ((fieldDom d).pow n).carrier) :
    inner ℂ (inclPow (L2dSpace d) polyGaussCore n x)
      (derPow (L2dSpace d) polyGaussCore M.innerHam n y) =
    (1/2 : ℂ) * ∑ s, ∑ j, inner ℂ (slot M n s j x) (slot M n s j y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz =>
      simp only [map_add, inner_add_left, hx, hz, Finset.sum_add_distrib, mul_add]
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
        simp only [map_add, inner_add_right, hy, hz, Finset.sum_add_distrib, mul_add]
      | tmul c e =>
        change polyGaussCore (d := d) at a c
        rw [inclPow_tmul, derPow_tmul, inner_add_right, TensorProduct.inner_tmul,
          TensorProduct.inner_tmul, Fin.sum_univ_succ]
        change _ = (1/2 : ℂ) * ((∑ j, inner ℂ
          ((factor M j a) ⊗ₜ[ℂ] inclPow (L2dSpace d) polyGaussCore n b)
          ((factor M j c) ⊗ₜ[ℂ] inclPow (L2dSpace d) polyGaussCore n e)) +
          ∑ s, ∑ j, inner ℂ ((a : L2d d) ⊗ₜ[ℂ] slot M n s j b)
            ((c : L2d d) ⊗ₜ[ℂ] slot M n s j e))
        simp only [TensorProduct.inner_tmul, LinearIsometry.inner_map_map]
        change inner ℂ (a : L2d d) (M.innerHam c) * inner ℂ b e +
          inner ℂ (a : L2d d) (c : L2d d) * inner ℂ
          (inclPow (L2dSpace d) polyGaussCore n b)
          (derPow (L2dSpace d) polyGaussCore M.innerHam n e) = _
        rw [inner_pair M a c, ih b e]
        rw [← Finset.sum_mul]
        have pull (q : ℂ) (f : Fin n → (Fin k ⊕ Fin r) → ℂ) :
            (∑ i, ∑ j, q * f i j) = q * ∑ i, ∑ j, f i j := by simp only [Finset.mul_sum]
        rw [pull (inner ℂ (a : L2d d) (c : L2d d))
          (fun i j => inner ℂ (slot M n i j b) (slot M n i j e))]
        ring


private theorem sector_nonneg (n : ℕ)
    (x : redDom (cbosonicProj (L2dSpace d) n) (fockSectorDom (L2dSpace d) polyGaussCore n)) :
    0 ≤ quadForm (cbosonicSectorOp (L2dSpace d) polyGaussCore M.innerHam n) x := by
  let Hs := L2dSpace d
  let D := polyGaussCore (d := d)
  let v := redIncl (cbosonicProj Hs n) (fockSectorDom Hs D n) x
  change 0 ≤ (inner ℂ (v : fockSector Hs n) (fockSectorOp Hs D M.innerHam n v)).re
  obtain ⟨z, hz, he⟩ := v.property
  rw [show fockSectorOp Hs D M.innerHam n v = sectorEmb Hs n
      (sectorOp Hs D M.innerHam n ⟨z, hz⟩) from pushOp_apply _ _ _ _ he.symm, ← he]
  change 0 ≤ (inner ℂ (sectorEmb Hs n z) (sectorEmb Hs n _)).re
  rw [LinearIsometry.inner_map_map]
  obtain ⟨s, hs⟩ := hz
  rw [sectorOp_apply Hs D M.innerHam n _ s hs.symm, ← hs]
  change 0 ≤ (inner ℂ (inclPow (L2dSpace d) polyGaussCore n s)
    (derPow (L2dSpace d) polyGaussCore M.innerHam n s)).re
  rw [sector_pair M n s s]
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
  simp only [Complex.re_sum]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => inner_self_nonneg (𝕜 := ℂ))


theorem outer_nonneg (x : hbosonicFockDom (L2dSpace d) polyGaussCore) :
    0 ≤ quadForm M.outerHam x :=
  QgOuterFock.dsOp_quadForm_nonneg _ (sector_nonneg M) x

theorem outer_positive_extension :
    ∃ (D : Submodule ℂ (hbosonicFock (L2dSpace d))) (A : D →ₗ[ℂ] hbosonicFock (L2dSpace d)),
      IsPositiveSelfAdjointExtension M.outerHam A :=
  friedrichs_extension_exists_of_complete_explicit
    ⟨_, M.outerHam, M.outer_symmetric, M.outer_nonneg⟩ (outerCore_dense d)

theorem outer_closure_nonneg (x : clDom M.outerHam) :
    0 ≤ quadForm (clExt M.outerHam (outerCore_dense d) M.outer_symmetric) x := by
  obtain ⟨D, A, hA⟩ := M.outer_positive_extension
  obtain ⟨hD, hval⟩ := positiveExtension_eq_closure_of_esa (outerCore_dense d) M.outer_symmetric
    M.outer_esa hA
  have hx : (x : hbosonicFock (L2dSpace d)) ∈ D := hD.symm ▸ x.property
  simpa only [quadForm, hval x hx x.property] using hA.2.2.1 ⟨x, hx⟩

/-- The closed nested Hamiltonian attains its lower bound zero in the unit outer vacuum. -/
theorem vacuum_ground :
    ∃ Ω : clDom M.outerHam, ‖(Ω : hbosonicFock (L2dSpace d))‖ = 1 ∧
      clExt M.outerHam (outerCore_dense d) M.outer_symmetric Ω = 0 ∧
      ∀ x, 0 ≤ quadForm (clExt M.outerHam (outerCore_dense d) M.outer_symmetric) x :=
  ⟨⟨vacuum d, coe_mem_clDom M.outerHam (vacuum d)⟩, vacuum_norm d,
    (clExt_extends M.outerHam (outerCore_dense d) M.outer_symmetric _).trans M.vacuum_energy_zero,
    M.outer_closure_nonneg⟩

end
end BookProof.Phi4.Model
```

---

### File: `BookProof/Phi4/ChapterScalarSirk.lean`

**Source:** `BookProof/Phi4/ChapterScalarSirk.lean` (complete file, 171 lines).

```lean
import BookProof.Phi4.ChapterScalarMehler
import BookProof.Sirk.ChapterSirkTrotterKato

/-!
# A full-action error estimate for the rank-one scalar Mehler window

The scalar reduced generator advances the inner vacuum by a phase. The full
operator also produces the second and fourth Hermites. Their orthogonal norm
controls the difference from the exact Stone evolution.
-/
namespace BookProof.Phi4

open MvPolynomial HermiteProductCore HermiteProductBasis HermiteCore
open EsaClosure FarisLavine YangMillsFriedrichs ChapterStoneResolvent ChapterSirkTrotterKato
open scoped InnerProductSpace

noncomputable section

/-- Undo the rank-one phase along the exact flow. Unitarity makes the norm of the
derivative equal to the norm of the full residual, at every time. -/
theorem rankOne_flow_error {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (T : UnboundedSelfAdjoint F) (x : T.domain) (E t : ℝ) :
    ‖T.stoneU t x - Complex.exp (-(Complex.I * E * t)) • (x : F)‖ ≤
      ‖T.op x - (E : ℂ) • (x : F)‖ * |t| := by
  let phase := fun s : ℝ => Complex.exp (-(Complex.I * E * s))
  let g := fun s : ℝ => phase s • T.stoneU (t-s) x
  let v := T.op x - (E : ℂ) • (x : F)
  have hd (s : ℝ) : HasDerivAt g ((phase s * Complex.I) • T.stoneU (t-s) v) s := by
    have hp : HasDerivAt (fun s : ℝ => -(Complex.I * E * (s : ℂ))) (-(Complex.I * E)) s := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I * E)).neg)
    have hu := (T.hasDerivAt_stoneU x (t-s)).comp_const_sub t s
    apply (hp.cexp.smul hu).congr_deriv
    simp only [phase, v, map_sub, map_smul, smul_sub, smul_smul, neg_smul, map_neg, neg_neg]
    module
  have hn (s : ℝ) : ‖(phase s * Complex.I) • T.stoneU (t-s) v‖ ≤ ‖v‖ := by
    rw [norm_smul, norm_mul, T.norm_stoneU_apply]
    simp [phase, Complex.norm_exp]
  have hm := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => hn s) Set.left_mem_uIcc Set.right_mem_uIcc
  have hgt : g t = phase t • (x : F) := by
    simp only [g, sub_self, T.stoneU_zero, ContinuousLinearMap.one_apply]
  have hg0 : g 0 = T.stoneU t x := by
    simp only [g, phase, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
      sub_zero, one_smul]
  rw [hgt, hg0, norm_sub_rev] at hm
  simpa only [sub_zero, Real.norm_eq_abs] using hm

/-- Integrate an affine envelope on the full-action residual of a reconstructed
Mehler-core orbit. The envelope may grow along the orbit, even for an exact reduced solve. -/
theorem Model.orbit_error {d k r : ℕ} (M : Model d k r) {T : UnboundedSelfAdjoint (L2d d)}
    (hext : IsSelfAdjointExtension M.innerHam T.op) (y : ℝ → polyGaussCore (d := d))
    (v : ℝ → L2d d) (hder : ∀ s, HasDerivAt (fun u => (y u : L2d d)) (v s) s)
    (a b t : ℝ) (ht : 0 ≤ t)
    (hbound : ∀ s ∈ Set.Ico 0 t, ‖Complex.I • M.innerHam (y s) + v s‖ ≤ a + b*s) :
    ‖(y t : L2d d) - T.stoneU t (y 0)‖ ≤ a*t + b*t^2/2 := by
  let g := fun s : ℝ => T.stoneU (t-s) (y s) - T.stoneU t (y 0)
  let w := fun s : ℝ => T.stoneU (t-s) (Complex.I • M.innerHam (y s) + v s)
  have hg (s : ℝ) : HasDerivAt g (w s) s := by
    obtain ⟨hmem, hval⟩ := hext.1 (y s)
    have h := hasDerivAt_stoneU_const_sub_apply T (hder s) hmem (t := t)
    rw [T.stoneU_op (t-s) (⟨y s, hmem⟩ : T.domain), hval] at h
    simpa only [g, w, map_add, map_smul] using h.sub_const (T.stoneU t (y 0))
  have hb (s : ℝ) : HasDerivAt (fun u : ℝ => a*u + b*u^2/2) (a+b*s) s := by
    convert ((hasDerivAt_id s).const_mul a).add
      ((((hasDerivAt_id s).pow 2).const_mul b).div_const 2) using 1 <;> simp <;> ring
  have hg0 : ‖g 0‖ ≤ a*0 + b*0^2/2 := by simp [g]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s _ => (hg s).continuousAt.continuousWithinAt)
    (fun s _ => (hg s).hasDerivWithinAt) hg0 hb
    (fun s hs => (T.norm_stoneU_apply _ _).le.trans (hbound s hs)) (Set.right_mem_Icc.mpr ht)
  simpa only [g, sub_self, T.stoneU_zero, ContinuousLinearMap.one_apply] using h

private def level (n : ℕ) : Fin 1 →₀ ℕ := Finsupp.single 0 n

private theorem hermite_levels :
    hermiteMv (level 2) = (X 0)^2 - 1 ∧
    hermiteMv (level 4) = (X 0)^4 - 6*(X 0)^2 + 3 := by
  have step (n : ℕ) := hermiteFactor_X_mul (d := 1) 0 n
  have h1 := step 0
  have h2 := step 1
  have h3 := step 2
  have h4 := step 3
  norm_num [hermiteFactor_zero, smul_eq_C_mul] at h1 h2 h3 h4
  have hc (n : ℕ) : (C (n : ℂ) : MvPolynomial (Fin 1) ℂ) = n := map_natCast _ _
  rw [show (C (2 : ℂ) : MvPolynomial (Fin 1) ℂ) = 2 from hc 2] at h3
  rw [show (C (3 : ℂ) : MvPolynomial (Fin 1) ℂ) = 3 from hc 3] at h4
  simp [hermiteMv, level]
  constructor
  · linear_combination -h2 - X 0 * h1
  · linear_combination -h4 - X 0*h3 - (X 0^2-3)*h2 - (X 0^3-5*X 0)*h1

private theorem residual_vector :
    unitCell.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ - (5/8 : ℂ) • pgLp 1 =
      (7/8 : ℂ) • pgLp (hermiteMv (level 2)) + (1/4 : ℂ) • pgLp (hermiteMv (level 4)) := by
  rw [unitCell_vacuum_column, hermite_levels.1, hermite_levels.2]
  change pgMap _ - _ • pgMap _ = _ • pgMap _ + _ • pgMap _
  rw [← map_smul, ← map_smul, ← map_smul, ← map_sub, ← map_add]
  congr 1
  simp [smul_eq_C_mul]
  ring

/-- The residual norm in the actual one-site L² inner product, relative to the
norm of the unnormalized Gaussian. -/
theorem unitCell_defect_norm_sq :
    ‖unitCell.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ - (5/8 : ℂ) • pgLp 1‖^2 =
      (97/32 : ℝ) * ‖pgLp (d := 1) 1‖^2 := by
  let ψ (n : ℕ) : L2d 1 := pgLp (hermiteMv (level n))
  have hi (m n : ℕ) : inner ℂ (ψ m) (ψ n) = (hermiteInner m n : ℂ) := by
    rw [inner_pgLp_hermiteMv]
    simp [level]
  have hz : pgLp (d := 1) 1 = ψ 0 := by simp [ψ, level, hermiteMv_zero]
  rw [residual_vector, hz]
  change ‖(7/8 : ℂ) • ψ 2 + (1/4 : ℂ) • ψ 4‖^2 = (97/32 : ℝ) * ‖ψ 0‖^2
  let y := (7/8 : ℂ) • ψ 2 + (1/4 : ℂ) • ψ 4
  change ‖y‖^2 = _
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) y, ← inner_self_eq_norm_sq (𝕜 := ℂ) (ψ 0)]
  dsimp only [y]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hi]
  simp only [map_div₀, map_ofNat]
  norm_num [hermiteInner_eq, Nat.factorial, Complex.mul_re]
  ring

/-- The exact one-column Hashimoto phase on the vacuum, compared with the full
unbounded evolution. Squaring avoids a square-root normalization on the Gaussian. -/
theorem unitCell_rankOne_error {T : UnboundedSelfAdjoint (L2d 1)}
    (hext : IsSelfAdjointExtension unitCell.innerHam T.op) (t : ℝ) :
    ‖T.stoneU t (pgLp 1) - Complex.exp (-(Complex.I * (5/8) * t)) • pgLp 1‖^2 ≤
      (97/32 : ℝ) * t^2 * ‖pgLp (d := 1) 1‖^2 := by
  let seed : polyGaussCore (d := 1) := ⟨pgLp 1, pgLp_mem_core 1⟩
  obtain ⟨hmem, hval⟩ := hext.1 seed
  have h := rankOne_flow_error T ⟨seed, hmem⟩ (5/8) t
  rw [hval] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  change (‖T.stoneU t (pgLp 1) - _ • pgLp 1‖)^2 ≤
    (‖unitCell.innerHam seed - _ • pgLp 1‖ * |t|)^2 at hs
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hs
  rw [mul_pow, sq_abs, unitCell_defect_norm_sq] at hs
  linarith

/-- Loss of return probability is bounded by squared distance from any
equal-norm reference state on the same ray. The inequality is homogeneous. -/
private theorem overlap_loss {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (x y : F) (hy : ‖y‖ = ‖x‖) :
    ‖x‖^4 - ‖inner ℂ x y‖^2 ≤ ‖x‖^2 * ‖x-y‖^2 := by
  rw [norm_sub_sq (𝕜 := ℂ), hy]
  have hr := Complex.re_le_norm (inner ℂ x y)
  change _ ≤ ‖x‖^2 * (‖x‖^2 - 2*(inner ℂ x y).re + ‖x‖^2)
  nlinarith [sq_nonneg (‖x‖^2 - ‖inner ℂ x y‖),
    mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.mpr hr)]

/-- For the one-site Gaussian seed the normalized return probability loses at most
(97/32)t². Both sides are multiplied by the fourth power of the Gaussian norm. -/
theorem unitCell_return_probability {T : UnboundedSelfAdjoint (L2d 1)}
    (hext : IsSelfAdjointExtension unitCell.innerHam T.op) (t : ℝ) :
    (1 - (97/32 : ℝ) * t^2) * ‖pgLp (d := 1) 1‖^4 ≤
      ‖inner ℂ (pgLp (d := 1) 1) (T.stoneU t (pgLp 1))‖^2 := by
  let x := pgLp (d := 1) 1
  let c := Complex.exp (-(Complex.I * (5/8) * t))
  have hc : ‖c‖ = 1 := by simp [c, Complex.norm_exp]
  have hn : ‖c • x‖ = ‖x‖ := by rw [norm_smul, hc, one_mul]
  have hy := T.norm_stoneU_apply t x
  have loss := overlap_loss (c • x) (T.stoneU t x) (hy.trans hn.symm)
  rw [hn, inner_smul_left, norm_mul, Complex.norm_conj, hc, one_mul, norm_sub_rev] at loss
  have err := unitCell_rankOne_error hext t
  change ‖T.stoneU t x - c • x‖^2 ≤ (97/32 : ℝ) * t^2 * ‖x‖^2 at err
  change (1 - (97/32 : ℝ) * t^2) * ‖x‖^4 ≤ ‖inner ℂ x (T.stoneU t x)‖^2
  nlinarith [mul_le_mul_of_nonneg_left err (sq_nonneg ‖x‖)]


end
end BookProof.Phi4
```

---

### File: `BookProof/Phi4/ChapterScalarTwoSite.lean`

**Source:** `BookProof/Phi4/ChapterScalarTwoSite.lean` (complete file, 350 lines).

```lean
import BookProof.Phi4.ChapterScalarMehler

/-!
# The periodic two-site scalar operator in uniform and staggered modes

The `2 x 1 x 1` periodic grid has two oriented links along its active axis and no
link along the two singleton axes. Rotating the site coordinates,

`u = (x₀ + x₁)/√2`,  `w = (x₀ − x₁)/√2`,

turns the link into `2 w²/a²` and the two local walls into the mixed quartic
`u⁴/8 + 3u²w²/4 + w⁴/8 − …`. This chapter proves the rotation on every polynomial,
identifies the full inner Hamiltonian with the mode operator, and evaluates its
three exact fixture columns in the unnormalized product Hermites.
-/
namespace BookProof.Phi4

open MvPolynomial BookProof.YangMillsHermite BookProof.HermiteProductCore

noncomputable section

/-- The normalization of the orthogonal two-site mode change. -/
def rot : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem rot_sq : rot * rot = (1 / 2 : ℂ) := by
  rw [rot, ← mul_inv]
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [h]
  norm_num

/-- Uniform and staggered coordinates `u = (x₀+x₁)/√2`, `w = (x₀−x₁)/√2`. -/
def fromModes : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.aeval ![C rot * (X 0 + X 1), C rot * (X 0 - X 1)]

@[simp] theorem fromModes_X_zero :
    fromModes (X 0) = C rot * (X 0 + X 1 : MvPolynomial (Fin 2) ℂ) := by
  simp [fromModes]

@[simp] theorem fromModes_X_one :
    fromModes (X 1) = C rot * (X 0 - X 1 : MvPolynomial (Fin 2) ℂ) := by
  simp [fromModes]

@[simp] theorem fromModes_C (c : ℂ) : fromModes (C c) = (C c : MvPolynomial (Fin 2) ℂ) := by
  simp [fromModes]

theorem fromModes_deriv_zero (p : MvPolynomial (Fin 2) ℂ) :
    pderiv 0 (fromModes p) = fromModes (rot • (pderiv 0 p + pderiv 1 p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    rw [← map_add]
    congr 1
    module
  | mul_X p n hp =>
    fin_cases n
    · simp [Fin.zero_eta, fromModes_X_zero, map_mul, pderiv_mul, pderiv_X,
        pderiv_C, map_add, map_sub, map_smul, smul_eq_C_mul, hp]
      ring_nf
    · simp [Fin.mk_one, fromModes_X_one, map_mul, pderiv_mul, pderiv_X,
        pderiv_C, map_add, map_sub, map_smul, smul_eq_C_mul, hp]
      ring_nf

theorem fromModes_deriv_one (p : MvPolynomial (Fin 2) ℂ) :
    pderiv 1 (fromModes p) = fromModes (rot • (pderiv 0 p - pderiv 1 p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    rw [← map_add]
    congr 1
    module
  | mul_X p n hp =>
    fin_cases n
    · simp [Fin.zero_eta, fromModes_X_zero, map_mul, pderiv_mul, pderiv_X,
        pderiv_C, map_add, map_sub, map_smul, smul_eq_C_mul, hp]
      ring_nf
    · simp [Fin.mk_one, fromModes_X_one, map_mul, pderiv_mul, pderiv_X,
        pderiv_C, map_add, map_sub, map_smul, smul_eq_C_mul, hp]
      ring_nf

theorem fromModes_mode_u :
    fromModes (rot • (X 0 + X 1)) = (X 0 : MvPolynomial (Fin 2) ℂ) := by
  rw [map_smul, map_add, fromModes_X_zero, fromModes_X_one, smul_eq_C_mul]
  apply MvPolynomial.funext
  intro x
  simp
  linear_combination (2 * x 0) * rot_sq

theorem fromModes_mode_w :
    fromModes (rot • (X 0 - X 1)) = (X 1 : MvPolynomial (Fin 2) ℂ) := by
  rw [map_smul, map_sub, fromModes_X_zero, fromModes_X_one, smul_eq_C_mul]
  apply MvPolynomial.funext
  intro x
  simp
  linear_combination (2 * x 1) * rot_sq

theorem mul_fromModes_zero (p : MvPolynomial (Fin 2) ℂ) :
    (X 0 : MvPolynomial (Fin 2) ℂ) * fromModes p =
      fromModes (rot • (X 0 + X 1) * p) := by
  nth_rewrite 1 [← fromModes_mode_u]
  rw [← map_mul]

theorem mul_fromModes_one (p : MvPolynomial (Fin 2) ℂ) :
    (X 1 : MvPolynomial (Fin 2) ℂ) * fromModes p =
      fromModes (rot • (X 0 - X 1) * p) := by
  nth_rewrite 1 [← fromModes_mode_w]
  rw [← map_mul]

theorem fromModes_derOp_zero (p : MvPolynomial (Fin 2) ℂ) :
    derOp (0 : Fin 2) (fromModes p) =
      fromModes (rot • (derOp (0 : Fin 2) p + derOp (1 : Fin 2) p)) := by
  rw [derOp_apply, fromModes_deriv_zero, mul_fromModes_zero]
  conv_lhs => rw [← map_smul, ← map_sub]
  congr 1
  simp only [derOp_apply, smul_eq_C_mul, mul_add, mul_sub]
  ring

theorem fromModes_derOp_one (p : MvPolynomial (Fin 2) ℂ) :
    derOp (1 : Fin 2) (fromModes p) =
      fromModes (rot • (derOp (0 : Fin 2) p - derOp (1 : Fin 2) p)) := by
  rw [derOp_apply, fromModes_deriv_one, mul_fromModes_one]
  conv_lhs => rw [← map_smul, ← map_sub]
  congr 1
  simp only [derOp_apply, smul_eq_C_mul, mul_add, mul_sub]
  ring

theorem fromModes_momOp_zero (p : MvPolynomial (Fin 2) ℂ) :
    momOp (0 : Fin 2) (fromModes p) =
      fromModes (rot • (momOp (0 : Fin 2) p + momOp (1 : Fin 2) p)) := by
  rw [momOp, LinearMap.smul_apply, fromModes_derOp_zero]
  conv_rhs =>
    simp only [momOp, LinearMap.smul_apply]
    rw [
      show rot • ((-Complex.I) • (derOp (0 : Fin 2) p) +
          (-Complex.I) • (derOp (1 : Fin 2) p)) =
        (-Complex.I) • (rot • (derOp (0 : Fin 2) p + derOp (1 : Fin 2) p)) by module]
  conv_rhs => rw [map_smul]

theorem fromModes_momOp_one (p : MvPolynomial (Fin 2) ℂ) :
    momOp (1 : Fin 2) (fromModes p) =
      fromModes (rot • (momOp (0 : Fin 2) p - momOp (1 : Fin 2) p)) := by
  rw [momOp, LinearMap.smul_apply, fromModes_derOp_one]
  conv_rhs =>
    simp only [momOp, LinearMap.smul_apply]
    rw [
      show rot • ((-Complex.I) • (derOp (0 : Fin 2) p) -
          (-Complex.I) • (derOp (1 : Fin 2) p)) =
        (-Complex.I) • (rot • (derOp (0 : Fin 2) p - derOp (1 : Fin 2) p)) by module]
  conv_rhs => rw [map_smul]

/-- The kinetic energy is invariant under the orthogonal mode change. -/
theorem fromModes_kinetic (p : MvPolynomial (Fin 2) ℂ) :
    (∑ i : Fin 2, momOp i (momOp i (fromModes p))) =
      fromModes (∑ i : Fin 2, momOp i (momOp i p)) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  set q0 := rot • (momOp (0 : Fin 2) p + momOp (1 : Fin 2) p) with hq0
  set q1 := rot • (momOp (0 : Fin 2) p - momOp (1 : Fin 2) p) with hq1
  have h0 : momOp (0 : Fin 2) (fromModes p) = fromModes q0 := fromModes_momOp_zero p
  have h1 : momOp (1 : Fin 2) (fromModes p) = fromModes q1 := fromModes_momOp_one p
  rw [h0, h1, fromModes_momOp_zero q0, fromModes_momOp_one q1, ← map_add]
  congr 1
  simp only [q0, q1, map_add, map_sub, map_smul, smul_sub, smul_add, smul_smul]
  rw [rot_sq]
  module

/-- The actual `2 x 1 x 1` periodic site model at unit side lengths. -/
def twoSite (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a) :
    Model 2 2 8 :=
  siteModel (periodicNext 1 0 0) ⟨lam, hlam, v, hv⟩ a ha

@[simp] theorem periodicNext_00 :
    periodicNext 1 0 0 (0 : Fin 2) (0 : Fin 3) = 1 := by decide

@[simp] theorem periodicNext_01 :
    periodicNext 1 0 0 (0 : Fin 2) (1 : Fin 3) = 0 := by decide

@[simp] theorem periodicNext_02 :
    periodicNext 1 0 0 (0 : Fin 2) (2 : Fin 3) = 0 := by decide

@[simp] theorem periodicNext_10 :
    periodicNext 1 0 0 (1 : Fin 2) (0 : Fin 3) = 0 := by decide

@[simp] theorem periodicNext_11 :
    periodicNext 1 0 0 (1 : Fin 2) (1 : Fin 3) = 1 := by decide

@[simp] theorem periodicNext_12 :
    periodicNext 1 0 0 (1 : Fin 2) (2 : Fin 3) = 1 := by decide

@[simp] theorem twoSite_momentum (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v)
    (ha : 0 < a) : (twoSite lam v a hlam hv ha).momentum = id := rfl

/-- The site form sum: two walls and the two oriented active links. -/
theorem twoSite_forms (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a)
    (p : MvPolynomial (Fin 2) ℂ) :
    ∑ j, (twoSite lam v a hlam hv ha).form j *
      ((twoSite lam v a hlam hv ha).form j * p) =
      ((lam / (2 * a^3) : ℝ) : ℂ) •
        ((X 0 ^ 2 - C ((a^3 * v^2 : ℝ) : ℂ)) *
          ((X 0 ^ 2 - C ((a^3 * v^2 : ℝ) : ℂ)) * p) +
         (X 1 ^ 2 - C ((a^3 * v^2 : ℝ) : ℂ)) *
          ((X 1 ^ 2 - C ((a^3 * v^2 : ℝ) : ℂ)) * p)) +
      ((2 / a^2 : ℝ) : ℂ) • ((X 0 - X 1) * ((X 0 - X 1) * p)) := by
  conv_lhs =>
    rw [← (finProdFinEquiv (m := 2) (n := 4)).sum_comp]
    rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_two]
  simp [Fin.sum_univ_succ, twoSite, siteModel, siteForm,
    Equiv.symm_apply_apply, wall, smul_eq_C_mul]
  ring_nf
  simp only [← map_pow, ← Complex.ofReal_pow]
  rw [Real.sq_sqrt (by positivity)]
  push_cast
  apply MvPolynomial.funext
  intro x
  simp
  field_simp
  ring

/-- The site potential after the mode rotation, including the mixed vertex. -/
def modePotential (lam v a : ℝ) (p : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  ((lam / (4 * a ^ 3) : ℝ) : ℂ) •
    ((X 0 ^ 2 + X 1 ^ 2 - C ((2 * a ^ 3 * v ^ 2 : ℝ) : ℂ)) *
      ((X 0 ^ 2 + X 1 ^ 2 - C ((2 * a ^ 3 * v ^ 2 : ℝ) : ℂ)) * p))
    + ((lam / a ^ 3 : ℝ) : ℂ) • ((X 0 * X 1) * ((X 0 * X 1) * p))
    + ((4 / a ^ 2 : ℝ) : ℂ) • (X 1 * (X 1 * p))

/-- Under the rotation the site form sum is the mode potential. -/
theorem twoSite_forms_modes (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a)
    (p : MvPolynomial (Fin 2) ℂ) :
    ∑ j, (twoSite lam v a hlam hv ha).form j *
      ((twoSite lam v a hlam hv ha).form j * fromModes p) =
      fromModes (modePotential lam v a p) := by
  rw [twoSite_forms]
  conv_rhs =>
    simp only [modePotential, map_add, map_mul, map_sub, map_pow, map_smul,
      fromModes_X_zero, fromModes_X_one, fromModes_C, smul_eq_C_mul]
  apply MvPolynomial.funext
  intro x
  simp
  ring_nf
  have hrot2 : rot ^ 2 = (1 / 2 : ℂ) := by rw [sq, rot_sq]
  have hrot4 : rot ^ 4 = (1 / 4 : ℂ) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hrot2]
    norm_num
  rw [hrot2, hrot4]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [ha']
  ring

/-- The full mode action: half the kinetic sum plus the mode potential. -/
def modeHam (lam v a : ℝ) (p : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  ((1 / 2 : ℝ) : ℂ) •
    ((∑ i : Fin 2, momOp i (momOp i p)) + modePotential lam v a p)

/-- The full `2 x 1 x 1` inner Hamiltonian on the rotated core. -/
theorem twoSite_action (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a)
    (p : MvPolynomial (Fin 2) ℂ) :
    ((1 / 2 : ℝ) : ℂ) • ((∑ i : Fin 2, momOp i (momOp i (fromModes p))) +
      (∑ j, (twoSite lam v a hlam hv ha).form j *
        ((twoSite lam v a hlam hv ha).form j * fromModes p))) =
      fromModes (modeHam lam v a p) := by
  rw [fromModes_kinetic, twoSite_forms_modes, ← map_add, ← map_smul]
  rfl

/-- Binding of the two-site calculation to the actual site operator. -/
theorem twoSite_innerHam (lam v a : ℝ) (hlam : 0 < lam) (hv : 0 < v) (ha : 0 < a)
    (p : MvPolynomial (Fin 2) ℂ) :
    (twoSite lam v a hlam hv ha).innerHam
        ⟨pgLp (fromModes p), pgLp_mem_core (fromModes p)⟩ =
      pgLp (fromModes (modeHam lam v a p)) := by
  rw [Model.innerHam_pgLp]
  simp only [twoSite_momentum, id_eq]
  rw [twoSite_action]

/-- Unnormalized probabilists' Hermites `He₀ … He₆` in mode `i`. -/
def modeHe : ℕ → Fin 2 → MvPolynomial (Fin 2) ℂ
  | 0, _ => 1
  | 1, i => X i
  | 2, i => X i ^ 2 - 1
  | 3, i => X i ^ 3 - 3 * X i
  | 4, i => X i ^ 4 - 6 * X i ^ 2 + 3
  | 5, i => X i ^ 5 - 10 * X i ^ 3 + 15 * X i
  | 6, i => X i ^ 6 - 15 * X i ^ 4 + 45 * X i ^ 2 - 15
  | _, _ => 0

/-- Fixture column `(0,0)`: the Gaussian seed. -/
theorem twoSite_column_00 :
    modeHam 1 1 1 (modeHe 0 0 * modeHe 0 1) =
      (13/4 : ℂ) • (modeHe 0 0 * modeHe 0 1) +
      (23/8 : ℂ) • (modeHe 0 0 * modeHe 2 1) +
      (1/8 : ℂ) • (modeHe 0 0 * modeHe 4 1) +
      (7/8 : ℂ) • (modeHe 2 0 * modeHe 0 1) +
      (3/4 : ℂ) • (modeHe 2 0 * modeHe 2 1) +
      (1/8 : ℂ) • (modeHe 4 0 * modeHe 0 1) := by
  simp [modeHam, modePotential, modeHe, momOp_apply, pderiv_C,
    Derivation.map_natCast, Complex.I_sq]
  apply MvPolynomial.funext
  intro x
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Fixture column `(2,0)`: the uniform-mode excitation. -/
theorem twoSite_column_20 :
    modeHam 1 1 1 (modeHe 2 0 * modeHe 0 1) =
      (7/4 : ℂ) • (modeHe 0 0 * modeHe 0 1) +
      (3/2 : ℂ) • (modeHe 0 0 * modeHe 2 1) +
      (37/4 : ℂ) • (modeHe 2 0 * modeHe 0 1) +
      (47/8 : ℂ) • (modeHe 2 0 * modeHe 2 1) +
      (1/8 : ℂ) • (modeHe 2 0 * modeHe 4 1) +
      (15/8 : ℂ) • (modeHe 4 0 * modeHe 0 1) +
      (3/4 : ℂ) • (modeHe 4 0 * modeHe 2 1) +
      (1/8 : ℂ) • (modeHe 6 0 * modeHe 0 1) := by
  simp [modeHam, modePotential, modeHe, momOp_apply, pderiv_C,
    Derivation.map_natCast, Complex.I_sq]
  rw [show (2 : MvPolynomial (Fin 2) ℂ) = C 2 from rfl, pderiv_C]
  apply MvPolynomial.funext
  intro x
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Fixture column `(0,2)`: the staggered-mode excitation. -/
theorem twoSite_column_02 :
    modeHam 1 1 1 (modeHe 0 0 * modeHe 2 1) =
      (23/4 : ℂ) • (modeHe 0 0 * modeHe 0 1) +
      (69/4 : ℂ) • (modeHe 0 0 * modeHe 2 1) +
      (31/8 : ℂ) • (modeHe 0 0 * modeHe 4 1) +
      (1/8 : ℂ) • (modeHe 0 0 * modeHe 6 1) +
      (3/2 : ℂ) • (modeHe 2 0 * modeHe 0 1) +
      (31/8 : ℂ) • (modeHe 2 0 * modeHe 2 1) +
      (3/4 : ℂ) • (modeHe 2 0 * modeHe 4 1) +
      (1/8 : ℂ) • (modeHe 4 0 * modeHe 2 1) := by
  simp [modeHam, modePotential, modeHe, momOp_apply, pderiv_C,
    Derivation.map_natCast, Complex.I_sq]
  rw [show (2 : MvPolynomial (Fin 2) ℂ) = C 2 from rfl, pderiv_C]
  apply MvPolynomial.funext
  intro x
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

end
end BookProof.Phi4
```

---

### File: `BookProof/Phi4/ChapterScalarRankTwo.lean`

**Source:** `BookProof/Phi4/ChapterScalarRankTwo.lean` (complete file, 286 lines).

```lean
import BookProof.Phi4.ChapterScalarTwoSite
import BookProof.ChapterQuadraticRotationEsa

/-!
# An exact two-site rank-two Hashimoto calculation

The three columns are in unnormalized product Hermites. Rational complex numbers
keep every finite identity decidable in the kernel. The Hermite Gram matrix enters
both the dual used in the compression and the norm of the discarded action.
-/
namespace BookProof.Phi4.RankTwo

abbrev QI := QuadraticAlgebra ℚ (-1) 0
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) QI
private def q (x : ℚ) : QI := ⟨x, 0⟩
private def ii : QI := ⟨0, 1⟩

/-- Retained rows first, then all other modes reached by one full action. -/
def modes : Fin 10 → ℕ × ℕ :=
  ![(0,0), (2,0), (0,2), (0,4), (0,6), (2,2), (2,4), (4,0), (4,2), (6,0)]

def fullColumns : Mat 10 3 := !![
    q (13/4), q (7/4), q (23/4);
    q (7/8), q (37/4), q (3/2);
    q (23/8), q (3/2), q (69/4);
    q (1/8), 0, q (31/8);
    0, 0, q (1/8);
    q (3/4), q (47/8), q (31/8);
    0, q (1/8), q (3/4);
    q (1/8), q (15/8), 0;
    0, q (3/4), q (1/8);
    0, q (1/8), 0]

private def retained (i : Fin 3) : Fin 10 := i.castLE (by decide)

noncomputable def modeTerm (i : Fin 10) := modeHe (modes i).1 0 * modeHe (modes i).2 1

/-- All ten rows are the full polynomial action on each retained mode. -/
theorem fullColumns_action (j : Fin 3) :
    modeHam 1 1 1 (modeTerm (retained j)) =
      ∑ i, ((fullColumns i j).re : ℂ) • modeTerm i := by
  fin_cases j
  · change modeHam 1 1 1 (modeHe 0 0 * modeHe 0 1) = _
    rw [twoSite_column_00]
    norm_num [Fin.sum_univ_succ, modeTerm, modes, fullColumns, q]
    abel
  · change modeHam 1 1 1 (modeHe 2 0 * modeHe 0 1) = _
    rw [twoSite_column_20]
    norm_num [Fin.sum_univ_succ, modeTerm, modes, fullColumns, q]
    abel
  · change modeHam 1 1 1 (modeHe 0 0 * modeHe 2 1) = _
    rw [twoSite_column_02]
    norm_num [Fin.sum_univ_succ, modeTerm, modes, fullColumns, q]
    abel

/-- The same coefficient array applied inside the two-site operator on the site Gaussian core. -/
theorem site_columns (j : Fin 3) :
    (twoSite 1 1 1 (by norm_num) (by norm_num) (by norm_num)).innerHam
      ⟨HermiteProductCore.pgLp (fromModes (modeTerm (retained j))),
        HermiteProductCore.pgLp_mem_core _⟩ =
      HermiteProductCore.pgLp (fromModes (∑ i, ((fullColumns i j).re : ℂ) • modeTerm i)) := by
  rw [twoSite_innerHam, fullColumns_action]

def hWin : Mat 3 3 := fullColumns.submatrix retained id

def metric : Mat 3 3 := Matrix.diagonal ![1, 2, 2]

def fullMetric : Mat 10 10 := Matrix.diagonal fun i =>
  q ((modes i).1.factorial * (modes i).2.factorial)

def inclusion : Mat 10 3 := fun i j => if i = retained j then 1 else 0

def shifted (γ : ℕ) : Mat 3 3 := γ • (1 : Mat 3 3) + ii • hWin

def basis : Mat 3 2 := !![
    1, ⟨37913768/237801325, -16436754/237801325⟩;
    0, ⟨-102704/9512053, 869/9512053⟩;
    0, ⟨-6355248/237801325, 895469/237801325⟩]

def generator : Mat 2 2 := !![
    ⟨-1975087311464981/387678327400657, -7803020777077170/387678327400657⟩, -1;
    ⟨-36582638530574935/3101426619205256, 39094647255223290/387678327400657⟩, 5]

private def res3 : Mat 3 3 := !![
    ⟨92129784/437912353, -64884570/437912353⟩,
    ⟨-13906464/437912353, 5240226/437912353⟩,
    ⟨-32208672/437912353, 15571010/437912353⟩;
    ⟨-6953232/437912353, 2620113/437912353⟩,
    ⟨15301428/437912353, -43357945/437912353⟩,
    ⟨469188/437912353, 2978483/437912353⟩;
    ⟨-16104336/437912353, 7785505/437912353⟩,
    ⟨469188/437912353, 2978483/437912353⟩,
    ⟨9938100/437912353, -26512025/437912353⟩]

def dual : Mat 2 3 := !![
    1, ⟨1027165/502353, -435020/502353⟩, ⟨895951/167451, -741260/502353⟩;
    0, ⟨-6419000/502353, -108625/1004706⟩, ⟨-5296040/167451, -4477345/1004706⟩]

private def gramInv : Mat 2 2 := !![
    q (9478442/502353), ⟨-47392210/502353, 4565765/111634⟩;
    ⟨-47392210/502353, -4565765/111634⟩, q (1189006625/2009412)]

def defectGram : Mat 2 2 := !![
    q (1227243135860099/387678327400657), ⟨-93714912/237801325, -55971003/475602650⟩;
    ⟨-93714912/237801325, 55971003/475602650⟩, q (53022439/237801325)]

def gram : Mat 2 2 := basis.conjTranspose * metric * basis

/-- The actual compressed bounded resolvent, using the physical left inverse of the basis. -/
def bounded : Mat 2 2 := dual * res3 * basis

theorem window_hermitian : hWin.conjTranspose * metric = metric * hWin := by decide +kernel

theorem shift_five_seed : (shifted 5).mulVec (fun i => basis i 1) = fun i => basis i 0 := by
  decide +kernel

theorem basis_second_column :
    (fun i => basis i 1) = ((shifted 5)⁻¹).mulVec (fun i => basis i 0) := by
  have h : IsUnit (shifted 5).det := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨-205184/237801325, -81248/237801325⟩, ?_⟩
    rw [Matrix.det_fin_three]
    decide +kernel
  rw [← shift_five_seed, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]

theorem shift_three_inverse : shifted 3 * res3 = 1 := by decide +kernel

theorem gram_inverse : gram * gramInv = 1 := by decide +kernel

theorem physical_dual : gramInv * basis.conjTranspose * metric = dual := by decide +kernel

theorem dual_basis : dual * basis = 1 := by decide +kernel

theorem compressed_inverse : bounded * (3 • (1 : Mat 2 2) - generator) = 1 := by
  decide +kernel

/-- The generator is obtained by inverting the compressed resolvent. -/
theorem hashimoto_generator :
    3 • (1 : Mat 2 2) - (gram⁻¹ * basis.conjTranspose * metric * (shifted 3)⁻¹ * basis)⁻¹ =
      generator := by
  rw [Matrix.inv_eq_right_inv gram_inverse, physical_dual,
    Matrix.inv_eq_right_inv shift_three_inverse, ← bounded,
    Matrix.inv_eq_right_inv compressed_inverse]
  abel

theorem differs_from_projected_h :
    generator ≠ (-ii) • (dual * hWin * basis) := by decide +kernel

def leak : Mat 3 2 := res3 * basis * (3 • (1 : Mat 2 2) - generator) - basis

/-- Dissipation of the reduced evolution in its own Gram metric. -/
theorem dissipation :
    generator.conjTranspose * gram + gram * generator =
      -(6 • (leak.conjTranspose * metric * leak)) := by decide +kernel

def defect : Mat 10 2 := ii • (inclusion * basis * generator) - fullColumns * basis

theorem full_defect_gram : defect.conjTranspose * fullMetric * defect = defectGram := by
  decide +kernel

/-- Squared Hilbert–Schmidt norm with the physical Gram matrices in both spaces. -/
theorem full_defect_hs_squared :
    Matrix.trace (gram⁻¹ * (defect.conjTranspose * fullMetric * defect)) =
      q (66577730826550897732871 / 259668494406269661228) := by
  rw [Matrix.inv_eq_right_inv gram_inverse, full_defect_gram]
  decide +kernel

/-- The discarded Hermite rows and the rational compression error inside the
window are orthogonal. Both are evaluated on the same two rational columns. -/
theorem defect_split :
    let inside := inclusion * inclusion.transpose * defect
    let tail := defect - inside
    let A := inside.conjTranspose * fullMetric * inside
    let B := tail.conjTranspose * fullMetric * tail
    A + B = defectGram ∧
      (A 0 0).re = 64208153658128/387678327400657 ∧ (B 0 0).re = 3 ∧
      (Matrix.trace (gramInv * A)).re = 608593260375654076576/194751370804702245921 ∧
      (Matrix.trace (gramInv * B)).re = 508924037/2009412 := by decide +kernel

private def normSq {n : ℕ} (W : Mat n n) (v : Fin n → QI) : ℚ :=
  (∑ i, star (v i) * (W.mulVec v i)).re

private def seed : Fin 2 → QI := ![1, 0]
private def speed := generator.mulVec seed
private def transverse : Fin 3 → QI :=
  let w := basis.mulVec speed
  ![0, w 1, w 2]

/-- In units of the Gaussian norm, these squared bounds control the short-time
integral of the full defect and the component orthogonal to the seed. -/
theorem orbit_rates :
    (defectGram 0 0).re ≤ (178/100 : ℚ)^2 ∧
    (Matrix.trace (gramInv * defectGram)).re ≤ (1602/100 : ℚ)^2 ∧
    normSq gram speed ≤ (529/100 : ℚ)^2 ∧
    normSq gram (generator.mulVec speed) ≤ (8851/100 : ℚ)^2 ∧
    (417/100 : ℚ)^2 ≤ normSq metric transverse := by decide +kernel

/-- The full seed variance uses all ten output rows; the shift is its mean 13/4. -/
theorem seed_variance :
    normSq fullMetric (fun i => fullColumns i 0 - q (13/4) * inclusion i 0) = 337/16 := by
  decide +kernel

open MvPolynomial HermiteProductCore HermiteProductBasis HermiteCore QuadraticRotation
noncomputable section

private def rotation : Matrix (Fin 2) (Fin 2) ℝ :=
  let a := (Real.sqrt 2)⁻¹
  !![a, a; a, -a]

private theorem orthogonal : rotation.transpose * rotation = 1 := by
  have h : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1/2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.mul_apply, Fin.sum_univ_two, h, Matrix.one_apply]

private theorem rotate_polynomial : fromModes = rotPoly rotation := by
  ext i
  fin_cases i <;>
    simp [rotPoly_X, rotation, rot, Fin.sum_univ_two, fromModes_X_zero, fromModes_X_one] <;> ring

theorem rotation_preserves_inner (p q : MvPolynomial (Fin 2) ℂ) :
    inner ℂ (pgLp (fromModes p)) (pgLp (fromModes q)) = inner ℂ (pgLp p) (pgLp q) := by
  rw [rotate_polynomial]
  exact inner_pgLp_rotPoly orthogonal p q

private theorem modeHe_factor (i : Fin 2) (n : ℕ) (hn : n ≤ 6) :
    modeHe n i = hermiteFactor i n := by
  have step (m : ℕ) (hm : m < 6) :
      modeHe (m+1) i = X i * modeHe m i - (m : ℂ) • modeHe (m-1) i := by
    interval_cases m <;> norm_num [modeHe, smul_eq_C_mul, map_ofNat] <;> ring
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact (hermiteFactor_zero i).symm
    | succ m =>
      rw [step m (by omega), ih m (by omega) (by omega), ih (m-1) (by omega) (by omega),
        hermiteFactor_X_mul]
      abel


private def exponent (a : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a.1, a.2]

private theorem productHe {a : ℕ × ℕ} (ha : a.1 ≤ 6 ∧ a.2 ≤ 6) :
    modeHe a.1 0 * modeHe a.2 1 = hermiteMv (exponent a) := by
  simp [hermiteMv, exponent, Fin.prod_univ_two, modeHe_factor _ _ ha.1,
    modeHe_factor _ _ ha.2]

theorem rotated_mode_inner (i j : Fin 10) :
    inner ℂ (pgLp (fromModes (modeHe (modes i).1 0 * modeHe (modes i).2 1)))
      (pgLp (fromModes (modeHe (modes j).1 0 * modeHe (modes j).2 1))) =
      ((fullMetric i j).re : ℂ) * ((Real.sqrt (2*Real.pi) : ℝ) : ℂ)^2 := by
  have hdeg : ∀ n, (modes n).1 ≤ 6 ∧ (modes n).2 ≤ 6 := by decide +kernel
  have hinj : Function.Injective modes := by decide +kernel
  rw [rotation_preserves_inner, productHe (hdeg i), productHe (hdeg j), inner_pgLp_hermiteMv]
  by_cases hij : i = j
  · subst j
    simp [fullMetric, q, exponent, Fin.prod_univ_two, hermiteInner_eq]
    ring
  · have hne : modes i ≠ modes j := fun h => hij (hinj h)
    rcases not_and_or.mp (fun h : (modes i).1 = (modes j).1 ∧ (modes i).2 = (modes j).2 =>
      hne (Prod.ext h.1 h.2)) with h | h <;>
      simp [fullMetric, hij, h, exponent, Fin.prod_univ_two, hermiteInner_eq]

/-- Reconstruct a physical site-space vector from any ten complex mode coefficients. -/
def synthesize (c : Fin 10 → ℂ) : L2d 2 :=
  ∑ i, c i • pgLp (fromModes (modeTerm i))

theorem synthesis_inner (a b : Fin 10 → ℂ) :
    inner ℂ (synthesize a) (synthesize b) =
      (∑ i, ∑ j, (starRingEnd ℂ) (a i) * ((fullMetric i j).re : ℂ) * b j) *
        ((Real.sqrt (2*Real.pi) : ℝ) : ℂ)^2 := by
  simp only [synthesize, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    modeTerm, rotated_mode_inner, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end

end BookProof.Phi4.RankTwo
```

---

### File: `BookProof/Phi4/ChapterScalarRankTwoOrbit.lean`

**Source:** `BookProof/Phi4/ChapterScalarRankTwoOrbit.lean` (complete file, 69 lines).

```lean
import BookProof.Phi4.ChapterScalarRankTwo

/-!
# The full-action residual of the rank-two two-site seed

The exact fixture column and the site operator identify the seed residual with the
ten-mode coefficient vector `fullColumns · 0 - (13/4) e₀`. This is the first
transport step from the rational compressed matrix to the full Stone orbit; the
matrix-exponential norm bound and the return interval are not yet included.
-/
namespace BookProof.Phi4.RankTwoOrbit

open BookProof.Phi4 BookProof.Phi4.RankTwo HermiteProductCore

noncomputable section

/-- The rank-two seed is the mode vacuum. -/
def seed : L2d 2 := pgLp (fromModes (modeTerm 0))

/-- The fixture's Gaussian diagonal energy. -/
def energy : ℂ := 13 / 4

/-- Residual coefficients in the ten-row exact column. -/
def residualCoeff (i : Fin 10) : ℂ :=
  ((fullColumns i 0).re : ℂ) - energy * (if i = 0 then 1 else 0)

/-- The synthesized ten-mode vector is the Gaussian image of the mode polynomial. -/
theorem synthesize_eq (c : Fin 10 → ℂ) :
    synthesize c = pgLp (fromModes (∑ i, c i • modeTerm i)) := by
  rw [show synthesize c = ∑ i, c i • pgLp (fromModes (modeTerm i)) from rfl]
  rw [show (∑ i, c i • pgLp (fromModes (modeTerm i))) =
      pgMap (d := 2) (∑ i, c i • fromModes (modeTerm i)) by
    rw [map_sum]
    simp only [map_smul, pgMap_apply]]
  simp only [pgMap_apply]
  congr 1
  rw [Finset.sum_congr rfl (fun i _ => (map_smul fromModes (c i) (modeTerm i)).symm)]
  rw [← map_sum]

/-- The full two-site Hamiltonian on the seed minus its Gaussian phase is the exact
ten-mode residual. -/
theorem twoSite_residual :
    (twoSite 1 1 1 (by norm_num) (by norm_num) (by norm_num)).innerHam
        ⟨pgLp (fromModes (modeHe 0 0 * modeHe 0 1)), pgLp_mem_core _⟩ -
      energy • pgLp (fromModes (modeHe 0 0 * modeHe 0 1)) =
    pgLp (fromModes (∑ i, residualCoeff i • modeTerm i)) := by
  have hfull := fullColumns_action 0
  have hsite := site_columns 0
  change modeHam 1 1 1 (modeHe 0 0 * modeHe 0 1) =
    ∑ i, ((fullColumns i 0).re : ℂ) • modeTerm i at hfull
  change (twoSite 1 1 1 (by norm_num) (by norm_num) (by norm_num)).innerHam
      ⟨pgLp (fromModes (modeHe 0 0 * modeHe 0 1)), pgLp_mem_core _⟩ =
    pgLp (fromModes (∑ i, ((fullColumns i 0).re : ℂ) • modeTerm i)) at hsite
  have hres : (∑ i, residualCoeff i • modeTerm i) =
      (∑ i, ((fullColumns i 0).re : ℂ) • modeTerm i) - energy • modeTerm 0 := by
    simp only [residualCoeff, sub_smul, Finset.sum_sub_distrib]
    congr 1
    simp [Finset.sum_ite_eq']
  rw [hsite]
  change pgMap (fromModes (∑ i, ((fullColumns i 0).re : ℂ) • modeTerm i)) -
      energy • pgMap (fromModes (modeHe 0 0 * modeHe 0 1)) =
    pgMap (fromModes (∑ i, residualCoeff i • modeTerm i))
  rw [← map_smul (pgMap (d := 2)) energy, ← map_sub]
  rw [← map_smul (fromModes) energy, ← map_sub]
  rw [hres]
  rfl

end
end BookProof.Phi4.RankTwoOrbit
```

---

### Excerpt: `CURRENT_WORK_ORDER.md` — λφ⁴ routing row

**Source:** `CURRENT_WORK_ORDER.md`, line 60 (the complete “Real scalar λφ⁴” table row).

```markdown
| **Real scalar λφ⁴** | [Scalar formalization plan][phi4-plan], “Next proofs”, item 1. The Gaussian column is certified by `unitJet_vacuum_column` and `jet_variance_weights`; next is the residual norm and rational orbit of the continuous-coordinate `jetModel`. The periodic two-site interval in the 2026-11-21 entry is a lattice comparison. | Initial scalar work order | — |
```

---

### Excerpt: `CONSOLIDATED_PLAN.md` — 2026-11-21 scalar λφ⁴ entry

**Source:** `CONSOLIDATED_PLAN.md`, lines 26908–26949 (the “State of the project —
2026-11-21: scalar λφ⁴ on the nested Mehler core” section, to end of file).

```markdown
## State of the project — 2026-11-21: scalar λφ⁴ on the nested Mehler core

The scalar work order starts with the continuous-coordinate independent-jet operator. The
one-particle operator contains the entire double-well interaction, including its
constant. The outer Hamiltonian is the creation-left, annihilation-right enclosure of
that operator. Each outer excitation carries all the inner coordinates. The scalar and three independent
jets are real variables. Hermite indices label functions of those variables. The periodic
site model uses spatial finite differences and supplies a separate lattice comparison.
[Current scalar work order](PHI4_FORMALIZATION_PLAN.md)

- **U — operator and vacuum.** The inner operator has a positive self-adjoint closure.
  The completed symmetric outer sectors carry its second quantization. Their dense
  finite-particle core gives the outer Stone flow. The outer closure is nonnegative
  and the unit outer vacuum attains zero energy. Ground-state uniqueness and a
  positive gap require further spectral estimates.
  [Inner operator](BookProof/Phi4/ChapterScalarMehler.lean) ·
  [Outer dynamics](BookProof/Phi4/ChapterScalarOuter.lean) ·
  [Ground-state proof](BookProof/Phi4/ChapterScalarEnergy.lean)
- **U — finite Mehler windows.** The inverses of the actual compressed Hamiltonians
  converge strongly at nonzero imaginary shifts. Their flows converge on each state
  uniformly on bounded time intervals. The one-site rank-one return theorem bounds
  the normalized Gaussian return below by 1 − (97/32)t² at unit parameters.
  [Window theorem](BookProof/Phi4/ChapterScalarWindows.lean) ·
  [One-site full-action estimate](BookProof/Phi4/ChapterScalarSirk.lean)
- **U — two-site finite identities.** Lean identifies the three input columns with the
  full rotated Hamiltonian including all ten output modes, checks the Hermite metric,
  and computes the rank-two Hashimoto generator and its full defect. The squared
  defect on the initial column and the Hilbert–Schmidt bound control different terms
  in the time integral. Lean proves its affine residual estimate for differentiable
  core orbits. The analytic derivation gives the normalized return interval
  [0.99789375, 0.999775] at t = 0.01. The time-dependent inference remains to be
  packaged in Lean. Rust has a three-mode compressed exponential test for this lattice
  example. A full-action-enclosed rank-two Rust trajectory remains open.
  [Two-site action](BookProof/Phi4/ChapterScalarTwoSite.lean) ·
  [Rank-two proof](BookProof/Phi4/ChapterScalarRankTwo.lean) ·
  [Derivation and replay](../unfer/docs/PHI4_ANALYTIC_PLAN.md)

**Specialist handoff.** Use the full Gaussian column of `jetModel` to prove the unit-width,
unit-parameter mean 17/8 and variance 145/32. Bind the rational orbit to this operator
and compare the error with the change under a coupling variation,
increasing the occupation cutoff independently of the rational Krylov rank. The current
bounds address one fixed scalar model and give no uniform-in-rank rate or field limit.
```

---

---

# Part II — external λφ⁴ material

## Scope of the external material

This part adds the analytic, numerical and symbolic material that surrounds the Lean
development. It is not a dump of the three repositories. The selection rule is:

- Include in full the two unfer λφ⁴ plans, the Cadabra2 script, its exact JSON fixture,
  the Rust periodic-comparison builder, and the ordered-action module it calls.
- Include the solver and defect interfaces that the numerical plan names, rather than
  their complete generic implementations.
- Include the timepiece Hermite, rotation and SIRK interfaces that the λφ⁴ modules
  import or cite.
- Include the two paper excerpts that the methods actually depend on: the SIRK
  convergence setting (Hashimoto) and the generic polynomial-interaction/Faris–Lavine
  template (Kopperman tutorial). Neither paper states the λφ⁴ model of this bundle.

The continuous-coordinate `jetModel` remains the object of record. `siteModel`,
`phi4_scalar.rs`, the two-site Cadabra checks and the two-site return interval are
labeled lattice comparisons throughout.

## External source revision and attribution

- `timepiece`: commit `fa22e6f`, with the λφ⁴ files as working-tree changes.
- `unfer`: commit `b0aaa7c`; the five λφ⁴ files below are untracked working-tree files.
- `papers`: not a Git repository; the excerpts are from the current working snapshot.
- Paths in this part are relative to the `timepiece` root, so external files begin
  with `../unfer/` or `../papers/`.
- `complete file` means the whole file is copied. `lines A–B` means exactly those
  lines; a later block in the same section gives the next disjoint range.
- Line numbers refer to the working tree at bundle time.
- Relative links inside a copied file are unchanged. They resolve from that
  file's original directory, not from the location of this bundle.

## External file tree

**Source:** generated from the section list below; it is not a copy of a repository
file.

```text
../unfer/
├── docs/
│   ├── PHI4_ANALYTIC_PLAN.md                       (complete)
│   ├── PHI4_NUMERICAL_PLAN.md                      (complete)
│   ├── phi4_mehler.cdb                             (complete)
│   ├── CADABRA2_GOTCHAS.md                         (complete)
│   └── fixtures/phi4_mehler.json                   (complete)
├── nested_fock_algebra/src/
│   ├── phi4_scalar.rs                              (complete)
│   └── exact_inner.rs                              (complete dependency)
└── fock_sirk/
    ├── src/joint_sirk.rs                           (interfaces and rational core)
    ├── src/sm_defect.rs                            (selected interfaces)
    └── examples/anharmonic_oscillator.rs           (complete comparison)

../papers/
├── Hashimoto.md                                    (SIRK excerpts)
├── Kopperman_Tutorial.p.tex                        (generic φ⁴ template excerpt)
└── book.tex                                        (nested-Fock excerpts)

timepiece/BookProof/
├── ChapterQuadraticRotationEsa.lean                (selected theorems)
└── Toolbox/
    ├── ChapterHermiteProductCore.lean              (selected definitions)
    └── ChapterHermiteProductBasis.lean             (selected definitions)
```

## 1. unfer analytic and numerical plans

### File: `../unfer/docs/PHI4_ANALYTIC_PLAN.md`

**Source:** `../unfer/docs/PHI4_ANALYTIC_PLAN.md` (complete file, 212 lines).

````markdown
# Real scalar λφ⁴ — analytical and Cadabra2 research plan

The primary analytic target is the local scalar operator on continuous field and jet
coordinates. Existing one- and two-site calculations are periodic lattice comparisons.
Their return intervals apply to their specified finite-difference operators.

[Lean contract](../../timepiece/PHI4_FORMALIZATION_PLAN.md) ·
[Numerical experiments](PHI4_NUMERICAL_PLAN.md)

## From a local field to an inner Hamiltonian

Use continuous time and three spatial dimensions. Write U(s) = λ(s² − v²)²/4
with λ,v > 0. Starting from the Lagrangian density
½(∂ₜφ)² − ½|∇φ|² − U(φ), retain the whole potential in the Legendre transform.
In the manuscript scalar realization the inner operator is
h = pₛ²/2 + (j₁² + j₂² + j₃²)/2 + U(s) on L²(ℝ⁴). Only the scalar carries a
momentum. Its whole action is enclosed as H = dΓ(h). The indices in a matrix
expansion of dΓ(h) label one-particle basis functions of these continuous variables.

At unit width and λ = v = 1, act on the Gaussian (constant Mehler polynomial).
The field terms contribute 5/8, 7/8 and 1/4 at scalar degrees 0, 2 and 4.
Each jet contributes (1 + He₂(jᵣ))/2. The full column has mean 17/8 and
squared residual (7/8)²·2! + (1/4)²·4! + 3·(1/2)²·2! = 145/32 for a unit seed.
These analytic values are the first continuous-coordinate solver reference.

## Periodic lattice comparison

On a periodic grid with M sites, spacing a and volume Ma³, the momentum conjugate
to φₓ is a³∂ₜφₓ. In the variables $Q_x=a^{3/2}\phi_x$ and $P_x=a^{3/2}\dot\phi_x$ the result is

$$
h=\frac12\sum_x P_x^2
  +\frac{1}{2a^2}\sum_{x,r}(Q_{x+\hat r}-Q_x)^2
  +\frac{\lambda}{4a^3}\sum_x(Q_x^2-a^3v^2)^2 .
$$

$$
H=d\Gamma(h)=\sum_{i,j}\langle e_i,h e_j\rangle\,C^\dagger(e_i)A(e_j).
$$

The nonnegative square fixes the energy zero. Expanding it gives a constant
λMa³v⁴/4. Dropping this inner constant shifts every outer sector in proportion to
its particle number. The global reflection (φ,π) ↦ (−φ,−π) preserves the Hamiltonian.
Expansion about +v gives U(v+η) = λv²η² + λvη³ + λη⁴/4. The cubic coefficient changes
sign about −v. These checks distinguish the fully interacting wall from its quadratic
small-oscillation approximation. Lean also defines a scalar instance of the manuscript’s
independent-jet density with three jet multipliers and a single field momentum. Label any such
calculation explicitly. In the grid model the differences above determine the gradient.

## Derivations and checks

| Step | Calculation and independent check | Acceptance |
|---|---|---|
| A1. Legendre transform | Differentiate the discrete Lagrangian with respect to each velocity, solve for it and substitute. Derive the discrete force again by varying the link energy. | Recover the kinetic coefficient, the periodic Laplacian and the local force −λφₓ(φₓ²−v²). A constant field at either minimum has zero classical energy at rest. |
| A2. Momentum vertex | Use $Q_x=M^{-1/2}\sum_k e^{ik\cdot x}\widehat Q_k$, with Q̂₋ₖ = Q̂ₖ† and the matching rule for P. Handle zero and self-conjugate modes once. | The quadratic gradient has eigenvalue 4 Σᵣ sin²(kᵣa/2)/a². The quartic vertex has coefficient λ/(4a³M) per ordered tuple with k₁+k₂+k₃+k₄ = 0 modulo the reciprocal grid. |
| A3. Two-site test | Use the periodic 2×1×1 cell and Q₁,₂ = (u ± w)/√2. Sum the two local fourth powers independently. | Recover (u⁴ + 6u²w² + w⁴)/2. The mixed term tests coupling between different modes. The two oriented links along the active axis both contribute. |
| A4. Ordered action | At unit width put Q = b†+b, P = i(b†−b)/2 on the same mode. Normal order using the CCR. | Obtain Q⁴ = :Q⁴: + 6:Q²: + 3I and the complete one-site vacuum column specified in the Lean plan. Test a boundary state for which a word leaves an occupation window and returns. |
| A5. Outer enclosure | Apply the indexed inner sum on zero, one and two outer particles. Evaluate the inner identity and a product before lifting. | On two particles an inner shift cI gives 2cI. Multiplying two separately lifted factors produces cross-particle terms. Include an input on which these terms survive. |

A2 follows by orthogonality of the discrete Fourier characters in a **local** product.
The selection rule conserves total lattice momentum. No independent derivative field
or prescription for a nonlinear spatial-derivative product is needed. Use real
sine/cosine coordinates or a conjugation-aware complex implementation in executable
work. Independent oscillators for both members of every ±k pair would double the field.

## Executed Mehler and SIRK examples

The Cadabra2 process checks the two-site quartic by native product distribution.
Its embedded SymPy code differentiates the jet and site actions, applies ordered ladders
to polynomials and computes exact rational matrices. The four-site ring check enumerates
all 256 ordered momentum tuples including the zero and self-conjugate modes. A general
grid Fourier derivation is still needed for a symbolic identity at arbitrary grid shape.
[Executable derivation](phi4_mehler.cdb) · [Exact fixture](fixtures/phi4_mehler.json)

**One occupied outer excitation, one site.** In the unit-width Mehler convention
the Gaussian represents the constant polynomial. The first three nonzero components
of its full image are 5/8, 7/8 and 1/4 at Hermite levels 0, 2 and 4. On the odd
seed He₁ the coefficients are 23/8, 15/8 and 1/4 at levels 1, 3 and 5. In the
one-dimensional vacuum window the rational generator is −5i/8 at every positive shift.
Its trajectory has return probability one inside the window. Applying the full h gives
squared defect (7/8)²2! + (1/4)²4! = 97/32 for a normalized seed. Integrating this
residual gives the Lean-certified lower bound 1 − (97/32)t² on the exact return probability.
The empty outer vacuum is a different initial state. The ordered outer action checks
also give shifts 0, c, 2c on zero, one and two outer particles.
[Lean error and observable](../../timepiece/BookProof/Phi4/ChapterScalarSirk.lean)

**One occupied outer excitation, two sites.** At a = λ = v = 1 retain the unnormalized
product Hermites (0,0), (2,0), (0,2) of the uniform and staggered modes. Their Gram
matrix is diag(1,2,2). The two rational columns of V are the Gaussian seed and its
shift-5 solve. With Hₚ the three-dimensional compression, set R = (3I + iHₚ)⁻¹.
With W the Hermite Gram matrix and † the conjugate transpose, the reduced operators are

$$
V^+=(V^\dagger W V)^{-1}V^\dagger W,\qquad B=V^+ R V,\qquad G=3I-B^{-1}.
$$
The executable check distinguishes G from −iV⁺HₚV. In the full action the seed alone
has squared norm 3 outside the window. Computing all output Hermites through degree
six exhausts hV exactly because the largest input degree is two.

The fixture records the complete complex generator. For D = iVG − hV its squared
Hilbert–Schmidt norm in the physical metrics is
66577730826550897732871/259668494406269661228. The script checks the dissipation
identity $G^\dagger W_2 + W_2G = -6L^\dagger W L$, with
$W_2=V^\dagger WV$ and $L=RVB^{-1}-V$. Thus the forward
reduced evolution is contractive. Integrating the defect of V exp(tG) against the
unitary inner evolution bounds the state error by t‖D‖HS for a normalized retained
seed and t ≥ 0. This two-site bound uses the exact symbolic matrix calculation and
the analytic integral argument. Lean checks the rank-two matrices, their physical
Hermite Gram weights, and the squared rates used below.
[Rank-two Lean certificate](../../timepiece/BookProof/Phi4/ChapterScalarRankTwo.lean)

The orthogonal split of D locates the largest error in this example. Its squared
Hilbert–Schmidt norm is about 3.125 inside the three-mode window and 253.270
outside it. On the initial seed the corresponding squared norms are about 0.166
and exactly 3. Increasing the Krylov rank within these same three modes can address
the first contribution. It cannot recover the missing rows of the first full action.
`defect_split` checks both contributions on the same basis and trajectory.
[Exact split](fixtures/phi4_mehler.json)

### A two-site return probability below one

Take the unit Gaussian seed e in one occupied outer excitation and t = 1/100. Write
y(s) = V exp(sG)e₀ for the reconstructed state and U(s)e for the exact evolution. In
the following norms the Gaussian has norm one. The Gram identity makes exp(sG)
contractive for s ≥ 0. Consequently the full residual satisfies
‖D exp(sG)e₀‖ ≤ ‖D e₀‖ + s‖D‖HS‖G e₀‖. Integrating the residual against U(t−s) gives

$$
\|U(t)e-y(t)\| \le t\|De_0\|+
  \tfrac{t^2}{2}\|D\|_{\mathrm{HS}}\|Ge_0\|
  \le 2203729/100000000 .
$$

To see what this error allows us to resolve, project away the initial Gaussian ray
with Q = I − |e⟩⟨e|. Twice integrating y′′ and using contractivity gives
‖Qy(t)‖ ≥ t‖QVG e₀‖ − t²‖G²e₀‖/2. The exact squared rates in the fixture give
‖QVG e₀‖ ≥ 4.17 and ‖G²e₀‖ ≤ 88.51. Subtracting the full state error leaves
‖QU(t)e‖ ≥ 1523721/100000000 ≥ 3/200. By unitarity the return probability is at most
1 − (3/200)². For the other endpoint, the one-column phase at energy 13/4 has full
seed variance 337/16. Its squared state-error bound gives return at least
1 − (337/16)t² by the overlap inequality. Hence

$$
\frac{159663}{160000} \le |\langle e,U(1/100)e\rangle|^2
  \le \frac{39991}{40000}.
$$

The interval certifies departure from the initial ray for this unit-parameter model.
Lean proves the affine-in-time residual estimate for a differentiable scalar-core orbit
in `Model.orbit_error`. The specialization of its hypotheses to this contractive matrix
exponential and the final projection argument are analytic. The fixture checks their arithmetic. A Rust comparison
can use the endpoints before sweeping λ or changing the window.

### Reproduce the fixture

From the unfer root run the following. The comparison requires the fixture marker
after all checks, so an interrupted engine run fails even if the CLI exits successfully.

```bash
cadabra2-cli -q -n docs/phi4_mehler.cdb > /tmp/phi4-mehler.log
python3 - <<'PYCODE'
import json
from pathlib import Path
rows = Path("/tmp/phi4-mehler.log").read_text().splitlines()
checks = [s for s in rows if s.startswith("PHI4_CHECK|")]
assert len(set(checks)) == len(checks) == 29 and all(s.endswith("|0") for s in checks)
[result] = [s.split("|", 1)[1] for s in rows if s.startswith("PHI4_FIXTURE|")]
assert json.loads(result) == json.loads(Path("docs/fixtures/phi4_mehler.json").read_text())
PYCODE
```

Cadabra2 CLI reported 2.5.15 private (Nix derivation 2.5.14-p1). Four deliberate
changes produced exact nonzero differences. Dropping the mixed vertex gave 3,
changing a link difference to a sum gave −4, omitting the double contraction gave 3,
and deleting the energy constant gave 1/4. The script SHA-256 is
`f980c5acc06af12b0453ebbdb1811a952633c9124c2057c55930057c2f3f59a3`.
The formatted fixture SHA-256 is
`3694921d365de9d7a63a3721079f7f72349078cd19963ceae1fecb855c6ba48f`.

## Next analytical work

1. Build the full polynomial columns and shifted-solve reference for the continuous
   four-coordinate jet model. Check the Gaussian column above and an occupied jet
   seed, the Gram weights, and the residual outside the retained Hermites. Integrate
   that residual for the actual reduced orbit before quoting a return interval.
2. For the periodic comparison, extend the orthogonal-coordinate and character derivations to general periodic grids.
   Preserve mode reality, oriented link counts and the inner constant. **The two-site
   rotation is now connected to the polynomial core in Lean**: `twoSite_innerHam`
   identifies the actual `2×1×1` site operator with the uniform/staggered mode action
   on every seed, and `twoSite_column_00`/`_20`/`_02` reproduce the three exact fixture
   columns through degree six (`timepiece/BookProof/Phi4/ChapterScalarTwoSite.lean`).
   The character substitution itself is already formalized for arbitrary dimension in
   `BookProof.ChapterQuadraticRotationEsa`: `rotPoly` is the orthogonal change, and
   `pderiv_rotPoly`, `rotPoly_mulXPoly`, `rotPoly_momPoly` and `inner_pgLp_rotPoly`
   give the chain rules, canonical-pair transport and Gaussian unitarity. A concrete
   real Fourier matrix is now implemented as `periodic_fourier_1d` in
   `unfer/nested_fock_algebra/src/phi4_scalar.rs` and checked orthogonal for several
   cycle lengths. The Lean quartic-vertex transport and its momentum-conserving
   selection rules remain open.
3. For that comparison, read the fixture through the scalar Rust builder and compare exact full columns
   before varying the occupation cutoff or Krylov rank. At fixed window vary only rank,
   then at fixed rank vary only window. Report bounds for discarded rows and the reduced
   generator separately, together with the computed return probability.
4. For a fixed seed and time interval, integrate the defect on the reduced orbit, enclose
   arithmetic and compare with the signal produced by varying λ. A uniform bound across
   scalar model sizes needs an embedding and an observable that survives that change.

The legacy one-real-component Higgs calculation and the N12 independent-mode pilot
provide comparisons with different scalar dictionaries. The new exact fixture can
distinguish a missing mixed vertex or contraction in a future joint solver run.
[Higgs comparison](../fock_sirk/tests/sm_higgs_mechanism_sirk.rs) ·
[Numerical program](PHI4_NUMERICAL_PLAN.md)

````

### File: `../unfer/docs/PHI4_NUMERICAL_PLAN.md`

**Source:** `../unfer/docs/PHI4_NUMERICAL_PLAN.md` (complete file, 103 lines).

```markdown
# Real scalar λφ⁴ — numerical research and validation plan

**First experiment.** Evolve a single outer excitation for the continuous scalar
and three independent jet coordinates. Use the local inner Hamiltonian
h = pₛ²/2 + (j₁² + j₂² + j₃²)/2 + λ(s²−v²)²/4. Spatial position remains
continuous. The integer labels in the code denote Mehler occupations. The number
of shifted-solve vectors determines the rational Krylov rank. Resolve the effect
of changing λ on the normalized Gaussian return probability by enclosing the
full-action error for each trajectory.
[Operator and Lean targets](../../timepiece/PHI4_FORMALIZATION_PLAN.md) ·
[Cadabra2 derivation and exact checks](PHI4_ANALYTIC_PLAN.md)

## Reuse and baseline

- Use the bosonic occupations of `JointInnerBasis`, the same-mode coordinate
  and momentum in `InnerExpr`, and its `d_gamma` action. One outer particle
  carries all four continuous variables. Apply the scalar momentum twice on the same
  mode, multiply by the three jet squares, and retain the whole wall inside h. [Ordered action](../nested_fock_algebra/src/exact_inner.rs)
- Use the existing joint shifted solves, whitening, full images and reduced
  matrix exponential. The anharmonic example uses a positive quadratic well
  and forward products. The legacy SM Higgs example uses independent momentum
  and field modes. Keep both as named comparisons.
  [Rational solver](../fock_sirk/src/joint_sirk.rs) ·
  [Oscillator](../fock_sirk/examples/anharmonic_oscillator.rs) ·
  [Higgs comparison](../fock_sirk/tests/sm_higgs_mechanism_sirk.rs)
- Reuse basis enumeration and root-scan diagnostics from the SM N12 scalar pilot.
  It used independent mode quartics and products of compressed coordinate matrices.
  At five modes, total-occupation cutoffs 3, 4 and 5 gave one, two and one matching
  roots. This establishes a concrete failure mode for fitting a connected four-point
  function. The local mixed-mode interaction needs its own evidence.
  [Pilot](../fock_sirk/examples/sm_finite_mode.rs) · [Reported data](SM_RESEARCH_PLAN.md)

## Experiment sequence

1. **Implement the continuous-coordinate operator.** Assign one real mode to s and
   three to j₁, j₂, j₃. Give only s a kinetic term. At unit width and λ = v = 1,
   check the full action on the normalized product Gaussian. In the unnormalized
   Hermite polynomial convention its constant coefficient is 17/8, its field
   degree-two and degree-four coefficients are 7/8 and 1/4, and each pure degree-two
   jet coefficient is 1/2. Weight the output by the factorial Gram matrix, or
   convert the coefficients before comparing normalized occupation vectors. The
   squared residual about the mean is 145/32. Check an occupied jet input as well.
   Check inner constant shifts by 0, c and 2c in the first three outer sectors.
2. **Establish a finite reference.** At total inner occupation C apply each full
   word before projecting the output. On a small Hermite window independently
   evaluate matrix elements by Gaussian polynomial moments. Compare the projected
   evolution with the rational result and retain full images for a separate
   residual bound. For example at C = 0 the fourth power of the compressed field
   coordinate vanishes while the compression of its fourth power gives 3.
3. **Run the bounded comparison.** Prepare one outer particle in the unit-width
   Gaussian inner state ψ. Use the bounded observable O = |ψ⟩⟨ψ| on this sector.
   Sweep C = 4, 8, 12 and Krylov ranks 2 and 4 at t = 0.05 and 0.1 as initial
   pilot values. Fix λ = 1 and 1.1 in paired cells with v = 1. Use identical
   initial states, shifts and windows across each pair. For example use the common
   shift budget 7t and spacing t, validating each rank with the existing helper.
   Run λ = 1 against itself as a null control. Record the effect interval and its
   cost. A changed width requires transporting H, ψ and O together before projection.
   Record how much of the residual is carried by discarded jet occupations.
4. **Bound the evolution that was computed.** With window projector P and isometry
   V, the numerical compression uses B ≈ V†(γI + iPHP)⁻¹V on the window, and
   G = γI − B⁻¹. Reconstruct V exp(tG)V†ψ. Keep the Ritz matrix V†HV for spectral
   diagnostics. Compute D = iVG − HV using **full**, unprojected images of every
   basis column. For a self-adjoint H and an exactly isometric V, bound state error
   by initial leakage plus the time integral of ‖D exp(sG)V†ψ‖. Bound reduced
   growth or enclose this integral. Record separately the error against the finite
   reference and the norms of discarded action. The latter can remain large even
   when the former is small. Allow for basis nonorthogonality, finite precision,
   GMRES, inversion, Padé and restarts wherever their effects are not already
   covered by the returned-map defect. With a state error ε, charge each probability
   estimate 2ε+ε² and add the two budgets for a response. Require the resulting
   interval to exclude zero before interpreting its sign. Bind parameters and
   interval endpoints to a Lean statement for this scalar instance. The SM defect
   artifact supplies reusable arithmetic and a conditional Duhamel estimate.
   [Defect implementation](../fock_sirk/src/sm_defect.rs) ·
   [SM fixture](fixtures/sm_defect_bridge.json)
5. **Extend the continuous-coordinate study.** For a fixed operator and preparation,
   compare even and odd channels as the occupation window grows. A mass claim needs
   bounds on missed states and the appropriate absolute energy or channel splitting.
   For spatial observables specify the continuous position dependence, test functions
   and their matrix elements on the common core. Any identification of independent
   jets with spatial derivatives of a field needs its own proof.

## Existing lattice comparison

`ScalarGrid::periodic` and `two_site_mode_hamiltonian` implement a different
Hamiltonian built from periodic links. Its two-site columns and its three-mode
compressed evolution have Rust tests. At unit parameters and t = 0.01 its analytic
Gaussian return interval is [0.99789375, 0.999775]. The three-mode exponential
test is a finite reference. The rank-two Hashimoto generator comes from a compressed
resolvent. The site fixture can check operator-ordering and residual routines.
Its site spacing, Fourier sums and lattice return interval are specific to this example.
[Comparison builder](../nested_fock_algebra/src/phi4_scalar.rs) ·
[Exact comparison fixture](fixtures/phi4_mehler.json)

## Evidence to retain

For each cell, store the source revision, operator/fixture digest, model and energy
convention, seed and observable, Mehler width, inner and outer occupations, basis
cutoff, requested and attained ranks, shifts, residuals, error components, time,
memory and failure reason. Publish the dense reference, projected rational error
and full-action estimate as different quantities. Compare efficiency at equal
bounded-observable error. Mark measurements, conditional bounds and kernel-checked
conclusions separately.

```

## 2. Cadabra2 derivation and exact fixture

### File: `../unfer/docs/phi4_mehler.cdb`

**Source:** `../unfer/docs/phi4_mehler.cdb` (complete file, 267 lines).
It is Cadabra2 input with an embedded SymPy section; the fence language is Python.

```python
# Run: cadabra2-cli -q -n docs/phi4_mehler.cdb
# Canonical unit-width Mehler coordinates, ordered actions on polynomials times the Gaussian.
# SymPy handles exact scalar derivatives; Cadabra independently expands the two-site vertex.
import json
import sympy as sp

def check(name, expr):
    result = sp.simplify(expr)
    if result != 0:
        raise AssertionError(name + ": " + str(result))
    print("PHI4_CHECK|" + name + "|0")

# Each deliberate mutation must change an observable exact value.
controls = {}
def distinguish(name, correct, mutant, at):
    difference = sp.simplify((correct-mutant).subs(at))
    assert difference.is_zero is False, name
    controls[name] = str(difference)
    print("PHI4_CONTROL|" + name + "|" + str(difference))

q = sp.Symbol("q",real=True)
v, lam, a = sp.symbols("v lam a", positive=True, real=True)
x, y, u, w, p, speed = sp.symbols("x y u w p speed", real=True)
def potential(field):
    return lam * (field**2 - v**2)**2 / 4

# Local unit-volume independent jets j1,j2,j3; the single active momentum belongs to q.
jets = sp.symbols("j1:4", real=True)
jet_energy = sum(j**2 for j in jets)/2 + potential(q)
lag = speed**2/2 - jet_energy
canonical = sp.diff(lag, speed)
check("jet-canonical-momentum", canonical - speed)
check("jet-legendre", (p*speed - lag).subs(speed, p) - (p**2/2 + jet_energy))

# Momentum from the site action with cell volume a^3, before canonical rescaling.
cell_lag = a**3 * (speed**2/2 - potential(q))
density_p = sp.diff(cell_lag, speed)
check("site-canonical-momentum", density_p - a**3*speed)
check("site-legendre", ((density_p*speed-cell_lag).subs(speed, p/a**sp.Rational(3,2))
    .subs(q,x/a**sp.Rational(3,2))) - p**2/2 - lam*(x**2-a**3*v**2)**2/(4*a**3))
check("constant", potential(0) - lam*v**4/4)
check("shifted-wall", potential(v+x) - (lam*v**2*x**2+lam*v*x**3+lam*x**4/4))
left, right = sp.symbols("left right")
local = ((x-left)**2 + (right-x)**2)/(2*a**2) + lam*(x**2-a**3*v**2)**2/(4*a**3)
check("site-force", -sp.diff(local,x) - ((left+right-2*x)/a**2-lam*x*(x**2/a**3-v**2)))

# Orthogonal two-site Fourier coordinates. Two positive-direction links wrap to each other.
mixed := (u+w)*(u+w)*(u+w)*(u+w)/4 + (u-w)*(u-w)*(u-w)*(u-w)/4.
distribute(mixed)
sort_product(mixed)
collect_terms(mixed)
assert len(mixed) == 3
expected := (u*u*u*u + 6*u*u*w*w + w*w*w*w)/2.
vertexdiff := @(mixed) - @(expected).
distribute(vertexdiff)
sort_product(vertexdiff)
collect_terms(vertexdiff)
if str(vertexdiff) != "0":
    raise AssertionError("two-site quartic: " + str(vertexdiff))
print("PHI4_CHECK|cadabra-mixed-vertex|0")
sites = [(u+w)/sp.sqrt(2), (u-w)/sp.sqrt(2)]
links = sum((sites[(i+1)%2]-sites[i])**2 for i in range(2))/(2*a**2)
check("link-eigenvalue", links - (4/a**2)*w**2/2)
distinguish("missing-mixed-vertex", sum(s**4 for s in sites), (u**4+w**4)/2, {u:1,w:1})
wrong_links = sum((sites[(i+1)%2]+sites[i])**2 for i in range(2))/(2*a**2)
distinguish("wrong-link-sign", links, wrong_links, {a:1,u:sp.sqrt(2),w:0})
distinguish("missing-energy-constant", potential(q), potential(q)-lam*v**4/4, {lam:1,v:1,q:0})

# Verify all ordered momentum tuples on a four-site ring, including its self-conjugate modes.
from itertools import product
for ks in product(range(4), repeat=4):
    vertex = sum(sp.I**(site*sum(ks)) for site in range(4))/16
    assert vertex == (sp.Rational(1,4) if sum(ks)%4 == 0 else 0)
print("PHI4_CHECK|four-site-ordered-vertices-256|0")

# Polynomial realization of b and b† in one Mehler coordinate.
def annihilate(f):
    return sp.diff(f,x)
def create(f):
    return sp.expand(x*f-annihilate(f))
def position(f):
    return sp.expand(create(f)+annihilate(f))
def momentum(f):
    return sp.I*(create(f)-annihilate(f))/2
def power(op, f, n):
    for _ in range(n):
        f = op(f)
    return f
def normal_power(f, n):
    return sum(sp.binomial(n,k)*power(create,power(annihilate,f,n-k),k) for k in range(n+1))
def unit_action(f):
    return sp.expand(momentum(momentum(f))/2 + (x**2-1)**2*f/4)

f = sp.Function("f")(x)
check("ccr",position(momentum(f))-momentum(position(f))-sp.I*f)
check("ordered-quartic",power(position,f,4)-normal_power(f,4)-6*normal_power(f,2)-3*f)
check("parity",unit_action(f.subs(x,-x))-unit_action(f).subs(x,-x))
distinguish("missing-double-contraction", power(position,1,4),
            normal_power(1,4)+6*normal_power(1,2), {x:0})

# Decompose h He_n in unnormalized probabilists' Hermites. Squared normalized column entries
# equal coeff^2 * m!/n!, without floating square roots. This uses the whole polynomial action.
def column(n):
    poly = unit_action(sp.hermite_prob(n,x))
    coeff = {}
    for m in range(n+4,-1,-1):
        c = sp.expand(poly).coeff(x,m)
        if c != 0:
            coeff[m] = c
            poly -= c*sp.hermite_prob(m,x)
    assert sp.expand(poly) == 0
    return coeff
vac = column(0)
odd = column(1)
assert vac == {0:sp.Rational(5,8),2:sp.Rational(7,8),4:sp.Rational(1,4)}
assert odd == {1:sp.Rational(23,8),3:sp.Rational(15,8),5:sp.Rational(1,4)}
print("PHI4_CHECK|even-and-odd-columns|0")
# At cutoff zero (P Q P)^4=0 while the vacuum expectation of Q^4 is 3.
check("window-exit-and-return", sp.integrate(x**4*sp.exp(-x**2/2),
      (x,-sp.oo,sp.oo))/sp.sqrt(2*sp.pi)-3)

# Apply C†_i A_j in the unnormalized outer monomial representation (annihilation = derivative).
y0,y2,y4 = sp.symbols("y0 y2 y4")
image = vac[0]*y0 + vac[2]*y2 + vac[4]*y4
for n in range(3):
    check("outer-column-"+str(n), image*sp.diff(y0**n,y0) -
          (0 if n == 0 else n*y0**(n-1)*image))
    check("outer-shift-"+str(n), y0*sp.diff(y0**n,y0)-n*y0**n)
check("lift-product-cross-term",y0*sp.diff(y0*sp.diff(y0**2,y0),y0)
      -y0*sp.diff(y0**2,y0)-2*y0**2)

# Actual compressed resolvent for the one-dimensional vacuum window, unit-width one site.
gamma = sp.symbols("gamma",positive=True)
reduced_resolvent = 1/(gamma+sp.I*vac[0])
generator = sp.simplify(gamma-1/reduced_resolvent)
check("rank-one-hashimoto-generator",generator+sp.I*sp.Rational(5,8))
variance = sum(c**2*sp.factorial(m) for m,c in vac.items() if m != 0)
check("full-action-defect-squared",variance-sp.Rational(97,32))

# A nontrivial rational compression. Work in the even two-site window (00,20,02).
# The Hermite Gram matrix supplies the physical metric in these unnormalized coordinates.
window = [(0,0),(2,0),(0,2)]
def herm2(i,j):
    return sp.hermite_prob(i,u)*sp.hermite_prob(j,w)
modes = [(i,n-i) for n in range(7) for i in range(n+1)]
sitewall = sum(potential(s) for s in sites).subs({lam:1,v:1})
def two_site_column(i,j):
    f = herm2(i,j)
    kinetic = 0
    for coord in (u,w):
        df = sp.diff(f,coord)-coord*f/2
        kinetic -= (sp.diff(df,coord)-coord*df/2)/2
    poly = sp.Poly(kinetic+(links.subs(a,1)+sitewall)*f,u,w)
    coeffs = {}
    for pair in reversed(modes):
        coeff = poly.coeff_monomial(pair)
        if coeff:
            coeffs[pair] = coeff
            poly -= sp.Poly(coeff*herm2(*pair),u,w)
    assert poly.is_zero
    return coeffs
cols = [two_site_column(*pair) for pair in window]
def rows(basis):
    return sp.Matrix([[col.get(pair,0) for col in cols] for pair in basis])
def gram(basis):
    return sp.diag(*(sp.factorial(i)*sp.factorial(j) for i,j in basis))
hwin = rows(window)
metric = gram(window)
assert metric*hwin == hwin.T*metric
seed = sp.eye(3)[:,0]
first = (5*sp.eye(3)+sp.I*hwin).inv()*seed
basis = seed.row_join(first)
def clean(mat):
    return mat.applyfunc(sp.cancel)
metric2 = clean(basis.H*metric*basis)
dual = clean(metric2.inv()*basis.H*metric)
assert clean(dual*basis) == sp.eye(2)
bounded = clean(dual*(3*sp.eye(3)+sp.I*hwin).inv()*basis)
reduced = clean(3*sp.eye(2)-bounded.inv())
assert clean(reduced+sp.I*dual*hwin*basis) != sp.zeros(2)
# Resolvent leakage gives the exact dissipation in the physical reduced metric.
# For Z=R V B^-1 we have V+ Z=I and (3I+i hwin)Z=V B^-1.
zlift = clean((3*sp.eye(3)+sp.I*hwin).inv()*basis*bounded.inv())
leak = clean(zlift-basis)
assert clean(reduced.H*metric2+metric2*reduced + 6*leak.H*metric*leak) == sp.zeros(2)
print("PHI4_CHECK|two-site-forward-contractivity|0")
embed = sp.Matrix([[int(pair == state) for state in window] for pair in modes])
defect = clean(sp.I*embed*basis*reduced-rows(modes)*basis)
defect_sq = clean(defect.H*gram(modes)*defect)
# Coordinate-independent Hilbert-Schmidt norm of the full defect (squared).
frobenius_sq = sp.cancel(sp.trace(metric2.inv()*defect_sq))
outside = [pair for pair in modes if pair not in window]
first_tail_sq = (rows(outside)[:,0].T*gram(outside)*rows(outside)[:,0])[0]
assert frobenius_sq > 0 and first_tail_sq > 0
print("PHI4_CHECK|two-site-rational-compression-and-full-defect|0")

# Orthogonally split the full residual into a rational-compression error within
# the window and the discarded occupation rows. Use the same trajectory for both.
inside = clean(embed*embed.T*defect)
outside_defect = clean(defect-inside)
inside_gram = clean(inside.H*gram(modes)*inside)
outside_gram = clean(outside_defect.H*gram(modes)*outside_defect)
assert clean(inside_gram+outside_gram) == defect_sq
def trace_physical(g):
    return sp.cancel(sp.trace(metric2.inv()*g))
split = {"inside":inside_gram, "outside":outside_gram}
check("two-site-defect-orthogonal-split", trace_physical(inside_gram)
      + trace_physical(outside_gram)-frobenius_sq)

# Certify a short-time return interval against the full two-site evolution.
# Norms use the retained Gram metric; the defect uses every output occupation.
seed2 = sp.Matrix([1,0])
def norm_sq(vect, weight):
    return sp.cancel((vect.H*weight*vect)[0])
velocity = clean(reduced*seed2)
acceleration = clean(reduced*velocity)
v_full = clean(basis*velocity)
transverse = clean(v_full-seed*(seed.H*metric*v_full)[0])
rates_sq = {
    "initial_defect":defect_sq[0,0], "defect_hs":frobenius_sq,
    "speed":norm_sq(velocity,metric2), "acceleration":norm_sq(acceleration,metric2),
    "transverse_speed":norm_sq(transverse,metric)}
Q = sp.Rational
assert rates_sq["initial_defect"] <= Q(178,100)**2
assert rates_sq["defect_hs"] <= Q(1602,100)**2 and rates_sq["speed"] <= Q(529,100)**2
assert rates_sq["acceleration"] <= Q(8851,100)**2
assert rates_sq["transverse_speed"] >= Q(417,100)**2
t = Q(1,100)
state_error = Q(178,100)*t + Q(1602,100)*Q(529,100)*t**2/2
transverse_floor = Q(417,100)*t - Q(8851,100)*t**2/2 - state_error
assert transverse_floor >= Q(3,200)
seed_residual = rows(modes)[:,0] - embed*seed*hwin[0,0]
variance2 = norm_sq(seed_residual,gram(modes))
check("two-site-full-seed-variance",variance2-Q(337,16))
return_lo = 1-variance2*t**2
return_hi = 1-Q(3,200)**2
assert 0 < return_lo < return_hi < 1
print("PHI4_CHECK|two-site-return-interval-arithmetic|0")

def exact_text(expr):
    return str(sp.expand(expr))
fixture = {
    "schema":"phi4-mehler-exact/v1", "mutation_differences":controls, "basis":"He_n (unnormalized); norm^2=n!",
    "jet_inner":"p^2/2 + sum_j jet_j^2/2 + lam*(q^2-v^2)^2/4",
    "grid":[2,1,1], "boundary":"periodic positive links", "energy_zero":"square retained",
    "commuting_coefficients":{
        "wall_density":exact_text(potential(q)), "two_site_gradient":exact_text(links),
        "two_site_wall":exact_text(sum(lam*(s**2-a**3*v**2)**2/(4*a**3) for s in sites))},
    "unit_cell_columns":{str(n):{str(m):str(c) for m,c in col.items()}
                         for n,col in [(0,vac),(1,odd)]},
    "two_site_sirk":{"parameters":"a=lam=v=1", "window":window, "shifts":[5,3],
        "rank":2, "forward_contractive":True,
        "defect_split":{k:{"initial_squared":str(g[0,0]),"hs_squared":str(trace_physical(g))}
                        for k,g in split.items()},
        "short_time":{"t":str(t), "squared_rates":{k:str(v) for k,v in rates_sq.items()},
            "state_error_upper":str(state_error), "transverse_norm_lower":str(transverse_floor),
            "return_probability_interval":[str(return_lo),str(return_hi)]}, "metric":"Hermite factorial weights",
        "window_gram_diagonal":[str(metric[i,i]) for i in range(3)],
        "full_columns":[{"input":pair, "outputs":[[i,j,str(c)] for (i,j),c in sorted(col.items())]}
                        for pair,col in zip(window,cols)],
        "basis":"seed,(5I+iPHP)^-1 seed",
        "generator":[[str(reduced[i,j]) for j in range(2)] for i in range(2)],
        "full_defect_hilbert_schmidt_squared":str(frobenius_sq),
        "seed_action_outside_window_squared":str(first_tail_sq)},
    "rank_one":{"shift":"gamma>0","seed":"one outer excitation in He_0","generator":str(generator),
                "full_defect_squared":str(variance)}}
print("PHI4_FIXTURE|" + json.dumps(fixture,sort_keys=True))

```

### File: `../unfer/docs/fixtures/phi4_mehler.json`

**Source:** `../unfer/docs/fixtures/phi4_mehler.json` (complete file, 245 lines).

```json
{
  "basis": "He_n (unnormalized); norm^2=n!",
  "boundary": "periodic positive links",
  "commuting_coefficients": {
    "two_site_gradient": "2*w**2/a**2",
    "two_site_wall": "a**3*lam*v**4/2 - lam*u**2*v**2/2 - lam*v**2*w**2/2 + lam*u**4/(8*a**3) + 3*lam*u**2*w**2/(4*a**3) + lam*w**4/(8*a**3)",
    "wall_density": "lam*q**4/4 - lam*q**2*v**2/2 + lam*v**4/4"
  },
  "energy_zero": "square retained",
  "grid": [
    2,
    1,
    1
  ],
  "jet_inner": "p^2/2 + sum_j jet_j^2/2 + lam*(q^2-v^2)^2/4",
  "mutation_differences": {
    "missing-double-contraction": "3",
    "missing-energy-constant": "1/4",
    "missing-mixed-vertex": "3",
    "wrong-link-sign": "-4"
  },
  "rank_one": {
    "full_defect_squared": "97/32",
    "generator": "-5*I/8",
    "seed": "one outer excitation in He_0",
    "shift": "gamma>0"
  },
  "schema": "phi4-mehler-exact/v1",
  "two_site_sirk": {
    "basis": "seed,(5I+iPHP)^-1 seed",
    "defect_split": {
      "inside": {
        "hs_squared": "608593260375654076576/194751370804702245921",
        "initial_squared": "64208153658128/387678327400657"
      },
      "outside": {
        "hs_squared": "508924037/2009412",
        "initial_squared": "3"
      }
    },
    "forward_contractive": true,
    "full_columns": [
      {
        "input": [
          0,
          0
        ],
        "outputs": [
          [
            0,
            0,
            "13/4"
          ],
          [
            0,
            2,
            "23/8"
          ],
          [
            0,
            4,
            "1/8"
          ],
          [
            2,
            0,
            "7/8"
          ],
          [
            2,
            2,
            "3/4"
          ],
          [
            4,
            0,
            "1/8"
          ]
        ]
      },
      {
        "input": [
          2,
          0
        ],
        "outputs": [
          [
            0,
            0,
            "7/4"
          ],
          [
            0,
            2,
            "3/2"
          ],
          [
            2,
            0,
            "37/4"
          ],
          [
            2,
            2,
            "47/8"
          ],
          [
            2,
            4,
            "1/8"
          ],
          [
            4,
            0,
            "15/8"
          ],
          [
            4,
            2,
            "3/4"
          ],
          [
            6,
            0,
            "1/8"
          ]
        ]
      },
      {
        "input": [
          0,
          2
        ],
        "outputs": [
          [
            0,
            0,
            "23/4"
          ],
          [
            0,
            2,
            "69/4"
          ],
          [
            0,
            4,
            "31/8"
          ],
          [
            0,
            6,
            "1/8"
          ],
          [
            2,
            0,
            "3/2"
          ],
          [
            2,
            2,
            "31/8"
          ],
          [
            2,
            4,
            "3/4"
          ],
          [
            4,
            2,
            "1/8"
          ]
        ]
      }
    ],
    "full_defect_hilbert_schmidt_squared": "66577730826550897732871/259668494406269661228",
    "generator": [
      [
        "-1975087311464981/387678327400657 - 7803020777077170*I/387678327400657",
        "-1"
      ],
      [
        "-36582638530574935/3101426619205256 + 39094647255223290*I/387678327400657",
        "5"
      ]
    ],
    "metric": "Hermite factorial weights",
    "parameters": "a=lam=v=1",
    "rank": 2,
    "seed_action_outside_window_squared": "3",
    "shifts": [
      5,
      3
    ],
    "short_time": {
      "return_probability_interval": [
        "159663/160000",
        "39991/40000"
      ],
      "squared_rates": {
        "acceleration": "75339036499256870978268144523520649/9618847074314944005261058025536",
        "defect_hs": "66577730826550897732871/259668494406269661228",
        "initial_defect": "1227243135860099/387678327400657",
        "speed": "86475734973080181/3101426619205256",
        "transverse_speed": "108061083758287089/6202853238410512"
      },
      "state_error_upper": "2203729/100000000",
      "t": "1/100",
      "transverse_norm_lower": "1523721/100000000"
    },
    "window": [
      [
        0,
        0
      ],
      [
        2,
        0
      ],
      [
        0,
        2
      ]
    ],
    "window_gram_diagonal": [
      "1",
      "2",
      "2"
    ]
  },
  "unit_cell_columns": {
    "0": {
      "0": "5/8",
      "2": "7/8",
      "4": "1/4"
    },
    "1": {
      "1": "23/8",
      "3": "15/8",
      "5": "1/4"
    }
  }
}

```

## 3. Rust comparison and solver dependencies

### File: `../unfer/nested_fock_algebra/src/phi4_scalar.rs`

**Source:** `../unfer/nested_fock_algebra/src/phi4_scalar.rs` (complete file, 393 lines).

```rust
//! Periodic lattice comparison for the scalar λφ⁴ model and its two-site fixture.
//! The spatial sites and links here belong to this comparison. The project's
//! continuous-coordinate scalar operator uses independent field and jet variables.
//!
//! The site Hamiltonian is
//! `h = ½ Σ p_x² + (1/(2a²)) Σ_links (q_next − q_x)²
//!      + Σ_x (λ/(4a³))(q_x² − a³v²)²`,
//! with `q = a† + a` and `p = i(a† − a)/2`.  The two-site `2×1×1` grid has one
//! positive direction, so its two wrapped links give the factor-two link of the
//! exact fixture.  The rotated builder rewrites the same operator in the uniform
//! and staggered modes `u = (q₀+q₁)/√2`, `w = (q₀−q₁)/√2`; because the Gaussian
//! is rotation invariant, mode and site vacua coincide and the mode occupation
//! basis is the fixture's unnormalized product-Hermite basis up to `√(m! n!)`.
//!
//! Coefficients are `f64`; the comparison tolerance is far above their rounding
//! error and far below any nonzero fixture coefficient.

use crate::exact_inner::{ActionLimits, InnerExpr, InnerVector, JointInnerBasis};
use num_complex::Complex64;

/// A scalar grid with one bosonic inner mode per site and oriented active links.
#[derive(Clone, Debug)]
pub struct ScalarGrid {
    pub a: f64,
    pub lam: f64,
    pub v: f64,
    pub sites: Vec<u32>,
    /// `(source, target)` for every oriented positive link counted by the model.
    pub links: Vec<(u32, u32)>,
}

impl ScalarGrid {
    /// A rectangular periodic grid with `nx * ny * nz` sites and one positive
    /// link per site and direction.
    pub fn periodic(nx: usize, ny: usize, nz: usize, a: f64, lam: f64, v: f64) -> Self {
        assert!(
            nx > 0 && ny > 0 && nz > 0,
            "periodic sides must be nonempty"
        );
        let index = |x: usize, y: usize, z: usize| -> u32 { (x + nx * (y + ny * z)) as u32 };
        let n = nx * ny * nz;
        let mut links = Vec::with_capacity(3 * n);
        for z in 0..nz {
            for y in 0..ny {
                for x in 0..nx {
                    let s = index(x, y, z);
                    links.push((s, index((x + 1) % nx, y, z)));
                    links.push((s, index(x, (y + 1) % ny, z)));
                    links.push((s, index(x, y, (z + 1) % nz)));
                }
            }
        }
        Self {
            a,
            lam,
            v,
            sites: (0..n as u32).collect(),
            links,
        }
    }

    /// The `2×1×1` periodic grid: two wrapped links along the active axis.
    pub fn two_site(a: f64, lam: f64, v: f64) -> Self {
        Self::periodic(2, 1, 1, a, lam, v)
    }

    fn coordinate(&self, site: u32) -> InnerExpr {
        InnerExpr::coordinate(site)
    }

    fn momentum(&self, site: u32) -> InnerExpr {
        InnerExpr::momentum(site)
    }

    fn scaled(expr: InnerExpr, c: f64) -> InnerExpr {
        expr.scaled(Complex64::new(c, 0.0))
    }

    fn sum(parts: Vec<InnerExpr>) -> InnerExpr {
        InnerExpr::Sum(parts)
    }

    fn product(factors: Vec<InnerExpr>) -> InnerExpr {
        InnerExpr::Product(factors)
    }

    fn square(expr: InnerExpr) -> InnerExpr {
        Self::product(vec![expr.clone(), expr])
    }

    fn difference(left: InnerExpr, right: InnerExpr) -> InnerExpr {
        Self::sum(vec![left, Self::scaled(right, -1.0)])
    }

    /// The site Hamiltonian in the original site coordinates.
    pub fn site_hamiltonian(&self) -> InnerExpr {
        let kinetic = Self::sum(
            self.sites
                .iter()
                .map(|&s| Self::square(self.momentum(s)))
                .collect(),
        );
        let wall = self.lam / (2.0 * self.a.powi(3));
        let offset = self.a.powi(3) * self.v * self.v;
        let mut forms = Vec::new();
        for &s in &self.sites {
            let q = self.coordinate(s);
            let shifted = Self::difference(
                Self::square(q),
                InnerExpr::Scalar(Complex64::new(offset, 0.0)),
            );
            forms.push(Self::scaled(shifted, wall.sqrt()));
        }
        for &(s, t) in &self.links {
            forms.push(Self::scaled(
                Self::difference(self.coordinate(t), self.coordinate(s)),
                1.0 / self.a,
            ));
        }
        let potential = Self::sum(forms.iter().cloned().map(Self::square).collect());
        Self::scaled(Self::sum(vec![kinetic, potential]), 0.5)
    }

    /// The same Hamiltonian in the two-site uniform/staggered modes.
    pub fn two_site_mode_hamiltonian(&self) -> InnerExpr {
        debug_assert_eq!(self.sites, vec![0, 1], "mode builder is the 2×1×1 grid");
        // After the orthogonal change these are the two independent mode labels;
        // the site coordinates are not used as basis labels here.
        let u = self.coordinate(0);
        let w = self.coordinate(1);
        let pu = self.momentum(0);
        let pw = self.momentum(1);
        let add = |x: InnerExpr, y: InnerExpr| Self::sum(vec![x, y]);
        let kinetic = Self::sum(vec![Self::square(pu), Self::square(pw)]);
        let wall_scale = self.lam / (4.0 * self.a.powi(3));
        let offset = 2.0 * self.a.powi(3) * self.v * self.v;
        let radial = Self::difference(
            add(Self::square(u.clone()), Self::square(w.clone())),
            InnerExpr::Scalar(Complex64::new(offset, 0.0)),
        );
        let wall = Self::scaled(Self::square(radial), wall_scale);
        let mixed = Self::scaled(
            Self::square(Self::product(vec![u, w.clone()])),
            self.lam / self.a.powi(3),
        );
        let link = Self::scaled(Self::square(w), 4.0 / (self.a * self.a));
        let potential = Self::sum(vec![wall, mixed, link]);
        Self::scaled(Self::sum(vec![kinetic, potential]), 0.5)
    }

    /// Coefficients of `h (He_i(u) He_j(w))` in the unnormalized mode basis.
    pub fn two_site_column(&self, i: u32, j: u32) -> Vec<((u32, u32), f64)> {
        let h = self.two_site_mode_hamiltonian();
        let key = JointInnerBasis::new([(0, i), (1, j)], []).expect("distinct bosonic modes");
        let input = InnerVector::from([(key, Complex64::new(1.0, 0.0))]);
        let output = h
            .apply(&input, ActionLimits::default())
            .expect("finite action");
        let input_norm = (factorial(i) * factorial(j)) as f64;
        let mut column = Vec::new();
        for (basis, amplitude) in output {
            let m = *basis.bosons().get(&0).unwrap_or(&0);
            let n = *basis.bosons().get(&1).unwrap_or(&0);
            let output_norm = (factorial(m) * factorial(n)) as f64;
            // InnerExpr uses normalized occupations; the fixture uses unnormalized Hermites.
            let coefficient = amplitude.re * (input_norm / output_norm).sqrt();
            if coefficient.abs() > 1e-10 {
                column.push(((m, n), coefficient));
            }
        }
        column.sort_by_key(|&(mode, _)| mode);
        column
    }
}

fn factorial(n: u32) -> u64 {
    (1..=u64::from(n)).product::<u64>().max(1)
}

/// Real Fourier modes of a one-dimensional periodic cycle. The returned rows are
/// orthonormal under the Euclidean inner product; `n = 2` is the uniform/staggered
/// rotation used by the two-site builder.
pub fn periodic_fourier_1d(n: usize) -> Vec<Vec<f64>> {
    assert!(n > 0, "periodic side must be nonempty");
    let norm = 1.0 / (n as f64).sqrt();
    let mode_norm = (2.0 / n as f64).sqrt();
    let mut rows = vec![vec![norm; n]];
    for k in 1..=((n - 1) / 2) {
        let cos: Vec<f64> = (0..n)
            .map(|x| (std::f64::consts::TAU * (k * x) as f64 / n as f64).cos() * mode_norm)
            .collect();
        let sin: Vec<f64> = (0..n)
            .map(|x| (std::f64::consts::TAU * (k * x) as f64 / n as f64).sin() * mode_norm)
            .collect();
        rows.push(cos);
        rows.push(sin);
    }
    if n % 2 == 0 {
        rows.push(
            (0..n)
                .map(|x| if x % 2 == 0 { norm } else { -norm })
                .collect(),
        );
    }
    rows
}

#[cfg(test)]
mod tests {
    use super::ScalarGrid;
    use crate::exact_inner::{ActionLimits, InnerVector, JointInnerBasis};
    use num_complex::Complex64;

    type Column = &'static [((u32, u32), f64)];

    const COLUMN_00: Column = &[
        ((0, 0), 13.0 / 4.0),
        ((0, 2), 23.0 / 8.0),
        ((0, 4), 1.0 / 8.0),
        ((2, 0), 7.0 / 8.0),
        ((2, 2), 3.0 / 4.0),
        ((4, 0), 1.0 / 8.0),
    ];
    const COLUMN_20: Column = &[
        ((0, 0), 7.0 / 4.0),
        ((0, 2), 3.0 / 2.0),
        ((2, 0), 37.0 / 4.0),
        ((2, 2), 47.0 / 8.0),
        ((2, 4), 1.0 / 8.0),
        ((4, 0), 15.0 / 8.0),
        ((4, 2), 3.0 / 4.0),
        ((6, 0), 1.0 / 8.0),
    ];
    const COLUMN_02: Column = &[
        ((0, 0), 23.0 / 4.0),
        ((0, 2), 69.0 / 4.0),
        ((0, 4), 31.0 / 8.0),
        ((0, 6), 1.0 / 8.0),
        ((2, 0), 3.0 / 2.0),
        ((2, 2), 31.0 / 8.0),
        ((2, 4), 3.0 / 4.0),
        ((4, 2), 1.0 / 8.0),
    ];

    fn assert_column(actual: Vec<((u32, u32), f64)>, expected: Column, label: &str) {
        for &(mode, coefficient) in expected {
            let got = actual
                .iter()
                .find(|&&(m, _)| m == mode)
                .map(|&(_, c)| c)
                .unwrap_or(0.0);
            assert!(
                (got - coefficient).abs() < 1e-8,
                "{label} mode {mode:?}: got {got}, expected {coefficient}"
            );
        }
        for (mode, coefficient) in actual {
            assert!(
                expected
                    .iter()
                    .any(|&(m, c)| m == mode && (c - coefficient).abs() < 1e-8),
                "{label} unexpected coefficient at {mode:?}: {coefficient}"
            );
        }
    }

    #[test]
    fn two_site_columns_match_fixture() {
        let model = ScalarGrid::two_site(1.0, 1.0, 1.0);
        assert_column(model.two_site_column(0, 0), COLUMN_00, "column (0,0)");
        assert_column(model.two_site_column(2, 0), COLUMN_20, "column (2,0)");
        assert_column(model.two_site_column(0, 2), COLUMN_02, "column (0,2)");
    }

    #[test]
    fn periodic_fourier_is_orthogonal() {
        for n in [2usize, 3, 4, 7, 8] {
            let o = super::periodic_fourier_1d(n);
            assert_eq!(o.len(), n);
            for i in 0..n {
                for j in 0..n {
                    let dot: f64 = (0..n).map(|k| o[i][k] * o[j][k]).sum();
                    let expected = if i == j { 1.0 } else { 0.0 };
                    assert!((dot - expected).abs() < 1e-10, "n={n} ({i},{j}) dot={dot}");
                }
            }
        }
    }

    #[test]
    fn two_site_return_lies_in_analytic_interval() {
        let h = [
            [13.0 / 4.0, 7.0 / 4.0, 23.0 / 4.0],
            [7.0 / 8.0, 37.0 / 4.0, 3.0 / 2.0],
            [23.0 / 8.0, 3.0 / 2.0, 69.0 / 4.0],
        ];
        let t = 0.01;
        let a: Vec<Vec<Complex64>> = h
            .iter()
            .map(|row| row.iter().map(|&x| Complex64::new(0.0, -t * x)).collect())
            .collect();
        let id: Vec<Vec<Complex64>> = (0..3)
            .map(|i| {
                (0..3)
                    .map(|j| {
                        if i == j {
                            Complex64::new(1.0, 0.0)
                        } else {
                            Complex64::new(0.0, 0.0)
                        }
                    })
                    .collect()
            })
            .collect();
        let mul = |x: &[Vec<Complex64>], y: &[Vec<Complex64>]| -> Vec<Vec<Complex64>> {
            let n = x.len();
            let m = y[0].len();
            (0..n)
                .map(|i| {
                    (0..m)
                        .map(|j| (0..y.len()).map(|k| x[i][k] * y[k][j]).sum())
                        .collect()
                })
                .collect()
        };
        let mut term = id.clone();
        let mut sum = id;
        for k in 1..60 {
            term = mul(&term, &a);
            for row in &mut term {
                for x in row {
                    *x /= k as f64;
                }
            }
            for i in 0..3 {
                for j in 0..3 {
                    sum[i][j] += term[i][j];
                }
            }
        }
        let return_probability = sum[0][0].norm_sqr();
        let lower = 159663.0 / 160000.0;
        let upper = 39991.0 / 40000.0;
        assert!(
            (lower..=upper).contains(&return_probability),
            "return {return_probability} outside [{lower}, {upper}]"
        );

        // Full ten-row image of the same window state: the tail is the finite-window error.
        let columns = [
            [13.0 / 4.0, 7.0 / 4.0, 23.0 / 4.0],
            [7.0 / 8.0, 37.0 / 4.0, 3.0 / 2.0],
            [23.0 / 8.0, 3.0 / 2.0, 69.0 / 4.0],
            [1.0 / 8.0, 0.0, 31.0 / 8.0],
            [0.0, 0.0, 1.0 / 8.0],
            [3.0 / 4.0, 47.0 / 8.0, 31.0 / 8.0],
            [0.0, 1.0 / 8.0, 3.0 / 4.0],
            [1.0 / 8.0, 15.0 / 8.0, 0.0],
            [0.0, 3.0 / 4.0, 1.0 / 8.0],
            [0.0, 1.0 / 8.0, 0.0],
        ];
        let v = [sum[0][0], sum[1][0], sum[2][0]];
        let tail: f64 = columns[3..]
            .iter()
            .map(|row| (0..3).map(|j| row[j] * v[j]).sum::<Complex64>().norm_sqr())
            .sum();
        assert!(tail.sqrt() < 1.0, "tail {}", tail.sqrt());
    }

    #[test]
    fn periodic_grid_topology() {
        let grid = ScalarGrid::periodic(3, 2, 1, 1.0, 1.0, 1.0);
        assert_eq!(grid.sites.len(), 6);
        assert_eq!(grid.links.len(), 3 * 6);
    }

    #[test]
    fn vacuum_energy_matches_fixture() {
        let model = ScalarGrid::two_site(1.0, 1.0, 1.0);
        let vacuum = InnerVector::from([(JointInnerBasis::vacuum(), Complex64::new(1.0, 0.0))]);
        let site = model
            .site_hamiltonian()
            .apply(&vacuum, ActionLimits::default())
            .unwrap();
        let mode = model
            .two_site_mode_hamiltonian()
            .apply(&vacuum, ActionLimits::default())
            .unwrap();
        // Both frames give the fixture's Gaussian diagonal 13/4.
        assert!((site[&JointInnerBasis::vacuum()].re - 13.0 / 4.0).abs() < 1e-10);
        assert!((mode[&JointInnerBasis::vacuum()].re - 13.0 / 4.0).abs() < 1e-10);
    }
}

```

### File: `../unfer/nested_fock_algebra/src/exact_inner.rs`

**Source:** `../unfer/nested_fock_algebra/src/exact_inner.rs` (complete file, 572 lines).

```rust
//! Ordered inner CCR/CAR action and a single outer `dGamma` enclosure.
//!
//! A basis label contains both bosonic occupations and fermionic occupations.
//! Products act right to left on that *same* inner state before the outer lift.
//! No normal-ordering, scalar subtraction, occupation cutoff or amplitude pruning
//! is performed. "Exact" refers to operator algebra; coefficients and square
//! roots still use floating point and carry no interval-rounding certificate.
//!
//! This is an additive construction API. It does not identify the full physical
//! SM term ledger, select its outer statistics, or replace the legacy CAS API.

use num_complex::Complex64;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Tensor-product inner occupation label, with canonical zero-free support.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct JointInnerBasis {
    bosons: BTreeMap<u32, u32>,
    fermions: BTreeSet<u32>,
}

impl JointInnerBasis {
    pub fn vacuum() -> Self {
        Self::default()
    }

    /// Duplicate bosonic mode entries are summed; Pauli duplicates are rejected.
    pub fn new(
        bosons: impl IntoIterator<Item = (u32, u32)>,
        fermions: impl IntoIterator<Item = u32>,
    ) -> Result<Self, ActionError> {
        let mut basis = Self::vacuum();
        for (mode, n) in bosons {
            if n != 0 {
                let old = basis.bosons.get(&mode).copied().unwrap_or(0);
                basis.bosons.insert(
                    mode,
                    old.checked_add(n).ok_or(ActionError::OccupationOverflow)?,
                );
            }
        }
        for mode in fermions {
            if !basis.fermions.insert(mode) {
                return Err(ActionError::PauliOccupation);
            }
        }
        Ok(basis)
    }

    pub fn bosons(&self) -> &BTreeMap<u32, u32> {
        &self.bosons
    }

    pub fn fermions(&self) -> &BTreeSet<u32> {
        &self.fermions
    }

    pub fn total_bosons(&self) -> u64 {
        self.bosons.values().map(|&n| u64::from(n)).sum()
    }
    pub fn is_odd(&self) -> bool {
        self.fermions.len() % 2 == 1
    }
}

pub type InnerVector = BTreeMap<JointInnerBasis, Complex64>;
pub type NestedVector = BTreeMap<JointOuterBasis, Complex64>;

/// A numerical resource failure aborts the action; it never truncates the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ActionLimits {
    pub max_components: usize,
    pub max_work: usize,
}

impl Default for ActionLimits {
    fn default() -> Self {
        Self {
            max_components: 100_000,
            max_work: 10_000_000,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActionError {
    ComponentLimit { limit: usize },
    WorkLimit { limit: usize },
    OccupationOverflow,
    PauliOccupation,
    NonFiniteAmplitude,
    UnsupportedBasis,
}

impl fmt::Display for ActionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ordered nested-Fock action failed: {self:?}")
    }
}

impl std::error::Error for ActionError {}

struct Budget {
    limits: ActionLimits,
    work: usize,
}

impl Budget {
    fn tick(&mut self) -> Result<(), ActionError> {
        if self.work >= self.limits.max_work {
            return Err(ActionError::WorkLimit {
                limit: self.limits.max_work,
            });
        }
        self.work += 1;
        Ok(())
    }

    fn add<B: Ord>(
        &mut self,
        vector: &mut BTreeMap<B, Complex64>,
        basis: B,
        amplitude: Complex64,
    ) -> Result<(), ActionError> {
        self.tick()?;
        if !amplitude.re.is_finite() || !amplitude.im.is_finite() {
            return Err(ActionError::NonFiniteAmplitude);
        }
        if amplitude == Complex64::new(0.0, 0.0) {
            return Ok(());
        }
        let previous = vector.get(&basis).copied();
        if previous.is_none() && vector.len() >= self.limits.max_components {
            return Err(ActionError::ComponentLimit {
                limit: self.limits.max_components,
            });
        }
        let sum = previous.unwrap_or_default() + amplitude;
        if !sum.re.is_finite() || !sum.im.is_finite() {
            return Err(ActionError::NonFiniteAmplitude);
        }
        if sum == Complex64::new(0.0, 0.0) {
            vector.remove(&basis);
        } else {
            vector.insert(basis, sum);
        }
        Ok(())
    }

    fn validate<B: Ord>(&mut self, input: &BTreeMap<B, Complex64>) -> Result<(), ActionError> {
        if input.len() > self.limits.max_components {
            return Err(ActionError::ComponentLimit {
                limit: self.limits.max_components,
            });
        }
        for amplitude in input.values() {
            self.tick()?;
            if !amplitude.re.is_finite() || !amplitude.im.is_finite() {
                return Err(ActionError::NonFiniteAmplitude);
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InnerLadder {
    BosonCreate(u32),
    BosonAnnihilate(u32),
    FermionCreate(u32),
    FermionAnnihilate(u32),
}

impl InnerLadder {
    pub fn adjoint(self) -> Self {
        match self {
            Self::BosonCreate(m) => Self::BosonAnnihilate(m),
            Self::BosonAnnihilate(m) => Self::BosonCreate(m),
            Self::FermionCreate(m) => Self::FermionAnnihilate(m),
            Self::FermionAnnihilate(m) => Self::FermionCreate(m),
        }
    }

    fn transition(
        self,
        basis: &JointInnerBasis,
    ) -> Result<Option<(JointInnerBasis, f64)>, ActionError> {
        let mut next = basis.clone();
        let factor = match self {
            Self::BosonCreate(m) => {
                let n = basis.bosons.get(&m).copied().unwrap_or(0);
                let n1 = n.checked_add(1).ok_or(ActionError::OccupationOverflow)?;
                next.bosons.insert(m, n1);
                f64::from(n1).sqrt()
            }
            Self::BosonAnnihilate(m) => {
                let Some(&n) = basis.bosons.get(&m) else {
                    return Ok(None);
                };
                if n == 1 {
                    next.bosons.remove(&m);
                } else {
                    next.bosons.insert(m, n - 1);
                }
                f64::from(n).sqrt()
            }
            Self::FermionCreate(m) | Self::FermionAnnihilate(m) => {
                let create = matches!(self, Self::FermionCreate(_));
                if basis.fermions.contains(&m) == create {
                    return Ok(None);
                }
                let sign = if basis.fermions.range(..m).count() % 2 == 0 {
                    1.0
                } else {
                    -1.0
                };
                if create {
                    next.fermions.insert(m);
                } else {
                    next.fermions.remove(&m);
                }
                sign
            }
        };
        Ok(Some((next, factor)))
    }
}

/// Factorized polynomial in inner ladders. Product factors are written in
/// mathematical order: `Product([B,C])` applies C first, then B.
/// An empty sum is zero; an empty product and `Scalar(1)` are the inner identity.
#[derive(Clone, Debug)]
pub enum InnerExpr {
    Scalar(Complex64),
    Ladder(InnerLadder),
    Sum(Vec<Self>),
    Product(Vec<Self>),
}

impl InnerExpr {
    /// Variance-one Hermite coordinate `q = a† + a`.
    pub fn coordinate(mode: u32) -> Self {
        Self::Sum(vec![
            Self::Ladder(InnerLadder::BosonCreate(mode)),
            Self::Ladder(InnerLadder::BosonAnnihilate(mode)),
        ])
    }

    /// Same-mode conjugate momentum `p = i(a† - a)/2`, so `[q,p] = i`.
    pub fn momentum(mode: u32) -> Self {
        Self::Sum(vec![
            Self::Ladder(InnerLadder::BosonCreate(mode)).scaled(Complex64::new(0.0, 0.5)),
            Self::Ladder(InnerLadder::BosonAnnihilate(mode)).scaled(Complex64::new(0.0, -0.5)),
        ])
    }

    pub fn scaled(self, coefficient: Complex64) -> Self {
        Self::Product(vec![Self::Scalar(coefficient), self])
    }

    pub fn adjoint(&self) -> Self {
        match self {
            Self::Scalar(c) => Self::Scalar(c.conj()),
            Self::Ladder(l) => Self::Ladder(l.adjoint()),
            Self::Sum(terms) => Self::Sum(terms.iter().map(Self::adjoint).collect()),
            Self::Product(factors) => {
                Self::Product(factors.iter().rev().map(Self::adjoint).collect())
            }
        }
    }

    pub fn apply(
        &self,
        input: &InnerVector,
        limits: ActionLimits,
    ) -> Result<InnerVector, ActionError> {
        let mut budget = Budget { limits, work: 0 };
        budget.validate(input)?;
        self.apply_with_budget(input, &mut budget)
    }

    fn apply_with_budget(
        &self,
        input: &InnerVector,
        budget: &mut Budget,
    ) -> Result<InnerVector, ActionError> {
        budget.tick()?;
        match self {
            Self::Scalar(c) => {
                // Reject invalid coefficients even when the input is zero.
                if !c.re.is_finite() || !c.im.is_finite() {
                    return Err(ActionError::NonFiniteAmplitude);
                }
                let mut out = InnerVector::new();
                for (b, a) in input {
                    budget.add(&mut out, b.clone(), c * a)?;
                }
                Ok(out)
            }
            Self::Ladder(ladder) => {
                let mut out = InnerVector::new();
                for (b, a) in input {
                    budget.tick()?;
                    if let Some((next, factor)) = ladder.transition(b)? {
                        budget.add(&mut out, next, a * factor)?;
                    }
                }
                Ok(out)
            }
            Self::Sum(terms) => {
                let mut out = InnerVector::new();
                for term in terms {
                    for (b, a) in term.apply_with_budget(input, budget)? {
                        budget.add(&mut out, b, a)?;
                    }
                }
                Ok(out)
            }
            Self::Product(factors) => {
                let mut current = input.clone();
                for factor in factors.iter().rev() {
                    current = factor.apply_with_budget(&current, budget)?;
                }
                Ok(current)
            }
        }
    }

    /// Apply `sum_ij h_ij C†_i A_j` after completing the entire inner action.
    /// Scalar inner expressions therefore give `c N_out`, not `c I_out`.
    /// Symmetric, antisymmetric and parity-graded outer statistics are supported.
    /// Physical Hilbert/core identification remains a separate proof obligation.
    pub fn d_gamma(
        &self,
        input: &NestedVector,
        limits: ActionLimits,
    ) -> Result<NestedVector, ActionError> {
        let mut budget = Budget { limits, work: 0 };
        budget.validate(input)?;
        let mut out = NestedVector::new();
        // Apply the factorized inner expression to a whole one-particle vector,
        // rather than separately expanding the image of every occupied label.
        // Bosonic and fermionic outer statistics remain separate summands.
        if input.keys().all(|outer| outer.particle_number() <= 1) {
            for statistics in [0, 1, 2] {
                let mut inner = InnerVector::new();
                for (outer, amplitude) in input {
                    let category = match outer {
                        JointOuterBasis::Bosonic(_) => 0,
                        JointOuterBasis::Fermionic(_) => 1,
                        JointOuterBasis::Graded(_) => 2,
                    };
                    if category == statistics {
                        if let Some(source) = outer.occupied().next() {
                            budget.add(&mut inner, source.clone(), *amplitude)?;
                        }
                    }
                }
                if inner.is_empty() {
                    continue;
                }
                for (target, amplitude) in self.apply_with_budget(&inner, &mut budget)? {
                    let outer = match statistics {
                        0 => JointOuterBasis::bosonic([(target, 1)])?,
                        1 => JointOuterBasis::fermionic([target])?,
                        _ => JointOuterBasis::graded([(target, 1)])?,
                    };
                    budget.add(&mut out, outer, amplitude)?;
                }
            }
            return Ok(out);
        }
        for (outer, amplitude) in input {
            for source in outer.occupied() {
                budget.tick()?;
                let basis_vector = InnerVector::from([(source.clone(), Complex64::new(1.0, 0.0))]);
                let image = self.apply_with_budget(&basis_vector, &mut budget)?;
                for (target, coefficient) in image {
                    if let Some((next, factor)) = outer.transition(source, &target)? {
                        budget.add(&mut out, next, amplitude * coefficient * factor)?;
                    }
                }
            }
        }
        Ok(out)
    }
}

/// Symmetric, antisymmetric or parity-graded Fock space over the joint inner basis.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum JointOuterBasis {
    Bosonic(BosonicOccupations),
    Fermionic(FermionicOccupations),
    Graded(GradedOccupations),
}

/// Private support prevents explicit zero occupations and overflow aliases.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct BosonicOccupations(BTreeMap<JointInnerBasis, u32>);

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct FermionicOccupations(BTreeSet<JointInnerBasis>);

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct GradedOccupations {
    even: BosonicOccupations,
    odd: FermionicOccupations,
}

impl JointOuterBasis {
    /// Even inner configurations obey CCR outer statistics, odd configurations
    /// CAR outer statistics. Inner parity is never confused with outer number.
    pub fn graded(
        input: impl IntoIterator<Item = (JointInnerBasis, u32)>,
    ) -> Result<Self, ActionError> {
        let mut occupations = GradedOccupations::default();
        for (b, n) in input {
            if n == 0 {
                continue;
            }
            if b.is_odd() {
                if n != 1 || !occupations.odd.0.insert(b) {
                    return Err(ActionError::PauliOccupation);
                }
            } else {
                let old = occupations.even.0.get(&b).copied().unwrap_or(0);
                occupations.even.0.insert(
                    b,
                    old.checked_add(n).ok_or(ActionError::OccupationOverflow)?,
                );
            }
        }
        Ok(Self::Graded(occupations))
    }
    pub fn bosonic(
        input: impl IntoIterator<Item = (JointInnerBasis, u32)>,
    ) -> Result<Self, ActionError> {
        let mut occupations = BTreeMap::<JointInnerBasis, u32>::new();
        for (b, n) in input {
            if n != 0 {
                let old = occupations.get(&b).copied().unwrap_or(0);
                occupations.insert(
                    b,
                    old.checked_add(n).ok_or(ActionError::OccupationOverflow)?,
                );
            }
        }
        Ok(Self::Bosonic(BosonicOccupations(occupations)))
    }

    pub fn fermionic(
        input: impl IntoIterator<Item = JointInnerBasis>,
    ) -> Result<Self, ActionError> {
        let mut occupations = BTreeSet::new();
        for b in input {
            if !occupations.insert(b) {
                return Err(ActionError::PauliOccupation);
            }
        }
        Ok(Self::Fermionic(FermionicOccupations(occupations)))
    }

    pub fn particle_number(&self) -> u64 {
        match self {
            Self::Bosonic(ns) => ns.0.values().map(|&n| u64::from(n)).sum(),
            Self::Fermionic(ns) => ns.0.len() as u64,
            Self::Graded(ns) => {
                ns.even.0.values().map(|&n| u64::from(n)).sum::<u64>() + ns.odd.0.len() as u64
            }
        }
    }

    /// Read-only joint labels/counts; this does not flatten the tensor factor.
    pub fn inner_occupations(&self) -> Vec<(&JointInnerBasis, u32)> {
        match self {
            Self::Bosonic(ns) => ns.0.iter().map(|(b, &n)| (b, n)).collect(),
            Self::Fermionic(ns) => ns.0.iter().map(|b| (b, 1)).collect(),
            Self::Graded(ns) => ns
                .even
                .0
                .iter()
                .map(|(b, &n)| (b, n))
                .chain(ns.odd.0.iter().map(|b| (b, 1)))
                .collect(),
        }
    }

    fn occupied(&self) -> Box<dyn Iterator<Item = &JointInnerBasis> + '_> {
        match self {
            Self::Bosonic(ns) => Box::new(ns.0.keys()),
            Self::Fermionic(ns) => Box::new(ns.0.iter()),
            Self::Graded(ns) => Box::new(ns.even.0.keys().chain(ns.odd.0.iter())),
        }
    }

    fn transition(
        &self,
        source: &JointInnerBasis,
        target: &JointInnerBasis,
    ) -> Result<Option<(Self, f64)>, ActionError> {
        match self {
            Self::Graded(ns) => {
                let mut next = ns.clone();
                let mut factor = if source.is_odd() {
                    let sign = if next.odd.0.range(..source).count() % 2 == 0 {
                        1.0
                    } else {
                        -1.0
                    };
                    next.odd.0.remove(source);
                    sign
                } else {
                    let n = next.even.0[source];
                    if n == 1 {
                        next.even.0.remove(source);
                    } else {
                        next.even.0.insert(source.clone(), n - 1);
                    }
                    f64::from(n).sqrt()
                };
                if target.is_odd() {
                    if next.odd.0.contains(target) {
                        return Ok(None);
                    }
                    if next.odd.0.range(..target).count() % 2 == 1 {
                        factor *= -1.0;
                    }
                    next.odd.0.insert(target.clone());
                } else {
                    let n = next.even.0.get(target).copied().unwrap_or(0);
                    let n1 = n.checked_add(1).ok_or(ActionError::OccupationOverflow)?;
                    next.even.0.insert(target.clone(), n1);
                    factor *= f64::from(n1).sqrt();
                }
                Ok(Some((Self::Graded(next), factor)))
            }
            Self::Bosonic(ns) => {
                let n = ns.0[source];
                let mut next = ns.clone();
                if n == 1 {
                    next.0.remove(source);
                } else {
                    next.0.insert(source.clone(), n - 1);
                }
                let m = next.0.get(target).copied().unwrap_or(0);
                let m1 = m.checked_add(1).ok_or(ActionError::OccupationOverflow)?;
                next.0.insert(target.clone(), m1);
                Ok(Some((
                    Self::Bosonic(next),
                    f64::from(n).sqrt() * f64::from(m1).sqrt(),
                )))
            }
            Self::Fermionic(ns) => {
                let n_before = ns.0.range(..source).count();
                let mut next = ns.clone();
                next.0.remove(source);
                if next.0.contains(target) {
                    return Ok(None);
                }
                let m_before = next.0.range(..target).count();
                let sign = if (n_before + m_before) % 2 == 0 {
                    1.0
                } else {
                    -1.0
                };
                next.0.insert(target.clone());
                Ok(Some((Self::Fermionic(next), sign)))
            }
        }
    }
}

```

### Dependency excerpt: `../unfer/fock_sirk/src/joint_sirk.rs` — options, result and solve entry points

**Source:** `../unfer/fock_sirk/src/joint_sirk.rs`, lines 44–112, 298–437, 699–723.
The omitted ranges are the finite-window cache, GMRES internals, the evolution loop and
the harness code.

```rust
pub struct JointSirkOptions {
    pub max_cached_components: usize,
    pub method: JointKrylovMethod,
    pub action_limits: ActionLimits,
    pub gram_relative_tolerance: f64,
    pub hermiticity_tolerance: f64,
    pub unit_norm_steps: bool,
    /// Sum of all retained inner bosonic occupations, across outer particles.
    /// This is an explicit numerical compression, never a deleted interaction.
    pub occupation_cutoff: Option<u64>,
    /// Optional independently declared finite basis window. Tail action is
    /// measured against the full operator, including omitted basis labels.
    pub basis_window: Option<BTreeSet<JointOuterBasis>>,
}

impl Default for JointSirkOptions {
    fn default() -> Self {
        Self {
            max_cached_components: 1_000_000,
            method: JointKrylovMethod::ShiftInvert {
                relative_tolerance: 1e-10,
                max_iterations: 48,
            },
            action_limits: ActionLimits::default(),
            gram_relative_tolerance: 1e-12,
            hermiticity_tolerance: 1e-9,
            unit_norm_steps: true,
            occupation_cutoff: None,
            basis_window: None,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct JointStateDictionary {
    labels: Vec<JointOuterBasis>,
    indices: BTreeMap<JointOuterBasis, usize>,
}
impl JointStateDictionary {
    pub fn register(&mut self, state: &NestedVector) {
        for basis in state.keys() {
            if !self.indices.contains_key(basis) {
                let index = self.labels.len();
                self.labels.push(basis.clone());
                self.indices.insert(basis.clone(), index);
            }
        }
    }
    pub fn len(&self) -> usize {
        self.labels.len()
    }
    pub fn is_empty(&self) -> bool {
        self.labels.is_empty()
    }
    pub fn is_bijective(&self) -> bool {
        self.labels.len() == self.indices.len()
            && self
                .labels
                .iter()
                .enumerate()
                .all(|(i, b)| self.indices.get(b) == Some(&i))
    }
    pub fn index(&self, b: &JointOuterBasis) -> Option<usize> {
        self.indices.get(b).copied()
    }
    pub fn basis(&self, i: usize) -> Option<&JointOuterBasis> {
        self.labels.get(i)
    }
}

```

*Lines 113–297 omitted.*

```rust
#[derive(Debug)]
pub struct JointSirkResult {
    pub h_proj: DMatrix<C>,
    /// Paper's bounded-resolvent compression B=V†(gamma+iH)^-1 V.
    pub projected_resolvent: Option<DMatrix<C>>,
    /// gamma I-B^-1 for rational SIRK; -i H_proj for the separately labeled
    /// forward/Galerkin diagnostic. The two projections generally differ.
    pub function_generator: DMatrix<C>,
    pub function_solve_error_bounds: Vec<f64>,
    pub gram: DMatrix<C>,
    pub whitening: DMatrix<C>,
    pub registry: JointStateDictionary,
    pub sequence: Vec<NestedVector>,
    /// Full H u_j, before occupation projection.
    pub full_images: Vec<NestedVector>,
    /// Reorthogonalized physical vectors avoid ill-conditioned Gram-coordinate
    /// cancellation in reconstruction and operator compression.
    pub orthonormal_basis: Vec<NestedVector>,
    pub orthonormal_images: Vec<NestedVector>,
    pub orthogonality_defect: f64,
    pub scales: Vec<f64>,
    pub shifts: Vec<C>,
    pub projected_action_tail_norms: Vec<f64>,
    pub hermiticity_defect: f64,
    /// Full shifted residuals divided by |Im z|. For a self-adjoint full H
    /// this bounds solve error, including occupation-projection error; no
    /// rounding enclosure is claimed. Empty for forward-product diagnostics.
    pub shift_solve_error_bounds: Vec<f64>,
    pub options: JointSirkOptions,
    pub cached_components: usize,
}

impl JointSirkResult {
    pub fn rank(&self) -> usize {
        self.h_proj.nrows()
    }
    fn initial_coefficients(&self) -> DVector<C> {
        DVector::from_iterator(
            self.rank(),
            self.orthonormal_basis
                .iter()
                .map(|v| joint_inner_product(v, &self.sequence[0])),
        )
    }
    pub fn time_evolve(&self, time: f64) -> Result<DVector<C>, JointSirkError> {
        if !time.is_finite() {
            return Err(JointSirkError::Invalid("nonfinite evolution time".into()));
        }
        Ok((self.function_generator.clone() * C::new(time, 0.0)).exp()
            * self.initial_coefficients())
    }
    pub fn reconstruct(&self, coefficients: &DVector<C>) -> Result<NestedVector, JointSirkError> {
        if coefficients.len() != self.rank() {
            return Err(JointSirkError::Invalid("coefficient dimension".into()));
        }
        let mut out = NestedVector::new();
        for (j, &c) in coefficients.iter().enumerate() {
            joint_axpy(
                &mut out,
                &self.orthonormal_basis[j],
                c,
                self.options.action_limits,
            )?;
        }
        Ok(out)
    }
    /// (Ritz value, absolute full-operator residual, state norm). No ordering
    /// or unseen-spectrum certificate is inferred from these finite windows.
    pub fn ritz_residuals(&self) -> Result<Vec<(f64, f64, f64)>, JointSirkError> {
        let eig = self.h_proj.clone().symmetric_eigen();
        let mut out = Vec::new();
        for i in 0..self.rank() {
            let theta = eig.eigenvalues[i];
            let c = eig.eigenvectors.column(i).into_owned();
            let state = self.reconstruct(&c)?;
            let mut residual = NestedVector::new();
            for (j, &x) in c.iter().enumerate() {
                joint_axpy(
                    &mut residual,
                    &self.orthonormal_images[j],
                    x,
                    self.options.action_limits,
                )?;
            }
            joint_axpy(
                &mut residual,
                &state,
                C::new(-theta, 0.0),
                self.options.action_limits,
            )?;
            out.push((theta, joint_norm(&residual), joint_norm(&state)));
        }
        out.sort_by(|a, b| a.0.total_cmp(&b.0));
        Ok(out)
    }
}

pub fn solve_joint_sirk(
    h: &InnerExpr,
    initial: &NestedVector,
    shifts: &[C],
    options: &JointSirkOptions,
) -> Result<JointSirkResult, JointSirkError> {
    if let Some(window) = &options.basis_window {
        let cache = FiniteWindowAction::build(h, window, options)?;
        let mut result = solve_joint_sirk_with_actions(
            |v| cache.full(v, options.action_limits),
            |v| cache.projected(v, options.action_limits),
            initial,
            shifts,
            options,
        )?;
        result.cached_components = cache.components;
        return Ok(result);
    }
    solve_joint_sirk_with_matvec(
        |v| h.d_gamma(v, options.action_limits),
        initial,
        shifts,
        options,
    )
}

pub fn solve_joint_sirk_with_matvec<F>(
    matvec: F,
    initial: &NestedVector,
    shifts: &[C],
    options: &JointSirkOptions,
) -> Result<JointSirkResult, JointSirkError>
where
    F: Fn(&NestedVector) -> Result<NestedVector, ActionError>,
{
    solve_joint_sirk_with_actions(
        &matvec,
        |v| Ok(project_joint(&matvec(v)?, options).0),
        initial,
        shifts,
        options,
    )
}

```

*Lines 438–698 omitted.*

```rust
/// Positive gamma_j=(budget-j*spacing)/time, j=1..m, for A=-iH corresponds to
/// z_j=i gamma_j in the H forward products. This checks the positive shift
/// budget; it does not assert the function/numerical-range theorem hypotheses.
pub fn hashimoto_unitary_shifts(
    time: f64,
    budget: f64,
    spacing: f64,
    count: usize,
) -> Result<Vec<C>, JointSirkError> {
    if !time.is_finite()
        || time <= 0.0
        || !budget.is_finite()
        || !spacing.is_finite()
        || spacing <= 0.0
        || count == 0
        || budget <= count as f64 * spacing
    {
        return Err(JointSirkError::Invalid(
            "Hashimoto requires t>0, spacing>0, and count<budget/spacing".into(),
        ));
    }
    Ok((0..count)
        .map(|j| C::new(0.0, (budget - (j + 1) as f64 * spacing) / time))
        .collect())
}

```

### Implementation excerpt: `../unfer/fock_sirk/src/joint_sirk.rs` — rational Krylov core

**Source:** `../unfer/fock_sirk/src/joint_sirk.rs`, lines 439–697 and 725–811.
This is the Hashimoto shift-invert rational Krylov implementation: the shifted-solve
basis, Gram/whitening compression, bounded-resolvent generator and shifted GMRES.

```rust
fn solve_joint_sirk_with_actions<F, P>(
    matvec: F,
    projected_matvec: P,
    initial: &NestedVector,
    shifts: &[C],
    options: &JointSirkOptions,
) -> Result<JointSirkResult, JointSirkError>
where
    F: Fn(&NestedVector) -> Result<NestedVector, ActionError>,
    P: Fn(&NestedVector) -> Result<NestedVector, ActionError>,
{
    let m = shifts.len();
    if m == 0
        || !joint_norm(initial).is_finite()
        || joint_norm(initial) == 0.0
        || shifts
            .iter()
            .any(|z| !z.re.is_finite() || !z.im.is_finite())
        || !options.gram_relative_tolerance.is_finite()
        || options.gram_relative_tolerance <= 0.0
        || options.gram_relative_tolerance >= 1.0
        || !options.hermiticity_tolerance.is_finite()
        || options.hermiticity_tolerance <= 0.0
    {
        return Err(JointSirkError::Invalid(
            "nonzero finite input, positive tolerances and nonempty finite shifts required".into(),
        ));
    }
    if !project_joint(initial, options).1.is_empty() {
        return Err(JointSirkError::Invalid(
            "initial state lies outside the declared numerical window".into(),
        ));
    }
    let mut checked = NestedVector::new();
    joint_axpy(
        &mut checked,
        initial,
        C::new(1.0, 0.0),
        options.action_limits,
    )?;
    let mut sequence = vec![checked];
    let mut images = Vec::new();
    let mut tails = Vec::new();
    let mut scales = vec![1.0];
    let mut solve_bounds = Vec::new();
    for (k, &shift) in shifts.iter().enumerate() {
        let image = matvec(&sequence[k])?;
        let mut validated = NestedVector::new();
        joint_axpy(
            &mut validated,
            &image,
            C::new(1.0, 0.0),
            options.action_limits,
        )?;
        let (projected, tail) = project_joint(&validated, options);
        tails.push(joint_norm(&tail));
        images.push(validated);
        let next = match options.method {
            JointKrylovMethod::ForwardProducts => {
                let mut next = projected;
                joint_axpy(&mut next, &sequence[k], -shift, options.action_limits)?;
                next
            }
            JointKrylovMethod::ShiftInvert {
                relative_tolerance,
                max_iterations,
            } => {
                let (solution, bound) = gmres_shift(
                    &matvec,
                    &projected_matvec,
                    &sequence[k],
                    shift,
                    options,
                    relative_tolerance,
                    max_iterations,
                )?;
                solve_bounds.push(bound);
                solution
            }
        };
        let norm = joint_norm(&next);
        if !norm.is_finite() {
            return Err(JointSirkError::Invalid("nonfinite forward sequence".into()));
        }
        if options.unit_norm_steps && norm > 0.0 {
            let mut normalized = NestedVector::new();
            joint_axpy(
                &mut normalized,
                &next,
                C::new(1.0 / norm, 0.0),
                options.action_limits,
            )?;
            scales.push(norm);
            sequence.push(normalized);
        } else {
            scales.push(1.0);
            sequence.push(next);
        }
    }
    let mut registry = JointStateDictionary::default();
    for state in &sequence {
        registry.register(state);
    }
    if !registry.is_bijective() {
        return Err(JointSirkError::Invalid(
            "joint registry aliases basis labels".into(),
        ));
    }
    let mut gram = DMatrix::<C>::zeros(m + 1, m + 1);
    for j in 0..=m {
        for k in 0..=m {
            gram[(j, k)] = joint_inner_product(&sequence[j], &sequence[k]);
        }
    }
    if gram.iter().any(|x| !x.re.is_finite() || !x.im.is_finite()) {
        return Err(JointSirkError::Invalid("nonfinite Gram matrix".into()));
    }
    let gsub = gram.view((0, 0), (m, m)).into_owned();
    let mut whitening = whiten_gram(&gsub, options.gram_relative_tolerance)?.w;
    let rank = whitening.ncols();
    let mut orthonormal = Vec::<NestedVector>::new();
    for i in 0..rank {
        let mut vector = NestedVector::new();
        for j in 0..m {
            joint_axpy(
                &mut vector,
                &sequence[j],
                whitening[(j, i)],
                options.action_limits,
            )?;
        }
        for _ in 0..2 {
            for k in 0..i {
                let coefficient = joint_inner_product(&orthonormal[k], &vector);
                joint_axpy(
                    &mut vector,
                    &orthonormal[k],
                    -coefficient,
                    options.action_limits,
                )?;
                for j in 0..m {
                    let previous = whitening[(j, k)];
                    whitening[(j, i)] -= previous * coefficient;
                }
            }
        }
        let norm = joint_norm(&vector);
        if !norm.is_finite() || norm < 1e-10 {
            return Err(JointSirkError::Invalid(
                "unstable physical Gram direction".into(),
            ));
        }
        let mut normalized = NestedVector::new();
        joint_axpy(
            &mut normalized,
            &vector,
            C::new(1.0 / norm, 0.0),
            options.action_limits,
        )?;
        for j in 0..m {
            whitening[(j, i)] /= norm;
        }
        orthonormal.push(normalized);
    }
    let mut orthogonality_defect = 0.0_f64;
    for i in 0..rank {
        for j in 0..rank {
            orthogonality_defect = orthogonality_defect.max(
                (joint_inner_product(&orthonormal[i], &orthonormal[j])
                    - C::new(if i == j { 1.0 } else { 0.0 }, 0.0))
                .norm(),
            );
        }
    }
    let mut orthonormal_images = Vec::new();
    for v in &orthonormal {
        registry.register(v);
        let image = matvec(v)?;
        let mut checked = NestedVector::new();
        joint_axpy(
            &mut checked,
            &image,
            C::new(1.0, 0.0),
            options.action_limits,
        )?;
        orthonormal_images.push(checked);
    }
    let mut reduced = DMatrix::<C>::zeros(rank, rank);
    for j in 0..rank {
        for k in 0..rank {
            reduced[(j, k)] = joint_inner_product(&orthonormal[j], &orthonormal_images[k]);
        }
    }
    let defect = (&reduced - reduced.adjoint()).norm() / reduced.norm().max(1.0);
    if !defect.is_finite() || defect > options.hermiticity_tolerance {
        return Err(JointSirkError::NonHermitian(defect));
    }
    let h_proj = (&reduced + reduced.adjoint()) * C::new(0.5, 0.0);
    let (projected_resolvent, function_generator, function_bounds) = match options.method {
        JointKrylovMethod::ForwardProducts => {
            (None, h_proj.clone() * C::new(0.0, -1.0), Vec::new())
        }
        JointKrylovMethod::ShiftInvert {
            relative_tolerance,
            max_iterations,
        } => {
            if shifts.iter().any(|z| z.re != 0.0 || z.im <= 0.0) {
                return Err(JointSirkError::Invalid(
                    "Hashimoto A=-iH requires z=i gamma with gamma>0".into(),
                ));
            }
            let shift = shifts[m - 1];
            let gamma = shift.im;
            let mut bounded = DMatrix::<C>::zeros(rank, rank);
            let mut bounds = Vec::new();
            for j in 0..rank {
                let (inverse, bound) = gmres_shift(
                    &matvec,
                    &projected_matvec,
                    &orthonormal[j],
                    shift,
                    options,
                    relative_tolerance,
                    max_iterations,
                )?;
                bounds.push(bound);
                for i in 0..rank {
                    bounded[(i, j)] = -C::i() * joint_inner_product(&orthonormal[i], &inverse);
                }
            }
            let inverse = bounded.clone().try_inverse().ok_or_else(|| {
                JointSirkError::Invalid("singular bounded-resolvent compression".into())
            })?;
            let generator = DMatrix::<C>::identity(rank, rank) * C::new(gamma, 0.0) - inverse;
            (Some(bounded), generator, bounds)
        }
    };
    Ok(JointSirkResult {
        h_proj,
        projected_resolvent,
        function_generator,
        function_solve_error_bounds: function_bounds,
        gram,
        whitening,
        registry,
        sequence,
        orthonormal_basis: orthonormal,
        orthonormal_images,
        orthogonality_defect,
        full_images: images,
        scales,
        shifts: shifts.to_vec(),
        projected_action_tail_norms: tails,
        hermiticity_defect: defect,
        shift_solve_error_bounds: solve_bounds,
        options: options.clone(),
        cached_components: 0,
    })
}

```

*Lines 698–724 omitted.*

```rust
fn gmres_shift<F, P>(
    matvec: &F,
    projected_matvec: &P,
    rhs: &NestedVector,
    shift: C,
    options: &JointSirkOptions,
    tolerance: f64,
    iterations: usize,
) -> Result<(NestedVector, f64), JointSirkError>
where
    F: Fn(&NestedVector) -> Result<NestedVector, ActionError>,
    P: Fn(&NestedVector) -> Result<NestedVector, ActionError>,
{
    if !tolerance.is_finite()
        || tolerance <= 0.0
        || tolerance >= 1.0
        || iterations == 0
        || shift.im == 0.0
    {
        return Err(JointSirkError::Invalid(
            "nonreal shifts, positive solve tolerance and iteration budget required".into(),
        ));
    }
    let beta = joint_norm(rhs);
    if beta == 0.0 {
        return Ok((NestedVector::new(), 0.0));
    }
    let limits = options.action_limits;
    let mut first = NestedVector::new();
    joint_axpy(&mut first, rhs, C::new(1.0 / beta, 0.0), limits)?;
    let mut basis = vec![first];
    let mut h = DMatrix::<C>::zeros(iterations + 1, iterations);
    let mut last_residual = f64::INFINITY;
    for k in 0..iterations {
        let image = projected_matvec(&basis[k])?;
        let mut w = NestedVector::new();
        joint_axpy(&mut w, &image, C::new(1.0, 0.0), limits)?;
        joint_axpy(&mut w, &basis[k], -shift, limits)?;
        // Two passes of modified Gram-Schmidt, preserving tiny support entries.
        for _ in 0..2 {
            for j in 0..=k {
                let coefficient = joint_inner_product(&basis[j], &w);
                h[(j, k)] += coefficient;
                joint_axpy(&mut w, &basis[j], -coefficient, limits)?;
            }
        }
        let next_norm = joint_norm(&w);
        h[(k + 1, k)] = C::new(next_norm, 0.0);
        let small = h.view((0, 0), (k + 2, k + 1)).into_owned();
        let mut target = DVector::<C>::zeros(k + 2);
        target[0] = C::new(beta, 0.0);
        let coefficients = small
            .clone()
            .svd(true, true)
            .solve(&target, 1e-14)
            .map_err(|e| JointSirkError::Invalid(format!("GMRES least squares: {e}")))?;
        let estimated = (&small * &coefficients - &target).norm() / beta;
        if estimated <= tolerance || k + 1 == iterations || next_norm <= 1e-14 {
            let mut solution = NestedVector::new();
            for (j, &c) in coefficients.iter().enumerate() {
                joint_axpy(&mut solution, &basis[j], c, limits)?;
            }
            let mut residual = matvec(&solution)?;
            joint_axpy(&mut residual, &solution, -shift, limits)?;
            joint_axpy(&mut residual, rhs, C::new(-1.0, 0.0), limits)?;
            let full_norm = joint_norm(&residual);
            let compressed = project_joint(&residual, options).0;
            last_residual = joint_norm(&compressed) / beta;
            if last_residual <= tolerance {
                return Ok((solution, full_norm / shift.im.abs()));
            }
            if next_norm <= 1e-14 {
                break;
            }
        }
        if next_norm == 0.0 || !next_norm.is_finite() {
            break;
        }
        let mut normalized = NestedVector::new();
        joint_axpy(&mut normalized, &w, C::new(1.0 / next_norm, 0.0), limits)?;
        basis.push(normalized);
    }
    Err(JointSirkError::ShiftSolve {
        residual: last_residual,
        iterations,
    })
}

```

### Dependency excerpt: `../unfer/fock_sirk/src/sm_defect.rs` — defect terms and the point certificate

**Source:** `../unfer/fock_sirk/src/sm_defect.rs`, lines 1–32, 167–205, 322–372.
The omitted ranges are interval arithmetic and JSON serialization.

```rust
//! N8: finite-map defect certificate for the compressed rational flow.
//!
//! For an isometric basis `V`, reduced generator `G` and full columns `HV`,
//! define `D = i V G - H V`. Then
//!
//! ```text
//! ||exp(-itH) psi - V exp(tG) V* psi||
//!   <= ||psi - V V* psi|| + integral_0^t ||D exp(sG) V* psi|| ds
//!   <= leakage + t ||D|| ||V* psi|| exp(omega_+ t),
//! ```
//!
//! where `omega_+ = max(0, lambda_max(Re G))` covers the returned inexact
//! generator. The `f64` path is a measured estimate. [`interval_terms`] repeats
//! it with directed `f64` endpoints, encloses `G = V* H V` from the declared
//! `H` and `V`, and applies a Gershgorin bound to the enclosed Hermitian part.
//! Its `hi` endpoint is therefore a directed bound on the declared finite
//! matrices, but still not a certified enclosure of a physical reduction. The
//! separately measured map error uses nalgebra's Padé exponential and is only a
//! diagnostic witness. Neither path is an unconditional physical-SM certificate:
//! the self-adjoint operator, the physical reduction, and the matrix-specific
//! defect bound remain assumptions.

use crate::sm_bridge::{bind_artifact, canonical_json_sha256, sha256_hex};
use nalgebra::{DMatrix, DVector};
use nested_fock_algebra::exact_inner::NestedVector;
use num_complex::Complex64 as C;
use serde_json::{Map, Value, json};
use std::collections::BTreeMap;

pub const DEFECT_SCHEMA: &str = "sm-defect-certificate/v1";

const SM_DEFECT_PROOF: &[u8] = include_bytes!("../../docs/fixtures/sm_defect_proof.ndjson");

```

*Lines 33–166 omitted.*

```rust
#[derive(Clone, Debug)]
pub struct DefectTerms {
    pub initial_leakage: f64,
    pub defect_frobenius: f64,
    /// `||D c||` for the projected seed coefficients, rather than the
    /// worst-case full-column Frobenius norm. This is a diagnostic; the
    /// certified bound still uses `defect_frobenius`.
    pub defect_seed_action: f64,
    /// Upper bound on `sup_{0<=s<=time} ||D exp(sG) c||`, from a grid plus a
    /// Lipschitz correction using `||D G||_F ||c|| exp(omega_+ time)`.
    pub defect_action_envelope: f64,
    /// `leakage + time * defect_action_envelope`: the state-dependent
    /// alternative to `evolution_bound`. Point f64; exact `exp`/`G` remain
    /// assumptions, so this is not a certified enclosure.
    pub state_weighted_bound: f64,
    pub seed_norm: f64,
    pub reduced_growth: f64,
    pub flow_growth: f64,
    pub time: f64,
    pub evolution_bound: f64,
}

impl DefectTerms {
    pub fn to_json(&self, extra: Value) -> Value {
        json!({
            "initial_leakage": self.initial_leakage,
            "defect_frobenius": self.defect_frobenius,
            "defect_seed_action": self.defect_seed_action,
            "defect_action_envelope": self.defect_action_envelope,
            "state_weighted_bound": self.state_weighted_bound,
            "seed_norm": self.seed_norm,
            "reduced_growth": self.reduced_growth,
            "flow_growth": self.flow_growth,
            "time": self.time,
            "evolution_bound": self.evolution_bound,
            "extra": extra,
        })
    }
}

```

*Lines 206–321 omitted.*

```rust
/// Point (non-enclosed) defect terms for the actual returned solve.
pub fn defect_terms(
    basis: &[NestedVector],
    full_images: &[NestedVector],
    generator: &DMatrix<C>,
    state: &NestedVector,
    time: f64,
) -> DefectTerms {
    let coefficients: DVector<C> =
        DVector::from_iterator(basis.len(), basis.iter().map(|vector| inner(vector, state)));
    let mut projected = NestedVector::new();
    for (vector, coefficient) in basis.iter().zip(coefficients.iter()) {
        add_scaled(&mut projected, vector, *coefficient);
    }
    let mut residual = state.clone();
    for (basis, amplitude) in &projected {
        let value = residual.entry(basis.clone()).or_default();
        *value -= *amplitude;
    }
    residual.retain(|_, amplitude| *amplitude != C::new(0.0, 0.0));
    let leakage = joint_norm(&residual);
    let seed = coefficients
        .iter()
        .map(|c| c.norm_sqr())
        .sum::<f64>()
        .sqrt();
    let defect = defect_frobenius(basis, full_images, generator);
    let seed_action = joint_norm(&defect_action(
        basis,
        full_images,
        generator,
        coefficients.as_slice(),
    ));
    let action_envelope =
        defect_action_envelope(basis, full_images, generator, coefficients.as_slice(), time);
    let growth = reduced_growth(generator).max(0.0);
    let flow = (growth * time).exp();
    DefectTerms {
        initial_leakage: leakage,
        defect_frobenius: defect,
        defect_seed_action: seed_action,
        defect_action_envelope: action_envelope,
        state_weighted_bound: leakage + time * action_envelope,
        seed_norm: seed,
        reduced_growth: growth,
        flow_growth: flow,
        time,
        evolution_bound: leakage + time * defect * seed * flow,
    }
}

```

### File: `../unfer/fock_sirk/examples/anharmonic_oscillator.rs`

**Source:** `../unfer/fock_sirk/examples/anharmonic_oscillator.rs` (complete file, 56 lines).

```rust
use fock_sirk::solve_forward_sirk;
use nested_fock_algebra::{
    Expression, InnerBosonicState, Operator, QuantumState, compile_expression,
    symengine::quantum::operators::{momentum_operator, position_operator},
};
use num_complex::Complex64;

fn main() -> anyhow::Result<()> {
    // 1. Define Physics: Anharmonic Oscillator
    let x_lib = position_operator();
    let p_lib = momentum_operator();

    // Map library internal symbols "a"/"a_dag" to our "a_0"/"c_0"
    let x = x_lib
        .substitute(&Expression::symbol("a"), &Expression::symbol("a_0"))
        .substitute(&Expression::symbol("a_dag"), &Expression::symbol("c_0"));
    let p = p_lib
        .substitute(&Expression::symbol("a"), &Expression::symbol("a_0"))
        .substitute(&Expression::symbol("a_dag"), &Expression::symbol("c_0"));

    let lambda = 0.1;
    let h_expr = (p.clone().pow(&Expression::int(2)) / Expression::from(2.0))
        + (x.clone().pow(&Expression::int(2)) / Expression::from(2.0))
        + (Expression::from(lambda) * x.pow(&Expression::int(4)));

    println!("Anharmonic Oscillator Hamiltonian (Symbolic): {}", h_expr);
    let hamiltonian = compile_expression(h_expr);

    // 2. Define Initial State
    let initial_state =
        QuantumState::vacuum().apply(&Operator::OuterBosonCreate(InnerBosonicState::vacuum()));

    // 3. Define Shifts
    let m_dim = 6;
    let shifts: Vec<Complex64> = (0..m_dim)
        .map(|j| Complex64::new(0.0, 1.0 + (j as f64) * 0.2))
        .collect();

    // 4. Solve
    let device = fock_sirk::best_device();
    let sirk_result = solve_forward_sirk(&hamiltonian, &initial_state, &shifts, &device, None)
        .expect("Failed to solve SIRK");

    println!(
        "Krylov subspace built. Matrix size: {}x{}",
        sirk_result.h_proj.nrows(),
        sirk_result.h_proj.ncols()
    );

    // 5. Time Evolution
    let t = 0.5;
    let coefficients = sirk_result.time_evolve(t);
    println!("Evolution coefficients: {:?}", coefficients);

    Ok(())
}

```

### File: `../unfer/docs/CADABRA2_GOTCHAS.md`

**Source:** `../unfer/docs/CADABRA2_GOTCHAS.md` (complete file, 199 lines).

````markdown
# Cadabra2 in this repository — operational gotchas

The reusable, hard-won knowledge about driving Cadabra2 (GPL-3.0) as a
**subprocess** from `prob_kernel::symbolic`. Extracted from `AGENTS.md` (project
review item **X3**, finding **G-U2**) because it was buried in a checklist
paragraph where nobody could find it.

**Why a subprocess and never a link.** Cadabra2 is GPL-3.0; these binaries are
Apache-2.0. `cadabra2-cli` is invoked as an external program
(`CADABRA_CLI` overrides the path), so no GPL code is linked into the Rust
binaries and the licence boundary is unaffected. Same pattern as the Why3 (LGPL)
seam. Keep it that way — vendoring the engine would change the licence of
everything downstream.

**Engine-dependent tests skip when `cadabra2-cli` is absent.** That is the
Cadabra2 skip pattern, also used by the GPU suites in `delta_algebra`. A skip is
not a pass: a green run on a machine without the engine has verified nothing
about these modules. `flake.nix` provides it in the dev shell.

---

## 1. The `@()` four-character rule

**The trap.** `@(name)` resolves its argument through the LaTeX parser, and that
parser reads `_` as a subscript separator *unless the stem before it is four or
more characters*. So:

| reference | resolves? |
|---|---|
| `@(action_st)` | ✅ stem `action` is 5 chars |
| `@(U_psi)` | ❌ mis-resolves to a `\prod` node |
| `@(ex1_st)` | ❌ |
| `@(H_8182_st)` | ❌ |
| `@(H_final_st)` | ❌ |

A mis-resolved reference aborts the run with:

```
RuntimeError: Python object '<…>' does not exist
```

**The rule: use a ≥4-character stem for anything referenced by `@()`.** If a
name genuinely cannot be renamed, use `dst = src.copy()` instead — but note
`dst = src` *aliases*, and Cadabra manipulates expressions in place, so the
copy is mandatory.

This bug aborted the Starobinsky-vielbein module, and its `unwrap` defect (below)
collapsed `ex1_st` to a single term, until 2026-09-18.

## 2. The `unwrap` trap

`unwrap` strips the top node of **every** term. Two distinct failure modes:

**In a wrapped derivation.** After `product_rule` the integrand is a *sum*, so
`unwrap` keeps only the first term. Keep the `\int` wrapper until *after*
`integrate_by_parts`, then take the integrand with `[0]` — **without** `unwrap`.

**In `post_process`.** An active `unwrap` there runs on the output of *every*
algorithm in the file and would corrupt every sum in it. The module-level audit
confirmed no module has one. If you add one, that audit result is no longer true.

**Benign case.** `unwrap` on a *plain* sum acts termwise, so the
`unwrap(lhs)`/`unwrap(rhs)` calls in `qg_unitarity_check.cdb`'s Hkern checks are
fine — `Hkern` still reaches 0. Content reference, not a line number: line
numbers shift when the module-documentation headers change.

## 2b. The `:=` line traps (found 2026-10-14, writing `momentum_space_products.cdb`)

Both traps are **silent**: the file keeps parsing and the failure surfaces
somewhere else, or nowhere.

**A trailing `#` comment on a `:=` line drops the assignment.**

```text
psA := um*um.                 # comment
fldx := um*Em + uo*Eo + up*Ep.
sq1 := @(fldx)*@(fldx).
distribute(sq1)               # RuntimeError: Python object 'fldx' does not exist
```

The misreported error names a *later* handle — the comment kills its own line,
not the one that fails. Comments on their own lines are fine even with
`u_{-2}`, `@()` and `$...$` inside them (verified). The whole existing corpus
already puts comments on their own lines; keep it that way.

**`x := len(ex)` silently swallows the rest of the file.** `:=` pushes its
right-hand side through the Cadabra expression parser; `len(...)` is not a
Cadabra expression, and the parse failure produces **no output and no
traceback** — the script simply stops before the next statement. Size captures
must use plain Python: `x = len(ex)` (verified working, including inside
`print`).

Related engine fact worth knowing when pinning sizes: `distribute` **already
collects like terms** (with coefficient arithmetic — identical terms with
opposite coefficients cancel there), so the post-`distribute` `len` equals the
post-`collect_terms` `len` unless a symbol table (e.g. the `E_a E_b -> E_{a+b}`
momentum table of `momentum_space_products.cdb`) changes term identity in
between. Pin what the engine actually prints, not what the algebra predicts.

## 3. Silent truncation — the failure mode to watch for

The base module `qg_gauge_fixed_hamiltonian.cdb` had a *silent* truncation: its
`ex1` (documented as the Einstein–Hilbert action density `eR` in the vielbein) was
**one summand** of the expanded action — `len(ex1)` 18 (a single product of 18
factors) against 120, and `pi_derived` 2 summands against 132. Repaired
2026-09-18 by removing the offending line.

**Nothing caught it**, because the Rust test asserted only that `ex1` is
non-empty and tetrad-shaped.

The `unwrap` defect was then found in the base module too, which is why there is
now a module-level audit: [`VERIFY_CDB_TRUNCATION_AUDIT.md`](VERIFY_CDB_TRUNCATION_AUDIT.md)
dumps the size of every named expression, runs counterfactuals, and replays the
Rust extraction trailer. It covers the seven `docs/*.cdb` modules that existed on
2026-09-18 and confirmed the base module was the only truncated one. (`docs/` has
22 modules as of 2026-10-14; the later ones carry their size guards as in-module
CHECK rows with pinned expected sizes.)

**The general lesson, and it is not Cadabra-specific:** a CHECK that reduces to 0
can still be asserting nothing. Any assertion of the form "the derivation
produced *a* thing" should also assert *how much* of it there was. The audit
above exists because the alternative is a test suite that reports green on an
empty result.

## 4. Two adjacent non-truncation findings

- The `diff` handle in `qg_densitized_hamiltonian.cdb` is a **hand-typed
  tautology** that cannot fail — it never references `Ktrans`/`Kflat`.
- `unwrap` on a plain sum is benign (see §2).

Both are recorded rather than fixed: fixing the first means deciding what it was
*meant* to compare, which is a physics question.

## 5. Reading the extraction pipeline

The pipeline reads only the run's **stdout markers**, so the comment headers
added to every `docs/*.cdb` module on 2026-10-04 are inert to it. Two stale
line-number references in `AGENTS.md` and `VERIFY_CDB_TRUNCATION_AUDIT.md` were
converted to content-based references at the same time, so future header edits
cannot rot them — keep it that way.

## 6. Error codes

| code | meaning |
|---|---|
| `UK-4901` | engine missing (`cadabra2-cli` not found) |
| `UK-4902` | malformed expression |

`verified` in the report is the **zero-detection** verdict (`H - H† = 0`, i.e.
Hermiticity), not a proof of anything beyond that.

## 7. The dialect round trip

`symbolic_analyze` canonicalizes the expression (TeX subset, or the `c_0 * a_0`
CAS dialect); `normalize_to_cas_dialect` translates Cadabra2's **braced** output
back into the dialect `compile_to_fock` accepts, closing the loop into a numerical
`Hamiltonian`.Both directions are load-bearing: a module that emits Cadabra's
braced form without the reverse translation produces a `Hamiltonian` the compiler cannot read, and
the failure surfaces much later as an empty operator.

One trap on the CAS side of that loop (not Cadabra — review finding F6): `compile_to_fock` must
**not** call the external `Expression::expand()` — it is quadratic-to-exponential in the number of
factors (φ⁴ takes ~11 s; six factors hang). The memoized `distribute_bounded` in
`nested_fock_algebra/src/cas.rs` does the same distribution bounded and in < 1 ms.

---

## Current operator-scope audit

The [nested-Fock enclosure audit](VERIFY_NESTED_FOCK_ENCLOSURE.md) fixes the
inner/outer and QG chart interpretation of the modules. Its new checks await
execution; this is not a replacement for historical engine transcripts.
Frame-matrix determinant scaling alone is not a field-coordinate Jacobian
or a unitary/ESA proof.

## Module index

Each `.cdb` module has a **MODULE DOCUMENTATION** header giving its purpose, its
role in the programme, its certified content, and the improvement notes tied to
the project's goals. Evidence lives in:

| module(s) | evidence |
|---|---|
| `faris_lavine_n_ns.cdb`, `faris_lavine_n_qg.cdb` | [VERIFY_FARIS_LAVINE_N.md](VERIFY_FARIS_LAVINE_N.md) |
| `faris_lavine_n_sm.cdb` | [VERIFY_SM_FARIS_LAVINE.md](VERIFY_SM_FARIS_LAVINE.md) |
| `qg_gauge_fixed_hamiltonian.cdb` and the truncation audit | [VERIFY_CDB_TRUNCATION_AUDIT.md](VERIFY_CDB_TRUNCATION_AUDIT.md) |
| `qg_densitized_hamiltonian.cdb`, `qg_unitarity_check.cdb` | [VERIFY_QG_DENSITIZED.md](VERIFY_QG_DENSITIZED.md) |
| `qg_starobinsky_hamiltonian.cdb` | [VERIFY_QG_STAROBINSKY_EINSTEIN_FRAME.md](VERIFY_QG_STAROBINSKY_EINSTEIN_FRAME.md) |
| `qg_starobinsky_vielbein_hamiltonian.cdb` | [VERIFY_QG_STAROBINSKY_VIELBEIN.md](VERIFY_QG_STAROBINSKY_VIELBEIN.md) |
| `ns_qg_fourier_elimination.cdb` | [VERIFY_NS_QG_FOURIER.md](VERIFY_NS_QG_FOURIER.md) |
| `momentum_space_products.cdb` | [VERIFY_MOMENTUM_SPACE_PRODUCTS.md](VERIFY_MOMENTUM_SPACE_PRODUCTS.md) |
| `ns_kvn_equation.cdb`, `ns_pressure_poisson.cdb`, `ns_pressure_constraint.cdb` | [VERIFY_FARIS_LAVINE_N.md](VERIFY_FARIS_LAVINE_N.md) |
| `ns_lagrangian_hamiltonian.cdb` | [VERIFY_NS_QG_FOURIER.md](VERIFY_NS_QG_FOURIER.md) |
| `mass_gap_norm_residual.cdb` | [VERIFY_MASS_GAP_NORM_RESIDUAL.md](VERIFY_MASS_GAP_NORM_RESIDUAL.md) |
| `ns_compressible_lagrangian.cdb`, `sm_gauge_fixed_hamiltonian.cdb` (2026-10-13) | the 2026-10-14 update in [CDB_MODULE_REVIEW.md](CDB_MODULE_REVIEW.md); numerical seam `fock_sirk/tests/{ns_compressible_lagrangian_validation,sm_gauge_fixed_validation,sm_higgs_mechanism_sirk}.rs` |

Related: [NUMERICAL_VALIDATION_GUIDE.md](NUMERICAL_VALIDATION_GUIDE.md) for the
numeric side, [ARCHITECTURE.md](ARCHITECTURE.md) for the crate map,
[../ATTRIBUTION.md](../ATTRIBUTION.md) for the licence boundary.
````

## 4. timepiece dependencies

### Dependency excerpt: `BookProof/ChapterQuadraticRotationEsa.lean` — orthogonal substitution and core unitarity

**Source:** `BookProof/ChapterQuadraticRotationEsa.lean`, lines 1–213, 413–436.
The omitted middle proves the general quadratic operator and its conjugation identity.

```lean
import Mathlib
import BookProof.ChapterHyperbolicQuadraticEsa

/-!
# General (non-diagonal) quadratic Hamiltonians of arbitrary signature

`BookProof.ChapterHyperbolicQuadraticEsa` proves that the *diagonal* quadratic operator

`H_c = ∑ᵢ cᵢ (−∂ᵢ² + xᵢ²/4)`,  `c : Fin d → ℝ` arbitrary (hyperbolic signatures included),

is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`.
This module removes the diagonality restriction: for an **arbitrary real symmetric matrix**
`A` the operator

`H_A = ∑_{k,l} A_{kl} (π_k π_l + x_k x_l / 4)`,  `π_k = −i ∂/∂x_k`,

— the general quadratic Hamiltonian whose kinetic and potential forms share the matrix
`A`, of arbitrary signature — is symmetric and essentially self-adjoint on the same core.
With `A = diag(c)` this is the diagonal theorem; with `A` a rotated Minkowski form it is
`□ + V` written in rotated coordinates, where neither the kinetic form nor the potential
is diagonal.

## The route

An orthogonal change of coordinates.  The Gaussian `e^{−‖x‖²/4}` is rotation invariant, so
composition with an orthogonal matrix `O` maps the Gauss–polynomial core onto itself; on
the polynomial coordinates it is the substitution `rotPoly O`, an algebra automorphism.
The canonical pair transforms contravariantly with the *same* matrix
(`rotPoly_mulXPoly`, `rotPoly_momPoly`), so the diagonal operator `H_c` is carried onto
`H_A` with `A = O diag(c) Oᵀ` (`quadPolyMat_rotPoly`).  The rotated product Hermite
functions are therefore an orthonormal family of joint eigenvectors of `H_A` spanning the
core (`orthonormal_rotHermiteLp`, `span_rotHermiteLp`, `quadOpMat_rotHermiteLp`), and the
diagonal instruments of `BookProof.ChapterHyperbolicQuadraticEsa`
(`symmetricOn_of_diagonal`, `deficiencyTrivialAt_of_diagonal`) finish the argument.
The spectral theorem for real symmetric matrices supplies `O` and `c` for an arbitrary
symmetric `A`.

## What is proved

* `rotPoly`, `pderiv_rotPoly`, `rotPoly_mulXPoly`, `rotPoly_momPoly` — the orthogonal
  substitution on polynomial coordinates and its action on the canonical pair;
* `rotIso`, `gaussInt_rotPoly`, `inner_pgLp_rotPoly` — the rotation as a
  measure-preserving linear isometry of `ℝᵈ`, and the resulting unitarity on the core;
* `quadPolyMat`, `quadPolyMat_rotPoly` — the general quadratic operator and the
  conjugation identity `H_{O diag(c) Oᵀ} ∘ R = R ∘ H_c`;
* `rotHermiteLp`, `orthonormal_rotHermiteLp`, `span_rotHermiteLp` — the rotated product
  Hermite functions are an orthonormal family whose span is the core;
* `quadOpMat_rotConj_symmetric`, `quadOpMat_rotConj_essentiallySelfAdjoint` — the headline
  for `A = O diag(c) Oᵀ`;
* `quadOpMat_symmetric`, `quadOpMat_essentiallySelfAdjoint` — **the headline**: for every
  real symmetric matrix `A`, `H_A` is symmetric and essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝᵈ)`;
* `quadOpMat_not_bounded`, `polyGaussCore_dense_L2` — non-vacuity: the operator is
  genuinely unbounded whenever `A ≠ 0`, and its domain is dense.

## Honest boundary

The potential is quadratic and its matrix is *the same* as the matrix of the kinetic form:
that matched pair is what a single rotation diagonalizes.  A general Faris–Lavine
potential bounded above by a quadratic remains out of reach by this argument, exactly as
recorded in `BookProof.ChapterHyperbolicQuadraticEsa`.
-/

namespace BookProof.QuadraticRotation

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

/-! ## 1. The orthogonal substitution on polynomial coordinates -/

/-- The substitution `Xᵢ ↦ ∑ⱼ Oⱼᵢ Xⱼ`: on functions this is `p ↦ p ∘ Oᵀ`. -/
def rotPoly (O : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ :=
  aeval (fun i => ∑ j, C ((O j i : ℝ) : ℂ) * X j)

theorem rotPoly_X (O : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    rotPoly O (X i) = ∑ j, C ((O j i : ℝ) : ℂ) * X j := by
  simp [rotPoly]

theorem rotPoly_C (O : Matrix (Fin d) (Fin d) ℝ) (z : ℂ) : rotPoly O (C z) = C z := by
  simp [rotPoly]

/-- **The chain rule** for the substitution: `∂_k (p ∘ Oᵀ) = ∑ᵢ O_{ki} (∂ᵢp) ∘ Oᵀ`. -/
theorem pderiv_rotPoly (O : Matrix (Fin d) (Fin d) ℝ) (k : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    pderiv k (rotPoly O p) = ∑ i, C ((O k i : ℝ) : ℂ) * rotPoly O (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib, mul_add]
  | mul_X p i hp =>
      have hd : pderiv k (rotPoly O (X i)) = C ((O k i : ℝ) : ℂ) := by
        rw [rotPoly_X, map_sum]
        simp [Pi.single_apply]
      have hr : ∀ m : Fin d, pderiv m (p * X i)
          = pderiv m p * X i + (if m = i then p else 0) := by
        intro m
        rw [Derivation.leibniz, pderiv_X]
        by_cases h : m = i <;> simp [h, Pi.single_apply, smul_eq_mul, mul_comm, add_comm]
      have hRHS : ∑ m, C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m (p * X i))
          = (∑ m, C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m p)) * rotPoly O (X i)
            + C ((O k i : ℝ) : ℂ) * rotPoly O p := by
        have hsplit : ∀ m : Fin d, C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m (p * X i))
            = C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m p) * rotPoly O (X i)
              + (if m = i then C ((O k m : ℝ) : ℂ) * rotPoly O p else 0) := by
          intro m
          rw [hr m, map_add, map_mul, mul_add]
          by_cases h : m = i <;> simp [h, mul_assoc]
        rw [Finset.sum_congr rfl fun m _ => hsplit m, Finset.sum_add_distrib, Finset.sum_mul]
        congr 1
        simp
      rw [map_mul, Derivation.leibniz, hd, hp, hRHS]
      simp only [smul_eq_mul]
      ring

/-- The substitutions by `O` and by `Oᵀ` are mutually inverse. -/
theorem rotPoly_rotPoly_transpose {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (p : MvPolynomial (Fin d) ℂ) : rotPoly O (rotPoly Oᵀ p) = p := by
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  have hgen : ∀ i : Fin d, rotPoly O (rotPoly Oᵀ (X i)) = X i := by
    intro i
    rw [rotPoly_X, map_sum]
    have hstep : ∀ j : Fin d, rotPoly O (C ((Oᵀ j i : ℝ) : ℂ) * X j)
        = ∑ k, C (((O i j * O k j : ℝ)) : ℂ) * X k := by
      intro j
      rw [map_mul, rotPoly_C, rotPoly_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, ← map_mul]
      norm_num [Matrix.transpose_apply]
    rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_comm]
    have hk : ∀ k : Fin d, ∑ j, C (((O i j * O k j : ℝ)) : ℂ) * X k
        = (if i = k then (1 : MvPolynomial (Fin d) ℂ) else 0) * X k := by
      intro k
      rw [← Finset.sum_mul]
      congr 1
      have h1 := congrFun (congrFun hOO i) k
      have h2 : ∑ j, O i j * O k j = if i = k then (1 : ℝ) else 0 := by
        simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using h1
      rw [← map_sum,
        show (∑ j, ((O i j * O k j : ℝ) : ℂ)) = ((∑ j, O i j * O k j : ℝ) : ℂ) by
          push_cast; ring,
        h2]
      by_cases h : i = k <;> simp [h]
    rw [Finset.sum_congr rfl fun k _ => hk k]
    simp
  have hcomp := MvPolynomial.algHom_ext (f := (rotPoly O).comp (rotPoly Oᵀ))
    (g := AlgHom.id ℂ (MvPolynomial (Fin d) ℂ)) (by intro i; simpa using hgen i)
  exact congrArg (fun f => f p) hcomp

theorem rotPoly_surjective {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) :
    Function.Surjective (rotPoly O) := fun p =>
  ⟨rotPoly Oᵀ p, rotPoly_rotPoly_transpose hO p⟩

/-! ## 2. The canonical pair transforms with the same matrix -/

theorem rotPoly_mulXPoly (O : Matrix (Fin d) (Fin d) ℝ) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (mulXPoly i p) = ∑ k, ((O k i : ℝ) : ℂ) • mulXPoly k (rotPoly O p) := by
  simp only [mulXPoly_apply, map_mul, rotPoly_X, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [MvPolynomial.smul_eq_C_mul, mul_assoc]

/-- `∂ᵢ` pulled back: `R(∂ᵢ p) = ∑ₖ O_{ki} ∂ₖ (R p)`, by the chain rule and `OᵀO = 1`. -/
theorem rotPoly_pderiv {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (pderiv i p) = ∑ k, ((O k i : ℝ) : ℂ) • pderiv k (rotPoly O p) := by
  have hexp : ∀ k : Fin d, ((O k i : ℝ) : ℂ) • pderiv k (rotPoly O p)
      = ∑ m, ((O k i * O k m : ℝ) : ℂ) • rotPoly O (pderiv m p) := by
    intro k
    rw [pderiv_rotPoly, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
  have hm : ∀ m : Fin d, ∑ k, ((O k i * O k m : ℝ) : ℂ) • rotPoly O (pderiv m p)
      = (if i = m then (1 : ℂ) else 0) • rotPoly O (pderiv m p) := by
    intro m
    rw [← Finset.sum_smul]
    congr 1
    have h1 := congrFun (congrFun hO i) m
    have h2 : ∑ k, O k i * O k m = if i = m then (1 : ℝ) else 0 := by
      simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using h1
    rw [show (∑ k, ((O k i * O k m : ℝ) : ℂ)) = ((∑ k, O k i * O k m : ℝ) : ℂ) by
        push_cast; ring, h2]
    by_cases h : i = m <;> simp [h]
  rw [Finset.sum_congr rfl fun m _ => hm m]
  simp

theorem rotPoly_momPoly {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (momPoly i p) = ∑ k, ((O k i : ℝ) : ℂ) • momPoly k (rotPoly O p) := by
  have hX : rotPoly O (X i * p) = ∑ k, ((O k i : ℝ) : ℂ) • (X k * rotPoly O p) := by
    simpa using rotPoly_mulXPoly O i p
  rw [momPoly_apply, map_mul, rotPoly_C, map_sub, map_mul, rotPoly_C, rotPoly_pderiv hO, hX,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [momPoly_apply, MvPolynomial.smul_eq_C_mul]
  ring

/-! ## 3. The general quadratic operator and the conjugation identity -/

/-- The general quadratic Hamiltonian `∑_{k,l} A_{kl}(π_k π_l + x_k x_l/4)` in polynomial
coordinates. -/
def quadPolyMat (A : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ k, ∑ l, ((A k l : ℝ) : ℂ) •
    ((momPoly k).comp (momPoly l) + (1/4 : ℂ) • ((mulXPoly k).comp (mulXPoly l)))

```

*Lines 214–412 omitted.*

```lean
/-- **The substitution is unitary on the core.** -/
theorem inner_pgLp_rotPoly {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp (rotPoly O p)) (pgLp (rotPoly O q)) : ℂ)
      = (inner ℂ (pgLp p) (pgLp q) : ℂ) := by
  have hL : (inner ℂ (pgLp (rotPoly O p)) (pgLp (rotPoly O q)) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun (rotPoly O p) x) * pgFun (rotPoly O q) x := by
    rw [inner_pgLp]
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn (rotPoly O q)] with x hx
    rw [hx]
  have hR : (inner ℂ (pgLp p) (pgLp q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * pgFun q x := by
    rw [inner_pgLp]
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn q] with x hx
    rw [hx]
  have hpt : ∀ x : Vd d, (starRingEnd ℂ) (pgFun (rotPoly O p) x) * pgFun (rotPoly O q) x
      = (fun y : Vd d => (starRingEnd ℂ) (pgFun p y) * pgFun q y) (rotIso hO x) := by
    intro x
    rw [pgFun_rotPoly hO, pgFun_rotPoly hO]
  rw [hL, hR, integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_comp_rotIso hO
    (fun y : Vd d => (starRingEnd ℂ) (pgFun p y) * pgFun q y)

```

### Dependency excerpt: `BookProof/Toolbox/ChapterHermiteProductCore.lean` — Gaussian core

**Source:** `BookProof/Toolbox/ChapterHermiteProductCore.lean`, lines 224–230, 860–868.

```lean
/-! ## The core as the range of a linear map -/

/-- `p ↦ [p · e^{-‖x‖²/4}]` as an element of `L²(ℝᵈ)`. -/
def pgLp (p : MvPolynomial (Fin d) ℂ) : L2d d := (memLp_pgFun p).toLp _

theorem pgLp_coeFn (p : MvPolynomial (Fin d) ℂ) :
    (pgLp p : Vd d → ℂ) =ᵐ[volume] pgFun p := (memLp_pgFun p).coeFn_toLp

```

*Lines 231–859 omitted.*

```lean
/-- The **product Hermite polynomial** `∏ᵢ He_{αᵢ}(xᵢ)`. -/
def hermiteMv (a : Fin d →₀ ℕ) : MvPolynomial (Fin d) ℂ := ∏ i, hermiteFactor i (a i)

theorem hermiteMv_zero : hermiteMv (0 : Fin d →₀ ℕ) = 1 := by
  simp [hermiteMv, hermiteFactor_zero]

theorem hermiteMv_erase (i : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMv a = hermiteFactor i (a i) * ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) := by
  rw [hermiteMv, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

```

### Dependency excerpt: `BookProof/Toolbox/ChapterHermiteProductBasis.lean` — Fubini, norm and Hilbert basis

**Source:** `BookProof/Toolbox/ChapterHermiteProductBasis.lean`, lines 96–130, 174–186.

```lean
/-- **Fubini for two product Hermite functions**: their `L²` inner product is the product
of the one-dimensional Hermite inner products. -/
theorem inner_pgLp_hermiteMv (a b : Fin d →₀ ℕ) :
    (inner ℂ (pgLp (hermiteMv a)) (pgLp (hermiteMv b)) : ℂ)
      = ((∏ i, hermiteInner (a i) (b i) : ℝ) : ℂ) := by
  rw [inner_pgLp]
  have key : (∫ x : Vd d, (starRingEnd ℂ) (pgFun (hermiteMv a) x)
        * (pgLp (hermiteMv b) : Vd d → ℂ) x)
      = ∫ x : Vd d, ∏ i, ((hermiteFun (a i) (x i) * hermiteFun (b i) (x i) : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn (hermiteMv b)] with x hx
    rw [hx, pgFun_hermiteMv, pgFun_hermiteMv, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [key, integral_prod_coord (fun i t => ((hermiteFun (a i) t * hermiteFun (b i) t : ℝ) : ℂ)),
    Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_complex_ofReal, integral_hermiteFun_mul]

/-! ## The orthonormal basis -/

/-- The `L²` norm of the product Hermite function `ψ_α`. -/
def hermiteMvNorm (a : Fin d →₀ ℕ) : ℝ := ∏ i, hermiteNorm (a i)

theorem hermiteMvNorm_pos (a : Fin d →₀ ℕ) : 0 < hermiteMvNorm a :=
  Finset.prod_pos fun i _ => hermiteNorm_pos (a i)

theorem hermiteMvNorm_ne_zero (a : Fin d →₀ ℕ) : ((hermiteMvNorm a : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (hermiteMvNorm_pos a)

/-- **The normalized product Hermite function** `ψ_α / ‖ψ_α‖`. -/
def hermiteMvLp (a : Fin d →₀ ℕ) : L2d d := ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (hermiteMv a)

theorem pgLp_hermiteMv_eq (a : Fin d →₀ ℕ) :
    pgLp (hermiteMv a) = ((hermiteMvNorm a : ℝ) : ℂ) • hermiteMvLp a := by
  rw [hermiteMvLp, smul_smul, mul_inv_cancel₀ (hermiteMvNorm_ne_zero a), one_smul]

```

*Lines 131–173 omitted.*

```lean
/-- **The product Hermite functions form a Hilbert basis of `L²(ℝᵈ)`**, indexed by the
multi-indices. -/
def hermiteMvBasis : HilbertBasis (Fin d →₀ ℕ) ℂ (L2d d) :=
  HilbertBasis.mk orthonormal_hermiteMvLp
    (by
      rw [span_hermiteMvLp]
      have hd := polyGaussCore_dense (d := d)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])

@[simp] theorem hermiteMvBasis_apply (a : Fin d →₀ ℕ) :
    hermiteMvBasis a = hermiteMvLp (d := d) a := by
  rw [hermiteMvBasis, HilbertBasis.coe_mk]

```

## 5. papers

### Paper excerpt: `../papers/book.tex` — recursive second quantization and nested Fock space

**Source:** `../papers/book.tex`, lines 3731–3739, 3880–3904 and 4030–4058.
This is the nested-Fock construction: second quantization applied recursively with the
original Fock space as the new base Hilbert space, the Fock-space proposition operators,
and the quadratic ordering that keeps the base-Hilbert-space commutation rules. The file
contains no literal `Mehler` or `Hermite` passage; its relevant background is the Gaussian
measure and Fock-space construction excerpted here.

```latex
Since the second-quantization procedure can be applied recursively, we
can assume without loss of generality that the Hamiltonian is quadratic
in the creation/annihilation operators and thus no further
regularization is needed (the wave-function parametrization can be
considered a regularization by itself). For instance, in case the
Hamiltonian acting in the Fock-space is not quadratic in the
creation/annihilation operators, then we can consider instead a new
Fock-space where the base Hilbert space is the original Fock-space. The
new Hamiltonian is quadratic in the creation/annihilation operators.

```

*Lines 3740–3879 omitted.*

```latex
The (bosonic or fermionic) Fock-space can be used as the wave-function
parametrization of an arbitrary probability distribution of a classical
field over space (for instance the 3D space), in the following way. For
a Hamiltonian involving at most first-order derivatives of the fields,
the propositions about a (non-free) field at an arbitrary discrete
finite number \(n\) of points in space are parametrized by the
Fock-space over \(S=\mathbb{R}^{d(1+m)+m}\), where \(d\) is the number
of space dimensions and \(m\) is the number of bosonic fields (to
include fermionic fields we replace \(\mathbb{R}\) by the discrete set
\(\{0,1\}\)). The operator corresponding to a proposition is:

\begin{equation}\begin{aligned}
    &\pi(\phi(x_1)\cap ...\cap \phi(x_n))=a^\dagger(\phi_1,x_1)a(\phi_1,x_1)...a^\dagger(\phi_n,x_n)a(\phi_n,x_n)\end{aligned}\end{equation}

Above, we assume no coinciding points such as \(x_n=x_1\). Note that
this operator still needs to be normalized to be considered a
proposition (such that its integral is the unit), since it is composed
of number operators and not projections. Moreover, the commutative
algebra generated by number operators is consistent with a point process
and its wave-function parametrization can be a bosonic or a fermionic
Fock-space. The normalization is done using the property of
tensor-product of the Fock-space, until each Fock-space appearing in the
tensor-product either has at most one point or it has a discrete
base-space, in both-cases it is straightforward to remove the base-space
from each Fock-space.

```

*Lines 3905–4029 omitted.*

```latex
\hypertarget{quadratic-ordering}{%
\section{Quadratic Ordering}\label{quadratic-ordering}}

The (symmetric) Weyl ordering of
operators~\cite{Fujii2004New}\cite{Tao2012Some} conserves the
exponential of operators, unlike
normal-ordering~\cite{Blasiak2007Combinatorics}. This is an important
property of the ordering, because we use often the Trotter product
formula~\cite{Simon2005Functional}\cite{Hatano2005Finding} (e.g.~in the time-evolution operator).

However, the Weyl ordering is not appropriate for the
second-quantization of an infinite-dimensional Hilbert space, since it
leads to infinite vacuum expectation values of quadratic operators.
Thus, we introduce the Quadratic Ordering which is a kind of
``incomplete'' normal ordering, which conserves the exponential of
operators. That is, we only order operators which conserve the number
operator such that these operators are a product of quadratic operators
(where each quadratic operator conserves the number operator and has
null vacuum expectation value). All other operators can be generated
from these products of quadratic operators and operators with
exclusively creation (or exclusively annihilation) operators which are
automatically ordered.

The quadratic operators are normalized by normal operators acting in the
Hilbert space \(H\) which generates the Fock-space, while the operators
with exclusively creation (or exclusively annihilation) operators are
normalized by wave-functions (elements of the tensor-products of \(H\)).
In this way, the commutation rules in the Fock-space are related to the
commutation rules of the Hilbert space \(H\).

```

### Paper excerpt: `../papers/Hashimoto.md` — shift-invert rational Krylov for unbounded operators

**Source:** `../papers/Hashimoto.md`, lines 6–16, 72–76, 186–200, 226–240.
This is the convergence setting behind the shifts used in `joint_sirk.rs`; it does not
mention λφ⁴.

```markdown
# Shift-invert Rational Krylov method for an operator $\phi$-function of an unbounded linear operator

Yuka Hashimoto$^{1,2}$ · Takashi Nodera$^3$

Received: 5 March 2018 / Revised: 14 January 2019

© The JJIAM Publishing Committee and Springer Japan KK, part of Springer Nature 2019

## Abstract

The product of a matrix function and a vector is used to solve evolution equations numerically. Hashimoto and Nodera (ANZIAM J 58:C149–C161, 2016) proposed the Shift-invert Rational Krylov method for computing these products. However, since matrices produced by evolution equations behave like unbounded operators in infinite-dimensional spaces, an analysis with the unbounded operator is essential. In this paper, the Shift-invert Rational Krylov method is extended to be applied to unbounded operators.

```

*Lines 17–71 omitted.*

```markdown
Shift-invert Rational Krylov method for an unbounded operator

and most well-known method is the Arnoldi method [5,11]. This method approximates an operator function of A in a space of polynomials of A of degree m. However, the approximation error of the Arnoldi method is not guaranteed to decay with respect to m, if A is unbounded. On the other hand, approximation errors of the Shift-invert Arnoldi (SIA) method [8,13] and the Rational Krylov (RK) method [1,6] decay even with unbounded operators. In these methods, the resolvents (γI - A)⁻¹, which are bounded, are used to construct a shift-invert Krylov or a rational Krylov subspace, where γ is not in the spectrum of A. γ is called a shift. Hashimoto and Nodera [10] proposed the Shift-invert Rational Krylov (SIRK) method for matrix φ functions. This method calculates the approximation in a similar manner as the SIA, but constructs a rational Krylov subspace with appropriate shifts which results in a faster decrease of the approximation error than the SIA.

In this paper, SIRK is extended for use with unbounded operators. The operator function is defined so that it can be adapted for an analysis for SIRK, and it is shown that the result of Theorem 5 [10] is also applicable to unbounded operator A.

```

*Lines 77–185 omitted.*

```markdown
### 3.3 Rational Krylov method

For $j = 1, \ldots, m$, let $X_j := (\gamma_j I - A)^{-1}$, where $\gamma_j \notin \Lambda(A)$. The following rational Krylov subspace is constructed:

$$\mathcal{Q}_m(\{X_j\}_{j=1}^{m-1}, v) := \text{span}\{v, X_1 v, X_2 X_1 v, \ldots, X_{m-1} \cdots X_1 v\}. \tag{8}$$

If the dimension of $\mathcal{Q}_m(\{X_j\}, v)$ is $m$, let $\{v_1, \ldots, v_m\}$ be the orthonormal basis of $\mathcal{Q}_m(\{X_j\}, v)$ which satisfy the condition:

$$X_j V_j \mathbf{t}_j = \sum_{i=0}^j \mathrm{h}_{i,j} v_j + \mathrm{h}_{j+1,j} v_{j+1} \quad (j = 1, \ldots, m-1), \tag{9}$$

where:

$$\mathrm{h}_{i,j} := (X_j V_j \mathbf{t}_j, v_i) \quad (i, j = 1, \ldots, m, i \le j),$$

$$\mathrm{h}_{i+1,i} := \left\| X_i V_i \mathbf{t}_i - \sum_{l=1}^i \mathrm{h}_{l,i} v_l \right\|,$$

```

*Lines 201–225 omitted.*

```markdown
## 4 Shift-invert rational Krylov method

For $j = 1, \dots, m$, let $\gamma_j := N - hj$, where $N, h > 0$ satisfy the condition $N > hj$. Rational Krylov subspace (8) is constructed with $\gamma_j$. If the dimension of $\mathcal{Q}_m(\{X_j\}, v)$ is $m$, the following relation is derived through Eq. (9):

$$V_m^*X_mV_m = \mathbf{H}_m\mathbf{K}_m^{-1}, \tag{10}$$

where $\mathbf{K}_m := (\mathbf{T}_m - \mathbf{H}_m\mathbf{D}_m + \gamma_m\mathbf{H}_m)$, $\mathbf{D}_m := \text{diag}(\gamma_1, \dots, \gamma_m)$, $\mathbf{T}_m$ is the $m \times m$ matrix in which the $j$th column is $[\mathbf{t}_j^T\mathbf{0}]^T \in \mathbb{C}^m$.

Since $\gamma_m > 0$, $\psi_{k,\gamma_m} \in \mathcal{M}(W(X_m))$ is satisfied. The following approximation of SIRK is generated in the same manner as SIA using relation (10), if $\mathbf{H}_m$ is invertible:

$$\phi_k(A)v = \psi_{k,\gamma_m}(X_m)v \approx V_m\psi_{k,\gamma_m}(\mathbf{H}_m\mathbf{K}_m^{-1})V_m^*v.$$

Springer

Y. Hashimoto, T. Nodera

```

### Paper excerpt: `../papers/Kopperman_Tutorial.p.tex` — generic polynomial interaction template

**Source:** `../papers/Kopperman_Tutorial.p.tex`, lines 458–476.
The only φ⁴ reference in the papers is the parenthetical `phi^4` example here. It is a
Faris–Lavine template, not a scalar-model derivation.

```latex
\subsection{Phase 5: QFT Hamiltonian Application}

Finally, we construct a polynomial interaction Hamiltonian $V(a, a^*)$ and prove it defines a unique quantum system.

\uplinline| theory QFT_Model {| 
\uplinline$    include HO_Analysis$
\uplinline$    $
\uplinline$    // Interaction Potential V (e.g., phi^4 polynomial in a, a*)$
\uplinline$    // We define a generic polynomial operator constructor$
\uplinline$    PolynomialOp : (Operator, Operator) -> Operator$
\uplinline$    $
\uplinline$    V_int = PolynomialOp(a_op, a_star)$
\uplinline$    $
\uplinline$    // Total Hamiltonian H = N + V$
\uplinline$    H_total = v -> plus(N_op(v), V_int(v))$
\uplinline$    $
\uplinline$    // The Main Result: The QFT Model exists and is unique$
\uplinline$    QFT_Existence : |- EssentiallySelfAdjoint(H_total, HO_Core)$
\uplinline|  }| 

```

## Cross-reference: which external part supports which Lean claim

**Source:** authored summary of the preceding sections; no new external content.

```text
unitJet_vacuum_column / jet_variance_weights
  <- ../unfer/docs/PHI4_ANALYTIC_PLAN.md (17/8, 145/32)
  <- ../unfer/docs/phi4_mehler.cdb (even column 5/8, 7/8, 1/4)
  <- ../unfer/docs/fixtures/phi4_mehler.json (unit-cell columns)
  <- ../unfer/docs/PHI4_NUMERICAL_PLAN.md (Gaussian ground-state check)

twoSite_innerHam / twoSite_column_00 / _20 / _02
  <- ../unfer/docs/phi4_mehler.cdb (two-site mixed vertex and columns)
  <- ../unfer/nested_fock_algebra/src/phi4_scalar.rs (site and mode builders)
  <- ../unfer/nested_fock_algebra/src/exact_inner.rs (ordered action)

Model.orbit_error / rank-two finite identities
  <- ../unfer/docs/phi4_mehler.cdb (rank-two generator and defect)
  <- ../unfer/fock_sirk/src/joint_sirk.rs (rational core: basis, B, G, GMRES)
  <- ../unfer/fock_sirk/src/sm_defect.rs (defect term decomposition)
  <- ../papers/Hashimoto.md (SIRK shift construction)

Hermite core / rotation unitarity
  <- BookProof/Toolbox/ChapterHermiteProductCore.lean
  <- BookProof/Toolbox/ChapterHermiteProductBasis.lean
  <- BookProof/ChapterQuadraticRotationEsa.lean

Nested Fock lift
  <- ../papers/book.tex (recursive second quantization, Fock-space propositions,
     quadratic ordering)

QFT existence template
  <- ../papers/Kopperman_Tutorial.p.tex (generic polynomial interaction only)
```

## End of bundle
