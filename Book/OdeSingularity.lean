import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Resolution of the Singularity of an ODE" =>
%%%
tag := "ode-chapter"
%%%

This chapter replaces the ODE chapter of the source manuscript. It follows the
expanded, operator-theoretic treatment of `ODE.tex`, and is honest about which parts
are formally verified and which remain open (see the proof-plan appendix).

# The Blow-Up

Consider the scalar autonomous ODE

$$`\dot x = x^2, \qquad x(0) = x_0 \in \mathbb{R}.`

Its unique maximal solution is

$$`x(t) = \frac{x_0}{1 - t\,x_0},`

defined only on $`(-\infty, 1/x_0)` when $`x_0 > 0`. As $`t \to 1/x_0`, the
solution *blows up*: $`|x(t)| \to \infty`. There is no global, deterministic
solution defined for all time.

This finite-time blow-up creates two problems:

 * *Undetectability* — if a numerical integrator fails to converge, one cannot
   tell a genuine singularity from insufficient resolution.
 * *Degeneracy* — the blow-up allows unrelated initial conditions to be glued
   before and after the singular time, destroying uniqueness of the initial-value
   problem.

The blow-up time is a concrete, verifiable quantity. In the repository's
`Singularity` library (module `Singularity.Singularity`), the blow-up time of
$`\dot x = x^2` is computed:

```
#check @blowupTime_x_sq
```

# The Central Idea: Admit Uncertainty

The manuscript's central claim is that *both problems are resolved by admitting a
finite amount of uncertainty in the initial condition*. Instead of a point
$`x_0 \in \mathbb{R}`, take a probability measure $`\mu_0` on $`\mathbb{R}` —
equivalently, by the Born parametrization of Part II, a wave-function
$`\psi_0 \in L^2(\mathbb{R})` with $`|\psi_0|^2 = \mu_0` — and evolve it under a
*unitary* group. The resulting evolution is globally defined in time,
non-deterministic in the coordinate $`x`, and reduces to the classical solution in
the zero-uncertainty limit.

This is the same philosophy as the rest of the book: replace a point of the
probability space by a wave-function, and gain structure (here, global unitary
evolution) in return.

*Honesty flag.* The manuscript itself concedes that the two problems are not
resolved equally well: the method solves the first problem (telling a genuine
singularity from insufficient numerical resolution), but it is *not completely
satisfactory* for the second one. The degeneracy is removed by selecting the
continuation that is compatible with analytic continuation, which is the only
physically viable choice in the manuscript's setting but does not give access to
the other, unrelated gluings that may be the relevant ones in other contexts.

# Koopman–von Neumann: Classical Mechanics as Quantum Mechanics

Given a sample space $`\Omega = \mathbb{R}` with a probability measure $`\mu`, one
may always define a wave-function $`\psi = \sqrt{d\mu/dx}` (up to a phase). The
*Koopman–von Neumann* formulation recasts classical statistical mechanics as a
special case of quantum mechanics in which the algebra of observables is
commutative (because the underlying time-evolution is deterministic).

Since $`\mathbb{R}` is a simply connected Lie group under addition, Bargmann's
theorem lifts any strongly-continuous projective unitary representation to a genuine
unitary representation $`U(t)`, and *Stone's theorem* then gives a unique
self-adjoint *Hamiltonian* $`H` with

$$`U(t) = e^{-iHt}.`

So the program is: turn the ODE into a Hamiltonian $`H`, and the (possibly
singular) classical flow into a (globally-defined) unitary group $`e^{-iHt}`.

# Weyl Quantization: From ODE to Hamiltonian

The passage from the classical vector field $`\dot x = f(x)` to a Hamiltonian is
*Weyl quantization*. Because $`x` and the momentum $`\hat p = -i\,\partial_x` do not
commute, the classical product $`f(x)\,p` must be *symmetrized*. For
$`\dot x = x^2` the (formal) Hamiltonian is

$$`H = x^2 \hat p - i\,\hat x,`

where the $`-i\hat x` term is the symmetrization correction. The repository defines
this Weyl-symmetrized Hamiltonian on a normal-ordered operator algebra (module
`Singularity.Hamiltonian` and `Singularity.Poly`):

```
#check @odeToHamiltonian
```

The normal-ordered operator algebra (module `Singularity.Poly`) represents an
operator on $`M` bosonic modes as a finitely-supported function recording
creation/annihilation counts per mode, and implements the *Wick recursion* for
multiplication. This part of the formalization is genuine and `sorry`-free.

*What Weyl quantization does and does not give.* The construction yields a *formal
operator*: a normal-ordered expression that is *Hermitian* (equal to its formal
algebraic adjoint). It does **not** by itself establish essential self-adjointness on
$`L^2` — that is a separate, analytic question governed by Nelson's theorem
(below) and by the completeness of the classical flow. Confusing the two is the
source of the manuscript's error, which we correct in the next section.

# Nelson's Theorem, Essential Self-Adjointness, and the x² Hamiltonian

For the unitary evolution $`e^{-iHt}` to exist globally, the Hamiltonian must be
*essentially self-adjoint* (its closure must be self-adjoint, so that the spectral
theorem applies). *Nelson's theorem* gives a criterion: a symmetric operator is
essentially self-adjoint on a domain if it has a dense set of *analytic vectors*.
For an ODE-derived Hamiltonian, the relevant analytic vectors are tied to the
*completeness of the classical flow*: if the classical flow exists for all time, the
Hamiltonian is essentially self-adjoint, and conversely.

The repository states this connection (module `Singularity.Esa`):

```
#check @nelson_essential_self_adjoint
```

`nelson_essential_self_adjoint` records the Nelson correspondence at the *algebraic
certificate layer*: it states that vanishing deficiency indices are equivalent to
completeness of the represented flow, proved by `simp` from the certificate
definitions. As we flag in "What Is Verified, and What Is Open" below, both sides of
that equivalence are currently placeholders (`isComplete := true` and
`deficiencyIndices := (0,0)` by definition), so this is a genuine theorem *about the
certificate interface*, not yet an analytic proof of essential self-adjointness. A
future analytic realization on a Hilbert space will refine the certificates.

*The manuscript's claim, and the correction to its proof.* The manuscript (book.tex)
asserts that for $`\dot x = x^2` the Hamiltonian $`H = x^2\hat p - i\,\hat x` on
$`C_c^\infty(\mathbb{R})` "can be proved to be essentially self-adjoint", citing a
positive-auxiliary-operator argument (`H^2` in a corollary). The *conclusion* — that
$`H` can be made essentially self-adjoint — is not unreasonable; the *justification*
offered is wrong, and the correct conditions are different. The claimed proof does
not go through: the classical flow
$`\Phi_t(x_0) = x_0/(1 - t x_0)` is defined only for $`t < 1/x_0` (when
$`x_0 > 0`): it is *incomplete*. By Nelson's theorem the deficiency indices do not
both vanish, so $`H` is *not* essentially self-adjoint on $`L^2(\mathbb{R})` as it
stands. The positive-auxiliary-operator method proves essential self-adjointness only
for operators whose classical flow *is* complete (e.g. polynomial Hamiltonians of
degree $`\le 1`, or the harmonic oscillator); the positivity hypothesis the
corollary requires is not satisfied by $`H^2` on the full domain
$`C_c^\infty(\mathbb{R})`.

The correct route to the manuscript's conclusion is by *completing the flow* — the
operator is made essentially self-adjoint on a suitable extension, not left on
$`L^2(\mathbb{R})` as is. This is precisely what the `Singularity` library and its
plan (`SINGULARITY_DETECTION_PLAN.md`) implement (see "Coordinate Transformations"
and "The Full Analysis Pipeline" below): apply a change of variables that makes the
flow complete, quantize the transformed vector field, and obtain an operator that
*is* ESA, whose unitary evolution is well defined and which recovers the original
singular dynamics in a limit. So the claim is reasonable; the difference from what
book.tex suggests is in the proof and the conditions under which it holds.

# The Resolution: Complexification

The cleanest mathematical argument that the singularity disappears is
*complexification*. Pass from $`L^2(\mathbb{R})` to $`L^2(\mathbb{R}^2)` and the
real variable $`x(t)` to a complex one $`z(t) = x(t) + i y(t)` satisfying
$`\dot z = z^2`. The solution is

$$`z(t) = \frac{z(0)}{1 - t\,z(0)},`

with a singularity when $`1 - t\,z(0) = 0`, i.e. $`t = 1/z(0)`. For this singular
time to be *real*, we need $`\operatorname{Im}(1/z(0)) = 0`, which forces
$`y(0) = 0`. But the line $`y(0) = 0` is a *null-measure subset* of
$`\mathbb{R}^2` (this is exactly the measure-theoretic phenomenon of
{ref "null-measure"}[Null-measure sets need not be small]). Therefore, for *almost
every* initial condition in $`L^2(\mathbb{R}^2)`, the singular time is non-real,
and *there is no finite-time singularity*.

Moreover, the imaginary part $`y(0)` can be concentrated arbitrarily close to zero,
so the unitary solution in $`L^2(\mathbb{R}^2)` recovers the (non-unitary,
isometric) solution in $`L^2(\mathbb{R})` in the limit $`y(0) \to 0`. Changing the
sample space effectively changes the equation: $`y(0) = 0` strictly is not
achievable in $`L^2(\mathbb{R}^2)`.

A complementary argument uses *energy-bounded initial conditions*: a finite-time
singularity would make the time-derivative of the wave-function diverge; but the
time-derivative corresponds to the Hamiltonian, whose spectral measure is conserved
by unitary evolution, so an initial condition using only eigenfunctions below some
$`E_{\max}` cannot produce a divergent time-derivative.

That complementary argument is now proved, in the spectral representation where the
Hamiltonian is multiplication by its (real) eigenvalue function, in
`BookProof/ChapterSpectralEnergyBound.lean`: the evolution is unitary
(`norm_evolve`), it satisfies the Schrödinger equation $`\psi'(t) = -iH\psi(t)`
(`hasDerivAt_evolve`), an initial state supported below $`E_{\max}` obeys the
spectral bound $`\|H\psi\| \le E_{\max}\|\psi\|` (`norm_diagOp_le`), so the
time-derivative is bounded uniformly in time (`norm_deriv_evolve_le`) and the
solution is globally Lipschitz — there is no finite-time singularity
(`evolve_lipschitz`).

```
#check @ChapterSpectralEnergyBound.norm_diagOp_le
#check @ChapterSpectralEnergyBound.norm_evolve
#check @ChapterSpectralEnergyBound.hasDerivAt_evolve
#check @ChapterSpectralEnergyBound.norm_deriv_evolve_le
#check @ChapterSpectralEnergyBound.evolve_lipschitz
```

*Formalization.* The complexification resolution is formalized in
`BookProof/ChapterOdeComplexification.lean`:

```
#check @ChapterOdeComplexification.ae_no_real_singular_time
```

`ae_no_real_singular_time` proves that for almost every initial condition in
$`L^2(\mathbb{R}^2)`$, the singular time of $`\dot z = z^2` is non-real, so there
is no finite-time singularity. The proof uses `MeasureTheory.Measure.addHaar_submodule`
to show the real axis has Lebesgue measure zero in $`\mathbb{R}^2`$.

# What Is Verified, and What Is Open

The repository's `Singularity` library is `sorry`-free, but its content splits into
genuine theorems and *algebraic certificates* that must not be read as analytic
results. We keep the two sharply separate.

: Genuinely proved

  The normal-ordered operator algebra and Wick recursion (`Singularity.Poly`); the
  formal Hermitian symmetry of the Weyl Hamiltonian (`weyl_symmetrization_self_adjoint`
  in `Singularity/Hamiltonian.lean`, asserting `adj H = H` at the algebraic level);
  the explicit blow-up time of $`x^2` (`blowupTime_x_sq` in `Singularity.Singularity`);
  and — analytically — the complexification resolution
  (`ae_no_real_singular_time` in `BookProof/ChapterOdeComplexification.lean`) and the
  spectral energy-bound (`ChapterSpectralEnergyBound`), both in `BookProof`.

  ```
  #check @weyl_symmetrization_self_adjoint
  #check @blowupTime_x_sq
  #check @ChapterOdeComplexification.ae_no_real_singular_time
  ```

: Algebraic certificates, not analytic theorems

  `Singularity.Flow` and `Singularity.Esa` build a *certificate layer* in which the
  flow-completeness flag and the deficiency indices are finite placeholders:
  `analyzeClassicalFlow` returns `isComplete := true` by definition, and
  `deficiencyIndices` returns `(0, 0)` by definition. Consequently
  `nelson_essential_self_adjoint` (`isEssentiallySelfAdjoint H ↔
  analyzeClassicalFlow … .isComplete`) is a tautology of these definitions, proved by
  `simp`, and the "completeness" theorems `blowup_criterion_scalar`,
  `linear_flow_complete`, and `even_degree_monomial_flow_complete` assert only that a
  constant flag is `true`. They do **not** establish that any classical flow is
  complete, and they do **not** establish that $`H = x^2\hat p - i\hat x` is
  essentially self-adjoint — indeed for $`\dot x = x^2` it is *not* (see Nelson's
  theorem above). These certificates are an interface for a future analytic
  realization; they are *not* a proof of the analytic claims, which remain open in
  the verified layer and are recorded as such in the proof-plan appendix.

  ```
  #check @analyzeClassicalFlow
  #check @deficiencyIndices
  #check @nelson_essential_self_adjoint
  #check @blowup_criterion_scalar
  #check @linear_flow_complete
  #check @even_degree_monomial_flow_complete
  ```

# Algorithmic Singularity Detection

The manuscript (ODE.tex §6) separates the *detection* of a singularity from its
*resolution*. Detection works on the classical flow. The intended core is
`analyzeClassicalFlow` (module `Singularity.Flow`), which integrates the vector
field and records whether a trajectory escapes a numerical window; the type
`FlowAnalysis` carries an `isComplete` flag and a list of `EscapeEvent`s
(indexing the initial condition, the blow-up time, and the divergent axes):

```
#check @Singularity.Flow.FlowAnalysis
#check @Singularity.Flow.EscapeEvent
```

The *interface* is real, but as noted above the present `analyzeClassicalFlow`
implementation is a certificate placeholder (`isComplete := true` by definition),
so the detection it performs is not yet a theorem about maximal ODE solutions — the
numerical escape experiments it is meant to host belong to a separate approximation
layer. We record the interface and its intended meaning, and flag the gap honestly.

For a scalar polynomial right-hand side the blow-up time has an exact quadrature:
$`T(x_0) = \int_{x_0}^{\infty} dx/f(x)`. The library provides the symbolic
`blowup_time_integral` (module `Singularity.Integration`), which evaluates this
antiderivative exactly for the monomial (power-law) case and falls back to
numerical integration otherwise:

```
#check @Singularity.Integration.blowup_time_integral
```

The detection pipeline assigns a *diagnostic code* categorizing the failure mode
(module `Singularity.Integration`): `odeNotEssentiallySelfAdjoint` (flow
incomplete and no change of variables applied), `odeSingularityDetected` (blow-up
found within the time horizon), `odeCovApplied` (a coordinate transformation
stabilized the Hamiltonian), `odeDeficiencyIndices` (a reduced 1D flow has
non-vanishing deficiency indices), and `odePolynomialTooLarge` (the normal-ordered
degree exceeds the explosion bound):

```
#check @Singularity.Integration.UKDiagnosticCode
```

# Coordinate Transformations

When the flow is singular, the manuscript's strategy is to *change coordinates*
(ODE.tex §7) so the transformed flow is tame, then quantize the new vector field.
The library records the elementary transformations (module `Singularity.ChangeOfVars`):
the *reciprocal* map $`x \mapsto 1/x` (with vector-field pushforward
$`\dot w = -f(1/w)/w^2`), the *logarithmic* map $`x \mapsto \ln x` (with
$`\dot w = f(e^w)/e^w`), and the identity:

```
#check @Singularity.ChangeOfVars.applyReciprocalTransform
#check @Singularity.ChangeOfVars.applyLogTransform
#check @Singularity.ChangeOfVars.detectChangeOfVariables
```

The honest caveat is recorded in the definitions themselves: a reciprocal (or
logarithmic) transformation of a *polynomial* system generally produces a
*rational* right-hand side, which cannot be represented in the polynomial
`ODESystem` type without extending it. The conserved detector
`detectChangeOfVariables` therefore returns the original system with the identity
observable map, and the transformed vector fields are stated at the level of `ℝ →
ℝ` functions rather than pretended to be polynomial systems. The `CoV` type
enumerates `reciprocal`, `logarithmic`, and `power`; the observable map
`observableMaps : Fin M → (ℝ → ℝ)` records how to pull a measurement back to the
original coordinates.

For $`\dot x = x^2` the reciprocal change of variables $`w = 1/x` turns the flow
into $`\dot w = -1`, which is complete: the singular point is pushed off to
infinity, and the quantized operator on the transformed coordinates *is* essentially
self-adjoint. This is the concrete mechanism by which the manuscript's conclusion is
recovered — the Hamiltonian is made self-adjoint by completing the flow, not by the
auxiliary-operator argument the manuscript cites (see Nelson's section above).

# The Full Analysis Pipeline

The pieces assemble into a single `sirk_pipeline` (module `Singularity.Integration`)
that, given a system and an initial condition, builds the Weyl Hamiltonian, runs
the classical-flow analysis, computes the ESA report, detects a change of
variables, and returns a `UKDiagnosticCode × EsaReport`:

```
#check @Singularity.Integration.sirk_pipeline
#check @Singularity.Report.esaReport
#check @Singularity.Report.session_detect_singularity
```

The `EsaReport` (module `Singularity.Esa`) packages the flow-completeness
certificate with the deficiency indices, and `isEssentiallySelfAdjoint` decides
whether both deficiency indices vanish — the Nelson criterion at the algebraic
certificate layer:

```
#check @Singularity.Esa.EsaReport
#check @Singularity.Esa.deficiencyIndices
#check @Singularity.Esa.isEssentiallySelfAdjoint
```

# Validation Cases

ODE.tex §10 and module `Singularity.Tests` validate the pipeline against a suite of
benchmarks. The `x' = x^2` scalar case blows up at $`T = -1/x_0` and fails ESA
(UK-2101) until the reciprocal change of variables is applied; the coupled system
$`x' = y, y' = 2xy` is flow-incomplete; the reduced system `p_x·y + p_z·p_y·y^2`
has non-vanishing deficiency indices (UK-2104); the punctured system hits the
boundary $`y = 0` (UK-2102); and the stable linear system $`x' = -x` is complete,
so ESA holds and the SIRK evolution matches the analytic exponential decay:

```
#check @Singularity.Tests.runTest
#check @Singularity.Tests.TestCase
```

These describe the *intended* behaviour of the pipeline (the `x' = x^2`, coupled,
`py2`, punctured, and stable-linear benchmarks). They are specifications, not
verified theorems: `runTest` builds the report from the certificate placeholders
above, so the ESA/singularity verdicts they record are not yet analytic facts. They
are consistent with the corrected mathematics — in particular the `x' = x^2` case is
rightly expected to *fail* ESA as it stands on $`L^2(\mathbb{R})` (the flow is
incomplete), and to become ESA only after the reciprocal change of variables — but
the actual SIRK/unitary realization they point to remains open in the verified layer.

# The Price: Non-Determinism

The resolution comes at a cost the manuscript is explicit about: the evolution is
deterministic in the coordinate $`x` but *non-deterministic* in the
energy-bounded sample space. The Hamiltonian's spectral measure is conserved, but
the map from spectral variables to coordinates is non-trivial. This non-determinism
is the price paid for removing the singularity — and it is of a piece with the
book's recurring theme that passing from a probability distribution to a
wave-function trades determinism of the observable for the richer, reversible
structure of the wave-function.
