import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "NS Numerics: Laminar Decay, Advection Symmetry, Turbulence Laws" =>
%%%
tag := "ns-numerics"
%%%

# What the NS Numerics Measure

:::paragraph
The companion solver's Navier–Stokes validation suite measures three things:
the *laminar decay rate* $`\nu k^2`$ of a diffusing velocity mode, the
*advection symmetry* that makes the quadratic generator a legitimate
Hamiltonian, and the *energy bookkeeping* (Ehrenfest identities, conserved
norm, no-blowup bounds) that distinguishes a computation about the
Navier–Stokes generator from an artifact of the discretization. Each of the
three has a verified counterpart in `BookProof`, and this chapter is the
map from the measured number to the theorem that licenses it.
:::

:::paragraph
This is an honesty page in the same style as the constants-suite chapter:
where the verified layer proves the statement, the theorem is named; where
the physical claim (a real viscosity, a real turbulence cascade) enters as
an *input*, we say so. Nothing here claims a continuum Navier–Stokes
result — the truncation boundary is stated with the theorems that live on
it.
:::

# The Laminar Decay Rate: Diffusive Decay of the Parabolic Part

:::paragraph
The laminar-regime test evolves $`du/dt = -\nu k^2 u`$ and measures the
exponential decay rate. The verified counterpart is the parabolic-semigroup
theorem: for a *coercive* bounded generator $`A`$ — one satisfying
$`\mu\|x\|^2 \le \operatorname{Re}\langle x, A x\rangle`$ — the heat
semigroup $`e^{-tA}`$ decays at exactly the coercivity rate, in vector norm
and in operator norm. The coercivity constant $`\mu`$ is precisely the
$`\nu k^2`$ the numerics read off the reduced model:
:::

```
#check @BookProof.ChapterSirkDiffusiveDecay.heatFlow
#check @BookProof.ChapterSirkDiffusiveDecay.IsCoercive
#check @BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_apply_le
#check @BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_le
```

:::paragraph
The decay bound is proved by a Grönwal argument on the weighted energy
$`\|e^{-tA}v\|^2 e^{2\mu t}`$: the energy identity
$`d/dt\,\|u(t)\|^2 = -2\operatorname{Re}\langle u(t), Au(t)\rangle`$ makes
the weight antitone, and the bound $`\|e^{-tA}v\| \le e^{-\mu t}\|v\|`$
follows for every $`t \ge 0`$. Crucially, the theorem is *exact at the
rate* — not merely asymptotic — which is what makes the measured decay
constant a certificate rather than a fit.
:::

:::paragraph
The reduction-invariance half of the statement is what connects the theorem
to the solver's Galerkin/SIRK reduction: the compression $`V^*AV`$ of a
coercive generator along an isometry is coercive with the *same* constant,
so the reduced propagator obeys the identical decay bound at every
reduction order. The measured laminar rate is therefore not an artifact of
the truncation:
:::

```
#check @BookProof.ChapterSirkDiffusiveDecay.isCoercive_compress
#check @BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_compress_apply_le
```

:::paragraph
The honest boundary: identifying $`\mu`$ with $`\nu k^2`$ for a
*particular* discretization is the content of the per-mode symbol
computations in the Navier–Stokes chapters, and the numerical value of
$`\nu`$ is an input, not a theorem. The generator in the decay theorem is
bounded — the regime in which the project's Galerkin/Hashimoto reduction is
an operator statement; the unbounded case is the standing
Stone/Trotter–Kato boundary.
:::

# Advection Symmetry: The Generator is a Hamiltonian

:::paragraph
Every decay and energy statement above silently assumes the generator is
*symmetric* — otherwise there is no self-adjoint evolution and no conserved
energy to track. For the truncated Navier–Stokes Hamiltonian
$`H = \sum_i (\pi_i A_i + A_i \pi_i)`$ with the advective term
$`A_i = \sum_j u_j u_{i,j} - \nu u_{i,jj}`$, symmetry is proved term by
term: the advective part is symmetric on the domain because the modes are
symmetric and pairwise commuting and the viscosity is real:
:::

```
#check @BookProof.NavierStokesFlow.FullEsa.NSFullData.advection
#check @BookProof.NavierStokesFlow.FullEsa.NSFullData.advection_isSymmetricDom
#check @BookProof.NavierStokesFlow.FullEsa.NSFullData.hamiltonian_isSymmetricDom
```

:::paragraph
The same structure holds *untruncated*: on a dense domain of an arbitrary
inner-product space, with fifteen symmetric pairwise-commuting field modes
and three symmetric momenta, the full Hamiltonian is symmetric on its
domain unconditionally — and for concrete realizations (bounded lattice
modes on $`\ell^2(\mathbb{Z})`$, diagonal modes on $`\ell^2(\mathbb{N})`$)
it is essentially self-adjoint. The sharpness companion proves the
converse boundary: structural hypotheses alone can never yield essential
self-adjointness, so the analytic input (a complete flow) is indispensable:
:::

```
#check @BookProof.NavierStokesFlow.FullEsa.latticeFull_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.FullEsa.diagFull_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn
```

:::paragraph
The differential realization carries the polynomial-transport route: the
Weyl-ordered Hamiltonian is the core realization of an explicit polynomial
whose Gauss symmetry is checked purely algebraically, the closure is the
*unique* self-adjoint extension, and the Hashimoto selection theorem pins
down the operator the SIRK Krylov iteration computes — the shift-inverted
resolvents exist, are bounded by $`1/|\operatorname{Im}\gamma_j|`$, and
each single one determines the generator completely:
:::

```
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffPoly
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_eq_coreOp
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_symmetricOn
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension_unique
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_hashimoto_selects
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_shiftInvert_selects
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsQuadraticDiffH_hashimoto_selects
```

:::paragraph
For the numerics this is the difference between measuring *something* and
measuring *the* generator: the selection theorem guarantees the Krylov
subspace reconstructs spectral information about the differential
Navier–Stokes operator rather than an artifact of the shifts. The
Ehrenfest identities the validation checks exactly on probes
($`i\langle[H, u]\rangle = 4\kappa\langle u\rangle + 4c`$ on the affine
fiber) are statements about this selected operator.
:::

# Turbulence Laws: Energy Bookkeeping on the Truncation

:::paragraph
The classical turbulence laws — kinetic-energy balance, enstrophy
bookkeeping for the 2D inverse cascade, the Kolmogorov $`-5/3`$ inertial
spectrum — are *statistical* statements about solutions the verified layer
does not construct. What it does prove is the exact finite-dimensional
energy bookkeeping the numerical pipeline relies on: the truncated flow is
a one-parameter unitary group (norm preserving, no finite-time blowup,
unique global solutions of the Cauchy problem), and the expectation of the
Hamiltonian is conserved along it:
:::

```
#check @BookProof.NavierStokesFlow.nsFlow_unitary
#check @BookProof.NavierStokesFlow.nsFlow_norm_preserving
#check @BookProof.NavierStokesFlow.nsFlow_noBlowup
#check @BookProof.NavierStokesFlow.nsCauchy_existsUnique
#check @BookProof.NavierStokesFlow.nsFlow_energy_conserved
```

:::paragraph
The Lagrangian (parcel) form of the generator — the four-term operator
with positive advective Laplacian, positive viscous term, force drift, and
the volume-preservation constraint — is Hermitian on the truncation, so the
same completeness carries over: its flow is unitary and its Cauchy problem
has exactly one global solution. This is the truncated form of the
transformation route; the continuum statement remains unclaimed:
:::

```
#check @BookProof.NavierStokesFlow.LagrangianNS.flowUnitary_unitary
#check @BookProof.NavierStokesFlow.LagrangianNS.cauchy_existsUnique
```

:::paragraph
At the kinematic layer, the Eulerian constraint algebra is verified
symbolically: the momentum constraint and the divergence-free constraint
are consistent under the derivative field's consistency identities, and
the cyclic-shear test field is exactly divergence-free — the decidability
core that any turbulence-law computation must respect before it can claim
to represent an incompressible flow:
:::

```
#check @BookProof.NavierStokesEulerian.eulerian_momentum_constraint
#check @BookProof.NavierStokesEulerian.eulerian_divergence_constraint
#check @BookProof.NavierStokesEulerian.cyclicShear_divergence_free
```

# What Is Verified, and What Is Open

:::paragraph
The exactly-verified laminar decay bound $`\|e^{-tA}\| \le e^{-\mu t}`$
for coercive generators with reduction-invariance of the rate; advection
symmetry of the truncated and untruncated Navier–Stokes Hamiltonians with
essential self-adjointness on concrete realizations and the Hashimoto
selection of the differential generator; and the complete finite-dimensional
energy bookkeeping — unitary flow, norm preservation, no blowup, unique
global Cauchy solutions, conserved Hamiltonian expectation — on the
truncation and its Lagrangian transform.
:::

:::paragraph
Deliberately left open is everything statistical: the inertial-range spectrum
($`E(k) \sim k^{-5/3}`$), the enstrophy cascade and its 2D inverse
counterpart, intermittency, and any claim about a *continuum* solution.
The viscosity $`\nu`$ and the per-mode identification $`\mu = \nu k^2`$ are
numerical inputs consumed by the theorems, not outputs of them. The
sharpness theorem
(`BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn`)
marks exactly where structural reasoning must stop and analytic input must
begin — the same boundary the $`\dot{x} = x^2`$ warning of the ODE chapter
draws for flows.
:::
