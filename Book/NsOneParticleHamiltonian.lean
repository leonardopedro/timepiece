import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Navier–Stokes One-Particle Hamiltonian and Its Fock Enclosure" =>
%%%
tag := "ns-one-particle-hamiltonian"
%%%

# The Final Hamiltonian of Record, and Why It Is a One-Particle Statement

:::paragraph
The {ref "fourier-elimination"}[Fourier-elimination chapter] fixed the strategy: the derivative
variables are *eliminated* by a spatial Fourier transform, not constrained by a gauge symmetry, so
that no ghost sector and no cubic derivative symbol survives. This chapter records what the
elimination buys on the **operator** side, and states the final Hamiltonian of record in the shape
the whole programme uses — QYM, QED, QG and Navier–Stokes alike:

$`H = \sum_{i,j} h_{ij}\, C^\dagger(e_i)\, A(e_j),`

the outer **second quantization** $`d\Gamma(h)` of an inner **one-particle** Hamiltonian $`h`,
with creation on the left and annihilation on the right. For Navier–Stokes the one-particle space of
the eliminated (reduced) sector is $`h = L^2(\mathbb{R}^6)` — one parcel's six coordinates
$`(u_i, q_i)` — and the one-particle Hamiltonian is the Weyl-ordered sum of squares of the seven
reduced constraint forms,

$`H_{\rm sp} \;=\; H_{\rm visc} + H_{\rm advect},
\qquad
H_{\rm visc} = \tfrac12\sum_{m<6}\pi_m^2 + \tfrac12\sum_{r \in \text{vis}}\big({\rm mulOp}\,\Phi_r\big)^2,
\qquad
H_{\rm advect} = \tfrac12\sum_{i<3}\big((k\cdot u)\,u_i\big)^2.`

Everything else in this chapter is the verification of the three claims that sentence contains: that
the one-particle operator really is that generator, that it is symmetric and bounded below so its
Friedrichs realization is a legitimate comparison operator, and that the outer Hamiltonian really is
its second quantization — no further square, no perturbation, no regularization.
:::

# The Momentum Variables: a Diagonal Derivative and a Partial Transform

:::paragraph
The elimination is only as good as the momentum variables it introduces, so the first obligation of
the plan is that the spatial Fourier transform is a unitary on the one-particle space and that on it
the derivative is *multiplication by a real symbol* — the symbol of the eliminated constraint.

On $`L^2(V)`, `l2Fourier` is the Plancherel identification, `fourier_opL2_eq_mulSymbol` is the
statement that an operator whose Schwartz form is multiplication by a real symbol $`\sigma` *is*
multiplication by $`\sigma` after the transform, and `fourier_opL2_momentumOp` is the specialization
to $`\pi_m = -i\partial_m`, whose symbol is $`2\pi\langle\xi, m\rangle`. The companion
`foSymbolFn_add_fibre` says the symbol of a *spatial* family of directions is unchanged when the
frequency is moved by a vector orthogonal to them, and `spatialMomentum_esa` records that the
momentum family is essentially self-adjoint on the Schwartz core, so the derivative side of the
construction is a proved instrument rather than a formal manipulation:
:::

```
#check @BookProof.NsSpatialMultiplier.l2Fourier
#check @BookProof.NsSpatialMultiplier.fourier_opL2_eq_mulSymbol
#check @BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp
#check @BookProof.NsSpatialMultiplier.foSymbolFn_add_fibre
#check @BookProof.NsSpatialMultiplier.spatialMomentum_esa
```

:::paragraph
The spatial transform must leave the *fibre* — the field's own variable — alone; otherwise there is
no elimination at all, only a change of variables in the whole space. The vector-valued model is
`L²(V; F)`, and the transform is `partialFourier`. Its one structural property is
`partialFourier_fibreOp`: it commutes with the pointwise action of *every* bounded operator of the
fibre, which is exactly what "partial" means. The derivative statement is
`fourier_vecMomentumOp_apply`, and §4 of the chapter is the concrete Navier–Stokes instance
$`F = L^2(W)`: `nsPartialFourier_fibreOp` (the transform leaves the field variable alone),
`nsPartialFourier_fibreFourier` and `nsPartialFourier_comp_fibreFourier_eq` (its composite with the
transform of the field variable is the full transform in both variables). A reusable by-product is
`postcompCLM`, the postcomposition of a Schwartz function with a continuous linear map of the target,
with `postcompCLM_lineDerivOp`, `fourier_postcompCLM` and `toLp_postcompCLM` — Mathlib does not
provide it.

The honest boundary is the model: the construction is the vector-valued `L²(V; L²(W))`, and its
measure-theoretic identification with the scalar `L²(V × W)` is not formalized, because Mathlib does
not have it.
:::

```
#check @BookProof.NsPartialFourier.partialFourier
#check @BookProof.NsPartialFourier.partialFourier_norm
#check @BookProof.NsPartialFourier.partialFourier_fibreOp
#check @BookProof.NsPartialFourier.fourier_vecMomentumOp_apply
#check @BookProof.NsPartialFourier.nsPartialFourier
#check @BookProof.NsPartialFourier.nsPartialFourier_fibreOp
#check @BookProof.NsPartialFourier.nsPartialFourier_comp_fibreFourier_eq
#check @BookProof.NsPartialFourier.postcompCLM
```

# The Constraint Solved: the Inverse Field Momentum

:::paragraph
The derivative gauge, read as a substitution rather than as a symmetry, solves the constraint for the
derivative mode: $`u^{(1)}_j = p_j\,\pi^{-1}`, where $`\pi_m = -i\partial_m` is the field momentum in
the fibre variable. The genuine analytic question the plan flags is the domain of $`\pi^{-1}`,
because $`\pi_m` is not boundedly invertible. The chapter settles it in the momentum representation of
the fibre variable, where — by `isMomInverse_momentumOp` — the field momentum *is* multiplication by
the real symbol $`\sigma(\xi) = 2\pi\langle\xi,m\rangle`:

 * `volume_momSymbol_zero` and `momSymbol_ne_zero_ae`: the symbol vanishes only on a hyperplane, a
   Lebesgue-null set. Consequently `momentum_kernel_trivial` — there is no kernel to split off, the
   `u`-constant mode the plan worried about is not an `L²` state — and `isMomInverse_unique`, the
   inverse is single valued;
 * `isMomInverse_of_memLp` is the honest domain criterion (the divided symbol is square integrable),
   `momDomain` is that domain as a submodule, and `momDomain_dense` proves $`\pi^{-1}` densely
   defined by cutting off a neighbourhood of the hyperplane `{σ = 0}`;
 * `isMomInverse_smul` is the physical identity $`u^{(1)}_j = p_j\pi^{-1}` and `eq_div_of_mul_eq_ae`
   its symbol form: a symbol $`t` with $`\sigma\cdot t = p` is $`p/\sigma` almost everywhere, so the
   derivative mode is *determined* by the constraint.
:::

```
#check @BookProof.NsFieldMomentumInverse.momSymbol
#check @BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae
#check @BookProof.NsFieldMomentumInverse.momentum_kernel_trivial
#check @BookProof.NsFieldMomentumInverse.isMomInverse_unique
#check @BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp
#check @BookProof.NsFieldMomentumInverse.momDomain_dense
#check @BookProof.NsFieldMomentumInverse.isMomInverse_smul
#check @BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp
```

# The Advection Becomes a Convolution

:::paragraph
Eliminating the derivative does not make the nonlinearity disappear — it changes its *kind*: in
momentum space the advection is not a differential operator but a **convolution**. The chapter proves
the momentum-space identity that the reduced letters $`(k\cdot u)u_i` stand for, for Schwartz velocity
components on a finite-dimensional real inner-product space:

 * `fourier_fourier_apply`: the double transform is the reflection, $`\mathcal F(\mathcal F f)(x) = f(-x)`;
 * `fourier_mul_eq_convolution`: the product-to-convolution theorem
   $`\mathcal F(f\,g)(Q) = \int \mathcal F f(q)\,\mathcal F g(Q-q)\,dq`, the *dual* of Mathlib's
   convolution theorem, obtained from it by Fourier inversion;
 * `fourier_lineDeriv_apply`: the derivative as a symbol,
   $`\mathcal F(\partial_m u)(q) = 2\pi i\,\langle q,m\rangle\,\mathcal F u(q)`;
 * `fourier_advection_convolution` and `fourier_advection_sum`: the item's theorem,
   $`\mathcal F[u_j\partial_m u_i](Q) = \int 2\pi i\,\langle q,m\rangle\,\hat u_i(q)\,\hat u_j(Q-q)\,dq`
   and its sum over a finite family of directions — the momentum-space replacement of the
   derivative-gauge generator.

The normalization is Mathlib's, $`\mathcal F f(\xi) = \int e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx`,
in which the convolution theorem carries no $`(2\pi)^{-d/2}` factors and the factor $`2\pi i\,q_j` is
the exact symbol of $`\partial_j`.
:::

```
#check @BookProof.NsAdvectionConvolution.fourier_fourier_apply
#check @BookProof.NsAdvectionConvolution.fourier_mul_eq_convolution
#check @BookProof.NsAdvectionConvolution.fourier_lineDeriv_apply
#check @BookProof.NsAdvectionConvolution.fourier_advection_convolution
#check @BookProof.NsAdvectionConvolution.fourier_advection_sum
```

# Uniformity Under the Energy Cutoff

:::paragraph
One obligation of the route is a *quantitative* one, and it is where the energy cutoff stops being
cosmetic: after the elimination the reduced forms carry the mode coefficients $`i k_j` and
$`-|k|^2`, and under the cutoff $`|k_j| \le \Lambda` they must be bounded by $`O(\Lambda)` **uniformly
in the parcel number `n`**, since that uniformity is what makes an `ℓ²`-lift of the sector
Hamiltonians possible. For the landed reduced family:

 * `norm_coeff_redVisc_le`, `norm_coeff_redAdvectPoly_le`, `norm_coeff_redMomentumPoly_le` and the
   headline `norm_coeff_redFormPoly_le`: every coefficient of every reduced form of every parcel is
   bounded by `cutoffBound ν Λ = 1 + 3Λ + 3|ν|Λ²` — the bound does not depend on the parcel number,
   on the parcel, on which of the seven forms is taken, or on the monomial;
 * `totalDegree_redFormPoly_le`: the reduced forms have degree at most two, uniformly;
 * `vars_redFormPoly_subset`: **parcel locality** — a reduced form involves only the six coordinates
   of its own parcel, so with the fixed number seven of forms per parcel the row/column (Schur) data
   of the sector Hamiltonians is independent of `n`;
 * `norm_coeff_redFormPoly_unbounded_of_no_cutoff`: the cutoff is *necessary* — without it the
   coefficients are unbounded, since the advection coefficient is $`k_j` itself.

This settles the coefficient half of the uniformity obligation. The operator-level relative bound
with a constant independent of `n` is *not* proved here — and on the landed route it is not needed
either, because the comparison actually used is the lifted Friedrichs extension of the reduced
Hamiltonian itself, for which the Faris–Lavine commutator constant is `c = 0`.
:::

```
#check @BookProof.NsCutoffUniformity.cutoffBound
#check @BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le
#check @BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le
#check @BookProof.NsCutoffUniformity.vars_redFormPoly_subset
#check @BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff
```

# The One-Body Generator, and the Outer Hamiltonian as Its Second Quantization

:::paragraph
Now the operator itself. The seven one-parcel forms are `spFormPoly`, and
`redFormPoly_eq_liftParcel` identifies them with the landed `n`-parcel family parcel by parcel — the
one-body generator really is the single-parcel member of the reduced family, not a new object. The
generator `spHam` on a core representation of the Gauss–polynomial core of `L²(ℝ⁶)` splits,

`spHam_eq_visc_add_advect` — $`H_{\rm sp} = H_{\rm visc} + H_{\rm advect}` — with `H_visc` carrying
the six momenta and the four non-advective squares and `H_advect` the three advection squares, whose
form is the momentum convolution of the previous section. Nothing is dropped and nothing is demoted
to a perturbation. The two Faris–Lavine inequalities then hold *for the exact nonlinear generator*:

 * `spVisc_symmetricOn`, `spAdvect_symmetricOn`, `spHam_symmetricOn` — symmetry on the core;
 * `spVisc_quadForm_nonneg`, `spAdvect_quadForm_nonneg`, `spHam_quadForm_nonneg` — positivity, with
   `spHam_quadForm_split` adding the two form contributions back to the generator's;
 * `spAdvect_apply` — the advection half is the multiplication operator of the convolution form.
:::

```
#check @BookProof.NsOneBody.spFormPoly
#check @BookProof.NsOneBody.redFormPoly_eq_liftParcel
#check @BookProof.NsOneBody.spHam_eq_visc_add_advect
#check @BookProof.NsOneBody.spVisc_symmetricOn
#check @BookProof.NsOneBody.spAdvect_symmetricOn
#check @BookProof.NsOneBody.spHam_quadForm_nonneg
#check @BookProof.NsOneBody.spHam_quadForm_split
#check @BookProof.NsOneBody.spAdvect_apply
```

:::paragraph
The comparison operator is the **Friedrichs realization of the generator itself** — `spFried`, with
`polyGaussCore_le_spFriedDom` the domain obligation — so the criterion is used in its `H = N`,
`c = 0` form (`spHam_commForm_zero`), and `spHam_esa_farisLavine` is the essential
self-adjointness of the one-particle operator, `spFried_isPositiveSelfAdjointExtension` the
extension statement. Then the second quantization: `nsOnePart` and `nsSpCol` are the generator in the
product Hermite basis, `nsSpCol_isHermCol` / `nsSpCol_isPosCol` are the column conditions the
`dΓ` machinery needs, and

 * `nsSpDGamma_symmetricOn`, `nsSpDGamma_quadForm_nonneg`, `nsSpDGamma_friedrichs_extension`,
   `nsSpDGammaFried_isPositiveSelfAdjointExtension`;
 * **`nsSpDGamma_esa_farisLavine`** — essential self-adjointness of $`d\Gamma(H_{\rm sp})` on the
   domain of its lifted comparison operator;
 * `nsSpDGamma_number_conserving` — every particle-number sector is preserved, so the outer operator
   is *quadratic* in the outer ladders (this is the structural reason a quartic nonlinearity costs
   nothing at the outer level: it lives entirely in the one-particle matrix elements);
 * `nsSpDGamma_one_particle` — on the one-particle sector $`d\Gamma` *is* the generator;
 * `spHam_stone_flow` and `nsSpDGamma_stone_flow` — by Stone's theorem each realization generates a
   strongly continuous one-parameter unitary group, which is the single-time package of the route.
:::

```
#check @BookProof.NsOneBody.spFried
#check @BookProof.NsOneBody.polyGaussCore_le_spFriedDom
#check @BookProof.NsOneBody.spHam_esa_farisLavine
#check @BookProof.NsOneBody.nsSpCol
#check @BookProof.NsOneBody.nsSpDGamma_quadForm_nonneg
#check @BookProof.NsOneBody.nsSpDGamma_esa_farisLavine
#check @BookProof.NsOneBody.nsSpDGamma_number_conserving
#check @BookProof.NsOneBody.nsSpDGamma_one_particle
#check @BookProof.NsOneBody.nsSpDGamma_stone_flow
```

:::paragraph
One structural identification used to be a *reading* and is now a theorem. The reduced `n`-parcel
Hamiltonian is the sum of `n` copies of the one-body generator — the `p`-th copy written in that
parcel's six coordinates and six momenta — not merely something that behaves as if it were. The
parcel summand is `redParcelHam` (symmetric and positive by `redParcelHam_symmetricOn` /
`redParcelHam_quadForm_nonneg`), `redHam_eq_sum_parcel` is the decomposition at the one-particle
level, `nsRedFullFockHam_sector_sum_parcel` transports it to the outer Hamiltonian's `n`-parcel
sector, and `weylOpDom_block_sum` is the general regrouping of a Weyl-ordered sum of squares into
blocks — the bookkeeping that makes the parcel decomposition compatible with the outer sum.
:::

```
#check @BookProof.NsOneBody.redParcelHam
#check @BookProof.NsOneBody.redParcelHam_symmetricOn
#check @BookProof.NsOneBody.redParcelHam_quadForm_nonneg
#check @BookProof.NsOneBody.redHam_eq_sum_parcel
#check @BookProof.NsOneBody.nsRedFullFockHam_sector_sum_parcel
#check @BookProof.NsOneBody.weylOpDom_block_sum
```

# Why Not the Mainstream Generator

:::paragraph
There is a tempting alternative one-particle operator, and it is the wrong one. The *mainstream*
incompressible Navier–Stokes system $`\dot u = -\nu A u + B(u,u)`, with Leray's energy identity
$`\sum_i u_iB_i = 0` and the Liouville identity $`\sum_i \partial_i B_i = 0`, has its own
Hamiltonian — the Koopman–von Neumann (Liouville) generator
$`H_{\rm NS} = -\tfrac i2\sum_m(\pi_m F_m + F_m\pi_m)` of the induced flow on wave functions, i.e. the
Hermitized "momentum times drift" shape, which is *not* a Weyl-ordered sum of squares. The chapter on
it proves what that shape can and cannot do:

 * `kvnPoly` / `nsKoopmanOp` — the Hamiltonian with the **exact** nonlinearity (no truncation, no
   linearization, no perturbative splitting), and `nsKoopmanOp_symmetricOn` — it is symmetric on the
   Gauss–polynomial core, so it passes the first Faris–Lavine requirement;
 * `quadP_starP` — the antiunitary conjugation $`C\psi = \bar\psi` anticommutes with it, so the
   numerical range is *symmetric about zero*; `gpair_hermite_kvn` computes the exact one-mode
   Hermite matrix element and shows the advection drops out of it by a degree-parity selection rule,
   while the viscous part grows like `n`;
 * `nsKoopmanOp_not_bounded_below` and `nsKoopmanOp_not_positive` — **the conclusion**: for
   $`\nu > 0` and one positive Stokes eigenvalue the quadratic form of $`H_{\rm NS}` is unbounded
   below. The mainstream generator can never be the positive comparison operator `N`, and the
   shortcut `H = N`, `c = 0` is not available for it.

What the chapter does supply is the *replacement* comparison operator, on the mainstream leg: the
Leray energy `energyPoly` / `nsEnergyOp`, i.e. multiplication by $`E = 1 + \|u\|^2` — positive and
$`\ge 1` by `nsEnergyOp_quadForm_ge`. The commutator is computed exactly,
`kvn_comm_energy` with the flux identity `fluxPoly_eq`: $`i[H_{\rm NS},N_E] = F\cdot\nabla E =
-2\nu\sum_i\lambda_i u_i^2` — the advection and the pressure gradient cancel by Leray's identity —
giving the Faris–Lavine commutator inequality `commForm_kvn_energy_bound`,
$`|\langle x, i[H_{\rm NS},N_E]x\rangle| \le 2\nu\Lambda\,\langle x, N_E x\rangle`, and then
`nsKoopman_esa_of_energy_comparison`. Non-vacuity is `nsTriad`, the resonant Navier–Stokes Fourier
triad with $`a+b+c = 0`.
:::

```
#check @BookProof.NsKoopman.kvnPoly
#check @BookProof.NsKoopman.nsKoopmanOp_symmetricOn
#check @BookProof.NsKoopman.quadP_starP
#check @BookProof.NsKoopman.gpair_hermite_kvn
#check @BookProof.NsKoopman.nsKoopmanOp_not_bounded_below
#check @BookProof.NsKoopman.nsKoopmanOp_not_positive
#check @BookProof.NsKoopman.nsEnergyOp_quadForm_ge
#check @BookProof.NsKoopman.kvn_comm_energy
#check @BookProof.NsKoopman.commForm_kvn_energy_bound
#check @BookProof.NsKoopman.nsKoopman_esa_of_energy_comparison
#check @BookProof.NsKoopman.nsTriad
```

# What Is Verified, and What Is Open

:::paragraph
The verified layer, in one list:

 * the eliminated sector's one-particle operator $`H_{\rm sp} = H_{\rm visc} + H_{\rm advect}` is
   the single-parcel member of the landed reduced family (`redFormPoly_eq_liftParcel`), symmetric and
   positive on the Gauss core for the **exact** nonlinearity (`spHam_symmetricOn`,
   `spHam_quadForm_nonneg`), with a Friedrichs realization as comparison and `c = 0`
   (`spHam_esa_farisLavine`);
 * its second quantization $`d\Gamma(H_{\rm sp})` is essentially self-adjoint on the lifted domain,
   preserves particle number, and restricts to the generator on the one-particle sector
   (`nsSpDGamma_esa_farisLavine`, `nsSpDGamma_number_conserving`, `nsSpDGamma_one_particle`), and the
   `n`-parcel reduced Hamiltonian is the sum over parcels of the one-body generator
   (`redHam_eq_sum_parcel`, `nsRedFullFockHam_sector_sum_parcel`);
 * the momentum variables are honest: a unitary partial transform that leaves the fibre alone, a
   derivative that is a real symbol, a densely defined $`\pi^{-1}` with trivial kernel, and the
   advection as a convolution whose coefficients are $`O(\Lambda)` uniformly in the parcel number;
 * the mainstream generator is symmetric but **indefinite**, so it cannot be the comparison operator
   of the criterion; its own leg carries the Leray-energy comparison instead.

What remains open on this leg, stated as obligations rather than as caveats:

 * the identification of the vector-valued `L²(V; L²(W))` with the scalar `L²(V × W)` (a
   Bochner–Fubini statement about slices; not in Mathlib);
 * the operator-level relative bound with a constant independent of the parcel number — not needed on
   the landed route, where the comparison is the lifted Friedrichs realization;
 * the identification of the parcel sectors with the symmetric tensor powers of the one-particle
   space (the remaining item of the record-definitions section of the plan);
 * on the mainstream leg, the surjectivity of $`N_E + 1` on a concrete domain (weighted
   Sobolev/Gauss), and the lift of that comparison operator to the nested-Fock setting.
:::
