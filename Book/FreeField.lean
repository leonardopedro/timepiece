import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Free Fields: the Gaussian and the Uniform Sphere" =>
%%%
tag := "free-field"
%%%

# Orientation: From the Manuscript to the Formal Development

:::paragraph
This chapter follows the free-field thread of `book.tex`, but the formal development
has two distinct layers. The probability and Gaussian constructions describe the
infinite-dimensional parametrization; the later Hamiltonian/SIRK material describes
finite truncations and their limits. A theorem citation below certifies only the exact
statement of its `BookProof` declaration. In particular, the QYM certificate currently
certifies a truncated value; the remaining specialist target is the lowest positive
one-particle edge and its lift through the free nested-Fock `dGamma` Hamiltonian.
:::

| Object | Formal status |
| :--- | :--- |
| Gaussian/Mehler and Born parametrization | proved model theorems |
| finite Krylov/SIRK approximation | proved/conditional error theorems |
| emitted QYM certificate | proved truncated enclosure |
| QYM Friedrichs/Hashimoto-selected operator | proved construction/selection |
| one-particle gap, lifted to Fock space | proved for the concrete gauge-fixed QYM one-particle operator, conditional on its one-particle *form* gap (`ChapterYangMillsFockGapChain`) |
| unbounded field perturbations of the gap | proved for the linear coupling `Φ(f)` (`ChapterFockFieldPerturbation`, `sorry`-free) and for the quadratic pair coupling `P(f,g)` (`ChapterFockPairPerturbation`); proved *impossible* for a bare cubic term (`ChapterFockCubicUnbounded`); the cubic–quartic pair is bounded below on all finite states (`ChapterFockCubicQuarticStability`) |
| gap for sectors with constant or diagonal one-particle energy | proved unconditionally: the R² scalaron at `m = 1/√(12α)` (`ChapterScalaronFockGapChain`) and any diagonal dispersion `ω_k = √(p_k² + m²)` (`ChapterFockDiagonalGapChain`) — no certificate, no form-gap hypothesis |
| real Fock mass gap of the continuum operator | still conditional on the one-particle form gap (the certificate supplies a truncated bound); no continuum claim |

# The Problem: There Is No Infinite-Dimensional Lebesgue Measure

:::paragraph
The new gap modules make the operator-level boundary explicit. `BookProof/ChapterFockOneParticleGap.lean` proves the positive one-particle edge statement under its spectral hypotheses; `ChapterFriedrichsFormGap.lean` packages the corresponding closed-form/Friedrichs route; and `ChapterBandEnclosure.lean` shows how nested finite bands can provide the remaining enclosure input. These are conditional analytic bridges, not a claim that numerical data alone proves the continuum gap.
:::

The finite-dimensional Born parametrization puts a uniform-looking measure on the
sphere and pushes it to the simplex. To pass to *field theory* — infinitely many
degrees of freedom — we would like a uniform (Lebesgue-like) measure on an
infinite-dimensional sphere. There is an immediate obstruction:

*There is no non-zero, translation-invariant measure that is finite on bounded sets in an infinite-dimensional normed space.*

The proof is a clean volume argument. In a translation-invariant measure, all balls
of a given radius have the same measure. In infinite dimension a ball of radius
$`r` contains *infinitely many* disjoint balls of radius $`r/2` (because there is
an infinite orthonormal set, and the small balls around well-separated points are
disjoint). If the small balls have measure $`m > 0`, the big ball has infinite
measure; if $`m = 0`, countable additivity is not even needed to see the big ball
has measure $`0` once it is covered by countably many null balls in the
finite-on-bounded case. Either way, no measure can be both translation-invariant and
finite and non-zero on bounded sets.

The verified statements (module `BookProof.ChapterNoLebesgue`):

```
#check @ChapterNoLebesgue.measure_ball_eq_measure_ball_zero
#check @ChapterNoLebesgue.not_exists_nonzero_isAddLeftInvariant_finite_on_bounded
```

This is the rigorous content of the manuscript's claim that "there is no
non-informative prior" on a continuous infinite-dimensional space, and it forces the
free-field construction to build its uniform measure *out of the Gaussian* rather
than out of a nonexistent Lebesgue measure.

# The Substitute: the Rotation-Invariant Gaussian

The standard Gaussian on $`\mathbb{R}^n`,

$$`\gamma_n(dx) = (2\pi)^{-n/2} e^{-\|x\|^2/2}\, dx,`

depends only on the radius $`\|x\|`. Consequently it is *rotation-invariant*:
pushing it forward by any orthogonal map $`L` leaves it unchanged. Its
characteristic function $`t \mapsto e^{-\|t\|^2/2}` likewise depends only on
$`\|t\|`, which pins down the measure and makes the invariance manifest.

The verified statements (module `BookProof.ChapterFreeFieldGaussian`):

```
#check @ChapterFreeFieldGaussian.instIsProbabilityMeasure_stdGaussian
#check @ChapterFreeFieldGaussian.charFun_stdGaussian
#check @ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv
```

The last is the headline: $`(\gamma_n).\mathrm{map}(L) = \gamma_n` for every
orthogonal $`L`. The Gaussian is the canonical *rotation-invariant probability
prior*, the finite-dimensional stand-in for the uniform measure that does not exist
in infinite dimension.

# Pushing the Gaussian to the Sphere

Because the Gaussian has no atom at the origin (in dimension $`n \ge 1`), radial
normalization $`x \mapsto x/\|x\|` is defined almost everywhere and pushes
$`\gamma_n` to a probability measure *on the unit sphere*. By rotation-invariance
of the Gaussian, this induced sphere measure is itself rotation-invariant — it is
the *uniform measure on the sphere*, constructed without ever invoking a
Lebesgue measure on the infinite-dimensional ambient space. This is the
manuscript's free-field prior: "a uniform measure of an infinite-dimensional sphere
defined using the Gaussian measure and the Fock space."

This uniform sphere measure is the *Mehler measure*, and it is the exception to the
slogan this chapter opened with. There is no _Lebesgue_ uniform probability measure
on an infinite-dimensional space, but the Gaussian-built sphere measure is a genuine
uniform prior on the infinite-dimensional hypersphere. It is genuinely
non-informative — invariant under every symmetry the language can express — in the
{ref "solovay-tensor"}[Solovay–Kopperman space], where the restricted decidable
language forbids the reparametrizations that would otherwise turn a uniform prior
into an informative one ({ref "sequential-bayes"}[non-informativeness is
coordinate-dependent]). The free-field construction is the finite-dimensional shadow
of that infinite-dimensional exception.

# Why the Gaussian Is the Uniform Measure on the Infinite Sphere: the Mehler Limit

:::paragraph
This probabilistic construction is also the domain in which the later Fock proofs operate. The unbounded-perturbation ladder is now complete at degrees one and two. `ChapterFockFieldPerturbation.lean` is `sorry`-free and controls the *linear* field coupling $`\Phi(f) = a^\dagger(f) + a(f)` — genuinely unbounded and number-changing — leaving the gap `(μ − 2‖f‖)‖u‖²` on vacuum-orthogonal states. `ChapterFockPairPerturbation.lean` carries the same package to the *quadratic*, pair-creating coupling $`P(f,g) = a^\dagger(f)a^\dagger(g) + a(g)a(f)` (particle number changes by two), leaving the gap `(μ − 2√2‖f‖‖g‖)‖u‖²` under the smallness condition `2√2‖f‖‖g‖ < μ`. And `ChapterFockCubicUnbounded.lean` proves that the route *stops* there: a bare cubic term has no relative form bound at all, so `dΓ(N) + λC` is unbounded below at every coupling strength — the divergence is cured only by the (bounded-below) quartic term. `ChapterFockInteractionStability.lean` records the quantitative loss of a gap under a bounded or relatively form-bounded interaction, and `ChapterYangMillsFockGapChain.lean` instantiates the whole chain for the concrete gauge-fixed QYM one-particle operator, conditionally on its one-particle form gap.
:::

The claim that the Gaussian is the uniform measure "on an infinite-dimensional
sphere" is not a slogan; it is a genuine limit, due in spirit to Mehler (1866) and
made quantitative by López and Temme. On the surface of a $`k`-sphere the
rotation-invariant (uniform) area element factorizes into single-coordinate weights
$`(1-x^2)^{(\alpha-1)/2}` — exactly the *Gegenbauer* weight of order $`\alpha`.
The uniform hyperspherical measure is therefore the natural *prior*: it assigns equal
weight to every direction, expressing that we have no information. Its orthogonal
polynomials are the Gegenbauer polynomials $`C_n^{(\alpha/2)}`.

The infinite-dimensional limit is where the identification becomes the Gaussian.
Rescale the coordinate $`x \mapsto \sqrt{2/\alpha}\,x` and let $`\alpha \to \infty`.
The single-coordinate hyperspherical weight tends to the Gaussian weight
$`e^{-x^2}`:

$$`\lim_{\alpha\to\infty}\Bigl(1 - \tfrac{x^2}{\alpha}\Bigr)^{\alpha-1/2} = e^{-x^2}.`

The verified statement (module `BookProof.PhysHSGaussian`):

```
#check @PhysHSGaussian.weight_tendsto_gaussian
```

At the same time the Gegenbauer polynomials become the Hermite polynomials
$`H_n/n!` (with the physicists' $`H_n` defined by the recurrence
$`H_0 = 1, H_1 = 2x, H_{n+2} = 2x H_{n+1} - 2(n+1)H_n`), in the scaled limit

$$`\lim_{\alpha\to\infty}\Bigl(\tfrac{\alpha}{2}\Bigr)^{-n/2}
  C_n^{(\alpha/2)}\Bigl(\sqrt{\tfrac{2}{\alpha}}\,x\Bigr)
   = \frac{H_n(x)}{n!}.`

The verified statement (module `BookProof.PhysHSGaussian`):

```
#check @PhysHSGaussian.physHermite
#check @PhysHSGaussian.gegenbauer
#check @PhysHSGaussian.gegenbauerScaled
#check @PhysHSGaussian.gegenbauerScaled_tendsto_hermite
```

The normalizations converge consistently as well: the (squared) Gegenbauer
normalization integral against the hyperspherical weight tends to the Hermite
normalization integral against the Gaussian weight,

$$`\int_\mathbb{R}\Bigl[\frac{H_n(x)}{n!}\Bigr]^2 e^{-x^2}\,dx
   = \frac{\sqrt{\pi}\,2^n}{n!}.`

The verified statements (module `BookProof.PhysHSGaussian`):

```
#check @PhysHSGaussian.hermite_normalization
#check @PhysHSGaussian.normalization_tendsto
```

This is the precise sense in which the uniform (hyperspherical) prior and the
Gaussian (Fock) vacuum coincide, and in which the orthogonal excitations of the Fock
space are the images of the hyperspherical harmonics. The dictionary is complete:

| Finite hypersphere ($`\alpha < \infty`) | Infinite-dimensional limit (Fock) |
| :--- | :--- |
| uniform surface measure $`d\sigma` | Gaussian measure $`e^{-x^2}dx` |
| Gegenbauer weight $`(1-x^2)^{(\alpha-1)/2}` | Gaussian weight $`e^{-x^2}` |
| Gegenbauer polynomials $`C_n^{(\alpha/2)}` | Hermite polynomials $`H_n/n!` |
| hyperspherical harmonics | number states $`\ket{n}` |
| uniform "no-information" prior | Gaussian source qsample $`\Psi_0 = \ket{0}` |

That the Gaussian pushes forward to the *uniform* sphere measure, and is itself
rotation-invariant, is proved in the same module (and is the mechanism used above to
build the sphere measure in the first place):

```
#check @PhysHSGaussian.gaussianE_rotation_invariant
#check @PhysHSGaussian.sphereUniform_rotation_invariant
```

And the concentration is quantitative: for an almost-every sequence of standard
Gaussian coordinates, the empirical squared norm $`\sum_{i<k}\omega_i^2` grows like
$`k`, i.e. the Gaussian sample sits on the sphere of radius $`\sqrt{k}` in the
limit — the strong-law form of "the Gaussian concentrates on the sphere":

```
#check @PhysHSGaussian.gaussian_concentration_sphere
```

So the free-field prior is not merely *a* rotation-invariant measure: it is the
infinite-dimensional limit of the family of uniform hyperspherical priors, with the
Fock excitations as the limits of the hyperspherical harmonics. This is what makes
the Gaussian source qsample $`\sqrt{p_0}` of a flow model coincide with the Fock
vacuum that the companion algebra manipulates natively.

# Born Pushes the Sphere to the Simplex

Composing the two maps — normalize the Gaussian to the sphere, then apply the Born
rule $`\psi \mapsto |\psi|^2` — parametrizes the probability simplex by the
Gaussian-built sphere measure. The finite-dimensional Born map is continuous and
surjective ({ref "born-reproduces"}[The Born rule reproduces every distribution]),
and its fibers are the phase/sign gauge of
{ref "born-fiber"}[the gauge ambiguity]. The simplex is thus realized as a
*quotient* of the Gaussian-built sphere by the gauge group, with a canonical
rotation-invariant measure on top.

# Differentiability in the Fourier-Transformed Space

The manuscript's free-field section is careful about a cost of the parametrization:
because the uniform prior attributes null measure to *deterministic* functions, one
*sacrifices point-evaluation* of a classical field, and so "continuity and
differentiability notions must be redefined for quantum fields". Its justification
that this is not a problem is that *the smooth wave-functions are dense in the
Hilbert space* — an approximation statement.

That justification is correct but incomplete. The stronger fact is that, in the
Fourier-transformed space, the field is already smooth almost everywhere, not merely
approximable by smooth functions. The momentum constraint of the free-field section
is $`iD_x = 0` with $`p` the eigenvalue of the derivative operator that the Fourier
transform diagonalizes: in the Fourier picture, differentiation is multiplication by
a real frequency, and the (Fourier-transformed) wave-function that defines the
creation operator is the analytic continuation of that frequency function. Analytic
functions are smooth everywhere, so the represented field is smooth on the
transformed space — the null-measure caveat of the manuscript's point-evaluation
discussion is discharged in the Fourier domain *before* any density argument is
needed.

The same phenomenon appears in number-theoretic series: the series used in
Bagchi's universality theorem (and the Dirichlet series it is built from) is
convergent and analytic on a half-plane, and its analytic continuation is smooth
almost everywhere in the transformed (frequency) variable. There too the smoothness
is not an approximation imposed by a choice of prior; it is a property the analytic
continuation already has. The manuscript's density argument describes what is true
in the *original* (position) space; the sharper statement is that the *Fourier* or
frequency representation of the same object is already smooth, so the
differentiability notions the manuscript says must be "redefined" are in fact
satisfied pointwise (almost everywhere) on the transformed side.

The density assertion the manuscript relies on is itself verified
(`polynomial_dense_L2` in `BookProof.PhysFunctionalAnalysis`: polynomials — hence
smooth functions — are dense in $`L^2` with respect to the uniform
(unit-interval) measure):

```
#check @PhysFunctionalAnalysis.polynomial_dense_L2
```

This is the approximation statement: it says smooth functions are *close* to every
$`L^2` field. The Fourier-domain observation above is the strictly stronger one: in
the transformed space the field is already smooth a.e., so no approximation step is
needed there. Both facts coexist — the former concerns the original space, the
latter concerns its Fourier representation.

This is consistent with, and sharpens, the rest of the free-field thread: the
Gaussian-built uniform measure is rotation-invariant, its Fourier transform is the
same Gaussian (self-dual), and the frequency representation of a field drawn from
that prior is a smooth, analytically-continuable object rather than a merely
approximable one.

# A Countability Sanity Check

One last measure-theoretic fact keeps the countable Euler-angle parametrization of
{ref "born-reproduces"}[the Born-rule chapter] honest. The manuscript asserts that
"any partition of the phase-space (where each part has a non-null Lebesgue measure)
is countable." This is a general fact about s-finite measures: a pairwise-disjoint
family of measurable sets, *every* one of positive measure, must be countable —
because in each measure band $`[1/(k+1), 1/k]` there can be only finitely many
disjoint sets, and a countable union of finite sets is countable.

The verified statements (module `BookProof.ChapterCountablePartition`):

```
#check @ChapterCountablePartition.countable_of_partition_pos
#check @ChapterCountablePartition.prob_partition_countable
```

So when the book indexes the parts of a phase-space partition by a countable
orthonormal basis (the setting of the countable stick-breaking chain), it is not
making an extra assumption: positivity of the part measures *forces* the index set
to be countable.

# Dimensional Reduction: the Krylov Shortcut and the Compiled Sketch

:::paragraph
The same Gaussian/Fock substrate is what makes the *computational* side of the
free-field thread tractable. Two reductions do the work. The first is the
inversion-free Krylov shortcut: the Krylov subspace
$`\mathrm{Kry}_m(\bar H, v_0) = \mathrm{span}\{v_0, \bar H v_0, \dots, \bar H^{m-1}v_0\}`
is unchanged when the generator is shifted by a multiple of the identity, because
the shift only adds lower-order terms. So the sequence $`w_k = (\bar H - \gamma I)w_{k-1}`,
which never solves a linear system, spans exactly the same subspace as the
rational construction that would; and pre-conditioning the seed makes the
resolvent merely lower the polynomial degree. The generator itself is bounded —
the Mehler projector is rank-one, the number operators diagonal.
:::

```
#check @BookProof.ChapterH5.krylovSpan
#check @BookProof.ChapterH5.krylov_subspace_span
#check @BookProof.ChapterH5.shift_pow_sub_pow_mem
#check @BookProof.ChapterH5.krylovSpan_shift_eq
#check @BookProof.ChapterH5.inversion_free_seed
#check @BookProof.ChapterH5.generator_bounded_of_rankOneProjector
#check @BookProof.ChapterH5.krylov_no_inversion_eq_standard
```

:::paragraph
The second reduction reads the Krylov projection as a *spectral low-pass filter*.
The compression $`\bar H_{\text{reduced}} = V^{\mathsf H}\bar H V` has the
restricted quadratic form, so each of its eigenvalues is a Rayleigh quotient of
the full generator and can never exceed its norm: the projection keeps
frequencies, it does not invent them. What it discards costs only the $`e^{-hm}`
term already carried by the SIRK error bound, which decays to zero as the
retained dimension grows. And generation is then a *single* matrix exponential
of an explicitly $`m \times m` object.
:::

```
#check @BookProof.ChapterH6.sirk_error_decay_exponential
#check @BookProof.ChapterH6.sirk_error_bound_antitone
#check @BookProof.ChapterH6.krylov_rayleigh_transfer
#check @BookProof.ChapterH6.krylovRetainsDominantSpectrum
#check @BookProof.ChapterH6.reduce_generator_mul_m
#check @BookProof.ChapterH6.generation_single_exponential
```

:::paragraph
The reductions form a *nested tower of approximation orders*, and this nesting is
itself a decidable, finite-dimensional statement — the part of the Hashimoto
convergence guarantee that needs no analytic input. Write $`\mathrm{Kry}_n`$ for
the order-$`n`$ Krylov subspace $`\mathrm{Kry}_n(\bar H, v_0)`$. Two facts are
purely algebraic. First, the subspaces nest:
$`\mathrm{Kry}_n \subseteq \mathrm{Kry}_{n+1}`$
($`\mathrm{krylovSpan\_mono}`$): the order-$`n`$ basis is the first $`n`$ vectors
of the order-($`n`+1) basis. Second, the order-$`n`$ reduced generator is the
top-left $`n \times n`$ block of the order-($`n`+1) reduced generator, because the
compression is upper-Hessenberg — so the order-$`n`$ approximant is the
*projection* of the order-($`n`+1) approximant onto $`\mathrm{Kry}_n`$: the finer
band, restricted to the coarser information, reproduces the coarser band exactly.
And the error bound is monotone in the same direction: the band
$`[0, \mathrm{sirkBound}(n+1)]`$ is contained in $`[0, \mathrm{sirkBound}(n)]`$
($`\mathrm{sirk\_error\_bound\_antitone}`$), and the bands collapse to $`\{0\}`$
as $`n`$ grows ($`\mathrm{sirk\_error\_decay\_exponential}`$).
:::

```
#check @BookProof.ChapterH5.krylovSpan_mono
#check @BookProof.ChapterH5.krylovSpan_map_le
#check @BookProof.ChapterH6.sirk_error_bound_antitone
#check @BookProof.ChapterH6.sirk_error_decay_exponential
#check @BookProof.ChapterH6.sirk_error_tendsto_zero
#check @BookProof.ChapterH7.compress_isSelfAdjoint
#check @BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange
#check @BookProof.ChapterH8.sirk_krylov_tower
#check @BookProof.ChapterH8.sirk_compression_block
#check @BookProof.ChapterH8.sirk_compression_submatrix
#check @BookProof.ChapterH8.sirk_band_refinement
#check @BookProof.ChapterH8.sirk_band_refinement_proj
#check @BookProof.ChapterH8.sirk_approx_projection
#check @BookProof.ChapterH8.sirk_band_refinement_poly
#check @BookProof.ChapterH8.sirk_band_refinement_rational
#check @BookProof.ChapterH8.sirk_approx_projection_poly
#check @BookProof.ChapterH8.sirk_approx_projection_rational
#check @BookProof.ChapterH8.sirk_band_refinement_of_orthonormal
#check @BookProof.ChapterH8.sirk_compression_submatrix_of_orthonormal
#check @BookProof.ChapterH8.krylovOrthonormal_span
#check @BookProof.ChapterH8.krylovEmbedding_range
#check @BookProof.ChapterH8.sirk_band_refinement_krylov
#check @BookProof.ChapterH8.sirk_band_contained
#check @BookProof.ChapterH8.sirk_band_contained_le
#check @BookProof.ChapterH8.sirk_compression_submatrix_le
#check @BookProof.ChapterH8.sirk_nested_orders
#check @BookProof.ChapterH8.sirk_nested_orders_le
```

:::paragraph
The honest boundary: the *nesting* above is finite-dimensional linear algebra over
the decidable skeleton (Solovay–Mehler–Kopperman: every inner product over the
infinite substrate collapses to a finite head integral), so it is provable
without any analytic hypothesis. What the nesting does *not* supply is the
numerical *width* of the bands: that the true error lies inside
$`\mathrm{sirkBound}(n)`$ is conditional on Crouzeix's inequality
($`\mathrm{sirk\_error\_bound\_decay}`$, `ChapterH4`), which is recorded in
`BookProof/` as a named hypothesis rather than an axiom. The band-containment
statement itself — order-($`n`$+1) refines order-$`n`$, iterated — is proved in
`ChapterH8`: the block identity $`\mathrm{sirk\_compression\_block}`$, the
projection identities $`\mathrm{sirk\_band\_refinement}`$ and
$`\mathrm{sirk\_approx\_projection}`$, and the tower
$`\mathrm{sirk\_nested\_orders}`$ — which holds not only one step at a time but
between any two orders $`m \le n`$ ($`\mathrm{sirk\_nested\_orders\_le}`$, with
the leading-block identity $`\mathrm{sirk\_compression\_submatrix\_le}`$). The
refinement is not restricted to powers of
the generator: it holds for an arbitrary polynomial of the reduced generator
($`\mathrm{sirk\_band\_refinement\_poly}`$) and for the rational functions the
SIRK step actually evaluates — numerator polynomial over an invertible
denominator whose compression is invertible
($`\mathrm{sirk\_band\_refinement\_rational}`$), with the whole-space projection
forms $`\mathrm{sirk\_approx\_projection\_poly}`$ and
$`\mathrm{sirk\_approx\_projection\_rational}`$. The hypotheses are not vacuous:
any pair of nested orthonormal Krylov bases realizes them, through the embedding
of an orthonormal family and the coordinate inclusion along $`\mathrm{castLE}`$,
which gives the hypothesis-free instances
$`\mathrm{sirk\_band\_refinement\_of\_orthonormal}`$ and
$`\mathrm{sirk\_compression\_submatrix\_of\_orthonormal}`$. Those bases exist:
Gram–Schmidt on the Krylov sequence $`k \mapsto H^k v`$ produces one orthonormal
sequence whose prefixes are orthonormal, nested by construction and span the
Krylov subspaces ($`\mathrm{krylovOrthonormal\_span}`$,
$`\mathrm{krylovEmbedding\_range}`$), which gives the refinement statement for the
Krylov flag itself ($`\mathrm{sirk\_band\_refinement\_krylov}`$, under the
hypothesis that the Krylov sequence has not broken down before the finer order).
Two provisos are recorded
there. The refinement of the *approximants* needs the order-$`n`$ subspace to be
invariant under the compressed operator — the block-triangularity that makes the
leading block a generator in its own right; and the whole-space form of the projection
identity needs that subspace to *reduce* the operator (invariance under the
adjoint as well), since without it the leading block controls only the coarse
data.
:::

:::paragraph
The nesting has a spectral face as well: not only do the approximants refine, the
*frequencies* the reduced generators can see nest. Writing $`W(\cdot)`$ for the
numerical range — the set of Rayleigh quotients over unit vectors — the reduced
generators $`B_k = V_k^{*} X V_k`$ satisfy
$`W(B_m) \subseteq W(B_n) \subseteq W(X)`$ for $`m \le n`$
($`\mathrm{sirk\_numRange\_nested\_orders}`$, and
$`\mathrm{sirk\_numRange\_krylov}`$ for the Krylov flag the method actually
builds), with the matching norm chain $`\|B_m\| \le \|B_n\| \le \|X\|`$ and the
uniform envelope $`W(X) \subseteq \{|z| \le \|X\|\}`$. Every Ritz value of a
coarse order is therefore a Rayleigh quotient of every finer order, and of the
full generator ($`\mathrm{ritz\_mem\_numRange}`$,
$`\mathrm{ritz\_mem\_numRange\_compress}`$): refining the order can only *add*
frequencies, and never one the physics does not already have. Since a
finite-dimensional reduced generator has only eigenvalues in its spectrum, the
whole Ritz *spectrum* nests the same way
($`\mathrm{spectrum\_compress\_subset\_numRange\_orthonormal}`$). Positivity and any
real window $`[a,b]`$ of the quadratic form survive compression at every order
($`\mathrm{compress\_nonneg}`$, $`\mathrm{compress\_re\_inner\_mem\_Icc}`$). The
direction matters for honesty: since the numerical ranges *grow* with the order,
a Crouzeix-type bound $`C \sup_{W(B)}|f|`$ is non-decreasing in the order — the
band decay of $`\mathrm{sirkBound}`$ comes from the approximation quality, not
from shrinking numerical ranges. Convexity of the numerical range
(Toeplitz–Hausdorff) is neither used nor claimed. The approximation quality
itself does improve, unconditionally: the Krylov subspaces are
finite-dimensional, so the orthogonal projection onto them exists, and since they
nest, the best-approximation error is antitone in the order — for $`m \le n`$ the
order-$`n`$ subspace approximates any target at least as well as the order-$`m`$
one ($`\mathrm{krylov\_bestApprox\_antitone}`$), and when the Krylov flag is
dense — a cyclic seed — the error tends to $`0`$
($`\mathrm{krylov\_bestApprox\_tendsto\_zero}`$). Those statements need no
Crouzeix constant; what they do *not* give is a rate.
:::

```
#check @BookProof.ChapterH9.numRange_compress_subset
#check @BookProof.ChapterH9.numRange_compress_mono
#check @BookProof.ChapterH9.numRange_compress_chain
#check @BookProof.ChapterH9.numRange_subset_closedBall
#check @BookProof.ChapterH9.convexHull_numRange_compress_mono
#check @BookProof.ChapterH9.norm_compress_le
#check @BookProof.ChapterH9.norm_compress_mono
#check @BookProof.ChapterH9.ritz_mem_numRange
#check @BookProof.ChapterH9.ritz_mem_numRange_compress
#check @BookProof.ChapterH9.ritz_re_mem_Icc_of_fine
#check @BookProof.ChapterH9.compress_nonneg
#check @BookProof.ChapterH9.compress_re_inner_mem_Icc
#check @BookProof.ChapterH9.numRange_compress_orthonormal_mono
#check @BookProof.ChapterH9.spectrum_compress_subset_numRange
#check @BookProof.ChapterH9.spectrum_compress_subset_numRange_compress
#check @BookProof.ChapterH9.spectrum_compress_subset_numRange_orthonormal
#check @BookProof.ChapterH9.sirk_numRange_nested_orders
#check @BookProof.ChapterH9.sirk_numRange_krylov
#check @BookProof.ChapterH9.norm_sub_starProjection_antitone
#check @BookProof.ChapterH9.krylov_bestApprox_antitone
#check @BookProof.ChapterH9.krylov_bestApprox_tendsto_zero
```

:::paragraph
Finally, the offline stage: a two-level sketch hashes raw coordinates into $`k`
features and places the features on distinct modes of a $`K_2`-mode Fock space,
producing a genuine single-excitation state from which the features can be read
back; and all observables of the reduced space are pre-projected into a complete
basis of $`m^2` matrix units. The corpus size enters only there — the online
cost carries no such term.
:::

```
#check @BookProof.ChapterF8.singleExcitation
#check @BookProof.ChapterF8.twoLevelHash_total
#check @BookProof.ChapterF8.featureHash_decodes
#check @BookProof.ChapterF8.offline_operatorBasis
#check @BookProof.ChapterF8.online_cost_independent_of_M
#check @BookProof.ChapterF8.tsr_offline_compiles
```

:::paragraph
Two properties make the reduction safe to *run*. First, when the full generator
is self-adjoint the compression is self-adjoint too, so every eigenvalue of the
reduced generator is real and is pinned between any bounds satisfied by the
quadratic form of the full generator: the reduced dynamics can neither go
complex nor leave the frequency band of the physics it came from. Second, the
reduced propagator $`e^{-\mathrm{i}t\bar H}` of a Hermitian generator is
unitary, hence generation conserves the $`\ell^2` mass exactly — the generated
state is a state, at every step and for every horizon $`t`.
:::

```
#check @BookProof.ChapterH7.compress_isSelfAdjoint
#check @BookProof.ChapterH7.compression_rayleigh_real
#check @BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange
#check @BookProof.ChapterH7.reduceGenerator_isHermitian
#check @BookProof.ChapterH7.generationOperator_mem_unitaryGroup
#check @BookProof.ChapterH7.generation_preserves_l2
```

# The Navier–Stokes Hamiltonian: a Complete Flow on the Truncation

:::paragraph
The same free-field parametrization is what the manuscript applies to the
Navier–Stokes equations: the velocity field, *its derivatives* $`u_{k,j}`,
$`u_{k,jj}`, and the conjugate momenta $`\pi^i` are all treated as independent
canonical degrees of freedom, and the Hamiltonian is the Weyl-symmetrized
$`H = \sum_i (\pi_i A_i + A_i \pi_i)` with
$`A_i = \sum_j u_j u_{i,j} - \nu\, u_{i,jj}`. That the derivatives may be treated
as fields is an operator statement: an operator-valued field
$`\varphi(X) = \varphi + \varphi_i (X_i - x_i)` collapses to its point value on
the position eigenstates, so the first-order Taylor coefficients are free modes
with commutation relations of their own.
:::

```
#check @BookProof.NavierStokesFlow.fieldTaylor
#check @BookProof.NavierStokesFlow.field_evaluates_to_value
#check @BookProof.NavierStokesFlow.field_evaluates_to_value_diagonal
#check @BookProof.NavierStokesFlow.ccr_field
#check @BookProof.NavierStokesFlow.derivativeField_momentum
#check @BookProof.NavierStokesFlow.secondDerivativeField_momentum
#check @BookProof.NavierStokesFlow.momentumConstraint_preserved
```

:::paragraph
The Eulerian side of that construction carries its own constraints, and the
manuscript's own taxonomy splits them in two. The relations that *define* the
derivative modes — $`u_{i,j} = \partial_j u_i` and $`u_{i,jk} = \partial_k
u_{i,j}` — have no explicit solution, so they are the ones a gauge generator has
to impose; their consequence is Clairaut's condition $`u_{i,jk} = u_{i,kj}`,
which makes the second-derivative modes symmetric. The momenta conjugate to the
derivative modes pair with them by a Kronecker delta, which is what makes each
derivative an independent canonical variable. Incompressibility
$`\partial_j u_j = 0`, by contrast, *does* have an explicit solution — the
substitution $`u_{3,3} = -(u_{1,1}+u_{2,2})` — so it is imposed by initial data
rather than by a gauge symmetry, and it is satisfied by genuinely non-constant
fields such as the cyclic shear $`u_i(x) = x_{i+1}`.
:::

```
#check @BookProof.NavierStokesEulerian.u_evaluates_to_value
#check @BookProof.NavierStokesEulerian.eulerian_momentum_constraint
#check @BookProof.NavierStokesEulerian.eulerian_momentum_dual
#check @BookProof.NavierStokesEulerian.derivativeField_relates_to_field
#check @BookProof.NavierStokesEulerian.derivativeField_second
#check @BookProof.NavierStokesEulerian.derivativeField_consistency
#check @BookProof.NavierStokesEulerian.eulerian_divergence_constraint
#check @BookProof.NavierStokesEulerian.cyclicShear_divergence_free
```

:::paragraph
The constraint is stated properly only once a *second coordinate* $`y` is
adjoined to the space coordinate $`x`: the field that enters the Hamiltonian is
the expansion $`u_i(y) = u_i + u_{i,j} y_j` in that second coordinate. Each
coordinate then comes with a gauge generator. For $`x` it is the standard
momentum $`\pi^j = \partial/\partial x_j`; for $`y` it is the generator built
from the *derivatives of* $`u_i`,
$`G_j = \partial/\partial y_j - u_{i,j}\,\partial/\partial u_i`, which translates
the second coordinate while shifting each velocity mode by its own first
derivative. Both generators annihilate $`u_i(y)` and the Hamiltonian symbol
$`A_i = u_j(y) u_{i,j} - \nu u_{i,jj}`, and they commute among themselves, so the
constraints are first class; and the coefficient $`u_{i,j}` is the only one for
which the invariance holds, which is exactly the content of
$`u_{i,j} = \partial u_i/\partial y_j`. In the initial state the second
coordinate evaluates to $`y = 0`, so the field collapses to its point value
$`u_i` there and the Hamiltonian acts as the ordinary Navier–Stokes one: the
second coordinate carries the constraint without changing the dynamics of the
initial data.
:::

```
#check @BookProof.NavierStokesGaugeY.uField
#check @BookProof.NavierStokesGaugeY.genX
#check @BookProof.NavierStokesGaugeY.genY
#check @BookProof.NavierStokesGaugeY.uField_pderiv_y
#check @BookProof.NavierStokesGaugeY.genX_ccr_x
#check @BookProof.NavierStokesGaugeY.genY_ccr_y
#check @BookProof.NavierStokesGaugeY.genY_shifts_velocity
#check @BookProof.NavierStokesGaugeY.genY_uField
#check @BookProof.NavierStokesGaugeY.genX_uField
#check @BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero
#check @BookProof.NavierStokesGaugeY.genY_genY_commute
#check @BookProof.NavierStokesGaugeY.genX_genY_commute
#check @BookProof.NavierStokesGaugeY.genY_nsSymbol
#check @BookProof.NavierStokesGaugeY.setYZero_uField
#check @BookProof.NavierStokesGaugeY.setYZero_nsSymbol
#check @BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero
#check @BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero
```

:::paragraph
That generator compensates only the *first* derivatives, so the Laplacian modes
$`u_{i,jj}` — the ones the viscous term is built from — are still spectators of
the expansion. Carrying the Taylor expansion in the second coordinate one order
further repairs this. The field is
$`u_i(y) = u_i + u_{i,j} y_j + \tfrac12 u_{i,jj} y_j^2`, its $`y`-derivative is
the *derivative field* $`u_{i,j}(y) = u_{i,j} + u_{i,jj} y_j`, and the gauge
generator becomes
$`G^2_j = \partial/\partial y_j - u_{i,j}\,\partial/\partial u_i
- u_{i,jj}\,\partial/\partial u_{i,j}`: it shifts the velocity modes by their
first derivatives *and* the first-derivative modes by the Laplacian modes.
$`G^2_j` annihilates both fields, hence the symbol
$`A_i(y) = u_j(y)u_{i,j}(y) - \nu u_{i,jj}` built from them, and the
second-order generators still commute with each other and with the momenta, so
the constraints remain first class. The two orders are genuinely different: the
first-order generator leaves $`u_{i,jj}\,y_j` behind on the second-order field,
the second-order generator does not annihilate the first-order field, and the
Taylor coefficient $`\tfrac12` is the only one that works. On the initial state
$`y = 0` the second-order symbol collapses, once more, to the ordinary
Navier–Stokes symbol $`u_j u_{i,j} - \nu u_{i,jj}`.
:::

```
#check @BookProof.NavierStokesGaugeY2.uField2
#check @BookProof.NavierStokesGaugeY2.uDField
#check @BookProof.NavierStokesGaugeY2.genY2
#check @BookProof.NavierStokesGaugeY2.uField2_pderiv_y
#check @BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice
#check @BookProof.NavierStokesGaugeY2.genY2_leibniz
#check @BookProof.NavierStokesGaugeY2.genY2_uField2
#check @BookProof.NavierStokesGaugeY2.genY2_uDField
#check @BookProof.NavierStokesGaugeY2.genY_uField2_ne_zero
#check @BookProof.NavierStokesGaugeY2.genY2_uField_ne_zero
#check @BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero
#check @BookProof.NavierStokesGaugeY2.genY2_genY2_commute
#check @BookProof.NavierStokesGaugeY2.genX_genY2_commute
#check @BookProof.NavierStokesGaugeY2.genY_genY2_not_commute
#check @BookProof.NavierStokesGaugeY2.genY2_nsSymbol2
#check @BookProof.NavierStokesGaugeY2.genX_nsSymbol2
#check @BookProof.NavierStokesGaugeY2.setYZero_nsSymbol2
```

:::paragraph
On a *finite truncation* — finitely many modes, each a Hermitian matrix, the
field modes commuting as multiplication operators do — the whole claim is
provable. The Hamiltonian is Hermitian (the anticommutator of two Hermitian
factors is Hermitian), it is a polynomial of degree at most three in the
generators, and therefore $`U(t) = e^{\mathrm{i}tH_N}` is a one-parameter
unitary group defined for *every* real time: the flow is complete, it preserves
the $`\ell^2` mass, and every coefficient of the evolved state stays bounded by
the initial mass — no finite-time singularity on the truncation. The truncated
generator also has vanishing deficiency, which on a finite-dimensional space is
exactly essential self-adjointness.
:::

```
#check @BookProof.NavierStokesFlow.NSTruncation
#check @BookProof.NavierStokesFlow.nsHamiltonian
#check @BookProof.NavierStokesFlow.nsHamiltonian_hermitian
#check @BookProof.NavierStokesFlow.nsHamiltonian_isPolynomial
#check @BookProof.NavierStokesFlow.nsWord_length_le_three
#check @BookProof.NavierStokesFlow.nsHamiltonian_ne_zero_example
#check @BookProof.NavierStokesFlow.nsFlow_zero
#check @BookProof.NavierStokesFlow.nsFlow_group
#check @BookProof.NavierStokesFlow.nsFlow_unitary
#check @BookProof.NavierStokesFlow.nsFlow_norm_preserving
#check @BookProof.NavierStokesFlow.nsFlow_noBlowup
#check @BookProof.NavierStokesFlow.nsFlow_groupOnEvolved
#check @BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiency
```

:::paragraph
Completeness of the flow has a differential counterpart, which is the form in
which the manuscript states existence and uniqueness. On the truncation the
curve $`\psi(t) = U(t)\psi` is differentiable and solves
$`\dot\psi(t) = \mathrm{i}H_N\psi(t)`, and it is the *only* solution: any
differentiable curve satisfying the same equation with the same initial value
coincides with it at every time. So the Cauchy problem has exactly one global
solution, defined for all $`t\in\mathbb{R}` and confined to the sphere of the
initial mass. The proof of uniqueness is the classical one — the derivative of
$`t \mapsto U(-t)y(t)` vanishes, so that curve is constant. Along the way the
energy is conserved too: the expectation of $`H_N` in the evolved state does not
depend on time.
:::

```
#check @BookProof.NavierStokesFlow.nsFlow_hasDerivAt
#check @BookProof.NavierStokesFlow.nsFlow_solves_schrodinger
#check @BookProof.NavierStokesFlow.nsFlow_unique_solution
#check @BookProof.NavierStokesFlow.nsCauchy_existsUnique
#check @BookProof.NavierStokesFlow.nsFlow_energy_conserved
#check @BookProof.NavierStokesFlow.nsFlow_continuous
```

:::paragraph
The divergence constraint enters à la BRST. Its resolution is the book's own
substitution $`u_{3,3} = -(u_{1,1} + u_{2,2})`, and the truncated BRST charge
$`\Omega = u_{j,j}\otimes\psi^\dagger` is nilpotent because the ghost creation
operator is — the charge itself is not Hermitian, which is why the physical
space is a cohomology and not an eigenspace. In parcel (Lagrangian) variables
the constraint becomes volume preservation: a unit Jacobian determinant
preserves the volume of every set, and its infinitesimal form is exactly
$`\nabla\cdot u = 0`, since the derivative of $`t \mapsto \det(1 + tA)` at
$`t = 0` is $`\operatorname{tr} A`. In those variables the advection term is a
*positive* second-order operator (a sum of squares of the parcel momenta), the
viscosity likewise, the force a first-order drift and the pressure the 0-order
constraint.
:::

```
#check @BookProof.NavierStokesFlow.nsDivergenceConstraint_resolution
#check @BookProof.NavierStokesFlow.nsBrstCharge
#check @BookProof.NavierStokesFlow.nsBrst_nilpotent
#check @BookProof.NavierStokesFlow.nsBrst_adjoint
#check @BookProof.NavierStokesEulerian.nsBrst_not_hermitian
#check @BookProof.NavierStokesEulerian.nsBrst_symmetrization_hermitian
#check @BookProof.NavierStokesFlow.lagrangian_velocity
#check @BookProof.NavierStokesFlow.volume_preservation_constraint
#check @BookProof.NavierStokesFlow.det_one_add_smul_hasDerivAt
#check @BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_decomposition
#check @BookProof.NavierStokesFlow.LagrangianNS.kinetic_posSemidef
#check @BookProof.NavierStokesFlow.LagrangianNS.viscous_posSemidef
#check @BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_hermitian
#check @BookProof.NavierStokesFlow.LagrangianNS.flowUnitary_unitary
#check @BookProof.NavierStokesFlow.LagrangianNS.flowUnitary_group
#check @BookProof.NavierStokesFlow.LagrangianNS.cauchy_existsUnique
```

:::paragraph
The gauge-fixing machinery behind such charges has an abstract skeleton worth
isolating on its own. Grade the fields by (form degree, ghost number): the
physical scalar $`\varphi` in $`(0,0)`, the gauge field $`v` in $`(1,0)`, the
ghost $`c` in $`(1,1)`, the anti-ghost $`\bar c` in $`(1,-1)` and the
Nakanishi–Lautrup field $`B` in $`(1,0)`. The BRST operator $`s` raises the
ghost number and is nilpotent, and $`s v = c`, $`s\bar c = B`,
$`s\varphi = 0` make $`(v,c)` and $`(\bar c, B)` *contractible pairs*, which is
the formal content of "the gauge field and the ghosts decouple". Since a product
is now involved, $`s` acts as an odd derivation, picking up a sign across the
anti-ghost. The Gauge-Fixing Fermion $`\Psi = \bar c\,(v - d\varphi)`, of
bidegree $`(2,-1)`, then has BRST variation
$`s\Psi = B\,(v - d\varphi) - \bar c\,c`: BRST exactness *generates* the
Lagrange multiplier that enforces $`v = d\varphi` together with a ghost term
carrying no momentum. Nilpotency gives $`s(s\Psi) = 0`, so the gauge-fixing
Lagrangian is BRST-invariant, and under any evaluation that annihilates exact
terms it contributes nothing to observables. The axioms are not vacuous: an
explicit $`2\times 2` matrix model realizes them with non-zero ghost, auxiliary
field, Fermion and Lagrangian.
:::

```
#check @BookProof.GaugeFixing.GaugeFixingSystem
#check @BookProof.GaugeFixing.Psi
#check @BookProof.GaugeFixing.s_c_eq_zero
#check @BookProof.GaugeFixing.s_B_eq_zero
#check @BookProof.GaugeFixing.s_gaugeField
#check @BookProof.GaugeFixing.L_gf_evaluation
#check @BookProof.GaugeFixing.L_gf_invariant
#check @BookProof.GaugeFixing.int_L_gf_eq_zero
#check @BookProof.GaugeFixing.matrixModel
#check @BookProof.GaugeFixing.matrixModel_s_Psi_ne_zero
```

:::paragraph
Three ways to relate a field to its derivatives. The relation "$`v` is the
spatial derivative of $`\varphi`" can be imposed in (at least) three distinct
ways, and the difference between them is exactly the difference between a
*physical constraint* and a *gauge-fixing condition* — the choice the skeleton
above has to make. The three are:

* Method A — the topological (gauge-invariant) constraint. One introduces a
  symmetry that shifts both fields at once, $`\delta\varphi = \varepsilon`$ and
  $`\delta v = d\varepsilon`$, so that the combination $`v - d\varphi`$ is
  *gauge-invariant* ($`\delta(v-d\varphi) = 0`$) and hence a candidate physical
  observable.  Promoting the parameter to a ghost, $`s\varphi = c`$,
  $`s v = dc`$, $`s c = 0`$ is nilpotent, and the constraint is BRST-closed
  but not BRST-exact: it sits in the BRST cohomology.  That is the correct
  structure when $`v = d\varphi`$ is a genuinely topological relation — a
  Bogomol'nyi equation, a field-strength relation $`F = dA`$ — a piece of physics
  one wants to keep.  It is the wrong structure for the Navier–Stokes thread,
  where the derivative modes are redundant canonical coordinates one wants to
  eliminate, not promote to observables.

* Method B — the gauge-fixing condition (the one chosen here). Here $`v`$
  starts as an arbitrary unconstrained field with its own shift symmetry,
  $`\delta v = \varepsilon`$, $`\delta\varphi = 0`$, and the relation
  $`v = d\varphi`$ is a condition one imposes by gauge fixing.  The Gauge-Fixing
  Fermion $`\Psi = \bar c\,(v - d\varphi)`$ is chosen so that its BRST variation
  $`s\Psi = B(v-d\varphi) - \bar c\,c`$ is a BRST-exact term: the Lagrange
  multiplier $`B`$ enforces $`v = d\varphi`$ as a delta function in the path
  integral, and the ghost term carries no derivatives, so the ghosts decouple.
  Being BRST-exact, the whole term integrates to zero against any evaluation
  functional that annihilates exact terms (`int_L_gf_eq_zero`) — it contributes
  nothing to physical observables, which is precisely what makes it a pure gauge
  fixing rather than new physics.  This is the method formalized in
  `BookProof/ChapterGaugeFixing.lean`.

* A complex gauge field (a flat-connection reading of the same content). One
  might instead replace the derivative $`\partial_\mu u`$ in the Hamiltonian by
  $`A_\mu u`$ for a complex gauge field $`A_\mu`$ (a complexified vector
  potential), fix the magnetic field to zero as an initial condition, and impose
  covariant constancy $`D_\mu u = \partial_\mu u + A_\mu u = 0`$ to fix the field
  derivatives.  This is geometrically elegant — the derivative field becomes the
  connection coefficient of a flat line bundle — but it carries no new content:
  wherever $`u \neq 0`$ the constraint forces $`A_\mu = -\partial_\mu\log u`$, a
  pure gauge with curvature automatically zero, so $`A`$ is the derivative field
  in disguise and the "magnetic field is zero" is the flatness consistency, not a
  dynamical condition.  It also costs the structure the proofs here depend on: a
  gauge field is not a constant of the motion (it is coupled to $`u`$ through the
  covariant constraint), so the block decomposition over the derivative spectrum
  that drives the ESA chain collapses; and a complex coefficient breaks the real
  Hermitian form of the Navier–Stokes Hamiltonian, re-opening the symmetrization
  question.  It is kept here only as a geometric interpretation of what the
  formalized gauge fixing does, not as an alternative implementation.
:::

:::paragraph
Why Method B is chosen.  The task in the Navier–Stokes thread is to *remove*
the derivative coordinates, not to make them physical: the Eulerian
derivatives-as-fields construction promotes $`u_{i,j}`$ and $`u_{i,jj}`$ to
independent canonical coordinates purely so the Hamiltonian carries momenta only
for the velocity modes — which is what makes the derivative field a constant of
the motion and the block decomposition possible.  Method B is the instrument that
completes that construction: it eliminates the redundant coordinates by a
BRST-exact gauge fixing whose ghosts decouple and whose Lagrange multiplier
enforces the constraint as a strict delta function, leaving the physical
cohomology untouched.  Method A would invert the logic (it would make
$`v - d\varphi`$ a physical observable), and the flat-connection reading, while
insightful, is the same logic repackaged at the cost of a new gauge redundancy and
a complexified Hermitian structure.  Method B is also the formalization-friendly
choice: one graded Leibniz rule, no analysis, a purely algebraic skeleton
(plan item E.6, `BookProof/ChapterGaugeFixing.lean`), and it is the gauge fixing
the A.6/A.7 `genY`/`genY2` generators perform when they tie the derivative fields
to the velocity field — the step on which the Hashimoto shift-invert selection for
the Navier–Stokes Hamiltonian (§9 item 8 of `CONSOLIDATED_PLAN.md`) is to be built.
:::

:::paragraph
Because that transformed operator is Hermitian on the truncation, everything
said about the flow of $`H_N` holds for it verbatim: $`e^{\mathrm{i}t\hat h}`$ is
a one-parameter unitary group and the corresponding Cauchy problem has exactly
one global solution. That is the truncated form of the Lagrangian route — the
continuum statement remains unclaimed.
:::

:::paragraph
The honest boundary. Nothing above claims essential self-adjointness of the
*untruncated continuum* operator — and with it, nothing claims global
existence/uniqueness for the *classical* Navier–Stokes equations (the Clay
regularity problem, deliberately out of scope). The distinction matters: once
ESA *is* proved, global existence of the operator flow follows automatically —
Stone's theorem (a self-adjoint operator generates a complete unitary group for
every real time) is itself proved in this project (2026-08-20e,
`ChapterStoneResolvent`–`ChapterStoneSeparable`) — and that is exactly what
`book.tex` §4210-4216 means by "the solution ... exists and it is unique", and
the truncation already proves it as `nsCauchy_existsUnique`. The open step is
ESA itself for the continuum operator, not a separate global-existence claim. The ODE chapter is the standing warning:
for $`\dot x = x^2` the Hamiltonian $`x^2\hat p - \mathrm{i}\hat x` is a
polynomial of degree three whose classical flow is incomplete, so "low degree in
the fields" cannot by itself give self-adjointness — it gives symmetry. The
continuum route that remains is the Faris–Lavine commutator criterion applied to
the Lagrangian-transformed operator, whose second-quantized form on the
Fock-of-a-Fock space is at most *quadratic* in the outer ladder operators, and
whose comparison operator is the (positive) outer number operator. That
criterion is recorded as a named hypothesis, never an axiom, exactly as
Crouzeix's inequality is in `ChapterH4`; its two analytic inequalities for the
continuum operator are a research target, not a result.
:::

```
#check @BookProof.NavierStokesFlow.nsFockOfFock
#check @BookProof.NavierStokesFlow.nsSecondQuant
#check @BookProof.NavierStokesFlow.ns_outer_degree_le_two
#check @BookProof.NavierStokesFlow.nsNumberOp
#check @BookProof.NavierStokesFlow.nsNumberOp_eq_secondQuant
#check @BookProof.NavierStokesFlow.nsNumberOp_posSemidef
#check @BookProof.NavierStokesFlow.HasZeroDeficiency
#check @BookProof.NavierStokesFlow.symmetric_hasZeroDeficiency
#check @BookProof.NavierStokesFlow.ns_esa_of_farisLavine
```

:::paragraph
The named hypothesis has to be the *honest* criterion. Stated without the
symmetry of the operator it is contradictory — $`H = \mathrm{i}\cdot 1` with
comparison operator the identity satisfies both inequalities while having a full
deficiency space — so a conditional theorem resting on it would be vacuous. With
symmetry the criterion is satisfiable, and for operators defined on the whole
space it is automatic: symmetry alone already forces the deficiency to vanish.
The analytic content of Faris–Lavine therefore lives entirely in the densely
defined case, where the deficiency spaces are those of the *adjoint*; that is
the predicate under which the conditional theorem is restated, and where the
truncation — whose domain is the whole space — is the only case proved here.
:::

```
#check @BookProof.NavierStokesFlow.farisLavine_without_symmetry_forces_trivial
#check @BookProof.NavierStokesFlow.farisLavine_holds_of_everywhereDefined
#check @BookProof.NavierStokesFlow.HasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.hasZeroDeficiencyOn_top_of_symmetric
#check @BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.ns_esa_of_farisLavine_dense
```

:::paragraph
There is one criterion under which the passage from the truncation to an
infinite-dimensional operator is not a change of kind: *a complete flow*. If a
symmetric operator on a dense domain generates a norm-preserving flow that is
defined for *every* real time and leaves the domain invariant, then the
deficiency spaces of its adjoint vanish — the operator is essentially
self-adjoint. The proof is the classical orbit argument: a deficiency vector
$`w` with $`H^{*}w = \pm\mathrm{i}w` makes the orbit function
$`g(t) = \langle w, U(t)v\rangle` satisfy $`g' = \pm g`, so $`g(t) = g(0)e^{\pm t}`,
while unitarity of the flow keeps $`|g|` bounded on the whole line; hence
$`g(0) = \langle w, v\rangle = 0` for every $`v` in the dense domain, and
$`w = 0`. Completeness is exactly the hypothesis that a finite-time blow-up
would destroy, which is why the ODE chapter's $`\dot x = x^{2}` example is the
standing warning for the continuum case.
:::

```
#check @BookProof.NavierStokesFlow.eq_zero_of_hasDerivAt_smul_of_bounded
#check @BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_completeUnitaryFlow
#check @BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn_of_flow
```

:::paragraph
The criterion is applied where its hypotheses are actually available: to the
truncation, whose flow is complete by construction. Nothing is claimed for the
untruncated generator, whose flow completeness is the open problem.

A second, genuinely infinite-dimensional case is available on the bounded
$`\ell^{2}(\mathbb{Z})` layer: a bounded symmetric operator is essentially
self-adjoint on *every* dense invariant domain, and the Weyl-symmetrized
continuity generator $`H = \tfrac12(pv + vp)` leaves the domain of finitely
supported modes invariant. That domain is dense but is *not* the whole space, so
this is the first instance in the development of vanishing adjoint deficiency on
a proper dense domain — the setting in which the notion has analytic content.
:::

```
#check @BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_bounded_symmetric
#check @BookProof.NavierStokesFlow.finiteModes
#check @BookProof.NavierStokesFlow.finiteModes_dense
#check @BookProof.NavierStokesFlow.finiteModes_ne_top
#check @BookProof.NavierStokesFlow.continuityHamiltonian_hasZeroDeficiencyOn_finiteModes
```

:::paragraph
Both criteria are needed, because symmetry on a dense domain is by itself never
enough. On $`\ell^{2}(\mathbb{N})`, with the finitely supported states as domain,
the tridiagonal operator
$`(Hf)(0) = a_{0}f(1)`, $`(Hf)(n+1) = a_{n}f(n) + a_{n+1}f(n+2)` with real
weights $`a_{0} = 2`, $`a_{n+1} = 4a_{n}+2` is symmetric on that dense domain,
yet the square-summable geometric sequence $`w(n) = (\mathrm{i}/2)^{n}` satisfies
$`Hw = \mathrm{i}w` coefficientwise and is therefore a deficiency vector of the
adjoint: essential self-adjointness *fails*. The one computation behind both
statements is the discrete Green identity — the truncated sum of Wronskian
increments telescopes to a boundary term, which vanishes for finitely supported
states.

So the "polynomial of low degree in the fields" hypothesis, which gives symmetry
on the finite-particle domain, cannot by itself yield essential self-adjointness;
an analytic input — a complete flow, boundedness, or the Faris–Lavine
inequalities — is required.
:::

```
#check @BookProof.NavierStokesFlow.JacobiDeficiency.jacobi_wronskian
#check @BookProof.NavierStokesFlow.JacobiDeficiency.jacobiOp_symmetric
#check @BookProof.NavierStokesFlow.JacobiDeficiency.defState_deficiency
#check @BookProof.NavierStokesFlow.JacobiDeficiency.jacobiOp_not_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.JacobiDeficiency.jacobi_symmetric_dense_not_esa
```

:::paragraph
Unboundedness by itself is not the obstruction either. A symmetric operator that
carries a *total* family of eigenvectors inside its domain — only the zero
vector is orthogonal to all of them — is essentially self-adjoint, because
testing the deficiency identity against an eigenvector `e` with real eigenvalue
$`\lambda` gives $`(\lambda \mp \mathrm{i})\langle e, w\rangle = 0`. A diagonal
operator on $`\ell^{2}(\mathbb{N})` with an arbitrary, possibly unbounded, real
sequence of entries satisfies this on the same finitely supported domain on
which the tridiagonal example fails. What separates the two is whether the
domain carries enough eigenvectors. That diagonal operator is genuinely
unbounded whenever its sequence of entries is: no constant dominates it on the
finite-mode domain, so essential self-adjointness there is not a boundedness
phenomenon in disguise.
:::

```
#check @BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
#check @BookProof.NavierStokesFlow.DiagonalEsa.diagOp
#check @BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis
#check @BookProof.NavierStokesFlow.DiagonalEsa.diagOp_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded
```

:::paragraph
The Lagrangian change of variables is what turns these criteria into a statement
about the Navier–Stokes generator itself. Writing the flow in parcel
coordinates — the trajectory operators $`X(\xi)` with conjugate momenta
$`P(\xi) = \dot X(\xi) = u(X(\xi))` in place of the Eulerian velocity — the
operator becomes
$`\hat h_{\mathrm{full}} = \tfrac12\sum_i P_i^{2} + \nu\sum_i Q_i^{2}
+ \sum_i f_i D_i + C`: two second-order terms, a first-order force drift and the
zeroth-order volume-preservation constraint. Untruncated — all of these are
(possibly unbounded) operators on a dense domain of an arbitrary complex
inner-product space — the transformed operator is symmetric, and the quadratic
forms of its two second-order terms are $`\tfrac12\sum_i\|P_i v\|^{2}` and
$`\nu\sum_i\|Q_i v\|^{2}`: the advection term, which in Eulerian variables is
the troublesome $`-u_j\partial_j u_i`, has become *positive*.
:::

```
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_isSymmetricDom
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_inner
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg
```

:::paragraph
Essential self-adjointness then follows in the transformed variables. A total
family of common eigenvectors of the constituents — the Lagrangian momentum
representation — makes the full transformed Hamiltonian essentially
self-adjoint, with eigenvalue
$`\tfrac12\sum_i p_i^{2} + \nu\sum_i q_i^{2} + \sum_i f_i d_i + c`; and because
vanishing adjoint deficiency is invariant under a unitary change of variables,
what is proved after the change of variables holds for the operator it came
from. Two untruncated realizations make this unconditional: on
$`\ell^{2}(\mathbb{Z})`, with the parcel momenta the symmetric-difference
lattice momentum — so $`\tfrac12\sum_i P_i^{2}` is a discrete Laplacian — the
transformed Hamiltonian is essentially self-adjoint on the *proper* dense domain
of finitely supported modes and is not the zero operator; on
$`\ell^{2}(\mathbb{N})`, with diagonal constituents of arbitrary real symbols,
it is essentially self-adjoint while being genuinely unbounded. The limits are
equally explicit: an unbounded first-order drift term alone already destroys the
property, so no criterion-free statement about the transformed data is
available, and essential self-adjointness of the *continuum* transformed
generator — the operator-flow global existence would follow from ESA by the
Stone theorem of 2026-08-20e, but the classical global existence for
Navier–Stokes would not — is not claimed here.
:::

```
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors
#check @BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_iff_of_linearIsometryEquiv
#check @BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian
#check @BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero
#check @BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.LagrangianEsa.diagLag_not_bounded
#check @BookProof.NavierStokesFlow.LagrangianEsa.exists_lagrangianFullData_not_hasZeroDeficiencyOn
```

:::paragraph
The last step of the chain is the passage from one particle to the Fock space,
and it is where the comparison operator of the Faris–Lavine criterion has to be
rebuilt. Fock space here is the $`\ell^{2}` direct sum of the particle sectors,
and the finite-particle domain is the span of states supported in finitely many
sectors with each component in that sector's core. That domain is dense as soon
as every sector core is, and it is a *proper* subspace of the Fock space, so
nothing below is a statement about a boundedly extended operator. The second
quantization $`d\Gamma(A)` acts sector by sector, and vanishing adjoint
deficiency lifts: if every sector operator has it on its own core, so does
$`d\Gamma(A)` on the finite-particle domain. Applied to a one-particle
comparison operator this is the "cage" the criterion needs.
:::

```
#check @BookProof.NavierStokesFlow.SecondQuant.fockCore
#check @BookProof.NavierStokesFlow.SecondQuant.fockCore_dense
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.SecondQuant.fockCore_ne_top
```

:::paragraph
The one-particle comparison operator is $`n = \sum_i \pi_i^{2} + \sum_i V_i^{2}
+ I`, with the $`\pi_i` the fiber momenta and the $`V_i` the fiber realization
of the advection field, all symmetric on a common dense domain. Because both
families enter squared, the quadratic form of $`n` is
$`\sum_i\|\pi_i v\|^{2} + \sum_i\|V_i v\|^{2} + \|v\|^{2}`, so $`n \ge I` — the
strict positivity that a comparison operator must have. In the momentum
representation, where the constituents are diagonal with arbitrary real symbols,
$`n` is essentially self-adjoint on the finite-mode domain and is genuinely
unbounded whenever its symbols are; second-quantizing that realization gives a
Fock-space comparison operator that is essentially self-adjoint on the
finite-particle domain, and it inherits `N̂ ≥ I` from the sectors.
:::

```
#check @BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
#check @BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison
#check @BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_ge_norm_sq
#check @BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_not_bounded
#check @BookProof.NavierStokesFlow.SecondQuant.fockComparison_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_ge_norm_sq
#check @BookProof.NavierStokesFlow.SecondQuant.fockComparison_ge_norm_sq
#check @BookProof.NavierStokesFlow.SecondQuant.fockComparison_domain_ne_top
```

:::paragraph
The two Faris–Lavine bounds then have to survive the lift, and here the two
halves behave differently. The form-commutator bound does lift as expected: the
commutator of the sums is the sum of the commutators once distinct particles
commute, and summing $`|\langle v, [h_k, n_k] v\rangle| \le c_2 \langle v, n_k
v\rangle` over the particles gives the same bound for the totals — stated with a
modulus on the left, since for symmetric constituents the commutator expectation
is purely imaginary and its real part carries no information. The operator bound
does *not* lift by the triangle inequality alone: the informal chain
$`\|\sum_k h_k v\| \le \sum_k\|h_k v\| \le c_1\sum_k\|n_k v\| \le c_1\|\sum_k n_k
v\|` uses a last step that is false, and two two-by-two operator pairs with
$`\|h_k x\| \le \|n_k x\|` for every $`x` but $`\|(n_0+n_1)v\| <
\|(h_0+h_1)v\|` witness the failure. What does lift is the pairwise-dominated
form of the hypothesis, and with the two bounds in that shape the Faris–Lavine
criterion — taken as a named hypothesis, not an axiom — yields vanishing adjoint
deficiency for the second-quantized Hamiltonian on the finite-particle domain.
Essential self-adjointness of the *continuum* Navier–Stokes Hamiltonian is not
claimed; the operator-flow global existence would follow from it by the Stone
theorem of 2026-08-20e, while classical global existence is a separate,
deliberately out-of-scope statement.
:::

```
#check @BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_le_of_pairwise
#check @BookProof.NavierStokesFlow.FarisLavineLift.not_forall_norm_sum_le_of_pointwise
#check @BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_le_of_sectors
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_inner_le_of_sectors
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn_of_farisLavine
```

:::paragraph
That last statement still carries the criterion as a hypothesis, and in the shape
it is stated there — a relative bound plus a commutator bound, with no positivity
of $`N` and no surjectivity of $`N+1` — the criterion is in fact refutable, by the
limit-circle Jacobi operator. The remedy is to supply exactly the input the
Faris–Lavine proof uses, and this the momentum representation does provide. Take
the comparison operator on its *maximal* domain in $`\ell^{2}`: multiplication by
the symbol $`\sigma`, defined on every state whose product with $`\sigma` is
again square summable. For a non-negative symbol that operator is symmetric,
positive, $`N+1` maps the maximal domain onto the whole space because
$`(\sigma+1)^{-1}` is a contraction, and the finite-mode states — the
momentum-space stand-in for $`C_c^\infty` — are an operator core, since the
truncations of a state converge to it in the graph norm. That package is the
Ikebe–Kato-type input, and it is proved, not assumed: for a non-negative symbol,
multiplication by $`\sigma` is essentially self-adjoint already on the finite-mode
core, and self-adjoint on its maximal domain.
:::

```
#check @BookProof.NavierStokesFlow.IkebeKato.maxDom
#check @BookProof.NavierStokesFlow.IkebeKato.diagMax
#check @BookProof.NavierStokesFlow.IkebeKato.diagMax_quadForm_ge_norm_sq
#check @BookProof.NavierStokesFlow.IkebeKato.diagMax_add_one_surjective
#check @BookProof.NavierStokesFlow.IkebeKato.exists_finiteModes_graph_approx
#check @BookProof.NavierStokesFlow.IkebeKato.diagMax_essentiallySelfAdjointOn
#check @BookProof.NavierStokesFlow.IkebeKato.ikebeKato_momentum
```

:::paragraph
With that input the Faris–Lavine theorem of the criterion chapter applies with no
hypothesis left over: any symmetric Hamiltonian on the maximal domain which is
relatively bounded by $`N` and whose form commutator with $`N` is dominated by
$`N` is essentially self-adjoint on the finite-mode core. Specialised to the
Navier–Stokes symbol $`\sigma(k)=\sum_i p_i(k)^2+\sum_i q_i(k)^2+1` this is the
one-particle statement, and the restriction of the maximal-domain operator to the
core is literally the comparison operator $`n=\sum_i\pi_i^2+\sum_i V_i^2+I` of the
fiber. In the occupation-number representation the bosonic Fock space over the
fiber is $`\ell^{2}` over the configurations $`\alpha:\mathbb{N}\to_{f}\mathbb{N}`
and $`\hat N = d\Gamma(n)+I` is again a multiplication operator, by the total
energy $`\Sigma(\alpha)=\sum_k \alpha(k)\,n(k)+1`; so the same theorem gives
essential self-adjointness of the second-quantized Navier–Stokes Hamiltonian on
the finite-particle, finite-mode core. What remains hypothetical are exactly the
two Faris–Lavine inequalities for the Hamiltonian itself; they are not vacuous —
an unbounded Hamiltonian $`N+B` with a rank-two perturbation satisfies both while
its commutator with $`N` is non-zero. Essential self-adjointness of the
*continuum* generator, and global existence, are still not claimed.
:::

```
#check @BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
#check @BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq
#check @BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato
#check @BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.MomentumEsa.fockSymbol
#check @BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_add
#check @BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato
#check @BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded
#check @BookProof.NavierStokesFlow.MomentumPerturbation.exists_commForm_ne_zero
```

:::paragraph
The quadratic Navier–Stokes symbol is a *direct sum* of linear ones. The
Hamiltonian carries momenta only for the velocity modes, so the derivative modes
$`u_{i,j}` commute with it: they are constants of the motion. Diagonalising the
derivative field splits the Hilbert space as
$`\ell^{2}(\mathbb{N}\times J)` — the Hermite levels of the velocity fiber times
the spectrum $`J` of the derivative field — and in the block $`j` the bilinear
symbol $`A = u_{,1}\,u` becomes the *linear* advection field
$`V(u)=\kappa_j u`, whose fiber Hamiltonian is exactly the one for which the two
Faris–Lavine inequalities are proved. The strain rates $`\kappa_j` range over
that spectrum and are in general unbounded, so no single pair of Faris–Lavine
constants can serve the whole operator; the deficiency problem, however,
decomposes over the blocks, because a deficiency vector restricts to one in each
block. Hence the bilinear (quadratic-symbol) Navier–Stokes Hamiltonian is
symmetric and essentially self-adjoint on the finite-mode core for an arbitrary
family of strain rates, and it is genuinely unbounded whenever they are. The
viscous term and the cross terms add a constant to the fiber field — an affine
$`V(u)=\kappa_j u + c_j`, a $`\pm 1` shift on top of the $`\pm 2` shift.
:::

```
#check @BookProof.NavierStokesFlow.BilinearEsa.bilH
#check @BookProof.NavierStokesFlow.BilinearEsa.bilFun_embFun
#check @BookProof.NavierStokesFlow.BilinearEsa.hasSum_inner_blocks
#check @BookProof.NavierStokesFlow.BilinearEsa.blockVec_bilH
#check @BookProof.NavierStokesFlow.BilinearEsa.bilH_symmetricOn
#check @BookProof.NavierStokesFlow.BilinearEsa.deficiencyTrivialAt_bilH
#check @BookProof.NavierStokesFlow.BilinearEsa.bilH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.BilinearEsa.bilH_ne_zero
#check @BookProof.NavierStokesFlow.BilinearEsa.bilH_domain_dense
#check @BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded
```

:::paragraph
That last shift is supplied by summing two hopping operators against one
comparison operator. The Faris–Lavine hypotheses used here — symmetry, a
relative bound $`\|Hx\|^{2}\le a\|Nx\|^{2}+b\|x\|^{2}` with no smallness
required of $`a`, and a commutator bound
$`|\langle x, i[H,N]x\rangle|\le c\,\langle x, Nx\rangle` — are all stable under
sums, because $`\|(H_1+H_2)x\|^{2}\le 2\|H_1x\|^{2}+2\|H_2x\|^{2}` and the
commutator form is additive in $`H`. Taking the number operator
$`N=\mu(2n+1)+1` with $`\mu=\kappa+c+1` as the common comparison operator, the
$`\pm 2` hopping $`(\kappa/2)\sqrt{(n+1)(n+2)}` of $`\kappa\,\tfrac12(\pi u+u\pi)`
and the $`\pm 1` hopping $`(c/\sqrt 2)\sqrt{n+1}` of $`c\,\pi` are both dominated
by it, so the affine fiber Hamiltonian is symmetric and essentially self-adjoint
on the finite-mode core, and both hoppings are genuinely present. Running the
block decomposition again with the affine fiber Hamiltonian in place of the
linear one covers the viscous term and the cross terms. Assumed throughout:
$`\kappa_j\ge 0` and $`c_j\ge 0`, the latter only because a hopping amplitude is
required to be non-negative. Only one velocity component is carried, and nothing
here claims global regularity for the classical Navier–Stokes equation.
:::

```
#check @BookProof.NavierStokesFlow.AffineFiber.PairShift
#check @BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH
#check @BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_relative_bound
#check @BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_commForm_bound
#check @BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.AffineFiber.affH
#check @BookProof.NavierStokesFlow.AffineFiber.affH_symmetricOn
#check @BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ
#check @BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ
#check @BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded
#check @BookProof.NavierStokesFlow.AffineBlock.affBlockH
#check @BookProof.NavierStokesFlow.AffineBlock.blockVec_affBlockH
#check @BookProof.NavierStokesFlow.AffineBlock.affBlockH_symmetricOn
#check @BookProof.NavierStokesFlow.AffineBlock.affBlockH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded
```

:::paragraph
Both restrictions just recorded are artefacts of the bookkeeping, and both are
now removed. The sign condition goes first: essential self-adjointness is a
*unitary invariant*, so if a unitary $`U` of the ambient space preserves the core
and intertwines $`H` with $`H'`, one is essentially self-adjoint exactly when the
other is. The sign-flip $`(Ux)_n=(-1)^n x_n` is such a unitary; it reverses the
sign of a $`\pm 1` hopping and preserves a $`\pm 2` hopping, so it conjugates the
affine fiber Hamiltonian with constant $`c` into the one with constant $`|c|`.
Hence the fiber and the block Hamiltonians are essentially self-adjoint for a
fiber constant of *arbitrary sign*.
:::

```
#check @BookProof.NavierStokesFlow.SignFlip.flipU
#check @BookProof.NavierStokesFlow.SignFlip.essentiallySelfAdjointOn_of_intertwine
#check @BookProof.NavierStokesFlow.SignFlip.shiftH_flip
#check @BookProof.NavierStokesFlow.SignFlip.saffH
#check @BookProof.NavierStokesFlow.SignFlip.saffH_symmetricOn
#check @BookProof.NavierStokesFlow.SignFlip.saffH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.SignFlip.sblockH_essentiallySelfAdjointOn_core
```

:::paragraph
The one-component restriction goes next. At one fiber the velocity is the vector
$`u=(u_1,u_2,u_3)`, the Hermite basis is indexed by $`\beta\in\mathbb{N}^3`, and
the fiber fields are the affine $`V_i(u)=\sum_k A_{ik}u_k+c_i` for an *arbitrary*
real $`3\times 3` matrix $`A` — the velocity gradient at the fiber, with no
symmetry, positivity or sign assumption — and an arbitrary real vector $`c`. The
Weyl ordering $`H=\sum_i\tfrac12(\pi_iV_i+V_i\pi_i)` becomes twenty-four hopping
terms: a $`\pm 2` hopping per component, a $`\pm 1` hopping per fiber constant,
and, for each pair of distinct components, a double-raising *strain* hopping of
amplitude $`\tfrac12(A_{ik}+A_{ki})\sqrt{(\beta_i+1)(\beta_k+1)}` and a
number-conserving *vorticity* hopping of amplitude
$`\tfrac12(A_{ik}-A_{ki})\sqrt{(\beta_i+1)\beta_k}`. The vorticity amplitude
increases in one coordinate and decreases in the other, so it is not monotone
along its shift, and the strain rates and the constants have arbitrary signs.
The instrument that copes with all of this is a hopping term whose amplitude is
an arbitrary real function dominated by $`\tfrac14\sigma+K`: the estimates never
need the amplitude itself, only a majorant that is non-negative, monotone along
the shift and dominated by the comparison symbol. A finite family of such terms
sharing one comparison symbol again sums to an operator that is symmetric and
essentially self-adjoint on the finite-mode core. Applied to the twenty-four
terms above with $`N=\mu(2|\beta|+3)+1`, this gives the coupled three-component
fiber Hamiltonian, essentially self-adjoint on the finite-mode core of
$`\ell^2(\mathbb{N}^3)` for every real $`A` and every real $`c`; the strain and
vorticity matrix entries are computed, so the coupling is genuinely there, and
the operator is unbounded. The statement is proved in the Hermite
(sequence-space) realization of the fiber; the next paragraph reads the same
operator back in canonical form. Nothing here claims global regularity for the
classical Navier–Stokes equation.
:::

```
#check @BookProof.NavierStokesFlow.SignedShift.SignedHop
#check @BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_relative_bound
#check @BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_commForm_bound
#check @BookProof.NavierStokesFlow.SignedShift.listH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.SignedShift.gaffH
#check @BookProof.NavierStokesFlow.SignedShift.gaffH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.ThreeComponent.velH
#check @BookProof.NavierStokesFlow.ThreeComponent.velH_symmetricOn
#check @BookProof.NavierStokesFlow.ThreeComponent.velH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.ThreeComponent.velH_coord_pair
#check @BookProof.NavierStokesFlow.ThreeComponent.velH_coord_rot
#check @BookProof.NavierStokesFlow.ThreeComponent.velH_not_bounded
```

:::paragraph
The hopping description is a matrix, and a matrix is not obviously a
Hamiltonian. What closes the gap is to build the canonical pairs *inside* the
sequence space and check that the matrix is the Weyl-ordered expression one
started from. On the finite-mode core of $`\ell^2(\mathbb{N}^3)` the three
ladder pairs are the coordinate shifts
$`(a_iX)(\beta)=\sqrt{\beta_i+1}\,X(\beta+e_i)` and
$`(a_i^\dagger X)(\beta)=\sqrt{\beta_i}\,X(\beta-e_i)`; they satisfy the full
canonical commutation relations, $`[a_i,a_k]=[a_i^\dagger,a_k^\dagger]=0` and
$`[a_i,a_k^\dagger]=\delta_{ik}`, and the resulting
$`u_i=(a_i+a_i^\dagger)/\sqrt2`, $`\pi_i=i(a_i^\dagger-a_i)/\sqrt2` are three
commuting canonical pairs with $`[\pi_i,u_k]=-i\delta_{ik}`. Writing
$`H_{\mathrm{can}}=\sum_i\tfrac12(\pi_iV_i+V_i\pi_i)` with
$`V_i(u)=\sum_kA_{ik}u_k+c_i` literally in those operators and expanding by the
commutation relations produces, term by term, exactly the twenty-four hopping
amplitudes of the previous paragraph: the two $`\sqrt2`'s of a Weyl-ordered
product combine into the $`\tfrac14` of the Hermite amplitudes, the double
raisings give the strain, the number-conserving terms the vorticity. So
$`H_{\mathrm{can}}=H` as operators on the core, and the essential
self-adjointness proved for the matrix is essential self-adjointness of the
canonically written quadratic symbol. Spelling the coefficients out the way the
Navier–Stokes symbol supplies them — linear part the velocity gradient,
constant part $`-\nu` times the velocity Laplacian at the fiber — gives the
statement in its intended form: for every viscosity, every velocity gradient and
every velocity Laplacian, the quantized full quadratic Navier–Stokes symbol
$`\sum_i\tfrac12(\pi_iA_i+A_i\pi_i)`,
$`A_i(u)=\sum_ju_{i,j}u_j-\nu u_{i,jj}`, is essentially self-adjoint on the
Hermite core of the three velocity components. The canonical pairs used here are
abstract, characterized by their commutation relations; the next paragraph
transports them to the concrete realization on $`L^2(du_1du_2du_3)`.
:::

```
#check @BookProof.NavierStokesFlow.CanonicalVector.comm_ann_cre
#check @BookProof.NavierStokesFlow.CanonicalVector.comm_mom_pos
#check @BookProof.NavierStokesFlow.CanonicalVector.comm_mom_pos_of_ne
#check @BookProof.NavierStokesFlow.CanonicalVector.canH
#check @BookProof.NavierStokesFlow.CanonicalVector.canH_eq_velH
#check @BookProof.NavierStokesFlow.CanonicalVector.canH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.CanonicalVector.canH_not_bounded
#check @BookProof.NavierStokesFlow.CanonicalVector.nsQuadraticH
#check @BookProof.NavierStokesFlow.CanonicalVector.nsQuadraticH_essentiallySelfAdjointOn_core
```

:::paragraph
The abstract picture is now carried to the concrete one. The product Hermite
functions $`\psi_\alpha(u)=\prod_iHe_{\alpha_i}(u_i)e^{-\|u\|^2/4}/\|\cdot\|`,
indexed by the three-mode multi-indices, are an orthonormal basis of
$`L^2(du_1du_2du_3)` (`hermiteMvBasis`, `velBasis`), so the sequence space of the
previous paragraph *is* $`L^2(\mathbb R^3)` under the unitary `velUnitary`. On the
Gauss–polynomial core of that space the two physical operators are honest: `posOp`
is multiplication by the coordinate $`u_i` and `momOp` is $`-i\partial/\partial u_i`
— `momOp_apply_eq_differential` states that its value at $`p(u)e^{-\|u\|^2/4}` is,
pointwise, $`-i` times Mathlib's `deriv` of that function along the $`i`-th
coordinate — and they satisfy the canonical commutation relation
$`[\pi_i,u_k]=-i\delta_{ik}` (`comm_momOp_posOp`). The unitary carries the
finite-mode core onto the Gauss–polynomial core and the ladder operators onto the
differential ones (`intertwine_ann`, `intertwine_cre`), hence the canonical
Hamiltonian onto the differentially written one (`intertwined_canH`). The
conclusion is the statement in its intended realization: for every real velocity
gradient and every constant part, the Weyl-ordered
$`\sum_i\tfrac12(\pi_iV_i+V_i\pi_i)` with $`\pi_i=-i\partial/\partial u_i` and
$`V_i` multiplication by $`\sum_kA_{ik}u_k+c_i` is essentially self-adjoint on the
Hermite core of $`L^2(du_1du_2du_3)`, the operator is unbounded there, and the
domain is dense. Nothing here claims global regularity of the classical
Navier–Stokes PDE: the theorem is about the Hilbert-space operator at one
Eulerian fiber, where the derivative fields are independent canonical coordinates.
:::

```
#check @BookProof.HermiteProductBasis.hermiteMvBasis
#check @BookProof.NavierStokesFlow.DifferentialL2.momOp_apply_eq_differential
#check @BookProof.NavierStokesFlow.DifferentialL2.comm_momOp_posOp
#check @BookProof.NavierStokesFlow.DifferentialL2.velUnitary
#check @BookProof.NavierStokesFlow.DifferentialL2.intertwined_canH
#check @BookProof.NavierStokesFlow.DifferentialL2.nsDiffH
#check @BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_not_bounded
#check @BookProof.NavierStokesFlow.DifferentialL2.nsQuadraticDiffH_essentiallySelfAdjointOn_core
```

:::paragraph
That realization inherited its essential self-adjointness by transport: the
estimate was proved in the sequence picture and carried across `velUnitary`. The
Faris–Lavine argument can instead be run in $`L^2(du_1du_2du_3)` itself, against a
comparison operator that is also a differential operator. Take the harmonic
oscillator $`N_\mu=2\mu\sum_i(\pi_i^2+u_i^2/4)+1` (`nsDiffN`). The identity that
makes the two pictures one is `oscOp_eq_number`: on the Gauss–polynomial core,
$`\pi_i^2+u_i^2/4=a_i^\dagger a_i+\tfrac12`, which is the polynomial identity
`oscPoly_eq` obtained from the Leibniz rule $`\partial_i(u_ip)=p+u_i\partial_ip`.
So $`N_\mu` is the transport of multiplication by the comparison symbol
$`\mu(2|\beta|+3)+1` (`intertwined_nsDiffN`), and `embedCore_surjective` says the
Gauss–polynomial core *is* the transported finite-mode core. With that, the two
Faris–Lavine inequalities hold for the differential operator itself: the relative
bound $`\|Hf\|^2\le a\|Nf\|^2+b\|f\|^2` (`nsDiffH_relative_bound`) and the
form-commutator bound $`|\langle f,i[H,N]f\rangle|\le c\langle f,Nf\rangle`
(`nsDiffH_commForm_bound`), with $`\langle f,Nf\rangle\ge\|f\|^2`
(`nsDiffN_quadForm_ge_norm_sq`). Carried to the maximal domain of $`N` inside
$`L^2(\mathbb R^3)` (`diffMaxH_relative_bound`, `diffMaxH_commForm_bound`,
`diffMaxN_add_one_surjective`, `diffMaxN_core_approx`, `diffMaxH_restrict`), the
Faris–Lavine criterion then yields `nsDiffH_esa_of_farisLavine` — the same
conclusion as above, but obtained from an estimate on the differential operator
rather than from a transported theorem.
:::

```
#check @BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN
#check @BookProof.NavierStokesFlow.DiffFarisLavine.oscPoly_eq
#check @BookProof.NavierStokesFlow.DiffFarisLavine.oscOp_eq_number
#check @BookProof.NavierStokesFlow.DiffFarisLavine.intertwined_nsDiffN
#check @BookProof.NavierStokesFlow.DiffFarisLavine.embedCore_surjective
#check @BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_quadForm_ge_norm_sq
#check @BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_relative_bound
#check @BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_commForm_bound
#check @BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_relative_bound
#check @BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_commForm_bound
#check @BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_restrict
#check @BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine
```

:::paragraph
The sequence-space chain ends with an operator, not just a predicate. Essential
self-adjointness is usually stated as vanishing adjoint deficiency, but what it
*selects* is the closure of the graph: the operator `clExt T` on the closed
domain `clDom T` whose graph is the topological closure of `opGraph T`. The
passage is explicit here — `clExt_extends` (it agrees with `T` on the original
domain), `clExt_symmetricOn` (the closure is symmetric), and the adjoint
criterion `clExt_selfAdjointCriterion`: whenever the deficiency spaces of the
adjoint vanish, `clExt T` is self-adjoint, i.e. the adjoint domain is the
closed domain and the adjoint operator is the closed operator. With that, the
deficiency form of essential self-adjointness used throughout this development
is converted into the classical objects: `exists_isSelfAdjointExtension_of_esa`
gives a self-adjoint extension of a densely defined symmetric operator with
trivial deficiency (no positivity, boundedness or semiboundedness anywhere),
and `isSelfAdjointExtension_unique_of_esa` proves it is the *only* one — von
Neumann's theorem that deficiency indices `(0,0)` admit exactly one
self-adjoint extension. For a positive extension the two notions coincide:
`positiveExtension_eq_closure_of_esa` is the statement that for an essentially
self-adjoint operator the Friedrichs extension *is* the closure.
:::

```
#check @BookProof.EsaClosure.opGraph
#check @BookProof.EsaClosure.clGraph
#check @BookProof.EsaClosure.clDom
#check @BookProof.EsaClosure.clFun
#check @BookProof.EsaClosure.clExt
#check @BookProof.EsaClosure.clExt_extends
#check @BookProof.EsaClosure.clExt_symmetricOn
#check @BookProof.EsaClosure.clExt_selfAdjointCriterion
#check @BookProof.EsaClosure.exists_isSelfAdjointExtension_of_esa
#check @BookProof.EsaClosure.isSelfAdjointExtension_unique_of_esa
#check @BookProof.EsaClosure.positiveExtension_eq_closure_of_esa
```

:::paragraph
A Cayley-transform section takes the selected operator one step further: symmetry
of `A` makes `A ± i` equinormal (`norm_add_I_eq_norm_sub_I`), so
`exists_cayley_unitary` builds the unitary `U = (A - i)(A + i)⁻¹` with
`U(Ax + ix) = Ax - ix`, and `exists_selfAdjointExtension_and_cayley_of_esa` turns
an essentially self-adjoint core into both the self-adjoint operator and that
unitary. This is the passage from generator to unitary that the older prose
recorded as an alternative to Stone's theorem; with the Stone theorem proved in
full (2026-08-20e) the unitary *group* `e^{-itA}` now follows directly, and the
Cayley transform is the one-parameter step that makes the correspondence
explicit.
:::

```
#check @BookProof.EsaClosure.norm_add_I_eq_norm_sub_I
#check @BookProof.EsaClosure.exists_cayley_unitary
#check @BookProof.EsaClosure.exists_selfAdjointExtension_and_cayley_of_esa
```

:::paragraph
The Hashimoto/SIRK selection for the Navier–Stokes generator is the abstract
statement applied. On the finite-mode core of `ℓ²(Vel)` the coupled
three-component fiber Hamiltonian is symmetric, densely defined and essentially
self-adjoint (`velCore`, `velCore_symmetricOn`, `velCore_dense`, `velCore_esa`),
so `ns_selfAdjoint_extension` gives its unique self-adjoint extension and
`ns_hashimoto_selects` the selection: for an arbitrary sequence of non-real
shifts the SIRK resolvents exist, are bounded by `1/|Im γ_j|`, share the domain
of the generator, satisfy the resolvent identity, commute, satisfy the
Hashimoto–Nodera rational-Krylov relation, have strongly convergent Galerkin
truncations, and each determines the generator completely. Unlike the
Yang–Mills instantiation this route uses no positivity: the Navier–Stokes
Hamiltonian is not semibounded, and the non-real shift is what makes the
resolvent exist.
:::

```
#check @BookProof.NavierStokesFlow.NSHashimoto.velCore
#check @BookProof.NavierStokesFlow.NSHashimoto.velCore_symmetricOn
#check @BookProof.NavierStokesFlow.NSHashimoto.velCore_dense
#check @BookProof.NavierStokesFlow.NSHashimoto.velCore_esa
#check @BookProof.NavierStokesFlow.NSHashimoto.ns_selfAdjoint_extension
#check @BookProof.NavierStokesFlow.NSHashimoto.ns_selfAdjoint_extension_unique
#check @BookProof.NavierStokesFlow.NSHashimoto.ns_hashimoto_selects
#check @BookProof.NavierStokesFlow.NSHashimoto.ns_shiftInvert_selects
```

:::paragraph
The same selection now holds for the *differential* realization, the picture in
which the operator is written with `π_i = -i ∂/∂u_i` and `u_i` as a genuine
multiplication operator on the Hermite core of `L²(du₁du₂du₃)`. Gaussian
integration by parts makes the Weyl-ordered expression `∑_i ½(π_i V_i + V_i π_i)`
symmetric there (`nsDiffH_symmetricOn`, through the Gauss symmetry
`nsDiffPoly_polySym` of its polynomial form), so with the essential
self-adjointness already proved the closure is the unique self-adjoint operator
the core determines (`nsDiffH_selfAdjoint_extension`,
`nsDiffH_selfAdjoint_extension_unique`) and `nsDiffH_hashimoto_selects` is the
selection statement for it: for an arbitrary sequence of non-real shifts the
resolvents exist, are bounded, share the domain of the generator, satisfy the
resolvent identity and the Hashimoto–Nodera relation, have strongly convergent
Galerkin truncations, and each determines the generator completely. The
enumerated product Hermite functions supply the Hilbert basis the Galerkin
truncations are taken in (`exists_l2dHilbertBasisNat`).
:::

```
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_symmetricOn
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_selfAdjoint_extension_unique
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_hashimoto_selects
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_shiftInvert_selects
#check @BookProof.NavierStokesFlow.DiffHashimoto.nsQuadraticDiffH_hashimoto_selects
#check @BookProof.NavierStokesFlow.DiffHashimoto.exists_l2dHilbertBasisNat
```

:::paragraph
The Lagrangian route gets the same package, independently of the Eulerian one.
The Kato–Rellich theorem is proved for a *relatively bounded* — possibly
unbounded — symmetric perturbation: `essentiallySelfAdjointOn_add_relBounded`
shows `‖Bx‖ ≤ a‖Hx‖ + b‖x‖` with `a < 1` on the common domain preserves
essential self-adjointness, by an explicit Neumann iteration at a large
non-real shift, with no closure and no spectral theorem. Applied to the
transformed Hamiltonian, the positivity gain of the Lagrangian variables *is*
the relative bound: `norm_P_le` interpolates the first-order drift against the
second-order Laplacian by the Ikebe–Kato square-root bound, so
`hFull_hasZeroDeficiencyOn_of_drive_eq_P` gives essential self-adjointness of
the full transformed operator from the positive second-order part alone, and
`hasZeroDeficiencyOn_of_lagrangian_katoRellich` transports it back to the
Eulerian operator. On top of it the Hashimoto/SIRK selection is proved on the
Lagrangian side — `lagrangian_selfAdjoint_extension`, `..._unique`,
`lagrangian_hashimoto_selects` — independently of the Eulerian item 8, on the
abstract diagonal instance `diagKR` over `ℓ²(ℕ)`.
:::

```
#check @BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded
#check @BookProof.NavierStokesFlow.LagrangianKatoRellich.norm_P_le
#check @BookProof.NavierStokesFlow.LagrangianKatoRellich.hFull_hasZeroDeficiencyOn_of_drive_eq_P
#check @BookProof.NavierStokesFlow.LagrangianKatoRellich.hasZeroDeficiencyOn_of_lagrangian_katoRellich
#check @BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension
#check @BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_selfAdjoint_extension_unique
#check @BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_hashimoto_selects
#check @BookProof.NavierStokesFlow.LagrangianKatoRellich.lagrangian_shiftInvert_selects
#check @BookProof.NavierStokesFlow.LagrangianKatoRellich.diagKR
```

:::paragraph
The Lagrangian route is now realized at the same level as the Eulerian one. In
`ChapterNavierStokesLagrangianCanonical` the parcel momenta and the viscous
gradients are built as the canonical pairs of the trajectory-space Hermite
basis `ℓ²(Fin 3 → ℕ)`: with `ω = √(2ν)` the operators `Qᵢ = ω^{-1/2}(aᵢ + aᵢ†)/√2`
and `Pᵢ = ω^{1/2}·i(aᵢ† − aᵢ)/√2` obey the canonical commutation relations
(`comm_lagP_lagQ`, `comm_lagP_lagQ_of_ne`), so — unlike in the diagonal
instance `diagKR` — they genuinely fail to commute, and they are symmetric
because the ladder operators are mutually adjoint (`inner_ann_cre`). The
choice of frequency is exactly the one that diagonalizes the positive
second-order part: `posSq_add_momSq` is the oscillator identity `uᵢ² + πᵢ² = 2Nᵢ + 1`
and `lagCan_secondOrder_eq` reads the Lagrangian second-order part as the number
operator, `½∑Pᵢ² + ν∑Qᵢ² = ω(N + 3/2)`. Its eigenvectors are the Hermite states
(`lagT_coreState`), a total family, so it is essentially self-adjoint on the
Hermite core (`lagT_hasZeroDeficiencyOn`) while being unbounded
(`lagT_not_bounded`); Kato–Rellich then gives essential self-adjointness of the
*full* transformed Hamiltonian there (`lagCan_esa`), and Stone's theorem the
complete unitary flow (`lagCan_stone_flow`). Nothing here claims global
regularity of the classical Navier–Stokes equation.
:::

```
#check @BookProof.NavierStokesFlow.LagrangianCanonical.inner_ann_cre
#check @BookProof.NavierStokesFlow.LagrangianCanonical.posSq_add_momSq
#check @BookProof.NavierStokesFlow.LagrangianCanonical.comm_lagP_lagQ
#check @BookProof.NavierStokesFlow.LagrangianCanonical.comm_lagP_lagQ_of_ne
#check @BookProof.NavierStokesFlow.LagrangianCanonical.lagCanData
#check @BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_secondOrder_eq
#check @BookProof.NavierStokesFlow.LagrangianCanonical.lagT_coreState
#check @BookProof.NavierStokesFlow.LagrangianCanonical.lagT_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.LagrangianCanonical.lagT_not_bounded
#check @BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_esa
#check @BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_stone_flow
```

:::paragraph
Stone's theorem — the abstract theorem that turns essential self-adjointness into
a *complete* flow — is itself proved in this project (2026-08-20e). The forward
half, `ChapterStoneResolvent`–`ChapterStoneGenerator`, constructs the one-
parameter unitary group of an arbitrary self-adjoint operator on a Hilbert space:
the resolvent exists and is invertible (`shift_bijective`), is contractive and
commutes with the operator (`resCLM`, `norm_resCLM_apply_le`, `inner_res`,
`res_comm`), the Yosida approximants converge to the group in the strong
operator topology (`yosida_tendsto`), each approximant is a unitary
(`approxU_mem_unitary`), the limit `stoneU t` is a strongly continuous unitary
group (`stoneU`, `continuous_stoneU_apply`), it maps the domain into itself and
its derivative at zero recovers the original operator (`stoneU_mem_domain`,
`hasDerivAt_stoneU_zero`), so the abstract Stone generator `stoneGroup.gen`
coincides with the operator we started with (`gen_stoneGroup_eq`). The group
`e^{-itA}` is thus defined for *every* real `t` — this is the "complete
operator-flow" half of the `book.tex` §4210-4216 claim, now a theorem rather
than a named result.
:::

```
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.shift_bijective
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.resCLM
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.norm_resCLM_apply_le
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.inner_res
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.res_comm
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.yosida_tendsto
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.approxU_mem_unitary
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.continuous_stoneU_apply
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_mem_domain
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneGroup
#check @BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.gen_stoneGroup_eq
```

:::paragraph
The converse half, `ChapterStoneMeasurable`–`ChapterStoneConverse`, recovers the
infinitesimal generator from any weakly measurable one-parameter unitary group:
the generator domain `genDomain` is the set of vectors for which the derivative
at zero exists, `genOp` is that derivative, and the main theorem `gen_stoneU_eq`
says every weakly measurable group is the exponential of its generator. The
technical engine is the separability of `H`: on a separable space the generator
domain is dense (`dense_avgSpan` via averaging over a countable dense family),
the averages converge uniformly on it (`norm_apply_avgVec_sub_le`), and the
averaged vectors are continuous in `t` (`continuous_apply`). Combined, the two
halves give the bijection `stone_bijection` of `ChapterStoneTheorem` between
self-adjoint operators and weakly measurable unitary groups — Stone's theorem in
full.
:::

```
#check @BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.genDomain
#check @BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.genOp
#check @BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen
#check @BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.norm_apply_avgVec_sub_le
#check @BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.dense_avgSpan
#check @BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.continuous_apply
#check @BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup.gen_stoneU_eq
#check @BookProof.ChapterStoneTheorem.stone_bijection
```

:::paragraph
Both halves of Stone's theorem take the self-adjoint operator as given. The
*Cayley transform* (2026-08-24g, `ChapterCayleyTransform`,
`ChapterCayleyInverse`) is the classical device that removes the unboundedness
from the discussion altogether: for a densely defined self-adjoint `A` the map
`V = (A − i)(A + i)⁻¹` — assembled here from the resolvents above — is a
*unitary* (`norm_cayleyMap`, `cayleyMap_surjective`, `cayley`) characterised by
`V(A + i)ψ = (A − i)ψ` (`cayley_shift`); `1` is not an eigenvalue of `V`
(`cayley_apply_ne_self`, `one_sub_cayley_injective`), the range of `1 − V` is
exactly the domain of `A` (`range_one_sub_cayley`) and is therefore dense
(`denseRange_one_sub_cayley`), and `A` is recovered as `i(1 + V)(1 − V)⁻¹`
(`op_eq_cayley`, `coe_eq_cayley`). The correspondence is exact in both
directions: the basic criterion `isSelfAdjointOn_of_surjective` (symmetric with
`A ± i` onto implies self-adjoint) shows that the inverse Cayley transform
`i(1 + V)(1 − V)⁻¹` of *any* unitary `V` with `1 − V` injective is self-adjoint
on `ran(1 − V)` (`invCayleyOp_isSelfAdjointOn`, packaged as `ofUnitary`), and
the two constructions undo one another (`cayley_ofUnitary`,
`invCayleyDomain_cayley`, `invCayleyOp_cayley`). The unbounded layer is thus
faithfully encoded by a bounded object — the standard route by which the
spectral theorem for unbounded self-adjoint operators is reduced to the bounded
(normal) case treated in `ChapterSpectralMultiplication`.
:::

```
#check @BookProof.ChapterCayleyTransform.norm_cayleyMap
#check @BookProof.ChapterCayleyTransform.cayleyMap_surjective
#check @BookProof.ChapterCayleyTransform.cayley
#check @BookProof.ChapterCayleyTransform.cayley_shift
#check @BookProof.ChapterCayleyTransform.sub_cayley_shift
#check @BookProof.ChapterCayleyTransform.add_cayley_shift
#check @BookProof.ChapterCayleyTransform.one_sub_cayley_injective
#check @BookProof.ChapterCayleyTransform.cayley_apply_ne_self
#check @BookProof.ChapterCayleyTransform.range_one_sub_cayley
#check @BookProof.ChapterCayleyTransform.denseRange_one_sub_cayley
#check @BookProof.ChapterCayleyTransform.op_eq_cayley
#check @BookProof.ChapterCayleyTransform.coe_eq_cayley
#check @BookProof.ChapterCayleyInverse.isSelfAdjointOn_of_surjective
#check @BookProof.ChapterCayleyInverse.invCayleyOp_symmetric
#check @BookProof.ChapterCayleyInverse.invCayleyOp_isSelfAdjointOn
#check @BookProof.ChapterCayleyInverse.ofUnitary
#check @BookProof.ChapterCayleyInverse.cayley_ofUnitary
#check @BookProof.ChapterCayleyInverse.invCayleyDomain_cayley
#check @BookProof.ChapterCayleyInverse.invCayleyOp_cayley
```

:::paragraph
Composing that correspondence with the bounded spectral theorem gives a
multiplication model for the *unbounded* operator itself
(`ChapterCayleySpectralModel`). The step that makes the composition elementary is
that the resolvent is a *continuous* function of the Cayley transform:
`(A + i)⁻¹ = (2i)⁻¹(1 − V)` and `(A − i)⁻¹ = (2i)⁻¹(V⁻¹ − 1)`
(`res_neg_one_eq_cayley`, `res_one_eq_cayley`), and `V` is a bounded *normal*
operator (`cayleyCLM`, `isStarNormal_cayleyCLM`), so the continuous functional
calculus applies to the two symbols `g(z) = (1 − z)/(2i)` and `h(z) = (1 + z)/2`
with `g(V) = (A + i)⁻¹` and `h(V)y = A(A + i)⁻¹y` (`cfcHom_resSymbol`,
`cfcHom_opSymbol`). Feeding them through the model of
`ChapterSpectralMultiplication` yields
`unbounded_spectral_multiplication_model`: if the Cayley transform has a cyclic
unit vector, there are a Borel probability measure `μ` on its spectrum and a
unitary `U : L²(μ) ≃ H` such that *every* vector of `D(A)` is `U(g·u)` and
`A U(g·u) = U(h·u)` — that is, `A` is multiplication by
`h/g = i(1 + z)/(1 − z)`. Only the reduction to a *single* cyclic subspace is
still missing from the general unbounded spectral theorem.
:::

```
#check @BookProof.ChapterCayleySpectralModel.res_neg_one_eq_cayley
#check @BookProof.ChapterCayleySpectralModel.res_one_eq_cayley
#check @BookProof.ChapterCayleySpectralModel.cayleyCLM
#check @BookProof.ChapterCayleySpectralModel.isStarNormal_cayleyCLM
#check @BookProof.ChapterCayleySpectralModel.resSymbol
#check @BookProof.ChapterCayleySpectralModel.opSymbol
#check @BookProof.ChapterCayleySpectralModel.cfcHom_resSymbol
#check @BookProof.ChapterCayleySpectralModel.cfcHom_opSymbol
#check @BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol
#check @BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol
#check @BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model
```

:::paragraph
The capstone `ChapterStoneSeparable` packages the full statement: on a separable
Hilbert space there exists a unique one-parameter unitary group with a given
self-adjoint generator, and conversely every weakly measurable group has a unique
self-adjoint generator — `stone_exists_unique_group`,
`stone_exists_unique_generator`, `stoneEquiv`. The file ends with a nontrivial
*instantiated* example on `ℓ²(ℤ)` (which is separable, `separableSpace_L2Z`):
the momentum operator `mulSA` given by `f ↦ (i n f(n))` is a genuinely
self-adjoint (not merely essentially self-adjoint) unbounded operator
(`mulSA`, `mulSA_position_unbounded`), and its Stone group is the unitary shift
group of the lattice (`stoneU_mulSA`) — the same group structure that carries
the momentum generators of the gauged fibers. This is the concrete realization
of the `book.tex` "self-adjoint ⇒ complete flow" assertion, independent of the
Navier–Stokes truncation.
:::

```
#check @BookProof.ChapterStoneSeparable.stone_exists_unique_group
#check @BookProof.ChapterStoneSeparable.stone_exists_unique_generator
#check @BookProof.ChapterStoneSeparable.stoneEquiv
#check @BookProof.ChapterStoneSeparable.separableSpace_L2Z
#check @BookProof.ChapterStoneSeparable.mulSA
#check @BookProof.ChapterStoneSeparable.mulSA_position_unbounded
#check @BookProof.ChapterStoneSeparable.stoneU_mulSA
```

:::paragraph
The bridge from the selection predicates to the flow is now a single packaging
step, `ChapterStoneBridge`.  The essential-self-adjointness / Hashimoto-selection
threads produce `IsSelfAdjointExtension` / `IsPositiveSelfAdjointExtension`
operators on a dense domain, while Stone's theorem consumes the bundled
`UnboundedSelfAdjoint` structure; `dense_domain_of_isSelfAdjointExtension` and
`isSelfAdjointOn_of_isSelfAdjointExtension` pull the two missing conjuncts out of
the predicate, and `unboundedSelfAdjointOf` assembles the bundle.  The complete
unitary group is packaged as `IsStoneFlow` (`U 0 = 1`, the group law, isometry of
each `U t`, and the Schrödinger equation on the domain), `isStoneFlow_stoneU`
shows the abstractly constructed group is such a flow, and
`exists_stone_flow_of_selfAdjointExtension` / `of_positive` / `of_esa` are the
three entry points — from a selected self-adjoint extension, from a positive
(Friedrichs) one, and directly from essential self-adjointness of a symmetric
core.
:::

```
#check @BookProof.StoneBridge.dense_domain_of_isSelfAdjointExtension
#check @BookProof.StoneBridge.isSelfAdjointOn_of_isSelfAdjointExtension
#check @BookProof.StoneBridge.unboundedSelfAdjointOf
#check @BookProof.StoneBridge.IsStoneFlow
#check @BookProof.StoneBridge.isStoneFlow_stoneU
#check @BookProof.StoneBridge.exists_stone_flow_of_selfAdjointExtension
#check @BookProof.StoneBridge.exists_stone_flow_of_positive
#check @BookProof.StoneBridge.exists_stone_flow_of_esa
```

:::paragraph
`ChapterStoneFlows` runs that bridge on the three concrete Hamiltonians of this
development, so each of them — not a hypothetical example — generates a complete
unitary flow.  `ns_stone_flow` gives the flow of the coupled three-component
Eulerian fiber generator `velCore A c` on `ℓ²(Vel)` (the unique self-adjoint
extension, the closure; no positivity is used, so there is no Friedrichs label).
`lagrangian_stone_flow` gives the flow of the transformed (parcel) Hamiltonian
`ĥ_full = ½∑Pᵢ² + ν∑Qᵢ² + ∑fᵢDᵢ + C` from essential self-adjointness of its core,
and `diagKR_stone_flow` instantiates it on the genuinely unbounded `ℓ²(ℕ)`
instance — the hypothesis discharged by the Kato–Rellich relative bound.  On the
gauge side, `ym_fock_stone_flow` gives the flow of the second-quantized Yang–Mills
Hamiltonian `dΓ(½Σπ² + ½ΣB²)` on the Fock space over the Gauss core of
`L²(ℝ⁹⁹)`, where the extension *is* positive (Friedrichs).  This is step (c) of
`CONSOLIDATED_PLAN.md` §9 item 11 — the complete operator flow for all three —
and the honest boundaries are unchanged: the flow is that of the selected
extension in the abstract realization, and nothing is claimed about the classical
Navier–Stokes regularity problem.
:::

```
#check @BookProof.StoneFlows.ns_stone_flow
#check @BookProof.StoneFlows.lagrangian_stone_flow
#check @BookProof.StoneFlows.diagKR_stone_flow
#check @BookProof.StoneFlows.ym_fock_stone_flow
```

:::paragraph
Essential self-adjointness glues along an orthogonal direct sum, and
`ChapterDirectSumEsa` isolates that step once and for all.  A deficiency vector of
`⊕ᵢ Hᵢ` may be tested against a state living in a single fibre, and the identity it
then satisfies is exactly the fibre deficiency identity, so each of its coordinates
vanishes: `dsOp_deficiencyTrivialAt`, hence `dsOp_essentiallySelfAdjointOn`.  No
relative bound, no comparison operator and no commutator estimate are involved — the
hypothesis is only that every fibre operator is essentially self-adjoint on its own
core — and `dsCore_dense` adds that the algebraic direct sum of the fibre cores is
dense as soon as every fibre core is.  The payoff is the continuum parcel picture:
`ChapterNavierStokesFockContinuum` proved essential self-adjointness of the
second-quantized Hamiltonian one sector at a time (on `L²(ℝⁿ)` it is multiplication by
the total energy `∑ₖ w(ξₖ)`, an operator with in general purely continuous spectrum and
no eigenvectors), and `fockH_hasZeroDeficiencyOn` is the same statement on the *whole*
Fock space `⊕ₙ L²(ℝⁿ)` — for an arbitrary measurable field `w`, with `fockCore_dense`
and `fockH_isSymmetricDom` supplying dense definition and symmetry.  Feeding that into
the Stone bridge closes the circle: `dsOpD_stone_flow` turns a family of dense fibre
cores carrying symmetric fibre operators of vanishing deficiency into a self-adjoint
extension of the glued operator together with the unitary group it generates, and
`fockH_stone_flow` is that statement for the continuum Fock Hamiltonian — the complete
flow `e^{−itĥ}` solving the Schrödinger equation on the domain.  The
honest boundary is that the fibres must be mutually orthogonal and invariant: this is
the discrete form of a direct-integral gluing, not a decomposition theorem.
:::

```
#check @BookProof.DirectSumEsa.dsCore
#check @BookProof.DirectSumEsa.dsOp
#check @BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt
#check @BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn
#check @BookProof.DirectSumEsa.dsOpD_hasZeroDeficiencyOn
#check @BookProof.DirectSumEsa.dsCore_dense
#check @BookProof.DirectSumEsa.fockCore_dense
#check @BookProof.DirectSumEsa.fockH_isSymmetricDom
#check @BookProof.DirectSumEsa.fockH_hasZeroDeficiencyOn
#check @BookProof.DirectSumEsa.dsOpD_stone_flow
#check @BookProof.DirectSumEsa.fockH_essentiallySelfAdjointOn
#check @BookProof.DirectSumEsa.fockH_stone_flow
```

:::paragraph
Carleman's criterion supplies the last realization of the *full* Navier–Stokes
Hamiltonian in which the momentum genuinely fails to commute with the field modes.
On the half-line lattice `ℓ²(ℕ)` the momentum is the symmetric-difference operator
and the fifteen field modes are multiplication by arbitrary — in particular unbounded
— real sequences; `weyl_momOp_diagOp` computes the Weyl-symmetrized product
`½(π A + A π)` and finds a tridiagonal (Jacobi) operator whose off-diagonal coupling
is `c_n = −(i/2)(α_n + α_{n+1})` for the Navier–Stokes symbol `α`, so
`halfLineFullData_hamiltonian` identifies the whole Hamiltonian as one Jacobi matrix.
The analytic input is `tridiag_hasZeroDeficiencyOn_of_carleman`: the classical
Wronskian argument — `tridiag_wronskian` for the discrete Green identity,
`wron_eq_sum` for its telescoping, `sum_normSq_le` for the resulting inequality —
shows that a deficiency vector would force `∑ 1/|c_n|` to converge, so divergence of
that sum gives essential self-adjointness.  Hence
`halfLineFull_hasZeroDeficiencyOn`, and, for a linearly growing viscous mode,
`linearFull_hasZeroDeficiencyOn` together with `linearFull_not_bounded`: an
unbounded, non-commuting, essentially self-adjoint full Navier–Stokes Hamiltonian.
The dichotomy is the lattice form of the ODE chapter's `ẋ = x²` warning — Carleman's
sum diverges for subquadratic growth and can converge for faster growth, where
`ChapterNavierStokesDeficiency` already exhibits a Jacobi operator that is *not*
essentially self-adjoint.
:::

```
#check @BookProof.NavierStokesFlow.Carleman.tridiagOp
#check @BookProof.NavierStokesFlow.Carleman.tridiagOp_isSymmetricDom
#check @BookProof.NavierStokesFlow.Carleman.tridiag_wronskian
#check @BookProof.NavierStokesFlow.Carleman.wron_eq_sum
#check @BookProof.NavierStokesFlow.Carleman.sum_normSq_le
#check @BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman
#check @BookProof.NavierStokesFlow.Carleman.momOp
#check @BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp
#check @BookProof.NavierStokesFlow.Carleman.halfLineFullData
#check @BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian
#check @BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.Carleman.linearFull_not_bounded
```

# Summary

The free-field thread replaces the nonexistent infinite-dimensional Lebesgue measure
with the rotation-invariant Gaussian, pushes it to a uniform measure on the sphere,
and then applies the Born rule to parametrize the simplex — all the while the gauge
fibers keep track of the invisible phase. The two negative results (no Lebesgue
measure; positive-measure partitions are countable) are not obstacles but the precise
statements that make the construction both necessary and well-defined.

The same free-field parametrization carries the Navier–Stokes thread: the velocity
field and its derivatives are independent canonical degrees of freedom, and on a
finite truncation the Weyl-symmetrized Hamiltonian has a complete, norm-preserving
flow, a unique global solution to the Cauchy problem, and a nilpotent BRST
constraint. Beyond the truncation, the essential self-adjointness of the generator
is now proved across an entire chain of abstract models in the Hermite
(sequence-space) representation: the bilinear quadratic-symbol Hamiltonian on
`ℓ²(ℕ × J)` (`BilinearEsa.bilH_essentiallySelfAdjointOn_core`), its affine
extension covering the viscous and cross terms (`AffineFiber.affH` /
`AffineBlock.affBlockH`), the sign-flip unitary that drops the `c ≥ 0` hypothesis
(`SignFlip.saffH` / `sblockH`), and finally all three coupled velocity components
with an arbitrary real velocity gradient (`SignedShift.gaffH`,
`ThreeComponent.velH`). The instrument throughout is the Faris–Lavine commutator
criterion, now itself proved (Theorem 1 + Cor. 1.1) rather than named. The
canonical reading of that same fiber is supplied by
`CanonicalVector` (`comm_ann_cre`, `comm_mom_pos`), which builds the ladder
pairs *inside* the sequence space and proves `canH_eq_velH` — the matrix
$`H` of the previous paragraph is the Weyl-ordered expression
$`\sum_i\tfrac12(\pi_iV_i+V_i\pi_i)` — so `canH_essentiallySelfAdjointOn_core`
and, with the Navier–Stokes coefficients, `nsQuadraticH_essentiallySelfAdjointOn_core`
are the same statement in canonical form. The
selected operators are made explicit by the graph-closure machinery of
`EsaClosure` (`clExt`, `IsSelfAdjointExtension`,
`exists_isSelfAdjointExtension_of_esa`, `isSelfAdjointExtension_unique_of_esa`,
`positiveExtension_eq_closure_of_esa`, and the Cayley-transform unitary), and the
selection is then *instantiated* on the Navier–Stokes side twice: by the
Hashimoto/SIRK resolvent route on the Eulerian fiber (`NSHashimoto.velCore`,
`ns_hashimoto_selects` — no positivity needed) and by the Kato–Rellich relative
bound on the Lagrangian side (`norm_P_le`,
`hFull_hasZeroDeficiencyOn_of_drive_eq_P`,
`lagrangian_hashimoto_selects`). The honest
boundary drawn at the end of that chain is the genuinely differential realization
of these operators on `L²(du)` (the abstract models give the operator by its
matrix in the Hermite basis only), and the *classical* existence/uniqueness claim
of `book.tex` (the Clay regularity problem) is not carried by any theorem here —
the operator-flow global existence would follow from the differential ESA by the
Stone theorem of 2026-08-20e, but that ESA is itself the open step; see
`Book/YangMillsQuantization.lean` for the pointer to this formalized subset.
Stone's theorem itself — the missing bridge from ESA to a complete flow — is now
proved in full (`stone_bijection` between self-adjoint operators and weakly
measurable unitary groups, `stoneEquiv` on separable spaces, instantiated on
`ℓ²(ℤ)` by the momentum operator `mulSA`), and the bridge is then *run*: the
packaging step `StoneBridge` (`unboundedSelfAdjointOf`, `IsStoneFlow`,
`exists_stone_flow_of_selfAdjointExtension` / `of_positive` / `of_esa`) turns a
selected extension into the bundled structure Stone consumes, and `StoneFlows`
instantiates the complete unitary flow for the Eulerian NS (`ns_stone_flow`), the
Lagrangian NS (`lagrangian_stone_flow`, `diagKR_stone_flow`) and the QYM
(`ym_fock_stone_flow`).  The *only* remaining step for a flow on the continuum is
the differential ESA, and the truncation already carries the complete flow
(`nsCauchy_existsUnique`).
