import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Solovay–Kopperman Tensor Product" =>
%%%
tag := "solovay-tensor"
%%%

# Orientation and Status

:::paragraph
The second chapter of the foundation, and the construction the physics parts
run on: finite observable data coupled to a separable infinite-dimensional
Hilbert space. We distinguish the product of probability spaces from the tensor
product of their wave-function spaces. The Mehler sphere limit supplies the
Gaussian coordinate prior; the Kopperman perspective asks which statements our
chosen language can decide. The construction allows an arbitrary finite-head
law, rather than every probability law on every function space.
:::

:::paragraph
The route: the three-instant ABL reconstruction and its joint and marginal laws
(the finite-dimensional model), post-selection and the reconstruction formula,
the tensor product and its finite-query language, the two factors and their
laws (arbitrary on the finite head, Gaussian on the tail with specified finite
marginals), the cross-dimensional inner product, and a closing
account of what is proved versus planned.
:::

:::paragraph
The proofs are spread across `BookProof/ChapterSolovayHilbertTensor`,
`ChapterSolovaySeparableExistence`, `ChapterSolovayCrossDim`,
`ChapterSolovayTailDimension`, `ChapterTensorCompleteness`, and the Mehler
uniqueness and orthogonal-invariance chapters; the planned items are stated in
the chapter and collected in {ref "proof-plans"}[the appendix]. The chapter
below on {ref "statistical-model-theory"}[statistical model theory] closes this
part, and the {ref "free-field"}[free-field chapter] later reuses the Mehler
measure as its Gaussian.
:::

# The Question

:::paragraph
The Introduction asks for a usable probability model of functions or fields:
a carrier with countable dense approximants, a reference prior, and a language
of queries that can be evaluated from finite data. These are separate
requirements. Separable function spaces and probability measures on them are
standard objects; the specific task here is to combine their analytic structure
with an explicitly controlled query language.
:::

:::paragraph
The manuscript also repeatedly forms *tensor products of sample spaces*. A joint
probability density lives on a product $`X \times Y`; the prior wave-function can be
"redefined as a tensor product of two Fock-spaces"; and often "we are interested in a
tensor product of sample spaces, some of which have finite degrees of freedom," for
instance $`\mathbb{Z}_2^n \times \mathbb{R}^m`. The construction below answers the
Introduction's problem precisely by building such a tensor product: a
*finite-dimensional* factor that carries an *arbitrary* probability law, tensored
with a *separable infinite-dimensional* wave-function factor built from a specified
Gaussian law. Uniqueness means uniqueness with those Gaussian finite marginals.
:::

:::paragraph
A simpler finite-dimensional instance of the same problem arises in
{ref "double-slit"}[the double-slit chapter]: given only the final screen position,
can one reconstruct the intermediate "which slit" trajectory? The
Aharonov–Bergmann–Lebowitz (ABL) two-state reconstruction answers this affirmatively.
The reconstruction is a finite-phase-space version of the same idea: a quantum
trajectory can be measured directly only at its final time, but the intermediate
instants can be recovered from the statistics of runs that ended in a chosen final
outcome — using probabilities conditional on the final state and the same quantum
time-evolution.
:::

# The Three-Instant ABL Reconstruction

:::paragraph
Model three instants — initial, intermediate, final — on a finite phase space. A unit
initial wave-function $`\Psi` is evolved by a unitary $`U` to the intermediate time,
where a measurement in the standard basis yields outcome $`a` with the Born
probability and *collapses* the state to $`e_a`:
:::

```
#check @midProb
```

:::paragraph
The collapsed state is then evolved by a unitary $`V` to the final time, where outcome
$`f` occurs with probability
:::

```
#check @transProb
```

:::paragraph
Both are genuine probabilities — non-negative, and each sums to one over its outcomes:
:::

```
#check @midProb_nonneg
#check @midProb_sum
#check @transProb_sum
```

# The Joint and Marginal Laws

:::paragraph
The joint law of the intermediate outcome $`a` and the final outcome $`f` is the
product of the two Born factors:
:::

```
#check @jointProb
```

:::paragraph
Summing over the intermediate outcome gives the marginal law of the final outcome:
:::

```
#check @finalProb
```

:::paragraph
The collapsed three-instant process is a genuine probability law: the marginal final
probabilities sum to one. This uses only the unitarity of $`U` and $`V` and the
normalization $`\|\Psi\| = 1`:
:::

```
#check @finalProb_total
```

# Post-Selection: the Reconstruction Formula

:::paragraph
Now condition on the final outcome $`f`. The *post-selected* law of the intermediate
outcome — the probability that the trajectory passed through $`a`, given that it ended
at $`f` — is the conditional probability
:::

$$`\mathrm{condProb}(f, a) = \frac{\mathrm{jointProb}(f, a)}{\mathrm{finalProb}(f)}.`

```
#check @condProb
#check @condProb_nonneg
```

:::paragraph
For each fixed final outcome $`f`, this is again a probability distribution over the
intermediate outcomes:
:::

```
#check @condProb_sum
```

:::paragraph
This is the reconstruction: although $`a` was not recorded, its conditional
distribution is determined by the final outcome and the same unitary evolution, and it
is a honest probability law.
:::

# Consistency of the Reconstruction

:::paragraph
The reconstruction does not depend on which final outcome one post-selects. Summing
the post-selected joint law over *all* final outcomes recovers the original
intermediate Born distribution:
:::

```
#check @jointProb_sum_final_eq_midProb
```

:::paragraph
So the intermediate statistics are stable: marginalizing the reconstructed joint law
back over the final outcomes returns exactly the Born probabilities one would have
measured directly at the intermediate time. The post-selection adds information about
individual runs without distorting the ensemble.
:::

# The Solovay–Kopperman Tensor Product

:::paragraph
The ABL reconstruction is a finite-phase-space instance of the general problem. The
general construction — the Solovay–Kopperman tensor product — answers the
Introduction's question directly: it is a systematic separable probability space
carrying an arbitrary finite-head law and a specified Gaussian coordinate law.
Its Hilbert-space interpretation requires keeping the following spaces distinct.
:::

# A Finite Vector Space Tensored with an Infinite Hilbert Space

:::paragraph
The tensor product in the question motivating this chapter is
$`V \widehat\otimes K`, where $`V` has finite dimension $`d` and $`K` is a
separable infinite-dimensional Hilbert space. Fix an orthonormal basis
$`e_1,\ldots,e_d` of $`V`. Every vector then has a unique description
:::

$$`\Psi=\sum_{a=1}^{d}e_a\otimes\psi_a,\qquad
\langle\Psi,\Phi\rangle=\sum_{a=1}^{d}\langle\psi_a,\phi_a\rangle_K.`

:::paragraph
Thus $`V\widehat\otimes K\cong K^d`: a finite list of Hilbert-space vectors.
The completion is already accounted for by completeness of $`K`. This is the
useful computational picture: finitely many channels, each admitting arbitrarily
accurate finite approximations. It does not require truncating the Hilbert space
once and for all.
:::

:::paragraph
For the Gaussian realization, take $`\Omega=\mathbb R^{\mathbb N}` with
$`\gamma=\bigotimes_{j\ge0}\mathcal N(0,1)` and
$`K=L^2(\Omega,\gamma;\mathbb C)`. Hermite polynomials in finitely many
coordinates give the finite expressions; their completed span gives the
wave-function Hilbert space. A finite discrete head with $`d` positive weights
$`\mu_a` realizes the same tensor product as
$`L^2(\{1,\ldots,d\}\times\Omega,\mu\otimes\gamma)`:
its channel coordinates are $`\psi_a(z)=\sqrt{\mu_a}\Psi(a,z)`.
The product-measure tensor and density theorems cited below supply the general
analytic ingredients. This displayed finite-channel specialization is an
explanation of them, not a new Lean declaration.
:::

:::paragraph
A finite-dimensional *coordinate carrier* is a different notion. With a
continuous head $`x\in\mathbb R^N`, the book uses
$`L^2(\mathbb R^N,\mu)\widehat\otimes K`.
Its first factor can itself be infinite-dimensional: one real coordinate has
infinitely many independent square-integrable functions. Also,
$`\mathbb R^N\times H` is a product (a finite Hilbert direct sum when $`H` is
Hilbert), whereas $`\mathbb R^N\widehat\otimes H\cong H^N` is a tensor
product. The two constructions serve different purposes.
:::

# A Two-Channel Calculation

:::paragraph
Let $`h_0(z)=1` and $`h_1(z)=z_0` under the standard Gaussian product law.
They are orthonormal because $`\mathbb E z_0=0` and $`\mathbb E z_0^2=1`.
For $`V=\mathbb C^2`, the state
$`\Psi=\alpha e_1\otimes h_0+\beta e_2\otimes h_1` has squared norm
$`|\alpha|^2+|\beta|^2`. Its normalization is an exact finite calculation,
even though its ambient space is infinite-dimensional. More general finite
Hermite expansions use finitely many Gaussian moments, computable exactly for
algebraic coefficients. A general completed vector is handled by approximants
and a supplied error modulus; density alone gives no algorithm for that modulus.
:::

# The Two Factors

:::paragraph
The total sample space splits as a finite *head* times an infinite *tail*:
:::

```
#check @InnerSpace
#check @InnerHead
#check @InnerTail
```

:::paragraph
The head $`\mathrm{InnerHead}\,N = \mathrm{Fin}\,N \to \mathbb{R} \cong \mathbb{R}^N`
is an ordinary finite-dimensional Euclidean Hilbert space. The tail
$`\mathrm{InnerTail}` is the Kopperman *substrate*, the standard separable real
Hilbert space $`L^2([0,1])`. Its separability is the topological precondition for
everything that follows, and it is verified directly:
:::

```
#check @kopperman_substrate_separable
#check @substrate_decidable_skeleton
```

:::paragraph
Separable, but not small: the tail carries a *countable* orthonormal family — the
normalized indicators of the disjoint intervals $`(1/(n+2),\,1/(n+1)]` — and
therefore has infinitely many independent directions. The head–tail split is not a
finite-dimensional artefact:
:::

```
#check @BookProof.ChapterSolovayTailDimension.substrateBasisVector_orthonormal
#check @BookProof.ChapterSolovayTailDimension.substrate_infinite_dimensional
#check @BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional
```

:::paragraph
The theorem `substrate_decidable_skeleton` proves existence of a countable dense
subset. Its type does not provide an enumeration, computable membership, or an
approximation algorithm. Such effective data must be supplied separately, for
example by rational finite expansions in a specified basis. Separability gives
the analytic possibility of approximation; effective presentation makes that
possibility usable by an algorithm.
:::

# What the Decidability Claim Means

:::paragraph
Decidability is a property of a specified language and its effective semantics.
For the pure real inner-product language, a finite tuple of vectors is described
by a finite Gram matrix. Positivity of that matrix is a finite collection of
polynomial conditions; a new vector is represented by its projections and an
orthogonal remainder. This leads to reductions to real closed fields.
Solovay, Arthan and Harrison prove decidability for their two-sorted first-order
Hilbert-space languages in §6 of
[their paper](https://arxiv.org/abs/0904.3482).
Kopperman's [1967 paper](https://doi.org/10.2307/2270770) concerns the distinct
infinitary $`L_{\omega_1,\omega_1}` setting. Its role here is to motivate the
careful separation of the completed carrier from the language used to describe it.
:::

:::paragraph
For example, two unit vectors with real overlap $`r` have Gram matrix
$`\left(\begin{smallmatrix}1&r\\r&1\end{smallmatrix}\right)`.
Such vectors exist in an infinite-dimensional real Hilbert space exactly when
$`1-r^2\ge0`. For algebraic $`r` this is an effective finite test of a statement
quantifying over infinite-dimensional vectors. Gaussian moment evaluation in
the two-channel example is a separate finite calculation.
:::

:::paragraph
The finite tensor factor preserves the finite-tuple description through
$`V\widehat\otimes K\cong K^d`. A decision claim for an expanded language
must also specify its allowed coefficients, predicates and operators and prove
the corresponding reduction. Arbitrary measures, Hamiltonians and expectation
operators do not automatically belong to the decidable pure geometric language.
:::

:::paragraph
The repository currently proves two more concrete facts. First,
`DecidableLanguage` packages a Boolean classifier. Its tensor classifier runs
the two supplied classifiers and takes their conjunction:
:::

```
#check @tensor_decide_apply
#check @tensor_language_membership_decidable
```

:::paragraph
Second, tensoring finite-head observables preserves dependence on a finite
head, and their inner products reduce to a finite-dimensional integral:
:::

```
#check @tensorHeadObservable_dependsOnlyOnHead
#check @tensor_language_decidable
#check @headSumEquiv
```

:::paragraph
Despite its name, `tensor_language_decidable` states an integral identity. It
has no encoded formulas, terminating decision algorithm or correctness theorem
for all sentences of a Hilbert-space theory. Likewise, a Lean Boolean function
on an arbitrary carrier is not by itself a Turing computation on finite codes.
A finite-head integral for an arbitrary probability measure need not be
computable. Effective polynomial geometry and explicit Gaussian moment queries
are useful controlled fragments; broader decision procedures remain separate
formalization tasks.
:::

# The Tensor-Product Hilbert Space

:::paragraph
The abstract sample carrier is the product
$`\mathrm{InnerSpace}\,N = \mathrm{InnerHead}\,N \times \mathrm{InnerTail}`.
Wave-functions on it belong to an $`L^2` space. `SolovayHilbertSpace` is the
metric completion of that wave-function space; it is not the product carrier
itself:
:::

```
#check @SolovayHilbertSpace
```

:::paragraph
The infinite tail itself tensors with a copy of itself back into a single tail: two
infinite Gaussian coordinate sequences interleave into one, and the product Mehler
law is carried exactly to the Mehler law. This is the measure-theoretic content of
$`\Gamma \otimes \Gamma \cong \Gamma` for the infinite factor:
:::

```
#check @tailTensorEquiv
#check @tailTensorEquiv_map
```

:::paragraph
The embedding of a wave-function into the completion preserves its inner
product. This proves the completion respects the existing geometry; the
product-measure and density results below establish the tensor interpretation:
:::

```
#check @toSolovay_inner
```

:::paragraph
In the coordinate model the tensor identification is available in full. Two Solovay
systems combine into one — the finite heads concatenate and the two Mehler tails
interleave — and the combination carries the *product* of the two state laws to the
state law of the combined system. That measure-preserving isomorphism induces a
unitary of the corresponding $`L^2` spaces, which is the Hilbert-space form of
$`H(N_1) \otimes H(N_2) \cong H(N_1+N_2)`:
:::

```
#check @BookProof.ChapterSolovayHilbertTensor.solovayTensorEquiv
#check @BookProof.ChapterSolovayHilbertTensor.solovayTensorEquiv_map
#check @BookProof.ChapterSolovayHilbertTensor.solovayTensorUnitary
```

:::paragraph
And the elementary tensors behave as elementary tensors must: a product
$`f(x)g(y)` of two square-integrable factors is square-integrable for the product
law, and the inner product of two such pure tensors is the product of the two
inner products.
:::

```
#check @BookProof.ChapterSolovayHilbertTensor.tensorLp
#check @BookProof.ChapterSolovayHilbertTensor.inner_tensorLp
```

:::paragraph
The completeness half holds too, for any two finite laws: the closed linear span
of the pure tensors is *all* of $`L^2(\mu \otimes \nu)`. The proof is the classical
π–λ argument — the indicator of a measurable rectangle $`s \times t` is the pure
tensor $`1_s \otimes 1_t`; the measurable sets whose indicator lies in the closed
span contain the rectangles and are stable under complements and countable
disjoint unions, hence are all of them; and indicators generate $`L^2`. Written as
an approximation statement, this is *separation of variables*: every
square-integrable function of two variables is an $`L^2`-limit of finite sums
$`\sum_k f_k(x)g_k(y)`. Together with the multiplicativity of the inner product on
pure tensors, it says that $`L^2(\mu \otimes \nu)` *is* the Hilbert tensor product
of $`L^2(\mu)` and $`L^2(\nu)` — a statement one can make here even though the
library has no Hilbert tensor product to name:
:::

```
#check @BookProof.ChapterTensorCompleteness.pureTensors
#check @BookProof.ChapterTensorCompleteness.indicator_mem_tensorSpan
#check @BookProof.ChapterTensorCompleteness.tensorSpan_eq_top
#check @BookProof.ChapterTensorCompleteness.pureTensors_dense
#check @BookProof.ChapterTensorCompleteness.exists_tensor_approx
```

:::paragraph
The practical corollary is the *product basis*. Writing $`u \otimes v` for the pure
tensor of two $`L^2` elements, the inner product multiplies and the norm
multiplies, the operation is bilinear and continuous in each slot; so the products
$`e_i \otimes f_j` of two orthonormal families are orthonormal, and if both
families are total then so is the family of products. A basis of the two-factor
state space is therefore obtained by multiplying a basis of each factor — the
familiar bookkeeping of a composite quantum system:
:::

```
#check @BookProof.ChapterTensorCompleteness.tensorOf
#check @BookProof.ChapterTensorCompleteness.inner_tensorOf
#check @BookProof.ChapterTensorCompleteness.norm_tensorOf
#check @BookProof.ChapterTensorCompleteness.orthonormal_tensorOf
#check @BookProof.ChapterTensorCompleteness.tensorFamily_span_eq_top
```

:::paragraph
Orthonormality and totality can be packaged into a single object. Given a Hilbert
basis $`(b_i)` of $`L^2(\mu)` and a Hilbert basis $`(c_j)` of $`L^2(\nu)`, the
products $`b_i \otimes c_j`, indexed by pairs, *are* a Hilbert basis of
$`L^2(\mu \otimes \nu)`. Its coefficients are the two-variable Fourier
coefficients $`\langle b_i \otimes c_j, F\rangle`, every square-integrable
function of two variables is the unconditional sum of its components, and
Parseval holds in the product form
$`\sum_{i,j} |\langle b_i \otimes c_j, F\rangle|^2 = \|F\|^2`. This is the
bookkeeping a composite quantum system actually uses:
:::

```
#check @BookProof.ChapterTensorCompleteness.tensorHilbertBasis
#check @BookProof.ChapterTensorCompleteness.coe_tensorHilbertBasis
#check @BookProof.ChapterTensorCompleteness.tensorHilbertBasis_repr_apply
#check @BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis
#check @BookProof.ChapterTensorCompleteness.hasSum_sq_norm_inner_tensorHilbertBasis
```

:::paragraph
The *decoupling theorem* applies to head-only wave-functions: because they
depend only on the finite head, and the tail measure is an independent
probability measure, the $`L^2` inner product over the infinite-dimensional total
space collapses exactly to a finite-dimensional integral over the head
$`\mathbb{R}^N`:
:::

```
#check @inner_reduces_to_head
```

:::paragraph
For head-only functions $`f(x,z)=f_0(x)` and $`g(x,z)=g_0(x)`, independence
and $`\gamma(\Omega)=1` remove the tail integral exactly. For a cylindrical
function involving $`k` tail coordinates, first enlarge the head and integrate
those $`k` Gaussian variables as well. This supplies finite input to a chosen
moment or integration procedure. Its computability and error bounds require
assumptions on that input; Tarski's theorem decides polynomial formulas, not
arbitrary integrals.
:::

# An Arbitrary Law on the Finite Part

:::paragraph
On the finite head we may choose *any* probability law. Given any probability
measure $`\mathrm{headDist}` on $`\mathbb{R}^N`, the product with the tail law is a
probability measure on the total space, and its finite marginal is exactly the law we
chose:
:::

```
#check @stateMeasure_isProbability
#check @stateMeasure_finite_marginal
```

:::paragraph
Put together, that is precisely the Introduction's question answered: a separable
probability space, over an infinite-dimensional carrier, on which the law of the
finite part may be chosen arbitrarily while the infinite part carries the Mehler
law — in the coordinate model and in the abstract substrate model alike:
:::

```
#check @BookProof.ChapterSolovaySeparableExistence.exists_separable_prob_with_arbitrary_finite_law
#check @BookProof.ChapterSolovaySeparableExistence.exists_separable_prob_with_arbitrary_finite_law_substrate
#check @BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional
```

:::paragraph
On the finite part the wave-function parametrization is always available: any
finite joint law is the squared modulus of a wave-function, and taking the
marginal of the Born probabilities gives the marginal of the law. And any joint
law whose second factor is standard Borel factors as its own marginal composed
with a Markov kernel — the disintegration used to condition without rewriting
history:
:::

```
#check @BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction
#check @BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod
#check @BookProof.ChapterSolovaySeparableExistence.prod_disintegration
```

:::paragraph
The same statement in the explicit coordinate model, where the tail is a countable
product of standard Gaussians:
:::

```
#check @coordinateStateMeasure
#check @coordinateStateMeasure_isProbability
```

:::paragraph
This is the finite-dimensional freedom the author wants: *our knowledge of the
finite-dimensional part is an arbitrary probability distribution.* Nothing
constrains it; it is the part we are free to choose.
:::

# From Uniform Hyperspheres to the Mehler Prior

:::paragraph
Start with independent $`G_j\sim\mathcal N(0,1)`. Radial normalization gives
$`U_n=(G_1,\ldots,G_n)/(\sum_{j=1}^nG_j^2)^{1/2}`, uniform on the unit
sphere in $`\mathbb R^n`. The strong law makes the denominator divided by
$`\sqrt n` tend to $`1`. Consequently, for each fixed $`k`,
:::

$$`\sqrt n\,(U_{n,1},\ldots,U_{n,k})
\ \Longrightarrow\ \mathcal N(0,I_k).`

:::paragraph
Equivalently, use spheres of radius $`\sqrt n` and leave their coordinates
unscaled. The unscaled coordinates of a unit sphere instead tend to zero.
The convergence is of fixed finite-coordinate distributions. This classical
Poincaré–Borel limit is the probabilistic reading of the manuscript's Mehler
sphere formalism; see the research account
[Limiting Probability Measures](https://arxiv.org/abs/1901.10507).
It motivates the compatible Gaussian marginals from which the coordinate tail
law is constructed. The existing `poincare_borel_ae` theorem already proves
the key coupling:
normalized Gaussian coordinates converge almost surely, coordinate by
coordinate, to the original Gaussian sequence. Packaging this as weak
convergence of fixed-dimensional sphere marginals requires identifying the
finite-block pushforward laws and applying bounded continuous test functions.
The polynomial and weight limits below provide complementary results.
:::

:::paragraph
For the resulting product law, the existing theorem states
$`n^{-1}\sum_{j<n}z_j^2\to1` almost surely:
:::

```
#check @mehler_concentrates_on_unit_sphere
#check @PhysHSGaussian.poincare_borel_ae
```

:::paragraph
The name uses the manuscript's sphere terminology. Its statement concerns an
*empirical mean squared radius*. In particular, $`\sum_j z_j^2=\infty`
almost surely. A Gaussian sequence sampled from this law is not an
$`\ell^2` vector or a point on the norm-unit sphere of a separable Hilbert space.
The countably additive prior lives on the sequence space $`\mathbb R^{\mathbb N}`;
its square-integrable wave-functions form the Hilbert space $`K` used above.
:::

# The Hilbert Space Associated with the Gaussian Prior

:::paragraph
There is also a Hilbert space of Gaussian *directions*. For
$`a\in\ell^2`, the sums $`\sum_{j<m}a_jz_j` converge in $`L^2(\gamma)` to
$`W(a)`, with $`\mathbb E[W(a)W(b)]=\langle a,b\rangle`.
Thus $`\ell^2` embeds isometrically as the first Gaussian chaos. This is a
Gaussian process indexed by a Hilbert space, although a sampled coordinate
sequence is not a vector in that Hilbert space.
:::

:::paragraph
To obtain an actual Hilbert-valued Gaussian random vector instead, choose a
positive trace-class covariance $`C`: in an eigenbasis, take
$`X=\sum_j\sqrt{\lambda_j}G_je_j` with $`\sum_j\lambda_j<\infty`.
Then $`\mathbb E\|X\|^2=\sum_j\lambda_j`. Identity covariance in infinite
dimension fails this condition. This distinction is explained in
[Hairer's Gaussian measure notes](https://hairer.org/notes/SPDEs.pdf).
A chosen covariance changes the prior and its symmetry group; it must be
recorded when identifying a field model with the Gaussian construction.
:::

:::paragraph
The earlier abstract substrate is $`L^2([0,1])` and its selected prior
`rcpPriorOnSubstrate` is obtained from existence of an atomless probability
measure. The current construction uses an orthonormal pair and an atomless
sphere measure. It does not identify that selected measure with the Gaussian
coordinate product, or prove that it is invariant under every orthogonal
operator of the substrate. An isometry between separable Hilbert spaces alone
would not establish equality of these probability laws. The coordinate model
is where the explicit Gaussian splitting and characterization theorems live.
:::

```
#check @TailPriorAdmissible
#check @only_mehler_on_tail
#check @tailMeasure_singleton
#check @mehler_invariant_under_finite_orthogonal
```

:::paragraph
Here `only_mehler_on_tail` establishes admissibility of the selected abstract
prior. Its invariance field assumes measure preservation and then concludes
equality of the pushed-forward measure. The uniqueness result for specified
Gaussian marginals below is stronger and uses a different, coordinate carrier.
:::

# The Polynomial Form of the Mehler Limit

:::paragraph
A single coordinate of uniform spherical area has a Gegenbauer weight; the
joint coordinates are constrained by the sphere and are not independent at
finite dimension. Write the weight as $`(1-u^2)^{\lambda-1/2}` and substitute
$`u=x/\sqrt\lambda`. Then
:::

$$`\lim_{\lambda\to\infty}(1-x^2/\lambda)^{\lambda-1/2}=e^{-x^2}.`

:::paragraph
After normalization this is a Gaussian of variance $`1/2`. The coordinate
convention above uses variance $`1`, obtained by multiplying $`x` by
$`\sqrt2`. Stating the variance prevents a hidden factor of two when moving
between the sphere, Hermite polynomials and field operators.
:::

:::paragraph
At the same time the Gegenbauer polynomials $`C_n^{(\lambda)}` (orthogonal with
respect to the uniform measure, and defining the hyperspherical harmonics) become
the Hermite polynomials $`H_n/n!` (with the physicists' $`H_n` from the recurrence
$`H_0 = 1, H_1 = 2x, H_{n+2} = 2x H_{n+1} - 2(n+1)H_n`), in the scaled limit
:::

$$`\lim_{\lambda\to\infty}\lambda^{-n/2}
  C_n^{(\lambda)}(x/\sqrt\lambda)
   = \frac{H_n(x)}{n!}.`

:::paragraph
And the normalizations converge consistently: the (squared) Gegenbauer
normalization integral against the hyperspherical weight tends to the Hermite
normalization integral against the Gaussian weight, $`\int_\mathbb{R}[H_n(x)/n!]^2
e^{-x^2}dx = \sqrt{\pi}\,2^n/n!`. The verified statements live in
`BookProof.PhysHSGaussian`:
:::

```
#check @PhysHSGaussian.physHermite
#check @PhysHSGaussian.gegenbauer
#check @PhysHSGaussian.gegenbauerScaled
#check @PhysHSGaussian.gegenbauerScaled_tendsto_hermite
#check @PhysHSGaussian.weight_tendsto_gaussian
#check @PhysHSGaussian.hermite_normalization
#check @PhysHSGaussian.normalization_tendsto
#check @PhysHSGaussian.gaussian_concentration_sphere
```

:::paragraph
For each fixed polynomial degree, the scaled Gegenbauer functions converge to
Hermite functions with the displayed normalization. Tensor products of Hermite
polynomials give the Gaussian Fock description. The limiting dictionary is:
:::

| Finite hypersphere | Fixed-coordinate Gaussian limit |
| :--- | :--- |
| scaled, normalized coordinate marginals | normalized Gaussian coordinate law |
| weight $`(1-u^2)^{\lambda-1/2}` | weight $`e^{-x^2}` |
| scaled Gegenbauer polynomials | Hermite polynomials $`H_n/n!` |
| hyperspherical harmonics | number states $`\ket{n}` |
| uniform "no-information" prior | Gaussian source qsample $`\Psi_0 = \ket{0}` |

:::paragraph
The fixed-coordinate sphere limit and the Hermite limits explain the Gaussian
choice and the Fock basis. Uniqueness of that choice uses the specified Gaussian
marginals, rather than unnameability of individual states alone. The prior of
{ref "free-field"}[the free-field chapter] is the same object, and why the Gaussian
source qsample $`\sqrt{p_0}` of a flow model coincides with the Fock vacuum. The
finite-hypersphere-to-Fock dictionary is the structural backbone of this part and of
the whole book.
:::

:::paragraph
In the coordinate model the prescribed marginals are explicit. Queries use finite
coordinate sets, and restriction to any finite set has the corresponding finite
product Gaussian law:
:::

```
#check @finiteCoordinateMarginal
```

:::paragraph
So the only data the language can observe is the family of finite-dimensional
marginals, and a probability measure on $`\mathbb{N} \to \mathbb{R}` is determined by
its finite marginals. The intended conclusion — that the Mehler measure is the
_unique_ law with the prescribed standard Gaussian finite marginals — is proved:
cylinder sets
form a generating π-system, so a projective limit of finite measures is unique.
:::

```
#check @BookProof.ChapterMehlerUniqueness.mehler_unique_by_finite_marginals
#check @BookProof.ChapterMehlerUniqueness.mehler_characterization
#check @BookProof.ChapterMehlerUniqueness.language_blind_implies_mehler
#check @BookProof.ChapterMehlerUniqueness.solovay_kopperman_probability_classification
```

:::paragraph
The condition on *every* finite marginal is essential. Two distinct sequences
always differ at some finite coordinate, and cylindrical tests can distinguish
many different priors. The theorem `language_blind_implies_mehler` assumes
agreement of expectations for all finite-coordinate real functions; it does not
derive that agreement from a Boolean classifier or from atomlessness.
`head_vs_tail_admissibility` records the separate abstract admissibility package:
:::

```
#check @head_vs_tail_admissibility
```

:::paragraph
The invariance half is now available in *concrete coordinates*, not only at the
abstract measure-preserving interface. The characteristic function of the standard
$`k`-dimensional Gaussian is $`\exp(-\|t\|^2/2)`, a function of the norm alone, so
the finite Gaussian head is invariant under the whole orthogonal group $`O(k)`; and
rotating the first $`k` coordinates of the infinite tail therefore leaves the Mehler
law unchanged:
:::

```
#check @BookProof.ChapterMehlerOrthogonalInvariance.charFun_stdGaussianEuclidean
#check @BookProof.ChapterMehlerOrthogonalInvariance.stdGaussianEuclidean_map_isometry
#check @BookProof.ChapterMehlerOrthogonalInvariance.gaussianHead_map_orthogonal
#check @BookProof.ChapterMehlerOrthogonalInvariance.coordinateTailMeasure_map_headRotation
```

:::paragraph
*Heads admit an arbitrary law; the tail admits the Mehler law.* That single
statement is the probabilistic content of the Solovay–Kopperman tensor product.
:::

# The Cross-Dimensional Inner Product

:::paragraph
Because the Mehler tail *splits* — the first $`k` Gaussian coordinates separate off
as an independent finite Gaussian block, leaving a fresh copy of the tail — we may
enlarge the finite head by adjoining $`k` tail coordinates:
:::

```
#check @tailSplitEquiv
#check @enlargeEquiv
```

:::paragraph
This makes the inner product well-defined *across dimensions*: an element with
$`N` head-coordinates and an element with $`N+k` head-coordinates can be compared
after padding the smaller one with $`k` fresh Gaussian coordinates, and the result
does not depend on the padding, because the added coordinates integrate to $`1`. The
finite dimensions "match" precisely because the Mehler measure is a product. The
measure-preservation of the coordinate tail-split — the theorem that splitting off
the first $`k` coordinates carries the Mehler law to the product of a finite Gaussian
head with a fresh copy of the tail — is proved:
:::

```
#check @tailSplitEquiv_map
```

:::paragraph
The cross-dimensional statement is now a theorem, not just an assertion: the
enlargement map $`N \mapsto N+k` is a *measure-preserving isomorphism* of the
corresponding state spaces, so it is a genuine embedding of the $`N`-dimensional
coordinate model into the $`(N+k)`-dimensional one. Consequently every expectation,
and in particular the $`L^2` inner product of two wave-functions, is unchanged when
it is computed after enlarging the head — the value does not depend on which head
dimension the computation is performed in. This is the manuscript's "the inner
product is well defined across head dimensions," made precise:
:::

```
#check @BookProof.ChapterSolovayCrossDim.cross_dim_embedding
#check @BookProof.ChapterSolovayCrossDim.integral_cross_dim_well_defined
#check @BookProof.ChapterSolovayCrossDim.inner_cross_dim_well_defined
#check @BookProof.ChapterSolovayCrossDim.lintegral_cross_dim_well_defined
#check @BookProof.ChapterSolovayCrossDim.cross_dim_isProbability
```

# What Is Proved and What Is Planned

| Layer | Source results and scope |
| :--- | :--- |
| Hilbert substrate | separable, infinite-dimensional; existence of a countable dense set |
| Completion | complete wave-function space; inner-product-preserving embedding |
| Finite queries | Boolean conjunction; head-only inner-product reduction |
| Gaussian tail | finite marginals; splitting, interleaving, finite orthogonal invariance |
| Uniqueness | a law with those same Gaussian finite marginals equals the product law |
| Hilbert tensor structure | product-law unitary, pure-tensor density, bases and Parseval |
| Sphere ingredients | radial measures, concentration, coordinatewise coupling, polynomial limits |

:::paragraph
The cited declarations are existing source proofs; this documentation edit has
not compiled them. Remaining tasks are an effective syntax and decision
procedure for the intended expanded language, packaging of the existing almost-sure coupling as weak
sphere-marginal convergence, and any claimed measure-preserving bridge
between the abstract substrate prior and the coordinate model. See
{ref "proof-plans"}[the specialist plan]. None of these tasks requires replacing
the available tensor-density or Gaussian-marginal uniqueness proofs.
:::

# Why This Matters Here

:::paragraph
The construction gives a usable hierarchy: finite channels tensored with a
completed Gaussian wave-function space, finite Hermite expressions for exact
calculations, and norm limits with explicit error estimates for more general
states. A Gaussian vacuum provides a reference prior. Interactions specify an
operator and a state relative to that reference; the reference prior alone does
not establish existence, a mass gap or decidability of the interacting theory.
:::

:::paragraph
In the nested-Fock physics chapters this is a representation of the inner
one-particle space. The final Hamiltonian remains
$`H=\sum_{i,j}C^\dagger(e_i)h_{ij}A(e_j)`:
creation on the left, annihilation on the right, with the complete interacting
inner $`h` and its constants retained. Choosing a Gaussian reference or finite
channel coordinates supplies no justification for discarding terms of $`h`.
The outer vacuum is annihilated by the rightmost operator; this statement is
distinct from choosing the Gaussian inner reference state.
:::

:::paragraph
Uniformity means invariance under a stated symmetry group and a stated scaling
limit. The Mehler prior is canonical once its Gaussian cylindrical marginals
are specified. This supplies a precise interpretation of the manuscript's
“uniform infinite sphere” while leaving the choice of coordinates, covariance
and observable language visible to the reader.
:::
