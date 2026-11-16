import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Euclidean Moments and Reflection Positivity at the Regulator" =>
%%%
tag := "euclidean-moments"
%%%

:::paragraph
The continuum-limit programme (`cftproof.md`) builds the Euclidean reconstruction in
stages. _C0_ fixes the manifest of assumptions, _C1_ constructs the finite-cutoff
massive Gaussian control in Mehler coordinates and proves its reflection positivity for
bounded cylinder observables, and _C2_ asks for the *interacting* regulated state together
with its Euclidean dictionary. This chapter documents the part of _C2_ that is formalized:
the Euclidean moment hierarchy, the separated-time two-point functions, and reflection
positivity of the reflected (Osterwalder–Schrader) form at the regulator. The interacting
closure is not part of what is proved here, and the last section says exactly where the
boundary lies.
:::

:::paragraph
The mathematical content is small and worth stating before any code. Fix a bounded
operator $`K` on a Hilbert space and a unit reference vector $`\Omega`. The Euclidean
evolution is $`e^{-hK}`; a *word* of insertions $`(\Delta_1, A_1), \dots, (\Delta_n, A_n)`
produces the operator product
$`A\,e^{-\Delta_1 K} A_1 \cdots e^{-\Delta_n K} A_n`, and its *moment* is that operator
sandwiched between $`\Omega`. This is the finite-mode regulator: every operator is bounded,
every moment is a finite scalar, and no domain question arises. The interesting structure is
not the existence of the moments but their *positivity* under time reflection.
:::

# The Moment Hierarchy

The Euclidean evolution and its semigroup law are the only dynamics the hierarchy needs.

```
BookProof.OSReconstruction.euclidEvol K h = NormedSpace.exp ((-(h : ℂ)) • K)
BookProof.OSReconstruction.euclidEvol_zero   : euclidEvol K 0 = 1
BookProof.OSReconstruction.euclidEvol_add  : euclidEvol K (s + t) = euclidEvol K s * euclidEvol K t
```

Words are ordered products, and the _extension convention_ says that splitting a word at
a gap composes the two operator products — appending a word is composing with the operator
of the appended word.

```
BookProof.OSReconstruction.euclidWord_append :
  euclidWord K A (l₁ ++ l₂) = euclidWord K (euclidWord K A l₁) l₂
```

The empty word and the normalization of the reference vector are the base case:

```
BookProof.OSReconstruction.euclidMoment_nil      : euclidMoment K Ω A [] = ⟪Ω, A Ω⟫
BookProof.OSReconstruction.euclidMoment_one_nil  : ‖Ω‖ = 1 → euclidMoment K Ω 1 [] = 1
```

# Separated-Time Two-Point Functions

The two-point function of the hierarchy inserts $`A` at time $`0` and $`B` at the later
time $`h`:

```
BookProof.OSReconstruction.twoPoint K Ω A B h = euclidMoment K Ω A [(h, B)]
BookProof.OSReconstruction.twoPoint_eq        : twoPoint K Ω A B h = ⟪Ω, A (euclidEvol K h (B Ω))⟫
BookProof.OSReconstruction.twoPoint_zero      : twoPoint K Ω A B 0 = ⟪Ω, A (B Ω)⟫
```

At zero separation the observable paired with its adjoint gives the square that all of the
positivity is built on:

```
BookProof.OSReconstruction.twoPoint_adjoint_zero :
  twoPoint K Ω (ContinuousLinearMap.adjoint A) A 0 = ((‖A Ω‖ ^ 2 : ℝ) : ℂ)
```

# Reflection Positivity of the Reflected Form

Time reflection sends an insertion of $`A_i` at time $`+s_i` to an insertion of $`A_i^\dagger`
at time $`-s_i`. Pairing the reflected family with the original family gives the
_reflected form_

```
reflectedForm K Ω f  =  Σ_i Σ_j ⟨A_i Ω, e^{-(s_i + s_j) K} A_j Ω⟩,
```

whose individual entries are exactly the separated-time two-point functions of the previous
section.

The reflection-positivity statement at the regulator is that this doubly-summed form is a
squared norm. It needs only that the Euclidean evolutions be self-adjoint — which holds
whenever the generator is, since the exponent $`-hK` is a real multiple of a self-adjoint
operator and the exponential preserves self-adjointness.

```
BookProof.OSReconstruction.euclidEvol_isSelfAdjoint :
  IsSelfAdjoint K → IsSelfAdjoint (euclidEvol K s)
BookProof.OSReconstruction.euclidMoment_adjoint_eq_inner :
  euclidMoment K Ω (adjoint A) [(s + t, B)] = ⟪e^{-sK}(A Ω), e^{-tK}(B Ω)⟫
BookProof.OSReconstruction.reflectedForm_eq_inner :
  reflectedForm K Ω f = ⟪reflectedVector K Ω f, reflectedVector K Ω f⟫,
    reflectedVector K Ω f = Σ_i e^{-s_i K}(A_i Ω)
BookProof.OSReconstruction.reflectedForm_re_nonneg :
  0 ≤ (reflectedForm K Ω f).re
```

No degree restriction appears anywhere: the norm square is produced by the sum
factorization, not by Wick's theorem on individual moments. Writing out the two-insertion
case makes the mechanism visible — the four-term reflected form of insertions at times
$`s` and $`t` is the squared norm of a sum of two evolved vectors:

```
BookProof.OSReconstruction.twoPoint_reflected_eq_normSq :
  ⟨A† e^{-2sK} A⟩ + ⟨A† e^{-(s+t)K} B⟩ + ⟨B† e^{-(s+t)K} A⟩ + ⟨B† e^{-2tK} B⟩
    = ‖e^{-sK}(A Ω) + e^{-tK}(B Ω)‖ ^ 2
BookProof.OSReconstruction.twoPoint_reflected_re_nonneg :
  the real part of the left-hand side is nonnegative
```
# The Interacting Half-Space Inequality

The form above is an inner-product identity on a Hilbert space, not a statement about a measure.
The measure-level version lives in the half-space modules and reads: for the state `covState ν`,
a pair of fields on the two halves that share a random shift, and a bounded measurable observable
`F` of one half,

```
BookProof.OSReconstruction.covState_reflectionPositive :
  0 ≤ ∫ z, F z.2 * F z.1 ∂covState ν
```

The reverse ordering in the integrand is the reflection: `ρ` swaps the halves, so the reflected
observable is `F` evaluated on the *first* coordinate. An interaction turns that inequality into a
question about a non-Gaussian state, and there is exactly one class of interactions where the
answer is inherited without any expansion: the ones whose Boltzmann weight factorizes across the
reflection plane.

```
ρ(z) = g z₁ * g z₂,   g ≥ 0 a positive-time weight,
BookProof.OSReconstruction.intWeight g z
BookProof.OSReconstruction.intState ν g          = (covState ν).withDensity (intWeight g)
BookProof.OSReconstruction.intState_univ         : mass = ∫⁻ ρ ∂(covState ν)
```

This is the lattice form of $`e^{-V}` with $`V = V_+ + \theta V_+`: an interaction built from
positive-time fields together with its reflection, the Dyson–Lieb–Simon class. Reflecting it costs
nothing, because the two factors are already one per half. The interacting Osterwalder–Schrader
form then *is* the free form of a different observable — each factor of the weight joins the
observable on its own side —

```
⟨θF F⟩_int = ∫ θF F · g₁ g₂ dμ₀ = ∫ θ(F g) (F g) dμ₀ ≥ 0
```

and the last inequality is the free statement applied to $`F g`$:

```
BookProof.OSReconstruction.intState_reflectionPositive :
  0 ≤ ∫ z, F z.2 * F z.1 ∂intState ν g        (g bounded, measurable, nonnegative)
BookProof.OSReconstruction.intState_expectation_re_nonneg :
  the normalized form 0 ≤ ⟨θF F⟩_int / ∫ 1 ∂intState ν g
```

The point is what the proof does *not* need: no cluster expansion, no smallness of the coupling,
no Gaussian approximation, and no cutoff removal. The interaction has to factorize, not to be
weak. That is also the honest limit of the statement — a general reflection-invariant positive
density does not preserve reflection positivity, and nothing here claims a converse. The weight is
a positive-time weight on the free state rather than a Gibbs measure with a pressure and a
thermodynamic limit, each term's weight `g` and the observable `F` are bounded (the mixture is
not), and `F` is a cylinder observable of one half rather than an element of the $`L^2`$ closure
of the positive-time algebra.

Nothing above used the fact that the weight has one term. A nonnegative *series* of factorized
weights is reflection positive term by term — the OS form of the mixture is the series of the OS
forms, and a series of nonnegative numbers is nonnegative — so the same argument covers

```
ρ(z) = ∑' i, (g i) z₁ * (g i) z₂,   every g i bounded,   Σᵢ C² Dᵢ² < ∞
BookProof.OSReconstruction.intStateSum ν g            = ∑' i, intState ν (g i)
BookProof.OSReconstruction.intStateSum_univ           : mass = ∑' i, ∫⁻ ρᵢ ∂μ₀
BookProof.OSReconstruction.intStateSum_reflectionPositive :
  0 ≤ ∫ z, F z.2 * F z.1 ∂intStateSum ν g
```

Such a density is not bounded: the bounds $`D_i`$ grow with $`i`$, so this is an unbounded
$`V_+`$ written as a sum of bounded pieces, and the summability $`\sum_i C^2 D_i^2 < \infty`$ is
exactly what makes the total form finite. What it is *not* is a general $`V_+`$: the weight still
has to decompose into matched factorized pairs, so a density outside the cone generated by the
$`g_1g_2`$ remains out of reach.

The boundedness of `F` is removable too, for a reason internal to the proof: the bound is used
only to make the triple product integrable. Stated as what it is — the OS form is finite — the
statement covers unbounded `F` and unbounded `g` alike.

```
BookProof.OSReconstruction.covState_reflectionPositive_of_integrable :
  0 ≤ ∫ z, H z.2 * H z.1 ∂covState ν          (H measurable, form integrable)
BookProof.OSReconstruction.intState_reflectionPositive_of_integrable :
  0 ≤ ∫ z, F z.2 * F z.1 ∂intState ν g        (g ≥ 0 measurable, no bound; form integrable)
```

The mean-of-squares representation $`\langle \theta H, H\rangle = \int (S_t H)^2\,d\nu`$ is
unchanged, so finiteness is the only hypothesis left — and it is a hypothesis that can be
*discharged*, not merely narrowed. The two halves of the form are integrated against shifted copies
of the same Gaussian, so an $`L^2`$ statement about the shift lives one product measure away from
the integrand. That distance is closed by two measure-preserving projections:

```
measurePreserving_covMarginal_left  : (t, x, y) ↦ (t, x)  pushes  ν ⊗ (γ ⊗ γ)  to  ν ⊗ γ
measurePreserving_covMarginal_right : (t, x, y) ↦ (t, y)  pushes  ν ⊗ (γ ⊗ γ)  to  ν ⊗ γ
```

Both are `Prod.map id Prod.fst` and `Prod.map id Prod.snd`, so `Measure.map_prod_map` reduces each
to the marginal law of a single Gaussian, and that marginal is $`\gamma`$ itself because $`\gamma`$
is a probability. Lifting `MemLp` along them and multiplying the two halves by Hölder
(`MemLp.integrable_mul`) produces the triple integrability, hence

```
BookProof.OSReconstruction.covState_reflectionPositive_of_memLp :
  0 ≤ ∫ z, H z.2 * H z.1 ∂covState ν      (H measurable, H(· + ·) ∈ L²(ν ⊗ γ))
```

The bounded-truncation argument is *not* what closes this, and the reason is worth recording: the
truncations $`H \wedge N \vee (-N)`$ converge with a dominator only if some integrable majorant of
$`(S_t H)^2`$ exists, which is the finiteness being proved. The lift-and-Hölder route has no such
circle, and it needs no boundedness anywhere.


# Sandwiching the Free Regulator Against the C1 Slices

C1 fixes the free Gaussian control in Mehler coordinates. In the slice coordinates
$`x_0 = (y_+ - y_-)/\sqrt2` and $`x_1 = (y_+ + y_-)/\sqrt2` its two-slice covariance is

```
C = [[A, B], [B, A]],   A = (v₊ + v₋)/2,   B = (v₊ − v₋)/2,
```

with Mehler variances $`v_+ = 1/(\lambda + 1)` and $`v_- = 1/(\lambda + 3)`. The diagonal is
the slice variance, and the cross term is positive — the sign responsible for C1's
reflected-covariance positivity.

The C2 hierarchy reproduces this covariance as a two-point function. In the state of norm
$`\sqrt A`, the free one-mode regulator with mass $`m` has

```
⟨Ω, e^{-hK} Ω⟩ = A · e^{-h m},
```

so choosing $`e^{-m} = B/A` — the Mehler covariance ratio, which lies in $`(0,1)` —
produces diagonal $`A` and unit-separation cross term $`B`:

```
BookProof.OSReconstruction.sliceDiagonal, sliceCross
BookProof.OSReconstruction.sliceCross_pos            : 0 < B
BookProof.OSReconstruction.sliceCross_lt_sliceDiagonal : B < A
BookProof.OSReconstruction.euclidMoment_scalarK_sqrt :
  euclidMoment (scalarK m) (√A) 1 [(h, 1)] = ↑(A * Real.exp (-(h * m)))
BookProof.OSReconstruction.free_regulator_reproduces_slice_covariance :
  ∃ m ≥ 0, (zero-separation moment = A) ∧ (unit-separation moment = B)
BookProof.OSReconstruction.free_regulator_twoPoint_reflected_re_nonneg :
  reflection positivity at this calibration
```

This is the bridge between the two constructions: the covariance C1 obtains by inverting a
two-slice Gaussian is, at one mode and unit separation, the two-point function of a free
transfer semigroup — and reflection positivity of that semigroup is the same norm-square
identity as above.

# The Reflected Form Is a Positive Semidefinite Form

Reflection positivity gives nonnegativity on the diagonal. That is already enough to obtain
the object the reconstruction needs, because the reflected form turns out to *be* an inner
product of explicitly given vectors, with no measure theory involved.

Pair two finite families rather than one, and the reflected form becomes a sesquilinear
form on the positive-time observables:

```
reflectedPair K Ω f g = Σ_i Σ_j ⟨A_i Ω, e^{-(s_i + s_j) K} B_j Ω⟩
reflectedPair_self        : reflectedPair K Ω f f = reflectedForm K Ω f
reflectedPair_eq_inner    : reflectedPair K Ω f g = ⟪reflectedVector K Ω f, reflectedVector K Ω g⟫
reflectedPair_conj_swap   : reflectedPair K Ω g f = conj (reflectedPair K Ω f g)
```

Three consequences make the pair form usable rather than merely nonnegative:

```
reflectedForm_re_eq_normSq     : (reflectedForm K Ω f).re = ‖reflectedVector K Ω f‖ ^ 2
reflectedForm_eq_zero_iff      : reflectedForm K Ω f = 0 ↔ reflectedVector K Ω f = 0
reflectedPair_eq_zero_of_null  : reflectedForm K Ω f = 0 → reflectedPair K Ω f g = 0
reflectedPair_cauchy_schwarz   : ‖reflectedPair K Ω f g‖
                                   ≤ √(reflectedForm K Ω f).re * √(reflectedForm K Ω g).re
```

The middle two say the null space of the form is exactly the kernel of the reflected vector,
so the pairing descends to the quotient of positive-time observables by null families — the
first well-definedness obligation of the reconstructed inner product. The last is
Cauchy–Schwarz, obtained from the ordinary Hilbert-space inequality applied to the reflected
vectors.

Applying it to a pair of insertions gives the standard Osterwalder–Schrader bound on the
two-point function: the two-by-two reflected matrix of `A` at time $`s` and `B` at time $`t`
is positive semidefinite, so

```
twoPoint_cauchy_schwarz :
  ‖⟨A† e^{-(s+t)K} B⟩‖ ^ 2
    ≤ ⟨A† e^{-2sK} A⟩.re * ⟨B† e^{-2tK} B⟩.re
```

Nothing beyond self-adjointness of the generator enters. In particular no spectral
hypothesis, no positivity of the evolution in an ordered space, and no Gaussian assumption is
used: the inequality is a consequence of RP and of the semigroup alone.

# The Reconstructed Pre-Hilbert Space

Having a nonnegative form and a well-defined quotient is not yet a Hilbert space. What makes
the reconstruction work at the regulator is that the quotient can be *realized*: keep each
family's insertion times separate from its operators, and the reflected vector becomes a
function of the operator family alone.

```
familyVector K Ω s A   = Σ_i e^{-s_i K} (A_i Ω)
familyVector_add       : familyVector K Ω s (A + A') = familyVector + familyVector
familyVector_smul      : familyVector K Ω s (c • A) = c • familyVector K Ω s A
```

So `familyVector` is the underlying map of a complex-linear map `familyVectorLM` into the
regulator Hilbert space, and the reflected pairing is simply the ambient inner product of
the images:

```
familyPair K Ω s A t B = ⟪familyVector K Ω s A, familyVector K Ω t B⟫
familyForm K Ω s A     = familyPair K Ω s A s A
```

`familyPair_eq_reflectedPair` checks that this is the same pairing as the double sum over
separated-time two-point functions, so nothing has been redefined along the way. The
consequences read as the inner-product axioms on classes:

```
familyPair_add_left, familyPair_add_right   linearity in each family
familyForm_eq_normSq                        familyForm = ↑‖familyVector‖ ^ 2
familyForm_re_nonneg                        the diagonal is nonnegative
familyForm_eq_zero_iff                      form = 0  ↔  reflected vector = 0
familyPair_eq_zero_of_null                  null families pair to zero
familyPair_congr_left                       the pairing depends only on the class
familyForm_sub_re_eq_dist_sq                class distance = ambient distance
familyPair_cauchy_schwarz                   the class pairing obeys Cauchy–Schwarz
```

Together these are what `reflected_reconstruction` bundles: the reflected pairing is the
inner product of the images of a linear map, its kernel is exactly the null families, the
diagonal is nonnegative, and the pairing obeys Cauchy–Schwarz. The quotient of positive-time
families by null families is therefore a pre-Hilbert space, isometric to the range of the
reconstruction map inside the regulator space; completing it is the only step still missing
to obtain the reconstructed Hilbert space at the regulator.

# The Coarse Density of a Block Step

The C3 programme begins with a step that contains no estimate at all: integrating a block of
the reference Gaussian out. The plan states its requirement as a warning — the coarse density
of $`|\Psi|^2` is $`E[|\Psi|^2 \mid G]`, not $`|E[\Psi \mid G]|^2` — and since these are
different functionals the warning is a theorem, not a convention.

Take the reference law to be two independent unit Gaussians, the first coordinate the block
and the second the exterior field. Coarse graining integrates out the block at fixed exterior
field:

```
blockIntegral f y      = ∫ x, f (x, y) ∂gamma
integral_blockIntegral : ∫ f d (gamma ⊗ gamma) = ∫ (blockIntegral f) ∂gamma
```

The second line is the tower identity: the partition-function content survives the step
intact. What does *not* survive is the density. The block step is additive on integrable
slices, pointwise nonnegative, normalised at constants, and fixes observables of the exterior
field — a positive unital linear map — and it is characterised as the conditional expectation
by pairing:

```
blockIntegral_add, blockIntegral_nonneg
blockIntegral_const, blockIntegral_exterior
blockIntegral_mul_exterior : ∫ (blockIntegral f) g ∂gamma = ∫ f (g ∘ snd) d (gamma ⊗ gamma)
```

Nothing in that last identity chooses a sigma-field: it is the characterising property of the
conditional expectation on cylinder test functions, stated as an equality of integrals.

For the cylinder observable $`\Psi_c(x,y) = x + c y` the two prescriptions can be read off:

```
blockIntegral_blockField           : blockIntegral (blockField c) y = c * y
blockIntegral_blockField_sq        : blockIntegral (fun p => blockField c p ^ 2) y = 1 + c^2*y^2
coarseDensity_eq_naiveDensity_add  : coarseDensity c y = naiveDensity c y + 1
coarseDensity_ne_naiveDensity      : coarseDensity c 0 ≠ naiveDensity c 0
integral_naiveDensity              : ∫ naiveDensity = c^2   while   ∫ |\Psi|^2 = 1 + c^2
variance_decomposition             : ∫ |\Psi|^2 = ∫ naiveDensity + 1
```

The conditional mean is the linear regression $`c y`; the coarse density is $`1 + c^2 y^2`,
and the squared conditional mean is $`c^2 y^2`. The difference is the conditional variance of
the block coordinate — $`1`, independent of both $`y` and $`c` — which is exactly the quantity
the plan insists must be preserved alongside the conditional means. At $`y = 0` the coarse
density is $`1` and the naive one vanishes, so no hypothesis can reconcile them; and the
totals differ by the same `1`, which is why the naive density cannot be repaired by a
normalisation.

# Two Block Steps, and the Small-Field Packet

A single step proves that the coarse density is the conditional second moment, but the
programme needs the step to be _iterable_. The same construction is therefore applied twice,
with a second block coordinate — the shell — integrated out after the first. Nothing new is
introduced: the second step is `blockIntegral` applied to the result of the first.

```
blockChainLaw                   = (gamma ⊗ gamma) ⊗ gamma
blockStep f z y                 = ∫ x, f (x, z, y) ∂gamma
blockChainDensity f y           = ∫ z, blockStep f z y ∂gamma
integral_blockChainDensity      : ∫ f d blockChainLaw = ∫ (blockChainDensity f) ∂gamma
blockChainDensity_const, blockChainDensity_nonneg, blockChainDensity_add
blockChainDensity_exterior
```

The composed map is again a positive unital linear map fixing the exterior field, and the
tower identity holds for it in the same form, so coarse graining twice loses nothing of the
partition function. The interesting content is what happens to the conditional mean and to
its covariance.

For the three-coordinate cylinder field $`\Psi_{c,d}(x,z,y) = x + c z + d y`:

```
blockStep_blockChainField             : blockStep (blockChainField c d) z y = c*z + d*y
blockChainDensity_blockChainField     : blockChainDensity (blockChainField c d) y = d*y
blockChainDensity_blockChainField_sq  : blockChainDensity (|blockChainField c d|^2) y
                                          = 1 + c^2 + d^2*y^2
blockChainCovariance_eq               : covariance = 1 + c^2
blockChainCovariance_small_field      : |c| ≤ 1 -> 1 ≤ covariance ≤ 2
```

The first step leaves the shell and exterior parts untouched; the second removes the shell
too. So the conditional mean after two steps is $`d y` alone: the interior coupling $`c` has
become invisible (`blockChainDensity_blockChainField_independent`), which is the
background-stability statement at this scale. The covariance tells the complementary story.
Each integrated direction contributes its unit variance, so the accumulated covariance is
$`1 + c^2` — independent of the exterior field $`y` and of the exterior coupling $`d`
(`blockChainCovariance_independent_of_background`), hence bounded by the explicit constant
$`2` under the small-field hypothesis $`|c| \le 1`. This is the C3b packet on the reference
system: an identity with an explicit constant, uniform in the background.

The small-field estimate the plan asks for is an _activity_ estimate in a norm, so the norm is
defined rather than implied, and the one estimate that a coarse step owes it is proved:

```
blockActivityNorm      f = ∫ |f| d (gamma ⊗ gamma)
blockChainActivityNorm f = ∫ |f| d blockChainLaw
integral_abs_partialIntegral_le   : ∫ |∫ f| ∂gamma ≤ ∫ |f| d (mu ⊗ gamma)
integral_abs_blockIntegral_le     : one step contracts blockActivityNorm
integral_abs_blockChainDensity_le : the chain contracts blockChainActivityNorm
```

The first line is the general statement, for a block coordinate carrying any probability
measure: a partial integral cannot increase the $`L^1` norm. That is the estimate a polymer
activity needs, and it is the honest content of "an activity estimate in an explicitly
defined norm" at this level — an $`L^1` contraction, not a polymer expansion.

# The Totals, and the Large-Field Complement

Integrating the two-step identities over the exterior field closes the bookkeeping and exposes
the regime the small-field packet does not cover:

```
integral_blockNaiveChainDensity          : ∫ naive = d^2
integral_blockChainDensity_sq            : ∫ coarse = 1 + c^2 + d^2
integral_blockChainDensity_eq_integral_naive_add
                                         : ∫ coarse = ∫ naive + (1 + c^2)
blockNaiveChainDensity_zero_background   : naive at y = 0 is 0
blockChainDensity_sq_zero_background     : coarse at y = 0 is 1 + c^2
```

The coarse total exceeds the naive one by exactly the constant that bounds the covariance
pointwise, and at zero background the naive density vanishes while the coarse one is
$`1 + c^2`. So the error of the naive prescription is _largest precisely where the background
is small_ — the regime the small-field packet addresses — and the complement of C3b therefore
has to be a statement in which the covariance is small _relative_ to the density it corrects:

```
blockChainCovariance_le_coupling_sq   : |c| ≤ M -> covariance ≤ 1 + M^2
blockChainCovariance_le_mul_density   : sqrt(2/eps) ≤ |d*y| -> covariance ≤ eps * coarse
```

The first line shows the covariance degrades only quadratically in the field strength, with no
exponential growth. The second is the C3c statement at this scale: wherever the exterior part
of the field dominates, the accumulated variance is at most the fraction $`\varepsilon` of the
coarse density, so with $`\varepsilon = 1` and $`|d y| \ge \sqrt 2` the correction is at most
half the total. That is what "large fields are easy, small fields are the work" means once the
covariance is a fixed constant rather than a field-dependent quantity.

# Arbitrarily Many Scales

The plan's C3d asks that the coupling trajectory "stay in the induction domain through
arbitrarily many UV scales". The reference system can be made scale-indexed, and then that
requirement — in the only form available here — is a theorem. The number of steps becomes a
parameter $`n`:

```
shellLaw n        = gamma^{⊗ n}  on  Fin n → ℝ
shellDensity n f y : the n-fold partial integral of f at fixed exterior value y
streamField c d n : Psi_n(z, g) = z + c * Psi_{n-1}(g),  exterior weight c^n * d
```

The field therefore carries the geometric weights of a rescaling by $`c` per scale, and the
exterior background is damped by $`c` at every step: the coupling runs, $`d \mapsto c d`. That is
the one coupling trajectory a product of independent Gaussians supports. Against it, the
density identity is a single induction with the quadratic invariant
$`A + B \Psi + C \Psi^2`:

```
shellDensity_quadratic : E_n[A + B Psi_n + C Psi_n^2] y
                           = A + B * (c^n * d * y) + C * (K_n + (c^n * d * y)^2)
shellDensity_streamField        : the running mean is c^n * d * y
shellDensity_streamField_sq     : the running second moment is K_n + (c^n d y)^2
shellDensity_streamField_covariance : second moment - mean^2 = K_n
```

The covariance after $`n` steps is $`K_n`, independent of the exterior field and of its
coupling, and it obeys the recursion

```
streamCovariance_succ        : K_{n+1} = 1 + c^2 * K_n
streamCovariance_closed_form : K_n = sum_{j<n} c^{2j}
streamCovariance_le_card     : c^2 ≤ 1 -> K_n ≤ n
streamCovariance_le_inv      : c^2 < 1 -> K_n ≤ 1/(1 - c^2)      -- uniformly in n
integral_shellDensity_streamField_sq : ∫ coarse = K_n + c^{2n} d^2
```

Each integrated Gaussian contributes exactly one unit of variance, so the accumulated covariance
is the geometric sum; it grows at most linearly in the number of scales, and if the per-scale
weight contracts ($`c^2 < 1`) it stays below the fixed constant $`1/(1-c^2)` for _every_
number of scales $`n`. That is the sense in which the small-field domain is preserved through
arbitrarily many scales: the bound does not degrade with the number of steps.

The recursion has a fixed point, and reading the statement that way is sharper than a uniform
bound. With $`c^2 < 1`$ the map $`K \mapsto 1 + c^2 K`$ has the unique fixed point
$`1/(1-c^2)`$, and the error after $`n`$ scales is exactly geometric:

```
streamCovariance_inv_sub  : K_n - 1/(1 - c^2) = - (c^2)^n / (1 - c^2)
streamCovariance_lt_inv   : c^2 < 1, c ≠ 0 -> K_n < 1/(1 - c^2)    -- strictly, at every n
tendsto_streamCovariance  : c^2 < 1 -> K_n -> 1/(1 - c^2)
tendsto_integral_shellDensity_streamField_sq
                          : the total K_n + c^{2n} d^2 tends to the same fixed point
```

So the accumulated covariance does not merely stay under a constant: it approaches the fixed
point from below at rate $`c^2`$ per scale, and the second summand of the total, $`c^{2n}d^2`$,
decays for the same reason. The uniform bound of the previous paragraph is the monotone half of
this statement; the convergence is what makes the domain statement quantitative rather than
merely uniform.

The two-step tower identity of the earlier section generalises, and the induction needs one
coordinate permutation rather than one per scale. The pointwise form pins the exterior value as
the *last* coordinate,

```
shellDensity_eq_integral_snoc : shellDensity n f y = ∫ g, f (Fin.snoc g y) ∂shellLaw n
```

and the induction splits the product law at its *first* coordinate —
`integral_shellLaw_cons_succ` at scale $`n + 1`, with `integral_shellLaw_cons` at the base —
peeling the coordinate the recursion peels. The permutation is the recentring
`piFinSuccAbove` at the last coordinate, performed once and reused at every scale; it is not a
Fubini shuffle of $`n`$ coordinates. The result is the tower identity at every scale:

```
integral_shellDensity_eq : ∫ y, shellDensity n f y ∂blockUnit = ∫ p, f p ∂shellLaw (n + 1)
```

for measurable bounded $`f`$, where `abs_shellDensity_le` and the `measurable_*` facts are what
the induction needs. This repairs a caveat the earlier section had to carry: the tower was proved
there only for two steps. It is now a theorem at every number of scales, and
`shellTail_eq_integral_snoc` reads the Chebyshev tail through it, so the tail bound is an
expectation over the reference law rather than a formal iterated integral.

That reading is what the large-field complement needs at $`n`$ scales, which is C3c in its
general-scale form:

```
shellDensity_nonneg          : f >= 0 -> shellDensity n f y >= 0
shellDensity_affine_field_le : density of {M <= |a (field - running mean) + b|}
                                 <= (a^2 K_n + b^2) / M^2
shellTail, shellTail_le      : the deviation tail at n scales is at most K_n / M^2
```

The affine form is one-step Chebyshev composed with the recursion: one more integrated scale
multiplies the coefficient $`a`$ by $`c`$ and adds a unit of variance, which is exactly
$`K_{n+1} = 1 + c^2 K_n`$. So the large-field region at any number of scales is controlled by the
same accumulated covariance the small-field packet bounds, and under $`c^2 < 1`$ the constant does
not grow with $`n`$. The estimate uses only $`K_n`$, so it is a second-moment bound, not a
bad-block entropy and not a polymer expansion, and $`M`$ is a threshold in the field's own units
rather than a normalised large-field region.

The tail bound is a statement about the *density* at fixed exterior value. Removing the damped
background from the field turns it into a statement about the law. The renormalised observable
subtracts the background read off the exterior coordinate, and its large set has a law-measure
that is an honest probability, uniformly bounded in the number of scales:

```
renormField                  : Ψ - c^n d (last coordinate)
shellTailLaw                 : (shellLaw (n+1)).real {p | M ≤ |renormField p|}
integral_shellTail_eq        : ∫ y, shellTail n c d y M = ∫ p, indicator ∂shellLaw (n+1)
shellTailLaw_le_inv          : c^2 < 1 -> shellTailLaw n c d M ≤ 1/((1 - c^2) M^2)
exists_shellTailLaw_le       : ε > 0 -> ∃ M > 0, ∀ n, shellTailLaw n c d M ≤ ε
```

The last line is **tightness**: one threshold works at every scale, which is the analytic premise
of Prokhorov's theorem for the sequence of laws of the renormalised observables. That is the
first rung of the observable limit estimate (C3e) and no more: Prokhorov's theorem itself, a
limiting law and any multi-point function are not proved here, and the renormalisation is the
subtraction of the background rather than of an interacting divergence.

The scalar sequence is not the only object that behaves this way. Replacing the renormalised
observable by an affine image of it keeps every step intact: the last coordinate still carries the
exterior value, so the iterated tail of an affine functional is the density the Chebyshev induction
already bounds, and the tower at its indicator moves the estimate to the law. What comes out is a
threshold that works at every scale for a whole affine family at once:

```
shellAffineLargeSet         : {p | M <= |a * renormField p + b|}
shellAffineTailLaw          : (shellLaw (n+1)).real (the affine large set)
integral_shellAffineTail_eq : integral of the density = law-level integral of the indicator
shellAffineTailLaw_le_inv   : c^2 < 1 -> tail <= (a^2/(1 - c^2) + b^2)/M^2
exists_shellAffineTailLaw_le: eps > 0 -> exists M > 0, forall n, tail <= eps
```

A shifted threshold is what a *centred* observable, or a difference of two observables, is written
in, and the price of the shift is the additive `b^2` in the numerator — which is the right scaling
for a second-moment estimate: doubling the shift quadruples the bound, and the number of scales
does not enter it at all. The scalar packet is the case `a = 1`, `b = 0`
(`shellAffineTailLaw_one_zero`), so this is a strict generalisation of it, and it shares its
ceiling: the estimate is a probability statement about an *indicator*, so no expectation, variance
or covariance of an affine image is computed. Those need the `L^1` extension of the tower named in
the qualification below.

Two honest qualifications belong here rather than in a footnote. First, the flow is a
_weight_, not a renormalisation: `streamField` multiplies by `c`, the law is still a product of
fresh independent Gaussians, and $`d \mapsto c d` is a definition, not a theorem about an
effective action. Second, `shellDensity` is defined as the $`n`-fold iterated integral, and the
*tower identity* $`\int f \,d\gamma^{\otimes (n+1)} = \int y, \mathrm{shellDensity}_n f y`
is proved at every scale above, but only for measurable *bounded* observables — the induction's
boundedness input is `abs_shellDensity_le`. Nothing here is a theory of the iterated integrals in
$`L^1`$, and the density is still *defined* as an iterated partial integral rather than derived
from a conditional expectation on a sigma-field. Nothing here is C3d in the plan's sense — there
is no effective action, counterterm, marginal direction or logarithmic running, and the
$`n`-uniformity is exactly what the triviality of the reference flow buys.

# What Is Verified, and What Is Open

Four honest boundaries delimit this chapter.

*First, the calibration is a covariance statement, not an identification of laws.* The
scalar regulator's moments are not the Mehler path measure; no field law, transfer operator
or interacting dynamics is constructed. The mass is the free mass that reproduces the ratio
$`B/A`, not the physical cutoff mass.

*Second, "reflection positivity at the regulator" has two forms, and only one of them is
general.* The Hilbert-space identity $`\langle \theta F, F\rangle = \|\cdot\|^2` for bounded
observables and their words holds for any self-adjoint generator. The *interacting* half-space
inequality $`\langle \theta F, F\rangle_{\mathrm{int}} \ge 0` holds here for the interactions whose
weight factorizes across the reflection plane, $`\rho = g_1 g_2` with a bounded positive-time
weight $`g` — where it is a consequence of the free statement, not an approximation to it.
An unbounded $`V_+`$ is covered only when it expands as a convergent series of
factorized weights — a mixture class, not a general interaction. That is not a gap to be closed by
more work on this mechanism: reflection positivity is a positivity condition on the reflected
kernel, not a consequence of reflection invariance, and a general density demonstrably fails it
and that failure is itself a theorem of the module, not a remark. For any probability `μ₀` and any
measurable `h` with $`|h| \le 1`$, $`\int h = 0`$ and $`\int h^2 = 1`$, and any
$`0 < \epsilon < 1`$,

```
BookProof.OSReconstruction.generalWeight_pos      : 0 < 1 - ε h z₁ h z₂
BookProof.OSReconstruction.generalWeight_swap     : reflection invariance
BookProof.OSReconstruction.generalWeight_osForm   : ⟨θh, h⟩_ρ = -ε
BookProof.OSReconstruction.not_reflectionPositive_of_generalWeight :
  ∃ W, (∀ z, 0 < W z) ∧ (∀ z, W (z.2, z.1) = W z) ∧ ∫ h z.2 h z.1 W z d(μ₀ ⊗ μ₀) < 0
```

The sign is the whole story: `1 + ε h₁h₂` has OS form `+ε`, and that sign is the coefficient of the
rank-one term. So the general case is false rather than open, and what a general `V` needs is a
*positivity structure* — $`V = V_+ + \theta V_+`$, a decomposition into individually
reflection-positive terms, or a convergent expansion in a stable regime — not more work on this
mechanism. The $`L^2`$ question splits, and both halves are now settled at the level of the form:
for the free covariant state the finiteness is *derived*, not assumed, from the single hypothesis
$`H(\cdot + \cdot) \in L^2(\nu \otimes \gamma)`$ (`covState_reflectionPositive_of_memLp`, resting
on the two marginal projections), and the interacting state inherits it verbatim -- `intState` is
the free state reweighted by the product $`g z_1 g z_2`$, so the weight rides along with the
observable and `intState_reflectionPositive_of_memLp` derives the weighted form's finiteness from
$`g F \in L^2(\nu \otimes \gamma)`$. What is not proved is whether that condition holds for the
interactions of C2/E3, and the closure of the positive-time algebra (completing the pre-Hilbert
space, and multiplying two $`L^2`$ families).
Separated-time *diagonal* positivity $`\langle A^\dagger e^{-hK} A\rangle \ge 0` at $`h > 0` is
likewise not claimed: it needs a positive (spectral) evolution, a hypothesis this slice does not
establish. The unbounded generator $`h_\sigma`, its closure and its selection, the field-law
representation, and the positivity-preserving semigroup with a ground function all remain open.
Nothing here is evidence that an interaction survives cutoff removal.

_Third, the reconstruction is a pre-Hilbert space, not a Hilbert space._
The positivity-preserving form is built from bounded observables and
a bounded `K`; the quotient by null families is realized isometrically inside the regulator
space but is neither completed nor given its own type, and Cauchy–Schwarz is derived from the
explicit norm identity rather than from abstract form theory. The OS inequality proved is the
finite-family one; the interacting version is the factorized-weight one above, and the
completeness of the reconstructed space and any field law are outside this chapter.

_Fourth, the coarse-graining step is one, two or arbitrarily many blocks of a reference
Gaussian._ The chain iterates the operation and, once indexed by $`n`, the number of scales
— but every coordinate remains a fresh independent Gaussian, so nothing is renormalised
between steps, the per-scale weight is put in by hand, and neither the chain nor the indexed
family is an RG map. There is no measure-level pushforward, no gauge transport and no
lattice. `blockIntegral_mul_exterior` is the characterising identity of the conditional
expectation on cylinder test functions rather than a construction of conditional
expectations, and `coarseDensity_ne_naiveDensity` shows the two prescriptions differ in this
one system without giving a lower bound for interacting or gauge theories. The C3b packet is
correspondingly narrow: `blockChainCovariance_small_field` is an exact identity with an
explicit constant, not an elliptic or derivative estimate for an interacting measure, and
`integral_abs_blockChainDensity_le` is $`L^1` contraction, not a polymer expansion with a
summable activity ledger. The C3c complement here is not a large-field theory either:
`blockChainCovariance_le_mul_density` says the _fixed_ covariance is relatively negligible
where the background is large; it does not bound a fluctuation covariance, control a bad-block
region or prove a summable tail, and `blockChainCovariance_le_coupling_sq` is a quadratic bound
in the coupling, not a large-field expansion. Running couplings (C3d) and the observable limit
estimate (C3e) remain open.

Everything proved in this chapter is `sorry`-free, and every declaration listed above
depends only on Lean's standard `propext`, `Classical.choice` and `Quot.sound`
(`Work/EuclideanMomentAudit.lean`, 195 declarations).
