import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Real Scalar Field: Continuous-Momentum lambda phi^4" =>
%%%
tag := "lambda4-sector"
%%%

# Orientation: One Scalar Field, Fully Continuous

:::paragraph
This chapter is the scalar entry of the final-Hamiltonian convention. The object is
a single real scalar field in the continuum: the coordinates of
$`L^2(\mathbb{R}^3_k \times \mathbb{R}_\varphi)` are $`(\varphi, k_1, k_2, k_3)`,
all continuous. Only $`\varphi` carries a conjugate momentum. The gradient term is
the diagonal momentum multiplier $`\tfrac12 |k|^2 \varphi^2`, integrated over
$`k`, so there is no discrete momentum sum, no spatial lattice, and no
spatial-derivative jet constraint. What is discrete is only the SIRK Krylov window
in which finite matrices are read off.
:::

:::paragraph
The one-particle Hamiltonian is

$$`h = \tfrac12 p_\varphi^2
     + \tfrac12 (k_1^2 + k_2^2 + k_3^2)\,\varphi^2
     + \tfrac{\lambda}{4}\,(\varphi^2 - v^2)^2 .`

The double-well wall lives in $`\varphi`; the three momenta enter only as
multipliers. The two-second-quantization operations of the
{ref "second-quantization-esa"}[second-quantization chapter] then act on
$`h`: the outer Hamiltonian is $`d\Gamma(h)`, creation on the left and
annihilation on the right, so every particle-number sector is preserved.
:::

| Claim | Formal status |
| :--- | :--- |
| inner Hamiltonian on the Gauss polynomial core | defined (`momContModel`), symmetric, positive |
| unconditional one-particle gap | proved: $`7/64` (`unitMomCont_inner_gap`) |
| unique outer vacuum ground state | proved (`vacuum_ground`) |
| continuous gradient and composite-pair Fourier identities | proved for Schwartz data |
| rank-one return loss | proved: mean $`17/8`, defect $`553/32` |
| rank-two $`S_3` certificate | proved in the kernel from rational data |
| two-sided return interval at $`t = 1/100` | proved: $`[319447/320000,\ 39999/40000]` |
| shift law $`d\Gamma(h + c) = d\Gamma(h) + c N_{\rm out}` | proved (`outerHam_add_const`) |
| one-particle outer sector | proved: acts as $`h` (`outerHam_oneParticle_eq`) |
| absolute edge of the interacting continuum operator | _not claimed_ |

# The Gap and the Outer Vacuum

:::paragraph
The analytic input is an uncertainty identity. For the Gaussian core the
position and momentum representatives satisfy, for every $`\alpha > 0`,

$$`\tfrac{\alpha}{2}\|\psi\|^2
   \le \tfrac12\bigl(\|P_j\psi\|^2 + \alpha^2\|X_j\psi\|^2\bigr),`

so the harmonic part of the wall alone bounds the quadratic form below. The
double-well minimum then contributes a positive constant, giving the uniform
bound
:::

```
#check @BookProof.Phi4.unitMomCont_inner_gap
```

:::paragraph
The bound is unconditional: it is a statement about the polynomial core, not a
numerical enclosure and not a hypothesis. Lifting it, the completed outer
Hamiltonian has a ground state — the vacuum is a unit vector, the closure
annihilates it, and the quadratic form is nonnegative everywhere:
:::

```
#check @BookProof.Phi4.Model.vacuum_ground
```

:::paragraph
Two $`\mathbb{Z}_2` facts accompany the gap and are proved separately: the field
reflection $`\varphi \mapsto -\varphi` and the spatial parity
$`k \mapsto -k` are superselection symmetries of the inner operator, so the
sectors they define are preserved rather than mixed.
:::

# Continuous Fourier Identities

:::paragraph
The gradient term is a statement about the Fourier transform, and it is proved
for Schwartz functions on a finite-dimensional real inner-product space. A
directional derivative becomes multiplication by $`2\pi i \langle k, m\rangle`,
so the squared gradient is diagonal multiplication by the square of that symbol:
:::

```
#check @BookProof.Phi4.fourier_grad_sq_identity
```

:::paragraph
The quartic composite is the other half. The transform of the pointwise square
is the convolution of the field with itself, and the transform of the fourth
power is the convolution integral over the continuous momentum space:
:::

```
#check @BookProof.Phi4.psiField_eq_fourier_mul
#check @BookProof.Phi4.fourier_phi4_composite_integral
```

:::paragraph
These are the identities behind "no derivative convolutions": the potential is
evaluated pointwise, and only the *composite pair* is integrated. Nothing here
introduces a jet coordinate or a discrete momentum sum.
:::

# The Rank-One Return

:::paragraph
The first finite diagnostic is a single Gaussian seed. On it the inner
Hamiltonian is close to a scalar multiple of the identity, and the residual is
computed exactly: the mean is $`17/8` and the squared defect is
$`553/32` times the seed norm.
:::

```
#check @BookProof.Phi4.unitMomCont_defect_norm_sq
#check @BookProof.Phi4.unitMomCont_rankOne_error
```

:::paragraph
Squaring the error avoids a square root normalization on the Gaussian. The
consequence is a quantitative return probability: after time $`t` the overlap
with the initial seed loses at most $`(553/32)\,t^2` of its squared mass.
:::

```
#check @BookProof.Phi4.unitMomCont_return_probability
```

# The Exact Rank-Two Certificate

:::paragraph
The second diagnostic is the exact $`S_3`-symmetric rank-two window. Eleven
rows record the polynomial action of the unit inner Hamiltonian on the symmetric
modes in the unnormalized product-Hermite basis, with the Hermite Gram weights
carried alongside. The matrices are rational and are transcribed from the
recorded numerical fixture; every finite identity is checked in the kernel, so no
floating-point value enters the certificate. The window retains the reversed
modes and the generator is real-symmetric in the Gram form:
:::

```
#check @BookProof.Phi4.MomRankTwo.window_hermitian
#check @BookProof.Phi4.MomRankTwo.defect_split
```

:::paragraph
The certificate's content is a *separation of two error sources*: the part of
the defect inside the retained window and the part outside it are bounded
separately, so a shifted-solve comparison and a truncation comparison cannot be
confused with one another.
:::

# The Two-Sided Return Interval

:::paragraph
Combining the rational transport of the certificate to $`\mathbb{C}` with the
mechanical identity of the Mehler evolution — speed and acceleration bounds, and
the transverse Gram inequality — gives a two-sided enclosure at a fixed time.
Both endpoints are rational, and the estimate needs no numerical input:
:::

```
#check @BookProof.Phi4.unitMomCont_return_interval
```

:::paragraph
At $`t = 1/100` the squared return lies in
$`[319447/320000,\ 39999/40000]`, i.e. between $`0.99827` and $`0.99998` of the
seed mass. This is a finite-horizon, finite-window statement: it certifies the
orbit of the recorded model at one time, not a continuum spectral edge.
:::

# Operations on the Outer Sector

:::paragraph
Two structural facts about $`d\Gamma` are proved for an *arbitrary* one-particle
operator and then specialized to the scalar model. The first is the shift law:
second quantization is affine along $`A \mapsto A + c\,\mathbf{1}`, and the
increment is $`c` times the outer number operator $`N_{\rm out}`, which acts on
the $`n`-particle sector as multiplication by $`n`.
:::

```
#check @BookProof.Phi4.Model.outerHam_add_const
```

:::paragraph
The second is the one-particle identification: in degree one the outer
Hamiltonian acts exactly as the inner Hamiltonian. Together with the gap, this
is what makes the outer vacuum the unique ground state of the scalar enclosure.
:::

```
#check @BookProof.Phi4.Model.outerHam_oneParticle_eq
```

:::paragraph
The proofs are purely algebraic in the sector derivation: additivity and
homogeneity of the derivation in the one-particle operator, the derivation of the
inclusion being the particle number, and then the specialization. The module
contains no axiom and no `sorry`.
:::

# What This Chapter Does Not Claim

:::paragraph
Three boundaries are recorded rather than glossed over. First, the periodic
lattice models and the static-jet model are *frozen comparisons*: they are not
this object, and no theorem about them transfers to the continuum by itself.
Second, the SIRK window, the rank-two certificate and the return interval are
finite-dimensional statements about the recorded model at fixed data; they do not
by themselves supply the absolute one-particle edge of the interacting continuum
operator, which remains the analytic input named in the
{ref "free-field"}[free-field chapter]. Third, the Rust solver's SIRK sweeps are
numerical evidence and replay records, not Lean theorems; the Lean content is
exactly the declarations cited above.
:::

:::paragraph
Read this chapter as the scalar mirror of
{ref "ns-one-particle-hamiltonian"}[the Navier–Stokes one-particle chapter] and
of {ref "qg-elimination"}[the quantum-gravity elimination chapter]: the same
enclosure $`d\Gamma(h)`, the same honest split between what the finite certificate
proves and what the continuum operator still needs.
:::
