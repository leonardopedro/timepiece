import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Constants Suite: g-2, Lamb Shift, Positronium, Blackbody" =>
%%%
tag := "constants-suite"
%%%

# Why These Four Numbers

:::paragraph
Every quantum field theory must eventually answer to the laboratory. Four
numbers have historically served as the touchstones of quantum
electrodynamics: the anomalous magnetic moment of the electron (the
$`g-2`$ measurement), the Lamb shift between the $`2S_{1/2}`$ and
$`2P_{1/2}`$ levels of hydrogen, the fine-structure spectroscopy of
positronium, and the blackbody radiation spectrum. Each one is a place
where the formalism leaves the safety of exact symmetries and must produce
a *number* that experiment can check.
:::

:::paragraph
This chapter is an honesty page. The verified layer of this book contains
the machinery that such a suite of computations would be built on — thermal
statistics, the harmonic-oscillator spectrum, certified spectral bands —
but it does not yet contain the radiative-correction calculations
themselves. Where a claim is not yet proved in `BookProof`, we say so
explicitly, and we show what instruments exist that a specialist would use
to close the gap.
:::

# The Blackbody Spectrum: Thermal Statistics

:::paragraph
The blackbody spectrum is the oldest of the four touchstones — it is where
quantum theory was born. Planck's law rests on two facts: the mean
occupation of a bosonic mode at energy $`\hbar\omega`$ above the ground
state follows the Bose–Einstein distribution, and the ground state itself
carries the zero-point energy $`\tfrac12\hbar\omega`$. Both facts are
proved in the verified layer.
:::

:::paragraph
The Bose–Einstein distribution is defined as
$`\bar{n}(x) = 1/(e^{x} - 1)`$, and the verified layer proves its
positivity, its strict monotone decrease, and — crucially — that the
thermal occupation computed from it equals the mean of the geometric
distribution that the thermal state assigns to number eigenstates. The
temperature identity $`\tau = \bar{n} + \tfrac12`$ then connects the
mean occupation to the observable energy including the zero-point half:
:::

```
#check @BookProof.ChapterBoseEinstein.boseEinstein
#check @BookProof.ChapterBoseEinstein.boseEinstein_mean
#check @BookProof.ChapterBoseEinstein.thermalTemperature_boseEinstein_eq_coth
#check @BookProof.ChapterCoherentTemperature.thermalProb_mean
#check @BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half
#check @BookProof.ChapterCoherentTemperature.thermalTemperature_vacuum
#check @BookProof.ChapterCoherentOccupation.thermalOccupation_energy
#check @BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation
```

:::paragraph
The zero-point half is not a cosmetic addition: it is the fingerprint of
the canonical commutation relations, and it is what makes the blackbody
spectrum *universal* — independent of the particular cavity. The verified
layer also proves that the thermal distribution maximizes entropy among
all distributions with the same mean occupation, which is the statistical
mechanics statement behind "the radiation is thermal because it is in
equilibrium":
:::

```
#check @BookProof.ChapterThermalMaxEntropy.thermalEntropy_eq
#check @BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy
```

:::paragraph
What is *not* yet proved is the final assembly: the spectral energy
density $`u(\omega, T) = \frac{\hbar\omega^3}{\pi^2 c^3}`$
$`\cdot \frac{1}{e^{\hbar\omega/kT} - 1}`$ requires integrating the mode
occupation against the density of states in a three-dimensional cavity.
The per-mode statistics are verified; the continuum mode sum is specialist
work.
:::

# The Oscillator Spectrum: The Bridge to Bound States

:::paragraph
Three of the four touchstones — the Lamb shift, positronium, and $`g-2`$
at its core — are ultimately questions about the *spectrum* of a
self-adjoint operator. The simplest nontrivial spectrum in the verified
layer is the harmonic oscillator: on the Hermite core of $`L^2(\mathbb{R})`$,
the operator $`-d^2/dx^2 + x^2/4`$ acts diagonally on the Hermite
functions, with eigenvalues $`n + \tfrac12`$. This is proved exactly, not
perturbatively:
:::

```
#check @BookProof.HermiteStrichartzQG.oscillatorSymbol
#check @BookProof.HermiteStrichartzQG.oscillator_eigenfunction
#check @BookProof.HermiteStrichartzQG.oscillatorOp_hermiteLp
#check @BookProof.HermiteStrichartzQG.oscillator_essentiallySelfAdjoint_on_hermiteCore
```

:::paragraph
The importance of this result for the constants suite is structural. The
oscillator spectrum is the exactly-solvable backbone against which every
perturbative correction is measured: the Lamb shift is a correction to a
Coulomb bound state computed in an oscillator-like basis, positronium's
fine structure is a relativistic correction to a hydrogenic spectrum, and
the leading term of $`g-2`$ is a magnetic-moment coupling whose
nonrelativistic limit is an oscillator problem. Essential
self-adjointness on the Hermite core guarantees that the spectrum is a
well-defined observable — there is a unique self-adjoint operator whose
eigenvalues the perturbation theory is correcting.
:::

# Positronium: The Two-Body Touchstone

:::paragraph
Positronium — the bound state of an electron and a positron — is the
cleanest two-body touchstone in QED: no hadronic baggage, no
renormalization of composite structure, pure leptons bound by the Coulomb
attraction. Its spectroscopy (the $`1S \to 2S`$ interval, the fine
structure, the lifetime split between para- and ortho-positronium) is a
precision test of the two-body Dirac equation and its radiative
corrections.
:::

:::paragraph
The verified layer contains the *algebraic* half of the positronium story:
the fermionic CAR algebra that distinguishes the two-body fermion pair from
a bosonic mode (the Jordan–Wigner two-mode anticommutation that underlies
the spin–statistics dichotomy), the parity classification of the Dirac mass
Hamiltonian (which mass term breaks parity and which conserves it — the
concrete, decidable core of the CPT discussion), and the relativistic
dispersion relation that fixes the two-body spectrum's kinematic backbone.
What these theorems fix is *which* states can exist and *which* terms
conserve parity; the decay *rates* are radiative-correction computations
that remain open:
:::

```
#check @BookProof.SpinStatistics.fermi_CAR_cross
#check @BookProof.SpinStatistics.fermiAnticomm_annih
#check @BookProof.ChapterCPTParity.parity_diracHamOp
#check @BookProof.ChapterCPTParity.parity_diracHamOp_invariant
#check @BookProof.ChapterCPTHamiltonian.diracHamOp_sq
```

:::paragraph
The honest boundary: the verified layer proves the algebraic selection
rules — the anticommuting two-fermion Fock space, the parity-even/odd
classification of every Dirac mass term, and the exact mass-shell
relation. It does not yet compute the decay rates
$`\tau_p \approx 1.25 \times 10^{-10}`$ s and
$`\tau_o \approx 1.42 \times 10^{-7}`$ s — those require the full QED
vertex calculus, which is not formalized.
:::

# The Lamb Shift and g-2: Radiative Corrections

:::paragraph
The Lamb shift and the anomalous magnetic moment are the two classic
radiative-correction touchstones. Both are *zero* in the Dirac theory and
*nonzero* only because of the quantized electromagnetic field: the Lamb
shift is the self-energy of a bound electron interacting with vacuum
fluctuations, and $`g-2`$ is the vertex correction to the
electron–photon coupling. The one-loop answers —
$`\Delta E_{2S-2P} \approx 1058`$ MHz and
$`a_e = \frac{\alpha}{2\pi} \approx 0.00116`$ — are among the most
precisely confirmed predictions in physics.
:::

:::paragraph
These are the hardest targets in the suite, and the verified layer does
not yet contain them. What it *does* contain is the certification
machinery that any such computation would feed into. The verified layer's
philosophy for numerical claims is: a number becomes a proof only when it
arrives wrapped in a certified enclosure. The Temple-certificate layer
proves exactly this: from a computed trial vector with its Rayleigh
quotient and residual, plus an *a priori* spectral separation, one obtains
a rigorous band containing the true eigenvalue — and the certificate
layer shows that without the separation hypothesis, no lower bound is
possible at all:
:::

```
#check @BookProof.RitzCertificate.temple_lower_bound
#check @BookProof.RitzCertificate.temple_band_mem
#check @BookProof.RitzCertificate.fock_mass_gap_of_temple_certificates
#check @BookProof.TempleSeparationNecessary.separation_necessary
```

:::paragraph
The same discipline is expressed in the gap-certificate structure: a
certificate is a pair of numbers (measured value, assembled width) and the
theorem consumes *only* those two numbers, proving a rigorous lower bound
from them and nothing more. The recorded $`g=2, m=4`$ fixture carries a
certified lower bound of $`1.932`$ — a statement about a finite
truncation, never claimed as a continuum result:
:::

```
#check @BookProof.SirkCertifiedGap.GapCertificate
#check @BookProof.SirkCertifiedGap.gap_ge_of_certificate
#check @BookProof.SirkCertifiedGap.qcdG2M4
#check @BookProof.SirkCertifiedGap.qcdG2M4_lower
```

:::paragraph
The route from here to the Lamb shift and $`g-2`$ is clear but long: one
would need (1) the free Dirac spectrum on a Coulomb background as the
exactly-solvable backbone, (2) the one-loop self-energy and vertex
integrals as certified numerical enclosures, and (3) the composition of
those enclosures through the band machinery above. Each step is a
specialist work package in the style of the mass-gap programme.
:::

# What Is Verified, and What Is Open

:::paragraph
The exactly-verified thermal statistics of bosonic modes (Bose–Einstein
distribution, mean occupation, zero-point energy, entropy maximality), the
exact harmonic-oscillator spectrum with essential self-adjointness on the
Hermite core, the symmetry selection rules for positronium decay channels,
and the complete certificate machinery for turning numerical output into
rigorous spectral enclosures.
:::

:::paragraph
Deliberately left open is the continuum mode-sum assembly of the Planck spectrum; the
two-body Coulomb bound-state spectrum and its relativistic corrections;
the one-loop self-energy and vertex integrals; and the final numbers
themselves — the Lamb shift in MHz, $`a_e`$ as a series in
$`\alpha`$, the positronium lifetimes. These are quarantined here and in
{ref "proof-plans"}[the appendix], in keeping with the book's rule:
nothing enters the verified layer without a proof.
:::
