import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Cosmological Amplification of the Matter/Radiation Ratio" =>
%%%
tag := "baryon-asymmetry"
%%%

# A Small Asymmetry, Amplified

In its chapter on entropy and irreversible time-evolution, the manuscript turns to
*baryon asymmetry*: why the observable universe contains matter but almost no
antimatter. The physical argument is that a tiny CP-violating asymmetry in the early
universe is "much amplified by the expansion of the Universe." This chapter isolates
the clean, self-contained mathematical core of that amplification: the classical
Friedmann–Robertson–Walker (FRW) scaling of perfect-fluid energy densities, and the
fact that the *matter-to-radiation ratio grows in proportion to the scale of the
Universe*.

# FRW Scaling of the Densities

Let $`a > 0` be the cosmological *scale factor* (the relative size of the
Universe). A perfect fluid with equation-of-state parameter $`w` has an energy
density that dilutes as the Universe expands. Matter (pressureless dust,
$`w = 0`) dilutes as the volume, $`a^3`; radiation ($`w = 1/3`) dilutes one power
faster, $`a^4`, because each photon is additionally redshifted. Concretely, from
present-day reference densities $`\rho_{m0}, \rho_{r0}`:

$$`\rho_m(a) = \frac{\rho_{m0}}{a^3}, \qquad \rho_r(a) = \frac{\rho_{r0}}{a^4}.`

These power laws are not arbitrary: they are *forced* by the FRW continuity
equation

$$`a\,\rho'(a) + 3(1+w)\,\rho(a) = 0,`

whose solution is $`\rho \propto a^{-3(1+w)}`, giving the exponents $`3` (matter)
and $`4` (radiation). The verified computation (a genuine derivative calculation):

```
#check @ChapterBaryonAsymmetry.matter_satisfies_continuity
#check @ChapterBaryonAsymmetry.radiation_satisfies_continuity
```

# The Ratio Grows Like the Scale Factor

The matter-to-radiation *ratio* is therefore

$$`\frac{\rho_m(a)}{\rho_r(a)} = \frac{\rho_{m0}/a^3}{\rho_{r0}/a^4} = \frac{\rho_{m0}}{\rho_{r0}}\, a.`

The $`a^3` dilution common to both cancels, leaving a single factor of $`a`:

```
#check @ChapterBaryonAsymmetry.matterRadiationRatio_eq
```

So the ratio is *proportional to the scale of the Universe*, exactly as the
manuscript states. It is strictly increasing in $`a`, and it diverges:

```
#check @ChapterBaryonAsymmetry.matterRadiationRatio_strictMonoOn
#check @ChapterBaryonAsymmetry.matterRadiationRatio_tendsto_atTop
```

The last is the headline: as $`a \to +\infty`, the matter/radiation ratio tends to
$`+\infty`. This is the precise sense in which the expansion "amplifies" the matter
content relative to radiation.

# How This Amplifies a Small Asymmetry

The physical conclusion the manuscript draws is now transparent. Suppose the early
universe has a tiny excess of matter over antimatter (a small CP asymmetry). As the
universe expands, the matter/radiation ratio grows *linearly in the scale factor*
and without bound. A small initial imbalance in the matter sector is therefore
magnified by the enormous growth of $`a` between the early universe and today. The
mathematics does not by itself explain the _origin_ of the asymmetry (that is the
role of CP violation); it explains why a small asymmetry, once present, becomes the
dominant, observable matter content — the expansion of the Universe does the
amplifying.

# The Same Scaling Is Checked in the Numerical Validation

The power laws above are not an isolated curiosity of this chapter: they are the
same Friedmann–Robertson–Walker content that the companion numerical validation
checks against published cosmology. For a flat FLRW universe the two scalars that
appear throughout the gravity thread — the Ricci scalar
$`R = 6(\dot H + H^2)` and the TEGR torsion scalar $`T = -6H^2` — are built
from the same $`H = \dot a/a` and $`\dot H` that enter the continuity equation
$`a\,\rho'(a) + 3(1+w)\rho(a) = 0` derived above (with matter, $`w=0`,
giving $`\rho \propto a^{-3}`). The numerical suite verifies both scalars, that
they give the same Friedmann equation $`3H^2 = 8\pi G\rho` (the
TEGR–GR equivalence, $`eR = e\cdot T + \text{divergence}`), and that their sum
reproduces the divergence term — the same $`R + T = 6\dot H` identity that makes
$`R = 6(\dot H + H^2)` and $`T = -6H^2` consistent. So the amplification
computed here and the equivalence checked there rest on the same FLRW scalars; the
cosmological content of the manuscript is verified both symbolically (this
chapter) and numerically (the companion solver work).

# A Caution: Amplification Is Not Explanation of the Origin

It is worth keeping the two claims separate. What is proved here — and what the
manuscript's argument needs — is that *if* a small asymmetry exists, the
expansion amplifies it proportionally to $`a`. That is a clean, verified
statement about FRW kinematics. What is *not* supplied by this chapter is the
origin of the asymmetry itself: the manuscript turns to CP violation in the
Standard Model for that, and notes that the Standard Model's CP asymmetry may be
too small to match observation unless the age of the Universe is larger than
standard cosmology provides — an inconsistency the manuscript reads as a problem
for the cosmology model rather than for the Standard Model. The verified content
stops at the amplification; the origin story is physics beyond it.
