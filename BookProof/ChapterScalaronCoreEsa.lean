import BookProof.ChapterScalaronCoreEsa.Part1
import BookProof.ChapterScalaronCoreEsa.Part2

/-!
# The scalaron sector: essential self-adjointness with an exponentially growing potential

Plan item **A5** (`CONSOLIDATED_PLAN.md` §10.5), the step that the Starobinsky wave left
open at the *continuum* level: the Einstein-frame scalaron potential

`V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²`

is **not** of temperate growth — it grows exponentially as `φ → −∞`, so the
multiplication-operator theorem of `BookProof.ChapterWaveUnboundedPotential`
(`potentialOp_essentiallySelfAdjoint`, stated for potentials of temperate growth on the
Schwartz core) does not apply to it.  This module removes that restriction.

## The point

Temperate growth is needed only to make the *Schwartz* core invariant.  On the smaller —
and still dense — core of **smooth compactly supported** functions no growth hypothesis is
needed at all: multiplication by any smooth real function maps the core into itself, and the
deficiency argument of `ChapterWaveUnboundedPotential` (divide a test bump `χ` by the
nowhere-vanishing smooth function `W − z̄`) stays inside the core.  What survives of the
analytic hypotheses is only what the plan records: *the operator must be defined on a dense
core*, and for the combination with the kinetic term the potential must be *bounded below*
— and the Starobinsky potential is bounded below in the strongest way, being a square.

## What is proved

**1. The compactly supported smooth core.**  `ccDomain E` is the image in `L²(E)` of the
smooth compactly supported functions, `ccDomain_dense` its density, and
`ccDomain_le_schwartzDomain` the inclusion in the Schwartz core.

**2. Multiplication by an arbitrary smooth potential.**  `opCc W hW` is multiplication by a
real `W`, assumed *only* smooth: `smoothPotential_symmetric`,
`smoothPotential_deficiencyTrivial` (at every non-real `z`) and
`smoothPotential_essentiallySelfAdjoint`.  No growth, no boundedness and no semiboundedness
hypothesis.

**3. The scalaron potential.**  `contDiff_starobinskyV`; `starobinskyV_not_hasTemperateGrowth`
— the potential genuinely falls outside the temperate class, so item 2 is needed;
`starobinskyV_essentiallySelfAdjoint` — and it is nevertheless essentially self-adjoint on
the compactly supported core, as is the full `V₃(R_c) + V(φ)` potential of the gauge-fixed
`R + αR²` Hamiltonian (`scalaronFullPotential_essentiallySelfAdjoint`), which is moreover
bounded below by `−M⁴/(16α)` (`scalaronFullPotential_ge`).

**4. The d'Alembertian with the scalaron potential.**  `wave_add_scalaron_symmetric` — the
gauge-fixed Hamiltonian `□ + V` is a well-defined symmetric operator on the dense compactly
supported core, and `wave_add_smoothTruncatedPotential_essentiallySelfAdjoint` — every
localization of it is essentially self-adjoint on the Schwartz core, again with smoothness
as the only hypothesis on the potential (`wave_add_scalaronTruncated_esa` for the scalaron
potential itself).  This is the exponential-growth analogue of
`wave_add_truncatedPotential_essentiallySelfAdjoint`.

**5. The full mode Hamiltonian with the scalaron sector, and its flow.**  At the mode level
the gravity fiber operator is multiplication by `(1/16)a_k² − (1/24)b_k² + V₃(R_c k) +
V(φ_k)`: `qgScalaronMode_esa` (essential self-adjointness on the dense maximal domain),
`qgScalaronMode_potential_ge` (the uniform lower bound `−M⁴/(16α)`, unaffected by the
non-negative scalaron term) and **`qgScalaron_stone_flow`** — the complete unitary group of
the `R + αR²` Hamiltonian *including* the scalaron potential.

## Honest boundary

Unchanged from `CONSOLIDATED_PLAN.md` §10.3/§10.5: the continuum `L²(ℝ⁸⁴)` essential
self-adjointness of the *sum* `□ + V` still needs the Strichartz finite-speed / gluing
input, which is not claimed here.  What this module settles is the point at issue for the
scalaron: the exponential wall is not an obstruction — the potential term is essentially
self-adjoint on a dense core with no growth hypothesis, every localization of the sum is
essentially self-adjoint, and the potential has the correct (bounded below) sign.
-/
