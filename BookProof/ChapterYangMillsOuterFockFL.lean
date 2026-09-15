import BookProof.ChapterYangMillsOuterFockFL.Part1
import BookProof.ChapterYangMillsOuterFockFL.Part2

/-!
# The gauge-fixed Yang–Mills Hamiltonian on the outer Fock space, by Faris–Lavine

This module does for Yang–Mills what `BookProof.ChapterNsOuterFockFarisLavine` does for
Navier–Stokes and `BookProof.ChapterQgOuterFockFullFL` for quantum gravity: it puts the 3D
gauge-fixed Yang–Mills Hamiltonian on the outer Fock space `⊕ₙ L²(ℝ^{99n})` and proves it
essentially self-adjoint there **by the Faris–Lavine criterion**, against the lifted
Friedrichs extension of the positive one-particle operator `N₁ = −Δ + ‖x‖²/4`.

## The one-particle statement, re-routed through Faris–Lavine

`BookProof.YangMillsAbelianEsa.ymAbelian_essentiallySelfAdjointOn_core` proves essential
self-adjointness of the one-particle Hamiltonian by the *Carleman* route.  That route does
not lift to the Fock space.  `ymAbelian_eq_sqSumOp` identifies the same Hamiltonian as a
kinetic-plus-squares operator `½ Σ_j κ_j π_j² + ½ Σ_m B_m²` and
`ymAbelian_esa_farisLavine` re-proves essential self-adjointness through
`BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine` — that is, through Theorem 1 of
Faris–Lavine with a Friedrichs comparison operator and a commutator bound, the only data
that survive second quantization.

## The parcel model

An excitation ("parcel") carries the `99 = 3 + 24 + 72` field-space coordinates of
`BookProof.ChapterYangMillsHermite`: the three spatial coordinates, the `24` gauge fields
`A_{j,a}` and the `72` **independent derivative coordinates** `∂_j A_{k,a}`.  The `n`-parcel
sector is `L²(ℝ^{99n})` and the state space is the outer Fock space `⊕ₙ L²(ℝ^{99n})`.

For every parcel `p` the Hamiltonian carries three families of squared linear forms:

* the `24` **magnetic fields** `B_{i a} = ε_{ijk} ∂_j A_{k,a}` of the parcel
  (`linForm_ymMag`);
* the `8` **Gauss/Coulomb gauge-fixing forms** `ζ Σ_j ∂_j A_{j,a}` (`linForm_ymGauss`) — the
  3D gauge condition, imposed as a squared constraint;
* the `72` **derivative-tie forms** `λ(∂_jA_{k,a} + A_{k,a} − A_{k,a}^{next})`
  (`linForm_ymTie`), which state that the independent coordinate `∂_jA_{k,a}` is the finite
  difference of the gauge field between neighbouring parcels.  These forms reach into the
  neighbouring parcel, so the Hamiltonian is genuinely **interacting**
  (`ym_interaction_nontrivial`).

The kinetic term is `½ Σ_{j,a} π_{A_{j,a}}²`, the momenta conjugate to the `24` gauge
fields of each parcel (`ymKap`).

## What is proved

* `ymKap`, `ymAbelian_eq_sqSumOp`, `ymAbelian_esa_farisLavine` — the one-particle
  Hamiltonian as a kinetic-plus-squares operator, and its essential self-adjointness by
  Faris–Lavine;
* `coordOf`, `parcelOf`, `locOf`, `sum_reindex_parcels` — the sector bookkeeping;
* `ymSame`, `ymNext`, `ymVec`, `linForm_ymVec`, `linForm_ymMag`, `linForm_ymGauss`,
  `linForm_ymTie`, `ym_interaction_nontrivial` — the linear forms, written out;
* `abs_ymSame_le`, `abs_ymNext_le`, `ymVec_row_le`, `ymVec_col_le` — the Schur data,
  uniform in the parcel number;
* `ymFamily` — the resulting uniform kinetic-plus-squares family;
* `ymOuterHam_symmetricOn`, `ymOuterHam_esa_fl` — the Hamiltonian on the finite-particle
  core, symmetric and essentially self-adjoint **by Faris–Lavine**;
* **`ymOuterFock_esa_farisLavine`** — the headline: essential self-adjointness on the
  domain of the lifted Friedrichs extension of `N₁`, with the extension property on the
  finite-particle core.

## Honest boundary

This is the **abelian** magnetic field `B_{i a} = ε_{ijk} ∂_j A_{k,a}`, i.e. the structure
constants are `f_{abc} = 0`, exactly as in `BookProof.ChapterYangMillsAbelianEsa`.  For
`f_{abc} ≠ 0` the magnetic field is quadratic in the gauge fields, so the potential is
quartic; then no comparison operator that is a function of the harmonic oscillator can
satisfy the Faris–Lavine relative bound, and the essential self-adjointness of the
one-particle operator — Kato's theorem for `−Δ + V`, `V ≥ 0`, `V ∈ L²_loc` — is not
available in this development (see `REVIEW_AND_PLAN_20260907.md`, gap G1).  What the
parcel model *does* add beyond the one-particle abelian statement is the 3D gauge fixing,
the derivative-coordinate ties and the resulting nearest-neighbour interaction, all carried
through second quantization with constants independent of the parcel number.  No mass gap
and no spectral information is claimed.

Everything is `sorry`-free and `axiom`-free.
-/
