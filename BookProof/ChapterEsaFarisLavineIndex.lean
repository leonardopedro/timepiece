import Mathlib
import BookProof.ChapterYangMillsOuterFockFL
import BookProof.ChapterNsOuterFockFarisLavine
import BookProof.ChapterScalaronOuterFockFL
import BookProof.ChapterQg3DGaugeFarisLavine
import BookProof.ChapterQgVielbeinScalaronGaugeFL
import BookProof.ChapterYangMillsFockFriedrichs
import BookProof.ChapterScalaronNotQuadratic
import BookProof.ChapterNavierStokesFullEulerianFock
import BookProof.ChapterNavierStokesFullLagrangianFock
import BookProof.ChapterProve2meReuse

/-!
# Index: self-adjointness of the three Hamiltonians — **Faris–Lavine only**, except that
Yang–Mills is bounded below and gets a **direct Friedrichs extension**

This chapter is the single place where the essential-self-adjointness statements of the
three threads — quantum Yang–Mills, Navier–Stokes and quantum gravity — are collected in the
form the strategy asks for: **every one of them is proved by the commutator criterion of
Faris–Lavine**, with a Friedrichs comparison operator, and never by the Carleman flux
criterion, a Schur weight or a Kato–Rellich perturbation.

The one exception is **Yang–Mills, where no commutator criterion is needed at all**: that
Hamiltonian is a positive sum of squares, hence bounded below, so the Friedrichs extension
applies to it directly.  `BookProof.YmFockFriedrichs` carries out that route on the nested
Fock space, for arbitrary real structure constants — the quartic, non-abelian case included
— together with the 3D gauge-fixing forms in the independent derivative coordinates
(`ym_fock_friedrichs`, `ym_fock_stone_flow`).

The reason for the restriction is the Fock lift.  Of the data that a proof of essential
self-adjointness can produce on the one-particle Hilbert space, exactly two survive the
passage to the outer Fock space `⊕ₙ L²(ℝ^{d·n})`:

* the **Friedrichs extension** of a positive one-particle operator — it lifts to the
  `ℓ²`-direct sum because symmetry, positivity and surjectivity of `N + 1` are fibrewise
  (`BookProof.QgOuterFockFL.dsComparison`, `dsCompOp_surj`), and
* the **commutator with `N`** — because the commutator form of the lift is the sum of the
  fibre commutator forms (`BookProof.QgOuterFockFL.dsFibOp_hasSum_commForm`), so
  `±i[H,N] ≤ cN` lifts *with the same constant* as soon as the fibre constants are uniform
  in the particle number.

A Carleman flux estimate and a Schur weight are statements about the shells of a *fixed*
one-particle basis; the number of shells of the `n`-particle sector grows with `n` and the
constants degrade, so neither lifts.

## The index

| thread | one-particle / sector | finite-particle core | lifted (Friedrichs) domain |
| :-- | :-- | :-- | :-- |
| QYM (abelian, 3D gauge-fixed) | `ymAbelian_esa_farisLavine` | `ym_outerHam_esa_fl` | `ym_outerFock_esa_fl` |
| QYM (**non-abelian**, 3D gauge-fixed) — direct Friedrichs, no Faris–Lavine | `ym_fock_bddBelow` | `ym_fock_friedrichs` | — |
| NS (quadratic/Oseen model, gauge-fixed, derivative variables) | `ns_sector_esa_fl` | `ns_outerHam_esa_fl` | `ns_outerFock_esa_fl` |
| NS **full nonlinear**, Eulerian variables — bounded below, direct Friedrichs | `nsFullEuler_sector_friedrichs` | `nsFullEuler_bddBelow` | `nsFullEuler_outer_esa_fl` |
| NS **full nonlinear**, Lagrangian variables — bounded below, direct Friedrichs | `nsFullLagrangian_sector_friedrichs` | `nsFullLagrangian_bddBelow` | `nsFullLagrangian_outer_esa_fl` |
| QG (`R²`, vielbein, torsion) | `qg_sector_esa_fl` | `qg_outerHam_esa_fl` | `qg_outerFock_esa_fl` |
| QG interacting (nearest-neighbour torsion coupling) | `qgInt_sector_esa_fl` | `qgInt_outerHam_esa_fl` | `qgInt_outerFock_esa_fl` |
| QG with the **full exponential** scalaron potential | — | `scalaron_esa_core_fl` | `scalaron_esa_fl` |
| QG, `84` jet coordinates, 3D gauge fixing **and** gauge fixing of the derivative coordinates | `qg84_gaugeFixed_esa_fl` | `qg84_outerHam_esa_fl` | — |
| QG, vielbein **and** scalaron **and** both gauge fixings, exact Fourier modes | — | `qgFull_esa_core_fl` | `qgFull_esa_fl` |

## The Carleman-route statements and their Faris–Lavine replacements

Every essential-self-adjointness statement of the main line that used to be proved by the
Carleman flux criterion now has a Faris–Lavine proof of the *same* statement:

| Carleman-route statement | Faris–Lavine replacement |
| :-- | :-- |
| `BookProof.QgOuterFock.sqSumOp_essentiallySelfAdjointOn` | `BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine` |
| `BookProof.YangMillsAbelianEsa.ymAbelian_essentiallySelfAdjointOn_core` | `BookProof.YmOuterFockFL.ymAbelian_esa_farisLavine` |
| `BookProof.Qg3DGaugeEsa.qgSigned_essentiallySelfAdjointOn_core` | `BookProof.Qg3DGaugeFL.qgSigned_esa_fl` |
| `BookProof.Qg3DGaugeEsa.qg3D_essentiallySelfAdjointOn_core` | `BookProof.Qg3DGaugeFL.qg3D_esa_fl` |
| `BookProof.QgOuterFock.qgOuterFock_esa` | `qg_outerHam_esa_fl`, `qg84_outerHam_esa_fl` |

The Carleman statements are kept — they are true, and they are the historical record — but
nothing in the Faris–Lavine line depends on them.

## Particle number

The outer Hamiltonians of the nested Fock space conserve the particle number, so no lattice
regularization is needed to decompose the problem: `BookProof.Qg3DGaugeFL.dsOp_number_conserving`
(every direct-sum Hamiltonian is block diagonal in the sectors),
`BookProof.Qg3DGaugeFL.qgGauge_number_conserving` and, for the mode model,
`BookProof.QgVielbeinScalaronGaugeFL.secHam_number_conserving`.

The finite-particle-core entries are new: the finite-particle-core statements used to be
proved by the Carleman route (`BookProof.QgOuterFock.sqSumOp_essentiallySelfAdjointOn`), and
here they are re-proved from the Faris–Lavine certificate through
`BookProof.QgOuterFockCoreFL.CoreData.esa_on_core`.  The scalaron entry
`scalaron_esa_core_fl` is likewise new: it moves the Faris–Lavine conclusion of
`BookProof.ScalaronOuterFockFL.secHam_essentiallySelfAdjointOn` from the domain of the
comparison operator down to the finite-particle core, for the Hamiltonian carrying the full
exponential Einstein-frame potential with no Taylor expansion.

## Honest boundary

Unchanged from the individual chapters, and repeated here because this is the index:

* the Faris–Lavine Yang–Mills statements are for the **abelian** magnetic field; for
  `f_{abc} ≠ 0` the potential is quartic and no comparison operator built from the harmonic
  oscillator satisfies the Faris–Lavine relative bound.  For the non-abelian Hamiltonian the
  statement proved is the *direct Friedrichs extension* (`ym_fock_friedrichs`): a distinguished
  positive self-adjoint realization and its unitary flow, not uniqueness of the self-adjoint
  extension;
* the gravity Hamiltonian **with** the scalaron is not a kinetic-plus-squares operator: the
  full exponential Einstein-frame potential is not a polynomial of degree `≤ 2`
  (`BookProof.ScalaronNotQuadratic.starobinskyV_not_quadratic`), so the `84`-coordinate
  kinetic-plus-squares identification applies only to the pure tetrad/jet sector, and the
  model with the scalaron is handled by the Faris–Lavine mode machinery with a genuine wall;
* the Navier–Stokes results come in two layers.  The **quadratic (Oseen) model** — advection
  by a background velocity — is *essentially* self-adjoint on the finite-particle core and on
  the lifted Friedrichs domain (`ns_sector_esa_fl`, `ns_outerHam_esa_fl`,
  `ns_outerFock_esa_fl`).  The **full nonlinear models**, in Eulerian and in Lagrangian
  variables, carry the exact advection `u·∇u`, the exact Piola pressure term and the exact
  `det F = 1` volume constraint (`BookProof.NsFullEuler.nsResPoly_not_affine`,
  `BookProof.NsFullLagrangian.volumePoly_not_quadratic` prove that these really are nonlinear);
  they are bounded below, so — exactly as for non-abelian Yang–Mills — the route is the
  *direct Friedrichs extension*, lifted fibrewise to the outer Fock space, and the
  Faris–Lavine criterion is run there with that lifted extension as comparison operator and
  commutator constant `c = 0` (`nsFullEuler_outer_esa_fl`, `nsFullLagrangian_outer_esa_fl`).
  What is *not* claimed for the nonlinear models is uniqueness of the self-adjoint extension
  from the finite-parcel core;
* nothing anywhere bears on classical Navier–Stokes regularity;
* no spectral information, no mass gap and no continuum limit is claimed anywhere.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

namespace BookProof.EsaFarisLavineIndex

open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFockCoreFL BookProof.FarisLavineOnly

/-! ## 1. Quantum gravity: the torsion sectors -/

open BookProof.QgOuterFock BookProof.QgOuterFockFullFL in
/-- **Each gravity sector is essentially self-adjoint on its Gauss–polynomial core, by
Faris–Lavine.** -/
theorem qg_sector_esa_fl (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := n * 84)) (qgSectorHam n) :=
  (qgSectorData n).esa_on_core (qgSectorHam_symmetricOn n) qgFLc_nonneg
    (qgSectorData_commForm_le n)

open BookProof.QgOuterFock BookProof.QgOuterFockFullFL in
/-- **The gravity Hamiltonian is essentially self-adjoint on the finite-particle core of the
outer Fock space, by Faris–Lavine.** -/
theorem qg_outerHam_esa_fl : EssentiallySelfAdjointOn qgOuterCore qgOuterHam :=
  dsOp_essentiallySelfAdjointOn _ fun n => qg_sector_esa_fl n

/-- **The gravity Hamiltonian on the lifted Friedrichs domain, by Faris–Lavine** — the
statement of `BookProof.ChapterQgOuterFockFullFL`, recorded here for the index. -/
alias qg_outerFock_esa_fl := BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full

/-! ## 2. Quantum gravity: the interacting family -/

namespace QgInt

open BookProof.QgOuterFock BookProof.QgOuterFockInteractionFL

/-- **Each sector of an interacting gravity family is essentially self-adjoint on its
Gauss–polynomial core, by Faris–Lavine.** -/
theorem qgInt_sector_esa_fl (F : QgFamily) (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := n * 84)) (F.secHam n) :=
  (F.secData n).esa_on_core (F.secHam_symmetricOn n) F.flc_nonneg (F.secData_commForm_le n)

/-- **The interacting gravity Hamiltonian is essentially self-adjoint on the
finite-particle core, by Faris–Lavine.** -/
theorem qgInt_outerHam_esa_fl (F : QgFamily) :
    EssentiallySelfAdjointOn qgOuterCore F.outerHam :=
  dsOp_essentiallySelfAdjointOn _ fun n => qgInt_sector_esa_fl F n

/-- The nearest-neighbour torsion coupling, on the finite-particle core, by Faris–Lavine. -/
theorem qgInteracting_esa_core_fl (lam : ℝ) :
    EssentiallySelfAdjointOn qgOuterCore (qgIntFamily lam).outerHam :=
  qgInt_outerHam_esa_fl (qgIntFamily lam)

/-- The nearest-neighbour torsion coupling, on the lifted Friedrichs domain. -/
alias qgInt_outerFock_esa_fl := BookProof.QgOuterFockInteractionFL.qgInteracting_esa_farisLavine

end QgInt

/-! ## 3. Navier–Stokes -/

namespace Ns

open BookProof.SqSumOuterFamily BookProof.NsOuterFock

variable {bv : Fin 3 → ℝ} {nu lam mu gg B : ℝ}
variable (hB : 0 ≤ B) (hbv : ∀ j, |bv j| ≤ B) (hnu : |nu| ≤ B) (hlam : |lam| ≤ B)
  (hmu : |mu| ≤ B) (hgg : |gg| ≤ B)

include hB hbv hnu hlam hmu hgg in
/-- **Each Navier–Stokes parcel sector is essentially self-adjoint on its Gauss–polynomial
core, by Faris–Lavine.** -/
theorem ns_sector_esa_fl (n : ℕ) :
    EssentiallySelfAdjointOn
      (polyGaussCore (d := (nsFamily hB hbv hnu hlam hmu hgg).dim n))
      ((nsFamily hB hbv hnu hlam hmu hgg).secHam n) :=
  secHam_esa_fl (nsFamily hB hbv hnu hlam hmu hgg) n

include hB hbv hnu hlam hmu hgg in
/-- **The gauge-fixed Navier–Stokes Hamiltonian is essentially self-adjoint on the
finite-particle core of the outer Fock space, by Faris–Lavine.** -/
theorem ns_outerHam_esa_fl :
    EssentiallySelfAdjointOn (outerCore (nsFamily hB hbv hnu hlam hmu hgg).dim)
      (nsFamily hB hbv hnu hlam hmu hgg).outerHam :=
  outerHam_esa_fl (nsFamily hB hbv hnu hlam hmu hgg)

end Ns

/-- The Navier–Stokes Hamiltonian on the lifted Friedrichs domain, by Faris–Lavine. -/
alias ns_outerFock_esa_fl := BookProof.NsOuterFock.nsOuterFock_esa_farisLavine

/-! ## 3b. Navier–Stokes without approximations: the full nonlinear models

The advection is the exact `u·∇u` in Eulerian variables, and in Lagrangian variables the
pressure term is the exact Piola transform `cof(F)ᵀ∇q` and incompressibility is the exact
`det F = 1`.  Both Hamiltonians are positive sums of squares, hence bounded below, so — as
for non-abelian Yang–Mills — the Friedrichs extension applies directly and lifts fibrewise
to the nested Fock space, where the Faris–Lavine criterion is then run with that lifted
extension as the comparison operator. -/

/-- The full nonlinear **Eulerian** Navier–Stokes Hamiltonian on the nested Fock space is
bounded below. -/
alias nsFullEuler_bddBelow := BookProof.NsFullEuler.nsFullFockHam_quadForm_nonneg

/-- Its Friedrichs extension on every parcel-number sector. -/
alias nsFullEuler_sector_friedrichs := BookProof.NsFullEuler.nsSector_friedrichs_extension

/-- Its Friedrichs extension on the nested Fock space. -/
alias nsFullEuler_friedrichs := BookProof.NsFullEuler.nsFullFock_friedrichs_extension

/-- **Faris–Lavine on the outer Fock space** for the full nonlinear Eulerian model. -/
alias nsFullEuler_outer_esa_fl := BookProof.NsFullEuler.nsFullOuterN_esa

/-- That realization extends the Hamiltonian defined on the finite-parcel core. -/
alias nsFullEuler_outer_extension :=
  BookProof.NsFullEuler.nsFullOuterN_isPositiveSelfAdjointExtension

/-- The unitary flow it generates. -/
alias nsFullEuler_stone_flow := BookProof.NsFullEuler.nsFullFock_stone_flow

/-- The advection of the Eulerian model is genuinely nonlinear: it is not an affine form of
the coordinates, so the model is not an Oseen linearisation. -/
alias nsFullEuler_nonlinear := BookProof.NsFullEuler.nsResPoly_not_affine

/-- The full nonlinear **Lagrangian** Navier–Stokes Hamiltonian on the nested Fock space is
bounded below. -/
alias nsFullLagrangian_bddBelow := BookProof.NsFullLagrangian.lagFullFockHam_quadForm_nonneg

/-- Its Friedrichs extension on every parcel-number sector. -/
alias nsFullLagrangian_sector_friedrichs :=
  BookProof.NsFullLagrangian.lagSector_friedrichs_extension

/-- Its Friedrichs extension on the nested Fock space. -/
alias nsFullLagrangian_friedrichs := BookProof.NsFullLagrangian.lagFullFock_friedrichs_extension

/-- **Faris–Lavine on the outer Fock space** for the full nonlinear Lagrangian model. -/
alias nsFullLagrangian_outer_esa_fl := BookProof.NsFullLagrangian.lagFullOuterN_esa

/-- That realization extends the Hamiltonian defined on the finite-parcel core. -/
alias nsFullLagrangian_outer_extension :=
  BookProof.NsFullLagrangian.lagFullOuterN_isPositiveSelfAdjointExtension

/-- The unitary flow it generates. -/
alias nsFullLagrangian_stone_flow := BookProof.NsFullLagrangian.lagFullFock_stone_flow

/-- Volume preservation in the Lagrangian model is the exact cubic `det F = 1`, not its
quadratic linearisation. -/
alias nsFullLagrangian_nonlinear := BookProof.NsFullLagrangian.volumePoly_not_quadratic

/-! ## 4. Quantum Yang–Mills

The Yang–Mills Hamiltonian is bounded below, so the primary route is the **direct Friedrichs
extension** — valid for every family of real structure constants, the non-abelian ones
included — and the Faris–Lavine statements below are the (abelian) essential-self-adjointness
refinements of it. -/

/-- **The Yang–Mills Hamiltonian on the nested Fock space is bounded below.** -/
alias ym_fock_bddBelow := BookProof.YmFockFriedrichs.ymFockHam_quadForm_nonneg

/-- **The direct Friedrichs extension of the (possibly non-abelian) gauge-fixed Yang–Mills
Hamiltonian on the nested Fock space.**  No Faris–Lavine certificate is used. -/
alias ym_fock_friedrichs := BookProof.YmFockFriedrichs.ymFock_friedrichs_extension

/-- The unitary time evolution generated by that self-adjoint realization. -/
alias ym_fock_stone_flow := BookProof.YmFockFriedrichs.ymFock_stone_flow

/-- The one-particle abelian gauge-fixed Yang–Mills Hamiltonian, by Faris–Lavine. -/
alias ym_one_particle_esa_fl := BookProof.YmOuterFockFL.ymAbelian_esa_farisLavine

/-- The Yang–Mills Hamiltonian on the finite-particle core, by Faris–Lavine. -/
alias ym_outerHam_esa_fl := BookProof.YmOuterFockFL.ymOuterHam_esa_fl

/-- The Yang–Mills Hamiltonian on the lifted Friedrichs domain, by Faris–Lavine. -/
alias ym_outerFock_esa_fl := BookProof.YmOuterFockFL.ymOuterFock_esa_farisLavine

/-! ## 4b. Particle-number conservation of the parcel families (Navier–Stokes, Yang–Mills)

Every outer Hamiltonian of a kinetic-plus-squares family is a direct sum, hence block
diagonal in the particle-number sectors.  This is what replaces a lattice regularization:
the nested Fock space is decomposed by its number sectors. -/

open BookProof.SqSumOuterFamily in
/-- **The outer Hamiltonian of any parcel family conserves the particle number** — in
particular the Navier–Stokes and the Faris–Lavine Yang–Mills parcel Hamiltonians. -/
theorem outerHam_number_conserving (F : SqFamily) (x : outerCore F.dim) {n : ℕ}
    (hx : ∀ m, m ≠ n → ((x : outerFock F.dim) : ∀ m : ℕ, L2d (F.dim m)) m = 0) (m : ℕ)
    (hm : m ≠ n) : ((F.outerHam x : outerFock F.dim) : ∀ m : ℕ, L2d (F.dim m)) m = 0 :=
  BookProof.Qg3DGaugeFL.dsOp_number_conserving _ x hx m hm

/-! ## 5. Quantum gravity with the full exponential scalaron potential -/

namespace Scalaron

open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL

variable {ι : Type*} (W : WallPot) (Q : QgModeData ι)

/-- **The full quantum-gravity Hamiltonian with the exponential Einstein-frame potential is
essentially self-adjoint on the finite-particle core of the outer Fock space, by
Faris–Lavine.**  `BookProof.ScalaronOuterFockFL.secHam_essentiallySelfAdjointOn` proves this
on the whole domain of the comparison operator; here the conclusion is brought back to the
core, which is where the Hamiltonian is originally defined.  No Taylor expansion of the
potential and no relative-boundedness hypothesis on the wall is used. -/
theorem scalaron_esa_core_fl :
    EssentiallySelfAdjointOn (secCore (ι := ι)) (secHam W Q) := by
  refine (secData W Q).esa_on_core (secHam_symmetricOn W Q)
    (c := 6 * Q.K) (by have := Q.K_nonneg; linarith) ?_
  intro p
  have hc : commForm (secData W Q).H₀ (secData W Q).coreN p
      = commForm (secHam W Q) (secDiag W Q) p :=
    commForm_congr _ _ _ _ _ _ rfl (secData_coreN W Q p)
  have hq : quadForm (secData W Q).coreN p = quadForm (secDiag W Q) p :=
    quadForm_congr _ _ _ _ rfl (secData_coreN W Q p)
  rw [hc, hq]
  exact secHam_commForm_le W Q p

end Scalaron

/-- The scalaron Hamiltonian on the domain of the lifted comparison operator, by
Faris–Lavine. -/
alias scalaron_esa_fl := BookProof.ScalaronOuterFockFL.secHam_essentiallySelfAdjointOn

/-! ## 6. Quantum gravity in the `84` jet coordinates, both gauge fixings -/

/-- The `84`-coordinate 3D gauge-fixed gravity Hamiltonian on the one-particle space, by
Faris–Lavine. -/
alias qg84_esa_fl := BookProof.Qg3DGaugeFL.qg3D_esa_fl

/-- The same with the 3D gauge condition and the gauge fixing of the derivative coordinates
added as quadratic gauge-fixing terms. -/
alias qg84_gaugeFixed_esa_fl := BookProof.Qg3DGaugeFL.qg3DGaugeFixed_esa_fl

/-- The gauge-fixed gravity Hamiltonian on the finite-particle core of the nested Fock
space, by Faris–Lavine. -/
alias qg84_outerHam_esa_fl := BookProof.Qg3DGaugeFL.qgGauge_outerHam_esa_fl

/-! ## 7. Quantum gravity: vielbein and scalaron and both gauge fixings -/

/-- **The complete model** — vielbein in exact Fourier modes, the independent derivative
variables with their gauge fixing, the 3D transverse gauge fixing and the scalaron with the
full exponential Einstein-frame potential — on the domain of the lifted Friedrichs
comparison operator, by Faris–Lavine. -/
alias qgFull_esa_fl := BookProof.QgVielbeinScalaronGaugeFL.qgFull_esa_farisLavine

/-- The same on the finite-particle core. -/
alias qgFull_esa_core_fl := BookProof.QgVielbeinScalaronGaugeFL.qgFull_esa_core_fl

/-- The physical instance, with the Einstein-frame Starobinsky potential in its full
exponential form. -/
alias starobinsky_qgFull_esa_fl := BookProof.QgVielbeinScalaronGaugeFL.starobinsky_qgFull_esa

/-! ## 8. Reused prove2me theorems (external hypotheses)

The Fourier-elimination route (the 2026‑09‑15 wave of `CONSOLIDATED_PLAN.md`) consumes a
handful of propositions that the prove2me catalogue **already proves** but that cannot be imported
across the Lean `v4.28.0` / `v4.33.1` split.  They are transcribed in
`BookProof.ChapterProve2meReuse` as **named hypotheses** — the bundle
`BookProof.Prove2meReuse.RouteHypotheses` and one `Prop` per theorem — never as `axiom`s.
The frozen source, with the platform ids, is `PROVE2ME_REUSABLE_THEOREMS.md` at the repository
root.  A route theorem takes the bundle as a parameter and calls the projection below.

* **NS 3** (convolution algebra) — `ns_convolution_symmetric`:
  `L2.convolutionCLM_isSymmetric_of_conj_neg` (Claude).
* **NS 3** (Ritz ladder) — `ns_convolution_compact`:
  `L2.exists_convolutionCLM_isCompactOperator_of_compactSpace` (Claude).
* **NS 4 / §5** (Friedrichs positivity) — `ns_friedrichs_lower_bound`:
  `posDef_quadratic_form_lower_bound` (olivier).
* **NS 6 / §6.1** (determinant) — `lagrangian_det_add_two`: `Diaz.det_add_two`
  (carlok).
* **QG 8** (band / Ritz ladder) — `qg_compact_spectral_edge`:
  `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker` (Claude).
* **QG 8** (Ritz truncation) — `qg_high_part_finiteDimensional`:
  `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal`
  (Claude).
* **QG 7** (Gribov region) — `qg_gribov_negative_direction`:
  `GribovRegion.exists_neg_quadratic_form_of_traceless` (Lucas).

The fully qualified source names (with namespaces) and the verbatim platform statements
are in `PROVE2ME_REUSABLE_THEOREMS.md`.

Nothing in the already-proved index above depends on these hypotheses; they are the
carrier for the *new* momentum-space route, which is still a plan item.
-/

open BookProof.Prove2meReuse in
/-- NS item 3: the one-particle convolution mode operator is symmetric (reused prove2me
hypothesis, `RouteHypotheses.convolution_symmetric`). -/
theorem index_ns_convolution_symmetric (H : RouteHypotheses) : ConvolutionCLMSymmetric :=
  ns_convolution_symmetric H

open BookProof.Prove2meReuse in
/-- NS item 4 / §5: the positive-definite form lower bound behind the Friedrichs comparison
(reused prove2me hypothesis). -/
theorem index_ns_friedrichs_lower_bound (H : RouteHypotheses) : PosDefLowerBound :=
  ns_friedrichs_lower_bound H

open BookProof.Prove2meReuse in
/-- QG item 8: the compact-symmetric spectral edge of the band / Ritz ladder (reused prove2me
hypothesis). -/
theorem index_qg_compact_spectral_edge (H : RouteHypotheses) :
    CompactSymmetricOrthogonalEigenspace :=
  qg_compact_spectral_edge H

open BookProof.Prove2meReuse in
/-- QG item 7: a traceless Hermitian non-zero matrix has a negative direction (reused prove2me
hypothesis). -/
theorem index_qg_gribov_negative_direction (H : RouteHypotheses) : GribovNegativeDirection :=
  qg_gribov_negative_direction H

end BookProof.EsaFarisLavineIndex

end
