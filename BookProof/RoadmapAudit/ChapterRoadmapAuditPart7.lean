/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import BookProof.RoadmapAudit.ChapterRoadmapAuditImports

/-!
# Roadmap headline certificate — audit ledger, slice 7 of 8

Slice 7 of the eight slices of the `#audit_axioms` ledger that used to sit at the end of
`BookProof/RoadmapAudit/ChapterRoadmapAudit.lean`.  The directives are the original ones,
verbatim and in the original order; the split exists only so that Lake elaborates eight modules in
parallel instead of one, which is where the aggregate build's 25 minutes went.

Each line prints the stock `'name' depends on axioms: [...]` line for one declaration; nothing
here asserts an axiom set.
-/

namespace BookProof.ChapterRoadmapAudit

open BookProof.AxiomAudit

-- `ChapterFockNumberPreservingGap` (plan, top work package): the `dΓ` lift no longer needs
-- the one-particle Hamiltonian to be diagonal, only number preserving with a one-particle
-- gap `h − μ ≥ 0`.
#audit_axioms BookProof.FockNumberPreservingGap.dGamma_shiftCol
#audit_axioms BookProof.FockNumberPreservingGap.dGamma_vac
#audit_axioms BookProof.FockNumberPreservingGap.number_quadForm_ge
#audit_axioms BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving
#audit_axioms BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving_op
#audit_axioms BookProof.FockNumberPreservingGap.isPosCol_shiftCol_diagCol
#audit_axioms BookProof.FockNumberPreservingGap.fock_gap_of_one_particle_form_gap

-- `ChapterFockInteractionStability` (plan, top work package): the number-preservation
-- hypothesis replaced by a quantitative one — a gap `μ` survives any perturbation whose
-- form is dominated by `a q + b‖·‖²` (`a ≤ 1`), leaving gap `(1 − a)μ − b`; in particular
-- `dΓ(h) + V` keeps gap `μ − ‖V‖` for an arbitrary bounded `V`, pair creation included.
#audit_axioms BookProof.FockInteractionStability.gap_persists_of_relative_form_bound
#audit_axioms BookProof.FockInteractionStability.gap_persists_of_bounded_form
#audit_axioms BookProof.FockInteractionStability.gap_persists_pos
#audit_axioms BookProof.FockInteractionStability.interaction_form_bound
#audit_axioms BookProof.FockInteractionStability.fock_gap_of_bounded_interaction
#audit_axioms BookProof.FockInteractionStability.fock_gap_of_one_particle_form_gap_interaction

-- `ChapterTempleSeparationNecessary` (plan, top work package): the spectral-separation input
-- of Temple's inequality is a genuine side condition — an exact eigenvector (zero residual)
-- says nothing at all about how far below the spectrum extends.
#audit_axioms BookProof.TempleSeparationNecessary.isSelfAdjoint_witness
#audit_axioms BookProof.TempleSeparationNecessary.rayleigh_witness
#audit_axioms BookProof.TempleSeparationNecessary.resid_witness
#audit_axioms BookProof.TempleSeparationNecessary.neg_mem_spectrum_witness
#audit_axioms BookProof.TempleSeparationNecessary.separation_necessary

-- `ChapterFockPairPerturbation` (plan, top work package): the next degree of perturbation —
-- the quadratic, pair-creating field term `P(f,g) = a†(f)a†(g) + a(g)a(f)`.  The canonical
-- commutation relation gives the exact identity `‖a†(g)u‖² = ‖a(g)u‖² + ‖g‖²‖u‖²`, hence the
-- `(N+1)^{1/2}` estimate a quadratic term needs; the pair form is then dominated by the free
-- form with *no* additive remainder on the vacuum-orthogonal sector, and the gap `μ` degrades
-- only to `μ − 2√2‖f‖‖g‖`.  `pairVec_vac` and `pairVec_unbounded` record that the term really
-- changes the particle number by two and really is unbounded.  Cubic and quartic Yang–Mills
-- terms remain outside this chapter.
#audit_axioms BookProof.FockPairPerturbation.annVec_creVec
#audit_axioms BookProof.FockPairPerturbation.norm_creVec_sq
#audit_axioms BookProof.FockPairPerturbation.norm_creVec_le
#audit_axioms BookProof.FockPairPerturbation.abs_re_inner_pairVec_le
#audit_axioms BookProof.FockPairPerturbation.pairVec_relative_form_bound
#audit_axioms BookProof.FockPairPerturbation.fock_gap_of_pair_perturbation
#audit_axioms BookProof.FockPairPerturbation.fock_gap_of_pair_perturbation_pos
#audit_axioms BookProof.FockPairPerturbation.fock_gap_of_one_particle_form_gap_pair
#audit_axioms BookProof.FockPairPerturbation.pairVec_vac
#audit_axioms BookProof.FockPairPerturbation.pairVec_unbounded
#audit_axioms BookProof.FockPairPerturbation.ym_fock_gap_of_pair_perturbation

-- `ChapterFockCubicUnbounded` (plan, top work package): the boundary of the
-- form-domination route.  Degrees one and two are covered by
-- `ChapterFockFieldPerturbation` and `ChapterFockPairPerturbation`; degree three is not,
-- and this chapter proves that it *cannot* be.  On the explicit two-term trial states
-- `|n⟩ + c|n+3⟩` the number form, the norm and the cubic form are computed exactly, and the
-- cubic form grows like `n^{3/2}` while the number form grows only like `n`.  Hence no
-- relative form bound `a·⟪u,Nu⟫ + b‖u‖²` can dominate the cubic form
-- (`cubic_no_relative_form_bound`), and `dΓ(N) + lam·C_k` is unbounded below on the
-- vacuum-orthogonal sector at every coupling strength `lam > 0`
-- (`fock_gap_fails_for_cubic`).  The complementary `trial_cubic_quartic_bounded_below`
-- shows that adding the normal-ordered quartic term `Q_k = (a_k†)²(a_k)²` restores a lower
-- bound `-(lam⁴/4 + 2lam²)‖u‖²` along that same family, so the divergence is a property of
-- a *bare* cubic term.  `cubeA` is a single-mode cubic term, not the physical Yang–Mills
-- cubic vertex, and no mass gap of the physical Hamiltonian is claimed.
#audit_axioms BookProof.FockCubicUnbounded.confNumber_confAt
#audit_axioms BookProof.FockCubicUnbounded.cubeA_coord
#audit_axioms BookProof.FockCubicUnbounded.trial_norm_sq
#audit_axioms BookProof.FockCubicUnbounded.trial_numberQuad
#audit_axioms BookProof.FockCubicUnbounded.trial_cubic_form
#audit_axioms BookProof.FockCubicUnbounded.cubic_no_relative_form_bound
#audit_axioms BookProof.FockCubicUnbounded.fock_gap_fails_for_cubic
#audit_axioms BookProof.FockCubicUnbounded.quartA_single_confAt
#audit_axioms BookProof.FockCubicUnbounded.trial_quartic_form
#audit_axioms BookProof.FockCubicUnbounded.trial_cubic_quartic_bounded_below

-- `ChapterFockCubicQuarticStability` (plan, top work package, next step 2): the same
-- cubic/quartic pair, now on *arbitrary* finite states rather than the two-term trial
-- family.  `quart_form_eq` and `cubic_form_eq` turn the two interaction forms into the
-- norms `‖a_k²u‖²` and `2Re⟪a_k²u, a_k†u⟫`, `norm_creA_sq` is the single-mode canonical
-- commutation relation and `sq_norm_annA_le_mul` the Cauchy–Schwarz bound that forces a
-- large mode occupation to carry a large quartic form.  Together they give
-- `mode_cubic_quartic_bounded_below` and `numberForm_cubic_quartic_bounded_below`, the
-- uniform lower bound `-(2lam² + (2lam² + ½ − mu)²/2)‖u‖²` for `mu⟪u,Nu⟫ + lam·C_k + Q_k`,
-- its `mu = 1` corollary, the multi-mode sums
-- `multiMode_cubic_quartic_bounded_below` / `dGamma_multiMode_cubic_quartic_bounded_below`
-- (one copy of the free form pays for every mode of a finite set, the constant growing
-- linearly in its cardinality) and the one-particle-gap version
-- `dGamma_cubic_quartic_bounded_below`.  This is semiboundedness, not a gap.
#audit_axioms BookProof.FockCubicQuarticStability.quart_form_eq
#audit_axioms BookProof.FockCubicQuarticStability.cubic_form_eq
#audit_axioms BookProof.FockCubicQuarticStability.norm_creA_sq
#audit_axioms BookProof.FockCubicQuarticStability.sq_norm_annA_le_mul
#audit_axioms BookProof.FockCubicQuarticStability.mode_cubic_quartic_bounded_below
#audit_axioms BookProof.FockCubicQuarticStability.numberForm_cubic_quartic_bounded_below
#audit_axioms BookProof.FockCubicQuarticStability.multiMode_cubic_quartic_bounded_below
#audit_axioms BookProof.FockCubicQuarticStability.trial_cubic_quartic_bounded_below_general
#audit_axioms BookProof.FockCubicQuarticStability.dGamma_cubic_quartic_bounded_below
#audit_axioms BookProof.FockCubicQuarticStability.dGamma_multiMode_cubic_quartic_bounded_below

-- `ChapterScalaronFockGapChain` (plan, top work package, next step 3): the abstract gap
-- chain instantiated for a sector with constant one-particle energy `m`, and then at the
-- Starobinsky scalaron mass `scalaronMass α = 1/√(12α)` on the Hermite basis of `L²(ℝ)`.
-- `constOnePart_quadForm` makes the one-particle form gap an identity, so
-- `const_fock_gap`, `const_fock_mass_gap`, `const_fock_gap_of_field_perturbation` and
-- `const_fock_cubic_quartic_bounded_below` — and their scalaron instances — need no
-- certificate, no Ritz data and no form-gap hypothesis.  Unconditional here is the *lift*:
-- that the `R²` sector's one-particle operator is this constant is a modelling statement,
-- and nothing about Yang–Mills is claimed.
#audit_axioms BookProof.ScalaronFockGapChain.constOnePart_quadForm
#audit_axioms BookProof.ScalaronFockGapChain.constOnePart_symmetricOn
#audit_axioms BookProof.ScalaronFockGapChain.const_fock_gap
#audit_axioms BookProof.ScalaronFockGapChain.const_isPosCol_shiftCol
#audit_axioms BookProof.ScalaronFockGapChain.const_fock_mass_gap
#audit_axioms BookProof.ScalaronFockGapChain.const_fock_gap_of_field_perturbation
#audit_axioms BookProof.ScalaronFockGapChain.const_fock_cubic_quartic_bounded_below
#audit_axioms BookProof.ScalaronFockGapChain.scalaronMass_pos
#audit_axioms BookProof.ScalaronFockGapChain.scalaron_fock_mass_gap
#audit_axioms BookProof.ScalaronFockGapChain.scalaron_fock_gap_of_field_perturbation
#audit_axioms BookProof.ScalaronFockGapChain.scalaron_fock_cubic_quartic_bounded_below

-- `ChapterFockDiagonalGapChain` (plan, top work package, next step 3): the chain for a
-- *diagonal* one-particle energy `e_k ↦ ω_k e_k`, the shape of the free sectors.
-- `diagOnePart_quadForm_ge` *proves* the one-particle form gap from `ω_k ≥ m`, so
-- `diag_fock_gap`, `diag_fock_mass_gap`, `diag_fock_gap_of_field_perturbation` and
-- `diag_fock_cubic_quartic_bounded_below` carry no certificate hypothesis;
-- `freeField_fock_mass_gap` is the free massive instance at the relativistic dispersion
-- `√(p² + m²)`.  Massless dispersion gives `m = 0`: positivity, no gap.
#audit_axioms BookProof.FockDiagonalGapChain.diagOnePart_inner
#audit_axioms BookProof.FockDiagonalGapChain.norm_sq_eq_sum
#audit_axioms BookProof.FockDiagonalGapChain.diagOnePart_symmetricOn
#audit_axioms BookProof.FockDiagonalGapChain.diagOnePart_quadForm_ge
#audit_axioms BookProof.FockDiagonalGapChain.diag_fock_gap
#audit_axioms BookProof.FockDiagonalGapChain.diag_isPosCol_shiftCol
#audit_axioms BookProof.FockDiagonalGapChain.diag_fock_mass_gap
#audit_axioms BookProof.FockDiagonalGapChain.diag_fock_gap_of_field_perturbation
#audit_axioms BookProof.FockDiagonalGapChain.diag_fock_cubic_quartic_bounded_below
#audit_axioms BookProof.FockDiagonalGapChain.freeDispersion_ge
#audit_axioms BookProof.FockDiagonalGapChain.freeField_fock_mass_gap

-- `ChapterScalaronEdge` (plan §state 29, item 4): the strict one-particle edge of the
-- Starobinsky fiber.  The plateau of `V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²` is `M⁴/(16α)`,
-- so for `0 < c < edgeShelf = M⁴/(32α)` the classically allowed region is the explicit
-- bounded window `[−A, B]`; the one-dimensional sup bound `‖f(x)‖² ≤ δ‖f‖² + δ⁻¹‖f'‖²`
-- then confines the core and yields the strict form gap `E₀ = min(1/(4(A+B)²), c/2) > 0`,
-- which `scalaronEdge_friedrichs_gap` transfers to the Friedrichs extension.
#audit_axioms BookProof.ScalaronEdge.starobinskyEdgeHam_symmetricOn
#audit_axioms BookProof.ScalaronEdge.starobinskyV_lt_shelf_bounded
#audit_axioms BookProof.ScalaronEdge.edge_normSq_hasDerivAt
#audit_axioms BookProof.ScalaronEdge.edge_re_mul_le
#audit_axioms BookProof.ScalaronEdge.edge_sup_sq_le
#audit_axioms BookProof.ScalaronEdge.edge_energy_bound
#audit_axioms BookProof.ScalaronEdge.starobinskyEdge_inner_eq
#audit_axioms BookProof.ScalaronEdge.starobinskyEdge_quadForm_eq
#audit_axioms BookProof.ScalaronEdge.starobinskyEdge_form_gap
#audit_axioms BookProof.ScalaronEdge.starobinskyEdge_quadForm
#audit_axioms BookProof.ScalaronEdge.scalaronEdge_friedrichs_gap

-- `ChapterVielbeinFiberFock` (plan §state 28j next steps, item 4(a)): the explicit
-- fibrewise reassembly of the vielbein/TEGR model — `d` harmonic shear fibers plus one
-- Starobinsky scalaron fiber per quantum — on the nested Fock space `⊕ₙ L²(ℝ^(n×(d+1)))`,
-- as thin glue over the generic instrument `fockSmoothPotential_esa`.
#audit_axioms BookProof.VielbeinFock.inner_vielbeinDir
#audit_axioms BookProof.VielbeinFock.vielbeinManyPotential_apply
#audit_axioms BookProof.VielbeinFock.vielbeinManyPotential_scalaron_fiber
#audit_axioms BookProof.VielbeinFock.contDiff_vielbeinManyPotential
#audit_axioms BookProof.VielbeinFock.vielbeinManyPotential_nonneg
#audit_axioms BookProof.VielbeinFock.vielbeinManyPotential_esa
#audit_axioms BookProof.VielbeinFock.vielbeinFockCore_dense
#audit_axioms BookProof.VielbeinFock.vielbeinFock_symmetric
#audit_axioms BookProof.VielbeinFock.vielbeinFock_deficiencyTrivialAt
#audit_axioms BookProof.VielbeinFock.vielbeinFock_esa
#audit_axioms BookProof.VielbeinFock.vielbeinFock_stone_flow
#audit_axioms BookProof.VielbeinFock.vielbeinFock_potential_ge

-- `ChapterQedFockGapChain` (plan §state 28j next steps, item 2): the QED instantiation of
-- the diagonal gap chain.  The free photon energy `ω_k = |p_k|` gives positivity at `m = 0`
-- and no gap — `photon_no_one_particle_gap` proves the obstruction for an
-- infrared-accumulating momentum assignment — while an infrared regulator `μ > 0` or a
-- massive (Proca) dispersion restores the nested-Fock mass gap.
#audit_axioms BookProof.QedFockGapChain.diagOnePart_quadForm_basis
#audit_axioms BookProof.QedFockGapChain.diagOnePart_no_form_gap
#audit_axioms BookProof.QedFockGapChain.photonDispersion_nonneg
#audit_axioms BookProof.QedFockGapChain.photon_fock_positivity
#audit_axioms BookProof.QedFockGapChain.photon_no_one_particle_gap
#audit_axioms BookProof.QedFockGapChain.irPhotonDispersion_ge
#audit_axioms BookProof.QedFockGapChain.irPhoton_fock_mass_gap
#audit_axioms BookProof.QedFockGapChain.proca_fock_mass_gap

-- `ChapterNavierStokesFiberGap` (plan §state 28j next steps, item 3): what the
-- Navier–Stokes Eulerian fiber can certify.  The fiber Hamiltonian is first order, so its
-- quadratic form vanishes at every Hermite basis state and it has no one-particle form gap
-- (`nsFiber_no_form_gap`); the Faris–Lavine comparison operator does carry a Friedrichs
-- form gap (`nsComparison_friedrichs_gap`).
#audit_axioms BookProof.NavierStokesFlow.FiberGap.cFun_coreState_self
#audit_axioms BookProof.NavierStokesFlow.FiberGap.aFun_coreState_self
#audit_axioms BookProof.NavierStokesFlow.FiberGap.ladFun_coreState_self
#audit_axioms BookProof.NavierStokesFlow.FiberGap.canH_coreState_self
#audit_axioms BookProof.NavierStokesFlow.FiberGap.nsFiber_quadForm_coreState
#audit_axioms BookProof.NavierStokesFlow.FiberGap.norm_coreState
#audit_axioms BookProof.NavierStokesFlow.FiberGap.nsFiber_no_form_gap
#audit_axioms BookProof.NavierStokesFlow.FiberGap.nsComparison_friedrichs_gap

-- `ChapterGaussCoordCombo`, `ChapterSqueezedGaussStates` and `ChapterYangMillsAbelianNoGap`
-- (plan §state 28j next steps, item 1): the one-coordinate Hermite calculus on the
-- Gauss-polynomial core, the truncated squeezed states built from it, and the resulting
-- negative answer for the abelian one-particle form gap.
#audit_axioms BookProof.GaussCoordCombo.gaussInt_hermiteFactor_mul
#audit_axioms BookProof.GaussCoordCombo.gaussInt_coordCombo_sq
#audit_axioms BookProof.GaussCoordCombo.gaussInt_prod_coordFactor
#audit_axioms BookProof.SqueezedGaussStates.op_squeezeState
#audit_axioms BookProof.SqueezedGaussStates.Usum_identity
#audit_axioms BookProof.SqueezedGaussStates.coordComboSum_opCoef_le
#audit_axioms BookProof.SqueezedGaussStates.exists_position_small
#audit_axioms BookProof.SqueezedGaussStates.exists_momentum_small
#audit_axioms BookProof.YangMillsAbelianNoGap.magPoly_abelian
#audit_axioms BookProof.YangMillsAbelianNoGap.norm_op_bigP_le
#audit_axioms BookProof.YangMillsAbelianNoGap.exists_core_state_small_energy
#audit_axioms BookProof.YangMillsAbelianNoGap.ym_abelian_no_one_particle_form_gap

-- `ChapterQgPhysicalSectorIdentity` (plan QG-3.2(a) attempt): the NS
-- derivative-variable fixing mechanism — the v-coupling vanishes on the
-- constraint surface `v = dφ`, the gauge-fixing Lagrangian reduces to the
-- ghost term, the promoted variable is a BRST doublet, and the fixing
-- integrates to zero on physical observables.  The concrete QG identity
-- (the 64 `idxDE` coordinates realizing the actual tetrad derivatives) stays
-- a named hypothesis with citation, never an axiom.
#audit_axioms BookProof.QgPhysicalSectorIdentity.s_gaugeField_eq_c
#audit_axioms BookProof.QgPhysicalSectorIdentity.lagrange_term_zero_of_fixing
#audit_axioms BookProof.QgPhysicalSectorIdentity.L_gf_constraint_surface
#audit_axioms BookProof.QgPhysicalSectorIdentity.int_L_gf_eq_zero_physical

-- `ChapterQgCouplingDGammaSum` (plan QG-3.2-exec (i), the operator track): the
-- lifted coupling `H_coup = Σ_ℓ dΓ(h_ℓ)` with the `h_ℓ` diagonalizable each in
-- its own basis.  Second quantization is additive in the one-particle datum, so
-- the coupling is a single `dΓ` — the common-alphabet weighted-`ℓ¹` gate is not
-- needed.  Hermiticity and positivity pass to the sum, so the Friedrichs
-- extension is unconditional; the relative form bound and the additivity of the
-- commutator form are proved; and the coupling is essentially self-adjoint on
-- the finite-occupation core whenever the *total* one-particle operator is
-- diagonal in the working basis with non-negative eigenvalues.
#audit_axioms BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq
#audit_axioms BookProof.QgCouplingDGammaSum.coupling_friedrichs
#audit_axioms BookProof.QgCouplingDGammaSum.coupling_quadForm_le
#audit_axioms BookProof.QgCouplingDGammaSum.commForm_finsetSum
#audit_axioms BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq
#audit_axioms BookProof.QgCouplingDGammaSum.coupling_esa_dGamma
#audit_axioms BookProof.QgCouplingDGammaSum.coupling_sum_friedrichs
#audit_axioms BookProof.QgCouplingDGammaSum.comparison_friedrichs
#audit_axioms BookProof.QgCouplingDGammaSum.coupling_quadForm_le_comparison
#audit_axioms BookProof.QgCouplingDGammaSum.numberOp_essentiallySelfAdjoint

-- `ChapterConformalSignFlip` (plan QG-2 / 29f Case B): the sign bookkeeping of
-- the densitized conformal direction.  `H ↦ −H` reflects the spectral
-- parameter, so essential self-adjointness is invariant under the global sign
-- flip and the wrong-sign-kinetic fiber `−K + V` is ESA iff the
-- positive-kinetic `K − V` is; a real shift only translates the deficiency
-- parameter.  This makes the plan's Case-B reduction rigorous; it does not
-- decide the remaining analytic (limit-circle) question.
#audit_axioms BookProof.ConformalSignFlip.deficiencyTrivialAt_neg
#audit_axioms BookProof.ConformalSignFlip.essentiallySelfAdjointOn_neg_iff
#audit_axioms BookProof.ConformalSignFlip.wrongSignKinetic_esa_iff
#audit_axioms BookProof.ConformalSignFlip.deficiencyTrivialAt_add_real
#audit_axioms BookProof.ConformalSignFlip.symmetricOn_neg
#audit_axioms BookProof.ConformalSignFlip.symmetricOn_add_real

-- `ChapterDirectSumEdge` (plan QG-3.4, derived case): fibre edges glue to their
-- infimum.  On the algebraic direct sum of the fibre cores the squared norm and
-- the energy are finite sums over the support, so a common lower bound `ν` of
-- the fibre form bounds is an edge of the glued operator — strict when `ν > 0`.
-- This is only the derived half of QG-3.4: it says nothing about the fibre
-- edges themselves, and a strict edge on a core is not a spectral gap.
#audit_axioms BookProof.DirectSumEdge.norm_sq_dsCore_eq_sum
#audit_axioms BookProof.DirectSumEdge.quadForm_dsOp_eq_sum
#audit_axioms BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges
#audit_axioms BookProof.DirectSumEdge.dsOp_edge_of_fibre_edges_le
#audit_axioms BookProof.DirectSumEdge.dsOp_edge_pos

-- `ChapterQgMultiHalfDensity` (plan QG-1): the multi-dimensional half-density
-- unitary of the densitized change of variables, and the transfer it enables.
-- General: a pair of mutually a.e.-inverse measure-preserving maps induces a
-- unitary of the `L²` spaces which carries bounded-energy cores onto each other
-- and intertwines the multiplication operators.  Concrete: `(y, ξ) ↦ (y², ξ)` on
-- the field space, i.e. the conformal coordinate densitized and every other
-- direction untouched.
#audit_axioms BookProof.QgMultiHalfDensity.mpUnitary_apply
#audit_axioms BookProof.QgMultiHalfDensity.mpUnitary_boundedEnergyCore_surjective
#audit_axioms BookProof.QgMultiHalfDensity.mpUnitary_intertwines_multOp
#audit_axioms BookProof.QgMultiHalfDensity.mpUnitary_hasZeroDeficiencyOn_transfer
#audit_axioms BookProof.QgMultiHalfDensity.measurePreserving_qgProdSquare
#audit_axioms BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_apply
#audit_axioms BookProof.QgMultiHalfDensity.multiHalfDensityUnitary_intertwines_multOp
#audit_axioms BookProof.QgMultiHalfDensity.multi_hasZeroDeficiencyOn_transfer
#audit_axioms BookProof.QgMultiHalfDensity.multi_physical_hasZeroDeficiencyOn
#audit_axioms BookProof.QgMultiHalfDensity.exists_field_halfDensity_unitary

-- `ChapterSirkRitzMinMax` (plan §12 Gap 2, QYM): the higher Rayleigh–Ritz levels
-- and the Ritz gap.  The Courant–Fischer min–max levels of a bounded operator,
-- the levels computed inside a Galerkin truncation, the variational principle in
-- the direction the algorithm certifies, the identification of level zero with
-- the bottom of the spectrum, and the convergence of the truncated levels — hence
-- of the computed gap — to the min–max levels.  Nothing here claims that a level
-- with `k ≥ 1` is an eigenvalue.
#audit_axioms BookProof.RitzMinMax.rayleighSup_le_norm
#audit_axioms BookProof.RitzMinMax.rayleighSup_mono
#audit_axioms BookProof.RitzMinMax.minmaxLevel_le_minmaxLevelIn
#audit_axioms BookProof.RitzMinMax.minmaxLevel_mono
#audit_axioms BookProof.RitzMinMax.minmaxLevel_zero_eq_rayleighInf
#audit_axioms BookProof.RitzMinMax.minmaxLevel_zero_eq_sInf_spectrum
#audit_axioms BookProof.RitzMinMax.finrank_galerkinSpan
#audit_axioms BookProof.RitzMinMax.exists_uniform_proj_bound
#audit_axioms BookProof.RitzMinMax.exists_galerkin_approx_subspace
#audit_axioms BookProof.RitzMinMax.galerkin_minmaxLevel_tendsto
#audit_axioms BookProof.RitzMinMax.galerkin_gap_tendsto
#audit_axioms BookProof.RitzMinMax.galerkin_gap_eventually_pos

-- `ChapterSirkRitzPerturbation` (plan §12 Gap 2, §13): the stability of the min–max
-- levels.  The Rayleigh quotients, the numerical-range suprema, the Courant–Fischer
-- levels and the Ritz levels of a truncation are all 1-Lipschitz in the operator norm;
-- the gap is 2-Lipschitz and survives a perturbation of less than half its size; a real
-- shift shifts the levels and leaves the gap invariant; and the Galerkin gaps of a model
-- operator converge to a limit within `2ε` of the true gap.
#audit_axioms BookProof.RitzPerturbation.abs_rayleighVal_sub_le_dist
#audit_axioms BookProof.RitzPerturbation.abs_rayleighSup_sub_le_dist
#audit_axioms BookProof.RitzPerturbation.abs_minmaxLevel_sub_le_dist
#audit_axioms BookProof.RitzPerturbation.abs_minmaxLevelIn_sub_le_dist
#audit_axioms BookProof.RitzPerturbation.minmaxLevel_le_minmaxLevelIn_add
#audit_axioms BookProof.RitzPerturbation.minmaxLevel_mono_form
#audit_axioms BookProof.RitzPerturbation.minmaxLevel_le_norm
#audit_axioms BookProof.RitzPerturbation.neg_norm_le_minmaxLevel
#audit_axioms BookProof.RitzPerturbation.minmaxLevel_shiftOp
#audit_axioms BookProof.RitzPerturbation.minmaxGap_shiftOp
#audit_axioms BookProof.RitzPerturbation.minmaxGap_nonneg
#audit_axioms BookProof.RitzPerturbation.abs_minmaxGap_sub_le
#audit_axioms BookProof.RitzPerturbation.minmaxGap_ge_of_dist_le
#audit_axioms BookProof.RitzPerturbation.minmaxGap_pos_of_dist_lt
#audit_axioms BookProof.RitzPerturbation.minmaxLevel_tendsto_of_tendsto
#audit_axioms BookProof.RitzPerturbation.minmaxGap_tendsto_of_tendsto
#audit_axioms BookProof.RitzPerturbation.galerkin_model_gap_tendsto
#audit_axioms BookProof.RitzPerturbation.galerkin_model_gap_eventually_pos
#audit_axioms BookProof.RitzPerturbation.abs_sInf_spectrum_sub_le_dist

-- `ChapterQgDerivativeRealization` (plan QG-3.2-exec (ii)): the concrete 84-dimensional
-- derivative-variable fixing `E = ∂e`.  The 1-jet realization of the coordinate space, the
-- concrete gauge field `v − dφ` and its zero locus, the reduction of the tetrad–torsion cross
-- coupling to field values on that locus, and the concrete gauge-fixing system (with the honest
-- exterior derivative) through which the abstract theorems of `ChapterQgPhysicalSectorIdentity`
-- run with their hypothesis discharged.
#audit_axioms BookProof.QgDerivativeRealization.configPoint_idxDE
#audit_axioms BookProof.QgDerivativeRealization.idx_cases
#audit_axioms BookProof.QgDerivativeRealization.jetDeriv_fixed
#audit_axioms BookProof.QgDerivativeRealization.fixed_iff
#audit_axioms BookProof.QgDerivativeRealization.exists_not_fixed
#audit_axioms BookProof.QgDerivativeRealization.configPoint_eq_jetPoint_of_fixed
#audit_axioms BookProof.QgDerivativeRealization.eval_torsionPoly_jetPoint
#audit_axioms BookProof.QgDerivativeRealization.eval_crossCouplingPoly_jetPoint
#audit_axioms BookProof.QgDerivativeRealization.eval_eq_of_fixed_of_comp_eq
#audit_axioms BookProof.QgDerivativeRealization.crossCoupling_eq_of_fixed
#audit_axioms BookProof.QgDerivativeRealization.couplingValue_ne_zero
#audit_axioms BookProof.QgDerivativeRealization.qgFixing_gaugeField
#audit_axioms BookProof.QgDerivativeRealization.qgFixing_gaugeField_eq_zero_iff
#audit_axioms BookProof.QgDerivativeRealization.qgFixing_gaugeField_ne_zero_of_not_fixed
#audit_axioms BookProof.QgDerivativeRealization.qgFixing_B_ne_zero
#audit_axioms BookProof.QgDerivativeRealization.qgSystemOf_gaugeField_eq_zero
#audit_axioms BookProof.QgDerivativeRealization.qgFixing_lagrange_term_zero
#audit_axioms BookProof.QgDerivativeRealization.qgFixing_L_gf_constraint_surface

-- `ChapterSirkBandLedger` (plan QYM-1 task 1): the emitted bands are nested-compatible
-- enclosures.  The exact-decimal band ledger and its reader, the decidable compatibility
-- check (same operator, orders in sequence, mesh refinement, each band an enclosure), the
-- nesting theorem, what a finite ledger cannot certify (width collapse), and the two
-- compositions with `ChapterBandEnclosure`.
#audit_axioms BookProof.SirkBandLedger.Decimal.leB_iff
#audit_axioms BookProof.SirkBandLedger.ledgerWf_sameOp
#audit_axioms BookProof.SirkBandLedger.ledgerWf_order
#audit_axioms BookProof.SirkBandLedger.ledgerWf_step
#audit_axioms BookProof.SirkBandLedger.loQ_monotone
#audit_axioms BookProof.SirkBandLedger.hiQ_antitone
#audit_axioms BookProof.SirkBandLedger.nestedBands_of_wf
#audit_axioms BookProof.SirkBandLedger.ledgerLo_le_ledgerHi
#audit_axioms BookProof.SirkBandLedger.ledger_width_eventually_const
#audit_axioms BookProof.SirkBandLedger.ledger_width_tendsto_zero_iff
#audit_axioms BookProof.SirkBandLedger.ritz_band_enclosure_of_ledger
#audit_axioms BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger
#audit_axioms BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger_lo_zero
#audit_axioms BookProof.SirkBandLedger.formatExampleLedger_parse
#audit_axioms BookProof.SirkBandLedger.formatExampleLedger_wf
#audit_axioms BookProof.SirkBandLedger.formatExampleLedger_nested

-- `ChapterTruncationGapLift` (plan QYM-1 task 2): the truncated → infinite lift.
#audit_axioms BookProof.TruncationGapLift.galerkinSpan_sup_tailSpan
#audit_axioms BookProof.TruncationGapLift.inner_eq_zero_of_mem_galerkin_tail
#audit_axioms BookProof.TruncationGapLift.norm_add_sq_of_galerkin_tail
#audit_axioms BookProof.TruncationGapLift.exists_galerkin_tail_decomp
#audit_axioms BookProof.TruncationGapLift.quadForm_add_of_symmetricOn
#audit_axioms BookProof.TruncationGapLift.gap_of_uniform_truncated_gap
#audit_axioms BookProof.TruncationGapLift.gap_of_level_gap_and_tail
#audit_axioms BookProof.TruncationGapLift.gap_of_level_gap_and_tail_decoupled
#audit_axioms BookProof.TruncationGapLift.quadForm_ge_of_le_ritzInf_on
#audit_axioms BookProof.TruncationGapLift.gap_of_le_ritzInf_and_tail
#audit_axioms BookProof.TruncationGapLift.ym_fock_gap_of_truncated_gap_and_tail
#audit_axioms BookProof.TruncationGapLift.ym_fock_mass_gap_of_truncated_gap_and_tail
#audit_axioms BookProof.TruncationGapLift.ym_fock_gap_of_band_and_tail

-- `ChapterSchurGershgorinGap` (plan QYM-1 task 3): the tail and coupling inputs of the lift,
-- proved from the recorded matrix elements (Gershgorin dominance and the Schur test).
#audit_axioms BookProof.SchurGershgorin.entry_conj
#audit_axioms BookProof.SchurGershgorin.norm_entry_symm
#audit_axioms BookProof.SchurGershgorin.exists_repr_of_mem_span_image
#audit_axioms BookProof.SchurGershgorin.norm_sq_sum
#audit_axioms BookProof.SchurGershgorin.inner_sum_apply_sum
#audit_axioms BookProof.SchurGershgorin.quadForm_sum
#audit_axioms BookProof.SchurGershgorin.sum_off_diag_comm
#audit_axioms BookProof.SchurGershgorin.quadForm_sum_ge
#audit_axioms BookProof.SchurGershgorin.quadForm_ge_of_gershgorin_on
#audit_axioms BookProof.SchurGershgorin.quadForm_ge_of_gershgorin
#audit_axioms BookProof.SchurGershgorin.tail_coercive_of_gershgorin
#audit_axioms BookProof.SchurGershgorin.abs_inner_block_le
#audit_axioms BookProof.SchurGershgorin.coupling_bound_of_schur
#audit_axioms BookProof.SchurGershgorin.gap_of_level_gap_and_matrix_bounds
#audit_axioms BookProof.SchurGershgorin.strict_pos_of_matrix_bounds
#audit_axioms BookProof.SchurGershgorin.ym_fock_gap_of_truncated_gap_and_matrix_bounds
#audit_axioms BookProof.SchurGershgorin.ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds

-- `ChapterWallDeficiencyObstruction` (plan QG-2, "Case B"): the deficiency space of
-- `−d²/dx² + V` on the compactly supported smooth core *is* its space of `L²` classical
-- solutions, in both directions, with a worked non-vacuous instance.
#audit_axioms BookProof.WallDeficiencyObstruction.integral_conj_deriv2_mul
#audit_axioms BookProof.WallDeficiencyObstruction.inner_eq_of_ode
#audit_axioms BookProof.WallDeficiencyObstruction.not_deficiencyTrivialAt_of_l2_solution
#audit_axioms BookProof.WallDeficiencyObstruction.deficiencyTrivialAt_iff_no_l2_solution
#audit_axioms BookProof.WallDeficiencyObstruction.isL2Ode_conj
#audit_axioms BookProof.WallDeficiencyObstruction.deficiencyTrivialAt_conj_iff
#audit_axioms BookProof.WallDeficiencyObstruction.not_essentiallySelfAdjointOn_of_l2_solution
#audit_axioms BookProof.WallDeficiencyObstruction.no_l2_solution_of_nonneg
#audit_axioms BookProof.WallDeficiencyObstruction.gaussianState_isL2Ode
#audit_axioms BookProof.WallDeficiencyObstruction.not_deficiencyTrivialAt_harmonicShifted_zero

-- `ChapterLimitCircleExample` (plan QG-2 sign warning, Case B): an explicit smooth real
-- potential, with an explicit square-integrable solution at `z = i`, for which essential
-- self-adjointness on the compactly supported smooth core fails.
#audit_axioms BookProof.LimitCircleExample.lcSol_isL2Ode
#audit_axioms BookProof.LimitCircleExample.lcV_not_deficiencyTrivialAt_I
#audit_axioms BookProof.LimitCircleExample.lcV_not_deficiencyTrivialAt_negI
#audit_axioms BookProof.LimitCircleExample.lcV_not_essentiallySelfAdjoint
#audit_axioms BookProof.LimitCircleExample.exists_smooth_potential_not_essentiallySelfAdjoint


end BookProof.ChapterRoadmapAudit
