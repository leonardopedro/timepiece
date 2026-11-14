/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle
-/
import BookProof.RoadmapAudit.ChapterRoadmapAuditImports

/-!
# Roadmap headline certificate — audit ledger, slice 6 of 8

Slice 6 of the eight slices of the `#audit_axioms` ledger that used to sit at the end of
`BookProof/RoadmapAudit/ChapterRoadmapAudit.lean`.  The directives are the original ones,
verbatim and in the original order; the split exists only so that Lake elaborates eight modules in
parallel instead of one, which is where the aggregate build's 25 minutes went.

Each line prints the stock `'name' depends on axioms: [...]` line for one declaration; nothing
here asserts an axiom set.
-/

namespace BookProof.ChapterRoadmapAudit

open BookProof.AxiomAudit

-- The concrete 3D gauge-fixed *gravity* field-space wave (plan §10.6.2 item 4, QG Part F):
-- the densitized-tetrad Hamiltonian on the Gauss–polynomial core of `L²(ℝ⁸⁴)`, and the BRST
-- charge with `ℤ₂¹⁹` ghosts on the graded space `ℂ[x₀,…,x₈₃] ⊗ Λ(ℂ¹⁹)`.
#audit_axioms BookProof.QuantumGravity3DGauge.qg3DDensity_densitized
#audit_axioms BookProof.QuantumGravity3DGauge.qgCCR
#audit_axioms BookProof.QuantumGravity3DGauge.qgKappa_indefinite
#audit_axioms BookProof.QuantumGravity3DGauge.qg3D_symmetricOn
#audit_axioms BookProof.QuantumGravity3DGauge.qg3D_quadForm
#audit_axioms BookProof.QuantumGravity3DGauge.qg3DElliptic_friedrichs_extension
#audit_axioms BookProof.QuantumGravity3DGauge.qg3DElliptic_hashimoto_selects
-- `ChapterQg3DGaugeEsa` (plan §10.2b): the same field-space Hamiltonian is quadratic in
-- the canonical pair, hence essentially self-adjoint on the Gauss–polynomial core for every
-- real signature — the physical hyperbolic one included — with its Stone flow.
#audit_axioms BookProof.Qg3DGaugeEsa.sum_torsionVec_X
#audit_axioms BookProof.Qg3DGaugeEsa.qgFqQ_quadratic_eq
#audit_axioms BookProof.Qg3DGaugeEsa.qgSignedPoly_eq_fqPoly
#audit_axioms BookProof.Qg3DGaugeEsa.qgSigned_eq_fqOp
#audit_axioms BookProof.Qg3DGaugeEsa.qgSigned_essentiallySelfAdjointOn_core
#audit_axioms BookProof.Qg3DGaugeEsa.qg3D_essentiallySelfAdjointOn_core
#audit_axioms BookProof.Qg3DGaugeEsa.qg3D_stone_flow
#audit_axioms BookProof.Qg3DGaugeEsa.qg3DElliptic_essentiallySelfAdjointOn_core
#audit_axioms BookProof.QuantumGravityBrstCharge.glin_sq
#audit_axioms BookProof.QuantumGravityBrstCharge.glin_mul_Q_add_Q_mul_glin
#audit_axioms BookProof.QuantumGravityBrstCharge.brst_full_nilpotent
#audit_axioms BookProof.QuantumGravityBrstCharge.brst_abelian_nilpotent
#audit_axioms BookProof.QuantumGravityBrstCharge.elemGen_bracket
#audit_axioms BookProof.QuantumGravityBrstCharge.linGen_bracket
#audit_axioms BookProof.QuantumGravityBrstCharge.ghost_car
#audit_axioms BookProof.QuantumGravityBrstCharge.bosOp_ghostOp_comm
#audit_axioms BookProof.QuantumGravityBrstCharge.qgGhostCar
#audit_axioms BookProof.QuantumGravityBrstCharge.qgBRST_nilpotent
#audit_axioms BookProof.QuantumGravityBrstCharge.qgBRST_abelian_nilpotent
#audit_axioms BookProof.QuantumGravityBrstCharge.affMat_non_abelian
#audit_axioms BookProof.QuantumGravityBrstCharge.affMat_close
#audit_axioms BookProof.QuantumGravityBrstCharge.affF_jacobi
#audit_axioms BookProof.QuantumGravityBrstCharge.affBRST_nilpotent

-- `ChapterQgOneParticleCcEsa` (plan §10.6.1 / §10.6.2 item 2): the same `R + αR²` class on
-- the *compactly supported smooth* core `C_c^∞`, obtained from the Hermite-core theorem by a
-- graph-norm cut-off transfer, together with the conformal mode, the reduced sector, the
-- `n`-particle sector and the finite-particle Fock space.
#audit_axioms BookProof.QgOneParticleCc.deficiencyTrivialAt_of_graphApprox
#audit_axioms BookProof.QgOneParticleCc.essentiallySelfAdjointOn_of_graphApprox
#audit_axioms BookProof.QgOneParticleCc.ccHam_symmetricOn
#audit_axioms BookProof.QgOneParticleCc.exists_cc_graph_approx
#audit_axioms BookProof.QgOneParticleCc.ccHam_essentiallySelfAdjoint_of_core
#audit_axioms BookProof.QgOneParticleCc.qgOneParticleCc_esa
#audit_axioms BookProof.QgOneParticleCc.qgOneParticleCc_stone_flow
#audit_axioms BookProof.QgOneParticleCc.confVCc_esa
#audit_axioms BookProof.QgOneParticleCc.confVCc_stone_flow
#audit_axioms BookProof.QgOneParticleCc.sectorQuadCc_esa
#audit_axioms BookProof.QgOneParticleCc.sectorQuadCc_stone_flow
#audit_axioms BookProof.QgOneParticleCc.sum_harmW_partLM
#audit_axioms BookProof.QgOneParticleCc.qgNParticleCc_esa
#audit_axioms BookProof.QgOneParticleCc.qgFockCc_esa
#audit_axioms BookProof.QgOneParticleCc.qgFockCc_stone_flow

-- `ChapterQuantumGravityFock` (plan §10.6.2 item 3, QG Part E): the graded Fock space
-- `Γˢ ⊗ Γᵃ` of the book's gravity Hilbert space — the fermionic (ghost) CAR half, the `ℤ₂`
-- grading and superbracket, the graded state space with its canonical relations, and the
-- essential self-adjointness (plus unitary group) of the graded Fock Hamiltonian.
#audit_axioms BookProof.QuantumGravityFock.qgCCR_bose
#audit_axioms BookProof.QuantumGravityFock.fermAnn_apply
#audit_axioms BookProof.QuantumGravityFock.fermCre_apply
#audit_axioms BookProof.QuantumGravityFock.car_fermAnn_fermCre
#audit_axioms BookProof.QuantumGravityFock.car_fermAnn_fermCre_of_ne
#audit_axioms BookProof.QuantumGravityFock.car_fermAnn_fermAnn
#audit_axioms BookProof.QuantumGravityFock.car_fermCre_fermCre
#audit_axioms BookProof.QuantumGravityFock.fermAnn_comp_self
#audit_axioms BookProof.QuantumGravityFock.fermCre_comp_self
#audit_axioms BookProof.QuantumGravityFock.inner_fermCre_left
#audit_axioms BookProof.QuantumGravityFock.fermGrade_involutive
#audit_axioms BookProof.QuantumGravityFock.fermGrade_fermAnn
#audit_axioms BookProof.QuantumGravityFock.fermGrade_fermCre
#audit_axioms BookProof.QuantumGravityFock.superBracket_fermAnn_fermCre
#audit_axioms BookProof.QuantumGravityFock.superBracket_bosOp_ghostOp
#audit_axioms BookProof.QuantumGravityFock.bosOp_ghostOp_comm
#audit_axioms BookProof.QuantumGravityFock.qgCCR
#audit_axioms BookProof.QuantumGravityFock.qgGhostCar
#audit_axioms BookProof.QuantumGravityFock.qgGhostCar_book
#audit_axioms BookProof.QuantumGravityFock.qgGrade_involutive
#audit_axioms BookProof.QuantumGravityFock.bosOp_even
#audit_axioms BookProof.QuantumGravityFock.ghostOp_odd_ann
#audit_axioms BookProof.QuantumGravityFock.ghostOp_odd_cre
#audit_axioms BookProof.QuantumGravityFock.qgGradedFock_esa
#audit_axioms BookProof.QuantumGravityFock.qgGradedFock_stone_flow
#audit_axioms BookProof.QuantumGravityFock.qgGradedFock_not_bounded
#audit_axioms BookProof.QuantumGravityFock.qgDGamma_esa
#audit_axioms BookProof.QuantumGravityFock.qgTwoLevel_esa
#audit_axioms BookProof.QuantumGravityFock.qgFock_hashimoto_selects

-- `ChapterQgBrstCompleted` (plan §10.6.2 item 4, the remaining join): the bounded nilpotent
-- BRST charge on the *completed* graded Hilbert space `ℓ²(GradedIdx)`, an explicit commuting
-- unitary group, and the resulting BRST-reduced transfer.
#audit_axioms BookProof.QgBrstCompleted.tsum_sq_weighted_le
#audit_axioms BookProof.QgBrstCompleted.wshift_norm_le
#audit_axioms BookProof.QgBrstCompleted.wshift_norm_eq
#audit_axioms BookProof.QgBrstCompleted.brstTerm_norm_le
#audit_axioms BookProof.QgBrstCompleted.brstTerm_comp_self
#audit_axioms BookProof.QgBrstCompleted.brstTerm_anticomm
#audit_axioms BookProof.QgBrstCompleted.qgBrstCharge_nilpotent
#audit_axioms BookProof.QgBrstCompleted.qgBrstCharge_ne_zero
#audit_axioms BookProof.QgBrstCompleted.qgPhase_zero
#audit_axioms BookProof.QgBrstCompleted.qgPhase_group
#audit_axioms BookProof.QgBrstCompleted.qgPhase_isometry
#audit_axioms BookProof.QgBrstCompleted.qgPhase_single
#audit_axioms BookProof.QgBrstCompleted.qgPhase_comm_brst
#audit_axioms BookProof.QgBrstCompleted.qgBrstCharge_one_ghost_zero
#audit_axioms BookProof.QgBrstCompleted.qgPhaseFull_isometry
#audit_axioms BookProof.QgBrstCompleted.qgPhaseFull_not_comm_brst
#audit_axioms BookProof.QgBrstCompleted.qgExact_le_physical
#audit_axioms BookProof.QgBrstCompleted.qgPhase_mem_physicalStates
#audit_axioms BookProof.QgBrstCompleted.qgPhase_mem_exactStates
#audit_axioms BookProof.QgBrstCompleted.qgBrstTransfer_zero
#audit_axioms BookProof.QgBrstCompleted.qgBrstTransfer_comp
#audit_axioms BookProof.QgBrstCompleted.qgBrstTransfer_bijective
#audit_axioms BookProof.QgBrstCompleted.qgBrstTransfer_infDist

-- `ChapterWeakSecondDerivative` (plan §10.6.1 / §10.6.2 item 2, the analytic input): the
-- one-dimensional distributional regularity toolkit — du Bois-Reymond, integration by parts
-- against the primitive of a locally integrable function, and the upgrade of an `L¹_loc`
-- weak solution of `u'' = c·u` to a genuine `C²` solution.
#audit_axioms BookProof.WeakSecondDeriv.exists_antideriv
#audit_axioms BookProof.WeakSecondDeriv.ae_eq_const_of_integral_deriv_smul_eq_zero
#audit_axioms BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero
#audit_axioms BookProof.WeakSecondDeriv.integral_deriv_mul_indefiniteIntegral
#audit_axioms BookProof.WeakSecondDeriv.integral_deriv2_mul_doubleAntideriv
#audit_axioms BookProof.WeakSecondDeriv.exists_ae_eq_doubleAntideriv_add_affine
#audit_axioms BookProof.WeakSecondDeriv.exists_deriv2_of_weak_eq

-- `ChapterScalaronWallEsa` (plan §10.6.1 / §10.6.2 item 2, the last open piece): the
-- non-perturbative route to the exponentially growing scalaron wall.  `−d²/dx² + V` is
-- essentially self-adjoint on the compactly supported smooth core of `L²(ℝ)` for every
-- smooth `V ≥ 0`, because a deficiency vector's modulus square is convex, non-negative and
-- integrable, hence zero.
#audit_axioms BookProof.ScalaronWallEsa.eq_zero_of_convexOn_nonneg_integrable
#audit_axioms BookProof.ScalaronWallEsa.ode_solution_eq_zero
#audit_axioms BookProof.ScalaronWallEsa.wallHam_symmetricOn
#audit_axioms BookProof.ScalaronWallEsa.wallHam_weak_eq
#audit_axioms BookProof.ScalaronWallEsa.wallHam_deficiencyTrivialAt
#audit_axioms BookProof.ScalaronWallEsa.wallHam_essentiallySelfAdjoint
#audit_axioms BookProof.ScalaronWallEsa.starobinskyWall_esa
#audit_axioms BookProof.ScalaronWallEsa.starobinskyWall_stone_flow

-- `ChapterSirkPerSystemFlowBound` (plan §12.4): the per-system end-to-end flow bound —
-- the assembly of `ChapterSirkEndToEnd` evaluated on the Crouzeix domain that
-- `ChapterSirkPerSystem` fixes for each physical shift-invert, with the two adjoint side
-- conditions derived from isometry alone and the order-`m` data bundled.  Crouzeix's
-- inequality and the `e^{−hm}` deformation stay named hypotheses (fields `cxX`, `cxB`).
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.norm_adjoint_apply_le_of_isometry
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_tendsto
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.isSirkScheme_trivial
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_tendsto_zero
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.ns_sirk_flow_error_bound
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.nsDiff_sirk_flow_error_bound
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.lagrangian_sirk_flow_error_bound
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.diagKR_sirk_flow_error_bound
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_bound
#audit_axioms BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_tendsto_zero

-- `ChapterSchrodingerCutoffEsa` (the Simader–Faris–Lavine cutoff / commutator energy
-- method in one dimension): the smooth rescaled cutoff with `|χ_R'| ≤ C/R`, the operator
-- `-f'' + V f` on the compactly supported twice-differentiable core and its symmetry, the
-- cutoff energy estimate in both its core and its `Re z + 1 ≤ V` forms, the `R → ∞` limit,
-- and the applications to `V(x) = eˣ + e⁻ˣ` and to the free Laplacian.
#audit_axioms BookProof.SchrodingerCutoff.integral_deriv_eq_zero_of_hasCompactSupport
#audit_axioms BookProof.SchrodingerCutoff.exists_scaled_cutoff
#audit_axioms BookProof.SchrodingerCutoff.schrodingerOp_symmetric
#audit_axioms BookProof.SchrodingerCutoff.cutoff_energy_core
#audit_axioms BookProof.SchrodingerCutoff.cutoff_energy_estimate
#audit_axioms BookProof.SchrodingerCutoff.l2_classical_solution_eq_zero
#audit_axioms BookProof.SchrodingerCutoff.l2_classical_solution_eq_zero_of_nonneg
#audit_axioms BookProof.SchrodingerCutoff.laplacian_deficiency_trivial
#audit_axioms BookProof.SchrodingerCutoff.laplacian_deficiency_trivial_I
#audit_axioms BookProof.SchrodingerCutoff.laplacian_deficiency_trivial_negI
#audit_axioms BookProof.SchrodingerCutoff.schrodinger_exp_deficiency_trivial
#audit_axioms BookProof.SchrodingerCutoff.schrodinger_exp_deficiency_trivial_I
#audit_axioms BookProof.SchrodingerCutoff.schrodinger_exp_deficiency_trivial_negI

-- `ChapterWallEsaSemibounded` (plan §9 item 1, the packaging lemma): the Green identity on
-- the compactly supported smooth core, and the semiboundedness of the quadratic form of
-- `−d²/dx² + V` when `V` is bounded below.
#audit_axioms BookProof.WallEsaSemibounded.integral_conj_neg_deriv2_mul
#audit_axioms BookProof.WallEsaSemibounded.kinCcR_quadratic_form
#audit_axioms BookProof.WallEsaSemibounded.opCc_quadratic_form
#audit_axioms BookProof.WallEsaSemibounded.ccEquiv_norm_sq
#audit_axioms BookProof.WallEsaSemibounded.wallHamBddBelow_semibounded
#audit_axioms BookProof.WallEsaSemibounded.wallHam_nonneg_form

-- `ChapterExpPotentialEsa`: essential self-adjointness of `−d²/dx² + (eˣ + e⁻ˣ)` on the
-- compactly supported smooth core, its unitary flow, the `cosh` restatement, and the
-- non-negativity of its quadratic form.
#audit_axioms BookProof.ExpPotentialEsa.expPotential_esa
#audit_axioms BookProof.ExpPotentialEsa.expPotential_stone_flow
#audit_axioms BookProof.ExpPotentialEsa.coshPotential_esa
#audit_axioms BookProof.ExpPotentialEsa.expPotential_semibounded

-- `ChapterSirkFinitePrecision` (plan §13.3, T1–T5): the finite-precision certificate
-- layer — the a-posteriori Rayleigh–Ritz residual bound, the eigendecomposition backward
-- error with Weyl, Temple's inequality, the observable propagation and the verified
-- interval core.
#audit_axioms BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual
#audit_axioms BookProof.SirkFinitePrecision.backward_error_weyl
#audit_axioms BookProof.SirkFinitePrecision.backward_error_weyl_symm
#audit_axioms BookProof.SirkFinitePrecision.ground_le_rayleigh
#audit_axioms BookProof.SirkFinitePrecision.temple_lower_bound
#audit_axioms BookProof.SirkFinitePrecision.ground_ge_of_no_eigenvalue_below
#audit_axioms BookProof.SirkFinitePrecision.observable_propagation
#audit_axioms BookProof.SirkFinitePrecision.observable_propagation_band
#audit_axioms BookProof.SirkFinitePrecision.CertInterval.mem_mul
#audit_axioms BookProof.SirkFinitePrecision.CertInterval.mem_widen
#audit_axioms BookProof.SirkFinitePrecision.CertInterval.mem_ofRounded
#audit_axioms BookProof.SirkFinitePrecision.CertInterval.dist_le_width
#audit_axioms BookProof.SirkFinitePrecision.CertInterval.mem_evalHorner
#audit_axioms BookProof.SirkFinitePrecision.CertInterval.abs_polyEval_le_of_mem

-- `ChapterSirkCertifiedGap` (plan §13.3, T6/T7 and the nested-selection lemma): the exact
-- parity split, the sector ground energy, the certified-gap theorem and the stopping rule,
-- all about the *truncated* Hamiltonian.
#audit_axioms BookProof.SirkCertifiedGap.paritySector_invariant
#audit_axioms BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric
#audit_axioms BookProof.SirkCertifiedGap.sectorGround_le_rayleigh
#audit_axioms BookProof.SirkCertifiedGap.sectorGround_eq_inf_eigenvalues
#audit_axioms BookProof.SirkCertifiedGap.sectorGround_ge_temple
#audit_axioms BookProof.SirkCertifiedGap.certified_parity_gap
#audit_axioms BookProof.SirkCertifiedGap.certified_parity_gap_pos
#audit_axioms BookProof.SirkCertifiedGap.certified_parity_gap_strong_coupling
#audit_axioms BookProof.SirkCertifiedGap.rayleigh_odd_ge_of_certified
#audit_axioms BookProof.SirkCertifiedGap.resolvent_commutes_parity
#audit_axioms BookProof.SirkCertifiedGap.resolvent_mapsTo_paritySector
#audit_axioms BookProof.SirkCertifiedGap.certifiedGap_tendsto
#audit_axioms BookProof.SirkCertifiedGap.certifiedGap_eventually_pos
#audit_axioms BookProof.SirkCertifiedGap.certifiedGap_sound
#audit_axioms BookProof.SirkCertifiedGap.gap_ge_of_certificate
#audit_axioms BookProof.SirkCertifiedGap.qcdG2M4_certified_gap

-- `ChapterSirkCertificateReader` (plan §13.7, T8): the instantiation seam — exact decimal
-- parsing of the emitted NDJSON certificate and T6 consumed through it.
#audit_axioms BookProof.SirkCertificateReader.parseDec_example
#audit_axioms BookProof.SirkCertificateReader.parseDec_reject
#audit_axioms BookProof.SirkCertificateReader.toGapCertificate_lower
#audit_axioms BookProof.SirkCertificateReader.gap_ge_of_ndjson
#audit_axioms BookProof.SirkCertificateReader.gap_pos_of_ndjson
#audit_axioms BookProof.SirkCertificateReader.formatExample_parse
#audit_axioms BookProof.SirkCertificateReader.formatExample_lower
#audit_axioms BookProof.SirkCertificateReader.formatExample_certified_gap

-- `ChapterSirkGapTable` (plan §13.7, T11/T12): the two-sided certified enclosure, the
-- per-coupling table with its strong-coupling consistency check, and the Richardson
-- extrapolation with its error propagation.
#audit_axioms BookProof.SirkGapTable.gap_le_of_certificate
#audit_axioms BookProof.SirkGapTable.certified_gap_mem_interval
#audit_axioms BookProof.SirkGapTable.certified_gap_table
#audit_axioms BookProof.SirkGapTable.certified_gap_table_interval
#audit_axioms BookProof.SirkGapTable.strongCoupling_lt
#audit_axioms BookProof.SirkGapTable.strongCoupling_mem_of_certificate
#audit_axioms BookProof.SirkGapTable.qcdG2M4Row_lo
#audit_axioms BookProof.SirkGapTable.qcdG2M4_strongCoupling_consistent
#audit_axioms BookProof.SirkGapTable.richardson_exact
#audit_axioms BookProof.SirkGapTable.richardson_error
#audit_axioms BookProof.SirkGapTable.richardson_qym_g4

-- `ChapterSpectralGapStability` (plan §13.7, the abstract core of the continuum leg): a
-- quantitative spectral gap degrades by at most the perturbation, survives an
-- operator-norm limit, and keeps the point out of the spectrum of a bounded self-adjoint
-- operator.
#audit_axioms BookProof.SpectralGapStability.gapAt_perturb
#audit_axioms BookProof.SpectralGapStability.gapAt_of_tendsto
#audit_axioms BookProof.SpectralGapStability.notMem_spectrum_of_gapAt
#audit_axioms BookProof.SpectralGapStability.exists_gapAt_of_notMem_spectrum
#audit_axioms BookProof.SpectralGapStability.notMem_spectrum_of_uniform_gap
#audit_axioms BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window

-- `ChapterFockOneParticleGap` (plan, top work package): the one-particle positive
-- spectral-edge enclosure and its free `dGamma` lift.  Diagonal second quantization,
-- vacuum energy zero, the number-operator shift, the Fock gap from `h₊ ≥ μI`, the
-- nested-band limit, and the composition (conditional on the enclosure hypothesis).
#audit_axioms BookProof.FockOneParticleGap.dGamma_diagCol_single
#audit_axioms BookProof.FockOneParticleGap.dGamma_diagCol_apply
#audit_axioms BookProof.FockOneParticleGap.dGamma_diagCol_vac
#audit_axioms BookProof.FockOneParticleGap.numberOp_vac
#audit_axioms BookProof.FockOneParticleGap.dGamma_diagCol_one_particle
#audit_axioms BookProof.FockOneParticleGap.dGamma_diagCol_shift
#audit_axioms BookProof.FockOneParticleGap.fock_gap_quadForm
#audit_axioms BookProof.FockOneParticleGap.fock_gap_of_one_particle_gap
#audit_axioms BookProof.FockOneParticleGap.fock_energy_one_particle
#audit_axioms BookProof.FockOneParticleGap.sInf_nonvacuumEnergies
#audit_axioms BookProof.FockOneParticleGap.one_particle_edge_ge_of_parity_certificate
#audit_axioms BookProof.FockOneParticleGap.band_endpoints_tendsto
#audit_axioms BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands
#audit_axioms BookProof.FockOneParticleGap.qcdG2M4_fock_gap_of_one_particle_enclosure
#audit_axioms BookProof.FockOneParticleGap.le_eigenvalue_of_le_spectrum
#audit_axioms BookProof.FockOneParticleGap.fock_gap_of_operator_spectral_edge
#audit_axioms BookProof.FockOneParticleGap.fock_mass_gap_of_certified_bands_operator

-- `ChapterFriedrichsFormGap` and `ChapterBandEnclosure` (plan, top work package): the
-- band-enclosure hypothesis is no longer assumed.  Nested bands plus convergence of the
-- approximants give the enclosure; the Hashimoto/Galerkin Ritz theorems supply the
-- convergence, for the bounded selected operator (spectral edge) and for the unbounded
-- Friedrichs extension (energy form).
#audit_axioms BookProof.FriedrichsFormGap.formSpace_norm_bound
#audit_axioms BookProof.FriedrichsFormGap.friedrichs_quadForm_lower_bound
#audit_axioms BookProof.FriedrichsFormGap.friedrichs_extension_form_gap
#audit_axioms BookProof.BandEnclosure.nestedBands_le
#audit_axioms BookProof.BandEnclosure.band_enclosure_of_nested
#audit_axioms BookProof.BandEnclosure.band_limit_unique
#audit_axioms BookProof.BandEnclosure.band_enclosure_endpoints_tendsto
#audit_axioms BookProof.BandEnclosure.sirk_nestedBands
#audit_axioms BookProof.BandEnclosure.sirk_band_widths_tendsto_zero
#audit_axioms BookProof.BandEnclosure.sirk_band_enclosure
#audit_axioms BookProof.BandEnclosure.ritz_band_enclosure_of_nested
#audit_axioms BookProof.BandEnclosure.fock_mass_gap_of_nested_ritz_bands
#audit_axioms BookProof.BandEnclosure.quadForm_ge_of_le_ritzInf
#audit_axioms BookProof.BandEnclosure.friedrichs_form_gap_of_nested_ritz_bands
#audit_axioms BookProof.BandEnclosure.shiftInvert_band_enclosure
#audit_axioms BookProof.BandEnclosure.shiftInvert_widths_tendsto_zero

-- `ChapterRitzCertificate` (plan, top work package): the per-order finite certificate is
-- no longer an input.  Temple's inequality turns the finite Rayleigh quotient and residual
-- into a two-sided enclosure of the spectral edge of the infinite operator, and the running
-- intersection makes any family of emitted bands nested.
#audit_axioms BookProof.RitzCertificate.norm_apply_sq
#audit_axioms BookProof.RitzCertificate.re_inner_factor
#audit_axioms BookProof.RitzCertificate.factor_nonneg
#audit_axioms BookProof.RitzCertificate.factor_nonneg_of_separation
#audit_axioms BookProof.RitzCertificate.temple_lower_bound
#audit_axioms BookProof.RitzCertificate.sInf_spectrum_le_rayleigh
#audit_axioms BookProof.RitzCertificate.temple_band_mem
#audit_axioms BookProof.RitzCertificate.temple_width_tendsto_zero
#audit_axioms BookProof.RitzCertificate.runBands_nested
#audit_axioms BookProof.RitzCertificate.mem_runBand
#audit_axioms BookProof.RitzCertificate.runBand_widths_tendsto_zero
#audit_axioms BookProof.RitzCertificate.nested_certificate_of_bands
#audit_axioms BookProof.RitzCertificate.temple_nested_certificate
#audit_axioms BookProof.RitzCertificate.fock_mass_gap_of_temple_certificates


end BookProof.ChapterRoadmapAudit
