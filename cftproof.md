# Euclidean fields, Mehler coordinates and nested-Fock reconstruction

## Current continuum work order · 2026-11-26

The October archive proves existence of a Wilson family with a compatible extracted
hierarchy and the reconstruction properties in its public statement. Its quantifiers
allow choices of extraction and phase. Uniqueness of a vacuum within a reconstructed
representation leaves uniqueness across candidate continuum theories open. The
outstanding existence question here is whether the specified continuous-momentum
nested-Fock Hamiltonian and state produce that selected hierarchy.
[Existence proof](../OpenAI-YM-20261028/Solution.lean) ·
[Quantifiers](../OpenAI-YM-20261028/ChallengeSpec.lean)

1. **Compare an observable before identifying two theories.** Fix the Wilson family,
   extraction order, phase, token, test normalization and time reflection from one
   witness. Use `YangMills.moment_eq` to express
   a finite Wilson moment in archive variables, then `wilsonLimit` for its ordered
   extraction. On the nested side choose the corresponding gauge-invariant smeared
   observable and a populated stationary state. Compare the centered pair at separated
   positive times. Record a bound on their difference in the same tests as the mesh
   tends to zero and the volume grows in the archive order. The trace test includes
   its own centering and short-distance normalization. A cubic magnetic packet entry
   alone cannot realize it. Extend the comparison to a generating positive-time
   algebra before constructing an OS isometry.
   [Wilson moment identity](../OpenAI-YM-20261028/WilsonBridge.lean) ·
   [Hierarchy extraction](../OpenAI-YM-20261028/HierarchyBridge.lean) ·
   [Trace test](../OpenAI-YM-20261028/TraceBridge.lean)

2. **Keep three convergence questions distinct.** The free Mehler kernel composes
   exactly at fixed finite times. An infinite sequence of discrete transitions exists,
   and finite path measures admit a positive Strang weight and a domination estimate.
   For an interacting continuous-time measure, identify all the required cylinder
   marginals, prove convergence of the weights and identify the limiting semigroup on
   the physical form domain. A bound on a shifted SIRK solve at one regulator controls
   its numerical error. Removing the spatial and volume regulators still requires
   estimates uniform in the observable tests. Bałaban blocking and large-field bounds
   are candidates for that last step once their insertions and scale conventions match.
   [Free kernel](BookProof/ReflectionPositivity/ChapterMehlerKernelSemigroup.lean) ·
   [Discrete trajectories](BookProof/OSReconstruction/ChapterMehlerTrajMeasure.lean) ·
   [Weighted paths](BookProof/OSReconstruction/ChapterWeightedPathMeasure.lean)

3. **Transport the entire stationary space.** Given a surjective isometry intertwining
   forward semigroups, `map_stationary_space` identifies subspaces characterized by
   stationarity at all nonnegative times. `ground_projection_error_eq` then gives
   equality of the two operator norms of heat flow minus stationary projection, at
   every such time. This includes ground degeneracy. For a nonnegative self-adjoint
   relative generator this is the quantity that tests exponential decay on the ground
   complement. The older contraction estimate toward a *single vector* imposes a
   different condition on a linear semigroup. Testing it on the zero input forces
   that vector to vanish as soon as the contraction factor drops below one. A physical application requires the
   actual bridge, generator and decay bound. The three-profile mass estimate applies
   in its occupied packet sector; it provides no value for this continuum decay rate.
   [Projection transport](BookProof/OSReconstruction/ChapterBridgeGapInvariance.lean) ·
   [Generator on differentiable orbits](BookProof/OSReconstruction/ChapterGeneratorTransport.lean) ·
   [Spectral work order](softmodes.md)

## Path-integral–Hamiltonian equivalence in the nested Fock / Mehler / SIRK formalism (2026-11-24)

**Strategy update.** This section updates the forward execution plan to follow the two-part
Hamiltonian-to-path-integral equivalence strategy of [cft_path.md](cft_path.md), adapted to the
nested Fock-space, Mehler-coordinate and SIRK formalism of [book.tex](book.tex) and the existing
`BookProof` corpus. It complements—rather than discards—the Bałaban/October-archive continuum-limit
programme (**C0–C10** and the 2026-11-24 work order below): **H0–H6** construct the regulated
Hamiltonian $\leftrightarrow$ Euclidean path-integral bridge, its SIRK certification and its
broken-phase vacuum-projection control directly from $H_\sigma = d\Gamma(h_\sigma)$, while
**H7 / C3–C9** handle UV/IR cutoff removal, archive compatibility, OS reconstruction and spectral
gap transfer. No Lean compilation, proof replay or numerical run is performed by this planning
update.

### Why the textbook derivation must be adapted to this formalism

[cft_path.md](cft_path.md) lays out two classical pillars:
(I) time-slicing $e^{-i\hat{H}T/\hbar}$ (or its Euclidean Wick-rotated semigroup $e^{-T\hat{H}}$)
via the Lie–Trotter product formula, inserting complete sets of position and momentum eigenstates
$|q_j\rangle, |p_j\rangle$, integrating out the Gaussian momentum variables, taking $N \to \infty$
with midpoint/Weyl ordering for position–momentum cross-terms; and
(II) projecting onto vacuum expectation values by Euclidean damping $e^{-T\hat{H}}$ at
$\tau = \pm T$, which **fails** in infinite spatial volume $V_3 \to \infty$ whenever the true
vacuum has a non-zero VEV ($\langle\Omega_v|\phi=0\rangle \propto e^{-c v^2 V_3} \to 0$) unless
equivalence is restored by shifting the field ($\phi = v + h$) or by adding an external source $J$
with the strict limit order $V_3 \to \infty$ **before** $J \to 0^+$.

Adapting both pillars honestly to [book.tex](book.tex) and `BookProof` enforces five structural
rules:

1. **Euclidean Feynman–Kac, not a $\sigma$-additive Minkowski path measure.**
   [book.tex](book.tex) explicitly rejects the oscillatory Minkowski Feynman path integral as a
   $\sigma$-additive measure ("not an integral", §*Quantization due to time-evolution*), while
   identifying imaginary-time evolution with a Wiener/Markov stochastic process (§*Reconstructing
   the classical trajectory*) and introducing continuous time-slicing through infinitesimal
   timepiece intervals (§*Statistical Source Field Theory*). Accordingly, the equivalence target
   is the **Euclidean semigroup** $e^{-\tau K_\sigma}$ ($\tau \ge 0$) and its Feynman–Kac /
   Mehler path measure, with real-time unitarity recovered after identifying the self-adjoint
   generator (preserving the 2026-11-08 forward-semigroup correction below).
2. **Time-slicing acts on the *inner* Hamiltonian $h_\sigma$ under $e^{-\tau d\Gamma(h_\sigma)} = \Gamma(e^{-\tau h_\sigma})$.**
   In [book.tex](book.tex) (§*Free field parametrization in Statistical Field Theory*, §*Pure
   SU(3) Yang-Mills theory*) and [ContinuumManifest](BookProof/OSReconstruction/ContinuumManifest.lean),
   the regulated Hamiltonian is outer-quadratic and number-conserving:
   $$H_\sigma = d\Gamma(h_\sigma) = \sum_{ij} \langle e_i, h_\sigma e_j \rangle\, C^\dagger(e_i) A(e_j),$$
   with all interactions living inside the **inner** operator $h_\sigma$. On the empty outer vacuum
   $\Omega_{\text{out}}$, $H_\sigma \Omega_{\text{out}} = 0$ identically; physical observables
   (normalized number-density propositions at resolved spatial supports) act on a **populated
   spatial prior / cyclic initial state** $\Psi_{\text{info}}$ (or $\omega_{\text{info}}$), with
   one outer particle per informed spatial point ([softmodes.md](softmodes.md),
   [ObservablePrior](BookProof/OSReconstruction/ObservablePrior.lean),
   [ContinuumPrior](BookProof/OSReconstruction/ContinuumPrior.lean)).
3. **Mehler/Hermite kernels replace flat $|q\rangle, |p\rangle$ eigenstates.**
   Non-normalizable $|q\rangle, |p\rangle$ eigenstates and divergent Lebesgue prefactors
   $(m/2\pi\epsilon)^{N/2}\prod dq_j$ are replaced by the unitary Mehler bridge
   $U f = \gamma^{1/2} f : L^2(\gamma) \to L^2(dx)$
   ([ChapterYangMillsMehlerBridge](BookProof/Qym/ChapterYangMillsMehlerBridge.lean)) and the
   orthonormal Hermite basis ([ChapterHermiteFunctions](BookProof/Toolbox/ChapterHermiteFunctions.lean),
   [ChapterHermiteProductBasis](BookProof/Toolbox/ChapterHermiteProductBasis.lean)). The free
   Euclidean slice is the **normalized Markovian Mehler semigroup** $T_\rho$ ($\rho = e^{-\epsilon}$,
   [MehlerEigenfunction](BookProof/MCMC/MehlerEigenfunction.lean)), which preserves the Gaussian
   reference probability measure $\gamma$ automatically with no divergent prefactor.
4. **SIRK complements Trotter rather than competing with it.**
   [ChapterSirkSingleTimeShift](BookProof/Sirk/ChapterSirkSingleTimeShift.lean) proves that SIRK
   evaluates the propagator at a **single finite time** using only the bounded shift-invert
   resolvent $(K_\sigma + \gamma)^{-1}$—with **no time discretization and no Trotter splitting**—and
   [ChapterHashimotoShiftInvert](BookProof/Sirk/ChapterHashimotoShiftInvert.lean) proves the
   Galerkin shift-invert limit selects the Friedrichs extension (`hashimoto_shiftInvert_selects_friedrichs`).
   Trotter / Mehler time-slicing therefore supplies the *analytic equivalence* to the Euclidean
   Feynman–Kac measure and reflection positivity, while SIRK supplies *time-discretization-free
   numerical/certified evaluation* and domain selection at fixed cutoffs $(a, L, R)$.
5. **Elitzur's theorem separates gauge symmetry from global/scalar SSB.**
   [book.tex](book.tex) (§*Gauge-variant gaussian measure and the phase diagram*, §*Spontaneous
   symmetry breaking*) and [ChapterGaugeVariantVanishing](BookProof/ChapterGaugeVariantVanishing.lean)
   (`no_spontaneous_gauge_symmetry_breaking`) establish that local/global *gauge* symmetry is never
   spontaneously broken in gauge-invariant expectations, whereas gauge-variant Gaussian reference
   measures and non-invariant cyclic initial states are mathematically valid. The VEV overlap
   catastrophe of [cft_path.md](cft_path.md) applies directly to **global/scalar SSB** (the Higgs
   multiplet of [ChapterSmHiggsVacuum](BookProof/ChapterSmHiggsVacuum.lean) and the $\phi^4$ double
   well of [ChapterScalarMehler](BookProof/Phi4/ChapterScalarMehler.lean)) and to any shifted
   Mehler reference measure $\gamma_v \perp \gamma_0$ in infinite volume.

---

### H0 — Inner/outer semigroup factorization and reference-state contract

*Adapts [cft_path.md](cft_path.md) §1 (Setup) to $H_\sigma = d\Gamma(h_\sigma)$.*

* **Bind the operator split.** Extend `NestedSpec` in
  [ContinuumManifest](BookProof/OSReconstruction/ContinuumManifest.lean) so the specified inner
  Hamiltonian carries an explicit decomposition $h_\sigma = h_{0,\sigma} + V_\sigma$ on a common
  core, where $h_{0,\sigma} \ge 0$ is the Mehler/Dirichlet reference kinetic operator and
  $V_\sigma$ is the interaction (magnetic curvature $B_{ia}^2$ in Weyl-gauge QYM, Higgs/$\phi^4$
  potential, or gauge-covariant matter/vielbein couplings). Retain the exact invariant
  $h_\sigma + cI \mapsto H_\sigma + c N_{\text{out}}$ (`finalHamiltonian_shift`,
  `shift_changes_model`) and the separation of physical cutoffs $(a, L, R)$ from solver budget
  $(m, q, \text{precision})$ (`krylov_not_continuum`).
* **Factorize the outer Euclidean semigroup.** Prove on each $N$-particle outer sector
  ([ChapterScalarOuter](BookProof/Phi4/ChapterScalarOuter.lean),
  [ContinuumManifest](BookProof/OSReconstruction/ContinuumManifest.lean)) that
  $$e^{-\tau d\Gamma(h_\sigma)}\big|_{\mathcal F^{(N)}_{\text{out}}} = \big(e^{-\tau h_\sigma}\big)^{\otimes N} \qquad (\tau \ge 0),$$
  so the $N$-point Euclidean evolution of a populated prior $\Psi_{\text{info}}$ reduces to
  evaluating the inner semigroup $e^{-\tau h_\sigma}$ on each informed spatial factor, while
  $e^{-\tau d\Gamma(h_\sigma)} \Omega_{\text{out}} = \Omega_{\text{out}}$ remains empty.
* **Acceptance:** a `sorry`-free sector-factorization theorem tying `NestedSpec.finalHamiltonian`
  and `NestedSpec.relativeGenerator` to $\Gamma(e^{-\tau h_\sigma})$, with a negative control
  confirming that $\Omega_{\text{out}}$ gives trivial expectations for number-density observables.

### H1 — Mehler/Hermite representation and the free Euclidean transition kernel

*Adapts [cft_path.md](cft_path.md) §§2 & 4 (Position/momentum resolutions of identity and Gaussian momentum integration).*

* **Use the Mehler bridge as the canonical chart.** Build on
  [ChapterYangMillsMehlerBridge](BookProof/Qym/ChapterYangMillsMehlerBridge.lean)
  (`conj_deriv`: $U\partial U^{-1} = \partial + x/2$; `conj_dirichlet`:
  $U(-\partial^2 + x\partial)U^{-1} = -\partial^2 + x^2/4 - 1/2$; `conj_mult`: $UVU^{-1} = V$)
  and its multi-coordinate Hermite basis
  ([ChapterHermiteProductBasis](BookProof/Toolbox/ChapterHermiteProductBasis.lean)).
* **Close the Mehler kernel gap.** [MehlerEigenfunction](BookProof/MCMC/MehlerEigenfunction.lean)
  already proves the eigenfunction identity `mehlerOp_physHermite` ($T_\rho H_n = \rho^n H_n$ for
  $\rho = e^{-\epsilon}$) and `mehlerOp_vacuum` ($T_\rho 1 = 1$), but the **closed-form Mehler
  transition density** $K_\epsilon(x, y)$ with respect to $\gamma(dy)$ is formalized for a one-dimensional slice against Lebesgue measure. For the
  finite-product stationary Gaussian reference, establish the kernel representation
  $$(e^{-\epsilon h_0} f)(x) = (T_{e^{-\epsilon}} f)(x) = \int K_\epsilon(x, y)\, f(y)\, \gamma(dy),$$
  with $K_\epsilon(x, y) > 0$, symmetry $K_\epsilon(x, y) = K_\epsilon(y, x)$, semigroup
  composition $\int K_{\epsilon_1}(x, z) K_{\epsilon_2}(z, y)\,\gamma(dz) = K_{\epsilon_1+\epsilon_2}(x, y)$,
  and exact probability normalization $\int K_\epsilon(x, y)\,\gamma(dy) = 1$.
* **Bridge to existing Feynman–Kac and 4D Gaussian controls.** Identify $K_\epsilon$ (under the
  ground-state transform $U$) with `freeTransferKernel` / `fkKernelProduct` in
  [FeynmanKac](BookProof/ReflectionPositivity/FeynmanKac.lean) and calibrate its two-slice
  covariance against [GaussianMehlerControl](BookProof/OSReconstruction/GaussianMehlerControl.lean)
  and [EuclideanMehlerCalibration](BookProof/OSReconstruction/EuclideanMehlerCalibration.lean).
* **Acceptance:** explicit closed-form Mehler kernel theorem on finite mode products, semigroup
  Chapman–Kolmogorov identity, positivity and $\gamma$-preservation, eliminating flat-space
  normalization divergences.

### H2 — Euclidean Lie–Trotter product formula and midpoint/Weyl ordering

*Adapts [cft_path.md](cft_path.md) §3 (Trotter approximation) and the Note on Operator Ordering (Midpoint Rule).*

* **Formalize the Euclidean Lie–Trotter product formula.** The Lean corpus currently has the
  *Trotter–Kato resolvent-to-flow approximation theorem*
  ([ChapterSirkTrotterKato](BookProof/Sirk/ChapterSirkTrotterKato.lean)), **not** the Lie–Trotter
  product formula. Build it in two stages:
  1. *Finite-dimensional / bounded stage:* for bounded (or Hermite-truncated) operators $A, B$,
     prove $\|(e^{-\frac{T}{N}A} e^{-\frac{T}{N}B})^N - e^{-T(A+B)}\| = \mathcal{O}(T^2/N)$
     (and the symmetric Strang splitting $e^{-\frac{\epsilon}{2}V} e^{-\epsilon h_0} e^{-\frac{\epsilon}{2}V}$
     for $\mathcal{O}(T^3/N^2)$ and exact slice self-adjointness).
  2. *Unbounded nonnegative self-adjoint stage:* for $h_0 \ge 0$ and $V \ge 0$ (or $h_0$-form-bounded
     with relative bound $< 1$) on a common core, prove strong convergence
     $$(e^{-\frac{T}{N}h_0} e^{-\frac{T}{N}V})^N \psi \xrightarrow{N\to\infty} e^{-T(h_0 \dot{+} V)} \psi$$
     using the nonnegative semigroup machinery of
     [ChapterNonnegSemigroup](BookProof/ChapterNonnegSemigroup.lean) and Chernoff's product
     formula.
* **Enforce the midpoint / Weyl operator-ordering gate.**
  * When $h_\sigma = h_{0,\sigma} + V_\sigma(q)$ has **no** first-order position–momentum
    cross-terms (e.g. pure Weyl-gauge QYM $h_W = -\frac{1}{2}\pi_a^i\pi_a^i - \frac{1}{2}B_{ia}^2$
    where the electric kinetic operator is purely quadratic in $\pi$ and $B_{ia}$ depends on $A$
    and spatial momentum convolutions, or pure $\phi^4$/Higgs scalar potentials), endpoint and
    Strang/midpoint splittings agree in the $N \to \infty$ limit.
  * When cross-terms appear—gauge-covariant matter kinetic terms $(p - eA(q))^2$, curved-space /
    QG vielbein kinetic operators, or non-constant field-space metrics—$\Delta q \sim \sqrt{\epsilon}$
    produces an $\mathcal{O}(\epsilon)$ ambiguity that survives $N\epsilon = T$. Require **midpoint
    discretization** $\bar{q}_j = \frac{1}{2}(q_{j+1} + q_j)$ (Stratonovich / Weyl ordering),
    connecting to [book.tex](book.tex) §*Quadratic Ordering* & §*Quantization due to time evolution*
    and [ChapterQuantizationWeyl](BookProof/ChapterQuantizationWeyl.lean). Keep Weyl ordering
    (which preserves operator exponentials in Trotter products) explicitly distinct from
    [book.tex](book.tex)'s Quadratic Ordering (which enforces number conservation and zero
    $\Omega_{\text{out}}$ expectation).
* **Acceptance:** a `sorry`-free Lie–Trotter theorem (bounded + unbounded nonnegative form-sum
  version) and a negative control demonstrating the $\mathcal{O}(1)$ drift error when endpoint
  discretization is mistakenly applied to a position–momentum cross-term.

### H3 — Time-sliced Mehler Feynman–Kac representation and reflection positivity

*Adapts [cft_path.md](cft_path.md) §§4–5 (Configuration-space path integral and $N\to\infty$ continuum-time limit).*

* **Time-sliced Markov path measure.** Combining H1 and H2 on the $N$-slice grid
  $\tau_j = j\epsilon$ ($\epsilon = T/N$), define the normalized finite-slice path measure
  $\mu_{\sigma, N}$ on $(\mathscr X_\sigma)^{N+1}$ with transition kernel $K_\epsilon$ and
  Strang-symmetrized potential weight $\exp(-\frac{\epsilon}{2}V_\sigma(q_0) - \epsilon\sum_{j=1}^{N-1} V_\sigma(q_j) - \frac{\epsilon}{2}V_\sigma(q_N))$
  (or midpoint weight when cross-terms are present). Prove exact algebraic identity between the
  $N$-slice integral and the inner matrix element
  $\langle \psi_b, (e^{-\frac{\epsilon}{2}V_\sigma} e^{-\epsilon h_{0,\sigma}} e^{-\frac{\epsilon}{2}V_\sigma})^N \psi_a \rangle$.
* **Continuous-time limit ($N \to \infty$ at fixed spatial cutoffs $(a, L, R)$).** Pass $N \to \infty$
  via H2 to identify the continuous-time Euclidean propagator and ordered multi-time moments
  ([EuclideanMomentHierarchy](BookProof/OSReconstruction/EuclideanMomentHierarchy.lean):
  `euclidWord`, `euclidMoment`, `twoPoint`) with the Mehler/Ornstein–Uhlenbeck Feynman–Kac
  expectation:
  $$\langle \psi_b, e^{-T h_\sigma} \psi_a \rangle = \mathbb{E}_{\text{OU/Mehler}}\!\left[\overline{\psi_b}(X_T)\,\psi_a(X_0)\,\exp\!\left(-\int_0^T V_\sigma(X_s)\,ds\right)\right].$$
* **Regulator reflection positivity.** Discharge the honest boundary of
  [FeynmanKac](BookProof/ReflectionPositivity/FeynmanKac.lean) by identifying the Strang-symmetric
  time-sliced path measure with `fkMeasure ρ ν` across the $\tau = 0$ slice, inheriting
  all-degree reflection positivity (`fk_reflectionPositive`,
  [HalfSpaceSplit](BookProof/ReflectionPositivity/HalfSpaceSplit.lean),
  [GaussianMehlerCylinderRP](BookProof/OSReconstruction/GaussianMehlerCylinderRP.lean)) for
  ordered positive-time observable words.
* **Acceptance:** exact $N$-slice equivalence, $N \to \infty$ Feynman–Kac identity at fixed
  $(a, L, R)$, and derived (not assumed) reflection positivity on the regulated positive-time
  algebra.

### H4 — SIRK certification without time-discretization error

*Integrates the project's SIRK/Hashimoto machinery into the [cft_path.md](cft_path.md) equivalence.*

* **Single-time Euclidean evaluation.** While H2–H3 use time-slicing $N \to \infty$ to *prove*
  equivalence with the path integral, evaluating or certifying finite-time Euclidean propagators
  $e^{-\tau K_\sigma} v$ and correlation words does **not** require time-slicing. Reuse
  [ChapterSirkSingleTimeShift](BookProof/Sirk/ChapterSirkSingleTimeShift.lean)
  (`sirk_single_time_shiftInvert_bound`),
  [ChapterCrouzeixSelfAdjoint](BookProof/Sirk/ChapterCrouzeixSelfAdjoint.lean)
  (`sirk_error_bound_selfAdjoint`) and
  [ChapterSirkTruncation](BookProof/Sirk/ChapterSirkTruncation.lean) to bound the rational-Krylov
  approximation of $e^{-\tau K_\sigma} v$ from the bounded shift-invert resolvent
  $(K_\sigma + \gamma)^{-1}$ ($\gamma > 0$) with **zero Trotter time-step error**.
* **Friedrichs domain selection.** Use `hashimoto_shiftInvert_selects_friedrichs`
  ([ChapterHashimotoShiftInvert](BookProof/Sirk/ChapterHashimotoShiftInvert.lean)) to pin down
  the self-adjoint realization of $h_\sigma$ whose semigroup H2–H3 represent as a Feynman–Kac
  integral, eliminating domain ambiguity between formal differential expressions and their
  self-adjoint closures.
* **Missing Euclidean heat-semigroup Trotter–Kato transfer.** Prove the nonnegative
  imaginary-time counterpart of
  [ChapterSirkTrotterKato](BookProof/Sirk/ChapterSirkTrotterKato.lean): strong resolvent
  convergence $(K_n + \gamma)^{-1} \to (K + \gamma)^{-1}$ ($\gamma > 0$, common lower bound
  $K_n \ge 0$) implies locally uniform strong convergence $e^{-\tau K_n} v \to e^{-\tau K} v$
  for $\tau \ge 0$. Combine with **U0–U6** of [softmodes.md](softmodes.md) for Hermite-tail and
  leakage control, and with **C6** below for telescoping multi-point correlation certificates.
* **Acceptance:** Euclidean heat-semigroup Trotter–Kato theorem, single-time SIRK error bound on
  `euclidMoment`, and explicit separation of solver error from physical cutoff error.

**Status (2026-11-26): H7/C8 bridge gap invariance.**
`BookProof/OSReconstruction/ChapterBridgeGapInvariance.lean` proves that an exponential
flow-gap estimate toward a fixed point is invariant under the cyclic unitary `OsFockBridge`:
`FlowGap P x m C ↔ FlowGapOn Q (U x) m C`.  This transports the stated fixed-vector estimate. The current work order uses
the full stationary projection for the spectral claim.

**Status (2026-11-26): H7/C7 generator transport.**
`BookProof/OSReconstruction/ChapterGeneratorTransport.lean` proves that an `OsFockBridge`
intertwining two contraction flows carries a right derivative at `0` of the OS orbit to a right
derivative of the physical orbit (`generator_image`), that the right derivative is unique on
`Ici 0` (`generator_eq`), and hence that the transported generator value is unique
(`generator_image_unique`).  This is the infinitesimal (operator-level) half of C7, complementing
the flow-level gap invariance of C8; no generator self-adjointness or gap value is asserted.

**Status (2026-11-26): H7/C9 negative control.**
`BookProof/OSReconstruction/ChapterEquivalenceNoGap.lean` records the sharp separation: without
a positive floor on the multiplier density the transfer semigroup does not converge in norm to
the ground projection, so the Hamiltonian ↔ Euclidean equivalence data by itself cannot certify
a mass gap.  This is a negative control; no no-gap theorem for the physical theory is claimed.

**Status (2026-11-26): H6 Route B limit order.**
`BookProof/ChapterExternalSourceLimitOrder.lean` proves the non-commuting limit order on the
finite-volume benchmark `m_V(J) = v·VJ/(1+VJ)`: the source removed after the volume limit leaves
`v ≠ 0`, while the volume limit after removing the source leaves `0`.  The lift to the physical
nested-Fock measure is open.

**Status (2026-11-26): H6 Route B Gaussian expectation.**
`BookProof/OSReconstruction/ChapterGaussianSourceExpectation.lean` lifts the benchmark to a
measure: `sourceGaussian V J v σ` is the Gaussian with mean `m_V(J)`, its expectation is exactly
`m_V(J)`, and it inherits both limit orders.  This is a measure-valued benchmark, not the
physical infinite-volume Higgs/φ⁴ expectation; no conditional prior or phase disintegration is
matched.

**Status (2026-11-26): H6 Route A finite-volume shift.**
`BookProof/Qym/ChapterShiftedVacuumEquivalence.lean` proves the algebraic input: at a Higgs
vacuum `v`, the radial curvature `μ²‖v‖²` is strictly positive and a transverse shift has no
quadratic term.  The field redefinition at the Mehler/SIRK level and the infinite-volume sector
inequivalence remain open.

**Status (2026-11-26): H6 Route A Gaussian reference.**
`BookProof/OSReconstruction/ChapterDisplacedMehlerMean.lean` proves the Gaussian-reference
half of the field redefinition: the Gaussian centered at `v` is the translated centered
Gaussian, its mean is `v`, the fluctuation `h = φ − v` has mean zero and unchanged variance,
and its density is strictly positive at nonzero variance.  `integral_displaced` gives the Route A
change of variables `∫ f dγ_v = ∫ f(·+v) dγ_0`, and `displaced_reference_second_moment` gives
`∫ φ² dγ_v = σ + v²`.  There is no
Weyl conjugation of the interacting Hamiltonian, no nested-Fock vacuum `Ω_v` and no
infinite-volume sector result.

**Status (2026-11-26): H5 symmetric-boundary mean at density level.**
`BookProof/OSReconstruction/ChapterSymmetrizedGaussianMean.lean` proves that the equally
weighted mixture of the Gaussians centered at `±v` is a probability measure whose first moment
is zero, independently of `v` and `σ`.  The second moment is `σ + v²` (and hence the variance
is `σ + v²`, since the mean vanishes), separating the common Gaussian fluctuation from the
separation of the two centers.  `symmetrizedGaussian_neg_invariant` shows the mixture is
invariant under `x ↦ −x`, and `symmetrizedGaussian_odd_moment_eq_zero` deduces that every odd
moment vanishes — the distribution-level form of the symmetric average.  This is the
density-level form of the symmetric-average
`⟨φ⟩ = 0` mechanism; no physical ground state, infinite-volume sector or cluster statement is
implied.

**Status (2026-11-26): H5 overlap collapse.**
`BookProof/OSReconstruction/ChapterOverlapCollapse.lean` proves that the coherent overlap of the
unshifted reference with a spatially constant shift `v` across `N` modes is
`exp(−N v²/2)` and tends to zero as `N → ∞` for `v ≠ 0` — the Gaussian/coherent-level
Kakutani bound.  The lift to the physical Higgs/φ⁴ ground states and the symmetric-average /
tachyonic failure modes remain open.

**Status (2026-11-26): H4 bounded transfer.**
`BookProof/Sirk/ChapterHeatSemigroupBoundedTransfer.lean` proves the bounded-generator half of
the missing Euclidean transfer: operator-norm convergence `A_n → A₀` implies convergence of the
heat semigroups `exp(−τ A_n) → exp(−τ A₀)` at every fixed time, via continuity of
`NormedSpace.exp` with the `NormedAlgebra ℚ` restriction instance for `E →L[ℂ] E`.  The
unbounded strong-resolvent-to-heat theorem is still open; the bounded result does not replace it.

**Status (2026-11-26): H4 resolvent-to-heat bridge (bounded).**
`BookProof/Sirk/ChapterResolventToHeatSemigroup.lean` connects H4's resolvent hypothesis to the
bounded transfer: since inversion is continuous at a unit of the Banach algebra `E →L[ℂ] E`
(`NormedRing.inverse_continuousAt`), norm convergence of `(A_n + γ)⁻¹` at one resolvent point
implies norm convergence of `A_n`, hence of the heat semigroups.  A quantitative bound
`‖A − A₀‖ ≤ ‖A₀+γ‖ ‖R₀−R‖ ‖A+γ‖` is also proved, and `heatSemigroup_continuous` /
`heatSemigroup_tendsto_joint` give joint continuity in time and generator.  This is still the
bounded case; each `A_n + γ` is assumed invertible and no unbounded/strong-resolvent theorem is
claimed.

### H5 — Euclidean vacuum projection and the infinite-volume overlap catastrophe

*Adapts [cft_path.md](cft_path.md) Part II §§1–2 (Projecting onto the vacuum state; why a Higgs / non-zero-VEV potential breaks naive equivalence).*

* **Physical ground-state projection ($T \to \infty$).** Lift the multiplier-model theorems of
  [MultiplierSelfAdjoint](BookProof/OSReconstruction/MultiplierSelfAdjoint.lean)
  (`norm_flowOfHCLM_sub_limitProjection`, `tendsto_opNorm_flowOfHCLM_sub_limitProjection_iff_gap`,
  `exists_time_norm_flowOfHCLM_sub_limitProjection_lt`) from `MulModel` to the physical cyclic
  representation of $K_\sigma = (H_\sigma - E_0 I)|_{\mathcal H_{\text{ref}}} \ge 0$. Prove that
  for boundary states $\Psi_a, \Psi_b$ at $\tau = \pm T$,
  $$\lim_{T\to\infty} \frac{\langle \Psi_b, e^{-T K_\sigma} \mathcal{O}_1 e^{-\Delta\tau K_\sigma} \mathcal{O}_2 e^{-T K_\sigma} \Psi_a \rangle}{\langle \Psi_b, e^{-(2T+\Delta\tau) K_\sigma} \Psi_a \rangle} = \langle \Omega_v, \mathcal{O}_1 e^{-\Delta\tau K_\sigma} \mathcal{O}_2 \Omega_v \rangle$$
  holds **if and only if** the boundary states have **non-zero overlap** with the ground state
  ($\langle \Omega_v | \Psi_a \rangle \neq 0$, $\langle \Psi_b | \Omega_v \rangle \neq 0$) and
  the ground projection $P_0 = |\Omega_v\rangle\langle\Omega_v|$ is rank-one in the selected
  sector (otherwise the limit projects onto $P_0 \Psi_a, P_0 \Psi_b$). Note that in
  [book.tex](book.tex) (L6616–6622, L7499–7506), finite-$T$ expectations in a general non-stationary
  populated prior $\Psi_{\text{info}}$ remain valid prior-dependent predictions even without taking
  $T \to \infty$.
* **Formalize the infinite-volume overlap collapse (Kakutani orthogonality).** Build directly on
  the existing Gaussian/coherent overlap lemmas—
  [ChapterCoherentOverlap](BookProof/Attention/ChapterCoherentOverlap.lean)
  (`coherentOverlap_eq_gaussian`),
  [ChapterCoherentGeometry](BookProof/Attention/ChapterCoherentGeometry.lean)
  (`neg_two_mul_log_coherentOverlap`: $-2\log\langle q|k\rangle = \|q-k\|^2$) and
  [ChapterF3](BookProof/Textbook/ChapterF3.lean) (`overlap_prod_pos`)—to prove that for a
  spatially constant field shift $v \neq 0$ across $N(V_3) \propto V_3$ spatial modes, the overlap
  between the unshifted Mehler reference state $|\phi = 0\rangle$ and the shifted ground state
  $|\Omega_v\rangle$ decays exponentially with volume:
  $$|\langle \Omega_v | \phi = 0 \rangle| \le \exp(-c\, v^2\, V_3) \xrightarrow{V_3 \to \infty} 0.$$
* **Record the two broken-phase failure modes on project models.** Instantiate on the static
  Mexican-hat Higgs potential of [ChapterSmHiggsVacuum](BookProof/ChapterSmHiggsVacuum.lean)
  (`higgsV_sq_form`, `higgsV_eq_min_iff`, `higgs_goldstone`, `higgs_radial`) and the double-well
  $\phi^4$ sector of [ChapterScalarMehler](BookProof/Phi4/ChapterScalarMehler.lean) and
  [ChapterScalarMomentumGap](BookProof/Phi4/ChapterScalarMomentumGap.lean) (`fieldReflMatrix`):
  1. *Symmetric averaging over vacua:* imposing naive Dirichlet / unshifted Mehler boundary
     conditions $\phi(\pm\infty) = 0$ sums symmetrically over $\pm v$ (connected by finite-volume
     tunneling/instanton sectors), producing $\langle \phi \rangle_{\text{PI}} = 0 \neq v$.
  2. *Tachyonic expansion around $\phi = 0$:* expanding around the unstable maximum
     $V''(0) = -\mu^2 < 0$ breaks positivity of the quadratic reference form and invalidates naive
     Gaussian-reference damping.
* **Preserve Elitzur's gauge-symmetry boundary.** In pure QYM and gauge sectors, retain
  [ChapterGaugeVariantVanishing](BookProof/ChapterGaugeVariantVanishing.lean)
  (`expectation_gauge_variant_eq_zero`, `no_spontaneous_gauge_symmetry_breaking`): gauge-variant
  operators have zero expectation in any gauge-invariant state, so the VEV obstruction above
  concerns **global/scalar order parameters** (Higgs/$\phi^4$) or gauge-fixed/gauge-variant
  Mehler reference measures ([book.tex](book.tex) L6652–6735), not spontaneous breaking of local
  gauge symmetry.
* **Acceptance:** a `sorry`-free volume-decay overlap theorem $\exp(-c v^2 V_3) \to 0$, a
  $\mathbb{Z}_2$-symmetric boundary-averaging theorem proving $\langle\phi\rangle = 0$ under
  unshifted boundary conditions, and an explicit non-zero-overlap hypothesis in the $T \to \infty$
  vacuum-projection theorem.

### H6 — Restoring equivalence in broken-symmetry / non-zero-VEV sectors

*Adapts [cft_path.md](cft_path.md) Part II §3 (Field shift $\phi = v + h$ and external source $J$ with $V_3 \to \infty$ before $J \to 0^+$).*

Implement both restoration mechanisms inside the Mehler / nested-Fock framework:

1. **Route A — Mehler-center shift (displacement $D(v)$, $\phi = v + h$).**
   * Define the displaced Mehler reference measure $\gamma_v = T_v^* \gamma_0$ centered at a
     minimum $v$ of `higgsV` (or `vev` in `ChapterScalarMehler`) and the corresponding unitary
     Weyl displacement operator $D(v)$ in finite volume.
   * Conjugate the inner Hamiltonian $h_\sigma \mapsto h_{\sigma, v} = D(v)^\dagger h_\sigma D(v)$
     before constructing the Hermite basis, Mehler kernel (H1), Lie–Trotter split (H2) and SIRK
     compression (H4). Then the fluctuating field $h = \phi - v$ has $\langle h \rangle = 0$, the
     radial curvature is strictly positive ($V''(v) = 2\mu^2 > 0$, `higgs_radial`), boundary
     condition $h(\pm\infty) = 0$ corresponds to $\phi(\pm\infty) = v$, and the shifted Mehler
     reference state maintains strictly positive overlap with $|\Omega_v\rangle$.
   * Record that in infinite volume $V_3 \to \infty$, $\gamma_v \perp \gamma_0$ (H5): the shift
     selects an inequivalent GNS / superselection sector rather than a unitary within the
     unshifted Fock space.
2. **Route B — External source $J$ / symmetry-breaking conditional prior with strict limit order.**
   * Add a linear symmetry-breaking source $h_\sigma(J) = h_\sigma - J \int \phi$ (or condition the
     spatial prior on a symmetry-breaking event $C = 0$ via `SpatialPrior.cond` in
     [PriorRefinement](BookProof/OSReconstruction/PriorRefinement.lean), directly formalizing
     [book.tex](book.tex) L6741–6749's conditional-expectation definition of SSB).
   * Formalize the **non-commuting limit order** theorem on a concrete double-well / Ising-type
     finite-volume benchmark first, then as the general sector-selection contract:
     $$\lim_{J \to 0^+} \lim_{V_3 \to \infty} \langle \phi \rangle_{V_3, J} = v \neq 0, \qquad
       \lim_{V_3 \to \infty} \lim_{J \to 0^+} \langle \phi \rangle_{V_3, J} = 0.$$
   * Match the selected $J \to 0^+$ phase to the phase disintegration used in the archive adapter
     (**C0 / C8**) and to Yang's long-range two-point criterion ([book.tex](book.tex) L6747–6749).
* **Acceptance:** a `sorry`-free finite-volume displacement equivalence theorem (Route A) and a
  `sorry`-free non-commuting limit-order theorem for $V_3 \to \infty$ vs. $J \to 0^+$ (Route B),
  plus a negative control rejecting reversed limits or unshifted expansions around $V''(0) < 0$.

### H7 — Continuum limit, Bałaban compatibility and OS reconstruction

**H0–H6** establish the Hamiltonian $\leftrightarrow$ Euclidean path-integral equivalence, SIRK
certification and broken-phase boundary control **at regulated physical cutoffs $(a, L, R)$**
(with continuous Euclidean time $N \to \infty$ already taken in H3). Passing to the 4D continuum
theory connects directly into the existing programme below:

* **UV/IR cutoff removal:** supply uniform multiscale moment, tightness and renormalization bounds
  via **C3–C5** (Bałaban small/large-field packets) or prove compatibility of the regulated H3
  Euclidean hierarchy with the selected October-archive Wilson witness via **C0** and the
  2026-11-24 Bałaban work order below.
* **OS reconstruction & unitary bridge:** apply **C7–C8** (half-space OS quotient, forward
  contraction semigroup, cyclic unitary $U : \mathcal H_{\text{OS}} \to \mathcal H_{\text{ref}}$)
  to identify the continuum OS generator with the limiting nested Hamiltonian $K$.
* **Mass gap & nontriviality kept separate:** retain **C9** and [softmodes.md](softmodes.md)
  **U0–U6**; neither Trotter/Feynman–Kac equivalence nor SIRK convergence nor vacuum uniqueness in
  a selected phase implies a positive mass gap by itself.

### Readiness ledger and negative controls for H0–H7

| Packet | Implemented | Next analytical identification |
| --- | --- | --- |
| H0 | Stone flow on tensor sectors, vacuum fixed | Identify the heat semigroup of the closed interacting inner generator on the physical outer sectors. |
| H1 | Scalar Mehler density, mass one, Gaussian kernel composition and the free endpoint limit | Pass to the chosen mode product, with detailed balance in the stationary Gaussian convention. |
| H2 | Midpoint cancellation for the exact Heisenberg/BCH example | Prove product convergence for the interacting form sum on its domain. |
| H3 | Finite Markov measures, last-slice consistency, discrete infinite trajectory, positive weighted finite measures and a constant-potential time limit | Identify all finite marginals and the continuous-time interacting weight with the physical semigroup and reflection form. |
| H4 | Heat transfer for bounded operators under norm hypotheses | Prove physical unbounded-generator convergence and keep SIRK tolerances separate from regulator removal. |
| H5–H6 | Coherent overlap collapse, displaced Gaussian benchmarks, symmetric mixture moments and a source-limit-order example | Identify these quantities in the selected interacting stationary state or phase. |
| H7 | Conditional generator-derivative transport, stationary-space identification and equality of heat errors | Match the selected Wilson hierarchy and construct the physical OS bridge. A positive gap also needs a full-complement decay estimate. |

**Additional negative controls (extending C10):** reject any proof claiming that (a)
`ChapterSirkTrotterKato` is a Lie–Trotter product formula; (b) endpoint time-slicing reproduces a
Weyl-ordered Hamiltonian with position–momentum cross-terms; (c) an oscillatory Minkowski path
integral is a $\sigma$-additive probability measure; (d) $\Omega_{\text{out}}$ is the physical
vacuum of a populated number-density algebra; (e) naive $\phi(\pm\infty)=0$ boundary conditions or
reversed limits ($J \to 0^+$ before $V_3 \to \infty$) reproduce a broken-symmetry VEV; or (f)
finite-time SIRK accuracy replaces UV/IR cutoff removal.

**Execution order:** **H0 → H1 → H2 → H3** (regulated Hamiltonian $\leftrightarrow$ Mehler
Feynman–Kac equivalence), in parallel with **H4** (Euclidean SIRK transfer) and **H5 → H6**
(vacuum projection, overlap collapse and broken-phase restoration), feeding into **H7 / C3–C9**
for the continuum limit.

**Status (2026-11-25): H0 landed (core level).**
`BookProof/OSReconstruction/ChapterOuterSemigroupFactorization.lean` proves that on each
$N$-particle outer sector the Stone flow of a self-adjoint one-particle operator is the
$N$-fold tensor power `Γ(U t)`: `tpow_add` gives the one-parameter group law,
`fockOrbit_add` carries it to the completed sector, `fockOrbit_zero_sector` pins the empty
vacuum, and `sector_flow_is_tensor_power` is the factorization statement itself (with
`ChapterFlowDGammaEsa.hasDerivAt_fockOrbit` supplying the sector derivation).  This is the
core-level factorization of H0's acceptance, not the unbounded operator equality
$e^{-\tau d\Gamma(h)}=\Gamma(e^{-\tau h})$ on $L^2$; H1–H7 remain open.

**Status (2026-11-25): H2 landed (midpoint ordering).**
`BookProof/ChapterSymmetricTimeStepOrdering.lean` proves in the exact Heisenberg/BCH model
that the symmetric Strang step $\exp(aX/2)\exp(bY)\exp(aX/2)$ equals $\exp(aX+bY)$ (no first
BCH commutator), while the endpoint Lie step differs by $\tfrac{ab}{2}Z$ — the negative
control against endpoint time-slicing of a Weyl-ordered cross-term Hamiltonian.  The general
operator-norm Lie–Trotter limit is **not** proved: this Mathlib has no product formula, and
`ChapterSirkTrotterKato` proves a different statement (strong resolvent convergence of a
family), as the readiness ledger requires us to note.

**Status (2026-11-25): H3 landed (one slice only).**
`BookProof/ReflectionPositivity/ChapterMehlerSliceReflectionPositivity.lean` identifies the
Mehler-kernel slice measure and proves its OS form nonnegative both directly (square of a
conditional expectation) and through `fkMeasure`/`fk_reflectionPositive`;
`fkOSForm_eq_kernel_square` is the exact identification of the two forms and
`mehlerSliceMeasure_univ` shows the slice kernel measure is a probability, and
`ChapterTwoSlicePathMeasure` builds the two-slice path measure and proves it a probability
by Tonelli, and `ChapterThreeSlicePathMeasure` extends this to three slices by two Tonelli
steps in path order.  Generalizing to arbitrary `N` was attempted with a recursive path type,
but the required measurable-space recursion (`Measurable (fun p => p.1)` into a `comap` space)
is not discharged by the available instances. A `Fin (N+1) → ℝ` path space was then developed:
`ChapterFinitePathMeasure` proves the base splitting at the last coordinate (`pathBase_split`)
and the kernel-product factorization (`pathDensity_last`) with zero-step normalization;
`ChapterPathMeasureInduction` closes the Tonelli induction, so the general `N`-slice path
measure is a probability for every admitted schedule (`pathMeasure_univ`), and
`ChapterWeightedPathMeasure` attaches the Strang weight, bounding its path integral by
`exp(−ε N m)` for a potential with floor `m` (`weighted_pathMeasure_le`), and
`ChapterContinuousTimeWeight` shows that at `ε = T/N` the constant-potential factor is exactly
`exp(−T c)` for every `N > 0`.  The measure convergence to continuous time remains open; and
`BookProof/ReflectionPositivity/ChapterMehlerKernelSemigroup.lean` proves the Gaussian
convolution law `∫ K_ρ(x,z)K_σ(z,y) dz = K_{ρσ}(x,y)` for the N-slice composition, iterated in
`mehlerKernel_integral_mul_three` to the three-slice path integral, and
`pathIntegral_eq` to any nonempty finite slice schedule (the nested path integral equals the
kernel at the product parameter), `pathIntegral_exp_schedule` shows the exponential schedule
$\rho_N=e^{-T/N}$ reproduces the continuous-time kernel exactly after $N$ slices, and
`tendsto_pathIntegral_linear` shows the Euler schedule $\rho_N=1-T/N$ converges to it as
$N\to\infty$, and `ChapterStrangPotentialWeight` gives the exact Strang weight
$\exp(-\epsilon V(q_0)/2 - \epsilon\sum_{j=1}^{N-1}V(q_j) - \epsilon V(q_N)/2)$ with its
endpoint/interior factorization and the constant-potential total factor `exp(−(εN·c))`.
The `N`-slice product **measure**, the $N\to\infty$
Feynman–Kac limit, the interacting potential weight and the full positive-time algebra are
**not** proved; H3 is not complete.

**Status (2026-11-26): H3 infinite Mehler path measure.**
`BookProof/OSReconstruction/ChapterMehlerTrajMeasure.lean` builds the Mehler one-step Markov
kernel (`mehlerStep`) and feeds it to Mathlib's Ionescu–Tulcea theorem
(`trajMeasure`), obtaining a probability measure `mehlerPathMeasure ρ hρ x` on infinite paths
`ℕ → ℝ`.  `mehlerPathMeasure_step` identifies the joint law of the history up to `n` and the
next position as the kernel-composition law.  `mehlerPathMeasure_eval_zero` (via the general
`trajMeasure_eval_zero`) pins the first coordinate to the starting Dirac `x`, the anchor of the
finite-marginal identification.  `mehlerPathMeasure_eval_one` further identifies the law of the
position at time `1` with the first Mehler kernel density, so the first two coordinates agree
with the two-slice `pathMeasure`.  This is the infinite discrete-time
measure only: the full finite marginals are not identified with `pathMeasure`, no continuum limit
`ε = T/N → 0` is taken, and the interacting Strang weight is absent.

**Status (2026-11-26): H3 projective consistency at the last slice.**
`BookProof/OSReconstruction/ChapterPathMeasureMarginal.lean` proves `pathMeasure_marginal`:
dropping the final time slice of `pathMeasure x ρ` by the coordinate projection gives exactly
`pathMeasure x (fun j => ρ j.castSucc)`, the measure with the final Mehler kernel removed.
This is the consistency relation the Ionescu–Tulcea extension needs to pass from the finite
family to a measure on infinite paths; it does not construct that limit measure or prove
convergence to continuous time.

**Status (2026-11-25): H1 landed (one-slice density).**
`BookProof/ReflectionPositivity/ChapterMehlerTransitionDensity.lean` defines
$K_\rho(x,z) = (\sqrt{\pi(1-\rho^2)})^{-1}\exp(-(z-\rho x)^2/(1-\rho^2))$ for $\rho^2<1$ and
proves positivity, unit mass, the identity with `FeynmanKac.freeTransferKernel` at stiffness
$2/(1-\rho^2)$ and drift $\rho x$, and that `mehlerOp ρ f x = ∫ f(z) K_\rho(x,z) dz`; the
stationary slice is $K_0(x,z)=(\sqrt\pi)^{-1}e^{-z^2}$, independent of $x$ (hence not symmetric
in the two configurations).  This is
the one-slice identity. H3 subsequently constructed finite path measures and the
discrete trajectory described above. Its interacting continuous-time identification
and physical reflection-positivity argument remain open.

---

## Balaban Yang–Mills and the continuous-momentum Hamiltonian

**Work order, 2026-11-24.** Reuse the October archive's existence theorem for its
four-dimensional Wilson family. The new formalization target is a comparison with
the specified continuous-momentum nested Hamiltonian. Two choices matter from the
first lemma. Wilson links, plaquettes, mesh and volume belong to the Bałaban-side
regulator. On the nested side a spatial derivative is multiplication by $2\pi i k_j$
on continuous spatial momentum, and the nonabelian curvature contains an ordered
convolution over $q,k-q$. Euclidean time remains available for reflection and the
forward transfer semigroup. Independent derivative jets and a spatial lattice are
unnecessary on this side. Residual gauge symmetry, Gauss reduction and positive
physical states still need their own identification.
[Hamiltonian and spectral targets](softmodes.md) · [Public existence theorem](../OpenAI-YM-20261028/Solution.lean)

1. **Retain the actual witness.** In the archive's pinned environment, specialize
   `YangMills.jointExistence` to a matching simple gauge group and representation.
   For the SU(3) target supply its simplicity data. The supplied SU(2) specialization
   is a useful first check. Keep the chosen Wilson family fixed *before* choosing the
   increasing volume order and its refinement. Carry the same hierarchy and selected
   character through reconstruction. The Wilson convergence statement concerns the
   unselected correlations. Passing to a particular phase requires the archive's
   phase disintegration and a matching nested state. Use the detailed construction
   when contact data or an OPE reader is needed. Uniqueness of the vacuum in a
   selected reconstruction leaves uniqueness across phases and models open.
   [Exact quantifiers](../OpenAI-YM-20261028/ChallengeSpec.lean) ·
   [Detailed witnesses](../OpenAI-YM-20261028/Construction.lean)
2. **Start with one gauge-invariant smeared insertion.** Select an actual archive
   token and its normalized stencil. Specify its proposed nested observable from
   smeared field strengths with color indices contracted, and prove its gauge
   invariance, normalization and vacuum centering. A magnetic component alone does
   not identify the archive's stress trace. Compare a pair at separated positive
   Euclidean times on smooth tests. Prove convergence of the difference between
   the Wilson smears and nested heat-semigroup matrix elements in the archive's
   mesh-then-volume order, with explicit uniformity in test seminorms. A first
   pair checks the dictionary. Identification requires compatible estimates on a
   generating family of words, reflection, state and time translations.
   [Wilson smearing](../OpenAI-YM-20261028/WilsonBridge.lean) ·
   [Ordered extraction](../OpenAI-YM-20261028/YM/Extraction/Limits.lean)
3. **Assign each error to the construction that produces it.** On the Wilson side
   prove or import bounds for the chosen blocking map, local gauge normalization,
   small-field estimates, large-field tails and running parameters with insertions.
   On the nested side define the closed physical inner operator, its bosonic outer
   lift for pure YM, and the populated stationary cyclic state
   used for expectations. Bound smearing, Hermite tails, rational-solve error and
   arithmetic independently. Use C3–C6 only with the hypotheses verified for the
   same observable and scales. The local summable-increment theorem assembles an
   input estimate. It supplies no gauge-theory increment bound by itself.
   [Local RG convergence lemma](BookProof/BalabanRG/Convergence.lean)
4. **Reconstruct, then state the spectral consequence at its proved scope.**
   Equality of the positive-time forms on the generating algebra induces an isometry
   of the OS quotients. Prove density on both sides and intertwining of the forward
   semigroups for all times. This identifies the relative self-adjoint generators in
   the selected cyclic representation. To transfer a positive gap also transport
   the entire ground projection. Alternatively prove a uniform exponential bound
   on the ground-complement heat semigroup there. A short-distance OPE, vacuum
   uniqueness or decay in a single trial channel supplies no such infrared bound.
   Existence and the comparison of theories can progress without a gap theorem.
   [Reconstruction bridge](../OpenAI-YM-20261028/HierarchyBridge.lean) ·
   [Strong-coupling and spectral coverage work](softmodes.md#continuous-momentum-hamiltonian-and-spectral-target)

The adapter is proposed. Keep the archive on Lean 4.32 and the local proof on its
pinned Lean 4.28 until an explicit port or checked correspondence exists. The separate
`balaban-lean` repository formalizes the low-temperature O(N) **spin** model. Its
estimates require new hypotheses to apply to Yang–Mills.
[Archive verification scope](../OpenAI-YM-20261028/README.md) · [Spin-model scope](../balaban-lean/README.md)

## Detailed continuum-limit programme (2026-11-15)

This is the execution guide for the **LLM-Lean4-specialist**. It supersedes the forward
ordering of E0–E5/B0–B3 and the historical task lists below; their proofs, corrections and
dated verification reports remain evidence. No compilation, proof replay or numerical
experiment is performed by this planning update. The QYM-first project priority remains.

The goal is a continuum **four-dimensional Euclidean field theory associated with the
specified nested Hamiltonian**, with one identified observable/state dictionary throughout.
Four-dimensional means three physical spatial coordinates and Euclidean time, not four
independent Gaussian coordinates. Mehler coordinates organize the regulated analysis;
Bałaban-style multiscale bounds control removal of physical cutoffs; SIRK controls solver
and compression errors; half-space OS reconstruction identifies the resulting dynamics.
Each has a different proof obligation.

### Existing existence theorem and the remaining identification problem

Use the existence result already supplied by
[the October archive](../OpenAI-YM-20261028/README.md), inspected at revision
`3456e5e75cf8d4cd558955a5c7638fba2d68f464`. In
[Solution.lean](../OpenAI-YM-20261028/Solution.lean), `YangMills.jointExistence` proves
`YangMills.JointExistence`. Its
[exact contract](../OpenAI-YM-20261028/ChallengeSpec.lean) chooses a Wilson family before
the volume order, then a refinement and **one hierarchy** satisfying Wilson convergence,
reconstruction, separated OPE and the trace test. The detailed
[construction](../OpenAI-YM-20261028/Construction.lean), `YangMills.constructed`, retains
phase, OPE-reader and contact data for the same witness. This is the existing
Wilson/Bałaban-side continuum-existence input, not a construction to start over from zero.

**Existence is available there; uniqueness of the continuum theory is not.** A selected
phase's unique invariant vacuum is not uniqueness of the phase, regulator limit, contact
prescription or theory. Keep inequivalent or nonstandard realizations compatible with
the stated contract in scope until a stronger theorem excludes them. Do not silently
replace mathematical uniqueness by a preference for the usual physical interpretation.
The archive explicitly leaves positive mass gap and general exclusion of continuous-mass
generalized free fields outside its public result. Its finite-Wick trace exclusions have
their stated, narrower comparison class.

The missing theorem here is identification: an existentially chosen Wilson hierarchy
need not be the continuum limit of our particular nested-Fock Hamiltonians. Work on two
compatible paths:

1. **Reuse and realize a selected existing witness.** Retain its family, extraction order,
   hierarchy, phase, field labels and contact prescription. Construct a Mehler/nested
   realization of its cyclic physical representation and prove the observable/flow bridge.
2. **Construct the nested regulator limit and compare.** Prove the uniform estimates for
   our actual family, then establish that its separated hierarchy equals an admissible
   selected archive hierarchy. A generic existence theorem cannot choose our prescribed
   family without such a compatibility theorem; absence of uniqueness makes this explicit.

A common Hilbert-space dimension, a fitted two-point function or a Hamiltonian gap is not
that bridge. Full agreement on a generating observable algebra with the relevant domains
can determine a cyclic representation without proving uniqueness among all continuum
limits. An abstract reformulation of the archive's OS Hamiltonian as `dGamma(h)` must
also identify the **specified** inner `h`; it cannot merely rename an unrelated generator.

### Source-present machinery and its actual scope

These are static source readings; their theorem assumptions must be checked again by the
specialist rather than inferred from a module's title.

- [ObservablePrior](BookProof/OSReconstruction/ObservablePrior.lean),
  [PriorRefinement](BookProof/OSReconstruction/PriorRefinement.lean) and
  [ContinuumPrior](BookProof/OSReconstruction/ContinuumPrior.lean) give normalized
  information propositions, joint correlations, marginal/refinement invariance and monotone
  support-exhaustion limits. `ContPrior` **takes a probability measure as input**. It does
  not construct an interacting Euclidean measure or a limit of field theories.
- [MehlerMeasure](BookProof/EuclideanFock4D/MehlerMeasure.lean) proves invariance of
  `gaussianE 4`. It is a finite-coordinate control. Product-Hermite and Mehler transfer
  results provide bases, cores and Gaussian conjugations, not spacetime covariance of
  an interacting field on `R^4`.
- [FeynmanKac](BookProof/ReflectionPositivity/FeynmanKac.lean) and
  [LatticeFreeField](BookProof/ReflectionPositivity/LatticeFreeField.lean) provide the
  boundary-conditioned mean-of-squares RP mechanism and a Gaussian lattice action split.
  Normalization, continuum covariance and the physical interacting-state identification
  still need their own proofs. Local non-Gaussian potentials can also split at the
  reflection plane; degree four is not a universal obstruction to this method.
- [HalfSpaceComplex](BookProof/OSReconstruction/HalfSpaceComplex.lean) already supplies
  the complex Hilbert-space carrier and completeness. Older prose calling complexification
  wholly absent is superseded. Concrete state/field/semigroup compatibility remains open.
  [MultiplierSelfAdjoint](BookProof/OSReconstruction/MultiplierSelfAdjoint.lean) and the
  half-space exponential modules construct or identify flows under their multiplier/flow
  hypotheses; they do not instantiate the physical interacting model.
- [BalabanRG/Convergence](BookProof/BalabanRG/Convergence.lean) converts a summable
  increment bound to a limit. Its `FTotal` is an `ell²` sum of fixed 64-coordinate sectors.
  [BlockOperator](BookProof/BalabanRG/BlockOperator.lean) averages component slots at a
  cell. Replace these prototypes by the actual spatial/gauge coarse maps before using
  their names as an RG construction. The physical summable bound is not proved there.
- [SirkTrotterKato](BookProof/Sirk/ChapterSirkTrotterKato.lean) transfers assumed strong
  resolvent convergence to locally uniform **real-time** flow convergence.
  [SirkTrotterKatoGalerkin](BookProof/Sirk/ChapterSirkTrotterKatoGalerkin.lean) and
  [YangMillsFriedrichsLimit](BookProof/Qym/ChapterYangMillsFriedrichsLimit.lean) have
  bounded-operator regimes; they are not unbounded interacting continuum-limit proofs.
  Heat-semigroup transfer under a common lower bound is an additional stated task.
- [SirkEndToEnd](BookProof/Sirk/ChapterSirkEndToEnd.lean), truncation, finite-precision
  and resolvent-transfer modules supply conditional approximation receivers. Seed/range
  invariance and rational-approximation inputs must be read literally. An ordinary Krylov
  subspace is not generally invariant under the full resolvent. Reuse
  [softmodes.md](softmodes.md) **U0–U6** for leakage, tails, spectral coverage and constants.

### Intermediate archive results to reuse, in order

Read the following source interfaces before porting large dependency cones. The declaration
names below exist **in the archive**; they are not local `BookProof` declarations.

1. [WilsonBridge](../OpenAI-YM-20261028/WilsonBridge.lean): `energy_eq`, `law_eq`,
   `moment_eq`, `smear_eq`, `fromWilson`. These explicitly tie action, normalized law,
   insertions and separated smearings to the public Wilson family. Use their commuting
   diagram as the template for our Hamiltonian-to-Euclidean dictionary. `fromWilson`
   consumes an `Ordered` extraction; it does not itself prove the multiscale estimates.
2. [Extraction/Limits](../OpenAI-YM-20261028/YM/Extraction/Limits.lean):
   `Order.upon` retains an `Ordered` witness under refinement, and `Order.determined`
   identifies two smooth separated kernels obtained from the **same family and order**.
   This conditional uniqueness is useful for our bridge despite the absence of global
   theory uniqueness. `Order.evaluated` needs the additional `Meshes` compact-uniform
   hypothesis to pass moving lattice points to point values; a smeared limit or smoothness
   of the limiting kernel alone does not supply it.
3. [HierarchyBridge](../OpenAI-YM-20261028/HierarchyBridge.lean): `regular`, `hierarchy`,
   `wilsonLimit`, `publicReconstruction`, `publicOPE`. The regularity interface includes
   insertion locality and the bare-coefficient/log-inverse-mesh asymptotics. The hierarchy
   records selected and unselected correlations separately. Reconstruction and OPE consume
   the corresponding completed data for the **same** `Final` witness and reader.
4. [YM/Nonperturbative/Continuum](../OpenAI-YM-20261028/YM/Nonperturbative/Continuum.lean):
   `contacts_on`, `continuum`, `continuum_with_position_tests`. Their important reusable
   structure is simultaneous extraction, reconstruction, OPE and contact resolution, with
   `M.basis = Q.port`. Preserve that equality and witness dependency through every adapter;
   do not combine independently selected continuum and OPE witnesses.
5. [ContactBridge](../OpenAI-YM-20261028/ContactBridge.lean): `contactDistribution` produces
   a continuous functional on compact smooth tests whose separated restriction is the
   stated hierarchy, assuming its contact data. Use it to avoid rebuilding that extension
   for the selected archive witness. It does not prove uniqueness of contact terms, raw
   lattice convergence at collisions, or unrestricted-test reflection positivity.
6. [TraceBridge](../OpenAI-YM-20261028/TraceBridge.lean): `publicTrace` transfers the centered
   stress-trace short-distance law and its specified finite-Wick exclusions. First identify
   our physical observable with that trace, including electric and magnetic contributions;
   a magnetic component or ordinary polynomial degree is not sufficient. The local
   [free-mode exclusion](BookProof/Sm/ChapterSmFreeModeExclusion.lean) is also a conditional
   diagnostic with a finite comparison class, not an all-model classification.
7. [CompactCheck](../OpenAI-YM-20261028/verification/CompactCheck.lean): `compactCoefficient`
   and `compactRemainder` turn the public OPE contract into compact separated-set bounds.
   They are useful for a uniform-observable error norm; they do not by themselves give
   tightness of fields or an infrared estimate.
8. [VerifyJoint](../OpenAI-YM-20261028/VerifyJoint.lean),
   [Usage](../OpenAI-YM-20261028/verification/Usage.lean) and the archive's negative controls
   show how to check exact endpoint types, reachable definitions and transitive axiom
   footprints. Port that evidence discipline as well as mathematics. A standard-axiom
   footprint alone does not establish that two endpoint definitions agree.

The archive pins Lean **4.32.0** and this project **4.28.0**. Prefer a small standalone
adapter/specification and the minimum useful lemmas; pin all source/dependency revisions
and inspect licenses. A cross-version correspondence is a theorem/proof artifact to build,
not a working import assumed by prose. External verification logs remain dated evidence;
no replay is claimed here. Do not add the archive's conclusion as an untracked axiom.

### C0 — bind the physical object, reference state and cutoffs once

Start with **pure nonabelian QYM**, using the concrete gauge group/representation of the
chosen local Hamiltonian and a matching archive specialization. A smaller SU(2) control
requires its own explicit coefficient/representation adapter; it does not silently replace
the existing SU(3)-indexed model. Fix a renormalized observable scale and normalization,
bare-coupling/counterterm trajectory, boundary condition, physical sector and gauge quotient.
The final regulated Hamiltonian remains

```text
H_sigma = dGamma(h_sigma)
        = sum_ij <e_i,h_sigma e_j> Cdag(e_i) A(e_j).
```

The complete specified interacting **inner** operator, with scalar terms, is enclosed
between outer creation on the left and annihilation on the right. The fixed
99-coordinate QYM realization supplies a comparison with independent jet variables.
Construct the nested momentum operator on packets. An equivalence claim for the
99-coordinate model would require a separate map of domains and actions. Track Wilson
spacing and volume on the archive side, smearing on both sides, and Mehler occupation
cutoff, Krylov rank, rational order and precision on the numerical side. Increasing
the rank of a fixed projected solve advances neither the Wilson limits nor removal of
a physical smearing.

Select the spatial information prior and its joint law. A nonempty reference state is
necessary for the manuscript's number-preserving observables: `H Omega_out=0` and such
observables annihilate the empty outer vacuum. A general informational prior need not be
stationary or a ground state. For vacuum OS reconstruction establish ground-state/positive
energy conditions in the chosen physical cyclic sector; for mixed or infinite-information
limits use a GNS state, not a normalized infinite-occupation vector in ordinary outer Fock.
On a ground sector use `K_sigma=(H_sigma-E_ref,sigma I)|cyclic >= 0` as **relative**
dynamics. This does not erase inner constants: `h+cI` changes `H` by `c N_out`.

**Acceptance:** one witness/manifest binds all these choices, the positive-time algebra,
field labels, renormalized smearings and the comparison archive hierarchy. Do not accept
an arbitrary reference vacuum or field law in place of the specified physical object.

**Landed 2026-11-15, in the finite form below.**
`BookProof/OSReconstruction/ContinuumManifest.lean` writes the binder down and proves the
identities and rejections it has to support. No `sorry`; axiom footprint of every theorem
below `{propext, Classical.choice, Quot.sound}` only (`Work/ContinuumManifestAudit.lean`).

* **The manifest.** `NestedSpec` binds the specified inner column family `h_sigma`, the
  **physical cutoff** `(a, L, R)` (`PhysicalCutoff`), the **solver budget** `(m, q,
  precision)` kept separate from it (`SolverBudget`), the renormalized scale, the colour
  rank and the reference energy. `NestedSpec.finalHamiltonian` is `H_sigma = dΓ(h_sigma)`
  and `numberOperator` is `N_out = dΓ(1)`, on the corpus's finite-mode Fock algebra — the
  same operator the manuscript writes as `Σ_ij ⟨e_i, h_sigma e_j⟩ C†(e_i) A(e_j)`.
* **`h + cI = H + c N_out`, and nothing else.**
  `NestedSpec.finalHamiltonian_shift` proves the shifted manifest's Hamiltonian is
  `dΓ(h_sigma) + c • dΓ(numberCol)`, and `NestedSpec.relativeGenerator_shift` that the
  reference subtraction `K_sigma = H_sigma − E_ref • 1` moves by the same `c N_out`.
  `NestedSpec.relativeGenerator_vac` records that `K_sigma Ω_out = −E_ref • Ω_out`: the
  subtraction is relative dynamics and does not erase the inner constant.
* **The inner object is recoverable.** `dGamma_injective` proves `dΓ` determines its
  one-particle matrix (via `dGamma_oneVec` and `onePartVec_apply`), hence
  `NestedSpec.inner_eq_of_finalHamiltonian_eq` and `NestedSpec.finalHamiltonian_eq_of_inner_eq`:
  "the same `dΓ`" is a statement about `h_sigma`, not about notation.
* **The negative controls.** `shift_changes_model` rejects a nonzero inner constant shift;
  `droppedInteraction_rejected` rejects any other inner column family (in particular the
  free part, i.e. a discarded interaction); `krylov_not_continuum` proves that enlarging
  the Krylov rank changes no physical cutoff, so `m → ∞` at fixed `a, L, R` is not a
  spacetime continuum limit; `unrelatedAdapter_rejected` and `mismatchedBasis_rejected`
  reject an archive adapter on a foreign family or with `M.basis ≠ Q.port`, and
  `ContinuumWitness` carries the compatibility proof with the witness so the archive side
  cannot be re-chosen later.
* **The observable dictionary.** `FieldLabel` names a smeared field observable together with
  the scale it is smeared against, and `HalfSpaceData` binds the positive-time half of each
  label to a `PositiveTimeAlgebra` element, with
  `HalfSpaceData.labels_mem_positiveTime` (`θ` sends the labels to the negative-time half),
  `HalfSpaceData.theta_labels_dependsOn_negTime`, and
  `HalfSpaceData.label_outside_algebra_rejected`. `ObservableDictionary n Ω` pairs that
  algebra data with the spatial prior and proves `labels_mem_positiveTime`,
  `prior_prop_normalized`, `prior_corr_eq` (the dictionary in integral form) and
  `label_outside_rejected`. `ContinuumWitness` now carries this dictionary together with
  `halfSpace_eq`, so the positive-time algebra and the field labels are part of the same
  witness as the Hamiltonian and the cutoff.

The archive side is an **inventory, not an import**: `../OpenAI-YM-20261028` is absent in
this workspace, so `ArchiveAdapter` records the data a real adapter must supply (the
Wilson family as columns, the extraction order, the basis and port labels) and no archive
theorem is assumed, ported or added as an axiom. Boundary: `NestedSpec.inner` is a
concrete finite-mode column family, not a self-adjoint operator with an identified domain;
the growing spatial regulator family, the gauge group/representation, the bare-coupling
trajectory, the boundary condition and the numerical law of the spatial prior are still
inputs (the dictionary binds which labels and positive-time algebra they act on, not the
prior's values), and C2–C10 are untouched.

### C1 — complete a genuine 4D Gaussian control in Mehler coordinates

Construct the massive scalar reference on distributions with covariance
`C0=(-Delta_4+m0²)^(-1)`, `m0>0`, as a control for the analytic infrastructure. For a real
Schwartz test `f`, its characteristic functional is `exp(-C0(f,f)/2)`. Check all cylinder
laws and moment normalizations against the variance convention of the chosen Mehler basis.

The field takes values in `S'(R^4)`, or another explicitly controlled distribution space.
Do not require `C0^(1/2)` to be globally Hilbert–Schmidt on `L²(R^4)` or the field to be
an `L²` function: those requirements exclude the intended continuum free field. A countable
Gaussian/Hermite representation needs weighted negative-Sobolev estimates and distributional
convergence. This corrects the suggested global-Hilbert–Schmidt step in some source headers.
Use a nuclear-space extension theorem or construct consistent coordinates and prove their
almost-sure continuity as distributions. Both routes need an actual proof, not `ContPrior`.

Prove reflected-covariance positivity on half-space tests and lift it to all polynomial
cylinders via Wick/chaos or the boundary-conditioned kernel. A positive covariance matrix
alone is insufficient. The banded Toeplitz counterexample in
[HalfSpaceInfiniteBandedCovariance](BookProof/OSReconstruction/HalfSpaceInfiniteBandedCovariance.lean)
illustrates this. Doubling two halves to force positivity is not a proof that one coherent
translation-covariant field law exists on all of spacetime.

A possible source for the Gaussian-only task is
[OSforGFF](https://github.com/mrdouglasny/OSforGFF), whose README and master declarations
provide a distribution-valued free-field/OS interface. Its inspected toolchain is
[4.33.0-rc1](https://github.com/mrdouglasny/OSforGFF/blob/main/lean-toolchain).
Treat this as a candidate for a pinned source/axiom/type audit and selective port, not an
already imported or locally verified theorem. It supplies no interacting QYM bridge.

**Acceptance:** a non-ultralocal 4D free covariance, normalized law, smeared moments, RP
and Euclidean covariance, with cutoff convergence. This is a completed control case,
not proof that the nonabelian interaction survives removal of cutoffs.

**Landed 2026-11-15, in the finite cutoff form below.**
`BookProof/OSReconstruction/GaussianMehlerControl.lean` constructs the control on two time
slices and a finite three-dimensional momentum box, in Mehler coordinates. No `sorry`; axiom
footprint `{propext, Classical.choice, Quot.sound}` only (`Work/GaussianMehlerAudit.lean`).

* **The covariance.** With `SpatialMode M = Fin M × Fin M × Fin M`,
  `spatialEigenvalue k = Σ_j (k_j + 1)²` and `variance m₀ p = 1/(m₀² + spatialEigenvalue
  (p.2) + (if p.1 then 1 else 3))`; `variance_pos` gives strict positivity. The two time
  slices are correlated, so the covariance is **not ultralocal** and is genuinely 4D (three
  spatial momenta times two time slices). `variance_symm_ge_antisymm` proves the symmetric
  Mehler mode dominates the antisymmetric one.
* **The normalized law.** `law m₀` is the product of one-dimensional Gaussians over modes and
  `law_isProbability` proves it is a probability measure.
* **Cylinder laws and moments.** `marginal` computes every one-mode cylinder law as
  `gaussianReal 0 (variance …)`; `charFun_one_mode` gives the one-mode characteristic
  functional `∫ exp(i t y_p) dμ = exp(−variance · t²/2)`; `second_moment` gives the smeared
  second moment `∫ y_p² dμ = variance m₀ p`.
* **Euclidean covariance and reflection.** `covBilin` is the diagonal Mehler covariance
  form, `covBilin_self_nonneg` its positivity, `reflectMehler` the time reflection
  (`y₊ ↦ y₊`, `y₋ ↦ −y₋`) with `reflectMehler_involutive`, and `reflection_invariant` the
  Euclidean-covariance clause `C(θf, θg) = C(f, g)`.
* **Reflected-covariance positivity on half-space tests.** `posTest` lifts a spatial test to
  the positive-time slice; `rp_covariance` proves `C(θf, f) ≥ 0` for `f = posTest g`, reducing
  to `∑_k (variance (true,k) − variance (false,k)) · g k²/4 ≥ 0`.
* **The negative control.** `badVariance` swaps the two Mehler eigenvalues while staying
  strictly positive, so `badCovBilin` is a positive-definite diagonal covariance; `bad_rp_fails`
  exhibits a spatial test with `badCovBilin (θf) f < 0`. A positive covariance matrix alone
  is therefore insufficient, matching
  [HalfSpaceInfiniteBandedCovariance](BookProof/OSReconstruction/HalfSpaceInfiniteBandedCovariance.lean).
* **Cutoff consistency.** `embedMehler` includes a mode into the next cutoff,
  `spatialEigenvalue_embed` and `variance_embed` show the variance is cutoff-independent on
  the common modes, and `marginal_embed` shows the one-mode cylinder laws of the `M` and
  `M + 1` cutoffs agree there.

Boundary: this is the finite-dimensional control, not the `S'(R⁴)` field. The lift of
reflected-covariance positivity from the covariance form to **all polynomial cylinders** is
the next paragraph; no globally Hilbert–Schmidt `C₀^{1/2}`, no `L²(R⁴)` field and no
`S'`-valued `M → ∞` limit is constructed here; only the consistent finite-dimensional
cylinder laws are.

**Landed 2026-11-15, all-degree lift via the boundary-conditioned kernel.**
`BookProof/OSReconstruction/GaussianMehlerCylinderRP.lean`. No `sorry`; axiom footprint
`{propext, Classical.choice, Quot.sound}` only (`Work/GaussianMehlerAudit.lean`).

* **Why not Wick.** Degree two collapses the Isserlis sum to a square
  (`ReflectionPositivity/QuadraticWick.lean`), but from degree three the pairing sum is a
  permanent of the reflected kernel and carries no sign in general; the *Wick* route therefore
  cannot be iterated. The all-degree mechanism is the kernel factorization of the free state.
* **The kernel form.** With `v₊ k = variance m₀ (true, k)` and `v₋ k = variance m₀ (false, k)`,
  the C1 covariance in the slice coordinates `x₀ = (y₊ − y₋)/√2`, `x₁ = (y₊ + y₋)/√2` is
  `[[A, B], [B, A]]` with `A k = (v₊ k + v₋ k)/2` and `B k = (v₊ k − v₋ k)/2 ≥ 0`
  (`variance_symm_ge_antisymm`). It is exactly the covariance of the shared-shift state
  `x₀ = T + X`, `x₁ = T + Y` with `T, X, Y` independent and `Var T k = B k`, `Var X k =
  Var Y k = v₋ k`; `shiftVariance`, `noiseVariance`, `shiftLaw`, `noiseLaw`, `kernelMap`,
  `kernelLaw` write it down, `kernelLaw_isProbability` proves it is normalized, and
  `sliceVariance_eq` records `B k + v₋ k = A k`.
* **The lift.** `kernelLaw_reflectionPositive` proves, for **every bounded measurable**
  cylinder observable `F` of one half, `0 ≤ ∫ z, F z.2 * F z.1 ∂(kernelLaw m₀)`. Conditioning
  on the shared shift makes the halves independent copies of `T + X`, so the OS form is the
  boundary average of `(∫ F (t + x) ∂γ)²`: one square, no degree restriction.
* **Polynomial cylinders.** `kernelLaw_reflectionPositive_of_integrable` replaces boundedness
  by integrability of the OS integrand, which is the form an unbounded polynomial takes:
  `P (T + X) * P (T + Y)` is a polynomial in Gaussian variables. Polynomials are therefore
  covered by the same inequality, with the polynomial-times-Gaussian moment input supplied as
  the hypothesis rather than recomputed.
* **The slice bridge.** `timeZero`, `timeOne` express the slices as functions of a Mehler
  configuration and `timeZero_reflect`/`timeOne_reflect` prove that the Mehler reflection
  swaps them, so the kernel state is the slice-coordinate form of the C1 covariance.

Boundary of the lift: the identification with the Mehler law is at the level of the
**covariance** (same two-point function, hence the same free `C₀`); equality of the two
Gaussian laws is not formalized, and the unconditional theorem is the bounded-observable one,
with polynomials entering through the integrability variant. The transfer operator is the
mixture average over the boundary law, not an interacting dynamics.

### C2 — construct the regulated interacting state and its Euclidean dictionary

At fixed `a,L`, close/select `h_sigma` and its outer lift on the specified common core.
Use the actual selection theorems; finite Hermite matrices are computational approximations
until unbounded tails and domains are controlled. Construct physical smeared observables,
adjoints, constraints and locality relations. Prove the reference-state conditions in C0.

For ordered Euclidean times, define the candidate moments by the corresponding products
of observables and `exp(-(t_(i+1)-t_i) K_sigma)` between reference vectors. Prove domain
and integrability for every word. Then establish their extension/permutation conventions,
stochastic positivity where a classical field law is asserted, and half-space OS positivity.
A positive self-adjoint Hamiltonian gives a contraction semigroup; it does **not** alone
supply a positive classical path measure or full Euclidean rotation covariance.

Where applicable, identify a configuration representation with a positivity-preserving
semigroup and a positive ground function. A ground-state transform can then supply a
Markov kernel and Feynman–Kac law, provided normalization and consistency are proved.
For gauge-invariant observables compare with positive group-valued Wilson measures and
retain the full gauge/constraint dictionary. A signed ghost or gauge-fixed density must
not be presented as a probability law. Otherwise work with the physical observable
hierarchy and its explicitly proved positivity axioms.

**Acceptance:** nonzero separated correlations with nontrivial time dependence, RP on the
physical positive-time algebra and the regulator-level moment/observable bridge. Independent
half-space replicas with identically zero connected cross correlations do not pass this gate.

**Landed 2026-11-15, first slice: the moment hierarchy at the regulator.**
`BookProof/OSReconstruction/EuclideanMomentHierarchy.lean`. No `sorry`; axiom footprint
`{propext, Classical.choice, Quot.sound}` only (`Work/EuclideanMomentAudit.lean`).

* **Euclidean evolution.** `euclidEvol K t = e^{-tK}` for a **bounded** generator `K` on a
  complete complex Hilbert space, with `euclidEvol_zero` and the semigroup law
  `euclidEvol_add` (exponentials of commuting multiples of one generator), plus
  `commute_euclidEvol`.
* **Words and moments.** `euclidWord K A word` is the ordered product
  `A e^{-Δ₁K} A₁ ⋯ e^{-ΔₙK} Aₙ`, and `euclidMoment K Ω A word = ⟨Ω, (that product) Ω⟩`.
  `euclidWord_append` gives the **extension convention**: splitting a word at a gap composes
  the two operator products. `euclidMoment_nil` and `euclidMoment_one_nil` give the empty
  word and the normalization `⟨Ω, Ω⟩ = 1` of a unit reference vector.
* **Two-point positivity at coincident times.** `euclidMoment_zero_adjoint` proves
  `⟨Ω, A† A Ω⟩ = ‖A Ω‖²`, hence `euclidMoment_zero_adjoint_re_nonneg`: the regulator-level
  square the separated-time half-space form has to generalize.
* **Nonzero, time-dependent correlation.** The one-mode free regulator `scalarK m = m • 1`
  has `euclidMoment_scalarK`: `⟨1, e^{-tK} 1⟩ = e^{-tm}`; `euclidMoment_scalarK_re_pos` makes
  it strictly positive for every `t`, and `scalarMoment_ne_one` proves the time‑`1` and
  time‑`0` moments differ for `m ≠ 0`. That is the C2 acceptance's non‑triviality condition at
  the free regulator level.

Boundary of this slice: `K` is bounded, so this is the finite‑mode regulator with every
moment a finite scalar (domain and integrability hold by construction); the unbounded
`h_sigma` closure and its selection are not built. Half-space OS positivity at the
**interacting** regulator, the configuration/field-law representation, and the
positivity-preserving semigroup with ground function are not constructed: moments of a
positive `K` are not a classical path measure, and the scalar free moment is not evidence
that the interaction survives cutoff removal.

**Landed 2026-11-15, second slice: separated-time two-point functions and their
reflection positivity at the regulator.** Same module, same audit; axiom footprint
unchanged (`Work/EuclideanMomentAudit.lean` now covers 31 declarations).

* **Separated-time two-point functions.** `twoPoint K Ω A B h = ⟨Ω, A e^{-hK} B Ω⟩` — `A`
  inserted at time `0`, `B` at the later time `h`; `twoPoint_eq` unfolds it,
  `twoPoint_zero` is the coincident-time value, and `twoPoint_adjoint_zero`
  (`⟨Ω, A† A Ω⟩ = ‖A Ω‖²`) is the square at zero separation.
* **The reflected (OS) form.** For a finite family of insertions `(sᵢ, Aᵢ)` with
  `sᵢ ≥ 0`, time reflection sends `Aᵢ` at `+sᵢ` to `Aᵢ†` at `−sᵢ`; the reflected form is
  `reflectedForm K Ω f = Σᵢ Σⱼ ⟨Aᵢ Ω, e^{-(sᵢ+sⱼ)K} Aⱼ Ω⟩`. Its entries are exactly the
  separated-time two-point functions (`euclidMoment_adjoint_pair`,
  `euclidMoment_adjoint_eq_inner`).
* **Reflection positivity.** For a **self-adjoint** generator the evolution `e^{-sK}` is
  self-adjoint (`euclidEvol_isSelfAdjoint`), so `reflectedForm_eq_inner` collapses the
  double sum to `‖Σᵢ e^{-sᵢK}(Aᵢ Ω)‖²`, all degrees at once, and `reflectedForm_re_nonneg`
  gives nonnegativity. The explicit two-insertion statement is
  `twoPoint_reflected_eq_normSq` / `twoPoint_reflected_re_nonneg`: the four-term form is the
  squared norm of `e^{-sK}(A Ω) + e^{-tK}(B Ω)`. `reflectedForm_scalarK_re_nonneg` is the
  free-regulator instance.
* **Calibration against C1** (`BookProof/OSReconstruction/EuclideanMehlerCalibration.lean`).
  The C1 Mehler slice covariance is `C = [[A,B],[B,A]]` with `A = (v₊+v₋)/2`
  (`sliceDiagonal`) and `B = (v₊−v₋)/2` (`sliceCross`); `sliceCross_eq_shiftVariance` and
  `sliceDiagonal_eq_shiftVariance_add_noiseVariance` tie it to the boundary-conditioned
  kernel, and `sliceCross_pos` / `sliceCross_lt_sliceDiagonal` show `B/A ∈ (0,1)`. In the
  state `Ω = √A` the free one-mode regulator has `⟨Ω, e^{-hK} Ω⟩ = A e^{-hm}`
  (`euclidMoment_scalarK_sqrt`), so `free_regulator_reproduces_slice_covariance` produces a
  mass `m = −log(B/A) ≥ 0` for which the zero-separation moment is `A` and the unit-separation
  moment is `B`: **the C1 slice covariance is exactly a free-regulator two-point function**.
  `free_regulator_twoPoint_reflected_re_nonneg` is reflection positivity at that calibration.

Boundary of this second slice: the calibration is a statement about the **two-point
function** at one mode and unit separation, not equality of laws — the scalar regulator's
moments are not the Mehler path measure, and no field law or transfer operator is
identified. The mass is the free mass that reproduces the covariance ratio `B/A`, not the
physical cutoff mass. Self-adjointness of the generator is used for RP; positivity of the
diagonal moment `⟨A† e^{-hK} A⟩` at separated times is **not** claimed (it needs a positive
evolution, i.e. a spectral hypothesis, which this slice does not establish). Reflection
positivity here is the regulator statement `⟨θF, F⟩ = ‖·‖²`; the interacting half-space
OS inequality remains open.

**Landed 2026-11-15, third slice: the reflected form as a positive semidefinite form.**
Same module, same audit; axiom footprint unchanged (42 declarations now audited). This is the
first reconstruction step at the regulator: RP already *is* an inner product, so no measure
theory is needed to see that the positive-time pair form is well defined.

* **The reflected pairing.** `reflectedPair K Ω f g = Σᵢ Σⱼ ⟨Aᵢ Ω, e^{-(sᵢ+sⱼ)K} Bⱼ Ω⟩` for
two finite families, with the same index type or different ones; `reflectedPair_self` recovers
the reflected form on the diagonal, and `reflectedPair_eq_inner` identifies the pairing with
`⟪reflectedVector f, reflectedVector g⟫` (self-adjoint `K`). `reflectedPair_conj_swap` is
conjugate symmetry: `reflectedPair g f = conj (reflectedPair f g)`.
* **Null space.** `reflectedForm_re_eq_normSq` gives `(reflectedForm f).re = ‖reflectedVector f‖²`,
so `reflectedForm_eq_zero_iff` shows a family is null exactly when its reflected vector
vanishes, and `reflectedPair_eq_zero_of_null` shows null families pair to zero with everything:
the pairing descends to the quotient by null vectors, which is the reconstructed Hilbert space's
first well-definedness obligation at the regulator.
* **Cauchy–Schwarz.** `reflectedPair_cauchy_schwarz`: `‖reflectedPair f g‖ ≤ √(reflectedForm f).re · √(reflectedForm g).re`.
The distinguished corollary is `twoPoint_cauchy_schwarz`: for a self-adjoint generator
`‖⟨A† e^{-(s+t)K} B⟩‖² ≤ ⟨A† e^{-2sK} A⟩.re · ⟨B† e^{-2tK} B⟩.re`, i.e. the two-by-two reflected
matrix of a pair of insertions is positive semidefinite — the standard OS bound on the
separated-time two-point function, obtained without any spectral or positivity-of-evolution
hypothesis beyond self-adjointness.

Boundary of this third slice: this is the pairing of the **regulator**, built from bounded
observables and bounded `K`; the quotient space is constructed only as a set of null classes
(no completion, no topology, no measure), and Cauchy–Schwarz is proved through the explicit
norm identity rather than by abstract form theory. Everything stated is about the reflected
pairing of finitely supported families; the interacting half-space inequality, the
reconstruction theorem, and the field law remain open.

**Landed 2026-11-15, fourth slice: the reconstructed pre-Hilbert space at the regulator.**
Same module; axiom footprint unchanged (55 declarations now audited). The object built is
the regulator-level reconstruction itself: the quotient of families by null families carries
a genuine inner product, realized isometrically inside the regulator Hilbert space.

* **The reconstruction map.** Separating the insertion times from the operators,
  `familyVector K Ω s A = Σᵢ e^{-sᵢK}(Aᵢ Ω)` is additive (`familyVector_add`) and
  complex-homogeneous (`familyVector_smul`) in the operators, so it is the underlying map of
  a complex-linear map `familyVectorLM`. The reflected pairing is then the ambient inner
  product of images, `familyPair K Ω s A t B = ⟪familyVector K Ω s A, familyVector K Ω t B⟫`,
  with `familyForm` its diagonal; `familyPair_eq_reflectedPair` proves this is the same
  pairing as the section 6 double sum over separated-time two-point functions.
* **The inner-product axioms on classes.** Additivity in each family
  (`familyPair_add_left`/`familyPair_add_right`), `familyForm_eq_normSq`,
  `familyForm_re_nonneg`, positive definiteness modulo nulls (`familyForm_eq_zero_iff`),
  `familyPair_eq_zero_of_null`, and `familyPair_congr_left`: the pairing is a function of the
  class of the reflected vector. `familyForm_sub_re_eq_dist_sq` identifies the class distance
  with the ambient distance of reflected vectors, and `familyPair_cauchy_schwarz` is
  Cauchy–Schwarz for the class pairing.
* **The capstone.** `reflected_reconstruction` bundles these: the pairing is the inner
  product of the images of a linear map, that map's kernel is exactly the null families, the
  diagonal is nonnegative, and Cauchy–Schwarz holds. Completing the range therefore yields
  the reconstructed Hilbert space, and the quotient is a pre-Hilbert space isometric to it.

Boundary of this fourth slice: **pre-Hilbert, not Hilbert.** The quotient is realized as a
subspace of the regulator space rather than as its own type; no completion, no topology on
classes, no cyclic-vector or time-translation action on the reconstructed space is built.
The inner product is the ambient one, so the result is honest but structural — it exhibits
what RP already delivers at the regulator and does not address the interacting half-space
inequality, the OS reconstruction theorem, or any field law.

**Landed 2026-11-15, fifth slice: the coarse density of a block step (C3a, first packet).**
New module `BookProof/OSReconstruction/GaussianBlockCoarseDensity.lean`; axiom footprint
unchanged (76 declarations now audited, all `propext`/`Classical.choice`/`Quot.sound`). The
plan's density warning is now a theorem instead of a caution: the coarse density of `|Psi|²`
is `E[|Psi|² | G]`, and it is not `|E[Psi | G]|²`.

* **The reference system.** Two independent unit Gaussians, one coordinate per variable: the
  first is the block, the second the exterior field. Coarse graining is the partial integral
  `blockIntegral f y = ∫ x, f (x, y) ∂gamma`, and `integral_blockIntegral` is the tower
  identity `∫ f ∂(gamma ⊗ gamma) = ∫ (blockIntegral f) ∂gamma` — integrating the coarse
  density over the exterior fields recovers the joint integral.
* **The step as a map.** `blockIntegral_add`, `blockIntegral_nonneg`, `blockIntegral_const`,
  `blockIntegral_exterior`: additive on integrable slices, pointwise nonnegative, normalised at
  constants, and fixing observables of the exterior field. `blockIntegral_mul_exterior` is the
  characterising identity — pairing `blockIntegral f` against an exterior test function
  reproduces the joint integral of `f` times it — which is what makes the partial integral the
  conditional expectation, with no sigma-field ever chosen.
* **The two densities.** For the cylinder observable `Psi_c (x, y) = x + c y`,
  `blockIntegral_blockField` gives the conditional mean `c y` and
  `blockIntegral_blockField_sq` gives the coarse density `1 + c² y²`.
  `coarseDensity_eq_naiveDensity_add` identifies the gap as the conditional variance `1`, and
  `coarseDensity_ne_naiveDensity` shows the prescriptions genuinely differ (`1` versus `0` at
  `y = 0`). The totals separate too: `integral_naiveDensity` is `c²`, `integral_blockField_sq`
  is `1 + c²`, so `variance_decomposition` reads `∫ |Psi|² = ∫ naiveDensity + 1` and
  `integral_coarseDensity_eq_integral_blockField_sq` confirms the coarse density reproduces the
  mean of `|Psi|²` while the naive one cannot.

Boundary of this fifth slice: **one block, real fields, no RG map.** The system is two real
coordinates with a Gaussian reference law; no scale iteration, measure-level pushforward,
gauge transport, constrained covariance, Haar/coarea/Faddeev–Popov factor or boundary
condition is represented. The conditional expectation is the characterising identity on
cylinder test functions, not a `condExp` construction, and the coarse-versus-naive theorem is
a statement about this one Gaussian system, not a lower bound for interacting or gauge
theories. C3b (small fields), C3c (large fields) and C3d (running parameters) remain open, as
do the interacting half-space inequality, the OS reconstruction theorem and any field law.

**Landed 2026-11-16, sixth slice: the step iterated twice, and the C3b packet it supports.**
Same module `BookProof/OSReconstruction/GaussianBlockCoarseDensity.lean`; axiom footprint
grown from 76 to 96 audited declarations, all `propext`/`Classical.choice`/`Quot.sound`. The
step of the fifth slice is now a map that can be applied twice, and the small-field packet is
proved for it instead of promised.

* **The chain.** A three-coordinate reference law `blockChainLaw = (gamma ⊗ gamma) ⊗ gamma`,
  an inner block, a shell and the exterior field. `blockStep f z y = ∫ x, f (x, z, y)` is the
  fifth slice's partial integral, and `blockChainDensity f y = ∫ z, blockStep f z y` applies it
  to the shell, so the second step is literally the same map one scale down
  (`blockChainDensity_eq_iterated`). `integral_blockChainDensity` is the tower identity for the
  composition, and `blockChainDensity_const`/`_nonneg`/`_add`/`_exterior` re-establish the
  positive-unital-fixing-the-exterior structure for the composed map.
* **The cylinder field.** For `Psi_{c,d}(x, z, y) = x + c z + d y`,
  `blockStep_blockChainField` gives `c z + d y` after the first step and
  `blockChainDensity_blockChainField` gives `d y` after the second: the interior coupling `c`
  is invisible at the coarse scale (`blockChainDensity_blockChainField_independent`), which is
  the background-stability statement, and `blockChainDensity_blockChainField_sq` gives the
  density `1 + c² + d² y²`.
* **C3b on this system.** The accumulated covariance is `1 + c²`, exactly and uniformly
  (`blockChainCovariance_eq`), independent of the exterior background
  (`blockChainCovariance_independent_of_background`) and bounded between `1` and `2` under the
  small-field hypothesis `|c| ≤ 1` (`blockChainCovariance_small_field`): an explicit-constant
  local covariance bound, scale-uniform in the only sense available here. The activity norm is
  defined rather than assumed (`blockActivityNorm`, `blockChainActivityNorm`) and a coarse step
  contracts it: `integral_abs_partialIntegral_le` for a general block measure,
  `integral_abs_blockIntegral_le` for one step, `integral_abs_blockChainDensity_le` for the
  chain.

Boundary of this sixth slice: **two steps, still not an RG map.** The chain iterates the
operation but not the scale — every coordinate is a fresh independent Gaussian, so no
rescaling, translation, renormalisation or measure pushforward happens between the steps, and
no lattice or gauge structure is present. The C3b claims are correspondingly narrow: the
covariance bound is an identity with an explicit constant rather than an elliptic, derivative
or Hessian estimate for an interacting measure; the activity estimate is L¹ contraction, not a
polymer expansion with a summable activity ledger and localisation; no background stability for
a non-Gaussian law, no large-field complement (C3c), no running coupling trajectory (C3d) and
no observable limit estimate (C3e) is proved. The interacting half-space inequality, the OS
reconstruction theorem and any field law also remain open.

**Landed 2026-11-16, seventh slice: the totals and the large-field complement (C3c at reference
scale).** Same module; 96 → 103 audited declarations, all standard axioms. C3b bounds the
covariance where the *coupling* is small; this slice closes the bookkeeping of the chain and
disposes of the opposite regime, where the *background field* is large.

* **The totals.** `integral_blockChainDensity_sq` gives `∫ coarse = 1 + c² + d²` and
  `integral_blockNaiveChainDensity` gives `∫ naive = d²`, so
  `integral_blockChainDensity_eq_integral_naive_add` states `∫ coarse = ∫ naive + (1 + c²)`:
  the total excess is exactly the constant that bounds the covariance pointwise.
* **Where the naive error lives.** `blockNaiveChainDensity_zero_background` and
  `blockChainDensity_sq_zero_background`: at zero background the naive density is `0` while the
  coarse density is `1 + c²`. The naive prescription is therefore *most* wrong exactly where the
  small-field packet applies, which is why the complement must be a relative statement.
* **The complement.** `blockChainCovariance_le_coupling_sq`: `|c| ≤ M ⇒ cov ≤ 1 + M²` — quadratic
  degradation in field strength, no exponential growth in the coupling.
  `blockChainCovariance_le_mul_density`: if `√(2/ε) ≤ |d y|` and `|c| ≤ 1` then
  `cov ≤ ε · coarse density`, so for `ε = 1`, `|d y| ≥ √2`, the accumulated variance is at most
  half of the density it corrects. Large fields are easy because the covariance is a fixed
  constant, not a field-dependent fluctuation covariance.

Boundary of this seventh slice: **large fields are easy only because the reference covariance is
constant.** `blockChainCovariance_le_mul_density` does not bound a fluctuation covariance, does
not control a bad-block region or its entropy, and proves no summable tail — C3c in the plan's
sense (the complement of an *interacting* small-field region with a summable tail after
normalisation and insertions) is untouched. `blockChainCovariance_le_coupling_sq` is a quadratic
bound in the coupling, not a large-field expansion, and the small-field packet it complements
is still an exact identity for two steps of a reference Gaussian. Arbitrarily many UV scales
(C3d) and the observable limit estimate (C3e) remain open, as do the interacting half-space
inequality, the OS reconstruction theorem and any field law. The most valuable next item on this
thread is not another identity of the same system but the scale-indexed version: an `n`-step
chain with covariance `∑_{j<n} c^{2j}` and an `n`-uniform bound.

**Landed 2026-11-16, eighth slice: the step iterated through arbitrarily many scales (C3d, first
packet).** New module `BookProof/OSReconstruction/GaussianChainScales.lean`, importing the
coarse-density module; 103 → 118 audited declarations of this thread, all standard axioms. The
number of steps is now a parameter, and the C3d requirement is proved in the only form this
reference system supports: the local covariance bound does **not** degrade with the number of
scales.

* **Scale-indexed data.** `shellLaw n = gamma^{⊗ n}` on `Fin n → ℝ`; `shellDensity n f y` is the
  `n`-fold partial integral (first `n` coordinates out, last one held at `y`); `streamField c d n`
  obeys `Psi_n(z, g) = z + c * Psi_{n-1}(g)` with exterior weight `c^n d` — the geometric weights
  of a rescaling by `c` per scale, i.e. the coupling trajectory `d ↦ c d`.
* **The density identity.** `shellDensity_quadratic`: for every `n`, a quadratic functional of the
  field has coarse density the same functional at the *running* mean `c^n d y` with `K_n` in place
  of the one-step variance. Hence `shellDensity_streamField` (running mean `c^n d y`),
  `shellDensity_streamField_sq`, and `shellDensity_streamField_covariance`: the covariance after
  `n` steps is `K_n`, independent of the background field and of its coupling.
* **The covariance recursion and the `n`-uniform bound.** `streamCovariance_succ`:
  `K_{n+1} = 1 + c² K_n` — one unit per integrated scale; `streamCovariance_closed_form`:
  `K_n = ∑_{j<n} c^{2j}`; `streamCovariance_le_card`: `c² ≤ 1 ⇒ K_n ≤ n`; and
  `streamCovariance_le_inv`: `c² < 1 ⇒ K_n ≤ 1/(1 − c²)` **uniformly in `n`**. The total after
  `n` scales is `integral_shellDensity_streamField_sq`: `K_n + c^{2n} d²`.
* **The measure-level step.** `integral_shellLaw_cons`: the reference law of `n + 2` coordinates
  splits as `blockUnit ⊗ shellLaw (n + 1)`, so each step of the density recursion is a genuine
  partial integral over the reference law at every scale, not only a formal iteration.
* **The fixed point.** `K ↦ 1 + c² K` has the fixed point `K* = 1/(1 − c²)`, and the error is
  exact: `streamCovariance_inv_sub` gives `K* − K_n = (c²)^n/(1 − c²)`; hence
  `streamCovariance_lt_inv` (`c ≠ 0 ⇒ K_n < K*`) and `tendsto_streamCovariance`
  (`c² < 1 ⇒ K_n → K*`). `tendsto_integral_shellDensity_streamField_sq` carries the limit over
  to the total `K_n + c^{2n} d²` at fixed background. The `n`-uniform bound is thus the shadow of
  a convergent recursion, and the domain is preserved *because* the trajectory converges inside
  it.
* **The large-field tail at every scale.** C3c asks for control of the complement; at the
  reference scale that is Chebyshev inside the iterated integral. `shellDensity_congr` and
  `shellDensity_nonneg` supply the structural facts, and
  `shellDensity_affine_field_le` proves the induction: for any `a, b`,
  `P{M ≤ |a·(field − running mean) + b|} ≤ (a² K_n + b²)/M²`. The step multiplies `a` by `c` and
  adds the unit variance of the new coordinate, which is precisely `K_{n+1} = 1 + c² K_n` — the
  tail recursion *is* the covariance recursion. Hence `shellTail_le`: `P{M ≤ |field − mean|} ≤
  K_n/M²`, uniformly in `n` for `c² < 1`.

Boundary of this eighth slice: **a weight, not a renormalisation.** `streamField` multiplies by
`c` and `d ↦ c d` is a definition; the law remains a product of fresh independent Gaussians, so
nothing is rescaled, blocked or pushed forward and there is no effective action, counterterm,
marginal/irrelevant direction, volume or separation dependence, and no logarithmic running. The
`n`-uniformity — and its sharp form, geometric convergence to `K*` — is exactly what the
triviality of the reference recursion buys, and the bound degenerates as `c² → 1`, so it says
nothing about a critical point: the fixed point that is reached is that of `K ↦ 1 + c² K`, a
geometric series, not the critical fixed point of an interacting flow. One gap is closed and one
remains: the tower identity is now proved at every scale (the next entry), but only for bounded
observables, so the moment statements of this slice are still read as iterated integrals; and the
tail bound `shellTail_le` is Chebyshev on a second moment: it is a moment estimate with no
bad-block entropy, no polymer
expansion and no small-field/large-field decomposition of an interacting weight, and it carries no
gauge chart, volume or insertion dependence. C3e and the interacting C3a–C3d packets remain open,
as do the interacting half-space inequality, the OS reconstruction theorem and any field law.

**Landed 2026-11-16, ninth slice: the tower identity at every scale (C3d, measure-level
coherence).** The gap left by the previous two slices was the composition of the recursion: the
density is the iterated partial integral, and only the two-step tower
(`integral_blockChainDensity`) related it to a `shellLaw`-integral. It is now proved at every
`n`, for measurable **bounded** observables, and the previous slice's diagnosis was too
pessimistic: no Fubini permutation is needed. Thirteen declarations were added to the audit, all
on standard axioms.

* **The trick is an indexing choice, not a measure-theoretic one.** Fix the exterior coordinate
  as the *last* one (`Fin.snoc`) and split the product law at its *first* one: then the
  recursion's peel and the tower's split act on the same coordinate and compose with no swap.
  The proof is `shellDensity_eq_integral_snoc`
  (`shellDensity n f y = ∫ g, f (Fin.snoc g y) ∂shellLaw n`), by induction on `n`; the one `Fin`
  fact it needs is `fin_cons_snoc` (`cons z (snoc g y) = snoc (cons z g) y`), and the one measure
  fact is `integral_shellLaw_cons_succ`, the product-law splitting of `integral_shellLaw_cons`
  with an `m`-dimensional shell, so that it also covers `m = 0`.
* **The tower.** `integral_shellDensity_eq`: for measurable bounded `f`,
  `∫ y, shellDensity n f y ∂blockUnit = ∫ p, f p ∂shellLaw (n + 1)`. Integrability of the
  sections — which is what a Fubini proof would have bought, and what blocks the general case —
  is supplied here by a uniform bound through `Integrable.of_bound` and
  `abs_shellDensity_le` (`|f| ≤ B ⇒ |shellDensity n f y| ≤ B`), plus the measurability facts
  `measurable_fin_cons`, `measurable_fin_snoc`, `measurable_fin_snoc_prod`,
  `measurable_comp_fin_cons`, `measurable_comp_fin_snoc`.
* **What that buys.** The tail is no longer a formal iterated integral: `shellTail_eq_integral_snoc`
  writes `shellTail n c d y M` as the reference-law expectation of its indicator over the `n`
  inner coordinates at fixed exterior value, using `measurable_streamField`. The indicator is
  bounded, so the tower of this slice covers exactly the large-field object of the previous one.

Boundary of this ninth slice: **coherence of the definitions, not an estimate, and bounded
observables only.** The tower says that integrating one observable over a product of independent
Gaussians can be done inner-first or outer-first; it contains no blocks, pushforwards, effective
action or interacting weight, and it does not by itself bound anything. The polynomial field
moments (`integral_shellDensity_streamField_sq`, the fixed-point limit, `shellTail_le`) are *not*
covered: extending the tower to them requires `L¹` section hypotheses in place of a uniform bound,
or a joint-integrability development for polynomial observables, and until then those statements
remain statements about the iterated integral. The natural next step on this thread is precisely
that extension — the moment observables are the ones the plan's estimates are about, and they are
the only reason the boundedness hypothesis is there.

**Landed 2026-11-16, tenth slice: the law-level tail and tightness (C3e, first packet).** The
tail of the previous slices was a *density* at fixed exterior value, which is why it could not be
compared with a probability. Applying the tower to its indicator moves it to the level of the law,
and the estimate becomes a statement about a measure of a set. Sixteen declarations were added to
the audit, all on standard axioms.

* **The substitution.** `shellDensity_subst_last`: substituting the vector's last coordinate for
  the exterior parameter does not change the iterated partial integral, because the only vector
  the recursion finally applies the observable to already carries the exterior value in its last
  slot. That makes `renormField c d n p = streamField c d n p − c^n d · p(last)` the honest
  renormalised observable and `shellTail_eq_density_renorm` the identification of the density-
  level tail with the density of `renormField`'s large set.
* **The law-level tail.** `shellTailLaw n c d M` is `(shellLaw (n+1)).real {p | M ≤ |renormField
  p|}`, with `integral_shellTail_eq` (the tower at the indicator) and `shellTailLaw_eq_integral`
  (`integral_indicator_one`) tying it to the density-level tail; `shellTailLaw_nonneg` and
  `shellTailLaw_le_one` say it is in `[0, 1]`.
* **The estimate.** `shellTailLaw_le`: `P{M ≤ |renorm|} ≤ K_n/M²`; `shellTailLaw_le_inv`: for
  `c² < 1`, `≤ 1/((1 − c²)M²)`, *uniformly in `n`*. `exists_shellTailLaw_le` is the consequence
  C3e asks for first: for every `ε > 0` there is one threshold `M > 0` with
  `shellTailLaw n c d M ≤ ε` at every number of scales — **tightness** of the laws of the
  renormalised observables.

Boundary of this tenth slice: **tightness of one scalar sequence, not a limit theorem.**
`exists_shellTailLaw_le` supplies the analytic hypothesis of Prokhorov's theorem on the line;
Prokhorov's theorem itself, a limiting law, a summable Cauchy estimate for correlations and any
multi-point function remain open, so C3e is started and not reached. The renormalisation is the
subtraction of the damped background `c^n d` read off the exterior coordinate — a subtraction
chosen to make the second moment scale-uniform, not the subtraction of an interacting divergence,
and no observable is shown to converge. The interacting C3a–C3d packets, the half-space
inequality, the OS reconstruction theorem and any field law are untouched.


**Landed 2026-11-16, eleventh slice: the whole affine family, uniformly (C3e, second packet).**
Tightness for one scalar sequence is weaker than it looks: the observable a multiscale argument
actually thresholds is rarely the field itself but a *centred* version of it, or a difference of
two observables, and both are affine images. Seventeen declarations were added to the audit, all on
standard axioms, generalising the tenth slice from the single observable `renormField` to every
affine image of it.

* **The affine large set and its tail.** `shellAffineLargeSet c d n M a b = {p | M ≤ |a·renormField
  p + b|}` with `shellAffineTailLaw` its `shellLaw (n+1)`-measure. The tower applies verbatim —
  the indicator is bounded — giving `integral_shellAffineTail_eq` and
  `shellAffineTailLaw_eq_integral`.
* **The density input is already there.** `shellAffineTail_eq` says the iterated tail of an affine
  image *is* the density that `shellDensity_affine_field_le` (proved in the tail slice, for
  arbitrary `a`, `b`) bounds, so `shellAffineTail_le` costs nothing new. This is the payoff of
  having proved Chebyshev for affine thresholds rather than only for the shifted one.
* **The estimate, uniformly in the scale count.** `shellAffineTailLaw_le`: `≤ (a²K_n + b²)/M²`;
  `shellAffineTailLaw_le_inv`: for `c² < 1`, `≤ (a²/(1 − c²) + b²)/M²` *uniformly in `n`*;
  `exists_shellAffineTailLaw_le`: for every `ε > 0` one threshold `M = 2/ε + a²/(1−c²) + b² + 1`
  works at every scale. `shellAffineTailLaw_one_zero` records that the scalar packet is `a = 1`,
  `b = 0`, so this is a strict generalisation.

Boundary of this eleventh slice: **the same ceiling as the tenth, at higher generality.** The
estimate is a probability statement about an indicator of a bounded function; no expectation,
variance, covariance or correlation of an affine image is computed, because each of those needs the
`L¹` extension of the tower (section-integrability hypotheses in place of the uniform bound), which
is still the open step. In particular the `b²` in the numerator is *not* a variance: it is the
Chebyshev cost of the shift, and no statement is made that the laws of the affine images converge,
that their means converge, or that any limiting covariance exists. The interacting C3a–C3d packets,
the half-space inequality, the OS reconstruction theorem and any field law are untouched.

**Landed 2026-11-16, twelfth slice: the `L¹` moment identity (C3e, third packet).** The
boundedness hypothesis of the tower was never about the field: it was there because the
per-`y` identity could only be built from integrability of sections. At the level of *totals* the
obstruction disappears, and with it the gap that kept every expectation out of reach. Sixteen
declarations were added to the audit, all on standard axioms.

* **The truncation is dominated by the exact value.** `shellDensity_sq_min_le`: the density of the
  truncation `min (a·S + b)² N` is at most `a²K_n + (a·c^n·d·y + b)²` at *every* scale. The
  induction needs no monotonicity lemma and no section integrability — the majorant is explicit.
* **The truncation rises to it.** `tendsto_shellDensity_sq_min`: dominated convergence through the
  recursion, with that same quadratic as majorant, using the new parameter-measurability lemma
  `measurable_shellDensity_param` (a jointly measurable family has a density measurable in the
  parameter) and `measurable_shellDensity` (a bounded observable's density is measurable in `y`,
  via the tower itself).
* **The monotone limit.** `truncated_moment_eq` (bounded tower at the truncation),
  `lintegral_shellLaw_sq` (`∫⁻` equality after `lintegral_iSup`, `iSup_ofReal_min`,
  `ofReal_iSup_of_tendsto`), hence `integrable_sq_affine` — the square is integrable — and the
  moment identity `integral_shellLaw_sq`:
  `∫ (a·S_n + b)² ∂shellLaw(n+1) = a²K_n + (a·c^n·d)² + b²`.
* **Expectation and variance.** `integral_shellLaw_streamField`: the mean is **zero** (the drift
  multiplies the exterior coordinate, whose average vanishes; the moment formula at `b = t` and at
  `b = 0` then forces the cross term to vanish). `integral_shellLaw_centered_sq`: the variance is
  `K_n + (c^n·d)²`. `variance_shellLaw_le`: for `c² < 1` it is at most `1/(1 − c²) + d²`,
  *uniformly in `n`*.

Boundary of this twelfth slice: **the totals, not the sections.** What is proved is that the
law-level integral of a quadratic of the field exists and equals the explicit number; the per-`y`
identity `shellDensity_eq_integral_snoc` remains a statement about bounded observables, so no
conditional expectation is constructed and no section-level statement is recovered. The variance is
that of `streamField`, *not* of the renormalised observable `renormField`: the latter would need the
cross moment `E[S · p_last]`, which is the first item of the two-point function and is not
computed. There is no Gaussianity statement (the second moment is not a distribution), no
correlation, no Prokhorov limit and no interacting observable; C3a–C3d, the half-space inequality,
the OS reconstruction theorem and any field law are untouched.

### C3 — use Bałaban's multiscale method for the physical uniform estimates

Bałaban's approach is a principal source of the analytic estimates, alongside reuse of the
already constructed archive witness. It must be applied to the **same family** in C0/C2.
If using Wilson-side estimates, first prove the action/law/observable comparison; a coordinate
change or a Fock representation alone does not identify the renormalization transformation.

Build scale-indexed gauge-covariant spatial/spacetime block maps, local gauge charts and
conditional fluctuation measures. Relate their Gaussian fluctuation coordinates to the
Mehler/Hermite representation. Represent the RG action as pushforward/integration of
measures or expectation functionals, with the effective action defined afterwards.
For a reference Gaussian `gamma` and coarse sigma-field `G`, the coarse density is
`E_gamma[|Psi|² | G]`, not `|E_gamma[Psi | G]|²`. Preserve conditional means and their
covariances when integrating over exterior fields; a chosen Hessian alone is not the
interacting covariance.

Split the difficult estimate into reviewable packets:

- **C3a — exact step and fluctuations.** Specify the gauge transports, constrained
  covariance, boundary conditions, Haar/coarea/Faddeev–Popov factors, domains and the
  conditional Gaussian comparison. Prove identities before estimates; no gauge determinant
  or normalization factor is absorbed into an unspecified constant.
- **C3b — small fields.** Prove scale-uniform local elliptic/covariance/derivative bounds,
  stability of the chosen background and a polymer-activity estimate in an explicitly
  defined norm. Keep relevant/marginal couplings, observable renormalization and field
  redefinitions in the induction; do not assume a global strictly convex magnetic potential.
- **C3c — large fields.** Control the complement, its gauge charts and bad-block entropy
  with a summable tail after normalization and observable insertions. Small-field control
  alone is not a theorem about the full interacting expectation.
- **C3d — running parameters and induction.** Prove the chosen coupling/counterterm
  trajectory stays in the induction domain through arbitrarily many UV scales. Track
  dependence on insertion number, physical separation, volume and phase. In four dimensions
  marginal running can be logarithmic; do not impose a geometric error `r^k` unless proved.
- **C3e — observable limit estimate.** Derive the moment/tightness bounds of C4 and either
  compactness or an actual summable Cauchy estimate for renormalized observables. A stable
  partition function by itself does not establish these correlation limits.

An exact coarse map preserves RP when its pullback preserves the positive-time algebra,
products, conjugation and reflection and the coarse state is its pushforward. Reflection
commutation of a vector contraction alone is insufficient. If an intermediate RG action
or approximate solver does not preserve RP, carry exact regulator RP to the final limit
through convergent reflected moments instead.

Use [Bałaban's large-field step](https://doi.org/10.1007/BF01257412) as a source to inspect
for the gauge construction. Dimock's exposition
[small fields](https://arxiv.org/abs/1108.1335),
[large fields](https://arxiv.org/abs/1212.5562) and
[convergence](https://arxiv.org/abs/1304.0705) is a useful staged proof model, explicitly
for scalar `phi^4` in **three** dimensions. Its conclusions are not a 4D gauge theorem.
The local [YM4 working manuscripts](../Yang--Mills-LLM-experiment/README.md) offer further
analytic candidates; their own unclosed NB/RS/LF/RC/B/CP interfaces and tentative status
must remain visible. Reuse the October archive's completed source lemmas wherever their
hypotheses actually match, rather than reopening its entire construction.

**Acceptance:** a named estimate for each packet with quantifiers and constants adequate
for C4/C5, or a precise conditional result identifying what remains. `balaban_rg_convergence`
may assemble a proved bound; assuming its bound is not completion of C3.

### C4 — prove uniform moments, continuity and the renormalization conditions

Choose one common space of renormalized smeared physical observables. For a classical
field-law route, aim first for a uniform second-moment seminorm bound
`E_sigma |Phi_sigma(f)|² <= C p(f)²`, and weighted distribution-space norm bounds with
compact embeddings for tightness. Control every field/component being claimed. Add higher
moment/uniform-integrability bounds for the polynomial words to be passed to the limit.
The constants must be uniform in the cutoff being removed, with explicit volume scope.

For the all-field reconstruction route, state an arity-dependent growth envelope and test
seminorm orders meeting the **precise corrected OS reconstruction theorem** being used;
existence of each isolated moment is weaker. Keep separated tests, product tests and tests
meeting collision diagonals distinct. Use the existing contact theorem for a selected
archive witness; constructing the same contact prescription for nested observables still
requires its identification and the required positivity/regularity checks.

Fix physical renormalization conditions so rescaling fields to zero cannot manufacture a
limit: exhibit a prescribed nonzero centered two-point pairing at separated physical supports,
or another genuinely nonconstant surviving observable.
Normalized information indicators also need care when their informing masses shrink with
cell volume: keep fixed resolved supports of positive mass or prove the smeared/renormalized
limit, rather than taking unsmeared density ratios at a point.

**Acceptance:** a uniform bound ledger indexed by cutoff, volume, arity, test seminorm and
observable identity, plus nonvanishing physical normalization. No finite-coordinate degree
bound or low matrix residual replaces these estimates.

### C5 — extract a continuum hierarchy, then a law where the positivity permits it

For the nested Hamiltonian path, use spatial boxes with continuous Euclidean time and take
`a -> 0` at fixed physical box, then a volume subsequence `L -> infinity`. A discrete time
step, if introduced, is an additional regulator with its own transfer-kernel consistency.
The archive's Wilson path instead has its stated four-dimensional finite-volume mesh limit
and subsequent volume refinement. Match the paths by a theorem, not by silently exchanging
their limit order. An infinite-volume-first Bałaban variant requires its own uniformity.

First extract on a countable dense set of smearings/words; C4's continuity estimates extend
it to the claimed test topology. Preserve normalization, ordinary positivity and OS RP by
limits of the **same** finite Gram forms. Uniform integrability, not weak convergence alone,
passes unbounded moments. If compactness yields only a subsequence, report subsequential
existence. A proved summable increment estimate can upgrade the chosen trajectory to a
full limit; it does not establish regulator or phase universality.

For commuting real fields, construct the limiting positive-definite characteristic
functional, prove continuity at zero in the nuclear test topology, and apply a proved
Minlos/coordinate-extension theorem to obtain a law on distributions. Alternatively
prove tightness and weak convergence there directly. OS positivity is distinct from the
ordinary positivity needed for that probability law. An abstract noncommutative or graded
hierarchy must retain its own construction; it cannot simply be declared a scalar measure.

**Acceptance:** one actual normalized continuum hierarchy with its field/state identities,
RP, test continuity and nonzero normalization, and a distribution-valued probability law
when claimed. Existence does not wait for uniqueness, a positive mass gap, or an exclusion
of every possible nonstandard model. Those are later, precisely stated properties.

### C6 — make SIRK a certified part of the convergence argument

Use SIRK for `R_sigma=(K_sigma+zeta)^(-1)`, `zeta>0`, or the corresponding bounded
heat-function calculus, after C2 fixes the operator. Separate physical cutoff error,
Hermite/occupation tails, Krylov/rational/leakage error and arithmetic error. A bound
uniform in Krylov rank alone is not uniform in spacing or volume.

For bounded insertions with norms `M_i`, telescoping an ordered correlation product gives
bounds of the form `product_i M_i * sum_j epsilon_j` for the propagator errors, together
with the separately bounded state and insertion errors. For unbounded fields first prove
energy-weighted insertion bounds and heat smoothing for separated times; control the
short-time/contact limit in C4. A seed-only propagation estimate does not control all
vectors created by successive insertions. Use a growing certified word family or a
proved energy-window/tail estimate rather than an unjustified supremum over the whole space.

A useful Cauchy certificate on a declared test/word norm is

```text
|S_(n+1)(F) - S_n(F)|
  <= |S_hat_(n+1)(F) - S_hat_n(F)| + eps_(n+1)(F) + eps_n(F).
```

To infer existence from this route, prove the right-hand bound is summable for **all**
scales with uniform test seminorm control. Finitely many good numerical comparisons are
not that theorem. The Bałaban estimates can control unresolved scales; SIRK can certify
finite heads and provide rigorously enclosed insertion/resolvent comparisons.

Do not demand finite-rank convergence in full operator norm to a unitary on an infinite
space. Norm convergence of finite-rank resolvents also requires compactness that cannot
be presumed in infinite volume. Strong or observable/energy-local convergence is the
appropriate general goal. Positive-time heat convergence is not obtained by substituting
imaginary time into a theorem about real-time strong convergence.

**Acceptance:** a solver-to-observable estimate with leakage and tails instantiated and
its constants uniform in exactly the limits used. SIRK supplies quantitative control; the
multiscale/tightness/state compatibility estimates carry the continuum existence claim.

### C7 — construct and identify the limiting generator

Where representations differ, compare them through the common observable algebra and its
GNS spaces, or explicit identification maps with proven norm/inner-product consistency.
A single global `L²(gamma)` amplitude limit is optional: interacting/infinite-volume laws
may be singular relative to a chosen Gaussian reference and admit inequivalent cyclic
representations. Do not assume a unitary identification between regulators to prove one.

Two viable analytic routes are a densely defined closable limiting energy form with both
Mosco inequalities (liminf and recovery sequence), or compatible resolvents with a proved
resolvent identity, injectivity and dense range. The latter conditions prevent the
spurious limit `R_sigma -> 0` from being called a densely defined Hamiltonian. Use a common
lower bound for the relative generators. If a form-domain core is used, prove it is a
core for the interacting form, not merely dense in the free Hilbert norm.

The varying-Hilbert-space framework in
[Kuwae–Shioya](https://archive.intlpress.com/site/pub/files/_fulltext/journals/cag/2003/0011/0004/CAG-2003-0011-0004-a001.pdf),
§2, supplies a reference for form/resolvent/semigroup compatibility. It is a theorem to
port and instantiate, not an assumed local API. On a common Hilbert space, use the
existing `StrongResolventConvergence`/Trotter–Kato results for their actual real-time
conclusion, and prove the nonnegative heat-semigroup version needed here. Strong
resolvent convergence by itself does not control unbounded fields or reference states;
C4 and the word-domain estimates remain necessary.

**Acceptance:** a constructed positive self-adjoint relative generator and convergence
of the actual positive-time correlation words, or a precise missing form/representation
estimate. Renormalization shifts must still respect `h+cI -> H+c N_out` before taking
sector-relative or GNS dynamics.

### C8 — reconstruct and bridge one selected hierarchy

Use the positive-time algebra, quotient by its OS null **subspace**, and complete. Reuse
`HalfSpaceState`, `HalfSpaceHilbert` and `HalfSpaceComplex`; prove the concrete state's
translation, reflection, continuity and null-space hypotheses. Euclidean evolution is a
symmetric contraction **semigroup for t>=0**, not a two-sided contractive self-adjoint group.

For the selected archive hierarchy, reuse its reconstruction and analytic-continuation
results through the audited adapter rather than reproving them without need. For the
nested path, establish the corrected OS regularity, Euclidean covariance, permutation
and locality/continuation requirements. A scalar subsector does not certify all gauge
fields; finite Mehler-coordinate rotations do not supply spacetime rotations or boosts.
The [corrected OS reconstruction paper](https://doi.org/10.1007/BF01608978) is the reference
for the exact reconstruction contract, beyond an informal list of axioms.

Prove clustering/ergodicity of the selected phase if the reconstruction target requires
one invariant vacuum; a mixture can remain a valid continuum hierarchy without that
property. A symmetry-compatible phase selection is an additional task, not a consequence
of tightness alone. Exponential clustering or a positive mass gap is stronger than the
asymptotic clustering used for vacuum uniqueness.

Construct the map from a positive-time observable word class to that word on the chosen
reference state. Prove equality of inner products/null spaces and dense cyclic range,
then complex-linearity, field intertwinement and semigroup identity. For a mixed reference
use its GNS cyclic vector. The target is the **physical cyclic space**, not automatically
all outer Fock sectors. `OsFockBridge` packages consequences of this map; it does not
construct it. Generator equality follows only with the relevant closed/domain identification.

**Acceptance:** one diagram ties the retained archive/nested witness, physical observable
algebra, state, fields, forward flow and relative generator together. This identifies a
realization; it leaves open whether other regulator families or phases give equivalent ones.

### C9 — separate nontriviality, uniqueness and mass gap from existence

Pass the fixed nonzero normalization from C4 first. For the stronger physical comparison,
identify the centered stress-trace observable and test its short-distance law and stated
finite-Wick exclusions against the selected archive witness. A nonzero connected fourth
cumulant excludes a Gaussian law for that field; it does not exclude a composite observable
of an underlying free field. A positive Hamiltonian or nonlinear coordinate expression
also does not establish interacting continuum physics.

Keep uniqueness questions separate: limit along the selected trajectory, independence
of subsequence, regulator/counterterm universality, phase uniqueness and contact-prescription
uniqueness. Equality of a complete Schwinger hierarchy can give cyclic reconstruction
uniqueness while these broader questions remain open. Specify the extra properties needed
to distinguish a proposed nonstandard realization instead of assuming they are excluded.

A mass gap requires the full ground projection and cutoff-uniform spectral/decay estimates
for the chosen generator. The archive's positive-energy theorem is not that gap. Use
softmodes U0–U6 for a strong-coupling witness and spectral coverage. For an asymptotically
free UV trajectory, a fixed strong **bare** lattice coupling need not approach the required
continuum regime: identify a physical/coarse scale and prove transport of the claimed
bound under the renormalization flow. Do not interchange infrared gap and ultraviolet
stability, or an inner excitation spacing and the absolute outer-vacuum gap.

### C10 — sector scope, specialist execution and negative controls

QYM is the first interacting target. QED needs its own charge/gauge and infrared contracts;
no positive photon gap is assumed. An extension to QG retains the **vielbein R²** record,
the full potential `M^4/(16 alpha) (1-exp(-sqrt(2/3) phi/M))²` and every interaction.
A Taylor polynomial, densitized comparison or scalaron-only model is not that record.
QG also needs its own physical positivity and covariance analysis. For QG and NS,
coordinate-space products involving spatial derivatives are represented by the specified
momentum convolutions, with cross-mode terms retained. A diagonal parcel approximation
cannot establish the full operator bridge. NS's positive eliminated Hamiltonian and signed
Koopman generator are distinct; NS does not acquire relativistic OS axioms by analogy.

Across sectors keep `dGamma(B²)` separate from `dGamma(B)²`. Full interacting inner
Hamiltonians can have outer-quadratic enclosures without giving Gaussian field laws.

Execution order: **C0 and the archive adapter inventory first; C1/C2 as concrete controls;
C3a–e and C4 for the new family's analytic estimates; C5/C6 and C7; then C8**. The
already-proved external existence/reconstruction path can proceed to identification while
new nested-family estimates are developed. Do not make a mass gap or global uniqueness
a prerequisite for the first existence/bridge deliverable. C9 records additional claims.

Proposed Lean modules/identifiers are implementation tasks, not declarations claimed to
exist. Each specialist packet records the exact theorem type and physical definitions,
remaining assumptions, source/dependency hashes and which limit constants are uniform.
The specialist later runs targeted elaboration, the axiom audit and relevant bridge checks;
this documentation task runs none of those compilation commands.

Negative controls must reject: a measure merely supplied to `ContPrior`; a fixed-dimensional
Gaussian called a 4D field; an unrelated archive witness; mismatched OPE/contact bases;
vanishing or ultralocal-only correlations; a changed inner constant or discarded interaction;
a signed density called a probability; covariance positivity substituted for RP; a
summability hypothesis reported as an instantiated Bałaban estimate; a zero limit
resolvent; and a seed/rank residual presented as a spacetime cutoff bound. Preserve valid
conditional theorems with their missing inputs named rather than marking the whole
continuum problem complete.

## Source audit and bridge work order (2026-11-11)

This revision replaces the earlier external-source commentary as the reading guide for that
commentary. The E0–E5 construction and dated implementation record below remain useful.
The two formalisms have separate endpoints: the nested-Fock/Mehler Hamiltonian is the object
of [softmodes.md](softmodes.md) and [the SM plan](SM_ESA_COMPLETION_PLAN.md); Euclidean
correlations and Wightman reconstruction are an additional route studied **in this file**.
Neither endpoint is a definition of the other. Combining them is a proposed theorem programme.
The priority decision in [CURRENT_WORK_ORDER.md](CURRENT_WORK_ORDER.md) remains in force.

### Physical prior and spatial outer occupation (clarified 2026-11-11)

The empty outer vacuum represents mathematical emptiness. Physical predictions use the
specified non-outer-vacuum prior: one outer particle at each informed point of 3D space.
Information about fields at several points can therefore require several outer particles;
there is no global `N_out = 1` restriction. Outer-free evolution retains the interactions
inside each particle's inner state. An outer particle here is not an elementary SM particle.

Reference: [book.tex](book.tex), “Free field parametrization in Statistical Field Theory”,
especially the recursive second-quantization paragraph and the proposition at distinct
points `x₁,…,xₙ`, expressed as a product of number densities. The text explicitly requires
normalization of these densities into propositions and describes local tensor factors
with at most one point. “Gauge-variant gaussian measure and the phase diagram” separately
uses the cyclic **initial state** to define gauge-invariant expectation functionals.

B0 must specify spatial localization, the local prior factors and their joint state,
including correlations; local occupation does not imply a product prior. Start with
finitely many resolved, distinct spatial supports and give their embedding into the
existing space containing spatial, field, derivative and graded coordinates. Refinement
must implement the manuscript's conditional-probability meaning of spatial points, rather
than assuming point-evaluation vectors in `L²`. Keep the continuous/infinite-information
representation and its consistency estimates as explicit further deliverables.

Write the physical state as `ω_info(A)`, represented when applicable by a normalized
vector `Ψ_info` or density operator `ρ_info`. Correlations are `ω_info(A₁⋯Aₙ)` on their
stated domains. Number-preserving observables can have nonzero correlations in this state.
Their vanishing on the empty `Ω_out` does not obstruct this physical construction and
does not require adding outer-number-changing observables.

### Sources, versions and what was actually inspected

The following are local source readings, not new builds or independent verification runs.
The revisions identify the inspected snapshots; external logs retain their original dates.

* [October submission](../OpenAI-YM-20261028/README.md), revision
  `3456e5e75cf8d4cd558955a5c7638fba2d68f464`: `PublicTheory.lean`,
  `PublicWilson.lean`, `ChallengeSpec.lean`, and the verification usage audit.
* [Results and review](../YM/README.md), revision
  `55ba9fc36293b3f4d52c6b1f813169a0be76ee98`: the 10 November assessment
  (`docs/assessment-1.pdf`), plus the October package's `docs/checks.md`,
  `checks/AcceptanceSpec.lean`, `checks/OPESpec.lean` and dated `evidence/`.
* [Balaban manuscripts](../Yang--Mills-LLM-experiment/README.md), revision
  `c7fef8b21b5846e1b5806a7d4f915737b9130c27`: the YM4 assembly overview PDF,
  YM4 source outlines and RP1's Theorem A. The README explicitly treats mathematical
  claims as tentative and not satisfactorily vetted; QED3/YM3 are manuscript claims too.

The October package uses Lean 4.32.0; this repository pins 4.28.0. Reuse of an external
proof would require an explicit port, dependency/license review and local proof checks.
No external theorem has been imported or made an extra axiom by this planning revision.

### Correct scope of the reusable examples

**One witness for many claims.** `JointExistence` chooses one Wilson family before the
volume order, then a subsequence and hierarchy. The review's `CombinedAcceptance` similarly
binds one table and `Spec.Final` witness for its lattice, phase, Ward, operator-content and
trace clauses. This prevents independent existential claims from silently choosing different
theories. Adopt that dependency structure for the bridge below.

**Two limit orders, two projects.** In the October source, `WilsonFamily.Converges` asserts
full mesh convergence at each suitable fixed physical volume, then convergence along a
volume subsequence. The Balaban YM4 overview instead chooses an infinite-volume Gibbs state
at each fixed spacing, then a subsequential continuum limit. Its target is a scalar SU(2)
action-density theory at small reference coupling. These orders cannot be interchanged
without a new uniformity theorem. Record one route in E2; any agreement is a separate result.

**Reconstruction is a reference target, not an imported local construction.** The review's
independent `PhaseAndOS` bridge concerns the selected centered stress-trace scalar family
on zero-diagonal Schwartz tests, including arity-linear growth and actual integral pairings.
The source has broader reconstruction conclusions, attached as `SourceConclusions`; this
is distinct from an independent all-field OS check. E3 must state its own test domain,
regularity, covariance and positivity hypotheses. Contact extensions do not automatically
supply unrestricted-test RP or raw lattice convergence on collision diagonals.

**Vacua and spectra.** W0 includes positive energy and a unique invariant vacuum in each
selected reconstructed theory. The unselected limit is a phase average; neither global
phase uniqueness nor a unique thermodynamic limit follows. Positive energy is
`energyMomentum.projection forwardConeᶜ = 0`; the nonzero vacuum still sits at momentum
zero. An energy gap means `E_H((0,m)) = 0`, or the E5 decay estimate off the full ground
projection. It does not mean that a ball containing the vacuum has zero projection.

**Grading and non-freeness.** External field grades form a filtration, not a proof of exact
scaling dimensions or conformal invariance (`OPESpec.lean` says so explicitly). Our
`totalDegree_magWeight_le` bounds ordinary polynomial degree in independent coordinates;
it does not identify a gauge-invariant local label. A proposed dictionary must distinguish
coordinate degree, engineering weight and quotient relations. The trace law
`r⁸ log²(1/r) C(r) → 3 dim(g)/π⁴` excludes specified finite Wick profiles; it supplies no
infrared gap. If a nested model is to represent that particular theory, its selected
observable must pass the same test. An abstract Hilbert-space isomorphism is insufficient.

**Landed 2026-11-11, in exactly that finite form.**
`BookProof/Sm/ChapterSmFreeModeExclusion.lean` states it as code rather than as prose:
`shortNorm r = r⁸ log²(1/r)` (the exponent is the weight of two grade-4 insertions,
`weight = 4 + 4`), `modeKernel E t c r = c · E^t · exp(−rE)` for the external
`(1/2E) E^timeOrder num(p) exp(−rE)` at fixed momentum, `wickSum` for the finite `List`, and
`not_eventuallyEq_wickSum` for the exclusion itself. The analytic half is proved
(`tendsto_shortNorm_modeKernel`: the normalisation kills one mode, hence
`tendsto_shortNorm_wickSum` kills a finite sum). The trace coefficient enters as a
**hypothesis** on `F`, so the module assumes nothing about any nested model's observable, and it is
finite-list only — `not_eventuallyEq_modeKernels` is the form an S3 candidate must fail.

### Two routes and the proposed common acceptance object

Keep E0–E3 as the Euclidean construction route. Keep S0–S4 of `softmodes.md` and P0–P8
of the SM plan as Hamiltonian routes with their own success criteria. The following bridge
packets refine E4; their names describe **proposed deliverables**, not existing declarations.

1. **B0 — observable and prior dictionary.** Fix a single nested Hamiltonian, statistics,
   spatial occupation/prior, physical sector, closure and common invariant domain. Select
   normalized propositions and smeared physical
   observables on it. Give their adjoints, reflection/time convention and gauge relations.
   Construct a candidate Euclidean hierarchy from these data, with domains/integrability
   for each product. A bare magnetic component is not automatically an invariant label;
   a magnetic energy alone is not the full covariant stress trace.
2. **B1 — state and time agreement.** For a chosen Euclidean limit/phase, prove equality
   of its separated smeared moments with the chosen nested reference-state moments at ordered
   imaginary times. Specify an extension to coincidence diagonals only if proved. Prove
   positivity, time translation and the null-space identities needed on the common algebra.
   Either construct the Euclidean state from the Hamiltonian or compare with an external
   construction; E0's Wilson benchmark alone does not identify the manuscript model.
   An arbitrary information prior need not be stationary, a ground state or invariant
   under spacetime symmetries. Verify the particular state hypotheses required for the
   selected Euclidean/OS theorem; retain general prior-dependent predictions separately.
3. **B2 — construct the unitary.** Send an OS word class to the corresponding nested
   observable word applied to the selected reference vector `Ψ_ref`, not the empty
   `Ω_out`. B1 must identify inner products and null vectors. For a mixed reference state
   use its GNS representation and cyclic vector; do not assume it is a vector in the
   original outer space. Complete onto that **physical cyclic space**. A number-preserving
   algebra acting on a fixed-number prior remains in that sector; full-Fock surjectivity
   is not required. Intertwine fields, reference states and forward semigroups on their
   specified domains. Generator equality follows from
   the semigroup identity; a formal core equality needs closure/core arguments instead.
4. **B3 — covariant completion and spectral transfer.** Construct spatial translations
   and covariance/locality for the represented observables, or explicitly retain these
   as open hypotheses. Transport the full ground projection through B2 before a gap or
   clustering assertion. Wightman claims require the entire reconstruction contract;
   ESA and a Hamiltonian gap alone do not provide boosts, locality or a momentum spectrum.

The common acceptance object must bind the spatial prior/reference state, phase,
observable dictionary, core,
unitary, semigroup and ground projection once. An OPE result obtained from a separate
existential witness needs an explicit identification: the review's separate OPE endpoint
is itself documented as not automatically sharing the combined endpoint's chosen witness.
A successful bridge relates the two formalisms; failure to construct it leaves valid
Hamiltonian and Euclidean results separately labeled.

**First B0 acceptance test:** calculate a normalized proposition and a nontrivial
correlation in the stated spatial prior, retaining joint information at different
points. On the outer one-particle sector, `dΓ(O)` acts as the inner `O`, so products
recover inner operator products on their common domain. On many-particle states retain
the cross-particle terms; use the book's normalization of number-density propositions.
Testing only `Ω_out` tests emptiness and cannot validate or invalidate these predictions.

### Analytic ideas to adapt with their hypotheses

The Balaban overview labels NB, RS, LF, RC, B and CP not closed. Its other boxes are
conditional on their inputs, not stand-alone construction theorems. CP is useful as a
checklist for a **proposed** conditional Gaussian comparison: identify the exterior
sigma-field, charts, full interacting density, coarea/Haar and gauge factors, constrained
Hessian, boundary terms, retained activities and exterior force before comparing covariance.
Its requirement to average histories before normalization and retain covariances of
conditional means prevents replacing the interacting law by a chosen Gaussian Hessian.

RP1's Theorem A assumes an actual random-distribution probability measure, exponential
moment control, translation invariance and RP for coordinate **and diagonal** mirrors,
with a restricted tensor representation (planar weights in `{-2,-1,0,1,2}`). Its conclusion
concerns rotation covariance of moments on disjoint-support tuples. The YM4 overview also
lists angular/plate and flat-test extension inputs. E2 must choose and verify the applicable
criterion, including its domain; one reflection plane or finite Mehler-coordinate rotations
cannot replace it. The absence of a continuum measure in the October endpoint blocks
a direct application of the random-distribution version until that measure is constructed.

### Verification packets and stopping rules

Reuse `scripts/axiom-audit`; supplement future bridge work with a manifest of endpoint
**types and reachable definitions**, source/dependency hashes, complete commands and dated
logs. What that script already enforces (landed 2026-11-11): `axiom_ledger.lean` writes one row
per theorem — `name` and its transitive axiom closure — to `evidence/axiom-ledger.tsv`, and the
gate fails on anything outside `{propext, Classical.choice, Quot.sound}`, on a ledger shorter than
its coverage baseline, and on an axiom **added** to a named declaration against the committed
baseline. It is wired into `axiom-gate.yml`. What it cannot do is the second half of the sentence
above: it checks axiom footprints, not that the endpoint type is the intended one, which is why the
negative controls must reject a changed proposition and a changed physical operator definition as
well as an added axiom. The October usage audit distinguishes endpoint-reachable declarations from
unrelated compiled modules. Axiom cleanliness alone does not detect a wrong target.
The review records separate combined/OPE Comparator runs, cache reuse and macOS development
mode without an external kernel; do not describe those records as a fresh local replay.

Next local deliverable: B0 for one concrete observable and B1 at a finite regulator, with
an explicit unproved continuum estimate. Keep the full E2 limit and B2 unitary conditional
until their inputs exist. Hashimoto/SIRK applies after the self-adjoint operator is fixed;
its approximation error neither constructs a Euclidean law nor proves any bridge packet.

**Landed 2026-11-12, in exactly that finite form.** `BookProof/OSReconstruction/ObservablePrior.lean`
states the two packets as code, `sorry`-free and with axiom footprint
`{propext, Classical.choice, Quot.sound}` only.

* **B0.** `SpatialPrior n Ω` is the stated prior: a probability law `μ` on a finite information
  space together with `n` resolved, distinct supports `inf : Fin n → Ω → Bool`. The law is an
  arbitrary *joint* law, so local occupation does not imply a product prior. `SpatialPrior.prop`
  is the **normalized number-density proposition** at a support, and `SpatialPrior.expect_prop`
  proves `ω (prop i) = 1` for every prior with positive mass there — the one-point functions
  therefore carry no prior information at all. `SpatialPrior.corr_eq` identifies the two-point
  function as `joint i j / (mass i · mass j)`, and `SpatialPrior.corr_eq_one_iff` turns that into
  the dictionary statement **correlation `1` ⇔ joint information factorizes**. The first
  acceptance test is `correlatedInformation`: two distinct supports whose informed sets coincide,
  where `correlatedInformation_corr` is `2` and `correlatedInformation_corr_ne_one` says it is
  not the uncorrelated value. The empty outer vacuum is `emptyVacuum`, and
  `emptyVacuum_cannot_distinguish` is the plan's remark made precise — its values vanish for
  every prior, so it validates nothing.
* **The one-particle sector.** `dGamma_diag_one_particle` is
  `dGamma_one_particle` specialized to a diagonal column, and `dGamma_diag_mul_one_particle` is
  the product statement B0 asks for: `dΓ(f) (dΓ(g) e_k) = dΓ(f · g) e_k`, so products recover
  inner operator products on their common domain.
* **B1 at the finite regulator**, on `gibbsHalfSpaceState` of `HalfSpaceFreeState`.
  `gibbsFun_posTime_eq` gives the one-point function as the boundary average,
  **`gibbs_separated_moment_factorises`** gives
  `⟨F, G⟩_OS = ω F · ω G`, and `gibbs_connected_corr_zero` concludes that the connected
  two-point function vanishes identically. The equality B1 asks for therefore holds at the
  regulator, but only because both sides are the empty correlation: the regulator's two halves
  are independent draws, and its time translation (`regulatorTimeTranslation`) is trivial.
* **The unproved continuum estimate** is `B1ContinuumEstimate ω T F m C` — a `def … : Prop`, not
  an axiom: after the continuum limit the connected two-point function of the chosen observable
  decays at rate `m > 0`. `b1ContinuumEstimate_of_clustering` shows it is exactly the
  specialization of the corpus's `SchwingerClustering` to one observable, i.e. the shape
  `osNorm_evol_le_of_clustering` and `genForm_gap_of_clustering` consume. The decay itself is
  **not** proved here; it is Bałaban's infrared input.

Boundary of the module, recorded there as well: finitely many resolved supports and a finite
information space (the continuous/infinite-information representation and its consistency
estimates are not built and no point-evaluation vectors in `L²` are assumed); the propositions are
normalized indicators rather than products of independent number densities; and B2/B3 are
untouched — no unitary `U : ℋ_OS → ℱ` is built (the corpus's `OsFockBridge` still states the
conditions and proves only their consequences).

**Landed 2026-11-12, the rest of B0's clause.** `BookProof/OSReconstruction/PriorRefinement.lean`
takes the three remaining items the paragraph above names — the conditional reading of a spatial
point, refinement, and the infinite-information representation with its consistency estimate — and
states them as code, `sorry`-free, axiom footprint `{propext, Classical.choice, Quot.sound}` only.

* **Conditional probability at a spatial point.** `SpatialPrior.massOn` / `jointOn` are the prior
  masses of an arbitrary event and of a conjunction; `massOn_inf` and `jointOn_inf` show the B0
  quantities are the case `A = inf i`, so no new notion is introduced. `SpatialPrior.cond` is the
  conditioned law (`cond_sum_one`: it is again a probability law), `cond_mass` reads the conditional
  mass at a point as `jointOn A (inf i) / massOn A`, `cond_expect` is Bayes' rule, and
  `cond_massOn_self` says conditioning makes `A` certain. `cond_expect_prop` records that B0's
  normalization survives conditioning. This is the manuscript's conditional meaning of a spatial
  point, with no point-evaluation vector in `L²` anywhere.
* **Refinement consistency.** `PriorRefinement` splits the information space as `Ω × Γ` with an
  arbitrary *joint* law on the product (the "no product prior" requirement is kept) and reads the
  resolved supports off the coarse factor; `PriorRefinement.coarse` is its marginal. Then
  `mass_refined_eq_coarse`, `joint_refined_eq_coarse`, `corr_refined_eq_coarse` and
  `expect_refined_eq_coarse` prove that splitting the information space changes no B0 number —
  the finite consistency estimate.
* **Infinite information.** `InfSpatialPrior n Ω` drops `[Fintype Ω]`: `Ω` is arbitrary, the law is
  an `ℝ`-valued mass function, and the *resolved* information is an explicit finite support
  `s : Finset Ω` (states outside `s` are unresolved, not `L²` vectors). `expect_prop`, `corr_eq`
  and `corr_eq_one_iff` transfer the whole dictionary, `ofFinite_corr` shows the finite packet is
  the case `s = univ`, and `correlatedInformationNat` repeats the acceptance test on the infinite
  information space `ℕ`, with `corr = 2 ≠ 1`.

Boundary recorded there: the refinement is the product `Ω × Γ` (not a general coarsening map), and
`InfSpatialPrior` has a finite *resolved* support inside an infinite information space — the
continuous law with no atomic support is still not constructed and remains an input, as does the
continuum estimate `B1ContinuumEstimate`.

**Landed 2026-11-12, the continuum regularization.** `BookProof/OSReconstruction/ContinuumPrior.lean`
closes the "continuous law" half of that boundary: the information space now carries a genuine
probability **measure**, and the dictionary is stated with integrals instead of fiber sums. Axiom
footprint of every headline theorem: `{propext, Classical.choice, Quot.sound}`; no `sorry`.

* **The measure-theoretic prior.** `ContPrior n Ω` is `μ : Measure Ω` with `IsProbabilityMeasure μ`
  and `n` measurable resolved supports; `ContPrior.mass` / `.joint` are `μ.real` of the informing
  event and of the conjunction, `.prop` is the normalized indicator, `.expect` is the integral
  against `μ`. `ContPrior.expect_prop` proves `∫ prop i ∂μ = 1` for every prior of positive mass,
  and `ContPrior.corr_eq` / `corr_eq_one_iff` restate the B0 dictionary (`joint / (mass * mass)`,
  unit correlation iff the joint measure factorizes). Nothing here is a point-evaluation vector in
  `L²`.
* **Refinement invariance (pushforward).** `ContRefinement` refines `Ω` to `Ω × Γ` with an arbitrary
  probability measure on the product — the tag may stay correlated with the coarse information —
  pulls the supports back along `Prod.fst`, and takes `ContRefinement.coarse` to be the pushforward
  `Measure.map Prod.fst`. Then `mass_refined_eq_coarse`, `joint_refined_eq_coarse`,
  `corr_refined_eq_coarse` and `expect_refined_eq_coarse` say marginalization changes no B0 number;
  the proofs are `Measure.map_apply` / `integral_map`, the exact analogue of the finite fiber sums.
* **Exhaustion/truncation consistency.** For a monotone exhaustion `A k ↑ inf i`,
  `ContPrior.tendsto_mass_of_iUnion` gives `μ.real (A k) → μ.real (inf i)`, `tendsto_pair_of_iUnion`
  does the same with both supports exhausted at once, and the bundled
  `ContPrior.tendsto_dictionary_of_iUnion` states the whole dictionary in one `Tendsto`: the mass
  vector, the joint matrix and the correlation matrix of the truncations converge coordinatewise to
  the continuum values (the correlations under the hypothesis that the limiting masses are
  positive). So the finite regulator's numbers are limits of the continuum ones — the finite packet
  is a genuine regularization of this object.
* **Acceptance test on a continuum information space.** `unitIntervalLaw` (Lebesgue measure
  restricted to `[0,1]`, a genuine probability measure) with both supports `[0, 1/2]`:
  `correlatedInfoCont_corr : corr 0 1 = 2` and `correlatedInfoCont_corr_ne_one` reproduce the finite
  acceptance test with integrals rather than sums.

Boundary recorded there: the continuum *law* is still an input — `IsProbabilityMeasure` is assumed,
never derived, and no Euclidean measure is constructed; supports are measurable sets of positive
finite measure, and the propositions are normalized indicators (not products of independent number
densities). The bundled exhaustion statement converges the dictionary coordinatewise, not in a
single operator topology, and the correlation clause needs the limiting masses to be positive. No
spatial translation, no unitary `ℋ_OS → ℱ`; B2/B3 remain conditional, and `B1ContinuumEstimate` is
still an explicit input.

**Landed 2026-11-12, B2 on the one-particle sector.** `BookProof/OSReconstruction/OneParticleBridge.lean`
gives `OsFockBridge` an inhabitant **whose `U` is constructed rather than assumed**, which was the
one thing the bundle's two previous inhabitants (`OsFockBridge.id`, `osFockBridgeOfMulModel`) never
did. Axiom footprint `{propext, Classical.choice, Quot.sound}`; no `sorry`.

* **A concrete state.** `evalZeroState` is the point-evaluation functional `ω F = F 0` on the full
  observable algebra — additive and homogeneous for *every* observable, θ-invariant because
  `fieldReflection` fixes `0`, and reflection positive because its OS form factorizes:
  `evalZero_osBilin : ⟨F,G⟩ = F(0)·G(0)`, hence `⟨F,F⟩ = F(0)² ≥ 0`.
* **Its OS space is the one-particle line, and the isometry is built.** The radical is the kernel of
  evaluation at `0` (`evalZero_mem_radical_iff`); evaluation descends to the quotient as `evalQuot`,
  which is an isometry onto `ℝ` (`evalQuot_norm : ‖[F]‖ = |F(0)|`, `evalQuot_surjective`), so
  `𝔄/𝔑 ≃ₗᵢ ℝ`. `LinearMap.extendOfNorm` along the dense embedding gives
  `evalHphysU : ℋ →ₗᵢ[ℝ] ℝ` (`evalHphysMap_norm`), onto (`evalHphysU_denseRange`).
* **The bridge.** `oneParticleBridge P : OsFockBridge ℝ P (oneParticleFlow P)` for an arbitrary
  transfer semigroup `P`, with all three fields proved: `U` is the constructed isometry, its range
  is dense, and on a one-dimensional sector every vector is `x = U x • Ω`, so linearity gives
  `U (P τ x) = c τ · U x` with `c τ = U (P τ Ω)` (`oneParticleScalar`) — the Fock-side flow is the
  scalar flow `c τ • id` (`oneParticleFlow`). The two-point function becomes
  `⟪x, P τ x⟫ = c τ · ‖x‖²` (`oneParticleBridge_twoPoint`) and `‖P τ x‖ = |c τ| ‖x‖`
  (`oneParticleBridge_norm`); `oneParticleBridge_unitary` records that the identification is a
  unitary.

Boundary recorded there, and it is the honest reading: the instance is non-conditional in `U`, but
it is a **degenerate model**. The point-evaluation state is a character of the observable algebra,
which is *why* its form is rank one and its Hilbert space is a line — there is no multi-particle
content to identify. `F = ℝ` is the one-particle sector of the Fock space over a one-dimensional
one-particle space and `oneParticleFlow` is `dΓ` of `c τ • id` there; it is not the manuscript's
inner `h_F`, no complex structure, spatial translation or identification with `ℱ_out` is built, and
`P` stays an input as for every bridge. The interacting B2 — a unitary `ℋ_OS → ℋ_ref ⊆ ℱ_out`
intertwining the smeared fields and the actual heat semigroup — remains open; this module only
records that the bundle is satisfiable by a constructed map, so B2's difficulty is the model, not
the bundle.

**Landed 2026-11-13, a physical (non-character) instance.**
`BookProof/OSReconstruction/FiniteVolumeGibbsBridge.lean` (namespace `TwoStateGibbs`) gives the same
bundle an inhabitant whose state is a **finite-volume Gibbs state** — not a character — with a
**two-dimensional** OS Hilbert space and a constructed isometry onto `ℝ²`. Axiom footprint
`{propext, Classical.choice, Quot.sound}`; no `sorry`.

* **The state.** The ensemble is the two *constant* field configurations `φ_t = const a_t`,
  `a = (0, 1)`. A constant field is fixed by `fieldReflection` whatever the component encoding is
  (`fieldReflection_constConfig`), so `θ` acts trivially on the support and
  `gibbs_osBilin : ⟨F,G⟩ = Σ_t w_t · F(φ_t) · G(φ_t)` is reflection positive *termwise*
  (`gibbs_reflectionPositive`). Boltzmann weights `w_t = exp(−β a_t²)/Z` are positive
  (`gibbsWeight_pos`) and normalized (`gibbsWeight_sum`); `gibbsState β` is the resulting `OSState`.
* **Finite support is forced, not a convenience.** `LinearFunctional` asks for additivity on *all*
  observables `Config → ℝ`, and Lean's Bochner integral is not additive off the integrable
  functions, so a Gibbs measure with infinite support cannot be a `LinearFunctional`. A
  finite-support Boltzmann law can, and `Σ_t w_t δ_{φ_t}` is the Gibbs measure of that
  sub-ensemble.
* **Non-character.** The indicators of the two configurations have disjoint support, so
  `gibbs_not_multiplicative : ω(δ₀ δ₁) = 0 ≠ w₀ w₁ = ω δ₀ · ω δ₁` — exactly what the
  point-evaluation state cannot exhibit.
* **The space.** The radical is `{F | F(φ₀) = F(φ₁) = 0}` (`gibbs_mem_radical_iff`), so `𝔄/𝔑` is
  two-dimensional; `gibbsCoord F = (√w_t · F(φ_t))_t` annihilates it exactly
  (`gibbsCoord_eq_zero_iff`), descends to an isometry `gibbsQuot` (`gibbsQuot_norm`,
  `gibbsQuot_surjective`), and `LinearMap.extendOfNorm` extends it to
  `gibbsU β : ℋ →ₗᵢ[ℝ] ℝ²` (`gibbsHphysMap_norm`, `gibbsU_denseRange`).
* **The bridge.** `gibbsBridge β E : OsFockBridge ℝ² (gibbsTransfer β E) (gibbsFlow E)`, both
  flows scalar (the two configurations are degenerate in energy), with
  `⟪x, P τ x⟫ = exp(−τE) ‖x‖²` (`gibbsBridge_twoPoint`) and `‖P τ x‖ = |exp(−τE)| ‖x‖`
  (`gibbsBridge_norm`).

Boundary recorded there: the state is a **two-point** sub-ensemble of the lattice Gibbs measure, not
the full Gaussian Gibbs measure; the genuine lattice Gibbs state of E3 (`gibbsFun V`) is not a state
of this carrier at all — its full-algebra OS form `Σ_{x,y} w x w y F(y,x) G(x,y)` is indefinite
(take `F(1,2) = 1`, `F(2,1) = −1`), and reflection positivity there holds only on `𝔄₊`, where the
OS space is a line again. Both configurations carry the same energy, so the transfer semigroup is a
scalar and no nontrivial dynamics is exhibited; `P` remains an input, as for every occupant of the
bundle; no spatial translation, complex structure or identification with `ℱ_out` is built. B2 in
general remains open.

**Landed 2026-11-14, the `Config`-side reflection positivity of item 3.** `BookProof/ReflectionPositivity/HalfSpaceSplit.lean`
§8 carries out the one bookkeeping step `gffConfigMeasure` left open, and it does so in the form the
lattice theorem needs — the OS *integral* rather than the measure — so the step costs three short
lemmas rather than a `Measure.map`-through-`withDensity` fight. No `sorry`; axiom footprint of every
theorem below `{propext, Classical.choice, Quot.sound}` only (`Work/HalfSpaceSplitAudit.lean`).

* **`gffHalfDensity`** is `exp(−h)`, one half of `configGibbsDensity`, with `gffHalfDensity_pos`,
  `measurable_halfMassAction` and `measurable_gffHalfDensity` supplying what the density argument
  needs.
* **`integral_splitMap_gffConfigMeasure`** — for any `G`,
  `∫ G d(splitMap (gffConfigMeasure m)) = ∫ a y₋ · a y₊ · G dLeb` on `(Y × Y)` with `a = gffHalfDensity m`.
  The proof is `integral_withDensity_eq_integral_toReal_smul`, which is unconditional in the
  integrand, plus `ENNReal.toReal_ofReal` — no integrability hypothesis on `G`.
* **`gffConfigMeasure_osForm_nonneg`** — hence `0 ≤ ∫ fkOSForm f ((), ·) d(splitMap ω)` for **every**
  future-half observable `f`, with no hypothesis on the state and none on `f`. This is §6's `hsplit`
  consumed at the one place `fkKernel_reflectionPositive` uses it: `fkKernel_inner` evaluated at the
  single boundary point `()`, where the product `ν ⊗ ν` *is* the Feynman–Kac square.
* **`gffConfigMeasure_isReflectionPositive`** — therefore the `hRP` of `reflection_positivity_continuum`
  holds for the functional `F ↦ ∫ F d(gffConfigMeasure m)` on the future-half observables, via
  `isReflectionPositive_of_splitIntegral`. Reflection positivity is not assumed anywhere in the
  chain; it is derived.

Boundary, in the same shape as §7's: the state is the **mass (ultralocal)** Gibbs measure on `Config`,
not the nearest-neighbour one, and it is unnormalised (positivity is invariant under a positive
rescaling, which is all that is used, so `m` is arbitrary). The coupled case stays the input its
module records: a nearest-neighbour action has no `ν ⊗ ν` split, which is exactly why the free-field
OS theorem is stated on the `2n+1`-slice model with a boundary slice and law `ρ ⊗ ν_z ⊗ ν_z`. No
spatial translation, no infinite-volume limit, and no unitarity `ℋ_OS → ℱ_out` is added here; E2 and
B2/B3 are untouched.

## Revised work order (2026-11-08)

This section supersedes the architecture, priority list and completion claims below **as a
reading guide for this file**. The earlier dated material is retained as implementation
history. It does not change the programme priorities in `CURRENT_WORK_ORDER.md` or claim
a continuum Yang–Mills construction, a mass gap, or conformal invariance. “4D Euclidean
to 3D” means reconstruction on a spatial slice with real-time evolution in $3+1$
dimensions; it is not a reduction to a three-dimensional spacetime theory.

This is a source-level documentation audit, not a fresh Lean build. Use **U** for an
existing result within its stated model, **C** for a missing hypothesis/identification,
**N** for an invalid inference, and **B** for a boundary of scope. Existing theorem
names such as `continuum` or `unconditional` do not erase their binders.

### Sources and conventions

* [book.tex](book.tex): the recursive second-quantization paragraph beginning “Since the
  second-quantization procedure can be applied recursively”, “Relation with the BRST
  formalism”, and “Pure SU(3) Yang-Mills theory”. These fix the nested field algebra
  and the role of observables; they do not identify an arbitrary Euclidean measure
  with the manuscript's Hamiltonian realization.
* [Book/FreeField.lean](Book/FreeField.lean), the Mehler-limit section, and
  [Book/SolovayTensor.lean](Book/SolovayTensor.lean), “Only the Mehler Measure on the
  Infinite Part”: Gaussian coordinate laws and Hilbert-space parametrization.
* [Book/YangMillsQuantization.lean](Book/YangMillsQuantization.lean), “The Weyl-Gauge
  Quadratic Form and the Friedrichs Route”: the inner Hamiltonian and its outer lift.
* [Hashimoto–Nodera](../papers/Hashimoto.md), Definition 2.4 and Theorem 4.1: bounded
  resolvents and approximation of operator $\phi$-functions, not an infrared gap theorem.
* [softmodes.md](softmodes.md), “Revised work package (2026-11-08)”: representation
  bridges, independent spectral exclusion, and the distinction between the absolute
  inner edge and inner excitation separation. Its S0–S4 obligations apply here too.
* [docs/euclidean_cft_proof.md](docs/euclidean_cft_proof.md): the detailed implementation
  record. Its older absence claims must be read against the newer modules listed here.

Keep four spaces distinct: the Euclidean configuration measure space $\mathscr X_E$;
its reference amplitude space $L^2(\gamma)$; the reconstructed OS space $\mathcal H_{OS}$;
and the manuscript's outer graded Fock space $\mathcal F_{out}$ over an inner space
$\mathcal K$. A Gaussian-chaos Fock representation of $L^2(\gamma)$, when constructed,
is another identification to prove, not a synonym for all four spaces.

Use $\theta$ for geometric reflection and
$\Theta F=\overline{F\circ\theta}$ for its action on complex observables. Reserve
$\Omega_{OS}=[1]$ for the reconstructed cyclic vector, $\Omega_{out}$ for empty outer
space, $\Psi_{info}$ for a vector prior when available, and $Q_{BRST}$ for the auxiliary
charge. An OS vacuum interpretation needs the chosen state hypotheses; it does not
identify that vector with empty outer space. BRST cohomology and the OS null-space
quotient serve different purposes and cannot replace one another.

### Corrections that govern the route

**N — finite coordinate rotation is not Euclidean field invariance.**
`EuclideanFock4D.mehlerMeasure4D = gaussianE 4` is a law on $\mathbb R^4$.
`mehler4D_O4_invariant` proves orthogonal invariance of that law, not invariance of a
random connection $A_\mu(x)$ under spacetime translations and rotations. Specify the
covariance and the action on spacetime, vector and colour indices. Rotational symmetry
alone also says nothing about reflection positivity of that covariance.

**N — nesting, scale decomposition and direct sum are different constructions.**
The manuscript's nested lift is $H=d\Gamma(h)$ with an interacting **inner** $h$.
A decomposition $\mathfrak h=\bigoplus_k\mathfrak h_k$ has a Fock tensor-factorization
only after the appropriate Fock functor and reference vacua have been specified.
It does not identify $\bigoplus_k\mathcal F_k$ with
$\bigotimes_k\mathcal F_k$ or with recursively nested Fock space. In the current
`BalabanRG` model, `Sector k` is the same $64$-dimensional real coordinate space at
every scale. `blockAveragingOp` projects the four component slots at each cell to
their common value; it is not yet physical gauge-covariant spatial block averaging.

**N — contraction does not preserve Born normalization.** Conditional expectation is
an $L^2$ contraction, not generally an isometry. For a coarse sigma-algebra $\mathcal G$,
the coarse density of $|\Psi|^2d\gamma$ is
$E_\gamma[|\Psi|^2\mid\mathcal G]$, not
$|E_\gamma[\Psi\mid\mathcal G]|^2$. The positive square-root amplitude update is
generally nonlinear. RG pushforward is linear on measures, while an effective-action
update involving a logarithm is not linear on amplitudes.

**N — commutation with reflection alone does not preserve RP.** To push RP through a
coarse map, prove its pullback sends the coarse positive-time algebra into the fine
positive-time algebra, intertwines reflection and preserves products/conjugation; then
identify the coarse state with the pushed-forward state. A bounded vector operator
$Q\Theta=\Theta Q$ alone supplies none of these state identities.

**N — the Wick obstruction is not a degree-three threshold.** The historical example
$\theta X=-X$ gives $E[(\theta X)X]=-E[X^2]<0$ already at degree one. For a centred
real Gaussian with compatible reflection symmetry, positivity of the **reflected
covariance on positive-time test functions** supports RP on the whole polynomial
algebra via Wick/chaos decomposition. There is no universal failure at degree three.
For ordinary quadratic monomials retain the same-half/disconnected contractions;
a formula containing only cross-plane contractions needs Wick ordering or centering.
The Markov/Feynman–Kac route remains a useful sufficient proof, not the only possible one.

**N — full-algebra RP is stronger than physical OS positivity.**
`ReflectionPositivity.IsReflectionPositive` quantifies over every `Observable`.
`OSReconstruction.OSState` consumes that stronger predicate and `Hphys` quotients the
full algebra. `ReflectionKernel.mk_thetaObs_eq_mk` shows the reflection becomes the
identity in that quotient under its hypotheses. Physical reconstruction instead uses
$\mathcal A_+$ only. Do not feed a theorem of RP **on** `PositiveTimeAlgebra` into
`OSState` as if it proved the stronger predicate. Reuse the quotient proof patterns
after restricting their carrier and hypotheses.

**N — Euclidean time is a forward semigroup.** Contractivity at every real time plus
the group law forces isometries; adding self-adjoint transfer maps makes the family
trivial (`TransferSelfAdjoint.physEvolCompletion_eq_one`). Use $\tau\ge0$,
$P(\tau)=e^{-\tau H}$ and the right generator $A=-H$, not a two-sided contractive
group or Stone's unitary-group converse. Real-time unitarity comes after identifying $H$.

### E0 — select and identify the concrete Euclidean model

Start with a finite-volume lattice benchmark with a specified compact gauge group,
links, plaquettes, boundary conditions and normalized Haar product measure. Define
$\mu_{a,L}=Z_{a,L}^{-1}e^{-S_{a,L}}\nu_{a,L}$ and the gauge-invariant observable
algebra. Separate this from a scalar Gaussian benchmark with a chosen covariance $C$.
A Gaussian coordinate prior does not by itself define the interacting measure or its
gauge-invariant correlations; a gauge-fixed vector Gaussian need not be RP on all components.

For a Mehler description choose a nuclear test space/cylindrical coordinate system,
a positive covariance and compatible finite marginals. If using a distribution-valued
field, prove the realization there. Standard independent Gaussian coordinates do not
produce identity-covariance Gaussian probability on $\ell^2$, and a pointwise “uniform
measure on the unit sphere of a Hilbert space” is not the needed construction.
At each finite cutoff establish the unitary chart and field identities. Hermite **functions**
need their Gaussian weights and normalization; bare Hermite polynomials are not an
orthonormal basis for Lebesgue $L^2$. A Gaussian chart does not add an oscillator
confinement term to the physical Hamiltonian (softmodes S0).

**Acceptance:** a model contract giving the measure, expectation, reflection, positive-time
test functions, field/loop observables and embeddings. Distinguish spatial volume $L$,
lattice spacing $a$, basis cutoff $\Lambda$ and RG depth $n$.

### E1 — assemble finite-model RP, then preserve it under actual coarse maps

Use a site-reflection/conditional-boundary benchmark first. With past/future conditional
laws matched by reflection, prove

$$d\mu(z,y_-,y_+)=d\rho(z)\,d\nu_z(y_-)\,d\nu_z(y_+),\qquad
\omega((\Theta F)F)=\int\left|\int F(z,y)\,d\nu_z(y)\right|^2d\rho(z)\ge0.$$

Supply integrability, positivity and normalization of the boundary law. For link-plane
reflections or actions with cross-plane plaquettes, prove the appropriate positive-kernel
or character-expansion identity; pointwise positivity of a Boltzmann weight is insufficient.
Transport vector signs for $A_0$ and reversal/inversion of oriented links explicitly.

Existing building blocks are `LatticeFreeField`, `HalfSpaceSplit`, `WilsonLattice`,
`WilsonLinkLattice`, `WilsonPastClass`, `HaarReference`, `GFFNormalization` and
`WilsonPartition` under `BookProof/ReflectionPositivity/`. Read their actual parameters:
`WilsonLinkLattice.Site L = Fin 3 → Fin L` is a three-coordinate box, not yet a
four-dimensional Euclidean gauge lattice. `HaarReference` is parametric in a compact
group and a measurable matrix representation; instantiate the intended non-abelian group
and prove the required a.e. unitarity/integrability. `WilsonPartition` proves normalized
probability and RP under its reference-probability and holonomy hypotheses. A closed-form
partition function is unnecessary; $0<Z<\infty$ suffices.

**Acceptance:** RP on the actual positive-time observable algebra for the normalized
finite model, including its concrete measure/geometry identification. Then prove each RG
pullback satisfies the algebra, support and state identities above. No full-algebra RP
assumption is allowed as a substitute.

### E2 — construct continuum expectations with the right convergence topology

Define coarse-graining maps and gauge transport before invoking Bałaban-type estimates.
State the bare coupling/counterterm trajectory and the precise norm in which the
small-field/large-field polymer estimate is sought. The existing
`BalabanRG.Convergence.balaban_rg_convergence` is the implication from a summable
increment estimate to a limit; it does not prove that estimate for Yang–Mills RG.

Prefer compatible expectations/Schwinger distributions on a common test algebra, with
tightness and uniform moment bounds where needed. A global amplitude $\Psi_\infty$ in
one reference $L^2(\gamma)$ is optional and needs absolute-continuity and embedding
proofs. Infinite-volume or continuum laws may be singular with respect to that reference.
Even when $\Psi_n\to\Psi$ in $L^2$ and all are normalized, the resulting $L^1$ density
convergence controls bounded observables; polynomial observables need additional moment
or uniform-integrability bounds. An unspecified vector norm limit does not imply all
Schwinger-function limits.

Pass RP through convergence of each reflected product $(\Theta F)G$ on a common
positive-time algebra. Prove limiting Euclidean translation/rotation covariance,
regularity and nontriviality separately; a finite regulator generally preserves only a
discrete subgroup. State which order of UV and thermodynamic limits is justified and
which constants are uniform. Existence and uniqueness of the limit for one Cauchy
sequence is not universality across regulators, boundary conditions or RG trajectories.

**Acceptance:** a normalized nontrivial limiting functional with half-space RP and
documented moment, covariance and continuity estimates. UV stability alone is not an
infrared clustering estimate. Keep the missing analytic estimates as named hypotheses.

### E3 — reconstruct on the positive-time algebra and build forward evolution

Construct the complex sesquilinear form
$\langle F,G\rangle_{OS}=\omega((\Theta F)G)$ on $\mathcal A_+$, its null
**subspace** $\mathcal N$, and the completion of $\mathcal A_+/\mathcal N$.
Do not call $\mathcal N$ an algebra ideal without proving ideal stability. Include the
unit to define $\Omega_{OS}=[1]$ and prove $\|\Omega_{OS}\|=1$.
The existing real bilinear quotient/completion is a reusable prototype; complexification
and the restriction to the half-space carrier remain explicit bridge work.

On positive-time smearings prove forward translation preserves support and the null
space. Derive symmetry, contractivity and strong continuity from the concrete state's
translation/reflection/regularity properties. These are inputs beyond RP in isolation.
Require $P(0)=I$, $P(s+t)=P(s)P(t)$ for $s,t\ge0$ and $P(t)^*=P(t)$.
Construct the dense right-generator domain, prove its range condition and identify the
positive self-adjoint $H=-A$. Use the symmetric contraction-semigroup theorem or a
verified resolvent/multiplication model; Hille–Yosida without symmetry gives a generator,
not automatically a self-adjoint Hamiltonian.

**Newer existing results:** `TransferSemigroupRight` and `SemigroupGenerator` provide
forward evolution, right derivatives, closedness/dissipativity and a resolvent estimate
under their bundled hypotheses. `MultiplierGenerator` and `MultiplierSelfAdjoint`
construct a positive self-adjoint `hamiltonianMulModel`, its resolvent and transfer flow
**given `MulModel`**. That bundle assumes a nonnegative measurable density, an isometry
onto a dense range in $L^2(\nu)$ and the exponential multiplier law. Producing those data
for the concrete half-space theory is still required. Thus “no generator exists anywhere
in the corpus” is stale, while “the physical interacting generator is identified” is unproved.

**2026-11-09:** `HalfSpaceState` / `HalfSpaceHilbert` now cover the half-space half of this
list — the quotient of `𝔄₊` with `Ω_OS = [1]`, `‖Ω_OS‖ = 1`, forward support and null-space
preservation (as hypotheses), and `P(0)=I`, `P(s+t)=P(s)P(t)`, `P(t)*=P(t)` with strong
continuity at `0⁺` on the completion. The concrete state (a measure on the lattice
configurations) and the generator domain/resolvent on `𝔄₊/𝔑₊` are still open, and the
constructed space is real.

**Acceptance:** a half-space state/space and a nontrivial strongly continuous symmetric
forward contraction semigroup, with its generator domain and resolvent identified.
Full Wightman reconstruction additionally needs the selected OS theorem's regularity,
Euclidean covariance, permutation/locality and clustering hypotheses, distributional
fields and analytic continuation. A Hilbert space and a heat semigroup alone do not
establish Lorentz covariance or locality.

### E4 — identify the reconstructed theory with the manuscript's nested fields

For a pure reference state satisfying B1, construct an isometry onto its physical
cyclic space $U:\mathcal H_{OS}\to\mathcal H_{ref}\subseteq\mathcal F_{out}$.
Align the OS cyclic vector with the selected spatial reference prior and intertwine
the smeared observable representations and heat semigroups. In the ground-vector case:

$$U\Omega_{OS}=\Psi_{ref},\qquad
UP(\tau)=e^{-\tau H_{ref}}U\quad(\tau\ge0),$$

$$H_{ref}=(H_{out}-E_{ref}I)|_{\mathcal H_{ref}},\qquad
H_{out}=d\Gamma(h_F).$$

Prove that this cyclic space reduces the dynamics, that `H_out Ψ_ref = E_ref Ψ_ref`
and that `H_ref ≥ 0` there. The reference-energy subtraction describes relative dynamics
on that space; it does not redefine the physical `h_F` by an outer number term. For a
general mixed prior use its GNS cyclic space. Without the required reference-state
properties retain a prior-dependent theory rather than assert a vacuum OS bridge.

`OSReconstruction/FockIntertwining.lean` defines `OsFockBridge` and proves consequences
of an assumed flow intertwiner. It does not construct this $U$. A real-linear bridge
also needs complex-structure compatibility before claiming a complex unitary field
identification. Gauge fixing or agreement of formal Hamiltonian expressions does not
identify the spaces, their domains, vacua or correlations. If the Euclidean construction
is not equivalent to this nested model, retain the two results as separate theories.

Keep inner composition and outer multiplication separate:
$d\Gamma(B^2)\ne d\Gamma(B)^2$ in general; likewise
$d\Gamma(I)=N_{out}$ while its square is $N_{out}^2$.
The inner interactions remain inside $h_F$ when its outer lift is quadratic. A density
for a non-Gaussian interacting measure does not become a free Gaussian field merely
because its Hilbert space has a Fock representation.

**Acceptance:** the concrete unitary/observable/flow diagram, or an explicit statement
that the bridge remains conditional. Do not transfer a gap or clustering rate before it.

### E5 — prove an infrared gap and only then attach certified numerics

Choose the spectral target and vacuum first. For an OS vacuum gap, prove
$\ker H=\mathbb C\Omega_{OS}$ (or state the full ground projection $P_0$) and

$$\|e^{-\tau H}(I-P_0)\|\le e^{-m\tau},\qquad m>0.$$

For the physical-prior bridge of E4, `H` here is the identified reference generator
`H_ref`, and `P₀` is its full ground projection. A gap above the empty outer sector is
a separate statement. A general time-dependent spatial prior need not define this
vacuum reconstruction, but still supplies prior-dependent predictions in the nested model.

Equivalently, after constructing the spectral measure, prove it has no support in
$(0,m)$ off the ground space. Pointwise strong convergence of the heat flow to $P_0$
does not give operator-norm convergence or a gap: positive masses can accumulate at zero.
`MultiplierSelfAdjoint` proves both the conditional norm-decay theorem and no-gap
obstructions in the multiplier model. Its symbol gap is an analytic input, not a result
about the Yang–Mills measure.

To infer a gap from clustering require a uniform estimate on a dense vacuum-complement
class, controlled by Hilbert norms, not decay of one chosen two-point function. With
a self-adjoint generator and a fixed finite prefactor, large-time decay excludes spectral
support below $m$. Do not discard that prefactor in a small-time difference quotient.
`Clustering` and `KallenLehmannModel` supply conditional Laplace-transform machinery;
the interacting infrared estimate remains open. Scalar radial time/space transfer requires
actual limiting $O(4)$ covariance; tensor/loop observables must be transformed with it.
The Mehler coordinate rotation theorem alone cannot supply that hypothesis.

If using softmodes S2 to prove $h_F\ge mI$ on **all** inner states, its outer lift
gives the outer-vacuum bound. An inner excitation gap above $E_0$ instead needs the
correct ground projection and the E4 identification. Shifting $h_F\mapsto h_F+\mu I$
adds $\mu N_{out}$, changes the model and does not manufacture physical inner clustering.
Never subtract two lower spectral bounds; use an independent ground upper bound or
direct coercivity. The occupation-diagonal surrogate still needs its physical form bridge.

For Hashimoto set $A=-H$ (or a declared time-rescaled version), so
$X_\gamma=(\gamma I+H)^{-1}$ has norm at most $1/\gamma$ for $\gamma>0$.
For the paper's Theorem 4.1 retain $\gamma_j=N_{shift}-sj>0$,
$m_{Krylov}<N_{shift}/s$, matrix invertibility, numerical-range and function-admissibility
hypotheses, and the full rational approximation factor:

$$\|\phi_k(A)v-u_{m_{Krylov}}\|\le2C\|v\|e^{-s m_{Krylov}}
\inf_{r\in\mathcal R^{SIRK}_{m_{Krylov}-1}}
\|f_{k,N_{shift}}-r\|_{\infty,\Sigma}.$$

The exponential alone is not an unlimited-depth convergence bound with fixed shift budget.
Carry rational approximation, inexact solve, rounding, basis-tail and continuum errors
separately. A solve defect $r$ yields inverse-action error at most $\|r\|/\gamma$;
a compressed-matrix eigenvector residual still omits $(I-P_\Lambda)Hu$.
Resolvent compression is not the inverse of Hamiltonian compression in general.
Strong resolvent convergence does not turn a finite gap into a continuum gap without
the independent uniform exclusion/form estimate. Keep the mass-gap sector gate §M4.9
in `CURRENT_WORK_ORDER.md` before any continuum interpretation of certificates.

**Temple acceptance:** an operator/domain/sector identification, normalized trial vector,
full residual $\eta$, and independently justified $\beta>\theta$ excluding the rest
of that sector's spectrum. Then $\theta-\eta^2/(\beta-\theta)\le E_0\le\theta$.
The operator-function approximation theorem does not supply that exclusion.

### Execution and validation

| Gate | Existing reusable content | Missing concrete input |
|---|---|---|
| E0 | Gaussian laws, Hermite bases | Euclidean field law and chart |
| E1 | Kernel RP, lattice splits, Haar/partition results | One matched 4D gauge model |
| E2 | Summable increments imply convergence | Actual RG estimates and limits |
| E3 | Half-space state/quotient (`HalfSpaceState`), forward semigroup (`HalfSpaceHilbert`), half-space generator with `H = −A` (`HalfSpaceGenerator`), finite-volume Gibbs state and its measure on the split lattice (`HalfSpaceFreeState`), complexification, complex OS form and `HilbertSpace ℂ` carrier (`HalfSpaceComplex`), quotients, multiplier generators, the bounded exponential `e^{−τH}` with its semigroup/contractivity/continuity laws (`HalfSpaceExponential`), its identification with the abstract `hsEvolCompletion` (`HalfSpaceExpIdentification`), the unbounded Hamiltonian in the multiplier model (`HalfSpaceUnboundedExp`) with dense domain and self-adjointness (`HalfSpaceMultiplierAdjoint`), the concrete lattice shift with the negative result on positive-time preservation (`HalfSpaceLatticeTranslation`), the two-point form of `hflow` (`HalfSpaceFlowMatrixElement`), the one-sided `ℕ`-indexed API (`HalfSpaceDiscreteSemigroup`) with an inhabiting half-preserving step and `HsHinvNat` for the Gibbs state (`HalfSpaceLatticeShiftSemigroup`), and the ultralocal infinite-volume free-field state via Ionescu–Tulcea (`HalfSpaceInfiniteVolumeGaussian`) with its reflection positivity on general positive-time cylinders (`HalfSpaceInfiniteVolumePositivity`), the two-site non-diagonal covariance pushforward matching `λ • (−Δ+m²)⁻¹` (`HalfSpaceCovariancePushforward`), the banded `n`-site chain covariance with its Hilbert–Schmidt norm (`HalfSpaceChainCovariance`), reflection positivity for a coupled covariant state (`HalfSpaceCovariantReflectionPositivity`), the covariance matrix `[[Cov T + 1, Cov T], [Cov T, Cov T + 1]]` of that state with its banded (`chainLaw`) and width-`k` (`bandLaw`) instantiations (`HalfSpaceCovStateCovariance`, `HalfSpaceChainBandCovariance`) | An infinite-volume *interacting* state and the *infinite* Hilbert–Schmidt pushforward by `(−Δ+m²)⁻¹`; the carrier identification `Hhalf Λ ≃ₗᵢ L²(ν)`; `hflow` itself (only its two-point consequence is proved) |
| E4 | `OsFockBridge` consequences, plus constructed (non-conditional) instances: the one-particle sector (`OneParticleBridge`) and a two-state finite-volume Gibbs state (`FiniteVolumeGibbsBridge`) | Physical spatial prior, field and flow bridge for the interacting theory |
| E5 | Conditional clustering and certificate receivers | Uniform infrared exclusion |

Execute **E0 → E1 → E2 → E3 → E4 → E5** as dependency gates; abstract E3 work and E5
error bookkeeping can progress before the continuum estimates. This ordering applies to
the Euclidean route, not to completion of the separate nested Hamiltonian plans. Reuse
the existing half-space interfaces; the new bridge task is B0's observable and spatial-prior
test, then B1 at a finite regulator. A finite-model measure/RP contract remains necessary
for the chosen Euclidean model.
Proposed new modules, not existing proofs, are
`BookProof/OSReconstruction/HalfSpaceState.lean` and
`BookProof/OSReconstruction/HalfSpaceHilbert.lean`.

**2026-11-09: both modules exist and build** (`lake build BookProof`).
`HalfSpaceState` supplies the half-space state (`HalfSpaceState`: `θ`-invariant linear
functional, reflection positive on `PositiveTimeAlgebra` only, `ω 1 = 1`), the OS form
`hsBilin` on `𝔄₊ × 𝔄₊` with bilinearity, symmetry (from `θ`-invariance, not positivity),
quadratic expansion and Cauchy–Schwarz, the null **subspace** `HsRadical` (no ideal claim)
with `mem_hsRadical_of_self_eq_zero` and descent, the quotient `HsSpace`, its inner-product
structure, the completion `Hhalf`, and the vacuum `hsVacuum = [1]` with `hsVacuum_norm`.
`HalfSpaceHilbert` supplies `PreservesPositiveTime`, the restricted evolution `hsEvol`, the
one-sided hypothesis `HsHinv`, `hsRadical_invariant` (forward translation preserves the null
space), the descended `hsQuotMap` with contractivity, `P(0) = I`, `P(s+t) = P(s)P(t)`, the
completion `hsEvolCompletion`, strong continuity at `0⁺` from matrix-element continuity, and
`hsEvolCompletion_isSelfAdjoint` — **`P(τ)* = P(τ)`** — from the dense two-point symmetry
hypothesis `HsSymmetric`.

**2026-11-09, follow-up (three modules, all building):** the generator/state/complexification
work listed as missing above now exists.

* `HalfSpaceGenerator` **ports** `SemigroupGenerator` to the half-space carrier: the difference
  quotient `hsDiffQuot`, the one-sided domain `HsHasGen`/`hsGenDomain`/`hsGenValue`, the
  restricted-evolution estimates `hsEvolCompletionFun_zero`, `dist_hsEvolCompletionFun_le`
  (contraction), `continuousOn_hsEvolCompletionFun`, `intervalIntegrable_hsEvolCompletionFun`,
  `hsEvol_sub_eq_integral` and `tendsto_average_hsEvol` (strong continuity in integral form),
  then closedness (`hsGenerator_isClosed`), dissipativity
  (`hsGenerator_inner_le_zero`), the resolvent bound `hsGenerator_resolvent_bound` and
  injectivity, and finally the identification `hsGenerator_eq_neg` / `hsGenerator_inner_eq_neg`:
  **`H = −A`** on the dense domain, self-adjointness carried by the symmetric-contraction
  hypotheses. The `H = −A` identification is conditional on
  `∀ z, HasDerivWithinAt (fun τ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0`, the
  local form of `P(τ) = e^{−τH}`. (That shape is now realised by a constructed family —
  `hsExpOp_hasDerivWithinAt_zero` below — though the family itself is not identified with
  `hsEvolCompletionFun`.)
* `HalfSpaceFreeState` **instantiates `HalfSpaceState` with a concrete state**: the finite-volume
  Gibbs functional `gibbsFun (V : GibbsVolume)` on the block lattice, with the configuration
  split `Config ≃ (HalfIdx → ℝ) × (HalfIdx → ℝ)` (`cellsPerBlock = 16 = 8 + 8`, no reflection
  slice, so `flipCell` is the half swap), `dependsOn_posTimeCoords_iff` (`𝔄₊` is exactly the
  observables that do not see the negative half), `gibbsFun_one` (`ω 1 = 1`),
  `gibbs_reflectionPositive` from the **finite-volume Feynman–Kac identity as a square**
  `gibbsFun_osForm : ω(θF·F) = (Σ_x ρ(x) F(x,0))²`, and the packaged `gibbsHalfSpaceState`
  with `gibbsVacuum_norm`, and **the state as a genuine measure on `Config`**: `gibbsAtom`,
  `gibbsMeasure` (the finitely supported law `Σ_{x,y} w x · w y · δ_{(x,y)}`), `gibbsMeasure_univ`
  and the `IsProbabilityMeasure` instance, the domination lemmas `gibbsAtom_le_row`/`gibbsRow_le`/
  `gibbsAtom_le`, and `integral_gibbsMeasure : ∫ F d(gibbsMeasure V) = gibbsFun V F` on the
  integrable observables — so the Gibbs functional is the integral state of its measure. The grid
  weights are the samples of the Gaussian density, and `freeFieldMeasure` (the product Gaussian
  `∏ N(0, 1/2)`) is recorded as the block-lattice reference law *without* an identification.
* `HalfSpaceComplex` **complexifies `Hhalf` and restates the OS form as a complex sesquilinear
  form**: carrier `HhalfC Λ = Hhalf Λ × Hhalf Λ` with `ofReal`/`ofImag`, the complex structure
  `cSMul (a+bi)(x+iy) = (ax−by) + i(bx+ay)` and its `Module ℂ` instance; the complex OS form
  `hsComplexForm z w = ⟪z₁,w₁⟫ + ⟪z₂,w₂⟫ + i(⟪z₁,w₂⟫ − ⟪z₂,w₁⟫)`, with the `ℂ`-sesquilinear
  laws (`hsComplexForm_smul_left` in Mathlib's `c̄ ⟪z,w⟫` convention, `hsComplexForm_smul_right`),
  conjugate symmetry `hsComplexForm_conj_symm`, realism of the diagonal
  `hsComplexForm_self_re : (⟪z,z⟫).re = ‖z₁‖² + ‖z₂‖²` with `hsComplexForm_self_nonneg`, and
  definiteness `hsComplexForm_self_eq_zero_iff`; `hsComplexForm_ofReal` records that the real
  OS form is the restriction of the complex one; `hsComplexPreCore`, `hsComplexSeminormed` and
  `instInnerProductSpaceHhalfC` register the complex inner product space; and **the carrier is
  complete**, so `instHilbertSpaceHhalfC : HilbertSpace ℂ (HhalfC Λ)` is attached. The proof is
  for the *core* (ℓ²) norm, not the product max norm: `HhalfC` is a `def`, so no `Prod` instance
  can compete, and `norm_sq_hhalfC : ‖z‖² = ‖z₁‖² + ‖z₂‖²` makes the coordinate bounds
  `norm_fst_le`/`norm_snd_le` and the ℓ¹ reassembly `norm_le_add_coord` available;
  `hhalfC_complete` takes coordinate Cauchy limits from the completeness of `Hhalf` and rebuilds
  the limit with `norm_eq_zero_iff_hhalfC`.

**Landed 2026-11-14, the exponential `e^{−τH}` of E3.** `BookProof/OSReconstruction/HalfSpaceExponential.lean`
constructs the family the generator identification names, for a **bounded**
`H : Hhalf Λ →L[ℝ] Hhalf Λ`, as `hsExpOp Λ H τ = NormedSpace.exp (τ • (-H))`, and proves the
semigroup laws on it rather than assuming them. No `sorry`; axiom footprint of every theorem below
`{propext, Classical.choice, Quot.sound}` only (`Work/HalfSpaceExponentialAudit.lean`).

* **`hsExpOp_zero`, `hsExpOp_add`** — `P(0) = I` and `P(s+t) = P(s)P(t)`, the latter from
  `exp_add_of_commute_of_mem_ball` applied to the two commuting scalar multiples `s • −H`, `t • −H`
  (`commute_smul_neg`); the ball condition is free because `expSeries_radius_eq_top` makes the
  radius `⊤`.
* **`hsExpOp_isSelfAdjoint`** — **`P(τ)* = P(τ)`** for self-adjoint `H`, via `NormedSpace.star_exp`
  and `star (τ • −H) = τ • −H`. Symmetry is therefore derived from `H`, not postulated as it is
  (`HsSymmetric`) for the abstract `hsEvolCompletion`.
* **`hasDerivAt_hsExpOp`, `hasDerivAt_hsExpOp_apply`, `hsExpOp_hasDerivWithinAt_zero`** — the
  operator derivative `P'(τ) = P(τ)·(−H)`, the orbit derivative `d/dτ P(τ)z = −H(P(τ)z)`, and hence
  `d/dτ P(τ)z = −H z` at `0` **from the right, with no condition on `z`**. The last statement is
  literally the `hflow` hypothesis of `hsGenerator_eq_neg`, so that hypothesis is non-vacuous: it is
  discharged by `fun _ => hsExpOp_hasDerivWithinAt_zero …` once the two families are identified.
* **`norm_hsExpOp_antitone`, `norm_hsExpOp_le`** — **contractivity** for `τ ≥ 0` under the quadratic
  form condition `∀ z, 0 ≤ ⟪H z, z⟫` (for self-adjoint `H` this *is* `H ≥ 0`): the derivative of
  `‖P(τ)z‖²` is `−2⟪H(P(τ)z), P(τ)z⟫ ≤ 0`, so `‖P(·)z‖` is antitone.
* **`continuous_hsExpOp`, `tendsto_hsExpOp_zero`** — **strong continuity at `0⁺`**, `P(τ)z → z`.

Boundary: `H` is bounded; the exponential of the unbounded physical Hamiltonian is not constructed
(that is the multiplier/spectral-theorem job `MultiplierSelfAdjoint` does inside its `MulModel`, and
E3's remaining infinite-volume work). What was established at that point is that the exponential
exists, is a symmetric strongly continuous contraction semigroup, and has generator `−H` — the input
`hsGenerator_eq_neg` was missing. The identification with `hsEvolCompletion` and the unbounded case
were landed the same day; see the next two paragraphs.

**Landed 2026-11-14, the identification of the semigroup with the exponential.**
`BookProof/OSReconstruction/HalfSpaceExpIdentification.lean`. Under the very hypothesis
`hsGenerator_eq_neg` assumes (`hflow`), the abstract semigroup **is** the exponential: no separate
uniqueness theorem for `ẋ = −H x` has to be built, Grönwall supplies it. No `sorry`; axiom footprint
`{propext, Classical.choice, Quot.sound}` only (`Work/HalfSpaceExpIdentificationAudit.lean`).

* `hsEvolCompletionFun_comp_neg` — the semigroup commutes with `H` (`A P(τ) = P(τ)A` for `A = −H` on
  all of `Hhalf`), by pushing the difference quotient through the continuous `P(τ)`.
* `hasDerivWithinAt_hsEvol_flow` — hence the orbit's right derivative at every `τ ≥ 0` is `−H(P(τ)z)`,
  and `Ici`/`Ioi` are interchanged through `hasDerivWithinAt_iff_tendsto_slope` (they cut out the
  same punctured neighbourhood).
* `hsEvolCompletionFun_eq_hsExpOp` — `P(τ)z = e^{−τH}z` for `τ ≥ 0`: both orbits solve `v' = −H v`
  from `0`, so `norm_le_gronwallBound_of_norm_deriv_right_le` with `δ = ε = 0` gives `‖v‖ ≤ 0`.
* `hsGenerator_eq_neg_exp` — `hsGenerator_eq_neg` plus the identification in one statement: every
  `z` is in the domain, `A z = −H z`, **and** the semigroup at `z` is the exponential.
* `hsExpOp_iff_flow` — `hflow` holds **iff** `P` is the exponential. The hypothesis is therefore not
  independent information about the flow: it pins it down completely.

Boundary: `hflow` is still an assumption (nothing derives the flow from the lattice translation), and
`H` is still bounded.

**Landed 2026-11-14, the unbounded Hamiltonian in the multiplier model.**
`BookProof/OSReconstruction/HalfSpaceUnboundedExp.lean`, on top of `L2Multiplier`. `NormedSpace.exp`
is never applied to an unbounded operator: the exponential of the multiplication operator `M_f` *is*
the multiplier `e^{−τ f}`, and an isometric equivalence `e : Hhalf Λ ≃ₗᵢ[ℝ] L²(ν)` transports it back
to the half-space carrier. No `sorry`; axiom footprint `{propext, Classical.choice, Quot.sound}` only
(`Work/HalfSpaceUnboundedExpAudit.lean`).

* `HsMulModel` — the datum: `ν`, a measurable `f ≥ 0` a.e., and `e`. The family
  `HsMulModel.flow τ = e⁻¹ ∘ (multiplication by e^{−τf}) ∘ e` is **constructed**, not assumed.
* `flow_zero`, `flow_comp`, `flow_contractive`, `flow_tendsto` — `P(0)=I`, `P(s+t)=P(s)P(t)`,
  contraction, strong continuity at `0⁺` (the last on the natural domain, which is all the corpus's
  `tendsto_expFlow_zero` requires).
* `HsMulModel.domain` — the natural domain `{z | f · e z ∈ L²(ν)}`, a submodule; `opValue` is `−M_f z`
  and `e_opValue` records `e (opValue z) = −f · e z`.
* `hasDerivWithinAt_flow` — **the unbounded generator statement**: `d/dτ P(τ)z = −M_f z` at `0⁺` for
  every `z` in that domain, the unbounded analogue of `hsExpOp_hasDerivWithinAt_zero`.
* `mem_domain_of_bounded` — when `f` is essentially bounded the domain is everything, so the bounded
  exponential of `HalfSpaceExponential` is the special case.

Boundary: `HsMulModel` assumes the carrier *is* `L²(ν)` (an isometric equivalence), which is
stronger than the dense-range `MulModel.U`; producing that equivalence for the concrete half-space
theory remains open. Density of the domain and self-adjointness of `M_f`, which were open here, are
closed by the next paragraph.

**Landed 2026-11-14, density and self-adjointness of the unbounded Hamiltonian.**
`BookProof/OSReconstruction/HalfSpaceMultiplierAdjoint.lean`. For **every** measurable real `f` — no
boundedness, no positivity, no `HinvRight`, no multiplier law — the domain is dense and the operator
is self-adjoint. No `sorry`; axiom footprint `{propext, Classical.choice, Quot.sound}` only
(`Work/HalfSpaceMultiplierAdjointAudit.lean`).

* `dense_domain` — the truncations `1_{|f| ≤ n} · u` lie in the domain and converge to `u` in `L²`:
  dominated convergence on `(u_n − u)²` (pointwise convergence is *everywhere*, because a real-valued
  `f` is finite at each point), then `‖v‖² = ∫ v²` (`norm_sq_eq_integral`) turns it into norm
  convergence; the isometric equivalence carries the dense set back to `Hhalf Λ`.
* `isFormalAdjoint_hamiltonian` — symmetry, from reality of `f`: `∫ (f u) v = ∫ u (f v)`.
* `le_adjoint_hamiltonian` — the non-trivial inclusion `H† ≤ H`, by the comparison multiplier
`φ = (1 + |f|)⁻¹`. Since `f φ` is bounded by one, `g = e⁻¹ (φ · u) ∈ dom H` for every `u ∈ L²`, so
the adjoint relation gives `∫ u · (φ(e w) + φ f (e v)) = 0` for all `u`; testing on the bracket
itself forces it to vanish, and `φ > 0` a.e. gives `f · e v = −(e w)` a.e. Hence `v ∈ dom H` and
`H v = w`.
* `hamiltonian_isSelfAdjoint` — `IsSelfAdjoint H`, combining the two inclusions with
`IsFormalAdjoint.le_adjoint`.

So the multiplier Hamiltonian is a genuine self-adjoint operator, not a formally symmetric one; what
`HsMulModel` still assumes is only the identification of the carrier with `L²(ν)`.

Two further E3 results settle what `hflow` can and cannot rest on.
`BookProof/OSReconstruction/HalfSpaceLatticeTranslation.lean` builds the translation the lattice
actually supplies — the cyclic cell rotation, lifted to an automorphism `obsShift k` (`k : ℤ`) of
the observable algebra — and proves `PreservesPositiveTime` is **false** for it: the last
positive-time cell rotates onto the first negative-time cell, so
`not_preservesPositiveTime_of_shift` rules out any `TimeTranslation` whose time-one map is the
shift. The hypothesis quantifies over all real `τ`, while the lattice gives a `ℤ`-action, so this
is an API mismatch rather than a missing proof.
`BookProof/OSReconstruction/HalfSpaceFlowMatrixElement.lean` proves the weaker form that does
follow: `hflow` implies the two-point derivative `d/dτ ⟪y, P τ z⟫ = ⟪y, −H z⟫` at `0⁺`
(`hasDerivWithinAt_inner_hsEvol`), in derivative and slope form. The converse fails in general
(weak convergence plus a norm bound is not strong convergence), so matrix elements cannot replace
`hflow`.

Three further E3 modules act on that API decision and on the infinite-volume question.
`BookProof/OSReconstruction/HalfSpaceDiscreteSemigroup.lean` weakens the evolution API from the
`ℝ`-indexed `TimeTranslation` to an `ℕ`-indexed semigroup `DiscreteTimeTranslation`
(`map_zero`, `map_add`, `discreteTimeTranslation_semigroup`), with `PreservesPositiveTimeNat`,
`hsEvolNat` and the contractivity hypothesis `HsHinvNat`; the old API embeds in it by
restriction (`ofTimeTranslation`, `hsEvolNat_ofTimeTranslation`, `hsHinvNat_of_hsHinv`), so nothing
is lost. `BookProof/OSReconstruction/HalfSpaceLatticeShiftSemigroup.lean` **inhabits the weakened
API**: `cellHalfRotate` rotates each time half internally (so
`preservesPositiveTimeNat_halfRotateTranslation` holds — exactly what the cyclic shift cannot
deliver), the step commutes with the reflection (`siteHalfRotate_reflectCoord`,
`thetaObs_obsHalfRotate`), and the finite-volume Gibbs state is invariant under it, so
`hsHinvNat_gibbsHalfSpaceState` proves `HsHinvNat` as an **equality** `⟨T n F, T n F⟩ = ⟨F, F⟩`
for any grid closed under the rotation (`IsHalfRotateInvariant`, a hypothesis on `V.support`).
`BookProof/OSReconstruction/HalfSpaceInfiniteVolumeGaussian.lean` builds the infinite-volume
free-field reference state `freeFieldInfinite` on `ℕ → Config`: the Ionescu–Tulcea product of the
block laws, shown to be `Measure.infinitePiNat` itself (`freeFieldInfinite_eq_infinitePiNat`), with
its cylinder marginals (`freeFieldInfinite_restrict`, `freeFieldInfinite_pi`) and the one-block
pushforward `map_blockProj_freeFieldInfinite : (freeFieldInfinite).map (blockProj k) =
freeFieldMeasure`. With independent blocks the covariance is the identity, so this is the
ultralocal free field, not `(−Δ+m²)⁻¹` and not the interacting Gibbs measure.

Two more E3 modules close the ambient statement and the covariance question as far as the
available measure theory allows. `BookProof/OSReconstruction/HalfSpaceInfiniteVolumePositivity.lean`
proves **reflection positivity of the infinite-volume free-field state**: with the state written in
half coordinates (`splitFreeField`), the reflection swapping the halves of every block
(`chainReflect`, an involution), and a positive-time cylinder observable — a finite product over
time slices of functions of the positive half — `0 ≤ ∫ θF · F` (`posCylinder_reflectionPositive`),
by `integral_restrict_infinitePi` plus Fubini over the finite product of blocks. The hypothesis
`IsHalfRotateInvariant` of `hsHinvNat_gibbsHalfSpaceState` is also discharged: the constant grid
`constGrid m` is rotation invariant (`isHalfRotateInvariant_constGrid`), so
`hsHinvNat_constGrid` and `constGrid_transfer_contractive` hold with no hypothesis left.
`BookProof/OSReconstruction/HalfSpaceCovariancePushforward.lean` builds a **non-diagonal covariance
pushforward** on the two-site truncation: the Cholesky map `p ↦ (p.1, ρ p.1 + s p.2)` pushes the
product of two unit Gaussians to a state with covariance `ρ` off the diagonal and `1` on it
(`corrLaw_cov`, `corrLaw_var`), covariance matrix of finite Hilbert–Schmidt norm `2 + 2ρ²`
(`covMatrix_hsNormSq`), and for `ρ = 1/(1+m²)` exactly `λ • (−Δ+m²)⁻¹` entrywise
(`covMatrix_eq_lapInv`).

Three further E3 modules extend that. `BookProof/OSReconstruction/HalfSpaceChainCovariance.lean`
carries the non-diagonal covariance from two sites to an `n`-site **chain**: for a permutation `σ` of
the sites, the additive-neighbour pushforward `Y i = X i + ρ X (σ i)` of white noise has covariance
`δ_{ij} + ρ(δ_{σ i,j} + δ_{i,σ j}) + ρ²δ_{ij}` (`chainLaw_cov`), which **vanishes off the band**
`{i, σ i, σ⁻¹ i}` (`chainCov_eq_zero`; the diagonal is `1 + ρ²`) and whose squared Hilbert–Schmidt
norm is `card ι · ((1+ρ²)² + 2ρ²)` (`chainCov_hsNormSq`), instantiated on the `(n+1)`-site cycle as
`cycleChain_cov_hsNormSq`. The banded matrix is the nearest-neighbour *truncation* of
`(−Δ+m²)⁻¹` (the inverse of a chain Laplacian is dense), so only the two-site case is an exact
multiple of `(−Δ+m²)⁻¹`; and the chain is finite, so no infinite covariance operator is involved.
The positivity module was also widened from slice products to the **whole positive-time algebra**:
`map_pi_prod_pi` proves that a finite product of pair laws separates into the product of the two
half-marginals (from `Measure.pi_eq_generateFrom` on measurable rectangles), and hence for an
*arbitrary* measurable `G` of the positive halves the OS form is `(∫ G)² ≥ 0`
(`posCyl_reflectionPositive`). Finally `BookProof/OSReconstruction/HalfSpaceCovariantReflectionPositivity.lean`
proves reflection positivity for a state that is **not a product of its halves**: the two halves are
white noise shifted by a common random vector `T` (`covState`), so they are coupled, and for a
bounded measurable observable of one half `0 ≤ ∫ θF · F` (`covState_reflectionPositive`), because
conditioning on `T` makes the halves independent and the OS form becomes the `ν`-average of
`(∫ F (t + x) ∂γ)²`.

That state's covariance matrix was described there only informally; it is now **proved**
(`BookProof/OSReconstruction/HalfSpaceCovStateCovariance.lean`).  For any shift law `ν` with finite
second moments the blocks of `covState ν` are `Cov T + 1` on the diagonal
(`covState_cov_fst_fst`, `covState_cov_snd_snd`) and `Cov T` off it (`covState_cov_fst_snd`), i.e.
`[[Cov T + 1, Cov T], [Cov T, Cov T + 1]]`, the `+1` being the white noise of the halves — the proof
is the observation that a covariance only reads the marginal it uses
(`covariance_fst_fst_prod`, `covariance_snd_snd_prod`).  Instantiating at the chain law makes the
coupling a banded equality rather than a posit: the cross-covariance of the two halves of
`covState (chainLaw σ ρ)` is `chainCov σ ρ` and vanishes off `{i, σ i, σ⁻¹ i}`
(`covState_chainLaw_cov_fst_snd_eq_zero`).  The band width is also no longer restricted to one:
`BookProof/OSReconstruction/HalfSpaceChainBandCovariance.lean` pushes white noise forward by
`1 + ρ ∑_{a=1}^{k} P_σ^a`, whose covariance
`δ_{ij} + ρ ∑_a (δ_{σ^a i,j} + δ_{i,σ^a j}) + ρ² ∑_{a,b} δ_{σ^a i,σ^b j}` (`bandLaw_cov`) is
supported exactly on `{σ^d i : |d| ≤ k}` (`bandCov_eq_zero`), has diagonal `1 + ρ²k` on a site with
no short cycle (`bandCov_diag`), and returns `chainCov` at `k = 1` (`bandCov_one`); at width `k` the
coupled state's off-diagonal block vanishes off that band
(`covState_bandLaw_cov_fst_snd_eq_zero`).  The width-`k` coefficients and the Hilbert–Schmidt
norm are proved in `HalfSpaceChainBandHSNorm` (`bandCov_comm`, `bandCov_forward`,
`bandCov_backward`, `bandCov_row_sum`, `band_sum_closed`, `bandCov_hsNormSq`, and
`bandCov_hsNormSq_one` matching `chainCov_hsNormSq`).  The bi-infinite width-`k` kernel is
recorded in `BookProof/OSReconstruction/HalfSpaceInfiniteBandedCovariance.lean` (`bandedCovZ` with
`bandedCovZ_self`, `bandedCovZ_forward`, `bandedCovZ_back`, `bandedCovZ_comm`,
`bandedCovZ_banded`), whose squared `ℓ²` row norm summed over all of `ℤ`
(`bandedCovZ_row_tsum`) is the same per-site factor as `bandCov_hsNormSq`
(`bandedCovZ_row_tsum_closed`; `bandedCovZ_row_tsum_one` and `bandedCovZ_row_tsum_zero` at widths
`1` and `0`) and agrees with the finite row sum `bandCov_row_sum`
(`bandedCovZ_row_tsum_eq_bandCov_row_sum`); it is also positive definite, being the
autocorrelation of the one-sided weight `1, ρ, …, ρ` (`bandedCovZ_eq_weight_sum`) with quadratic
form an explicit sum of squares (`bandedCovZ_quadForm_eq_sum_sq`, `bandedCovZ_posSemidef`) that
vanishes only on the zero test function (`bandedCovZ_posDef`), so positivity of the Toeplitz symbol
is no longer the missing ingredient — only the extension theorem is.  The kernel is Toeplitz
(`bandedCovZ_translate`) but **not** reflection positive on a half-line for `θ i = -i`
(`bandedCovZ_not_reflectionPositive`): RP is a property of the doubled `covState`, where the
white-noise block cancels the cross block — and that doubled form is nonnegative for this kernel
too, for any finitely supported test-function pair (`doubledOSForm_eq_folded`,
`bandedCovZ_doubled_reflectionPositive`).  The finite-volume cycle has the same statement
(`HalfSpaceChainBandReflectionPositivity`: `bandCov_posSemidef` via the variance of `bandLaw`, and
`bandCov_doubled_reflectionPositive` for any reflection preserving `bandCov`).  A banded Toeplitz matrix is still not
Hilbert–Schmidt on `ℓ²(ℤ)`.  What remains unbuilt is the Gaussian *measure* on `ℤ → ℝ` with that
kernel and any Hilbert–Schmidt square root of it.

The chain is collected, link by link with its remaining hypotheses, in
[E3_RECONSTRUCTION_CHAIN.md](E3_RECONSTRUCTION_CHAIN.md); its §4.2 surveys what an infinite-volume
state would require and inventories the Mathlib projective-limit/Ionescu–Tulcea machinery that is
already available.

Still missing at E3: an infinite-volume *interacting* or continuum state — the ultralocal free-field
reference state now exists, but `gibbsMeasure` is supported on the declared finite grid, is not a
marginal of `freeFieldInfinite`, and is not identified with `freeFieldMeasure`; the Hilbert–Schmidt
pushforward by the *infinite* non-diagonal covariance `(−Δ+m²)⁻¹`, which is what would couple the
blocks — only a banded `n`-site truncation and a coupled (covariant) state with proved positivity
exist; the carrier identification
`Hhalf Λ ≃ₗᵢ L²(ν)` that `HsMulModel` takes as datum; `hflow` itself (the lattice shift cannot
witness `PreservesPositiveTime`, and only the two-point consequence is proved); and surjectivity of
`λ − A` (Lumer–Phillips' range condition). Separability of the
complexified carrier, support preservation, contractivity and two-point symmetry remain named
hypotheses, as `HinvRight` and `∀ τ, IsSelfAdjoint (P τ)` already are in the corpus.

Use the local `lean-toolchain` (currently v4.28.0). A proof port from another toolchain
must compile here before it is counted as implemented; verify sibling paths rather than
relying on the historical `../timepiee331/` spelling. MM0 export is a separate deliverable
requiring supported statement and proof translation; emitting theorems as new axioms is
not proof conversion.

For a later implementation, build affected modules, audit final theorem binders and
axioms, and distinguish abstract tests from instantiations of the interacting model.
For this documentation-only revision, check relative links, whitespace and doc-index
freshness. No numerical certificate, Lean compilation or book-rendering result is claimed.

## Historical architecture and status (2026-10-29 to 2026-11-05)

The revised work order above controls the interpretation of all completion claims below.
In particular the full-algebra OS receiver, the Wick degree-threshold claim, the old
generator absence claims and the proposed softmodes separation are superseded by the
specific corrections and dependencies above.

The original proposal was a modular research plan for formalizing **Bałaban’s constructive
Euclidean approach** using the **nested Fock-space framework**, constructing a Euclidean
statistical theory before deriving its Hamiltonian by reflection-positive reconstruction.

Note that you can produce the proofs in any version  of Lean4 it is more convenient to you , you can also use the the 4.33.1 version of these proofs in ../timepiee331/ , since the end goal is to convert everything to MM0.

---

### Conceptual Architecture

```
                    4D Euclidean Spacetime (No Hamiltonian)
            ┌────────────────────────────────────────────────────────┐
            │  Configuration space: A ∈ S'(ℝ⁴, 𝔰𝔲(N))                │
            │  Prior: 4D Rotation-Invariant Mehler / Gaussian       │
            │  Nested Fock-Space: ℱ_E = ⨂_{scale k} ℱ_k              │
            └───────────────────────────┬────────────────────────────┘
                                        │
                         Bałaban Multiscale RG Operators
                                        │
            ┌───────────────────────────▼────────────────────────────┐
            │  Block-averaging: Q_k : ℱ_k → ℱ_{k+1}                  │
            │  State sequence: Ψ_N = ⨂_{k=0}^N Q_k Ψ_0              │
            │  Convergence in ℱ_E: Ψ_∞ = lim_{N→∞} Ψ_N (Cauchy)       │
            └───────────────────────────┬────────────────────────────┘
                                        │
                          Reflection Positivity Check
                                        │
            ┌───────────────────────────▼────────────────────────────┐
            │  Time-reflection: θ(x₀, x) = (-x₀, x)                  │
            │  Half-space algebra 𝒜₊ (x₀ > 0)                        │
            │  Theorem: ⟨Ψ_∞, π(θ(F)* F) Ψ_∞⟩ ≥ 0                    │
            └───────────────────────────┬────────────────────────────┘
                                        │
                       Osterwalder–Schrader Reconstruction
                                        │
            ┌───────────────────────────▼────────────────────────────┐
            │  Physical Hilbert Space: ℋ_Mink = 𝒜₊ / 𝒩               │
            │  Emergent Hamiltonian: e^{-τ H} [F] = [T_τ F]          │
            │  Relativistic Wightman Theory on ℝ^{1,3}               │
            └────────────────────────────────────────────────────────┘
```

---

### Phase 1: 4D Euclidean Nested Fock Space & $O(4)$ Invariant Measure
**Goal:** Define the 4D Euclidean field substrate without breaking space and time into a $3+1$ split, using the Mehler measure on an infinite-dimensional sphere.

#### 1.1. 4D Euclidean Configuration Core
* In Hamiltonian field theory, one works with $(A_i, \pi_i)$ on $\mathbb{R}^3$ [1.1]. In the 4D Euclidean theory, the field coordinate is a 4-vector $A_\mu(x) = (A_0, A_1, A_2, A_3)(x)$ on $\mathbb{R}^4$ taking values in $\mathfrak{su}(N)$.
* Construct the configuration space using the 4D product Hermite basis on $L^2(\mathbb{R}^4 \otimes \mathfrak{su}(N))$:
  $$\phi_{\alpha, \mu, a}(x) = H_{\alpha_0}(x_0) H_{\alpha_1}(x_1) H_{\alpha_2}(x_2) H_{\alpha_3}(x_3) T_a$$
* **Lean 4 Target File:** `BookProof/EuclideanFock4D/CoreBasis.lean`
  ```lean
  def EuclideanHermiteBasis4D (N : ℕ) : OrthonormalBasis (ℕ⁴ × Fin 4 × Fin (N^2 - 1)) ℝ (L2 (ℝ⁴ × Fin 4 × Fin (N^2 - 1)))
  ```

#### 1.2. The 4D Mehler Measure and $O(4)$ Invariance
* Generalize `PhysHSGaussian` [1.1] to dimension 4: Define the free Euclidean Gaussian measure $d\gamma_0(A)$ on the sphere $S^\infty$.
* Prove that $d\gamma_0$ is invariant under the full 4D Euclidean rotation/reflection group $O(4)$:
  ```lean
  theorem mehler4D_O4_invariant (R : EuclideanIsometry 4) :
    Measure.map (liftIsometry R) (mehlerMeasure4D) = mehlerMeasure4D
  ```

---

### Phase 2: Bałaban Multiscale RG as Nested Fock Operators
**Goal:** Translate Bałaban’s functional block-spin transformations into bounded linear operators acting between sectors of a nested Fock space.

#### 2.1. Scale Decomposition of the Nested Fock Space
* Instead of treating the multiscale expansion as an infinite sequence of unregularized path integrals, define the total Euclidean space as a **nested, graded Fock space over scales**:
  $$\mathcal{F}_{\text{total}} = \bigoplus_{k=0}^\infty \mathcal{F}_k, \quad \text{where } \mathcal{F}_k \cong \Gamma^s(L^2(\text{Block}_k \times \mathfrak{su}(N)))$$
* Scale $k$ corresponds to effective lattice cells of volume $L^{4k} a^4$.
* **Lean 4 Target File:** `BookProof/BalabanRG/MultiscaleSpace.lean`

#### 2.2. The Block-Averaging Operator
* Bałaban’s block transformation $Q$ averages gauge fields over a 4D hypercube $B_k(y)$ of size $L$:
  $$(Q A)_\mu(y) = \frac{1}{L^4} \int_{B_k(y)} A_\mu(x) \, dx + \text{gauge-connection corrections}$$
* In the wave-function parametrization, this averaging is an **isometric conditional expectation operator**:
  $$\mathbb{Q}_k : \mathcal{F}_k \to \mathcal{F}_{k+1}$$
* Prove that $\mathbb{Q}_k$ is bounded and preserves the Born probability normalization:
  ```lean
  def blockAveragingOp (k : ℕ) : ℱ k →L[ℝ] ℱ (k + 1)
  theorem blockAveragingOp_norm_le (k : ℕ) : ‖blockAveragingOp k‖ ≤ 1
  ```

#### 2.3. The State Sequence and Continuum Convergence
* The regularized state at cutoff $N$ (lattice spacing $a = L^{-N}$) is the product wave-function:
  $$\Psi_N = \left( \prod_{k=0}^{N-1} \mathbb{Q}_k \right) \Psi_{\text{bare}}$$
* Formalize Bałaban’s small-field/large-field polymer contraction as an operator Cauchy estimate:
  $$\|\Psi_{N+1} - \Psi_N\|_{\mathcal{F}_{\text{total}}} \le C \cdot L^{-\epsilon N}$$
* By completeness of the Hilbert space (`completeSpace_iff_summable_norm`) [1.1], deduce that $\Psi_N$ converges to a **unique continuum state vector $\Psi_\infty \in \mathcal{F}_{\text{total}}$**:
  ```lean
  theorem balaban_state_cauchy : CauchySeq (fun N => psiSeq N)
  theorem balaban_continuum_state_exists : ∃ (Ψ_∞ : ℱ_total), Tendsto psiSeq atTop (𝓝 Ψ_∞)
  ```

---

### Phase 3: Reflection Positivity (Osterwalder–Schrader Positivity)
**Goal:** Prove that the 4D static measure $d\mu_\infty(A) = |\Psi_\infty(A)|^2$ satisfies reflection positivity across the $x_0 = 0$ hyperplane.

#### 3.1. Euclidean Time Reflection
* Define the reflection operator $\theta$ on $\mathbb{R}^4$:
  $$\theta(x_0, x_1, x_2, x_3) = (-x_0, x_1, x_2, x_3)$$
* On the gauge connection, $\theta$ acts with the proper parity sign on the temporal component:
  $$(\theta A)_0(x) = -A_0(\theta x), \quad (\theta A)_j(x) = A_j(\theta x) \quad (j=1,2,3)$$
* Lift $\theta$ to a unitary involution $\Theta$ on $\mathcal{F}_{\text{total}}$:
  ```lean
  def timeReflection : ℱ_total →L[ℝ] ℱ_total
  theorem timeReflection_involution : timeReflection ∘L timeReflection = ContinuousLinearMap.id ℝ ℱ_total
  ```

#### 3.2. The Half-Space Observable Algebra $\mathcal{A}_+$
* Define the subalgebra $\mathcal{A}_+$ of cylindrical observables supported strictly on the positive Euclidean time half-space:
  $$\operatorname{supp}(F) \subset \{x \in \mathbb{R}^4 : x_0 > 0\}$$
* **Lean 4 Target File:** `BookProof/ReflectionPositivity/HalfSpaceAlgebra.lean`
  ```lean
  def PositiveTimeAlgebra : Subalgebra ℝ (CylindricalObservables ℱ_total)
  ```

#### 3.3. Proof of Reflection Positivity
* For the bare Wilson lattice action, reflection positivity across site/link boundaries is an established algebraic identity:
  $$\langle \theta(F) F \rangle_a \ge 0 \quad \forall F \in \mathcal{A}_{+, a}$$
* Prove that Bałaban's block-spin averaging $\mathbb{Q}_k$ commutes with time reflection:
  $$\Theta \mathbb{Q}_k = \mathbb{Q}_k \Theta$$
* Conclude that reflection positivity is preserved at every RG step $k$, and passes to the continuum limit:
  ```lean
  theorem reflection_positivity_continuum (F : PositiveTimeAlgebra) :
    0 ≤ innerProduct ℱ_total (timeReflection (observableOp F Ψ_∞)) (observableOp F Ψ_∞)
  ```

---

### Phase 4: Wick Rotation and Osterwalder–Schrader Reconstruction
**Goal:** Reconstruct the physical Minkowski Hilbert space $\mathcal{H}_{\text{Mink}}$, the vacuum state $\Omega$, and the physical Hamiltonian $H_{\text{phys}}$ directly from the reflective Euclidean state $\Psi_\infty$.

#### 4.1. Construction of the Physical Minkowski Hilbert Space
* Define the positive semi-definite form on $\mathcal{A}_+$:
  $$\langle F_1, F_2 \rangle_{\text{phys}} := \langle \Psi_\infty, \pi(\theta(F_1)^* F_2) \Psi_\infty \rangle$$
* Define the null space:
  $$\mathcal{N} = \{ F \in \mathcal{A}_+ : \langle F, F \rangle_{\text{phys}} = 0 \}$$
* Define the physical Minkowski space as the metric completion of the quotient:
  $$\mathcal{H}_{\text{Mink}} := \overline{\mathcal{A}_+ / \mathcal{N}}$$
* **Lean 4 Target File:** `BookProof/OSReconstruction/PhysicalHilbertSpace.lean`
  ```lean
  def PhysicalNullSpace : Submodule ℝ PositiveTimeAlgebra
  def PhysicalPreHilbert := PositiveTimeAlgebra ⧸ PhysicalNullSpace
  def MinkowskiHilbertSpace := UniformSpace.Completion PhysicalPreHilbert
  ```

#### 4.2. Emergence of the Physical Hamiltonian $H_{\text{phys}}$
* Notice that **no Hamiltonian was postulated in 4D Euclidean space**. The physical Hamiltonian emerges through the Euclidean time translation semigroup:
  $$T_\tau(x_0, \mathbf{x}) = (x_0 + \tau, \mathbf{x}) \quad (\tau \ge 0)$$
* For any $F \in \mathcal{A}_+$ and $\tau \ge 0$, $T_\tau F \in \mathcal{A}_+$.
* By reflection positivity and the Cauchy–Schwarz inequality, $T_\tau$ induces a symmetric, contraction semigroup on $\mathcal{H}_{\text{Mink}}$:
  $$P(\tau)[F] = [T_\tau F], \quad \|P(\tau)\| \le 1$$
* Using the Hille–Yosida theorem (or Stone's theorem for symmetric semigroups, already formalizable from `BookProof.ChapterStoneResolvent` [1.1]):
  $$P(\tau) = e^{-\tau H_{\text{phys}}}$$
* Deduce that the infinitesimal generator $H_{\text{phys}}$ is **automatically self-adjoint and positive**:
  ```lean
  theorem emergent_hamiltonian_selfAdjoint : IsSelfAdjoint H_phys
  theorem emergent_hamiltonian_nonnegative (ψ : MinkowskiHilbertSpace) :
    0 ≤ innerProduct MinkowskiHilbertSpace ψ (H_phys ψ)
  ```

---

### Phase 5: Connecting the Mass Gap
With the 4D Euclidean theory reconstructed into Minkowski spacetime, the mass gap is the spectral gap of the emergent operator $H_{\text{phys}}$:

1. **Spatial vs. Temporal Clustering:**
   Because the Euclidean theory has full $O(4)$ invariance (from Phase 1), exponential decay of Schwinger functions in the Euclidean time direction $\tau$:
   $$\langle \mathcal{O}(\tau, \mathbf{0}) \mathcal{O}(0, \mathbf{0}) \rangle - \langle \mathcal{O} \rangle^2 \le C e^{-m \tau}$$
   is strictly equivalent to exponential spatial decay at distance $r = |\mathbf{x}|$.
2. **Transfer to SIRK / Temple:**
   The emergent operator $H_{\text{phys}}$ on the reconstructed space $\mathcal{H}_{\text{Mink}}$ now serves as the input to the existing `BookProof.SirkCertifiedGap` pipeline [1.1], allowing certified interval calculation of the lowest mass $m > 0$.

---

### Lean 4 File Hierarchy for the Project

| Module Path | Primary Theorem / Definition | Proof Mechanism |
| :--- | :--- | :--- |
| `BookProof/EuclideanFock4D/CoreBasis.lean` | `EuclideanHermiteBasis4D` | 4D product Hermite functions [1.1] |
| `BookProof/EuclideanFock4D/MehlerMeasure.lean` | `mehler4D_O4_invariant` | Projective limit of Gaussians on $S^\infty$ [1.1] |
| `BookProof/BalabanRG/BlockOperator.lean` | `blockAveragingOp` | Gauge-covariant kernel on blocks |
| `BookProof/BalabanRG/Convergence.lean` | `balaban_continuum_state_exists` | Cauchy sequence in $\mathcal{F}_{\text{total}}$ via polymer bound |
| `BookProof/ReflectionPositivity/Involution.lean` | `timeReflection` | Parity lift: $A_0 \mapsto -A_0, A_j \mapsto A_j$ |
| `BookProof/ReflectionPositivity/Proof.lean` | `reflection_positivity_continuum` | $\mathbb{Q}_k \Theta = \Theta \mathbb{Q}_k$ + lattice OS identity |
| `BookProof/OSReconstruction/PhysicalSpace.lean` | `MinkowskiHilbertSpace` | Quotient by null ideal + metric completion [1.1] |
| `BookProof/OSReconstruction/Hamiltonian.lean` | `emergent_hamiltonian_selfAdjoint` | Hille–Yosida / Stone generator of time shifts [1.1] |

### Why This Research Plan Works
**Superseded rationale:** the claims in this historical subsection are objectives, not
established compatibility or existence theorems. E0–E5 state their missing inputs.

* **Eliminates the Gauge-Fixing Conflict:** Working in 4D Euclidean space avoids the temporal gauge $A_0 = 0$ (which ruins 4D Euclidean covariance) while avoiding non-local Coulomb gauges [1.1].
* **No Premature Hamiltonian:** The physical Hamiltonian $H_{\text{phys}}$ is not constructed by hand with operator ordering problems; it **emerges dynamically** from the Euclidean translation semigroup via reflection positivity.
* **Direct Compatibility with *Timepiece*:** The entire construction relies solely on objects already validated in `BookProof`: separable Hilbert spaces, the Mehler measure, Riesz–Fischer completions, and Stone's flow machinery [1.1].

---

## Implementation status (2026-10-29)

This section records what of the plan above is actually implemented in **this** repository
(`timepiece`, Lean v4.28.0), with the declaration names to read.  The module-by-module record
lives in `docs/euclidean_cft_proof.md`; this is the plan-side mirror.  `lake build BookProof`
is the verification gate; no module below contains `sorry`.

### Phase → module → declaration

| Phase | Module | Declarations | Status |
| :--- | :--- | :--- | :--- |
| 1.1 | `BookProof/EuclideanFock4D/CoreBasis.lean` | `euclideanHermiteBasis4D`, orthonormality, totality, `euclideanHermiteNet4D`, `colourBasis` | **PROVED** |
| 1.2 | `BookProof/EuclideanFock4D/MehlerMeasure.lean` | `mehlerMeasure4D := gaussianE 4`, `mehler4D_O4_invariant`, `sphereUniform4D` | **PROVED** (the measure is the 4-fold product Gaussian on the Hermite core; no projective limit is built — see Boundary) |
| 2.1 | `BookProof/BalabanRG/MultiscaleSpace.lean` | `Sector k`, `FTotal` (an `ℓ²` sum over scales), `rgOnTotal`, `rgOnTotal_norm_le`, `psiSeq` | **PROVED** |
| 2.2 | `BookProof/BalabanRG/BlockOperator.lean` | `blockConst`, `blockAveragingOp`, **`blockAveragingOp_norm_le`** (`‖Q_k‖ ≤ 1`), idempotence, image in the coarse sector | **PROVED** |
| 2.3 | `BookProof/BalabanRG/Convergence.lean` | `summable_of_increment_bound`, `psiSeq_has_limit`, `psiSeq_cauchy`, **`balaban_rg_convergence`** | **PROVED, conditional** on the geometric increment bound (Bałaban's polymer estimate) — the bound itself is the open analytic input |
| 3.1 | `BookProof/ReflectionPositivity/Involution.lean` | `timeReflection` (`θ² = 1`, coordinate formula), **`timeReflection_measure_invariant`**, `flipCell`, `fieldReflection` | **PROVED** |
| 3.1 | `BookProof/ReflectionPositivity/BlockCommute.lean` | **`blockOf_reflectCoord`**, `mem_blockConst_fieldReflectionSector`, **`theta_commutes_blockAveraging`** (`Θ Q_k = Q_k Θ`) | **PROVED** |
| 3.2 | `BookProof/ReflectionPositivity/HalfSpaceAlgebra.lean` | `PositiveTimeAlgebra`, `CylindricalObservables`, `positiveTimeAlgebra_cylindrical`, `thetaObs`, **`thetaObs_dependsOn_negTime`** | **PROVED** |
| 3.3 | `BookProof/ReflectionPositivity/Proof.lean` | `osForm`, `IsReflectionPositive`, **`reflection_positivity_continuum`**, `psiSeq_component_tendsto` | **PARTIAL**: the passage to the continuum limit from pointwise convergence is proved; the *lattice OS identity itself* is a hypothesis |
| 3.3 | `BookProof/OSReconstruction/MomentumBasis.lean` | `dft_mul_eq_convolution`, **`reflection_positivity_momentum`**, `covarianceForm_eq_dft`, `freePropagator_reflect_eq_transfer`, `freeOSForm_eq_momentum` | **PROVED** for the free field, degree one (two-point function) |
| 3.3 | `BookProof/ReflectionPositivity/FeynmanKac.lean` | `freeTransferKernel` with **`freeTransferKernel_pos`** and **`fkKernelProduct_pos`** (the pointwise positive kernel), `freeAction` with **`freeAction_cross_vanishes`** (the Markov property: no past–future coupling) and **`freeAction_reflect`**, `freeDensity_factorises`, `fkMeasure` (`= ρ ⊗ ν ⊗ ν`), `fkOSForm`, **`fk_integral_eq`** and **`fk_reflectionPositive`** | **NEW (2026-10-30)**: the Feynman–Kac route — the transfer kernel is pointwise positive, the action splits at the reflection slice, and reflection positivity of `ρ ⊗ ν ⊗ ν` holds for *every* integrable half-space observable (polynomials included), with no degree restriction. The identification of the concrete lattice Gaussian with this product form is in the row below |
| 3.3 | `BookProof/ReflectionPositivity/LatticeFreeField.lean` | `fkKernelDensity`, **`fkKernelMeasure`** (`ρ ⊗ ν_z ⊗ ν_z`, boundary-*dependent* half-space law), **`fkKernel_integral_eq`**, **`fkKernel_reflectionPositive`**, `chain`, `halfAction`, `boundaryTerm`, `latticeAction`, `latticeGFFMeasure`, **`latticeGFFMeasure_eq_fkKernelMeasure`**, **`latticeGFF_integral_eq`**, **`latticeGFF_reflectionPositive`** | **NEW (2026-10-30)**: the **identification**. The free field's half-space law depends on the boundary slice (`ν = ν_z`), which `fkMeasure` cannot express, so the FK theorem is proved in kernel form; then the concrete lattice Gaussian free field on `2n+1` slices with the nearest-neighbour action splits as `S = h(z,y₋) + h(z,y₊) + d(z)`, i.e. it *is* `ρ ⊗ ν_z ⊗ ν_z` with `ρ = exp(−d)` and `ν_z = exp(−h(z,·))`. Reflection positivity of the free field therefore holds for every half-space observable with integrable moments. Boundary: the normalising constant `Z` is not evaluated (it cancels), so no `m > 0` and no finiteness is claimed |
| 3.3 | `BookProof/ReflectionPositivity/WilsonLattice.lean` | `plaqDensity`, **`re_trace_le_card`**, `plaqDensity_nonneg`, **`plaqDensity_le_one`**, `plaqWeight`, **`plaqWeight_pos`**, **`plaqWeight_le_one`**, **`wilsonAction`**, **`wilson_mixed_difference_zero`**, **`wilson_density_factorises`**, **`wilsonAction_reflect`**, **`wilsonMeasure_eq_fkKernelMeasure`**, **`wilson_reflectionPositive`** | **NEW (2026-10-30)**: the interaction does **not** spoil the slice split. The plaquette bound `Re tr U ≤ N` (`|tr U| ≤ N` for `U` unitary, from row-orthonormality) makes every plaquette contribute `0 < weight ≤ 1`; a plaquette uses only past, only invariant, or only future links, so `S = A(z,y₋) + A(z,y₊) + b(z)` and the **mixed difference vanishes identically** — the interacting analogue of `freeAction_cross_vanishes`. Hence the Wilson measure *is* `ρ ⊗ ν_z ⊗ ν_z` with the interacting kernel `ν_z = exp(−A(z,·))`, and is reflection positive for every half-space observable with integrable moments. Boundary: the lattice geometry (which links a plaquette uses) is an input, the group measure is not modelled (a fixed reference measure, not Haar), and `Z` of the interacting measure is not evaluated |
| 3.3 | `BookProof/ReflectionPositivity/GFFNormalization.lean` | `sqSum`/`layerSq`/`latticeSq`, **`integral_exp_neg_mul_sqSum`** (`∫ exp(−c‖x‖²) = (√(π/c))^{\|S\|}`), **`integral_exp_neg_mul_layerSq`**, **`integral_exp_neg_mul_latticeSq`** (`= (√(π/c))^{(2n+1)\|S\|}`), `lintegral_exp_neg_mul_latticeSq`, **`latticeAction_ge_mass`**, **`latticeAction_le`**, `latticeGFFMass`, **`latticeGFFMass_le`**, **`latticeGFFMass_ge`**, **`latticeGFFMass_pos`**, **`latticeGFFMass_lt_top`**, `latticeGFFZ_eq_toReal`, **`latticeGFFMass_zero`**, **`latticeGFFProbability`**, **`isProbabilityMeasure_latticeGFFProbability`**, **`latticeGFFProbability_reflectionPositive`** | **NEW (2026-10-30)**: the normalising constant. The reference Gaussians are evaluated exactly, with their constants (Fubini over the sites plus `integral_gaussian`); the action is sandwiched, `(m/2)‖φ‖² ≤ S ≤ (8n + m/2)‖φ‖²`, giving `(√(π/(8n+m/2)))^{(2n+1)\|S\|} ≤ Z ≤ (√(2π/m))^{(2n+1)\|S\|}`, so **`Z` is finite and non-zero** and `latticeGFFMeasure` normalised by it **is a probability measure** (for `m > 0`), still reflection positive because a positive rescaling is. Boundary: *this* chapter proves only the sandwich; the exact closed form `(2π)^{N/2}/√det K` needs the slice recursion `μ₀ = m/2`, `μ_{j+1} = m/2 + μ_j/(1+μ_j)` and is proved in `ChainPartition` (`chainZ_closed_det` + `latticeGFFMass_eq_chainZ`, next rows). The single-slice value `Z = (2π/m)^{\|S\|/2}` is exact here (`latticeGFFMass_zero`) |
| 3.3 | `BookProof/ReflectionPositivity/WilsonLinkLattice.lean` | `Site`, `stepSite`, `Link`, `time`, `theta`, **`theta_involutive`**, **`time_theta`**, `Plaquette` with `c10`/`c01`/`c11`/`siteSet`, **`timeSet_subset`**, `IsPastSide`, `IsFutureSide`, `IsInvariant`, **`plaq_cover`**, **`plaq_classification`**, `reflectTime`, **`pastSide_image_iff`**, **`Plaquette.holonomy`**, **`Plaquette.holonomy_mem_unitaryGroup`**, `re_trace_inv_of_mem_unitaryGroup`, **`Plaquette.plaqDensity_holonomy_inv`**, `Plaquette.plaquetteWeight_holonomy_inv`, **`Plaquette.pastSide_link_time`**, **`Plaquette.futureSide_link_time`**, **`wilsonLatticeAction`**, `pastSideWeight`/`futureSideWeight`/`invariantWeight`, **`wilsonLatticeAction_split`**, **`reflectT_link0`**–**`reflectT_link3`**, **`reflectT2_link0`**–**`reflectT2_link3`**, **`reflectT_c10`/`_c01`/`_c11`**, **`reflectT2_c10`/`_c01`/`_c11`**, **`holonomy_reflectT`**, **`holonomy_reflectT2`**, **`trace_holonomy_reflectT`**, **`trace_holonomy_reflectT2`**, **`trace_holonomy_reflectPlaq`**, **`reflectPlaq_involutive`**, **`wilsonLatticeAction_reflectConfig`** | **NEW (2026-10-30, temporal cases closed 2026-10-31, action invariance 2026-10-31)**: the plaquette classification is now *derived* from an explicit lattice instead of assumed. On the `L × L × L` box with oriented links, every plaquette's time support is contained in `{t, t+1}` (`timeSet_subset`: spatial plaquettes sit at one time, temporal ones span exactly one step); consequently every plaquette is on the past side or the future side of the reflection plane (`plaq_cover`) and the two sides cover while intersecting exactly in the reflection-invariant (boundary) class (`plaq_classification`); and the reflection `t ↦ L−1−t` (an involution, `theta_involutive`, `time_theta`) carries the past side onto the future side (`pastSide_image_iff`) — the input `wilsonAction_reflect` used to take. The four links are now attached to the corner data as genuine `Link` values (`Link.ofStep`, `link0`–`link3`: `base → c10 → c11` and `base → c01 → c11`, with `link_targets`/`link_endpoints_mem` and the square closing at `stepSite_c01`). The holonomy is built from the four links (`U0·U1·U2⁻¹·U3⁻¹`), is unitary for unitary link variables, and its Wilson weight does not see the orientation of the square (`Re tr` of a unitary inverse equals `Re tr`). Past-side plaquettes use only links at time ≤ M, future-side ones only links at time ≥ M (`pastSide_link_time`/`futureSide_link_time`), and the action of the box — summed over *all* plaquettes — splits as `S = past + future − invariant` (`wilsonLatticeAction_split`), the shape `wilsonAction` takes as an input. **All three cases of the reflection are closed**: the four link identities of the reflected square are proved for the spatial case (`reflectS_link0`–`link3`, where the holonomy is *literally* equal, `holonomy_reflectS`) and for both temporal cases (`reflectT_link0`–`link3`, `reflectT2_link0`–`link3`, through the corner lemmas `reflectT_c10`/`_c01`/`_c11`, `reflectT2_c10`/`_c01`/`_c11`), where the reflected holonomy is the cyclic rotation `u₁u₂⁻¹u₃⁻¹u₀` (time first) or `u₃⁻¹u₀u₁u₂⁻¹` (time second) of `u₀u₁u₂⁻¹u₃⁻¹` — one `trace_rot_inv` / `trace_rot` from it, so the **trace identity `Re tr h_{θp} = Re tr h_p` holds in every case** (`trace_holonomy_reflectS`/`_reflectT`/`_reflectT2`, umbrella `trace_holonomy_reflectPlaq`), with the double inverse of a time link unwrapped by `inv_inv_of_mem_unitaryGroup`. The trace identity is lifted to the action: `reflectPlaq` **is an involution** of the plaquette set (`reflectPlaq_involutive`, through `eq_of_data` which reduces a plaquette equality to its base and two directions), so the sum reindexes and **`wilsonLatticeAction_reflectConfig`** gives `S(U_θ) = S(U)` exactly — the reflection invariance the reflection-positivity argument needs. Its remaining gap — identifying the past sum with a measurable function of `(z, y₋)` alone — is closed in the next row. |
| 3.3 | `BookProof/ReflectionPositivity/WilsonPastClass.lean` | **`timeSet_reflectPlaq`**, `siteSet_reflectS`/`_reflectT`/`_reflectT2`, **`IsPastSide_reflectPlaq`**, **`IsInvariant_reflectPlaq`**, **`pastSideWeight_reflectConfig`**, **`futureSideWeight_reflectConfig`**, **`invariantWeight_reflectConfig`**, **`wilsonLatticeAction_reflectConfig_of_split`**, **`measurable_of_inv_apply`**, `PastLink`/`BoundaryLink`/`PastConf`/`BoundConf`, `pastLinkVar`/`pastConfig`/`pastHolonomy`, **`measurable_pastHolonomy_apply`**, **`measurable_weight_pastConfig`**, **`pastSideObservable`**, **`measurable_pastSideObservable`**, **`pastSideWeight_eq_observable_of_eq`** | **NEW (2026-10-31)**: the concrete past-class weight, both halves of the gap recorded in `WilsonLinkLattice`. **Reflection identity.** The reflected plaquette's corner set is the `θ`-image of the original's in all three cases (spatial, time-first, time-second), so its time support is the original's under `t ↦ L−1−t` (`timeSet_reflectPlaq`); with the middle reflection plane `L = 2M+1` the reflection therefore carries the past side onto the future side (`IsPastSide_reflectPlaq`) and preserves the invariant slice (`IsInvariant_reflectPlaq`). Reindexing the sum by the involution `reflectPlaq` and using the trace identity gives **`pastSideWeight β N (reflectConfig U) M = futureSideWeight β N U M`**, with the future (`reflectConfig_involutive`) and invariant companions, and — assembled through `wilsonLatticeAction_split` — `S(U_θ) = S(U)` as an identity between the three class sums (`wilsonLatticeAction_reflectConfig_of_split`), matching the unconditional `wilsonLatticeAction_reflectConfig`. **Measurability packaging.** The half-space configuration space is explicit: past links (time ≤ M), boundary links (time = M), with the link variable `pastLinkVar` reading the past configuration below the slice and the boundary one in it. The entries of `A ↦ A⁻¹` are measurable from `A⁻¹ = det A⁻¹ • adjugate A` (`measurable_of_inv_apply`) — *not* from continuity of the inverse, which fails at singular matrices — and the past-class holonomy's entries are assembled by `measurable_entry_mul` rather than `fun_prop`, so no measurable structure on `Matrix` is needed. The past-class sum is then the measurable function `pastSideObservable` of `(y, z)` (**`measurable_pastSideObservable`**), identified with `pastSideWeight` of any configuration agreeing below the slice (`pastSideWeight_eq_observable_of_eq`) — the `hmeas` input of `wilson_reflectionPositive`. Boundary: the reference measure is instantiated as Haar measure in `HaarReference` (see the next row); gauge invariance is not used, and `Z` is not evaluated |
| 3.3 | `BookProof/ReflectionPositivity/ChainPartition.lean` | `sliceFactor`, `chainForm`, `chainZ`, **`chainForm_cons`**, **`chainForm_linear`**, **`lintegral_exp_neg_mul_sqSum`**, **`lintegral_exp_neg_slice_step`**, **`chainZ_succ`**, `effSeq`, **`effSeq_shift`**, **`chainZ_closed`**, **`chainZ_closed_half`**, `halfAction_split`, **`chainForm_chain`**, **`latticeAction_chain`**, **`lintegral_fkKernel_eq_chainZ`**, `chainMatrix`, **`chainMatrix_zero`**, **`chainMatrix_one`**, **`det_corner_schur`**, **`chainMatrix_succ_det`**, **`chainMatrix_det`**, **`chainMatrix_det_half`**, **`chainZ_closed_det`**, **`chainForm_symm`**, **`chainForm_symm_rev`**, `foldIdx`, **`foldChainEquiv`**, **`volume_preserving_foldChainEquiv`**, **`sum_foldChain_sqSum`**, **`foldChainEquiv_past_chain`**, **`foldChainEquiv_future_chain`**, **`sum_foldChain_diffSq`**, **`latticeAction_eq_chainForm`**, **`latticeGFFMass_eq_chainZ`** | **NEW (2026-10-30, determinant closed 2026-10-31, lattice relabelling closed 2026-10-31)**: the effective-mass recursion itself. The one-slice Gaussian identity (`integral_exp_neg_slice_step`, from `GFFNormalization` §5) is iterated along a chain of `N+1` slices in `ℝ≥0∞` (Tonelli, so no integrability is assumed), giving the recursion `Z_{N+1}(c) = (√(π/(1+c)))^{\|S\|} · Z_N(m/2 + δ(c))` with `δ(c) = c/(1+c)`, and its closed form `Z_N(c) = (∏_{j<N}(√(π/(1+c_j)))^{\|S\|})·(√(π/c_N))^{\|S\|}`, `c₀ = c`, `c_{j+1} = m/2 + δ(c_j)`; with `c = m/2` the `c_j` are exactly `effMass m j`, i.e. `μ₀ = m/2`, `μ_{j+1} = m/2 + μ_j/(1+μ_j)`. The two translations around that recursion are now proved: at the level of measures, `∫⁻ (z,y), ρ(z)·ν_z(y) = chainZ m (m/2) n` (**`lintegral_fkKernel_eq_chainZ`**), and at the level of the operator, the tridiagonal determinant identity `det (chainMatrix m c N) = ∏_{j<N}(1 + c_j)·c_N` (**`chainMatrix_det`**, `= ∏(1+μ_j)μ_N` in **`chainMatrix_det_half`**), by block elimination at the `1 × 1` corner (**`det_corner_schur`**, the Schur complement of the outermost slice) plus induction. **The lattice itself is now a chain**: `foldChainEquiv` presents the `2n+1` slices as a chain (past half backwards, reflection slice, future half; measure preserving by **`volume_preserving_foldChainEquiv`**), the **mass** term matches (**`sum_foldChain_sqSum`**) and so do the **links** (`foldChainEquiv_past_chain`/`_future_chain` slice the two halves, **`sum_foldChain_diffSq`** matches the `2n` links), whence the lattice action *is* the chain form of the folded slices (**`latticeAction_eq_chainForm`**) and **`latticeGFFMass m n = chainZ m (m/2) (2n)`** (**`latticeGFFMass_eq_chainZ`**) — the whole-lattice partition function in closed form, `Z = π^{(2n+1)\|S\|/2}/(det K_{2n})^{\|S\|/2}`. Boundary: this is the *free* (Gaussian) action; the interacting Wilson measure is not relabelled this way, since its density does not factorise along the links |
| 3.3 | `BookProof/ReflectionPositivity/WilsonPartition.lean` | **`plaqDensity_le_two`**, **`wilsonHalfAction_le`**, **`wilsonAction_nonneg`**, **`wilsonAction_le`**, `exp_neg_wilsonAction_le_one`, **`wilsonMass`**, **`wilsonMass_le`**, **`wilsonMass_ge`**, **`wilsonMass_eq_top`**, **`wilsonMass_pos_of_univ_eq_one`**, **`wilsonProbability`**, **`isProbabilityMeasure_wilsonProbability`**, **`wilsonProbability_reflectionPositive`** | **NEW (2026-10-30)**: the interacting partition function. The plaquette density lies in `[0,2]` (`\|Re tr U\| ≤ \|tr U\| ≤ N`), so the action is *bounded*, `0 ≤ S ≤ 4β#P + sup b`, and the Boltzmann weight is squeezed uniformly, `exp(−(4β#P + M)) ≤ exp(−S) ≤ 1`. Hence `Z` is a multiple of the reference volume: `exp(−(4β#P+M))·μ(univ) ≤ Z ≤ μ(univ)`. Against Lebesgue that forces `Z = ⊤` (**`wilsonMass_eq_top`**) — a bounded interaction cannot damp an infinite reference measure, so the model *needs* the finite Haar measure of the compact gauge group; with a normalised reference measure (`μ(univ) = 1`) the same bound gives `0 < Z ≤ 1` and `Z⁻¹ • wilsonMeasure` **is a probability measure**, still reflection positive. Boundary: Haar itself is not constructed and `β, N, P, U` are fixed |
| 3.3 | `BookProof/ReflectionPositivity/QuadraticWick.lean` | `osQuadForm`, `kern`, **`pairing_swap`**, **`osQuadForm_eq_two_mul_kern`**, `kern_transfer`, **`osQuadForm_eq_two_sum_sq`**, **`osQuadForm_nonneg`** | **NEW (2026-10-30)**: the degree-two lift — the Isserlis sum of a quadratic half-space observable equals `2 Σ_{y x} w_x w_y (Σ a_{i j} u_{x i} u_{y j})²`, and is nonnegative for `w ≥ 0`. Degrees ≥ 3 are obstructed (see item 2 below) |
| 3.3 | `BookProof/ReflectionPositivity/HalfSpaceSplit.lean` | `PosTime`/`NegTime`, `negToPos`, `configSplitFun`/`configJoinFun`, **`configSplit`** (`Config ≃ (PosTime → ℝ) × (PosTime → ℝ)`), `configJoin_split`/`configSplit_join`, **`configSplit_fieldReflection`**, **`thetaObs_split`**, **`osForm_split`**, **`osForm_liftHalf_eq`**, **`isReflectionPositive_of_fkOS`**, **`measurable_configSplitFun`**, `splitMap`, **`integral_splitMap`**, **`osForm_eq_integral_splitMap`**, **`isReflectionPositive_of_splitIntegral`**, **`measurable_mk_unit`**, **`mk_unit_snd_eq_id`**, **`map_snd_map_mk`**, **`integral_snd_fkKernel`**, **`isReflectionPositive_of_fkKernelMeasure`**, **`isReflectionPositive_of_wilsonKernelMeasure`** | **NEW (2026-11-04)**: the half-space splitting of the *index set*, so the lattice OS theorems land on the observables `reflection_positivity_continuum` quantifies over. `cellsPerBlock = 16` is even, hence `isPosTime i = (coordOf i).2.val < 8` has no fixed point and every component lies in exactly one half; reading the past half through `θ` indexes both factors by the future half, so the reflection becomes the plain swap `((cs x).2, (cs x).1)` (`configSplit_fieldReflection`) — the same shape as `reflectConf`. Then `ω(θF·F)` for a future-half observable is `ω(fkOSForm f)` in split coordinates, and after pushing the measure (`splitMap ω = ω.map configSplit`) it is the product-model integral `∫ fkOSForm f ∂(splitMap ω)`; `isReflectionPositive_of_splitIntegral` therefore discharges `hRP` from exactly the conclusion of `fkKernel_reflectionPositive`/`wilson_reflectionPositive`. **The identification of `splitMap ω` with the lattice kernel measures is the second half of the row.**  The boundary factor is trivial (`PUnit`, because the reflection has no fixed point), so the index arithmetic `PosTime × PosTime ≃ Z₀ × (Y × Y)` collapses: `map_snd_map_mk` shows that reading the kernel measure on its future half and re-inserting the trivial boundary returns the same measure, `integral_snd_fkKernel` identifies the split-coordinate OS integral with `∫ fkOSForm f ∂(fkKernelMeasure ρd νd)`, and **`isReflectionPositive_of_fkKernelMeasure`** concludes `hRP` from `fkKernel_reflectionPositive` — no hypothesis on the OS form, only measurability of the density and integrability of the OS integrand.  The Wilson case is the same statement with the interacting weights through `wilsonMeasure_eq_fkKernelMeasure` (**`isReflectionPositive_of_wilsonKernelMeasure`**).  Boundary: what is still not constructed is the measure `ω` *itself* on `Config` whose split is that kernel law, and the odd-slice geometry in which the boundary carries a non-trivial law; the reflection has no fixed point here |
| 3.3 | `BookProof/OSReconstruction/ReflectionKernel.lean` | `IsReflectionPositiveOn`, `isReflectionPositiveOn_of_factorization`, `osBilin_sub_theta_self_eq_zero`, **`mk_thetaObs_eq_mk`** | **PROVED**: explains why the hypothesis must be the half-space one. The factorisation route is the uncorrelated (white-noise) case only |
| 4.1 | `BookProof/OSReconstruction/PhysicalSpace.lean` | `osForm` bilinearity, `osForm_expand`, **`osForm_cauchy_schwarz`**, `Radical`, **`osForm_well_defined`**, `osNorm_triangle` | **PROVED** |
| 4.1 | `BookProof/OSReconstruction/HilbertSpace.lean` | `physForm`, **`physCore`**, **`physInnerProductSpace`**, **`Hphys`** (`UniformSpace.Completion`), `physNorm_mk`, `physNorm_eq_zero_iff` | **PROVED** (`Hphys` is the plan's `MinkowskiHilbertSpace`; the plan's `PhysicalNullSpace` is `Radical Λ.ω`) |
| 4.2 | `BookProof/OSReconstruction/Hamiltonian.lean` | `TimeTranslation`, `timeTranslation_semigroup`, **`osNorm_evolution_antitone`**, `radical_invariant`, `timeEvolution_well_defined` | **PROVED** (contractive semigroup part) |
| 4.2 | `BookProof/OSReconstruction/HilbertSpace.lean` | `physEvol`, **`physEvol_contractive`**, `physEvol_zero`, `physEvol_add`, `physEvolCompletion`, **`norm_physEvolCompletion_le`**, **`physEvolCompletion_zero`**, **`physEvolCompletion_add`** | **PROVED** (contractive extension to `Hphys`, and — 2026-11-04 — the semigroup law on it: `P(0) = 1` and `P(s+t) = P(s)∘P(t)` by density of `𝔄/𝔑`, from `timeTranslation_zero` / `timeTranslation_semigroup` through the quotient) |
| 4.2 | — | `emergent_hamiltonian_selfAdjoint`, `emergent_hamiltonian_nonnegative` | **NOT CLAIMED** — but the *reason* has changed, so the row reads: Stone theory is now proved in this repository in both directions (`ChapterStoneResolvent` → `ChapterStoneTheorem`, converse `WeakMeasurableUnitaryGroup.gen_stoneU_eq`), so "Mathlib has no spectral theorem" is no longer accurate. What is missing is the **converse for contraction semigroups** (Lumer–Phillips/Hille–Yosida: symmetric + strongly continuous + contractive ⇒ self-adjoint generator), plus complexification and separability of the real space `Hphys`. Feasibility written up in open item 4 above. The positivity *content* that is proved remains `osNorm_evolution_antitone` |
| 5 | `BookProof/Sirk/ChapterRitzCertificate.lean` | `rayleigh`, `resid`, `SpectralSeparation`, **`temple_lower_bound`**, `temple_band_mem`, `fock_mass_gap_of_temple_certificates` | **PROVED** (the SIRK/Temple receiver) |
| 5 | `BookProof/OSReconstruction/Clustering.lean` | `schwinger`, `connectedCorr`, `SchwingerClustering`, **`schwinger_symm`**, **`osNorm_evol_le_of_clustering`**, `osNorm_evol_iterate_le`, `cluster_decay_tendsto_zero`, **`eNorm_timePoint_eq_spacePoint`**, **`spatial_decay_of_temporal`**, **`osBilin_le_mul_osNorm`**, `osNorm_sub_le`, **`osNorm_sub_evol_ge`**, `genForm`, `one_sub_exp_neg_ge`, **`genForm_ge_of_contraction`**, **`genForm_gap_of_clustering`** | **NEW (2026-10-30)**: Euclidean clustering at mass `m` ⇔ decay of the transfer operator at rate `m` off the vacuum; `O(4)` time→space transfer; and the *separation*: the norm gap `1 − √C e^{−mτ}` of `I − T_τ` and the form gap `m(1 − ε)` of the effective generator `(I − T_τ)/τ`. The clustering bound itself is the hypothesis (see Boundary) |
| 5 (Temple feed) | `BookProof/Sirk/ChapterTempleContinuumGap.lean` | **`gapAt_of_separation`**, `gapAt_of_form_domination`, **`gap_survives_norm_limit`**, `notMem_spectrum_of_separation_limit`, `continuum_gap_of_form_domination` | **NEW (2026-10-30)**: the plan's `SpectralSeparation` becomes a quantitative `GapAt` at the window centre and survives an operator-norm limit, leaving a `c₁Δ_ref/2` hole in the limit's spectrum |
| 4.1′ | `BookProof/OSReconstruction/GaussianMoments.lean` | `productGauss`, **`isserlis_productGauss`**, `integral_prod_coord_productGauss`, `integral_pow_gaussianReal_one_moment` | **NEW (2026-10-29)**: the Gaussian/Wick step the corpus previously lacked — standard covariance only |
| 3.3 + 4.1 (bridge) | `BookProof/OSReconstruction/YangMillsBridge.lean` | `loopProd`, **`thetaObs_loopProd`**, **`osBilin_gram`**, `osBilin_gram_nonneg`, **`complex_sum_quadform`**, **`isReflectionPositive_yangMills`**, `isReflectionPositiveOn_loopProd` | **NEW (2026-10-29)**: the dictionary between the platform's `YangMills.IsReflectionPositive` on correlation functionals of dyadic loops and the state-level `IsReflectionPositiveOn PositiveTimeAlgebra` — the loop observables and their positivity are hypotheses, the equivalence of the two statements is proved |

### Boundary (recorded, never assumed)

* **Phase 2.3**: `balaban_rg_convergence` is the implication *increment bound ⟹ limit*. The
  geometric bound `‖Ψ_{N+1} − Ψ_N‖ ≤ C L^{-εN}` for the actual block operators is Bałaban's
  hard estimate and is not proved (nor is gauge-connection covariance of `Q_k` beyond the
  block-constant model).
* **Phase 3.3**: the lattice Wilson OS identity `⟨θ(F) F⟩_a ≥ 0` for the interacting measure is
  a hypothesis (`IsReflectionPositive`).  For observables supported on one half its *coordinate*
  content is no longer assumed (2026-11-04, `HalfSpaceSplit`): the split of the index set, the
  intertwining `configSplit ∘ θ = swap ∘ configSplit`, and the identity between `osForm` and the
  product-model integral in split coordinates (`osForm_eq_integral_splitMap`, with the
  pushed-forward measure `splitMap ω`, up to the ae-strong-measurability side condition that the
  lattice theorems' `Integrable` hypotheses supply) are proved, so
  `isReflectionPositive_of_splitIntegral`
  reduces the hypothesis to precisely what `fkKernel_reflectionPositive` and
  `wilson_reflectionPositive` prove.  **The identification is proved too** (§6 of the same file):
  the boundary factor is `PUnit`, and `splitMap ω = (fkKernelMeasure ρd νd).map Prod.snd` *is* the
  hypothesis of `isReflectionPositive_of_fkKernelMeasure`, which returns `hRP` from
  `fkKernel_reflectionPositive` alone; the Wilson weights are the same statement via
  `wilsonMeasure_eq_fkKernelMeasure`.  What remained was the construction of the measure itself,
  and a first case is now in place (§7 of the same file, 2026-11-05): `gffConfigMeasure m` is the
  Gibbs measure of the mass (ultralocal) action `S(x) = (m/2) Σ_i (x i)²` on `Config`, written as
  a density against Lebesgue measure on `Config`; `configAction_eq_split` proves `S` separable
  across the halves with the *same* half action on both, Lebesgue measure on `Config` is proved
  invariant under the split (`measurePreserving_configSplitEquiv`), and
  **`splitMap_gffConfigMeasure`** identifies the split law as the product `ν ⊗ ν` of the same
  half-space Gibbs density — the kernel law with a trivial boundary factor.  Two things were still
  open: rewriting that product into the exact `(fkKernelMeasure (Z₀ := PUnit) …).map Prod.snd`
  shape §6 consumes (bookkeeping over the trivial base measure), and the coupled
  case — a nearest-neighbour action does *not* split this way, its cross-plane edge couples the
  halves, which is why the free-field theorem uses the `2n+1`-slice model with a boundary slice
  where the boundary carries a non-trivial law.  The first is now closed (§8 of the same file,
  2026-11-14; see the landing above): the OS form of the mass model on `Config` is nonnegative for
  every future-half observable, with no hypothesis on the state.  What is proved is its
  preservation under limit
  (`reflection_positivity_continuum`), the momentum-space form for a free field — degree one in
  `MomentumBasis`, degree two in `QuadraticWick`, and  all degrees in `FeynmanKac` *given* the Markov/product structure of the measure — **that
  structure holding for the concrete lattice free field in the kernel form `ρ ⊗ ν_z ⊗ ν_z`
  (`LatticeFreeField`) and, given the plaquette link classification, for the interacting Wilson
  measure too (`WilsonLattice`)**, and that the full-algebra strengthening would trivialise the
  reflection (`mk_thetaObs_eq_mk`).  What remains an input for the interacting measure is the
  lattice geometry (which links each plaquette uses) and the group measure (a fixed reference
  measure stands in for Haar); the normalisation of the free measure is settled in
  `GFFNormalization` (a probability measure for `m > 0`), the closed-form partition function and
  the interacting normalisation are not.
* **Phase 1.2 / Fock**: `ℱ_k` is modelled by its one-particle content; the `S^∞` projective
  limit and the scale measures `dγ_k` are not built (`dγ₀ = mehlerMeasure4D` only).
* **Phase 4.2**: the emergent generator is not constructed; no self-adjointness or
  nonnegativity of `H_phys` is claimed (see the row above).
* **Phase 5**: the *equivalence machinery* is now proved in `OSReconstruction.Clustering` —
  clustering at mass `m` gives `‖T_τ F‖ ≤ √C e^{−mτ}‖F‖` off the vacuum, iterates to
  `(√C e^{−mτ})^n`, and `O(4)` invariance transfers temporal decay at `(τ,0,0,0)` to spatial
  decay at `(0,r,0,0)` at the same rate.  The step *from* that decay *to* a spectral separation is
  also proved (2026-10-30), on the bounded side: `osNorm_sub_evol_ge` (the gap of `I − T_τ` at fixed
  `τ`) and `genForm_ge_of_contraction` / `genForm_gap_of_clustering` (the form gap `m(1 − ε)` of the
  effective generator `(I − T_τ)/τ`, with `τ → 0` recovering `m`).  What is **not** proved is the
  clustering bound itself (Bałaban's infrared analysis) and the identification of the rate with the
  bottom of the spectrum of the *unbounded* `H_phys`.  Note that the spectral theorem is *not* a missing ingredient: it
  is in this repository (`ChapterSpectralMultiplication`, `ChapterSpectralDirectSum`,
  `ChapterUnboundedSpectralModel`, `ChapterStoneConverse`) and in `physlib/`
  (`SelfAdjointSpectralTheorem.lean`, `CayleySpectralData/SpecTheorem.lean`).  On the bounded
  side, `BookProof/Sirk/ChapterTempleContinuumGap.lean` turns a spectral separation into a
  quantitative gap and carries it across an operator-norm limit; `softmodes.md` Phase 5.2's
  certificate arithmetic (`continuum_gap_unconditional`) is in
  `BookProof/Sirk/ChapterTempleSeparationBound.lean`.

### Current plan / todo list for the contents of this file

Ordered by what unblocks the rest; each item names the module it lands in.

1. **Wick/Isserlis, general covariance** (`BookProof/OSReconstruction/GaussianMoments.lean`) —
   **DONE**: `isserlis_gaussLaw` and `isserlis_multivariateGaussian` prove exactly the pairing
   form `E[∏_k X(p k)] = ∑_{σ ∈ pairings (2m)} ∏_{k < σ k} C (p k) (p σ k)` for a Gaussian of
   covariance `A Aᵀ`, resp. `K ⪰ 0` (see that module's header and `Boundary`).  Kept here for the
   record of the route, which is what item 2 consumes.
   Extend `isserlis_productGauss` from the standard measure (covariance `δ`) to a field
   `X p = Σ_a v a p * y a` with covariance `C p q = Σ_a v a p * v a q`, giving
   `E[∏_k X(p k)] = Σ_{pairings σ} ∏_{pairs {a,b}} C (p a) (p b)`. Two steps: the linear-image
   moment formula (multinomial expansion + the coordinate factorisation already proved), then
   the invariant-theoretic double count. The combinatorics to port are in
   `../physlib/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean`
   (`involutionNoFixedZeroEquivProd`, `involutionNoFixed_card_mul_two : card = (2n−1)‼`) and
   `../physlib/Physlib/QFT/PerturbationTheory/WickContraction/Card.lean` (`cardFun`,
   `card_eq_cardFun`); the Lean versions differ (physlib is v4.35), so this is a port.
2. **Phase 3.3, the RP lift** — **degrees 1 and 2 done; from degree 3 the Isserlis route is
   obstructed, and the obstruction is structural rather than a matter of labour.**  Checked on
   2026-10-30; the route specified for this item (expand, apply Isserlis, match the transfer form)
   is carried out as far as it goes, and where it stops is now a theorem, not an estimate.
   * Degree 1 *is* the transfer form: `freeOSForm_eq_momentum` (with
     `freePropagator_reflect_eq_transfer`, `transferForm_eq`) is exactly "Isserlis sum = Källén–Lehmann
     modulus squares" for a smeared **linear** field.
   * **Degree 2 is now proved** — `BookProof/ReflectionPositivity/QuadraticWick.lean`.  For a
     quadratic half-space observable `F = Σ_{i j} a_{i j} φ_i φ_j` (symmetric `a`) and reflected
     covariance `K_{i k} = ω(φ(θi) φ_k)`, the Isserlis sum is the two pairings
     `Σ a_{i j} a_{k l} (K_{i k}K_{j l} + K_{i l}K_{j k})` (`osQuadForm`).  `pairing_swap` merges
     them (the relabelling `k ↔ l`), `osQuadForm_eq_two_mul_kern` collapses them to
     `2 Σ_{i j} a_{i j}(KAK)_{i j}`, and for a covariance in transfer form
     `K_{i j} = Σ_x w_x u_{x i}u_{x j}`,
     **`osQuadForm_eq_two_sum_sq`** gives
     `ω(θF·F) = 2 Σ_{x y} w_x w_y (Σ_{i j} a_{i j} u_{x i} u_{y j})²`, with **`osQuadForm_nonneg`**
     the `w ≥ 0` positivity.  This is the degree-two match of `transferForm_eq`, but note its
     *form*: the weight multiplies the **square of the bilinear pairing of two modes**, not a single
     `|Σ_p F p u_a p|²`.  The degree-1 statement is the diagonal `x = y` picture; it does not lift
     verbatim, and this is the correct degree-2 statement instead.
   * **Correction (2026-11-08): the following obstruction claim is superseded.**
     Its example fails linear RP already; with a reflection-positive Gaussian covariance,
     an all-degree Wick/chaos proof remains possible. See the revised correction above.
     Historical claim: **from degree 3 the Wick route fails, and cannot be repaired.**
     At degree `2m` the same
     substitution gives products of `m` pairings with no collapse into one square, and positivity
     genuinely fails for a `θ`-invariant Gaussian: on the odd subspace, where the reflection acts
     as `φ(θp) = −φ(p)` and the covariance is `θ`-invariant by construction, the cubic half-space
     monomial `F = φ(p)³` satisfies `θF = −F`, hence `ω(θF·F) = −ω(F²) < 0`.  So
     `IsReflectionPositiveOn PositiveTimeAlgebra ω` is **false** for a θ-invariant free measure in
     general, and no Isserlis/Wick manipulation can prove it.  (Earlier notes put this threshold at
     degree 2; `QuadraticWick` shows degree 2 is in fact positive for symmetric `a` and symmetric
     `K`, so the correction is that the counterexample lives at degree 3 and above.)
   * **The Feynman–Kac structure is now built** — `BookProof/ReflectionPositivity/FeynmanKac.lean`.
     The three inputs the free measure actually uses, none of which is Wick's theorem:
     - the **pointwise positive transfer kernel**: `freeTransferKernel lam z z'` is the Gaussian
       weight `exp(-(lam/2) Σ_i (z' i - z i)²)` of one Euclidean time step, with
       **`freeTransferKernel_pos`** (`0 < K`) and **`fkKernelProduct_pos`** (`0 <` the `n`-step
       product) — positivity of the kernel, not just of the operator;
     - the **Markov property**: `freeAction` is the action `Σ_{i j} φ i A i j φ j`, and
       **`freeAction_cross_vanishes`** shows that block-tridiagonality (no past–future entry in
       the precision matrix) kills every term pairing a past with a future coordinate — so the
       Gibbs weight factorises (`freeDensity_factorises`) and the two half-spaces are
       conditionally independent given the boundary slice;
     - **reflection invariance**: `freeAction_reflect` — the action is symmetric, so the past and
       future conditional laws agree, which is what makes the OS form a *single* square rather
       than a product of two different integrals.
     From these, **`fk_integral_eq`** is the Feynman–Kac identity for the measure
     `fkMeasure ρ ν = ρ ⊗ ν ⊗ ν`: `∫ θF·F d(ρ ⊗ ν ⊗ ν) = ∫ z, (∫ y, F z y ∂ν)² ∂ρ`, and
     **`fk_reflectionPositive`** is its nonnegativity.  That holds for **every** measurable
     half-space observable with integrable moments — every polynomial half-space observable whose
     Gaussian moments are finite — so the degree restriction of `QuadraticWick` is exactly what
     the Markov structure removes.
   * **The identification is now done** — `BookProof.ReflectionPositivity.LatticeFreeField`.  The
     half-space law of the free field depends on the boundary (`ν = ν_z`, a kernel rather than a
     fixed measure), so the FK theorem is restated in kernel form (`fkKernelMeasure ρd νd`, the
     measure with density `ρd z · νd z y₋ · νd z y₊`) with its own Fubini identity
     `fkKernel_integral_eq` and positivity `fkKernel_reflectionPositive`.  The concrete lattice
     Gaussian free field on `2n+1` slices (`latticeGFFMeasure`) satisfies the density identity
     `exp(−S) = exp(−d) · exp(−h(z,y₋)) · exp(−h(z,y₊))` — `fkKernelDensity_lattice`, the Markov
     property in density form, with the *same* half-action on both sides — whence
     **`latticeGFFMeasure_eq_fkKernelMeasure`** and **`latticeGFF_reflectionPositive`**.

     Two of the three follow-ups named here are now closed.  The **interacting Wilson measure**
     does satisfy the same kernel form — not because the quartic term factorises like a Gaussian,
     but because a plaquette can use only past, only invariant or only future links, so the
     mixed difference of the action vanishes identically (`wilson_mixed_difference_zero`) and
     `wilsonMeasure_eq_fkKernelMeasure`, `wilson_reflectionPositive` follow from the plaquette
     bound `Re tr U ≤ N`; and the **normalising constant** of the free field is now pinned:
     `(√(π/(8n+m/2)))^{(2n+1)|S|} ≤ Z ≤ (√(2π/m))^{(2n+1)|S|}`, so `Z ∈ (0,∞)` and
     `latticeGFFProbability` is a probability measure (`GFFNormalization`), and the
     effective-mass recursion `μ₀ = m/2`, `μ_{j+1} = m/2 + μ_j/(1+μ_j)` is now *carried out* along
     a chain of slices (`ChainPartition`: `chainZ_succ`, `chainZ_closed`, `chainZ_closed_half`).
     Both translations around that recursion are now proved: `∫⁻ (z,y), ρ(z)ν_z(y) =
     chainZ m (m/2) n` (`lintegral_fkKernel_eq_chainZ`) and `det K_N = ∏_{j<N}(1 + c_j)·c_N`
     (`chainMatrix_det`, `chainMatrix_det_half`), the latter through the block elimination
     `det_corner_schur` and the peeling step `chainMatrix_succ_det`.  Combining them gives the
     textbook closed form for a chain of `N+1` slices,
     `Z_N = π^{(N+1)|S|/2}/(det K_N)^{|S|/2}` (`chainZ_closed_det`, i.e.
     `(2π)^{(N+1)|S|/2}/√det K` for the standard operator `K = 2·chainMatrix`).  The relabelling
     of the whole `2n+1`-slice `latticeGFFMass` as such a chain is proved as well
     (`latticeGFFMass_eq_chainZ`, through the measure-preserving `foldChainEquiv` and the mass and
     link sums `sum_foldChain_sqSum` / `sum_foldChain_diffSq`), so the free-field partition
     function is closed: `Z = π^{(2n+1)|S|/2}/(det K_{2n})^{|S|/2}`.  Still open: the normalising
     constant of the *interacting* measure.

   Consequence for this file's status table: the `3.3` free-field row now reads "degrees 1 and 2
   proved, higher degrees not", and `isReflectionPositiveOn_of_factorization` stays the
   *uncorrelated* (white-noise) case it says it is.  The hyperlink between the two is the
   independence hypothesis, not a theorem about correlated Gaussians.
3. **Phase 3.3, the interacting identity** (`BookProof/ReflectionPositivity/LatticeOS.lean`).
   The Wilson lattice OS identity for `ω_a(F) = ∫ F dμ_a` on the block-constant algebra, plus
   its preservation under `Q_k` (the commutation `theta_commutes_blockAveraging` is already
   proved). This is the hypothesis `reflection_positivity_continuum` consumes.

   **Feasibility check (2026-11-01).**  The mathematics of this item is done; what is missing is
   an identification between two *different* modelings of "configuration space" that the
   development never made.

   *What is proved.*  Both lattice reflection-positivity theorems exist and are `sorry`-free:
   `latticeGFF_reflectionPositive` (the free field, `GFFNormalization`) and
   `wilson_reflectionPositive` (the interacting Wilson plaquette action).  The second is proved
   from exactly two facts — every plaquette weight is positive (`Re tr U ≤ N`,
   `re_trace_le_card`) and the plaquettes classify into past / invariant / future
   (`wilson_mixed_difference_zero`) — so the measure is `ρ ⊗ ν_z ⊗ ν_z` with a positive kernel
   (`wilsonMeasure_eq_fkKernelMeasure`) and `fkKernel_reflectionPositive` applies.  The `Q_k`
   side of the item is closed as well: `theta_commutes_blockAveraging` is proved
   (`ReflectionPositivity.BlockCommute`).  And the limit passage the item exists to feed,
   `reflection_positivity_continuum`, is proved in `ReflectionPositivity/Proof.lean`.

   *What is missing, precisely.*  `reflection_positivity_continuum` consumes states
   `ω : Observable → ℝ` where `Observable = Config → ℝ`, `Config = Fin latticeDim → ℝ`, with
   `thetaObs F x = F (fieldReflection x)` and `fieldReflection x i = x (reflectCoord i)`.  The
   two lattice theorems, by contrast, are stated on the *product* configuration spaces
   `Z₀ × (Y × Y)` (free) and `Gz × (Gy × Gy)` (Wilson), with the reflection
   `reflectConf γ = (γ.1, (γ.2.2, γ.2.1))` swapping the two half-space factors and leaving the
   boundary factor alone.  Turning `latticeGFF_reflectionPositive` /
   `wilson_reflectionPositive` into the hypothesis `hRP : ∀ N F, 0 ≤ osForm (ω N) F F` therefore
   requires an equivalence `Config ≃ Z₀ × (Y × Y)` (resp. `Gz × (Gy × Gy)`) intertwining
   `fieldReflection` with `reflectConf`, i.e. the lattice-geometry statement that the component
   index splits as *boundary × past-half × future-half* with `reflectCoord` acting as the flip
   on the last two factors.  Nothing in `BalabanRG.MultiscaleSpace` provides that split:
   `coordOf` exposes only the *cell* of a component (`μ`, cell), which is exactly enough for
   `blockOf_reflectCoord` (block stability) and not enough for a half-space factorisation.
   `wilson_reflectionPositive` also carries an integrability hypothesis against *Lebesgue
   volume* on `Gz × (Gy × Gy)`, which the `Config` model does not equip with a measure at all.

   *Consequence.*  `LatticeOS.lean` should not be written as if the OS identity were a Lean
   bookkeeping gap: the identity is a theorem in the product model, and the remaining work is a
   modelling choice (fix the half-space splitting of `Fin latticeDim`, transport the two
   theorems along it, and equip `Config` with the transported measure).  Until that choice is
   made, `reflection_positivity_continuum` keeps `hRP` as a hypothesis — which is the honest
   status, since the RP of the lattice measure *is* the nontrivial theorem of the subject and
   the file that proves it (`WilsonLattice.lean`) proves it in its own model.
4. **Phase 4.2, the generator** (`BookProof/OSReconstruction/Hamiltonian.lean`). From
   `physEvolCompletion` (a *contractive one-parameter semigroup* on the complete space `Hphys` —
   the semigroup law itself is now proved, 2026-11-04: `physEvol_zero` / `physEvol_add` on the
   quotient and `physEvolCompletion_zero` / `physEvolCompletion_add` on `Hphys`, so what stays a
   hypothesis is only strong continuity at `0`, since an arbitrary `TimeTranslation` need not be
   continuous) invoke the Stone/Lumer–Phillips machinery in
   `BookProof/Toolbox/ChapterStoneResolvent.lean` (`UnboundedSelfAdjoint`, `ofBounded`,
   `trotterKato_tendsto`) to obtain `H_phys`, `IsSelfAdjoint H_phys`, `H_phys ≥ 0`.

   **Feasibility check (2026-11-01).**  Two things about this item have changed, in opposite
   directions.

   *The stated blocker is half outdated.*  The reason `Hamiltonian.lean` gives for not claiming
   these theorems is that "(ii)–(iii) [the spectral theorem and Stone/Lumer–Phillips theory do]
   not exist in Mathlib".  Stone's theorem now exists *in this repository*, in full generality
   and `sorry`-free, in both directions: `ChapterStoneResolvent` (resolvents of an unbounded
   self-adjoint `T`, `shift_bijective`, `resCLM`, `‖(A − il)⁻¹‖ ≤ 1/|l|`) →
   `ChapterStoneEvolution`/`ChapterStoneGenerator`/`ChapterStoneUnitary` (the Yosida group
   `stoneU`, strongly continuous and unitary) → `ChapterStoneConverse` (the converse:
   `WeakMeasurableUnitaryGroup.gen_stoneU_eq`) → `ChapterStoneTheorem` (`stone_bijection`), with
   `ChapterStoneBridge` packaging the predicate form.  The non-negative side is there too:
   `ChapterNonnegResolvent` → `ChapterNonnegUnitaryGroup` (`e^{-itT}`) → `ChapterNonnegSemigroup`
   (the heat semigroup `e^{-tT}`), and `ChapterNumericalRangeSemigroup` has the half-plane
   estimate (`NumReLE`, `norm_exp_le_one` = the contraction bound, `norm_resolvent_le` = the
   Hille–Yosida resolvent bound).  So an outdated "no Stone theory" should not be left as the
   recorded reason.

   *What still blocks it.*  Three things, none of them bookkeeping.

   1. **`Hphys` has no topology.**  `OSReconstruction/HilbertSpace.lean`'s physical space is a
      bare `HilbertSpace`-bundled object; the operator it carries is a map into `Hphys` rather
      than a densely defined operator on a complex Hilbert space, so it cannot be fed to
      `UnboundedSelfAdjoint` (which needs a `Submodule ℂ H` domain, `IsSymmetricOn`,
      `IsSelfAdjointOn`).  A Hilbert-space structure with the OS inner product, plus a dense
      domain, would have to be built first.
   2. **No strong continuity.**  `TimeTranslation` is a group of *linear maps on the
      observables* with no continuity hypothesis whatsoever; `physEvolCompletion` therefore
      takes `IsContractive` as a hypothesis, and `ChapterStoneConverse` needs a *weakly
      measurable* one-parameter group (`WeakMeasurableUnitaryGroup`) in the first place.  An
      arbitrary `TimeTranslation` is none of these.  The plan says as much: strong continuity
      is "currently a hypothesis since an arbitrary `TimeTranslation` need not be continuous".
   3. **`H ≥ 0` needs more than contractivity.**  `ChapterNumericalRangeSemigroup`'s
      `norm_exp_le_one` gives `‖e^{-tT}‖ ≤ 1`, i.e. accretivity of the generator.  Nonnegativity
      of the *Hamiltonian* in the OS sense is the positivity of the transfer matrix, and in this
      development that input is `osNorm_evolution_antitone` / `radical_invariant` in
      `Hamiltonian.lean` — already proved, but at the level of the OS seminorm on observables,
      not as `H ≥ 0` on a self-adjoint operator, and bridging the two needs (1) and (2).

   So the honest reading of this item is: the *machinery* is complete and `sorry`-free; the
   gap is that the OS side never produced the analytic objects (a topological physical space, a
      strongly continuous contraction group on it) that the machinery consumes.  Those are
   modelling/analysis tasks on `OSReconstruction/HilbertSpace.lean`, not steps in a proof
   that can be filled from what is here.

   *The actual gap is narrower but real, and it is the wrong direction of the theorem.*  Every
   one of those modules runs **from** a self-adjoint `T` **to** the group or semigroup.  Item 4
   needs the converse **from** `physEvolCompletion` **to** `H_phys`, and there the repo has only
   the *unitary group* converse (`gen_stoneU_eq`).  `physEvolCompletion` is neither:

   * it is a **contraction semigroup on `τ ≥ 0`**, not a unitary group — `gen_stoneU_eq` does not
     apply to it, and the converse for contraction semigroups (Lumer–Phillips / Hille–Yosida:
     symmetric + strongly continuous + contractive ⇒ self-adjoint generator) is not in the
     repository.  `norm_exp_le_one` and `norm_resolvent_le` run in the other direction again
     (bounded generator ⇒ bounds), so they do not substitute for it;
   * `Hphys` is a **real** Hilbert space (`physInnerProductSpace` is an
     `InnerProductSpace ℝ (PhysSpace Λ)`, completed from `Submodule ℝ Observable`), while all of
     the above is over `InnerProductSpace ℂ H`.  No complexification of `Hphys` exists in the
     corpus;
   * `gen_stoneU_eq` additionally needs `TopologicalSpace.SeparableSpace H`, not established for
     `Hphys`;
   * symmetry of the evolution and strong continuity at `0` are still hypotheses, as the plan
     already says.

   So the work item 4 still needs, stated precisely: (a) complexify `Hphys` (or run a
   real-Hilbert-space Stone analogue); (b) prove symmetry of `physEvolCompletion` from OS
   positivity and record strong continuity; (c) supply the contraction-semigroup converse, or
   extend the evolution to a unitary group so that the existing `gen_stoneU_eq` applies.  (c) is
   the missing theorem; (a)–(b) are scaffolding.  Until (c) exists, `emergent_hamiltonian_
   selfAdjoint` and `emergent_hamiltonian_nonnegative` cannot be claimed, and the boundary
   `Hamiltonian.lean` records stays correct — but for *this* reason, not for "Mathlib lacks the
   spectral theorem".
5. **Phase 2.3, the polymer bound** (`BookProof/BalabanRG/Convergence.lean`). Supply the
   increment estimate for the concrete `Q_k` of `BlockOperator.lean`, which is what
   `balaban_rg_convergence` consumes.

   **Done (2026-11-01), in the only form this model permits — and the reason is worth stating.**
   The estimate is supplied, with explicit constants, but its proof is a fact about the *model*
   rather than a proof of Balaban's bound.

   The modelled `Q_k` is `blockConst.starProjection` at every scale, so it is idempotent:
   **`blockAveraging_idempotent`** (`BlockOperator.lean`), from
   `starProjection_eq_self_iff` applied to `blockAveragingOp_mem`.  The recursion
   `Ψ_{N+1} = Q_N Ψ_N` acts componentwise at each scale as `(Q_k)^N`, which is `Q_k` for every
   `N ≥ 1` — **`psiSeq_component_eq`**, `Ψ_{n+1} k = Q_k(ψ₀ k)` — hence
   **`psiSeq_succ_eq_of_idempotent`**: `Ψ_{N+2} = Ψ_{N+1}`, the iteration stabilises after a
   single step.  The increment hypothesis then reads off directly
   (**`psiSeq_increment_bound_of_idempotent`**):

   `‖Ψ_{N+1} − Ψ_N‖ ≤ ‖ψ₀ − Q ψ₀‖ · r^N`  for any `0 ≤ r`,

   with the `N = 0` term the whole of it and every later term zero.  Feeding that into
   `balaban_rg_convergence` gives **`balaban_rg_convergence_blockAveraging`**: for the concrete
   `Q_k`, with `C = ‖ψ₀ − Q ψ₀‖` and `r = 1/2`, `∃ Ψ_∞, Tendsto Ψ_N atTop (𝓝 Ψ_∞)` — the
   convergence of Phase 2.3 is now a theorem about `FTotal`, not an assumption.

   **What it does not say.**  In Balaban's construction the coarse graining genuinely loses
   degrees of freedom at each step (the block lattice is smaller than the fine one), so `Q_k` is
   *not* idempotent and the geometric `C L^{−εN}` decay is analytic — that is the polymer bound.
   In `MultiscaleSpace` every sector carries the same carrier `EuclideanSpace ℝ (Fin latticeDim)`
   by design (see its module docstring, which records why: `Q_k` has to be a map *between*
   sectors that can be iterated inside `F_total`), and that is exactly what makes `Q_k` a
   projection.  So the plan's genuinely geometric content stays the input its boundary names;
   what is added is that for the operator the corpus actually defines, the hypothesis degenerates
   to a single-step estimate and nothing further is needed.  A `Q_k` that carried scale
   information (a genuinely dimension-dependent sector carrier, with transport of norms along
   `dimBlock k → dimBlock (k+1)`) would make this item non-trivial, and is the modelling change
   it would take.
6. **Phase 5, clustering ⇒ mass gap** (`BookProof/OSReconstruction/Clustering.lean`) — *formulated
   and half-proved (2026-10-30).*  `SchwingerClustering ω T m C` is the plan's decay bound, and
   `osNorm_evol_le_of_clustering` / `osNorm_evol_iterate_le` derive from it the operator decay
   `‖T_τ F‖ ≤ √C e^{−mτ}‖F‖` off the vacuum at every iterate; `spatial_decay_of_temporal` is the   `O(4)` step.  **(ii) is now done in bounded form (2026-10-30):** `osNorm_sub_evol_ge` turns the
   contraction into the norm gap `‖(I − T_τ) F‖ ≥ (1 − √C e^{−mτ}) ‖F‖` at every fixed `τ`, and
   `genForm` / **`genForm_ge_of_contraction`** / **`genForm_gap_of_clustering`** turn it into the
   form gap of the *generator*: for every `ε ∈ (0,1)` there is `τ > 0` with
   `m(1 − ε)‖F‖² ≤ (‖F‖² − ⟨F, T_τ F⟩)/τ` off the vacuum (`one_sub_exp_neg_ge` is the elementary
   `1 − e^{−x} ≥ x/(1+x)` behind the `τ → 0` limit).  So the clustering rate `m` *is* the bottom of
   the emergent generator's form spectrum, in the only form the corpus can state it — the operator
   `H_phys` itself is not constructed, so the separation is stated for `(I − T_τ)/τ`.
   Remaining: (i) the decay bound for the actual Bałaban measure, (ii′) the identification of the
   bounded separation with a `SpectralSeparation` of the *unbounded* generator, (iii) the
   Temple feed, whose arithmetic is done in `ChapterTempleSeparationBound.continuum_gap_unconditional`
   with `c₁ Δ_ref` from `softmodes.md`.

   **Correction (2026-11-08):** this paragraph's claim that the physical separation constant
   is established is superseded by softmodes S0–S2. Its comparison thresholds do not
   identify actual spectral levels; the concrete form, sector and margin remain inputs.
   The newer multiplier/operator results also supersede generic absence claims below.

   **Historical (iii) assessment — 2026-11-04.** `softmodes.md` Phase 4 now certifies
   `c₁ Δ_ref` on the `L²` form of record (`closed_yangMillsGap`) *and*, for an off-diagonal
   interaction, on the core (`hopping_farisLavine`), so the constant is no longer the obstruction.
   What `continuum_gap_unconditional` consumes is different in kind: its hypothesis is
   `SpectralSeparation A l b`, i.e. `l ≤ b ∧ ∀ t ∈ spectrum ℝ A, t = l ∨ b ≤ t` for a **bounded
   self-adjoint operator** `A`, while the certificate is about a **quadratic form** on `ℓ²`.  Two
   things are therefore missing, and neither is arithmetic: the operator `A` on `L²` whose
   Rayleigh form is `closedForm (yangMillsSymbol) x` (the diagonal multiplication operator, which
   is bounded only when the symbol is), and the identification
   `spectrum ℝ A = closure (range (symbol))` for that operator, from which a *spectral* gap off the
   vacuum would follow.  Mathlib has no spectrum computation for diagonal operators on `ℓ²`, and a
   form gap does not imply a spectral one without the spectral measure — the form gap holds on the
   vacuum-orthogonal sector, where Rayleigh quotients of *mixtures* `Ω + e` can still take any
   intermediate value.  So item (iii) is blocked on the same operator⇄form bridge as (ii′), and
   `ChapterTempleSeparationBound`'s honest boundary ("the transfer across the strong-resolvent
   limit is not proved") should be read as covering this too.

**Landed 2026-11-16, thirteenth slice: the two-point functions, and the renormalised variance
(C3f).** The twelfth slice computed the moments of `streamField` but had to say that the variance of
the *renormalised* observable `renormField = streamField − c^n·d·p_last` was out of reach, because
it needs the cross moment `E[S · p_last]`. That moment is now computed. Twelve declarations were
added to the audit; all rest on standard axioms.

* **Coordinates.** `integral_shellLaw_coord` and `integral_shellLaw_coord_sq`: a single coordinate
  has mean `0` and second moment `1` under the reference law, with `integrable_shellLaw_coord`
  and `integrable_shellLaw_coord_sq` supplying the integrability. Both come from Mathlib's
  `integral_comp_eval` (`∫ f (x i) ∂Measure.pi μ = ∫ f ∂μ i`) and the one-dimensional moment
  `∫ z² ∂blockUnit = 1`.
* **The cross moment.** `integral_shellLaw_streamField_mul_last`: `E[S_n · p_last] = c^n·d`.
  Proved by induction on the number of scales, splitting the product law at the first coordinate
  (`integral_shellLaw_cons_succ`, which is stated for *integrable* functions — this is the Fubini
  step the density tower deliberately avoided). The newly integrated coordinate `z` multiplies
  `g_last`, whose mean is zero, so each step only reads off its own drift. Integrability of the
  product is `integrable_streamField_mul_last`, dominated by `(S² + p_last²)/2`.
* **Decorrelation.** `integral_shellLaw_renormField_mul_last = 0`: the drift the renormalisation
  subtracts is *exactly* the field's correlation with the exterior coordinate. Consequently
  `integral_shellLaw_renormField_sq = K_n` and its mean-subtracted form
  `integral_shellLaw_renormField_centered_sq = K_n`; with `c² < 1` the variance is at most
  `1/(1 − c²)` uniformly in `n` (`variance_renormField_le`). `covariance_pair_shellLaw` packages the
  `2×2` covariance matrix of `(streamField, p_last)` with its diagonal and off-diagonal.

Boundary of this thirteenth slice: **the pair, and only the pair.** The two-point function is
computed for the field against a single coordinate, including the drift coordinate it is
renormalised against; the interior cross moments `E[p_i·p_j]` for two coordinates, the covariance
`E[S_n · S_m]` between two different scales, and the four-point function are not computed, so no
cluster expansion, no second-moment matrix in the multi-scale sense and no Gaussianity statement
follows. The renormalisation is still the subtraction of the damped background read off the
exterior coordinate, not a renormalisation of an interacting observable. No conditional
expectation is constructed (the per-`y` identity stays bounded-only), and C3a–C3d, the half-space
inequality, the OS reconstruction theorem and any field law are untouched.

**Landed 2026-11-16, fourteenth slice: the interior cross moments and the second-moment calculus
(C3g).** The thirteenth slice computed the two-point function of the field against a single
coordinate, but only for the exterior one, and said so. The interior pairings are now proved and the
whole second-moment calculus of linear statistics follows. Eight declarations were added to the
audit; all rest on standard axioms.

* **The interior cross moments.** `integral_shellLaw_coord_mul_coord`: `E[p_i·p_j] = 1` when
  `i = j` and `0` otherwise, with `integrable_shellLaw_coord_mul` supplying integrability by
  domination with `(p_i² + p_j²)/2`. The proof splits the product law at the first coordinate and
  runs four explicit cases through `Fin.cases`: the newest coordinate multiplies itself (one unit of
  variance), a distinct new coordinate (zero mean), or two older coordinates (the induction
  hypothesis).
* **The coefficient vector.** `streamCoeff c d n` is `c^j` on the interior coordinates and `c^n·d`
  on the exterior one, and `streamField_eq_sum_coeff` proves the field *is* that linear statistic.
  The induction rewrites the recursion as `coeff_{n+1}(j.succ) = c · coeff_n(j)` plus
  `coeff_{n+1}(0) = 1`.
* **The kernel.** `integral_shellLaw_linear_mul_coord` (a statistic against a coordinate),
  `integral_shellLaw_linear_mul_linear` (two statistics against each other: the inner product of
  their coefficient vectors) and `integral_shellLaw_streamField_mul_linear` (the field against an
  arbitrary statistic). Every two-point function of a linear statistic — the field, the
  renormalised field, affine images — is now an inner product rather than an estimate.

Boundary of this fourteenth slice: **still no three- or four-point function and no cross-scale
pairing.** The kernel is a bilinear form on coefficient vectors, so it says nothing about
`E[p_i·p_j·p_k·p_l]`, which needs the pairings (i,j)(k,l), (i,k)(j,l), (i,l)(j,k) and hence a
four-index induction this slice does not do; it also says nothing about `E[S_n · S_m]` for
`m ≠ n`, because the smaller field must first be transported into the `n`-scale space along
`Fin.castLE` and the resulting inner product is a different sum. Gaussianity is still not proved —
a complete two-point kernel is necessary but not sufficient for it — and there is no conditional
expectation, no multi-point cluster estimate, and no change to C3a–C3d, the half-space inequality,
the OS reconstruction theorem or any field law.

**Landed 2026-11-26, fifteenth slice: the cross-scale covariance and the factorization of every
coordinate moment (C3h).** The fourteenth slice left two items open and named both. This slice
closes the cross-scale one and, in doing so, replaces the induction route to multi-point functions
with a one-line factorization, which changes what the four-point function now costs. Six
declarations were added to the audit; all rest on standard axioms.

* **The cross-scale covariance.** `integral_shellLaw_streamField_mul_smaller`: for `m < n`,
  `E[S_n · S_m] = K_m + c^(2m)·d`, where the smaller field is read in the `n`-scale space through
  `Fin.castLE`. The route is three new pieces — `truncCoeff` lifts a coefficient vector along the
  inclusion and reads the extra coordinates with weight `0`, `sum_truncCoeff_mul` proves the lifted
  pairing is the small-space pairing (a filtered-`Finset` argument, not a new induction), and
  `sum_streamCoeff_mul_pow` evaluates the resulting pairing against the powers `c^j` as
  `K_m + c^(2m)·d`. With `integral_shellLaw_streamField_mul_coord` (the field against one
  coordinate is that coordinate's coefficient) the kernel is now closed under inclusion.
* **The exponent.** The correct answer is *not* `K_m + (c^m d)²`, the smaller field's own second
  moment. Its exterior coefficient `c^m·d` meets the larger field's *interior* coefficient `c^m`,
  because in the larger space coordinate `m` is no longer the exterior one. The correction is the
  drift the larger field assigns to a coordinate the smaller one treats as background, so
  cross-scale covariance is a property of the trajectory and not of either field alone. This is the
  formula the previous slice's boundary paragraph anticipated in the wrong exponent; the Lean
  statement is the one above.
* **Every coordinate moment at once.** `integral_shellLaw_prod_coord_pow`:
  `∫ ∏ i, (p i)^(e i) = ∏ i, ∫ z, z^(e i)`, by a single application of
  `integral_fintype_prod_eq_prod` to the product law. No induction over the number of coordinates,
  no truncation, no domination. This is a stronger standard than the pair-restricted kernel: every
  coordinate moment of the reference law is now a product of one-dimensional moments.

Boundary of this fifteenth slice: **the `δ`-form of the four-point function is not a Lean
statement.** The factorization gives it as `∏ i, ∫ z^(e i)` for the exponent vector supported on
the four indices, and evaluating that product to
`δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk` is arithmetic on the multiplicity pattern —
`(1,1,1,1) → 0`, `(2,2) → 1`, `(2,1,1) → 0`, `(3,1) → 0`, `(4) → 3`. What is missing is the case
analysis over the six equalities among `i, j, k, l` that turns the one into the other, and while it
is elementary it is not yet done. There is also still no three-point function as a Lean statement,
no Gaussianity proof (the factorization is consistent with it but does not assert it), no
conditional expectation, no multi-point cluster estimate, and no change to C3a–C3d, the half-space
inequality, the OS reconstruction theorem or any field law.

**Landed 2026-11-27, sixteenth slice: the three- and four-point functions of the reference law
(C3i).** The fifteenth slice left one item open and named it: the factorization gives the
four-point function as a product of one-dimensional moments, but the `δ`-form was arithmetic on
the multiplicity pattern and needed a case analysis over the six equalities among `i, j, k, l`.
This slice closes it — and the case analysis is not needed, because the pattern can be read
through the *pairings* instead of through the multiplicities. Eleven declarations were added to the
audit; all rest on standard axioms.

* **The bridge.** `shellLaw_eq_productGauss`: `shellLaw m` *is*
  `productGauss (Fin m) = Measure.pi (fun _ ↦ gaussianReal 0 1)`, by `rfl`. The reference law is
  therefore exactly the product Gaussian whose moments `GaussianMoments` computes, and Isserlis'
  theorem there applies at the level of sites rather than coordinate exponents.
* **The factorization, indexed by sites.** `integral_shellLaw_prod_coord`: for any
  `f : Fin M → Fin m`, `∫ p, ∏ t, p (f t) = ∏ a, ∫ z, z^(#{t | f t = a})`.
  This is the site-indexed form of
  `integral_shellLaw_prod_coord_pow` (an exponent vector is a multiplicity vector), and it is the
  "factorization lemma" the rest of the slice is a corollary of.
* **The four-point function.** `integral_shellLaw_coord_four`:
  `E[p_i p_j p_k p_l] = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`. The route is two steps, neither of
  which looks at the equalities among the four indices. First
  `wickSum_identity_eq_prod_doubleFactorial` identifies the multiplicity product with the weighted
  pairing sum — this is the only place the factorization is used. Then `Fin 4` has exactly three
  pairings, so the pairing sum is three terms: `pairingSet_four` lists them (`(0 1)(2 3)`,
  `(0 2)(1 3)`, `(0 3)(1 2)` as `pairingSwap01/02/03`, checked by `decide`), `pairingProd01/02/03`
  evaluate each filtered product to one contraction, and `wickSum_four` sums them. Substituting
  `f = ![i, j, k, l]` turns the three contractions into `δ_ij δ_kl`, `δ_ik δ_jl`, `δ_il δ_jk`.
* **The three-point function.** `integral_shellLaw_coord_three`:
  `E[p_i p_j p_k] = 0`. Three sites cannot all occur an even number of times: their multiplicities
  sum to `3` (`exists_odd_card_fiber_three`, by `Finset.sum_fiberwise` and the fact that a sum of
  evens is even), so one factor of the multiplicity product is an odd power of a centred Gaussian,
  and `integral_pow_odd_blockUnit` — the odd half of `integral_pow_gaussianReal_one_moment` — makes
  that factor zero, whence `Finset.prod_eq_zero`.

Boundary of this sixteenth slice: **these are the moments of this law, not a characterization of
it.** `integral_shellLaw_coord_four` is Isserlis for the covariance `1`: nothing here shows that a
law with these three- and four-point functions is Gaussian (the converse is false without extra
hypotheses), no cumulant, connected correlation or clustered moment is computed, and no moment
above the fourth exists as a Lean statement — a five-point function, or the general-`M` Wick
recursion on `shellLaw` itself, is not proved (the general recursion stays in `GaussianMoments`,
on `productGauss`). The multiplicity evaluations run through `decide` on the concrete index types
`Fin 3` and `Fin 4`; no uniform-in-`M` combinatorial statement is extracted. There is still no
conditional expectation, no multi-point cluster estimate, no limiting law, and no change to
C3a–C3d, the half-space inequality, the OS reconstruction theorem or any field law.

**Verification.** `lake env lean BookProof/OSReconstruction/GaussianChainScales.lean` is clean and
`lake build BookProof.OSReconstruction.GaussianChainScales` succeeds (8028 jobs).
`lake build BookProof` currently stops in `BookProof.Qym.ChapterYangMillsPacketCharge` (two
`unsolved goals`, at `BookProof/Qym/ChapterYangMillsPacketCharge.lean:272` and `:315`), a module
last touched by commit `6a5ab20` and unrelated to this slice, so the whole-library gate did not run
to completion on this tree; the Gaussian chain module and the audit are independent of it.
`lake env lean Work/EuclideanMomentAudit.lean` reports `[propext, Classical.choice, Quot.sound]` for
all eleven new declarations (304 rows in the ledger). `./patches/build-book.sh` under
`nix-shell -p python3` renders the book and asserts `OK: no <base>; fragment links present`.

**Landed 2026-11-27, seventeenth slice: the five- and six-point functions, uniformly in the
number of fields (C3j).** The sixteenth slice closed the `δ`-form of the four-point function but
named three things as still open: a five-point function, a moment above the fourth, and the
general-`M` Wick recursion "on `shellLaw` itself" (it lived only in `GaussianMoments`, on
`productGauss`). This slice closes all three in one step, because the right object is not the
five-point or the six-point function but the moment at an *arbitrary* tuple of sites. Twenty-three
declarations were added to the audit; all rest on standard axioms.

* **The uniform statement, first.** `integral_shellLaw_prod_coord_eq_wickSum`: for every
  `f : Fin M → Fin m`,
  `∫ p, ∏ t, p (f t) = wickSum (fun a b ↦ if f a = f b then 1 else 0) univ`.
  The multiplicity product of `integral_shellLaw_prod_coord` is turned into the pairing sum by
  `wickSum_identity_eq_prod_doubleFactorial` in one rewrite; `M` is a parameter, so the theorem is
  uniform in the number of fields and neither the five-point nor the six-point case is a separate
  computation.
* **Both parities, from the pairing set.** `integral_shellLaw_prod_coord_odd`
  (`f : Fin (2k+1) → Fin m`) is zero because `pairingSet_univ_odd` says the pairing set of an odd
  number of sites is empty, and `integral_shellLaw_prod_coord_even` (`f : Fin (2k) → Fin m`) is the
  sum over `pairings (2k)` because `pairingSet_univ_even` says the pairing set is the full one. Both
  are the same one-line rewriting of the uniform Wick form; neither re-proves a moment.
* **The five-point function.** `integral_shellLaw_coord_five`:
  `E[p_i p_j p_k p_l p_r] = 0`. It is the odd case at `k = 2` after `Fin.prod_univ_five` reads
  `p_i p_j p_k p_l p_r` as `∏ t, p (![i, j, k, l, r] t)`. No parity argument over multiplicities is
  repeated: the vanishing is the emptiness of the pairing set.
* **The six-point function.** `integral_shellLaw_coord_six`:
  `E[p_i p_j p_k p_l p_r p_s] = δ_ij δ_kl δ_rs + … (fifteen terms)`. It is the even case at
  `k = 3`. The pairings of six sites are the fifteen perfect matchings of `{0, …, 5}` — `5 · 3 · 1`
  — and the slice uses the same route as at four sites: `pairingSet_six` lists the fifteen
  permutations (`pairingSix01` … `pairingSix15`, products of three disjoint swaps, checked by
  `decide`), `pairingSet_six_card` records the count `15`, `pairingProdSix01` … `pairingProdSix15`
  evaluate each filtered product to its three contractions, `wickSum_six` sums the fifteen terms,
  and substituting `f = ![i, j, k, l, r, s]` turns each contraction into a `δ`. The orientation
  filter `{a | a < σ a}` is the one used at four sites.
* **Reference cross-check.** The two QYM developments were consulted for the convention in which a
  pairing is a perfect matching and each pair is oriented by its smaller member:
  `../OpenAI-YM-20261028/YM/Push/STRESS_FLUX/Pairing.lean` proves its two-point contractions by
  summing over matchings of `Occ` oriented by `corners`, and
  `../OpenAI-YM-20261104/lean/YM/Maxwell/Wick.lean` gives the general `Matching`/`corners`/`graph`
  presentation, `∑ over matchings of ∏ over corners`. This slice's `pairingSet`/`filter (a < σ a)`
  is the same shape, and the fifteen-term sum is the `n = 6` instance of it. Those developments do
  not contain a Gaussian-moment theorem, so nothing is imported or reused from them; the reference
  is for the matching convention, not for a proof.

Boundary of this seventeenth slice: **the moments are still those of the reference law, and the
uniformity stops where the combinatorics is evaluated.** The odd/even and pairing-sum statements
are uniform in `M`, but the per-pairing evaluation at four and six sites is a finite `decide`
computation on `Fin 4` and `Fin 6`; no closed form for the number of pairings at arbitrary `M`
(e.g. `(M-1)‼` on `shellLaw`) is derived, and no `M`-uniform algorithm for the `δ`-form is
extracted. The six-point display is fifteen explicit contractions rather than a single indexed
formula. There is still no cumulant, connected correlation, clustered moment, or Gaussianity
criterion: Isserlis for covariance `1` computes the moments of *this* product law and says nothing
about a law merely having them, and no interacting-theory statement follows. C3a–C3d, the
half-space inequality, the OS reconstruction theorem and every field law are unchanged.

**Verification.** `lake env lean BookProof/OSReconstruction/GaussianChainScales.lean` is clean and
`lake build BookProof.OSReconstruction.GaussianChainScales` succeeds (8028 jobs).
`lake env lean Work/EuclideanMomentAudit.lean` reports `[propext, Classical.choice, Quot.sound]` for
all twenty-three new declarations (327 rows in the ledger). `./patches/build-book.sh` under
`nix-shell -p python3` renders the book and asserts `OK: no <base>; fragment links present`.

**Landed 2026-11-27, eighteenth slice: the connected four-point function vanishes (C3k).** The
seventeenth slice ended by naming the cumulants as still open: "no cumulant, connected correlation
or clustered moment". This slice computes the fourth joint cumulant of the reference law — the
first cumulant above the two-point function — and proves it zero. Twelve declarations were added
to the audit; all rest on standard axioms.

* **The cumulant, by its partition formula.** `connectedFour` is the fourth joint cumulant as the
  Möbius sum over the partitions of the four positions: `m₁₂₃₄`, minus the three partitions into
  two pairs, minus the four partitions into a singleton and a triple, plus twice the six
  partitions into a pair and two singletons, minus six times the four singletons — the
  coefficients `(−1)^(k−1)(k−1)!` of a partition into `k` blocks. This is the four-point analogue
  of `connectedThree` in the QYM development
  (`../OpenAI-YM-20261104/lean/MSPositionLabels.lean`), and `../QCD` carries the frozen reference
  copy of the same development (`provenance/supplied-comparator/frozen/reference/YM/...`); that
  development defines the three-point cumulant by exactly this inclusion–exclusion, and the
  definition here follows it rather than inventing a convention. Neither development states a
  Gaussian cumulant theorem, so nothing is imported or reused.
* **The face functional and the centring.** `shellFace m f s = ∫ p, ∏ t ∈ s, p (f t)` is the
  joint moment of the positions in `s`, with `shellFace_empty` (the empty product integrates to
  one) and `shellFace_singleton` (a single coordinate has mean zero, `integral_shellLaw_coord`).
  The cumulant of the law is `connectedFourShell m f = connectedFour (shellFace m f)`.
* **The derivation.** `connectedFourShell_eq` evaluates the singleton terms to zero and
  `connectedFourShell_eq_pair` states the result in moment language:
  `κ = m₁₂₃₄ − m₁₂ m₃₄ − m₁₃ m₂₄ − m₁₄ m₂₃`. Only the partition into two pairs survives, because
  every other partition has a singleton block and the law is centred. `connectedFour_coord_eq`
  reads the same identity at four coordinates.
* **The vanishing.** `connectedFourShell_eq_zero` (and `connectedFour_coord_eq_zero`) substitute
  the Isserlis forms: the four-point function is δ₁₂δ₃₄ + δ₁₃δ₂₄ + δ₁₄δ₂₃ and each pair moment is
  a δ, so the cumulant is `(δδ + δδ + δδ) − δδ − δδ − δδ`, which `ring` closes to `0`. The
  reference law has no connected four-point part.

Boundary of this eighteenth slice: **one cumulant of one law, and its vanishing is not a
Gaussianity criterion.** The computation shows that *this* product law has zero fourth cumulant —
the property every Gaussian has — but not that a law with vanishing fourth cumulant is Gaussian,
and no converse is attempted. No cumulant above the fourth is defined, no connected correlation at
separated points is computed, and no clustering estimate follows: the vanishing is the algebraic
cancellation of Isserlis pairings, not a decay statement. The cumulant is defined by its explicit
fifteen-term partition formula on `Fin 4`, not by a general moment–cumulant transform, and no
partition-lattice machinery is built. Everything remains a statement about the reference law;
C3a–C3d, the half-space inequality, the OS reconstruction theorem and every field law are
unchanged.

**Verification.** `lake env lean BookProof/OSReconstruction/GaussianChainScales.lean` is clean and
`lake build BookProof.OSReconstruction.GaussianChainScales` succeeds (8028 jobs).
`lake env lean Work/EuclideanMomentAudit.lean` reports `[propext, Classical.choice, Quot.sound]` for
all twelve new declarations (339 rows in the ledger). `./patches/build-book.sh` under
`nix-shell -p python3` renders the book and asserts `OK: no <base>; fragment links present`.

**Status (2026-11-27): pairing-count recursion (C3j).**
`BookProof/OSReconstruction/ChapterPairingCount.lean` specializes the existing `wickSum_rec`
bijection to the constant weight one: `wickSum_one_eq_card` identifies the Wick sum with
`(pairingSet s).card`, and `card_pairingSet_rec` counts pairings by the partner of the least site
and the pairings of the remaining sites. Strong induction on the cardinality then gives the
closed form: `card_pairingSet_eq_doubleFactorial` states `card (pairingSet s) = (s.card−1)‼` for
even `s.card` (odd sets have no pairings, by `Equiv.Perm.two_dvd_card_support`), and
`card_pairings_even` specializes to `card (pairings (2m)) = (2m−1)‼`;
`pairingSet_six_card_closed` cross-checks the explicit six-site enumeration against the closed
form (15).  This closes the counting
item from the seventeenth slice; an `M`-uniform δ-algorithm on `shellLaw` is still open.

**Verification note (2026-11-27).** `lake build BookProof` is green at 9127 jobs after repairing
two elaboration failures in `BookProof/Qym/ChapterYangMillsPacketCharge.lean` (commit `6e62952`),
and `scripts/health.sh` reports 3 pass, 0 warn, 0 fail after registering the `ChapterPairingCount`
and `ChapterYangMillsGaussRotationFlow` roots.

**Landed 2026-11-27, nineteenth slice: the connected five-point function vanishes (C3l).** The
eighteenth slice computed the fourth cumulant and recorded "no cumulant above the fourth" as open.
This slice computes the fifth joint cumulant of the same reference law — again by the Möbius
partition formula — and proves it zero. Twelve declarations were added to the audit; all rest on
standard axioms.

* **The cumulant, by its partition formula.** `connectedFive` is the fifth joint cumulant as the
  Möbius sum over all fifty-two partitions of the five positions (`Bell 5 = 52`), with the same
  coefficient `(−1)^(k−1)(k−1)!` per partition into `k` blocks: one partition into one block,
  fifteen into two (five singleton + quadruple, ten pair + triple), twenty-five into three, ten
  into four, and one into five singletons. `connectedFive_one` checks the list: with every face
  equal to one the sum is `1 − 15 + 50 − 60 + 24 = 0`, the partition-lattice identity
  `Σ_π μ(π, ⊤) = 0` that has to hold for `n ≥ 2`.
* **The structural vanishing condition.** `shellFace5 m f s = ∫ p, ∏ t ∈ s, p (f t)` is the joint
  moment of the positions in `s`, with `shellFace5_singleton` giving the centred one-point
  function. `connectedFive_eq_zero` states the criterion on the face alone: if every face of
  cardinality one and of cardinality three is zero, and the full face is zero, then the Möbius sum
  is zero. That is the whole content of the odd case — on five positions every partition has a
  block of one, three or five elements, so every product in the sum carries a zero factor.
* **The three block lemmas.** `shellFace5_card_one` (the centred law), `shellFace5_card_three`
  (from `integral_shellLaw_coord_three`, after reading a three-element block as three
  coordinates) and `shellFace5_univ_eq_zero` (from `integral_shellLaw_coord_five`, via
  `shellFace5_univ`). No reduction to pair moments is needed: the odd blocks vanish on their own.
* **The vanishing.** `connectedFiveShell_eq_zero` instantiates the structural lemma at
  `connectedFive (shellFace5 m f)`, and `connectedFive_coord_eq_zero` reads it at five
  coordinates. The reference law has no connected five-point part.

Boundary of this nineteenth slice: **one more cumulant, still only odd-block vanishing.** The
cumulant is defined by its explicit fifty-two-term partition formula on `Fin 5`, not by a general
moment–cumulant transform, and no partition-lattice machinery is built. No cumulant of arbitrary
order is defined; in particular the even case is untouched, where the surviving partitions at six
points (`6`, `4+2`, `2+2+2`) have non-vanishing Möbius coefficients and a genuine Isserlis
cancellation would have to be computed rather than an odd block observed. No separated connected
correlation and no clustering estimate is derived: the vanishing here is algebraic, not decay. It
is still not a Gaussianity criterion — vanishing fourth and fifth cumulants do not make a law
Gaussian, and no converse is attempted. Everything remains a statement about the reference law;
C3a–C3d, the half-space inequality, the OS reconstruction theorem and every field law are
unchanged.

**Verification.** `lake env lean BookProof/OSReconstruction/GaussianChainScales.lean` is clean and
`lake build BookProof.OSReconstruction.GaussianChainScales` succeeds (8028 jobs).
`lake env lean Work/EuclideanMomentAudit.lean` reports `[propext, Classical.choice, Quot.sound]` for
all twelve new declarations (351 rows in the ledger). `./patches/build-book.sh` under
`nix-shell -p python3` renders the book and asserts `OK: no <base>; fragment links present`.

**Landed 2026-11-27, twentieth slice: the connected six-point function vanishes (C3m).** The
nineteenth slice computed the fifth cumulant and named the even case as the frontier: at six
positions the surviving partitions (`6`, `4+2`, `2+2+2`) have non-zero Möbius coefficients, so the
odd-block count cannot finish the job. This slice computes the sixth joint cumulant of the same
reference law and proves it zero, this time by a genuine Isserlis cancellation. Thirteen
declarations were added to the audit; all rest on standard axioms.

* **The cumulant, by its partition formula.** `connectedSix` is the sixth joint cumulant as the
  Möbius sum over all two hundred and three partitions of the six positions (`Bell 6 = 203`), with
  the coefficient `(−1)^(k−1)(k−1)!` per partition into `k` blocks: one partition into one block,
  thirty-one into two, ninety into three, sixty-five into four, fifteen into five and one into six.
  `connectedSix_one` checks the list: with every face equal to one the sum is
  `1 − 31 + 180 − 390 + 360 − 120 = 0`, the same partition-lattice identity `Σ_π μ(π, ⊤) = 0`.
* **The reduction.** `connectedSix_eq_reduced` states the criterion on the face alone: if every face
  of cardinality one and every face of cardinality three is zero, the Möbius sum is the whole-set
  face minus the fifteen `4+2` products plus twice the fifteen `2+2+2` products. A block of five
  positions is not a hypothesis: it always leaves a singleton, so its product carries a zero
  factor. Only the even partitions survive.
* **The moment lemmas.** `shellFace6 m f s = ∫ p, ∏ t ∈ s, p (f t)` is the joint moment of the
  positions in `s`, with `shellFace6_singleton`/`shellFace6_card_one` for the centred one-point
  function and `shellFace6_card_three` for a three-element block (read as three coordinates,
  `integral_shellLaw_coord_three`). `shellFace6_univ` reads the whole set as the six-point
  integral, `shellFace6_four` reads a four-element block as a four-point integral — the four
  distinctness facts are derived from `({a, b, c, d}).card = 4`, not assumed — and `shellFace6_pair`
  reads a pair.
* **The vanishing.** `connectedSixShell_eq_zero` applies the reduction, rewrites every surviving
  face as an integral, expands the six-point function into its fifteen Isserlis pairings
  (`integral_shellLaw_coord_six`) and each four-point function into its three
  (`integral_shellLaw_coord_four`), and closes the resulting identity in the fifteen `δ`-atoms with
  `ring`: each of the fifteen matchings of six sites appears once in `m123456`, three times in the
  `4+2` sum (once for each choice of the pair that is the two-block) and once with coefficient `2`
  in the `2+2+2` sum, so every matching contributes `1 − 3 + 2 = 0`.
  `connectedSix_coord_eq_zero` reads the result at six coordinates.

Boundary of this twentieth slice: **the first cumulant whose vanishing is a cancellation rather
than a count.** The cumulant is still one explicit two-hundred-and-three-term partition formula on
`Fin 6`, not a general moment–cumulant transform, and no partition-lattice machinery is built. The
cancellation is proved as a finite polynomial identity in the fifteen pairing indicators, not by a
structural bijection between matchings and partitions, and no matching count at general order is
derived. No cumulant of arbitrary order is defined; the odd case beyond six points and the even
case beyond six would each need their own partition list. No separated connected correlation and no
clustering estimate is derived: the vanishing is algebraic, not decay. It remains not a Gaussianity
criterion — vanishing cumulants up to order six do not make a law Gaussian, and no converse is
attempted. Everything remains a statement about the reference law; C3a–C3d, the half-space
inequality, the OS reconstruction theorem and every field law are unchanged.

**Verification.** `lake build BookProof.OSReconstruction.GaussianChainScales` succeeds (8028 jobs)
with no new warnings. `lake env lean Work/EuclideanMomentAudit.lean` reports
`[propext, Classical.choice, Quot.sound]` for all thirteen new declarations (364 rows in the
ledger). `lake build BookProof` succeeds (9128 jobs). `./patches/build-book.sh` under
`nix-shell -p python3` renders the book and asserts `OK: no <base>; fragment links present`.
`scripts/health.sh` reports 3 pass, 0 warn, 0 gap, 0 fail; `check-links` resolves 273 relative
links over 88 documents and the doc index is fresh (88 docs, 252 links).

**Landed 2026-11-27, twenty-first slice: cumulants of arbitrary order, and the vanishing of all
higher ones (C3n).** The twentieth slice computed the sixth cumulant and closed it with the
matching cancellation `1 − 3 + 2 = 0`, and named two boundaries: no cumulant of arbitrary order,
and the cancellation itself locked inside one arity. This slice removes both. The joint cumulant is
defined for every order as the Möbius inversion of the moments over the partition lattice, the
vanishing of every cumulant of order at least three is proved as a single theorem, the matching
cancellation is extracted as a standalone statement about the `wickSum` moments, and the seventh
cumulant (the odd-order case, including the `3+2+2` partitions) is discharged by the general
result. Nineteen declarations were added to the audit; all rest on standard axioms.

* **The cumulant over the partition lattice.** `cumulant face s` is the Möbius sum
  `Σ_π μ(π, ⊤) ∏_{B ∈ π} face B` — equivalently the `(−1)^(k−1)(k−1)!` sum over the `k`-block
  partitions of `s` — computed by the standard recursion that splits off the block of the least
  position: `κ s = face s − Σ_{t ⊆ s, min s ∈ t, t ≠ s} κ t · face (s \ t)`
  (`cumulant_unfold`, with `cumulant_empty` fixing the empty-set convention). Enumerating the
  partitions of `s` is exponential in `card s`, so this is the form that scales past six.
  `moment_eq_sum_cumulant` records the inverse relation (the moment is the cumulant plus the proper
  blocks), `cumulant_singleton` and `cumulant_pair_of_lt` compute the one- and two-element blocks
  (`κ {x, y} = face {x, y} − face {x} face {y}`), and `sum_two_block` is the reindexing that turns
  the surviving two-element blocks into a sum over `s.erase (min s)`: this is the only genuinely
  new combinatorial step, and it is what makes the induction run at every order.
* **All higher cumulants vanish.** `cumulant_eq_zero_of_wick` proves, by induction on `card s`,
  that a moment function with unit total mass, vanishing odd moments and the Wick recursion
  `face s = Σ_{b ∈ s.erase (min s)} c (min s) b · face (s \ {min s, b})` has **every** cumulant of
  order at least three equal to zero. No partition list is inspected: odd moments kill the odd
  blocks and the induction kills every even block except the two-element ones, whose sum is exactly
  the Wick recursion.
* **The matching cancellation, standalone.** `pairingSet_eq_empty_of_odd` (an involution has even
  support, so an odd `s` carries no pairing) and `wickSum_eq_zero_of_odd` give the odd-moment
  hypothesis for the `wickSum` moment sequence, `wickSum_rec` is its Wick recursion and
  `wickSum_empty` its total mass. `cumulant_wickSum_eq_zero` is therefore the cancellation as a
  statement about the pairing sum at **every** order, and `cumulant_wickSum_six_eq_zero` is its
  order-six instance — the `1 − 3 + 2 = 0` of the twentieth slice, now a corollary of a general
  theorem rather than a `ring` computation on `Fin 6`.
* **The reference law at every order.** `shellMoment m f s = ∫ p, ∏ t ∈ s, p (f t) ∂shellLaw m`
  is the joint moment of a finite set of positions. `shellMoment_eq_wickSum` is Isserlis' theorem
  in pairing form at every order, `E[∏_{t ∈ s} p (f t)] = wickSum (fun a b ↦ if f a = f b then 1
  else 0) s`, proved from the general Wick recursion for linear forms `wick_pi` (unit vectors at
  the sites) and not from an enumeration of pairings. `shellMoment_empty`, `shellMoment_odd` and
  `shellMoment_wick` supply the three hypotheses, and `cumulant_shellMoment_eq_zero` concludes that
  **every joint cumulant of the reference law of order at least three vanishes at every order**,
  the eleventh, the hundredth and so on included.
* **The seventh cumulant, and the `3+2+2` partitions.** `cumulant_seven_eq_zero` is the order-seven
  instance, `κ univ = 0` for seven positions. It needs no cancellation: every partition of seven
  positions has a block of odd cardinality, and the `3+2+2` partitions are killed by their block of
  three (`integral_shellLaw_coord_three`), `5+2` by its block of five, and the one-block partition
  by the odd seven-point function. The twenty-first slice therefore records a correction to the
  twentieth's guess: `3+2+2` does not survive the odd-block test. The `1 − 3 + 2` cancellation is
  not the last one either — at order eight the general theorem again replaces a hand-built
  partition list.

Boundary of this twenty-first slice: **the vanishing is general in the order, not in the law.** The
cumulant is the Möbius sum over the partition lattice, but it is computed by the recursion, not by
a formalised `Finpartition` Möbius function: no `μ(π, ⊤) = (−1)^(k−1)(k−1)!` is proved from the
partition lattice's own Möbius theory, and the equivalence between the recursion and an explicit
partition sum is not formalised in general (it is checked in `connectedSix_one` and its
predecessors only through the vanishing of the coefficient sum). The vanishing is proved for the
reference law — the product standard Gaussian — through its three moment properties; it is not a
Gaussianity criterion, no converse is attempted, and no connected correlation at separated points
is computed. `cumulant_wickSum_eq_zero` is algebraic: it says nothing about decay, clustering or
the interacting theory. Everything remains a statement about the reference law; C3a–C3d, the
half-space inequality, the OS reconstruction theorem and every field law are unchanged.

**Verification.** `lake build BookProof.OSReconstruction.GaussianMoments` and
`...GaussianChainScales` succeed (8028 jobs) with no new warnings; `lake env lean
Work/EuclideanMomentAudit.lean` reports `[propext, Classical.choice, Quot.sound]` for all nineteen
new declarations (383 rows in the ledger). `lake build BookProof` succeeds (9128 jobs).
`./patches/build-book.sh` under `nix-shell -p python3` renders the book and asserts
`OK: no <base>; fragment links present`. `scripts/health.sh` reports 3 pass, 0 warn, 0 gap, 0 fail;
`check-links` resolves 273 relative links over 88 documents and the doc index is fresh.
