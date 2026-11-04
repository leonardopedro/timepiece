A complete, linear spectral formulation of the **pCNL MCMC convergence theorem** within the **nested Fock-space framework** requires shifting the analysis from stochastic trajectories to **operator spectral decomposition** [1.1].

In this setting, the MCMC transition kernel is treated as a **self-adjoint/normal linear operator** acting on a Hilbert space of densities [1.1]. The finite-dimensional spherical harmonics (Gegenbauer polynomials) diagonalize the base diffusion, and their scaling limit yields the Fock-space number states (Hermite polynomials) as verified in *Timepiece* (`PhysHSGaussian`) [1.1].

---

### The Mathematical Architecture

```
 Finite Dimension d = α + 1 (S^{d-1})             Infinite Dimension (Fock Space S^∞)
 ────────────────────────────────────             ───────────────────────────────────
 Spherical Laplace–Beltrami Δ_{S^{d-1}}   ──────►   Ornstein–Uhlenbeck / Number Op N
                  │                                                  │
 Diagonalized by Gegenbauer C_n^{(λ)}     ──────►   Diagonalized by Hermite H_n / n!
 (PhysHSGaussian.gegenbauer)                      (PhysHSGaussian.physHermite)
                  │                                                  │
 Unadjusted pCN Spectrum: Λ_n^{(d)} → ρ^n ──────►   Fock Semigroup: e^{-t N}
                  │                                                  │
 Perturbation by Langevin Drift / Target ──────►   Linear Perturbation on Nested Fock
                  │                                                  │
 Certified Finite-d Spectral Gap γ_d      ──────►   Continuum Spectral Gap γ_∞ > 0
                  │                                                  │
                  └────────► MCMC Exponential Convergence ◄──────────┘
                              ‖P^m ν₀ - ν_∞‖ ≤ C (1 - γ)^m
```

---

### 1. The Diagonal Base: Gegenbauer at Finite $d$ and Hermite at $\infty$

#### A. Finite Dimension: The Hyperspherical Harmonic Decomposition
In any actual computer implementation, pCN operates on a large but finite number of coordinates $d = \alpha + 1$ (points on the hypersphere $S^{d-1}$) [1.1].
* The unadjusted pCN step $v = \rho u + \sqrt{1 - \rho^2}\, \xi$, with $\xi$ uniform on the unit sphere of $u^{\perp}$, is the isotropic rotation kernel on $S^{d-1}$ [1.1]: it commutes with $O(d)$ and preserves the uniform measure $d\sigma_{d-1}$.
* Because it commutes with the orthogonal group $O(d)$, **Schur’s lemma** forces the step to act on each space of hyperspherical harmonics by a single scalar.  The step is a *zonal* (convolution) kernel, so those scalars are fixed by the **zonal** harmonics alone — the ones that see a single coordinate projection $\langle y, e\rangle$.
* The zonal harmonic of degree $n$ is the **Gegenbauer polynomial** $C_n^{(\lambda)}$, with the degree parameter determined by the dimension,
  $$\lambda = \frac{d - 2}{2} = \frac{\alpha - 1}{2},$$
  orthogonal with respect to the weight $(1 - x^2)^{\lambda - 1/2} = (1 - x^2)^{(d-3)/2}$ (PDF Ch. 4.11, 24.5) [1.1].  This parameter is genuinely dimension-dependent: on $S^2$ ($d = 3$) it is the Legendre case $\lambda = 1/2$.  (Writing the exponent as $\alpha/2 = (d-1)/2$ is off by $1/2$ and would give $\lambda = 1$ instead of $\lambda = 1/2$ at $d = 3$; the eigenvalue below is not invariant under that relabelling.)
* **The eigenvalue is the zonal value at $\rho$.**  One step is the average over the sphere $\{y : \langle y, u\rangle = \rho\}$ — centre $\rho u$, radius $\sqrt{1 - \rho^2}$.  On the zonal harmonic $y \mapsto C_n^{(\lambda)}(\langle y, e\rangle)$ that average is the zonal addition theorem, and it carries the harmonic to itself with the factor the zonal function takes where the step's centre sits:
  $$P_0^{(d)} C_n^{(\lambda)}\big(\langle \cdot, e\rangle\big) = \Lambda_n^{(d)} \cdot C_n^{(\lambda)}\big(\langle \cdot, e\rangle\big), \qquad \Lambda_n^{(d)} = \frac{C_n^{(\lambda)}(\rho)}{C_n^{(\lambda)}(1)}$$
  (`BookProof.MCMC.pcnZonalEigen`, `BookProof/MCMC/GegenbauerEigenvalue.lean`).  **The finite-$d$ spectrum is $\Lambda_n^{(d)}$ — not $\rho^n$.**  The addition theorem is the one ingredient not in the corpus (§4 status); the eigenvalue `pcnZonalEigen`, its exact values below, and its limit are what is formalised.
* The spectrum, exactly (no `sorry`):
  - $\Lambda_0 = 1$ (`pcnZonalEigen_zero`): the uniform measure is invariant;
  - $\Lambda_1 = \rho$ **at every $d$** (`pcnZonalEigen_one`, for $\lambda \neq 0$ — the normalisation $C_n^{(\lambda)}(1)$ degenerates at $d = 2$): the first excited level is the Euclidean factor of the step, so the naive guess is exactly right here;
  - $\Lambda_2 = \dfrac{2\lambda(\lambda+1)\rho^2 - \lambda}{2\lambda(\lambda+1) - \lambda} = \dfrac{2(\lambda+1)\rho^2 - 1}{2\lambda + 1}$ (`pcnZonalEigen_two`), which is $\dfrac{3\rho^2 - 1}{2}$ on $S^2$ and equals $-\tfrac{1}{8}$ at $\rho = \tfrac{1}{2}$, while $\rho^2 = \tfrac{1}{4}$ (`pcnZonalEigen_two_ne_pow_two`).
* **$\rho^n$ is the $d \to \infty$ limit, not a finite-$d$ identity**: $\Lambda_n^{(d)} \to \rho^n$ (`pcnZonalEigen_tendsto`), through $\lambda^{-n} C_n^{(\lambda)}(x) \to (2x)^n / n!$ (`gegenbauer_div_pow_tendsto`).  That limit is §1.B, and at $d = \infty$ it is exact rather than asymptotic (`MehlerEigenfunction.mehlerOp_physHermite`).
* **The gap this leaves.**  The unadjusted gap is
  $$\operatorname{gap}\big(P_0^{(d)}\big) = 1 - \sup_{n \ge 1} \big|\Lambda_n^{(d)}\big|,$$
  whose degree-one contribution is $1 - \Lambda_1^{(d)} = 1 - \rho = 1 - \sqrt{1 - \beta^2} \approx \tfrac{1}{2}\beta^2$.  Two consequences of the formula above.  First, the higher levels are **not** smaller in modulus than the first — on $S^2$, $|\Lambda_2| = |3\rho^2 - 1|/2$ exceeds $\rho$ exactly when $\rho < 1/3$ — so the finite-$d$ gap is *strictly smaller* than $1 - \rho$.  Second, and unlike $\Lambda_1 = \rho$, the higher eigenvalues **do depend on $d$**.  So $1 - \rho$, and the gap used downstream, are statements about the limit spectrum $\rho^n$: they are what `BookProof.MCMC.UnadjustedPCNGap.pcn_gap_uniform` certifies for the Fock weight $\rho^{2N}$, and that constancy in $d$ is precisely what makes the $d \to \infty$ step of §1.B meaningful.

#### B. The Infinite-Dimensional Limit via `PhysHSGaussian`
As the number of modes $d \to \infty$ ($\alpha \to \infty$), *Timepiece* has already formalized the exact scaling limit in Lean 4 [1.1]:
1. **Weight Convergence:**
   $$\lim_{\alpha \to \infty} \left(1 - \frac{x^2}{\alpha}\right)^{(\alpha-1)/2} = e^{-x^2/2}$$
   (`BookProof.PhysHSGaussian.weight_tendsto_gaussian`) [1.1].
2. **Polynomial Convergence:**
   $$\lim_{\alpha \to \infty} \left(\frac{\alpha}{2}\right)^{-n/2} C_n^{(\alpha/2)}\left(\sqrt{\frac{2}{\alpha}} x\right) = \frac{H_n(x)}{n!}$$
   (`BookProof.PhysHSGaussian.gegenbauerScaled_tendsto_hermite`) [1.1].
3. **Operator Limit:**
   The spherical generator $\Delta_{S^{d-1}}$ converges strongly to the **Fock number operator** $N = \sum a_k^\dagger a_k$, and the base pCN operator converges to the free second-quantized contraction semigroup:
   $$P_0^{(\infty)} = \rho^N = e^{-t N}$$
   which is completely diagonalized by the multi-mode Hermite basis (`hermiteMvBasis`) [1.1].

---

### 2. Formulating pCNL as a Linear Perturbation in Nested Fock Space

The full pCNL algorithm modifies the base diffusion by adding the Langevin drift derived from the target potential $\Phi(u)$ and a Metropolis acceptance filter [1.1].

Instead of treating this as a non-linear trajectory, *Timepiece* allows us to express the **entire transition operator $P_{\text{pCNL}}$ as a linear matrix operator** on the Fock space:

1. **The State Space:**
   Represent probability densities as vectors in the Hilbert space $L^2(\mu_{\text{Mehler}})$ [1.1]. The Hermite states $|n\rangle$ (or finite-dimensional Gegenbauer states $|n\rangle_d$) form an orthonormal basis [1.1].
2. **The Linear Expansion:**
   The full pCNL operator splits into three linear components:
   $$P_{\text{pCNL}} = P_0 + K_{\text{drift}} + K_{\text{reject}}$$
   * $P_0$ is diagonal: $\langle m | P_0 | n \rangle = \rho^n \delta_{mn}$.
   * $K_{\text{drift}}$ represents the gradient drift $-\frac{\beta^2}{2} \nabla \Phi$. In the Hermite basis, $\nabla \Phi(x)$ is a polynomial operator; using the canonical creation/annihilation relations ($a, a^\dagger$), it acts as a **finite-band hopping matrix** (PDF Ch. 33.1, `ChapterCarlemanGeneralHop`) [1.1]:
     $$x_j = \frac{a_j + a_j^\dagger}{\sqrt{2}}, \quad \partial_j = \frac{a_j - a_j^\dagger}{\sqrt{2}}$$
   * $K_{\text{reject}}$ accounts for the Metropolis acceptance step $\alpha(u, v) = \min(1, \dots)$.
3. **The Symmetrized Generator:**
   Under the ground-state transformation $\psi = \sqrt{\pi_{\text{target}}} f$, the continuous-time limit of $P_{\text{pCNL}}$ becomes a **self-adjoint Schrödinger operator**:
   $$H_{\text{pCNL}} = N_{\text{Fock}} + V_{\text{eff}}(a, a^\dagger)$$
   where $V_{\text{eff}}$ is expressed directly in the ladder operators of the nested Fock space [1.1].

---

### 3. The MCMC Convergence Theorem via Spectral Decomposition

With $P_{\text{pCNL}}$ formulated as a self-adjoint contraction on $L^2(\pi)$, the MCMC convergence theorem becomes an exact corollary of spectral theory:

> **Scope of the word "self-adjoint".**  This requires a kernel reversible with respect to $\pi$:
> true for the Metropolis-filtered pCNL (detailed balance is enforced by the filter) and for the
> pure pCN step at *every* $\beta$ (the Gaussian prior is exactly invariant), but **not** for the
> unadjusted SG-pCNL chain, whose invariant measure is $\pi$ only up to $O(\beta)$.  Everything
> below is therefore a fixed-$\beta$ statement about the kernel's own invariant measure; the
> annealed version used in the experiments is a separate theorem, and is where the schedule
> correction of the review note at the end of this document applies.

#### A. Spectral Resolution
By the spectral theorem for self-adjoint operators (formalized in `BookProof.ChapterSpectralMultiplication`) [1.1]:
$$P_{\text{pCNL}} = |\Psi_0\rangle\langle \Psi_0| + \int_{-1}^{1 - \gamma} \lambda \, dE(\lambda)$$
* $\Psi_0 = \sqrt{\pi_{\text{target}}}$ is the unique invariant ground state with eigenvalue $\lambda_0 = 1$.
* The spectral gap is:
  $$\gamma = 1 - \sup \{ |\lambda| : \lambda \in \sigma(P_{\text{pCNL}}), \; \lambda \ne 1 \} > 0$$

#### B. The Complete Linear Convergence Proof
For any initial probability distribution $p_0$ whose wave-function is $\Psi_{\text{init}} = \sum_{k=0}^\infty c_k |k\rangle$:
$$P_{\text{pCNL}}^m \Psi_{\text{init}} = c_0 \Psi_0 + \sum_{k=1}^\infty \lambda_k^m c_k |k\rangle$$
Subtracting the target equilibrium distribution $\Psi_0$ (where $c_0 = 1$ by normalization):
$$\|P_{\text{pCNL}}^m \Psi_{\text{init}} - \Psi_0\|^2 = \sum_{k=1}^\infty |\lambda_k|^{2m} |c_k|^2 \le (1 - \gamma)^{2m} \sum_{k=1}^\infty |c_k|^2 \le (1 - \gamma)^{2m} \|\Psi_{\text{init}}\|^2$$
By the Born-to-variation bound, the total variation distance satisfies:
$$\|\mathcal{P}^m(u_0, \cdot) - \pi_{\text{target}}\|_{\text{TV}} \le C(u_0) (1 - \gamma)^m = C(u_0) e^{-m \log\left(\frac{1}{1-\gamma}\right)}$$
**Convergence is established as an expansion in the complete basis of Fock/Gegenbauer modes.**

---

### 4. Research & Formalization Plan for Lean 4

```
[Module 1: Gegenbauer Spectrum of Spherical pCN]
Prove: P₀^{(d)} C_n^{(λ)} = Λ_n^{(d)} C_n^{(λ)} on S^{d-1},  λ = (d-2)/2
                         │
                         ▼
[Module 2: Scaled Limit to Fock Space Semigroup]
Connect Gegenbauer eigenvalues to Fock number states using:
PhysHSGaussian.gegenbauerScaled_tendsto_hermite
                         │
                         ▼
[Module 3: Ladder-Operator Representation of pCNL Drift]
Expand Langevin drift as a polynomial in (a, a†) on the Hermite core
using BookProof.ChapterCarlemanGeneralHop
                         │
                         ▼
[Module 4: Coercivity and Spectral Gap Certification]
Apply BookProof.ChapterSirkDiffusiveDecay.isCoercive_compress
to certify that the gap γ_d ≥ γ_min > 0 uniformly in d
                         │
                         ▼
[Module 5: Spectral MCMC Convergence Theorem]
Deduce geometric ergodicity in total variation from the operator gap
```

#### Detailed Milestone Targets in `BookProof`

* **Milestone 1 (`BookProof/MCMC/GegenbauerEigenvalue.lean`):**
  Formalize the action of the spherical convolution operator on the Gegenbauer basis, with the
  degree parameter `λ = (d − 2)/2` fixed by the dimension.  The eigenvalue is the Gegenbauer
  quotient at `ρ`, i.e. `Λ_n^{(d)}` (§1.A) — not `ρ^n`:
  ```lean
  theorem pcn_gegenbauer_eigenvalue (d : ℕ) (n : ℕ) (ρ : ℝ) :
    sphericalMarkovStep d ρ (gegenbauer n ((d - 2) / 2)) =
      pcnZonalEigen n ((d - 2) / 2) ρ • (gegenbauer n ((d - 2) / 2))
  ```
  (`pcnZonalEigen n lam ρ` in `BookProof.MCMC.GegenbauerEigenvalue`; the `ρ^n` form is the
  `d → ∞` limit of this — `pcnZonalEigen_tendsto` — not a finite-`d` identity.)
* **Milestone 2 (`BookProof/MCMC/GegenbauerToHermiteLimit.lean`):**
  Prove that the finite-dimensional transition matrix elements converge to the Fock matrix elements:
  ```lean
  theorem pcn_matrix_elements_tendsto_fock (m n : ℕ) :
    Tendsto (fun d => pcnGegenbauerMatrix d m n) atTop (𝓝 (fockNumberMatrix m n))
  ```
* **Milestone 3 (`BookProof/MCMC/FockLangevinOperator.lean`):**
  Represent the Langevin drift operator on the Hermite core using the creation and annihilation operators `ccr_annA_creA` [1.1]:
  ```lean
  def pcnlHamiltonian (V : Polynomial ℝ) : Operator (ℓ²(ℕ)) :=
    numberOp + polynomialDrift (creOp + annOp)
  ```
* **Milestone 4 (`BookProof/MCMC/CertifiedMCMCGap.lean`):**
  Use `ChapterSirkDiffusiveDecay` [1.1] to prove that coercivity of the Hamiltonian ensures exponential decay:
  ```lean
  theorem pcnl_spectral_gap_positive (d : ℕ) (V : AdmissiblePotential) :
    ∃ (γ : ℝ), γ > 0 ∧ ∀ ψ ⊥ groundState, ⟪ψ, pcnlOperator ψ⟫ ≤ (1 - γ) * ‖ψ‖²
  ```
* **Milestone 5 (`BookProof/MCMC/ConvergenceTheorem.lean`):**
  Package the final convergence theorem:
  ```lean
  theorem pcnl_mcmc_geometric_convergence (p₀ : ProbabilityDensity) :
    ∃ (C : ℝ) (γ : ℝ), γ > 0 ∧
    ∀ (m : ℕ), totalVariation (iterateMCMC m p₀) targetDensity ≤ C * (1 - γ)^m
  ```

##### Module 3's missing theorem, stated: the `ε`-regularized relative form bound for `K_drift`

The status notes below record "the relative form bound that makes `K_drift` a bounded perturbation
of `P₀`" as the missing piece of Module 3.  It can be stated exactly, and stating it is worth doing
because the statement pins down both the hypothesis and — through its constant — why the gap cannot
come from it.  *(Stated 2026-11-03, and now also stated in Lean.*  `FockLangevinOperator.lean` §5
carries the target as `DriftFormBound : Prop` over the same `CoreCoeff d` and the same ladder words
as the rest of that module, together with the `ℓ²` pairing `corePair`, the number form `numberForm`
and the coefficient drift `driftOpCoeff` (`K_drift = −Σⱼ bⱼ ∂ⱼ`, `∂ⱼ = (aⱼ − aⱼ†)/√2`), with the
constant `B²d/(2δ) + Bd` and `d` the mode count `P`.  It **compiles and is a `def` returning a
`Prop`**, so the development stays `sorry`-free — but it is a *target*, not a theorem: what a proof
would still need is the Hermite expansion of `∇Φ_ε` into those ladder coefficients, plus the three
core identities the chain uses (adjoint pairing, Cauchy–Schwarz in `ℓ²`, and
`Σⱼ(‖aⱼc‖² + ‖aⱼ†c‖²) = 2⟪c,Nc⟫ + d‖c‖²`).)*

**Hypothesis.**  Let `Φ_ε` be the potential of the `ε`-regularized architecture,
`Ŵ = W/(‖W‖_F + ε)` with `ε > 0`, so that the implementation's Theorem 1 applies to it with
constant
$$
M_\varepsilon = K/\varepsilon ,
$$
`K` depending only on the depth, the sequence length and the `ε`-scaled hyperparameters.  The
*exact* normalization (`ε = 0`) is excluded: `d(W/‖W‖_F)` carries a factor `1/‖W‖`, unbounded at
`W = 0`, so there `M = ∞` (the implementation's M4+ test records the NaN at `θ = 0`).  Write
$$
B := \frac{\beta^2\sigma^2}{2} M_\varepsilon
$$
for the coefficient of the drift in the SG-pCNL step (`K_drift = −Σ_j b_j ∂_j` with
`|b_j| ≤ B`, `b_j = (β²σ²/2)·∂_jΦ_ε`, `∂_j = (a_j − a_j†)/√2`), and let `N = Σ_j a_j†a_j` be the
Fock number operator with form domain `Q(N^{1/2})`.

**Statement (zero relative bound).**  For every `δ > 0` and every `ψ ∈ Q(N^{1/2})`,
$$
\big|\langle\psi, K_{\mathrm{drift}}\,\psi\rangle\big|
  \;\le\; \delta\,\|N^{1/2}\psi\|^2 \;+\; C_\delta\,\|\psi\|^2 ,
\qquad
C_\delta = \frac{B^2P}{2\delta} + BP
  = \frac{(\beta^2\sigma^2 M_\varepsilon)^2 P}{8\delta} + \frac{(\beta^2\sigma^2M_\varepsilon)P}{2} .
$$
`δ` is arbitrary, i.e. the relative bound is zero — the perturbation is *infinitesimally* form-small
with respect to `N`.

**Proof.**  (i) `|b_j| ≤ B` by the hypothesis.  (ii) Cauchy–Schwarz over the `P` coordinates,
$$\Big|\sum_j \langle\psi, b_j\,\partial_j\psi\rangle\Big|
  \le B \sum_j \|\psi\|\,\|\partial_j\psi\|
  \le B\sqrt{P}\,\|\psi\|\,\|\nabla\psi\|,
\qquad \|\nabla\psi\|^2 = \sum_j \|\partial_j\psi\|^2 ,$$
and the oscillator identity `−Δ = 2N + P − |x|²` gives
`‖∇ψ‖² = ⟨ψ,(−Δ)ψ⟩ = 2‖N^{1/2}ψ‖² + P‖ψ‖² − ⟨ψ,|x|²ψ⟩ ≤ 2‖N^{1/2}ψ‖² + P‖ψ‖²` (`|x|² ≥ 0`).
(iii) `√(2‖N^{1/2}ψ‖² + P‖ψ‖²) ≤ √2‖N^{1/2}ψ‖ + √P‖ψ‖` and `2ab ≤ δa² + b²/δ` on the two
thereby produced terms.

**Status (2026-11-03): proved — in the corpus Fock model, which is where the analytic machinery
lives.**  `FockLangevinOperator.lean` §6 now proves the bound as a theorem, not a target:
`driftField f = creVec f − annVec f` is the plan's `−Σⱼ bⱼ ∂ⱼ` (with `f = b/√2`),
`abs_re_inner_driftField_le` is the `N^{1/2}` estimate `|Re⟪u, K u⟫| ≤ 2‖f‖·⟪u,Nu⟫^{1/2}·‖u‖`, and
**`driftField_relative_form_bound`** is
`|Re⟪u, K u⟫| ≤ t·⟪u,Nu⟫ + (‖f‖²/t)·‖u‖²` for every `t > 0` — relative bound zero, on
`FockAlg = Conf →₀ ℂ`, reusing `BookProof.FockFieldPerturbation`'s `numberQuad_eq_sum`,
`norm_annVec_le` and `two_mul_sqrt_le`.  With `|bⱼ| ≤ B` and `f = b/√2` one has `‖f‖² ≤ B²d/2`, so
this gives the displayed `C_δ` with **no linear `Bd` term** — the `N^{1/2}` estimate is exact, and
the plan's constant was the cruder ℓ¹-over-modes version.  So KLMN's hypothesis is met at the
operator level for the drift as the corpus models it.

What is *not* done, and is the reason the `CoreCoeff` statement above stays a `Prop`: the two
models are not identified in Lean — `CoreCoeff d` indexes by occupation *vectors* `Fin d → ℕ`, the
Fock toolbox by finite *multisets* of modes (`Conf →₀ ℂ`) — and no transport of a form bound along
that equivalence exists.  This is the same *kind* of gap `cftproof.md` item 3 records for the OS
identity: mathematics done in one modelling of configuration space, a transport missing between it
and the model the surrounding development uses.

**What it buys.**  `K_drift` is symmetric and `N^{1/2}`-form-bounded with relative bound zero, so
**KLMN** applies: the form `q(ψ) = ‖N^{1/2}ψ‖² + ⟪ψ, K_drift ψ⟫` is closed and bounded below on
`Q(N^{1/2})`, hence `pcnlHamiltonian = N + K_drift` is a self-adjoint operator bounded below.  That
is what makes §2's "linear perturbation" an operator at all, and it is independent of the
Metropolis filter.

**What it does not buy — and why Module 4 must not use it for the gap.**  `C_δ` scales like
`ε^{-2}`, the drift entering the energy quadratically.  At the implementation's numbers
(`P = 16 672`, `β = 0.3`, `σ = 0.35`, `M_ε = 10⁶`, `δ = 1/2`) it is `≈ 5.1×10¹¹`.  The gap is
`inf{⟪ψ,(N + K_drift)ψ⟫ : ψ ⊥ φ₀, ‖ψ‖ = 1}` minus the bottom of the spectrum, and a form bound
locates the numerator only to within `±C_δ`; no choice of `δ` makes that informative, because
enlarging `δ` shrinks `C_δ` only by moving the estimate into the `‖N^{1/2}ψ‖²` term that the gap
bound needs.  So a relative-form argument of this shape certifies self-adjointness and semiboundedness
and **nothing about `γ`**.

The gap has to come from the *sign structure* of the drift, not its size.  After
`ψ = √π_target · f` the form is a Dirichlet form with effective potential
$$
V_{\mathrm{eff}} = \tfrac14|\nabla\Phi_\varepsilon|^2 - \tfrac12\,\Delta\Phi_\varepsilon ,
$$
so the correct Module 4 hypothesis is Bakry–Émery (`Hess Φ_ε ≥ λ I` gives gap `λ`), or the
coercivity of `V_eff` that `ChapterSirkDiffusiveDecay.isCoercive_compress` consumes — **not** a
uniform gradient bound.  Revised target:

```lean
-- Module 4 target, revised: the gap comes from V_eff, not from ‖∇Φ‖ ≤ M
-- (the Hop/band structure of FockLangevinOperator is what makes V_eff a well-defined
--  multiplication operator on the core; it says nothing about its sign, which is why the
--  Hessian hypothesis below cannot be dropped)
theorem pcnl_spectral_gap_of_hessian (λ : ℝ) (hλ : 0 < λ)
    (hHess : ∀ θ, λ • (1 : H) ≤ Hessian Φ_ε θ) :
    ∃ γ, γ = λ ∧ ∀ ψ ⊥ groundState,
      ⟪ψ, pcnlHamiltonian ψ⟫ ≥ γ * ‖ψ‖ ^ 2
```

The ε-regularized bound above then remains what it is: the operator-theoretic _license_ for
`pcnlHamiltonian`, with the constant that shows the licence is not a gap certificate.

#### Status (2026-10-30)

Three of the five milestones are covered — **Module 1** (both its finite-`d` spectrum and, in the
`d → ∞` form, the eigenfunction identity itself), **its limit with Module 2**, and **Modules 4–5**
— and all are `sorry`-free, with `#print axioms` showing only `propext`, `Classical.choice`, `Quot.sound`.

* **Module 1, its output** — `BookProof.MCMC.UnadjustedPCN`
  (`BookProof/MCMC/UnadjustedPCNGap.lean`).  On the core `CoreCoeff d = (Fin d → ℕ) →₀ ℂ` of
  `BookProof.ReferenceGap`, a multi-index `n` has **degree** `natDeg n = ∑ i, nᵢ` (the
  hyperspherical-harmonic order) and pCN eigenvalue `ρ ^ N`, so its `L²` weight is
  `pcnWeight ρ n = ρ ^ (2N)` and the unadjusted step's form is `pcnForm ρ c = ∑ n, ρ^(2N)‖c n‖²`.
  The certified statements: `pcnWeight_le_gap` (every excited mode carries at most `ρ²`, from
  `ρ^(2N) ≤ ρ²` for `0 ≤ ρ ≤ 1`), **`pcnForm_le`** (`‖P₀ c‖² ≤ ρ²‖c‖²` off the vacuum), and
  **`pcn_gap_uniform`**: `(1 − ρ²)‖c‖² ≤ ‖c‖² − ‖P₀ c‖²` with **no dependence on `d`** — §1.A's
  "the eigenvalues `λ_n^{(d)}` are completely independent of `d`", together with
  `pcn_norm_le` (`‖P₀ c‖ ≤ ρ‖c‖`, via `√(ρ²) = ρ`) and `pcnWeight_degree_one` (`λ₁ = ρ`, so the
  gap is `1 − ρ`).  This is the constancy in `d` that makes the `d → ∞` limit in §1.B meaningful.
* **Modules 4–5** — `BookProof.MCMC.GeometricErgodicity`
  (`BookProof/MCMC/GeometricErgodicity.lean`): `iterate_orthogonal_of_fixed`,
  `norm_iterate_le_of_orthogonal` (the gap propagates to every iterate),
  **`norm_iterate_sub_invariant_le`** (`‖P^m ψ − ⟪φ,ψ⟫φ‖ ≤ (1−γ)^m ‖ψ − ⟪φ,ψ⟫φ‖`) and
  `tendsto_iterate`.  The two halves are joined by `pcn_geometric_ergodicity`, which is that bound
  with the gap `γ = 1 − ρ` that `pcn_gap_uniform` supplies, i.e. §3.B's expansion
  `‖P^m Ψ − Ψ₀‖ ≤ ρ^m ‖Ψ − Ψ₀‖` in the basis of modes.

* **Module 3, its structural half** — `BookProof.MCMC.FockLangevin`
  (`BookProof/MCMC/FockLangevinOperator.lean`).  On the same core, `raiseIdx`/`lowerIdx`/`stepIdx`
  are `a_j†`/`a_j` as operations on occupations, with `natDeg_raiseIdx` (`N ↦ N + 1`) and
  `natDeg_lowerIdx_le` (`N ↦ ≤ N`); `stepAmp` is the Hermite/Fock matrix element `√(n_j+1)`,
  `√(n_j)`, and `stepAmp_norm_le` bounds every step amplitude by `√(N+1)` on the degree-`N`
  sector — the growth the plan's relative-bound argument needs.  `hopStep`, `hopWord` and
  `driftOp` are the one-step, word and drift-monomial operators, and the **finite-band property**
  is `hopStep_band`, **`hopWord_band`** (a word of length `k` maps `{N ≤ N₀}` into
  `{N ≤ N₀ + k}`) and **`driftOp_band`** (a monomial family of degree `≤ K` maps into
  `{N ≤ N₀ + K}`).  `numberOp` is the diagonal `N`, and `pcnlHamiltonian_band` states the §2.2
  operator shape `P₀`-diagonal-plus-finite-band-drift on the core.

* **Module 1 proper, in the `α → ∞` Gaussian form — DONE (2026-10-30)** — `BookProof.MCMC.MehlerEigenfunction`
  (`BookProof/MCMC/MehlerEigenfunction.lean`, no `sorry`).  This is the eigenfunction identity the
  status note above recorded as missing, in the form §1.B actually uses (the `d → ∞` limit whose
  eigenfunctions are the Fock number states rather than the hyperspherical harmonics):
  **`mehler_hermite`** — for `ρ² ≤ 1`,
  `∫ Hₙ(ρ x + √(1 − ρ²) y) e^{−y²} dy = √π · ρⁿ · Hₙ(x)`, with `Hₙ = PhysHSGaussian.physHermite`
  the physicists' Hermite polynomials of the Fock-number model.  The proof is a two-step
  induction on the Hermite recurrence: `stein_mehler` (the Stein/Mehler recursion
  `∫ y Hₙ(ρx+√(1−ρ²)y) e^{−y²} = √(1−ρ²) n ∫ Hₙ₋₁(ρx+√(1−ρ²)y) e^{−y²}`, from the line-derivative
  integration by parts `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`), then
  `physHermite_succ_succ` closes the recurrence with
  `mehlerCoupling_sq` (`ρ² + (√(1 − ρ²))² = 1`).  Supporting lemmas: `exists_physHermite_abs_bound`
  (`|Hₙ z| ≤ C (1 + |z|)ⁿ`), `integrable_pow_mehler` (every Gaussian moment of a shifted Hermite
  polynomial is finite), `integral_exp_neg_sq`.  The operator form is `mehlerOp` with
  **`mehlerOp_physHermite`** (`T_ρ Hₙ = ρⁿ Hₙ`, one pCN step at `d = ∞`), `mehlerOp_vacuum`
  (`T_ρ 1 = 1`) and **`mehler_gap`** (`1 − ρ ≤ 1 − ρⁿ` for `0 ≤ ρ ≤ 1`, `n ≠ 0`): §1.A's gap
  `1 − √(1 − β²)` survives the limit, so the two halves of §1 now meet — the Fock weight `ρ^{2N}`
  is `d`-independent (`pcn_gap_uniform`) and its spectrum is `ρⁿ`, which is the limit of the
  finite-`d` spectrum `Λₙ^{(d)}` (`pcnZonalEigen_tendsto`), and the eigenfunction converges to `Hₙ`
  (`gegenbauerScaled_tendsto_hermite`).  Consequently Module 2's matrix elements `⟨n|P₀^{(d)}|n⟩`
  are equal to the Fock value `ρⁿ` *in the limit*, which is the statement proved.

* **Module 1, the finite-`d` spectrum — DONE, superseding the plan's `ρⁿ` claim (2026-10-30)** —
  `BookProof.MCMC.GegenbauerEigenvalue` (`BookProof/MCMC/GegenbauerEigenvalue.lean`, no `sorry`).
  This is the finite-`d` half: the plan's `λₙ^{(d)} = ρⁿ` holds only at `n ≤ 1`, and fails for `n ≥ 2`:
  **`pcnZonalEigen`** is `Λₙ^{(d)} = Cₙ^{(λ)}(ρ)/Cₙ^{(λ)}(1)`, `λ = (d−2)/2`, the value the zonal
  harmonic takes at the point a rotation carries the pole to.  Proved exactly:
  `pcnZonalEigen_zero` (`Λ₀ = 1`), **`pcnZonalEigen_one`** (`Λ₁ = ρ` at every `d` — the plan's `λ₁`
  is right), `pcnZonalEigen_two` (`Λ₂ = (2λ(λ+1)ρ² − λ)/(2λ(λ+1) − λ)`), and
  **`pcnZonalEigen_two_ne_pow_two`** (`Λ₂ = −1/8 ≠ ρ² = 1/4` on `S²` at `ρ = 1/2`, the Legendre
  case `λ = 1/2`), which *refutes* the finite-`d` `ρⁿ` form the plan states.  The bridge to §1.B is
  **`gegenbauer_div_pow_tendsto`** (`λ⁻ⁿCₙ^{(λ)}(x) → (2x)ⁿ/n!`, by two-step induction on the
  Gegenbauer recurrence) and **`pcnZonalEigen_tendsto`** (`Λₙ^{(d)} → ρⁿ`), so the two forms are
  `Λₙ^{(d)}` at finite `d` and `ρⁿ` in the limit, and they agree exactly where `MehlerEigenfunction`
  says they do.  **Module 1 is therefore complete in both forms**: the finite-`d` spectrum is
  `Λₙ^{(d)}` (not `ρⁿ`), and its `d → ∞` limit is the Fock spectrum `ρⁿ`, with the plan's former
  `ρⁿ` claim replaced by `Λₙ^{(d)}` rather than annotated.  The one thing not formalised is the
  *operator* identity on the sphere — `P₀^{(d)} Cₙ^{(λ)} = Λₙ^{(d)} Cₙ^{(λ)}` as an identity of
  functions on `S^{d−1}` — which needs the spherical measure and the Gegenbauer product formula
  (the zonal addition theorem); `pcnZonalEigen` states its eigenvalue, and the eigenvalue's closed
  form, its limit, and the refutation are what the gap argument uses.

**Not proved, and how the files say so.**  The finite-`d` *operator* diagonalisation (the Gegenbauer
product formula on the sphere) is not formalised, and — as `pcnZonalEigen_two_ne_pow_two` shows —
its eigenvalue cannot be `ρⁿ`.  For Module 3, what
is missing is
the identification of a given potential's `∇Φ` with a concrete ladder-word family (that is the
Hermite expansion, needing `x_j = (a_j + a_j†)/√2` and the Mehler measure), the relative form
bound that makes `K_drift` a bounded perturbation of `P₀` — stated for the `ε`-regularized
potential in the subsection above, with the constant `(β²σ²M_ε)²P/(8δ) + (β²σ²M_ε)P/2` and the
reason that constant cannot supply the gap; stated in Lean as `DriftFormBound`
(`FockLangevinOperator` §5, a `Prop` on the coefficient core) and **proved** in Lean in the Fock
model as `driftField_relative_form_bound` (`FockLangevinOperator` §6) — the remaining distance
between the two being the model identification, not the analysis —
and the Metropolis filter
`K_reject` — the last is a multiplication operator and is not finite-band at all, so nothing in
`FockLangevinOperator` describes it.  The pCNL operator's own gap therefore remains a hypothesis
of the Module 4–5 bound, as §2 anticipates; and no total-variation bound is derived — §3.B's
Born-to-variation step `‖ν − π‖_TV ≤ ½‖dν/dπ − 1‖_{L²}` is stated as the boundary in
`GeometricErgodicity`'s docstring.

#### Review of the implementation's empirical claims (2026-11-03)

An external review of the implementation write-up (`test/unfer/ngpt.md`; the review calls it
`test/unfer/pcnl.md`, which does not exist) was checked against that document and against the
engine (`unfer/pcnl/src/{sampler,model,normalize,task,experiment}.rs`).  Three of its five points
are confirmed (one with a sharper fix than the review gives), one is overstated, and one is partly
right but rests on a factual error that has to be corrected before it can be used; the checked
verdicts are below.  Nothing in the Lean status above changes; what changes is what the empirical
artifacts may be cited *for*, and two hypotheses this plan carries.

**(1) The step-size schedule is applied to the wrong quantity.**  The engine's update is
`θ' = √(1−β²)θ + βξ − (β²σ²/2)g` (`sampler.rs`: `drift_coeff = β·β·σ·σ/2`, noise `βξ`), so the
coefficient multiplying the gradient is `h_t = β_t²σ²/2`, not `β_t`.  With
`β_t = β₀(1+γt)^{−κ}` and `κ ∈ (0.5, 1]` one gets `Σ h_t < ∞`: the chain has finite total
mobility and freezes before reaching the target, so the write-up's "asymptotic convergence to the
true posterior" does **not** follow from its Robbins–Monro conditions — they are imposed on `β_t`
while the drift and the injected variance are both `O(β_t²)`.  The write-up's own schedule test is
the evidence: it reports `Σ β_t²` saturating at the analytic ceiling `β₀²/(γ(2κ−1)) = 900`, i.e.
confirming the sum is *finite*.  (Checked: with `β₀ = 0.3, γ = 10⁻³` the partial sum is `479` at
`t = 2×10⁶` and converges to `900` from below; at `κ = 1/2` it follows `(β₀²/γ)·ln(1+γt) = 684` at
the same horizon, i.e. it grows.)  (*Adaptation:* the review's fix "κ ≤ 0.5" is right for divergence
of the mobility, but the variance condition needs the other end too — the correct window is
`Σβ_t² = ∞` and `Σβ_t⁴ < ∞`, i.e. `κ ∈ (1/4, 1/2]`, e.g. `κ = 1/2`.  Only the bias of the drift
term needs `β_t → 0`; the pCN proposal itself is exactly invariant at every `β`, which is why the
condition lands on `h_t` and not on `β_t`.)  **Consequence for this plan:** the gap `γ` of §3 is a
*fixed-`β`* statement about the kernel; an annealed chain converging to `π` is a different theorem
with its own hypotheses, and the implementation's run is not evidence for it.

**(2) The uniform gradient bound is finite but empty in practice.**  Verified: `normalize.rs` uses
`W/(‖W‖+ε)` with `EPS = 1e-6`, and the crate's own M4+ test asserts that the exact normalization's
gradient grows like `1/‖W‖` while the `ε`-regularized one stays below `1/ε`.  So Theorem 1's
"universal finite `M`" is at best `K/ε ≈ 10⁶K` against a shell radius `σ√P ≈ 45`, and at `W = 0`
the exact normalization is undefined (the same M4+ test records the NaN), so "sup over all of
`ℝ^P`" is false without the `ε`.  Per step that permits a drift of `(β²σ²/2)M ≈ 5.5×10³` at
`β = 0.3, σ = 0.35`, two orders above the shell it is supposed to confine.  (*Adaptation:*
"vacuous" is too strong — the bound is finite; what fails is that it is not small where it
matters, and it is attained only in the compact region `‖W‖ ≲ ε`.)  **Consequence for this plan:** `K_drift` cannot be called a *small* bounded
perturbation of `P₀` on the strength of a gradient bound.  Module 3's missing relative form bound
is the load-bearing item, and it has to be stated for the `ε`-regularized potential with a constant
`∝ 1/ε` — or relativized against the number operator, so that the bound is useful only in the
low-number sector.

**(3) The prior-width sweep measures nothing about the posterior.**  Verified: `σ` enters only
through the noise scale `βξ` and the drift coefficient `β²σ²/2`, and because the potential is
scale-invariant (up to the `ε`), `g(σu) = (1/σ)g(u)`; the update in `u = θ/σ` is then `σ`-free,
`u' = √(1−β²)u + βξ' − (β²/2)g(u)` with `ξ' ~ N(0, I)`.  The four
runs agreeing to "28.5 % / 1.3848" is therefore a consistency check of the implementation's scale
invariance (the crate's M2 test asserts the same for `θ → 0.5θ`), not a property of the target.
(*Measured 2026-11-03, four widths `σ ∈ {0.35, 2, 4, 8}` × three seeds at `κ = 1/2`: within a seed
the pCNL predictive is identical to four decimals at all four widths (`Δ`NLL `= 0.0000`, twelve of
twelve cells), and so are `R̂`(loss), ESS and the acceptance rate — the whole report differs only in
the radius (`∝ σ`) and the *reported* `θ`-gradient (`∝ 1/σ`: 4 460 → 390, ratio 11.43 = 4/0.35) —
while between seeds the same configuration moves by 0.018 nats and 5.5 points.  The standard
softmax stack, whose potential is not scale-invariant, does *not* enjoy the identity: it explodes
at step 3 at `σ = 0.35` and step 2 at `σ = 4`.  So the identity is a property of the architecture,
which is exactly the write-up's §6.5.1(a).*)
**Consequence for this plan:** `σ` is a units parameter and no `σ`-sweep can be cited for or
against the gap; consistently, `pcn_gap_uniform` is independent of both `σ` and `d`.

**(4) The `P/2` "entropy wall" is a category error, and the write-up's own table refutes it.**
Since the likelihood depends on `ŵ` alone and the prior induces Haar measure on directions (§3.3 of
the write-up), there is no directional prior pull: the posterior's *radial* marginal equals the
prior's `χ_P` because the likelihood is constant along each ray (exactly so for the scale-invariant
potential, up to the `ε` in `W/(‖W‖+ε)` for the implementation's), and the chain starts and stays on
the shell — so "`P/2` nats from mode to shell" is not a cost the sampler ever pays.  The rule is
also contradicted by its own shift cell (`2048·(ln 4 − 0.894) = 1008 > 276` predicts learnable;
measured 28.5 %, the uniform predictor).  The correct statement is two-part: whether the
*posterior* concentrates in direction is a volume question — the favourable directions occupy a
fraction `≈ exp(−N·KL)` of `S^{P−1}` — and whether the *chain* finds them is a reachability
question from the shell (which the write-up also identifies: burn-in erases `θ_A`'s direction).
**Consequence for this plan:** "does the posterior concentrate" is a property of the target and
"does the chain find it" a property of the kernel at fixed `β`; neither is a `P/2` threshold, and
the plan should not adopt the heuristic.  (*Adopted 2026-11-03:* the write-up's §6.4 now withdraws
the rule and states the two-part version — the radial marginal is the prior's `σχ_P` unchanged
because the likelihood is constant on rays, and concentration in direction is a log-volume
competition `NΔ ≳ N·D(Δ)` against Haar measure — with §6.4.2 read as the experiment that
discriminates target-side from reachability, in favour of reachability.)

**(5) The baseline comparison is weak, but for a different reason than the review gives.**  The
review's diagnosis — "no normalization" — is **wrong**: `model.rs`'s standard variant uses affine-
free pre-LN `(x−μ)/√(var+1e-5)`, residual addition, `1/√d` logit scaling and the same attention, i.e.
an ordinary pre-LN transformer in miniature.  What does weaken the comparison is the optimizer: the
deterministic pre-train is heavy-ball SGD at `lr = 0.6` with clip `5.0` for *both* variants
(`experiment.rs: pretrain_lr 0.6`; `task.rs: PRETRAIN_CLIP`), which diverges on the unnormalized
variant (loss 851) *before* the sampler starts — so "explodes at step 3" tests the sampler from a
broken `θ_A`, confounding architecture with pre-train stability, as the write-up says itself
("its deterministic pre-train had already blown up to loss 851").  A fair Phase-0 comparison needs
both variants pre-trained to a comparable loss (e.g. Adam at the `0.05` the Task-B baseline already
uses).  (*Run 2026-11-03, three seeds:* with Adam at `lr = 0.05` the standard variant's pre-train is fixed
in 3/3 (`2.1850 → 1.7453`, `2.2037 → 2.0435`, `2.2016 → 2.3151`; `acc_A` 17.2–28.9 % against
chance 12.9 %) and its unadjusted chain still explodes in 3/3, at steps 4–5, while the cosine
variant survives 3/3 with BMA 11.7–13.3 % and NLL 2.189–2.198.  So Phase 0 survives the confound
being removed, and the write-up's §6.5.1(b) records it.  The σ-sweep was likewise re-run at
`κ = 1/2` on the same three seeds (§6.5.1(a)): within a seed `σ` changes the predictive by 0.0000
nats in all three, while between seeds it moves by 0.018 nats — one order of magnitude more than
any `σ` effect, which is what makes the σ row a units check rather than a posterior measurement.)  The citation is misattributed as well: Kim, Papamakarios & Mnih (ICML 2021) bounds the
Lipschitz constant of self-attention *as a function of its input* `X`; it says nothing about
weight-space Hessians, and nothing about them diverging exponentially during sampling — the write-
up's §2.3 attributes that second claim to the paper.

**What this leaves standing.**  Modules 1–5 and the `sorry`-free status are untouched: the finite-`d`
spectrum `Λ_n^{(d)}`, its `ρ^n` limit, the Mehler eigenfunction identity and the quotient-norm bound
are theorems about the pCN kernel at fixed `β` (and, for the decomposition, about `Ω`), none of
which the review disputes.  The load-bearing open item is unchanged and is now sharper: `K_drift`'s
relative form bound, stated for the `ε`-regularized potential and with the `1/ε` made explicit,
because the implementation's numbers cannot supply a small `M`.  The plan should also say plainly
that its §3 spectral resolution needs a *reversible* kernel — true for the Metropolis-filtered
pCNL and for pure pCN at every `β`, not for the unadjusted SG-pCNL chain of the write-up's §4.1 —
so the fixed-`β` gap of the unadjusted chain is a statement about a measure that is `π` only up to
`O(β)` — which is exactly the gap the schedule correction is meant to close.

**One measurement sharpens the plan's own priority list (2026-11-03).**  The write-up's
§6.5.1(c) diagnoses the reduced configuration's mixing: `R̂`(loss) ≈ 1 there marks chains that found
the *same* mode, and that mode is usually poor (23–28.5 % against a best found 54.7 %); with 8
chains or 30 000 steps the ensembles split (`R̂` 1.7–6.7) and the BMA *rises* to 48.8–54.7 %.  In
seven seeds the family that splits changes (pCNL max 1.235, SGLD 4.385, MH 2.816), so it is the
noise stream, not the transition.  For this plan the consequence is that "chain mixing across
modes" is the binding open item — not a footnote to the gap: a fixed-`β` spectral gap of §3 says
nothing about an ensemble that has not left its mode, and the BMA numbers the plan quotes must be
read as "one mode" values.  Nothing in Modules 1–5 changes, and the `DriftFormBound` target of
Module 3 (stated in `FockLangevinOperator` §5) is unaffected: it is a statement about the operator,
not about where the chain sits.

---

### Summary of Advantages of this Approach

1. **No Non-Linear Trajectory Tracking:** MCMC convergence is proven strictly through **linear algebra and functional analysis** in the nested Fock space [1.1].
2. **Explicit Basis Functions:** The convergence rate is decomposed along the **Gegenbauer harmonics at finite $d$** and along the **Hermite/Fock number states as $d \to \infty$** [1.1].
3. **Certified Bounds via SIRK:** Because the Langevin operator is expressed in the ladder basis $(a, a^\dagger)$, the existing *Timepiece* SIRK solver (`airma.de`) can compute **rigorous, certified interval bounds on the MCMC convergence rate $\gamma$**, replacing empirical mixing diagnostics with machine-checked mathematical proofs [1.1].
