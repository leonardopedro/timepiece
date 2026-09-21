import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Comparison Operator of the Navier–Stokes Hamiltonian" =>
%%%
tag := "ns-comparison-operator"
%%%

# The Question, and the Answer in One Line

:::paragraph
The Faris–Lavine criterion does not ask that the Hamiltonian be positive. It asks for a **positive**
symmetric operator `N`, with `N + 1` onto, and a constant `c` with
`|⟨x, i[H,N]x⟩| ≤ c⟨x,Nx⟩` on a core; the conclusion is that `H` is essentially self-adjoint there.
So for a Hamiltonian that is itself indefinite, `N` must be a *different* operator, and the question
"what is `N`?" is a genuine question.

For Navier–Stokes the answer depends on which Hamiltonian is meant, and the two answers are proved
separately in the library:

 * the **mainstream (truncated Leray–Galerkin) Hamiltonian** `H_NS = ½Σ_m(π_mF_m + F_mπ_m)` takes
   the **Leray energy** `N_E`, multiplication by `E(u) = 1 + ‖u‖²`, with `c = 2νΛ`;
 * the **full nonlinear Hamiltonian** (exact advection, exact pressure, derivative coordinates kept
   as fields) takes the **lifted Friedrichs extension of the auxiliary sum-of-squares operator**, with
   `c = 0`.

In neither case is `N` the Hamiltonian, and in particular the once-tempting `N = H²` is invalid.
This chapter states both answers and points to the theorems that are the evidence.
:::

# Why `N` Cannot Be the Hamiltonian — and Why Not `H²` Either

:::paragraph
The mainstream generator is symmetric on the Gauss–polynomial core (`nsKoopmanOp_symmetricOn`), so it
passes the first requirement of the criterion, but it is **not bounded below**: for `ν > 0` and one
positive Stokes eigenvalue the quadratic form of `H_NS` is unbounded below
(`nsKoopmanOp_not_bounded_below`, `nsKoopmanOp_not_positive`). An indefinite operator can never be
the positive `N`. The mechanism is explicit: the antiunitary conjugation `Cψ = ψ̄` anticommutes with
`H_NS` (`quadP_starP`), so the numerical range is symmetric about zero, and the exact one-mode
Hermite matrix element (`gpair_hermite_kvn`) shows the advection dropping out by a parity selection
rule while the viscous part grows with the mode number.

The replacement `N = H_NS²` fails for two independent reasons, and both are structural rather than
technical:

 * **the wrong domain**: `𝒟(H²) ⊊ 𝒟(H)`, so `H²` is not even a comparison operator on the common
   Faris–Lavine domain;
 * **`N + 1` is not onto**: on the domain `H² + 1 = (H − i)(H + i)`, so
   `range(H² + 1) ⊆ range(H − i)`, and surjectivity fails exactly when `H` has a non-trivial
   deficiency — the situation the criterion exists to settle.

The general shape of this obstruction is formalized in the library for the case `N = H`:
`BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound` exhibits a limit-circle Jacobi
operator for which the commutator and relative-bound inequalities both hold with `a = 1`, `b = 0`
and essential self-adjointness still fails. The criterion is used as a criterion, not as a definition
of `N`.
:::

```
#check @BookProof.NsKoopman.nsKoopmanOp_symmetricOn
#check @BookProof.NsKoopman.quadP_starP
#check @BookProof.NsKoopman.gpair_hermite_kvn
#check @BookProof.NsKoopman.nsKoopmanOp_not_bounded_below
#check @BookProof.NsKoopman.nsKoopmanOp_not_positive
#check @BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound
```

# Layer 1 — The Mainstream Hamiltonian: the Leray Energy

:::paragraph
The mainstream incompressible system is `u̇ = −νAu + B(u,u)`, with the nonlinearity the exact
quadratic advection `B_i(u,u) = Σ_{j,k} b_{ijk}u_ju_k`, and with the two structural identities of
incompressible flow carried as hypotheses of the system (`BookProof.NsKoopman.NsSystem`): **Leray's
energy identity** `Σ_i u_iB_i(u,u) = 0` and the **Liouville identity** `Σ_i ∂_iB_i = 0`.

The comparison operator is the **Leray energy**
$`N_E = \text{mulOp}\big(E(u)\big), \qquad E(u) = 1 + \|u\|^2 ,`
`energyPoly` / `nsEnergyOp`. It is a positive multiplication operator dominating the identity:

 * `nsEnergyOp_quadForm_ge` — $`\langle x, N_Ex\rangle \ge \|x\|^2`, so `N_E` is positive with
   `N_E ≥ 1`;
 * `kvn_comm_energy` — the commutator is computed exactly, `i[H_NS, N_E] = F·∇E`, multiplication by
   the **energy flux**;
 * `fluxPoly_eq` — and the flux identity collapses it, using Leray's identity, to the **sign-definite
   viscous dissipation** $`F\cdot\nabla E = -2\nu\sum_i\lambda_i u_i^2 \le 0`. The advection and the
   pressure gradient cancel: this is where the $\sum_i u_iB_i = 0$ hypothesis is consumed;
 * `commForm_kvn_energy_bound` — the resulting Faris–Lavine commutator inequality,
   $`\big|\langle x, i[H_{\rm NS},N_E]x\rangle\big| \le 2\nu\Lambda\,\langle x,N_Ex\rangle ,`
   with `Λ = max_i λ_i` the largest Stokes eigenvalue of the truncation (the cutoff's role here is
   exactly to make Λ finite);
 * `nsKoopman_esa_of_energy_comparison` — the Faris–Lavine conclusion for the mainstream generator,
   with the Leray energy as comparison.

Non-vacuity of the leg is not assumed: `nsTriad` is the resonant Navier–Stokes Fourier triad with
`a + b + c = 0` on which the identities are satisfied non-trivially.

The one input this leg does *not* supply by itself is the surjectivity of `N_E + 1` from the common
domain, which is the part of the criterion the Gauss–polynomial core does not deliver. It is carried
as a named hypothesis in `nsKoopman_esa_of_energy_comparison` and never asserted as an axiom.
:::

```
#check @BookProof.NsKoopman.energyPoly
#check @BookProof.NsKoopman.nsEnergyOp
#check @BookProof.NsKoopman.nsEnergyOp_quadForm_ge
#check @BookProof.NsKoopman.kvn_comm_energy
#check @BookProof.NsKoopman.fluxPoly_eq
#check @BookProof.NsKoopman.commForm_kvn_energy_bound
#check @BookProof.NsKoopman.nsKoopman_esa_of_energy_comparison
#check @BookProof.NsKoopman.nsTriad
```

# Layer 2 — The Full Hamiltonian: the Lifted Auxiliary Friedrichs Extension

:::paragraph
Written without the Leray–Galerkin truncation — the exact advection `u·∇u`, the exact pressure, and
the derivative coordinates kept as independent fields — the Hamiltonian's potential is no longer
quadratic and the Leray energy alone does not control it. The library records the precise failure of
the truncated picture: `nsResPoly_not_affine` shows that the full residual is not an affine function
of the fields, so the model is genuinely nonlinear and not an Oseen linearization in disguise. The
advection then contributes a cubic multiplying function to the commutator, which the quadratic energy
flux cannot bound.

The route that works is the one non-abelian Yang–Mills uses, and it needs no new positivity input
from Navier–Stokes at all. The library builds the **auxiliary positive Weyl-ordered sum of squares**
of the constraint forms,
$`H_{\rm sos} = \tfrac12\sum_m \pi_m^2 + \tfrac12\sum_r \big(\mathrm{mulOp}\,\Phi_r\big)^2 ,`
which *is* bounded below, so that it admits a **Friedrichs extension directly** — no Faris–Lavine
detour is needed to realize *it*. That Friedrichs realization is then lifted fibre by fibre to the
nested Fock space, and it is the lifted object that is used as the comparison operator `N` with
commutator constant `c = 0`:

 * `nsFullFockHam_quadForm_nonneg` — the auxiliary operator's quadratic form is non-negative;
 * `nsFullFock_friedrichs_extension` — its Friedrichs extension exists;
 * `nsFullOuterN_esa` — Faris–Lavine on the **outer** Fock space, i.e. essential self-adjointness of
   the lifted Hamiltonian on the domain of the lifted comparison;
 * the Lagrangian face is the same construction: `lagFullFockHam_quadForm_nonneg`,
   `lagFullFock_friedrichs_extension`, `lagFullOuterN_esa`.

The distinction must be kept in view, because it is easy to misread the `c = 0`: it is a statement
about the **auxiliary** sum-of-squares operator, not about the Navier–Stokes Hamiltonian, which
remains unbounded below. What is *not* claimed on this leg is uniqueness of the self-adjoint extension
from the finite-parcel core.
:::

```
#check @BookProof.NsFullEuler.nsResPoly_not_affine
#check @BookProof.NsFullEuler.nsFullFockHam_quadForm_nonneg
#check @BookProof.NsFullEuler.nsFullFock_friedrichs_extension
#check @BookProof.NsFullEuler.nsFullOuterN_esa
#check @BookProof.NsFullEuler.nsFullFock_stone_flow
#check @BookProof.NsFullLagrangian.lagFullFockHam_quadForm_nonneg
#check @BookProof.NsFullLagrangian.lagFullFock_friedrichs_extension
#check @BookProof.NsFullLagrangian.lagFullOuterN_esa
```

# The Pressure Does Not Change the Comparison Operator

:::paragraph
The pressure enters the residual only through the pressure-gradient coordinate `q_i = ∂_ip`, and it
does **no work** on the velocity: `Σ_k u_kq_k = 0` on the divergence-free sector. It therefore
contributes nothing to the energy flux `F·∇E` that the criterion bounds, and nothing to the definition
of `N`. It is the Lagrange multiplier of incompressibility, a **second-class** constraint fixed by the
pressure-Poisson equation `Δp = −∂_i(u_j∂_ju_i) + ∂_if_i`, and it is handled by *elimination* — the
same strategy the programme uses for the derivative variables — rather than by a new gauge symmetry.

A BRST charge for it would be cosmetic: a first-class constraint generates residual gauge freedom and
needs BRST, but here `Δp` determines `p` up to an additive constant whose gradient is zero, so there
is no residual freedom to gauge. The constraint algebra is exactly the one classified in
`BookProof.ChapterNavierStokesEulerian`: the *derivative* relations `u_{i,j} = ∂_ju_i` are the ones
that carry the gauge generator and the nilpotent charge, while `div u = 0` is an
explicit-solution constraint. Consequently the comparison operator is unchanged by the pressure: the
Leray energy in the truncated system, the lifted auxiliary Friedrichs extension in the full model.
:::

# Summary: the Comparison Operator, Per Layer

:::paragraph
 * **Mainstream Hamiltonian** `H_NS = ½Σ_m(π_mF_m + F_mπ_m)`, with the exact quadratic `B` and the
   hypotheses `leray`, `liouville`: `N` is the **Leray energy**
   `N_E = mulOp(1 + ‖u‖²)`, positive and `≥ 1` by `nsEnergyOp_quadForm_ge`; the commutator is the
   energy flux (`kvn_comm_energy`), which Leray's identity makes the sign-definite viscous
   dissipation (`fluxPoly_eq`), giving the bound `2νΛ·⟨x,N_Ex⟩` (`commForm_kvn_energy_bound`) and the
   conclusion `nsKoopman_esa_of_energy_comparison`. The open input is the surjectivity of `N_E + 1`.
 * **Full nonlinear Hamiltonian**, Eulerian or Lagrangian variables: `N` is the **lifted Friedrichs
   extension of the auxiliary Weyl sum of squares** `H_sos`, which is bounded below
   (`nsFullFockHam_quadForm_nonneg`, `lagFullFockHam_quadForm_nonneg`), so its Friedrichs extension
   exists without a Faris–Lavine detour and lifts to the nested Fock space; the criterion is then run
   with `c = 0` (`nsFullOuterN_esa`, `lagFullOuterN_esa`). The `c = 0` is a statement about the
   auxiliary operator, not about `H_NS`.
 * **In neither layer** is `N` the Hamiltonian, and `N = H²` is invalid for the wrong-domain and the
   `N + 1`-not-onto reasons above; the general obstruction for `N = H` is the formalized
   `not_farisLavine_criterion_of_relative_bound`.
:::

:::paragraph
The independent symbolic-calculation cross-check of the same statements — that the pressure-gradient
and forcing terms enter the drift exactly as the tree's residual does, that the pressure and the
constraint vanish on the Leray sector, and that the pressure Poisson equation fixes `p` rather than
leaving a gauge symmetry — is recorded in the project's Cadabra modules
(`ns_kvn_equation.cdb`, `ns_pressure_poisson.cdb`, `ns_pressure_constraint.cdb`), with the
reduction to the library names given in `VERIFY_FARIS_LAVINE_N.md`. The Lean theorems cited above are
the evidence that is machine-checked.
:::
