import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Eliminating the Derivative Variables in Quantum Gravity" =>
%%%
tag := "qg-elimination"
%%%

# The Problem: Twenty-Seven Derivative Components Per Momentum

:::paragraph
The quantum-gravity model of record is the $`R^2` (Starobinsky) Hamiltonian in **vielbein** form,
with the **full exponential** Einstein-frame scalaron wall and the interaction (coupling) terms. Its
field-space model carries `36` components per momentum: the nine vielbein components
$`e_\nu^i(k)` *and* the twenty-seven independent derivative variables $`D_{\mu\nu}^i(k)`, the latter
present because the derivative gauge forms $`G_{\mu\nu}^i = D_{\mu\nu}^i - i k_\mu e_\nu^i` are imposed
inside the quadratic form.

The {ref "fourier-elimination"}[Fourier-elimination chapter] explained for Navier–Stokes why the
current plan of record *eliminates* such variables instead of fixing them by a BRST gauge symmetry:
the substitution is used when the operator is *defined*, so the auxiliary variables never have to
exist. This chapter is the quantum-gravity half of that strategy, and it is done in two steps — first
the derivative components alone (which is where the vielbein self-interaction lives), then the whole
Hamiltonian, rebuilt on the nine physical components with nothing else left over.
:::

# Step One: the Torsion Is a Form in the Physical Modes Alone

:::paragraph
Read the gauge condition as a substitution, $`\sigma(D_{\mu\nu}^i(k)) = k_\mu e_\nu^i(k)`, and the
torsion becomes a linear form in the physical vielbein modes `CMode` only — the extended space
`EMode` appears neither in the definition nor in the domain of the operator built from it:

 * `elimD` is the elimination and `elimTorsion` the torsion $`T = D - D^{\mathsf T}` *after* it; both
   have type $`\mathrm{CMode} \to \mathbb C`;
 * `elimTorsion_eq_torsionCoef`: the eliminated torsion is exactly the physical Fourier torsion
   $`k_\mu e_\nu^i - k_\nu e_\mu^i` at momentum `k` (and zero on the other momenta), so the
   substitution is **lossless**; `elimTorsion_eq_gaugeReduce` identifies it with the gauge-reduced
   extended form of the BRST chapter, which is how that chapter's identities are restated as an
   elimination rather than as a symmetry;
 * `elimTorsion_antisymm`, `elimTorsion_diag`, `elimTorsion_conj`: the structural facts — the
   torsion is antisymmetric in the derivative indices, vanishes on the diagonal, and is
   real-coefficient;
 * `elimGram_eq_contTorsionGram`: the Gram matrix of *all* eliminated torsion forms is exactly the
   vielbein self-interaction `contTorsionGram` of the continuum model, with no hypothesis relating
   the two momenta (off the momentum diagonal both sides vanish). This is the statement that makes
   the elimination admissible: the interaction of the model survives it verbatim;
 * consequently `qgElimModes` is the continuum mode data (`qgElimModes_A` states that its
   self-interaction matrix *is* the eliminated Gram matrix), and `qgElim_esa` /
   `starobinsky_qgElim_esa` give essential self-adjointness of the model it defines on the outer Fock
   space, with the full exponential Einstein-frame wall and **arbitrary coupling constant**. No BRST
   charge, no ghost sector and no restriction-to-a-subset argument is used: the physical torsion is
   the only torsion from the start.
:::

```
#check @BookProof.QgFourierElim.elimD
#check @BookProof.QgFourierElim.elimTorsion
#check @BookProof.QgFourierElim.elimTorsion_eq_torsionCoef
#check @BookProof.QgFourierElim.elimTorsion_eq_gaugeReduce
#check @BookProof.QgFourierElim.elimTorsion_antisymm
#check @BookProof.QgFourierElim.elimTorsion_conj
#check @BookProof.QgFourierElim.elimGram_eq_contTorsionGram
#check @BookProof.QgFourierElim.qgElimModes
#check @BookProof.QgFourierElim.qgElimModes_A
#check @BookProof.QgFourierElim.qgElim_esa
#check @BookProof.QgFourierElim.starobinsky_qgElim_esa
```

:::paragraph
In the *full* vielbein–scalaron model, whose modes carry the nine vielbein components together with
the twenty-seven derivative components, `elimConfig` parameterizes the derivative-gauge constraint
surface **exactly**: an eliminated configuration satisfies all twenty-seven constraints identically
(`formValue_dGauge_elimConfig`), and every configuration satisfying them is eliminated
(`eq_elimConfig_of_gauge_fixed`). On that surface the torsion form is the exact Fourier torsion
(`formValue_torsion_elimConfig`) and the transverse gauge form is unchanged
(`formValue_gauge3d_elimConfig`). The elimination is not vacuous — `elimTorsion_ne_zero` exhibits a
torsion that the elimination genuinely produces.
:::

```
#check @BookProof.QgFourierElim.elimConfig
#check @BookProof.QgFourierElim.formValue_dGauge_elimConfig
#check @BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed
#check @BookProof.QgFourierElim.formValue_torsion_elimConfig
#check @BookProof.QgFourierElim.formValue_gauge3d_elimConfig
#check @BookProof.QgFourierElim.elimTorsion_ne_zero
```

# Step Two: the Whole Hamiltonian on the Nine Components

:::paragraph
Step one still leaves the derivative-gauge *form* in the quadratic form of the full model. Step two
rebuilds the entire Hamiltonian — vielbein self-interaction (torsion), derivative gauge fixing, 3D
transverse gauge fixing, the scalaron in position representation with the full exponential
Einstein-frame wall, and the coupling to the trace of the vielbein — on the nine eliminated
components `EComp` alone, i.e. on `EGMode = Mom × EComp`, and proves its essential self-adjointness
again, by the same Faris–Lavine route, on the *smaller* outer Fock space:

 * `elimCoef` is the coefficient vector of each form *in the nine vielbein components only*, and
   `eFormValue` evaluates it; `eFormValue_torsion`, `eFormValue_dGauge`,
   `eFormValue_gauge3d` are the three families of forms, and
   `eFormValue_eq_formValue_elimConfig` is the agreement with the eliminated configurations of step
   one — the two steps describe the same forms;
 * the coefficient bound is uniform in the momentum, `norm_elimCoef_le` — needed because the
   elimination trades the extended index for momentum-dependent coefficients;
 * `eGram` is the self-interaction Gram matrix on the physical modes, with `eGram_herm`,
   `eGram_off` (the neighbourhood sparsity) and the Schur-type bound `norm_eGram_le`; then
   `eGram_eq_torsion_add_gauge3d` decomposes it and `eGram_quadForm` / `gGram_quadForm` are the
   quadratic forms of the eliminated and gauge-fixed presentations, identified by
   `quadForm_eq_of_gauge_fixed`;
 * `eCoupling` is the coupling to the trace (`eTrace`), with `eCoupling_herm`, `eCoupling_off` and
   `norm_eCoupling_le`; this is where the scalaron-vielbein **interaction terms** enter;
 * `qgElimFullModes` assembles the mode data, and the results are
   `qgElimFull_esa_farisLavine`, `qgElimFull_esa_core_fl` (the essential self-adjointness on the
   finite-occupation core), `eSecCore_dense`, and the scalaron instances `starobinsky_qgElimFull_esa`
   / `starobinsky_qgElimFull_esa_core` — with the full exponential wall and arbitrary coupling.
:::

```
#check @BookProof.QgFullEliminated.EComp
#check @BookProof.QgFullEliminated.EGMode
#check @BookProof.QgFullEliminated.elimCoef
#check @BookProof.QgFullEliminated.eFormValue
#check @BookProof.QgFullEliminated.eFormValue_eq_formValue_elimConfig
#check @BookProof.QgFullEliminated.norm_elimCoef_le
#check @BookProof.QgFullEliminated.eGram
#check @BookProof.QgFullEliminated.eGram_eq_torsion_add_gauge3d
#check @BookProof.QgFullEliminated.eGram_quadForm
#check @BookProof.QgFullEliminated.quadForm_eq_of_gauge_fixed
#check @BookProof.QgFullEliminated.eCoupling
#check @BookProof.QgFullEliminated.norm_eCoupling_le
#check @BookProof.QgFullEliminated.qgElimFullModes
#check @BookProof.QgFullEliminated.qgElimFull_esa_farisLavine
#check @BookProof.QgFullEliminated.qgElimFull_esa_core_fl
#check @BookProof.QgFullEliminated.starobinsky_qgElimFull_esa
```

:::paragraph
**Manuscript provenance — why the Hamiltonian may be taken quadratic in the ladders.**  The shape
above is the manuscript's, and its justification is the recursive construction of the Fock space:
*“Since the second-quantization procedure can be applied recursively … in case the Hamiltonian acting
in the Fock-space is not quadratic in the creation/annihilation operators, then we can consider
instead a new Fock-space where the base Hilbert space is the original Fock-space. The new Hamiltonian
is quadratic in the creation/annihilation operators.”*  The manuscript writes each sector's
Hamiltonian as a one-particle operator enclosed between creation and annihilation,
$`H = \int d^3\vec x\, a^\dagger(\vec x)\, H(\vec x)\, a(\vec x)` — its Navier–Stokes instance is
$`H(\vec x) = \pi^i(u_j u_{i,j} - \nu u_{i,jj}) + (h.c.)`, and the graviton/scalaron instance has the
same envelope.  The inner space is where the fields and their spatial derivatives live; in this
chapter the vielbein's derivative modes are **not** constrained by a gauge symmetry — they are
eliminated by the spatial Fourier substitution and reappear in momentum space as **convolutions**
(`ChapterQgFourierElimination`, `ChapterQgFullEliminated`), the same device the Navier–Stokes route
uses (`BookProof.NsAdvectionConvolution`).
:::

:::paragraph
The final Hamiltonian of the sector is again the one-particle Hamiltonian enclosed in creation (on
the left) and annihilation (on the right) operators on the outer Fock space, and the chapter proves
the structural clauses that make that enclosure usable: `qgElimFull_momentum_conserving` (momentum),
`qgElimFull_number_conserving` (the one-particle operator of each mode, so that every
particle-number sector is preserved), `qgElimFull_stone_flow` and `starobinsky_qgElimFull_stone_flow`
(the single-time package by Stone's theorem). The model is not degenerate:
`elimCoef_torsion_ne_zero`, `elimCoef_gauge3d_ne_zero`, `eGram_diag_ne_zero` and `eCoupling_ne_zero`
exhibit non-vanishing torsion, transverse gauge and trace coupling at non-zero momentum and coupling,
and `infinite_egmode` records that the eliminated mode set is infinite, so the outer Fock space is a
genuine infinite-dimensional one.
:::

```
#check @BookProof.QgFullEliminated.qgElimFull_momentum_conserving
#check @BookProof.QgFullEliminated.qgElimFull_number_conserving
#check @BookProof.QgFullEliminated.qgElimFull_stone_flow
#check @BookProof.QgFullEliminated.starobinsky_qgElimFull_stone_flow
#check @BookProof.QgFullEliminated.eCoupling_ne_zero
#check @BookProof.QgFullEliminated.elimCoef_gauge3d_ne_zero
#check @BookProof.QgFullEliminated.infinite_egmode
```

# What This Doctrines, and What It Leaves Open

:::paragraph
The verified layer:

 * the derivative variables of the vielbein sector carry **no independent content**: the constraint
   surface is exactly the image of the elimination (`formValue_dGauge_elimConfig`,
   `eq_elimConfig_of_gauge_fixed`), the eliminated torsion is the physical torsion
   (`elimTorsion_eq_torsionCoef`), and the vielbein self-interaction is reproduced verbatim
   (`elimGram_eq_contTorsionGram`);
 * the full model — $`R^2` vielbein, full exponential wall, interaction terms — is essentially
   self-adjoint on the nine-component representation with arbitrary coupling, both on the Friedrichs
   domain and on the finite-occupation core (`qgElimFull_esa_farisLavine`,
   `qgElimFull_esa_core_fl`, `starobinsky_qgElimFull_esa`, `starobinsky_qgElimFull_esa_core`), with
   momentum and particle number conserved and the Stone flow available;
 * the BRST material is thereby *restated*, not discarded: it survives as the consistency check that
   the elimination agrees with the gauge reduction (`elimTorsion_eq_gaugeReduce`).

Open items, as obligations:

 * the coupling across *differing bases* — the plan's `Σ_ℓ dΓ(h_ℓ)` — is proved separately, and its
   `ℓ¹`-free comparison is what makes the multi-gauge-sector model a single second-quantized operator;
 * the numerical twin's term lists and the eliminated presentation are compared structurally rather
   than term-by-term for the gravity kinetic forms, which is the honest status of that cross-check;
 * the decoupling of the scalaron and vielbein one-particle operators in the *fiber* model is an
   assumption, not a theorem; the eliminated full model does not need it, but the closed-form
   spectrum of the fiber model does.
:::
