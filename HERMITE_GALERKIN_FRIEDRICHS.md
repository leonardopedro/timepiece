# Hermite-basis Galerkin truncation and the Friedrichs extension — what was formalized

Lean module: `BookProof/ChapterHermiteGalerkinFriedrichs.lean`
(namespace `BookProof.HermiteGalerkin`; `sorry`-free, no new axioms — every
result below depends only on `propext`, `Classical.choice`, `Quot.sound`, as
certified in `BookProof/ChapterRoadmapAudit.lean`).

The prose argument was: *a Krylov/Galerkin algorithm run in the Hermite basis
performs a Rayleigh–Ritz minimization of the energy form, the finite energy
minimizations exhaust the form domain, and therefore the truncated resolvents
converge to the resolvent of the Friedrichs extension — no boundary condition
has to be supplied.*  Here is the claim-by-claim correspondence.

## §1 The Rayleigh–Ritz connection (formalized, no boundedness needed)

| Prose | Lean |
| --- | --- |
| step `m` builds `Hₘ = Pₘ H Pₘ` | `galerkinSpan`, `galerkinCompression` |
| the finite matrix *is* the energy form on the subspace | `inner_galerkinCompression`, `quadForm_galerkinCompression` |
| minimizing `⟨ψ,Hψ⟩` on the subspace | `ritzSet`, `ritzInf` |
| enlarging the subspace lowers the minimum | `ritzInf_antitone` |
| the minima converge to the bottom of the form | `ritzInf_tendsto_domainInf` |
| the limit dominates the bottom of every self-adjoint extension | `ritzInf_extension_le` |

The last two are the precise sense in which the algorithm's ground-state
estimate is the bottom of the *form* of `H` rather than of some other
extension: every positive self-adjoint extension has its energy bounded above
by that number, and the extension attaining it is the one whose form is the
closure of the form of `H`.

## §2 Completeness of the Hermite basis (formalized)

| Prose | Lean |
| --- | --- |
| `Pₘ → I` because the basis is complete | `galerkinProj_tendsto` (via `starProjection_tendsto_of_monotone_dense`) |
| the flag exhausts the domain where the matrix elements live | `exists_mem_galerkinSpan`, `finiteModeDomain_eq_iSup`, `finiteModeDomain_dense` |
| the domain is a genuine (proper) dense subspace | `finiteModeDomain_ne_top` (in `ℓ²(ℕ,ℂ)`) |

The Hermite basis enters only through orthonormality and completeness, so the
statements are proved for an arbitrary Hilbert basis indexed by `ℕ`;
`ell2Basis` is the canonical `ℓ²(ℕ,ℂ)` model of it.

## §3 The limit is the Friedrichs extension (formalized in the bounded regime)

| Prose | Lean |
| --- | --- |
| `Pₘ A Pₘ → A` strongly | `galerkinCompression_tendsto`, `compression_tendsto_of_starProjection_tendsto` |
| `(Pₘ A Pₘ − z)⁻¹ → (A − z)⁻¹` strongly for `Im z ≠ 0` | `resolvent_tendsto_of_strong_tendsto`, `galerkinResolvent_tendsto` |
| the resolvent bound `‖(A − z)⁻¹‖ ≤ 1/|Im z|` behind it | `norm_sub_smul_ge`, `isUnit_algebraMap_sub`, `norm_resolvent_apply_le` |
| the algorithm has no freedom: the extension is unique | `positive_selfadjoint_extension_unique` |
| everything combined | `hermiteGalerkin_selects_friedrichs` |
| feeding in the matrix elements of a bounded operator recovers that operator | `finiteModeRestrict_hypotheses`, `finiteModeRestrict_selects_operator` |

The construction of the extension itself is the one already in
`BookProof/ChapterYangMillsFriedrichsLimit.lean` (`friedrichs_of_bounded`).

## What is *not* claimed

* Every statement in §3 carries an explicit **boundedness hypothesis** on the
  operator on its domain.  For a genuinely unbounded, non-essentially-self-adjoint
  Hamiltonian the identification of the Galerkin limit with the Friedrichs
  extension is **not proved here**; only §1 and §2 (the variational content) are
  unconditional.  In particular no claim is made that the Hermite truncation of
  such a Hamiltonian converges to `e^{-i H_F t}`.
* Nothing about the indeterminate **Stieltjes moment problem**, Padé
  approximants, or Nevanlinna-extremal measures (the "moment trick" paragraph of
  the informal argument) is formalized.
* No claim about the continuum Yang–Mills operator, a mass gap, or global
  existence; those scopes are unchanged from the earlier work in this project.
