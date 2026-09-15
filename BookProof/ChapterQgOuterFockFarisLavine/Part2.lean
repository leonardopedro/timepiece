import Mathlib
import BookProof.ChapterQgOuterFockEsa
import BookProof.ChapterFriedrichsExtension
import BookProof.ChapterQgOuterFockFarisLavine.Part1

/-!
# Faris–Lavine on the outer Fock space: the lifted Friedrichs comparison operator

`BookProof.ChapterQgOuterFockEsa` proves that the full gauge-fixed gravity Hamiltonian is
essentially self-adjoint on the finite-particle core of the outer Fock space
`𝔉 = ⊕ₙ L²(ℝ^{84n})`, by the Carleman route sector by sector.  This module builds the
**Faris–Lavine apparatus on the outer Fock space itself**, with the comparison operator
that the strategy calls for: the Friedrichs extension of the positive one-particle
operator `N₁ = −Δ + ‖x‖²/4`, lifted to `𝔉`.

Theorem 1 of Faris–Lavine (`BookProof.ChapterFarisLavine`) needs exactly three things of
its comparison operator `N`: symmetry, positivity, and that `N + 1` maps the domain
**onto** the space — the one consequence of self-adjointness the argument uses.  The point
of this module is that all three survive the two constructions the strategy chains
together:

* **Friedrichs.**  `friedrichsComparison` packages the Friedrichs extension of
  `BookProof.ChapterFriedrichsExtension` as such a comparison operator: the extension is
  built there as `S⁻¹ − 1` for the resolvent `S = (P+1)⁻¹`, so `N + 1` is onto by
  construction.  `Comparison.selfAdjoint` shows conversely that these three properties
  *are* self-adjointness, so `Comparison.isPositiveSelfAdjointExtension` produces the
  project's `IsPositiveSelfAdjointExtension` predicate.
* **Lifting.**  `dsComparison` lifts a family of fibre comparison operators to the
  `ℓ²`-direct sum, on the maximal domain `dsDom`.  Symmetry and positivity are fibrewise
  (`dsCompOp_hasSum_quadForm`), and surjectivity of `N + 1` lifts because the fibre
  solutions obey `‖xᵢ‖ ≤ ‖(Nᵢ+1)xᵢ‖ = ‖fᵢ‖` (`norm_le_norm_shift`), so they are
  automatically square-summable (`dsCompOp_surj`).  This is the precise sense in which
  "the Friedrichs extension of the positive one-particle operator lifts to an operator on
  the outer Fock space".

## What is proved

* `Comparison`, `Comparison.selfAdjoint`, `Comparison.isPositiveSelfAdjointExtension`,
  `Comparison.essentiallySelfAdjointOn`, `Comparison.esa_self` — comparison operators and
  the Faris–Lavine criterion packaged with one; a comparison operator is essentially
  self-adjoint on its own domain (the case `H = N`, `c = 0`).
* `friedrichsComparison`, `friedrichsComparison_extends` — every densely defined positive
  symmetric operator has one, namely its Friedrichs extension.
* `dsDom`, `dsCompOp`, `dsComparison`, `dsCompOp_surj` — the lift to an `ℓ²`-direct sum.
* `dsFibOp`, `dsFibOp_symmetricOn`, `dsFibOp_hasSum_commForm`, `dsFibOp_commForm_le` — a
  fibrewise symmetric operator on the lifted domain, under a relative bound
  `‖Hᵢu‖ ≤ K‖(Nᵢ+1)u‖` uniform in the fibre; **the commutator form of the lift is the sum
  of the fibre commutator forms**, so the Faris–Lavine bound `±i[H,N] ≤ cN` lifts with the
  *same* constant `c`.
* `dsFibOp_essentiallySelfAdjointOn` — **Faris–Lavine on an `ℓ²`-direct sum**: uniform
  fibre data gives essential self-adjointness of the direct-sum operator on the lifted
  domain.
* `harmPosSym`, `harmFried`, `harmFried_isPositiveSelfAdjointExtension` — the positive
  one-particle gravity operator `N₁ = −Δ + ‖x‖²/4` and its Friedrichs extension.
* `qgOuterComparison`, `qgOuterFriedDom`, `qgOuterFriedN`, `qgOuterFriedN_surj`,
  `qgOuterCore_le_friedDom`, `qgOuterFriedN_isPositiveSelfAdjointExtension`,
  `qgOuterFriedN_esa` — **the lifted comparison operator on the outer Fock space**: it is
  a positive self-adjoint extension of the finite-particle-core operator `dΓ(N₁)`
  (`qgOuterN`), `𝑁 + 1` is onto `𝔉`, and it is essentially self-adjoint on its domain.
* `qgOuterFock_esa_farisLavine` — **the Faris–Lavine theorem for the gravity Hamiltonian
  on the outer Fock space**: given sector realizations of the `n`-particle Hamiltonians on
  the domain of the sector comparison operator that are symmetric, relatively bounded by
  `N + 1` and satisfy `±i[H,N] ≤ cN`, all with constants uniform in the particle number,
  the lifted Hamiltonian is essentially self-adjoint on the lifted domain and extends the
  outer Fock Hamiltonian `qgOuterHam` on the finite-particle core.

## Honest boundary

The sector data of `qgOuterFock_esa_farisLavine` are hypotheses, not theorems of this
module: extending the `n`-particle quadratic Hamiltonian from the Gauss–polynomial core to
the *whole* domain of the sector oscillator, with a relative bound and a commutator bound
whose constants do not degrade as the particle number grows, is a separate analytic step
(the Hermite matrix elements of `BookProof.FullQuadratic.fqOp_hermiteCore` are the natural
route to it) and is not carried out here.  What is unconditional here is everything about
the comparison operator — the Friedrichs extension, its lift, and the fact that
Faris–Lavine applies on the outer Fock space once the sector data are supplied, with the
same constant `c` — together with the observation that uniformity in the particle number
is the only thing the lift asks for.  The *unconditional* essential self-adjointness of
the gravity Hamiltonian on the finite-particle core is proved, by the independent Carleman
route, in `BookProof.ChapterQgOuterFockEsa` (`qgOuterFock_esa`).

Everything in this module is `sorry`-free and `axiom`-free.
-/

open scoped ENNReal

namespace BookProof.QgOuterFockFL

open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore

noncomputable section
/-! ## 3. The quantum-gravity outer Fock space -/

/-- The **positive one-particle operator** `N₁ = −Δ + ‖x‖²/4` of the gravity sector, as a
densely defined positive symmetric operator on `L²(ℝᵈ)`. -/
def harmPosSym (d : ℕ) : PosSymOp (L2d d) where
  dom := polyGaussCore (d := d)
  op := harmCore
  sym := harmonicCore_symmetricOn
  pos := harmonicCore_quadForm_nonneg

/-- **The Friedrichs extension of the positive one-particle operator**, as a Faris–Lavine
comparison operator: positive, self-adjoint, and with `N₁ + 1` onto `L²(ℝᵈ)`. -/
def harmFried (d : ℕ) : Comparison (L2d d) :=
  friedrichsComparison (harmPosSym d) polyGaussCore_dense

theorem polyGaussCore_le_harmFriedDom (d : ℕ) :
    (polyGaussCore (d := d)) ≤ (harmFried d).dom := fun v hv =>
  (friedrichsComparison_extends (harmPosSym d) polyGaussCore_dense ⟨v, hv⟩).choose

/-- On the Gauss–polynomial core the Friedrichs extension is the harmonic Hamiltonian. -/
theorem harmFried_op_core (d : ℕ) (p : polyGaussCore (d := d))
    (h : (p : L2d d) ∈ (harmFried d).dom) :
    (harmFried d).op ⟨(p : L2d d), h⟩ = harmCore p :=
  (friedrichsComparison_extends (harmPosSym d) polyGaussCore_dense p).choose_spec

/-- The Friedrichs extension really is a positive self-adjoint extension of the harmonic
one-particle operator. -/
theorem harmFried_isPositiveSelfAdjointExtension (d : ℕ) :
    IsPositiveSelfAdjointExtension (harmCore (d := d)) (harmFried d).op :=
  (harmFried d).isPositiveSelfAdjointExtension harmCore
    (fun p => ⟨polyGaussCore_le_harmFriedDom d p.2, harmFried_op_core d p _⟩)

/-- **The lift of the one-particle comparison operator to the outer Fock space**: the
`ℓ²`-direct sum `⊕ₙ N₁^{(n)}` of the sector realizations of the Friedrichs extension.  It
is again positive, self-adjoint and has `𝑁 + 1` onto the whole outer Fock space, so it is
an admissible Faris–Lavine comparison operator there. -/
def qgOuterComparison : Comparison qgOuterFock :=
  dsComparison (fun n : ℕ => harmFried (n * 84))

/-- The domain of the lifted comparison operator. -/
abbrev qgOuterFriedDom : Submodule ℂ qgOuterFock := qgOuterComparison.dom

/-- The lifted comparison operator `dΓ(N₁)` on the outer Fock space. -/
abbrev qgOuterFriedN : qgOuterFriedDom →ₗ[ℂ] qgOuterFock := qgOuterComparison.op

theorem qgOuterFriedN_symmetricOn : SymmetricOn qgOuterFriedDom qgOuterFriedN :=
  qgOuterComparison.sym

theorem qgOuterFriedN_quadForm_nonneg (x : qgOuterFriedDom) : 0 ≤ quadForm qgOuterFriedN x :=
  qgOuterComparison.pos x

/-- **`𝑁 + 1` is onto the outer Fock space** — the property of the comparison operator
that the Faris–Lavine argument consumes, and the reason the lift works. -/
theorem qgOuterFriedN_surj (f : qgOuterFock) :
    ∃ x : qgOuterFriedDom, qgOuterFriedN x + (x : qgOuterFock) = f :=
  qgOuterComparison.surj f

set_option maxHeartbeats 1600000 in
-- the lifted domain is built from the Friedrichs completion, so unfolding it is costly
/-- The finite-particle core sits inside the domain of the lifted comparison operator. -/
theorem qgOuterCore_le_friedDom : qgOuterCore ≤ qgOuterFriedDom := by
  intro x hx
  refine ⟨fun n => polyGaussCore_le_harmFriedDom (n * 84) (hx.2 n), ?_⟩
  have hfun : (fun n : ℕ => opTot (harmFried (n * 84)).op ((x : qgOuterFock) n))
      = fun n : ℕ => (harmCore ⟨(x : qgOuterFock) n, hx.2 n⟩ : L2d (n * 84)) := by
    funext n
    rw [opTot_of_mem _ (polyGaussCore_le_harmFriedDom (n * 84) (hx.2 n)),
      harmFried_op_core (n * 84) ⟨(x : qgOuterFock) n, hx.2 n⟩]
  rw [hfun]
  refine memLp_of_finite_support (Set.Finite.subset hx.1 fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro h0
  refine hn ?_
  have hz : (⟨(x : qgOuterFock) n, hx.2 n⟩ : polyGaussCore (d := n * 84)) = 0 :=
    Subtype.ext h0
  rw [hz, map_zero]

/-- The lifted comparison operator, fibrewise. -/
theorem qgOuterFriedN_apply (x : qgOuterFriedDom) (n : ℕ) :
    ((qgOuterFriedN x : qgOuterFock) : ∀ n : ℕ, L2d (n * 84)) n
      = (harmFried (n * 84)).op ⟨((x : qgOuterFock) : ∀ n : ℕ, L2d (n * 84)) n, x.2.1 n⟩ :=
  dsCompOp_fib _ x n

set_option maxHeartbeats 2000000 in
-- the Friedrichs domain is a range of a completion-built resolvent: defeq checks are costly
/-- **The lifted Friedrichs extension is a positive self-adjoint extension of the lifted
one-particle operator** `⊕ₙ dΓ(N₁)` on the finite-particle core.  This is the statement
that the Friedrichs extension of the positive one-particle operator lifts to the outer
Fock space. -/
theorem qgOuterFriedN_isPositiveSelfAdjointExtension :
    IsPositiveSelfAdjointExtension qgOuterN qgOuterFriedN :=
  qgOuterComparison.isPositiveSelfAdjointExtension qgOuterN (fun x => by
    refine ⟨qgOuterCore_le_friedDom x.2, ?_⟩
    refine lp.ext (funext fun n => ?_)
    rw [qgOuterFriedN_apply, harmFried_op_core (n * 84) ⟨(x : qgOuterFock) n, x.2.2 n⟩]
    exact (dsOp_coe (fun n : ℕ => harmCore (d := n * 84)) x n).symm)

/-- **The lifted comparison operator is essentially self-adjoint on its own domain** — the
`H = N`, `c = 0` case of the Faris–Lavine criterion. -/
theorem qgOuterFriedN_esa : EssentiallySelfAdjointOn qgOuterFriedDom qgOuterFriedN :=
  qgOuterComparison.esa_self

set_option maxHeartbeats 2000000 in
-- the Friedrichs domain is a range of a completion-built resolvent: defeq checks are costly
/-- **The full gravity Hamiltonian on the outer Fock space is essentially self-adjoint by
Faris–Lavine**, with the lifted Friedrichs extension of the positive one-particle operator
as comparison operator.

The hypotheses are the sector-level Faris–Lavine data: a realization `H n` of the
`n`-particle gravity Hamiltonian on the domain of the sector comparison operator
(`hext` says it *is* a realization: on the Gauss–polynomial core it is `qgSectorHam n`),
symmetric, relatively bounded by `N + 1` with a constant `K` uniform in the particle
number, and with the commutator bound `±i[H, N] ≤ c N` with a constant `c` uniform in the
particle number.  Uniformity in `n` is what the lift needs and all that it needs. -/
theorem qgOuterFock_esa_farisLavine
    (H : ∀ n : ℕ, (harmFried (n * 84)).dom →ₗ[ℂ] L2d (n * 84))
    (hsym : ∀ n : ℕ, SymmetricOn (harmFried (n * 84)).dom (H n))
    (hext : ∀ (n : ℕ) (p : polyGaussCore (d := n * 84))
      (h : (p : L2d (n * 84)) ∈ (harmFried (n * 84)).dom),
      H n ⟨(p : L2d (n * 84)), h⟩ = qgSectorHam n p)
    (K c : ℝ) (hc : 0 ≤ c)
    (hrel : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom),
      ‖H n u‖ ≤ K * ‖(harmFried (n * 84)).op u + (u : L2d (n * 84))‖)
    (hcomm : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom),
      |commForm (H n) (harmFried (n * 84)).op u| ≤ c * quadForm (harmFried (n * 84)).op u) :
    EssentiallySelfAdjointOn qgOuterFriedDom
        (dsFibOp (fun n : ℕ => harmFried (n * 84)) H K hrel) ∧
      ∀ x : qgOuterCore, ∃ h : (x : qgOuterFock) ∈ qgOuterFriedDom,
        dsFibOp (fun n : ℕ => harmFried (n * 84)) H K hrel ⟨(x : qgOuterFock), h⟩
          = qgOuterHam x := by
  refine ⟨dsFibOp_essentiallySelfAdjointOn hc hrel hsym hcomm, fun x => ?_⟩
  refine ⟨qgOuterCore_le_friedDom x.2, ?_⟩
  refine lp.ext (funext fun n => ?_)
  have hfib : ((dsFibOp (fun n : ℕ => harmFried (n * 84)) H K hrel
        ⟨(x : qgOuterFock), qgOuterCore_le_friedDom x.2⟩ : qgOuterFock)
      : ∀ n : ℕ, L2d (n * 84)) n
      = H n ⟨((x : qgOuterFock) : ∀ n : ℕ, L2d (n * 84)) n,
          polyGaussCore_le_harmFriedDom (n * 84) (x.2.2 n)⟩ :=
    dsFibOp_fib hrel _ n
  rw [hfib, hext n ⟨(x : qgOuterFock) n, x.2.2 n⟩]
  exact (dsOp_coe (fun n : ℕ => qgSectorHam n) x n).symm

end

end BookProof.QgOuterFockFL
