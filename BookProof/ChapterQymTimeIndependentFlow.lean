import Mathlib
import BookProof.ChapterFiniteSectionSingleTime
import BookProof.Toolbox.ChapterFockSecondQuantization
import BookProof.Qg.ChapterQgCouplingDGammaSum
import BookProof.Toolbox.ChapterFockWeightedSchurEsa

/-!
# The Weyl-gauge quantum Yang–Mills Hamiltonian is time-independent, and one finite time
# suffices

This is the quantum Yang–Mills counterpart of `BookProof.ChapterQgTimeIndependentFlow`
(quantum gravity) and `BookProof.ChapterNsTimeIndependentFlow` (Navier–Stokes).

In the **Weyl gauge** `A₀ = 0` the gauge-fixed Yang–Mills Hamiltonian is the sum of squares
of the *spatial* electric and magnetic field operators,

`H₁ = ½ Σ_m (π_m)² + ½ Σ_m (B_m)²`

(`BookProof.YangMillsHermite.ymHamiltonian`, with the sum-of-squares form
`ymHamiltonian_quadForm`).  The gauge condition removes the time component of the connection
outright: no time derivative and no time parameter enters, so the quantized Hamiltonian —
and its second quantization `dΓ(H₁)` on the Fock space over the Gauss–polynomial core of
`L²(ℝ⁹⁹)` — is a single fixed self-adjoint operator, an **autonomous** generator.  The
BRST-exact gauge-fixing term `{Ω, Ψ}` that `book.tex` may add to the 4D Hamiltonian
vanishes on this slice (`BookProof.BookBrstGaugeFixing.bookGfTerm_eq_zero_of_Afield0`,
QYM instance `su2_bookGfTerm_eq_zero_of_Afield0` in `ChapterBookBrstInstances.lean`), so
the spatial-only record of `H₁` already accounts for the gauge-fixing/ghost sector — no
extra summand in `h` or `N`.  Combined
with `BookProof.ChapterSirkSingleTimeShift` (the SIRK/Hashimoto algorithm evaluates the
propagator at *one* finite time through the bounded shift-invert resolvent) this removes any
need for a discretization of time.

## What is proved

* **`ymFock_weylGauge_timeIndependent`** — unconditionally, for the physical second-quantized
  Yang–Mills Hamiltonian `dΓ(H₁)`: the Weyl-gauge sum-of-squares identity (first conjunct,
  the gauge-fixing content: only spatial fields occur), and a self-adjoint extension `T`
  (the one the Friedrichs construction produces), whose propagator `U(t,s) = e^{−i(t−s)H}` is
  unitary,
  satisfies Chapman–Kolmogorov, is **time-translation invariant** and **uniquely** solves the
  Schrödinger equation of the one fixed generator.  No time ordering and no Dyson series
  occurs.
* **`ymFock_timeIndependent_singleTime_of_esa`** — the full package, including the
  approximation half: given essential self-adjointness of `dΓ(H₁)` on the finite-occupation
  core, the finite sections (Galerkin truncations in the occupation basis) have self-adjoint
  realizations whose Hashimoto shift-invert operators converge at **every** nonzero shift,
  and whose propagators converge to the exact one at **every single finite time**.
* **`ymFock_diagonalBasis_timeIndependent_singleTime`** — the same *unconditionally* whenever
  the working basis diagonalizes the one-particle Yang–Mills Hamiltonian with non-negative
  eigenvalues (`ymFockCol e fabc = diagCol lam`), since then `dΓ(H₁)` is essentially
  self-adjoint on the finite-occupation core
  (`BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_essentiallySelfAdjoint`).
* `exists_confEnum` — the enumeration of the occupation configurations used to build the
  windows exists, so the statements are not vacuous.

## Honest boundary

Unchanged from the rest of the Yang–Mills thread: **no mass gap** and no spectral information
is claimed, the cubic and quartic self-interaction of the one-particle operator is the one
recorded in `BookProof.YangMillsHermite`, and the essential self-adjointness of `dΓ(H₁)` on
the finite-occupation core is a hypothesis (only the Friedrichs extension is unconditional) —
it is discharged exactly when the working basis diagonalizes the one-particle operator.  What
is proved is the evolution statement: the generator carries no time dependence, and the
algorithm evaluates its propagator at a single finite time through a bounded shift-invert
resolvent.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QymTimeIndependent

open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.HashimotoShiftInvert BookProof.SirkSingleTime BookProof.QgTimeIndependent
open BookProof.FiniteSectionSingleTime BookProof.YangMillsFriedrichs
open BookProof.FockSecondQuantization BookProof.QgCouplingDGammaSum
open BookProof.YangMillsHermite BookProof.HermiteGalerkin BookProof.HermiteProductCore
open BookProof.NavierStokesFlow

noncomputable section

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

/-- The matrix of the one-particle Yang–Mills Hamiltonian in the product Hermite basis is
Hermitian. -/
theorem isHermCol_ymFockCol : IsHermCol (ymFockCol e fabc) :=
  isHermCol_opCol (ymHamiltonian_symmetricOn (coreRepBasis e) fabc)

theorem dGammaOp_ymFockCol_symmetricOn :
    SymmetricOn (lpFiniteModes Conf) (dGammaOp (ymFockCol e fabc)) :=
  dGammaOp_symmetricOn (isHermCol_ymFockCol e fabc)

/-! ## 1. The Weyl gauge: an autonomous generator -/

/-- **The Weyl-gauge Yang–Mills Hamiltonian is time-independent.**

The first conjunct is the gauge-fixing content itself: in the Weyl gauge `A₀ = 0` the
one-particle Hamiltonian is the sum of squares of the *spatial* electric and magnetic field
operators, `⟪x, H₁ x⟫ = ½ Σ ‖π_m x‖² + ½ Σ ‖B_m x‖²`; no time component of the connection and
no time derivative occurs.  Consequently its second quantization `dΓ(H₁)` is one fixed
positive self-adjoint operator `T` — the statement asserts `IsSelfAdjointExtension`, and
`ymFock_dGamma_extension_eq_closure` below identifies every such extension with the closure
`clExt` as soon as `dΓ(H₁)` is essentially self-adjoint, so the operator is then not selected
but determined — and the remaining conjuncts say that its
propagator `U(t,s) = e^{−i(t−s)H}` is unitary, obeys Chapman–Kolmogorov, is invariant under a
common shift of both times and uniquely solves the Schrödinger equation — so the evolution
problem is the evaluation of one unitary group at one finite time, with no time ordering and
no Dyson series. -/
theorem ymFock_weylGauge_timeIndependent :
    (∀ x : finiteModeDomain (coreBasis e),
        quadForm (ymHamiltonian (coreRepBasis e) fabc) x
          = 1 / 2 * (∑ m, ‖((piOps (coreRepBasis e) m x : finiteModeDomain (coreBasis e)) :
              L2d 99)‖ ^ 2)
            + 1 / 2 * ∑ m, ‖((magOps (coreRepBasis e) fabc m x :
                finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2) ∧
      ∃ T : UnboundedSelfAdjoint Fock,
        IsSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) T.op ∧
          (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
          (∀ (t s : ℝ) (x : Fock), ‖prop T t s x‖ = ‖x‖) ∧
          (∀ (t s r : ℝ) (x : Fock), prop T t s (prop T s r x) = prop T t r x) ∧
          (∀ t s u : ℝ, prop T (t + u) (s + u) = prop T t s) ∧
          (∀ y : ℝ → Fock, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) := by
  refine ⟨fun x => ymHamiltonian_quadForm (coreRepBasis e) fabc x, ?_⟩
  obtain ⟨Dom, A, hA⟩ := ym_fock_friedrichs_extension e fabc
  exact timeIndependent_of_selfAdjointExtension finiteOccupation_dense
    (isSelfAdjointExtension_of_positive hA)

/-! ## 2. The finite sections: one shift, one finite time -/

/-- **The Yang–Mills finite-section scheme needs no discretization of time.**  Given essential
self-adjointness of `dΓ(H₁)` on the finite-occupation core — the hypothesis that selects the
generator without appealing to the Friedrichs construction — the exact Hamiltonian and its
finite sections in the occupation basis have self-adjoint realizations, the propagator of the
exact one is time-translation invariant and uniquely solves the Schrödinger equation, the
Hashimoto shift-invert operators of the finite sections converge at **every** nonzero shift,
and their propagators converge to the exact one at **every single finite time**. -/
theorem ymFock_timeIndependent_singleTime_of_esa (en : ℕ ≃ Conf)
    (hesa : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (ymFockCol e fabc))) :
    ∃ (T : UnboundedSelfAdjoint Fock) (S : ℕ → UnboundedSelfAdjoint Fock),
      IsSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) T.op ∧
        (∀ n, IsSelfAdjointExtension
          (((secOp (dGammaOp (ymFockCol e fabc)) (windowOfEquiv en n) :
              Fock →ₗ[ℂ] Fock)).comp (lpFiniteModes Conf).subtype) (S n).op) ∧
        (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
        (∀ (t s : ℝ) (x : Fock), ‖prop T t s x‖ = ‖x‖) ∧
        (∀ (t s r : ℝ) (x : Fock), prop T t s (prop T s r x) = prop T t r x) ∧
        (∀ t s u : ℝ, prop T (t + u) (s + u) = prop T t s) ∧
        (∀ y : ℝ → Fock, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧
            ∀ u : Fock, Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : Fock) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) :=
  finiteSection_singleTime (dGammaOp (ymFockCol e fabc))
    (dGammaOp_ymFockCol_symmetricOn e fabc) hesa (windowOfEquiv_exhausts en)

/-- **The ESA of `dΓ(H₁)`, reduced to the one-particle symbol gates.**  The obstruction to
proving `EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (ymFockCol e fabc))` outright is
not the Fock space: `dGamma_essentiallySelfAdjointOn_core_w` (weighted Schur test, §Toolbox)
makes the second quantization essentially self-adjoint on the finite-occupation core as soon as
the one-particle matrix satisfies three quantitative gates against a symbol `w ≥ 1` — rows
`∑_j |A_{kj}| ≤ K w_k`, columns `∑_k |A_{jk}| / w_k ≤ K`, and the commutator gate
`∑_j |A_{kj}| |w_j² − w_k²| / (w_k w_j) ≤ B`.  This theorem is the instantiation for the
physical Yang–Mills matrix, so what remains is exactly those three estimates for `ymFockCol`.
They are *not* proved here: `ymFockCol` is the matrix of the quartic one-particle Hamiltonian, so
its rows do not decay (the unweighted `SchurBound` gate of `ChapterFockSchurEsa` cannot hold) and
the weighted gates are genuine analytic estimates in the product Hermite basis. -/
theorem ymFockCol_essentiallySelfAdjointOn_core_of_symbolGates {w : ℕ → ℝ} (hw : ∀ k, 1 ≤ w k)
    {K B : ℝ} (hK0 : 0 ≤ K)
    (hrow : BookProof.FockWeightedSchur.WRowBound w (ymFockCol e fabc) K)
    (hcolg : BookProof.FockWeightedSchur.WColBound w (ymFockCol e fabc) K)
    (hbg : BookProof.FockWeightedSchur.WCommBound w (ymFockCol e fabc) B) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (ymFockCol e fabc)) :=
  BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w
    hw (isHermCol_ymFockCol e fabc) hrow hcolg hK0 hbg

/-- **The ESA of `dΓ(H₁)` from the row estimate alone.**  With the unweighted symbol `w ≡ 1` the
column gate coincides with the row gate (`wColBound_one_of_wRowBound_one`) and the commutator gate
is free (`wCommBound_one`), so the three symbol gates of
`ymFockCol_essentiallySelfAdjointOn_core_of_symbolGates` collapse to the single ℓ¹ row estimate

  `∀ k, ∑_{j} |(ymFockCol e fabc k) j| ≤ K`.

That is the minimal form of what is still missing for the physical matrix. -/
theorem ymFockCol_essentiallySelfAdjointOn_core_of_rowBound {K : ℝ} (hK : 0 ≤ K)
    (hrow : BookProof.FockWeightedSchur.WRowBound (fun _ => 1) (ymFockCol e fabc) K) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (ymFockCol e fabc)) :=
  ymFockCol_essentiallySelfAdjointOn_core_of_symbolGates (e := e) (fabc := fabc)
    (w := fun _ => 1) (K := K) (B := 1) (fun _ => le_rfl) hK hrow
    (BookProof.FockWeightedSchur.wColBound_one_of_wRowBound_one hrow)
    (BookProof.FockWeightedSchur.wCommBound_one _ zero_le_one)


/-- **The YM generator is determined, not selected.**  Whenever `dΓ(H₁)` is essentially
self-adjoint on the finite-occupation core — the hypothesis of
`ymFock_timeIndependent_singleTime_of_esa` — *every* self-adjoint extension of it has the domain
of the closure and agrees with `clExt` there.  So the flow of that theorem, when it exists, is
the flow of a determined operator, and the Friedrichs realisation is not a choice: it coincides
with the closure.  Without the essential-self-adjointness hypothesis nothing here applies; for the
physical `ymFockCol` that hypothesis is not proved, and
`ymFockCol_essentiallySelfAdjointOn_core_of_symbolGates` reduces it to the three symbol gates
(row, column and commutator) for the Yang–Mills matrix. -/
theorem ymFock_dGamma_extension_eq_closure
    (hesa : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (ymFockCol e fabc)))
    {Dom : Submodule ℂ Fock} {A : Dom →ₗ[ℂ] Fock}
    (hA : IsSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A) :
    Dom = clDom (dGammaOp (ymFockCol e fabc)) ∧
      ∀ (x : Fock) (h : x ∈ Dom) (h' : x ∈ clDom (dGammaOp (ymFockCol e fabc))),
        A ⟨x, h⟩ = clExt (dGammaOp (ymFockCol e fabc)) finiteOccupation_dense
          (dGammaOp_ymFockCol_symmetricOn e fabc) ⟨x, h'⟩ :=
  isSelfAdjointExtension_unique_of_esa hesa hA
    ⟨fun v => ⟨coe_mem_clDom _ v, clExt_extends _ _ _ v⟩,
      clExt_symmetricOn _ _ _, clExt_selfAdjointCriterion _ _ _ hesa⟩

/-- **The unconditional instance: a basis diagonalizing the one-particle Hamiltonian.**  If
the product Hermite basis diagonalizes the gauge-fixed one-particle Yang–Mills Hamiltonian
with non-negative eigenvalues `lam`, then `dΓ(H₁)` is essentially self-adjoint on the
finite-occupation core, and the whole package of
`ymFock_timeIndependent_singleTime_of_esa` holds with no further hypothesis. -/
theorem ymFock_diagonalBasis_timeIndependent_singleTime (en : ℕ ≃ Conf) (lam : ℕ → ℝ)
    (hlam : ∀ k, 0 ≤ lam k) (hdiag : ymFockCol e fabc = diagCol lam) :
    ∃ (T : UnboundedSelfAdjoint Fock) (S : ℕ → UnboundedSelfAdjoint Fock),
      IsSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) T.op ∧
        (∀ n, IsSelfAdjointExtension
          (((secOp (dGammaOp (ymFockCol e fabc)) (windowOfEquiv en n) :
              Fock →ₗ[ℂ] Fock)).comp (lpFiniteModes Conf).subtype) (S n).op) ∧
        (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
        (∀ (t s : ℝ) (x : Fock), ‖prop T t s x‖ = ‖x‖) ∧
        (∀ (t s r : ℝ) (x : Fock), prop T t s (prop T s r x) = prop T t r x) ∧
        (∀ t s u : ℝ, prop T (t + u) (s + u) = prop T t s) ∧
        (∀ y : ℝ → Fock, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧
            ∀ u : Fock, Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : Fock) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by
  refine ymFock_timeIndependent_singleTime_of_esa e fabc en ?_
  rw [hdiag]
  exact dGammaOp_diagCol_essentiallySelfAdjoint hlam

/-- The configurations are enumerable, so the window family used above exists: the statements
are not vacuous. -/
theorem exists_confEnum : Nonempty (ℕ ≃ Conf) := nonempty_equiv_of_countable

end

end BookProof.QymTimeIndependent
