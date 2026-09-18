import Mathlib
import BookProof.ChapterYangMillsHermite
import BookProof.ChapterHermiteProductBasis
import BookProof.ChapterFarisLavineCore
import BookProof.ChapterGaussCoreQuadBounds

/-!
# The mainstream Navier–Stokes Hamiltonian and why it is not bounded below

The Navier–Stokes system, written in the functional (Leray–Galerkin) form in which it is
always stated,

```
u̇ = − ν A u + B(u, u),      ⟨u, B(u, u)⟩ = 0,      div_u B = 0,
```

is a *first-order* evolution, and its Hamiltonian — the generator of the flow it induces on
wave functions, i.e. the Koopman–von Neumann (Liouville) generator

```
H_NS = ½ Σ_m (π_m F_m + F_m π_m) = −i ( Σ_m F_m ∂_m + ½ div F ),      F = − ν A u + B(u,u),
```

— is symmetric but **indefinite**: it is bounded neither below nor above.  Consequently it can
never be the *positive* comparison operator `N` of the Faris–Lavine criterion, and the shortcut
`H = N`, `c = 0` used elsewhere in this project for the auxiliary sum-of-squares operator is not
available for it.  This module proves exactly that, on the Gauss–polynomial core of `L²(ℝᵈ)`:

* `NsSystem` — the data of the mainstream system: viscosity `ν ≥ 0`, the (diagonalized) Stokes
  eigenvalues `λ_i = |k_i|² ≥ 0`, and the exact quadratic advection
  `B_i(u,u) = Σ_{j,k} b_{ijk}u_ju_k`
  subject to the two structural identities of incompressible Navier–Stokes — Leray's energy
  identity `Σ_i u_i B_i(u,u) = 0` (the advection and the pressure gradient do no work) and the
  phase-space Liouville identity `Σ_i ∂_i B_i = 0`;
* `kvnPoly` — the Hamiltonian `H_NS` above, Weyl-ordered, with the *exact* nonlinearity: no
  square of a residual, no linearization, no perturbative splitting;
* `kvnPoly_polySym` — it is symmetric on the core;
* `quadP_starP` — the antiunitary conjugation `C ψ = ψ̄` satisfies `C H_NS C = − H_NS`, so the
  numerical range of `H_NS` is symmetric about `0`: bounded below iff bounded above;
* `gpair_hermite_kvn` — the exact matrix element of `H_NS` between the one-mode Hermite states
  `|n⟩` and `|n+2⟩`.  The advection drops out of it by a parity selection rule
  (`gpair_parity`), so the element is the viscous one and grows like `n`;
* `kvn_quadP_not_bounded_below`, `nsKoopmanOp_not_bounded_below` — **the headline**: for
  `ν > 0` and one positive Stokes eigenvalue, the quadratic form of `H_NS` on the core satisfies
  `inf ⟪x, H_NS x⟫ / ‖x‖² = −∞`.  In particular `H_NS` is not positive
  (`nsKoopmanOp_not_positive`) and is not a Faris–Lavine comparison operator for itself.

`BookProof.ChapterNsKoopman.Part2` supplies the replacement comparison operator and the
Faris–Lavine commutator bound that the mainstream Hamiltonian does satisfy.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsKoopman

open MvPolynomial
open BookProof.HermiteCore BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.GaussCoreQuadBounds

noncomputable section

variable {d : ℕ}

/-! ## 1. The Gauss pairing of two core vectors -/

/-- The Gauss pairing `⟪p, q⟫ = ∫ p̄ q e^{−‖x‖²/2}`: the `L²` inner product of the two core
vectors `p·e^{−‖x‖²/4}` and `q·e^{−‖x‖²/4}`. -/
def gpair (p q : MvPolynomial (Fin d) ℂ) : ℂ := gaussInt (starP p * q)

theorem gpair_eq_inner (p q : MvPolynomial (Fin d) ℂ) :
    gpair p q = (inner ℂ (pgLp p) (pgLp q) : ℂ) := (inner_pgLp_pgLp p q).symm

theorem gpair_conj (p q : MvPolynomial (Fin d) ℂ) :
    gpair q p = (starRingEnd ℂ) (gpair p q) := by
  rw [gpair_eq_inner, gpair_eq_inner, inner_conj_symm]

theorem gpair_add_right (p q r : MvPolynomial (Fin d) ℂ) :
    gpair p (q + r) = gpair p q + gpair p r := by
  simp only [gpair, mul_add]
  exact gaussInt_add _ _

theorem gpair_smul_right (c : ℂ) (p q : MvPolynomial (Fin d) ℂ) :
    gpair p (c • q) = c * gpair p q := by
  simp only [gpair, mul_smul_comm]
  exact gaussInt_smul _ _

theorem gpair_add_left (p q r : MvPolynomial (Fin d) ℂ) :
    gpair (p + q) r = gpair p r + gpair q r := by
  simp only [gpair, starP_add, add_mul]
  exact gaussInt_add _ _

theorem gpair_smul_left (c : ℂ) (p q : MvPolynomial (Fin d) ℂ) :
    gpair (c • p) q = (starRingEnd ℂ) c * gpair p q := by
  simp only [gpair, starP_smul, smul_mul_assoc]
  exact gaussInt_smul _ _

theorem gpair_sum_right {ι : Type*} (s : Finset ι) (p : MvPolynomial (Fin d) ℂ)
    (f : ι → MvPolynomial (Fin d) ℂ) : gpair p (∑ v ∈ s, f v) = ∑ v ∈ s, gpair p (f v) := by
  classical
  induction s using Finset.induction with
  | empty => simp [gpair, gaussInt]
  | insert v s hv ih => rw [Finset.sum_insert hv, Finset.sum_insert hv, gpair_add_right, ih]

theorem norm_pgLp_sq_eq (p : MvPolynomial (Fin d) ℂ) : ‖pgLp p‖ ^ 2 = (gpair p p).re := by
  rw [gpair_eq_inner]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (pgLp p)).symm

theorem gpair_sub_right (p q r : MvPolynomial (Fin d) ℂ) :
    gpair p (q - r) = gpair p q - gpair p r := by
  rw [show q - r = q + (-1 : ℂ) • r by module, gpair_add_right, gpair_smul_right]
  ring

theorem gpair_self_nonneg (p : MvPolynomial (Fin d) ℂ) : 0 ≤ (gpair p p).re := by
  rw [← norm_pgLp_sq_eq]
  positivity

/-- The Gauss pairing of two product Hermite polynomials: the orthogonality relation. -/
theorem gpair_hermiteMv (a b : Fin d →₀ ℕ) :
    gpair (hermiteMv a) (hermiteMv b)
      = if a = b then (((∏ i, ((a i).factorial : ℝ)) * Real.sqrt (2 * Real.pi) ^ d : ℝ) : ℂ)
        else 0 := by
  rw [gpair_eq_inner, inner_pgLp_hermiteMv]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hprod : (∏ i, hermiteInner (a i) (a i))
        = (∏ i, ((a i).factorial : ℝ)) * Real.sqrt (2 * Real.pi) ^ d := by
      have : ∀ i : Fin d, hermiteInner (a i) (a i)
          = ((a i).factorial : ℝ) * Real.sqrt (2 * Real.pi) := by
        intro i; rw [hermiteInner_eq]; simp
      rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_mul_distrib]
      simp
    rw [hprod]
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ : ∃ i : Fin d, a i ≠ b i := by
      by_contra hcon
      push_neg at hcon
      exact hab (Finsupp.ext hcon)
    have hz : (∏ i, hermiteInner (a i) (b i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hermiteInner_eq, if_neg hi])
    rw [hz]
    simp

/-! ## 2. The mainstream Navier–Stokes system in Leray–Galerkin form -/

/-- The advection field `B_i(u,u) = Σ_{j,k} b_{ijk} u_j u_k` of a Galerkin form of the
incompressible Navier–Stokes equation: the exact quadratic term, with the pressure already
eliminated by the Leray projection (that elimination is what the two structural identities of
`NsSystem` record). -/
def advOf (b : Fin d → Fin d → Fin d → ℝ) (i : Fin d) : MvPolynomial (Fin d) ℂ :=
  ∑ j, ∑ k, ((b i j k : ℝ) : ℂ) • (X j * X k)

/-- **The mainstream incompressible Navier–Stokes system**, in the functional form
`u̇ = −νAu + B(u,u)` in which it is always written: `nu` is the viscosity, `lam i = |k_i|²` the
Stokes eigenvalues in the divergence-free Fourier basis, and `bcoef` the structure constants of
the exact quadratic advection.  The two hypotheses `leray` and `liouville` are the two
structural identities of the incompressible equation: the nonlinearity (advection together with
the pressure gradient) does no work on the velocity, and the phase-space flow is
volume-preserving. -/
structure NsSystem (d : ℕ) where
  /-- The kinematic viscosity `ν`. -/
  nu : ℝ
  /-- The Stokes eigenvalues `λ_i = |k_i|²`. -/
  lam : Fin d → ℝ
  /-- The structure constants of the advection `B_i(u,u) = Σ_{j,k} b_{ijk}u_ju_k`. -/
  bcoef : Fin d → Fin d → Fin d → ℝ
  nu_nonneg : 0 ≤ nu
  lam_nonneg : ∀ i, 0 ≤ lam i
  /-- **Leray's energy identity** `⟨u, B(u,u)⟩ = 0`. -/
  leray : ∑ i, X i * advOf bcoef i = (0 : MvPolynomial (Fin d) ℂ)
  /-- **The Liouville identity** `div_u B = 0`: the phase-space flow of the advection preserves
  volume. -/
  liouville : ∑ i, pderiv i (advOf bcoef i) = (0 : MvPolynomial (Fin d) ℂ)

variable (S : NsSystem d)

/-- The **drift field** of the mainstream system: the right-hand side
`F_i(u) = −ν λ_i u_i + B_i(u,u)` of the Navier–Stokes equation. -/
def drift (i : Fin d) : MvPolynomial (Fin d) ℂ :=
  -(((S.nu * S.lam i : ℝ) : ℂ) • X i) + advOf S.bcoef i

/-- **The Navier–Stokes Hamiltonian** `H_NS = ½ Σ_m (π_m F_m + F_m π_m)`: the Weyl-ordered
Koopman–von Neumann (Liouville) generator of the mainstream Navier–Stokes flow.  No square of a
residual, no linearization and no perturbative splitting occurs in it. -/
def kvnPoly : Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  ∑ i, weylProd (momOp i) (mulOp (drift S i))

/-- The total Stokes trace `ν Σ_i λ_i`, i.e. `− div F`. -/
def viscTrace : ℝ := S.nu * ∑ i, S.lam i

theorem realCoeff_neg {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) : RealCoeff (-p) := by
  change starP (-p) = -p
  rw [starP_neg, show starP p = p from hp]

theorem realCoeff_one : RealCoeff (1 : MvPolynomial (Fin d) ℂ) := map_one _

theorem realCoeff_sub {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p - q) := by
  change starP (p - q) = p - q
  rw [starP_sub, show starP p = p from hp, show starP q = q from hq]

theorem advOf_realCoeff (b : Fin d → Fin d → Fin d → ℝ) (i : Fin d) : RealCoeff (advOf b i) :=
  RealCoeff.sum fun _ _ => RealCoeff.sum fun _ _ =>
    RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _))

theorem drift_realCoeff (i : Fin d) : RealCoeff (drift S i) :=
  (realCoeff_neg (RealCoeff.smul (realCoeff_X i))).add (advOf_realCoeff S.bcoef i)

theorem polySym_zero : PolySym (0 : Module.End ℂ (MvPolynomial (Fin d) ℂ)) := by
  intro p q
  simp [gaussInt]

theorem polySym_sum {ι : Type*} {s : Finset ι} {T : ι → Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (h : ∀ i ∈ s, PolySym (T i)) : PolySym (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using polySym_zero
  | insert v s hv ih =>
      rw [Finset.sum_insert hv]
      exact (h v (Finset.mem_insert_self v s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **The Navier–Stokes Hamiltonian is symmetric on the core.** -/
theorem kvnPoly_polySym : PolySym (kvnPoly S) :=
  polySym_sum fun i _ => weylProd_polySym (momOp_polySym i) (mulOp_polySym (drift_realCoeff S i))

/-- The Weyl-ordered product of a momentum and a multiplication operator, expanded. -/
theorem weylProd_mom_mul_apply (f p : MvPolynomial (Fin d) ℂ) (i : Fin d) :
    weylProd (momOp i) (mulOp f) p
      = (-Complex.I) • (f * derOp i p + ((1 / 2 : ℝ) : ℂ) • (pderiv i f * p)) := by
  have hder : derOp i (f * p) = pderiv i f * p + f * derOp i p := by
    rw [derOp_apply, derOp_apply, pderiv_mul]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  simp only [weylProd, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    mulOp_apply, momOp, hder, mul_smul_comm]
  push_cast
  module

theorem pderiv_drift (i : Fin d) :
    pderiv i (drift S i) = -(((S.nu * S.lam i : ℝ) : ℂ) • 1) + pderiv i (advOf S.bcoef i) := by
  rw [drift, map_add, map_neg, MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_X_self]
  simp [MvPolynomial.smul_eq_C_mul]

theorem sum_pderiv_drift :
    ∑ i, pderiv i (drift S i) = ((-(viscTrace S) : ℝ) : ℂ) • (1 : MvPolynomial (Fin d) ℂ) := by
  simp only [pderiv_drift]
  rw [Finset.sum_add_distrib, S.liouville, add_zero]
  have hterm : ∀ x : Fin d,
      -((((S.nu * S.lam x : ℝ)) : ℂ) • (1 : MvPolynomial (Fin d) ℂ))
        = (((-(S.nu * S.lam x) : ℝ)) : ℂ) • (1 : MvPolynomial (Fin d) ℂ) := by
    intro x
    push_cast
    module
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_smul]
  congr 1
  rw [viscTrace, Finset.mul_sum]
  push_cast
  rw [← Finset.sum_neg_distrib]

/-- **The Hamiltonian is the Liouville generator of the Navier–Stokes flow**:
`H_NS = −i (Σ_i F_i ∂_i + ½ div F)`, and by the Liouville identity `div F = −ν Σ_i λ_i`. -/
theorem kvnPoly_apply (p : MvPolynomial (Fin d) ℂ) :
    kvnPoly S p
      = (-Complex.I) • ((∑ i, drift S i * derOp i p) + ((-(viscTrace S) / 2 : ℝ) : ℂ) • p) := by
  have hsum : kvnPoly S p = ∑ i, weylProd (momOp i) (mulOp (drift S i)) p := by
    rw [kvnPoly]
    simp
  rw [hsum, Finset.sum_congr rfl fun i _ => weylProd_mom_mul_apply (drift S i) p i,
    ← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_mul,
    sum_pderiv_drift]
  congr 2
  rw [smul_mul_assoc, one_mul, smul_smul]
  congr 1
  push_cast
  ring

/-! ## 3. The conjugation `C ψ = ψ̄` reverses the sign of the form -/

theorem starP_derOp (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (derOp i p) = derOp i (starP p) := by
  rw [derOp_apply, derOp_apply, starP_sub, starP_pderiv, starP_real_smul, starP_mul, starP_X]

/-- **`C H_NS C = − H_NS`**: the Hamiltonian anticommutes with the antiunitary conjugation, the
first-order operator being `i` times a real one. -/
theorem starP_kvnPoly (p : MvPolynomial (Fin d) ℂ) :
    starP (kvnPoly S p) = - kvnPoly S (starP p) := by
  rw [kvnPoly_apply, kvnPoly_apply, starP_smul, starP_add, starP_sum, starP_real_smul,
    Complex.conj_neg_I]
  have hterm : ∀ i : Fin d, starP (drift S i * derOp i p) = drift S i * derOp i (starP p) := by
    intro i
    rw [starP_mul, show starP (drift S i) = drift S i from drift_realCoeff S i, starP_derOp]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  module

/-- The quadratic form of the Navier–Stokes Hamiltonian at a core vector. -/
def quadP (p : MvPolynomial (Fin d) ℂ) : ℝ := (gpair p (kvnPoly S p)).re

theorem starP_starP (p : MvPolynomial (Fin d) ℂ) : starP (starP p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [starP_add, starP_add, hp, hq]
  | mul_X p i hp => rw [starP_mul, starP_X, starP_mul, starP_X, hp]

theorem gaussInt_starP (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (starP r) = (starRingEnd ℂ) (gaussInt r) := by
  rw [gaussInt, gaussInt, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [eval_starP, map_mul, Complex.conj_ofReal]

theorem gpair_starP (p q : MvPolynomial (Fin d) ℂ) :
    gpair (starP p) (starP q) = (starRingEnd ℂ) (gpair p q) := by
  rw [gpair, gpair, starP_starP, ← gaussInt_starP, starP_mul, starP_starP]

/-- **The numerical range of `H_NS` is symmetric about `0`.** -/
theorem quadP_starP (p : MvPolynomial (Fin d) ℂ) : quadP S (starP p) = - quadP S p := by
  have hH : kvnPoly S (starP p) = - starP (kvnPoly S p) := by
    have h := starP_kvnPoly S (starP p)
    rw [starP_starP] at h
    calc kvnPoly S (starP p) = starP (starP (kvnPoly S (starP p))) := (starP_starP _).symm
      _ = starP (-kvnPoly S p) := by rw [h]
      _ = - starP (kvnPoly S p) := starP_neg _
  have hneg : gpair p (-kvnPoly S p) = - gpair p (kvnPoly S p) := by
    rw [show (-kvnPoly S p) = (-1 : ℂ) • kvnPoly S p from (neg_one_smul ℂ _).symm,
      gpair_smul_right]
    ring
  rw [quadP, quadP, hH, show (-starP (kvnPoly S p)) = starP (-kvnPoly S p) from
      (starP_neg _).symm, gpair_starP, hneg]
  simp

/-- On real core vectors the form vanishes. -/
theorem quadP_of_realCoeff {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) : quadP S p = 0 := by
  have h := quadP_starP S p
  rw [show starP p = p from hp] at h
  linarith

/-- The Hamiltonian is symmetric for the Gauss pairing. -/
theorem gpair_kvn_symm (p q : MvPolynomial (Fin d) ℂ) :
    gpair (kvnPoly S p) q = gpair p (kvnPoly S q) := kvnPoly_polySym S p q

theorem gpair_expand (α β : MvPolynomial (Fin d) ℂ) (s : ℂ)
    (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    gpair (α + s • β) (T (α + s • β))
      = gpair α (T α) + s * gpair α (T β) + (starRingEnd ℂ) s * gpair β (T α)
        + (starRingEnd ℂ) s * (s * gpair β (T β)) := by
  rw [map_add, map_smul, gpair_add_left, gpair_add_right, gpair_add_right, gpair_smul_right,
    gpair_smul_left, gpair_smul_left, gpair_smul_right]
  ring

/-- The form of `H_NS` on the two-real-vector family `α + i t β`. -/
theorem quadP_real_pair {α β : MvPolynomial (Fin d) ℂ} (hα : RealCoeff α) (hβ : RealCoeff β)
    (t : ℝ) :
    quadP S (α + ((t : ℂ) * Complex.I) • β) = -2 * t * (gpair α (kvnPoly S β)).im := by
  have hA : (gpair α (kvnPoly S α)).re = 0 := quadP_of_realCoeff S hα
  have hB : (gpair β (kvnPoly S β)).re = 0 := quadP_of_realCoeff S hβ
  have hC : gpair β (kvnPoly S α) = (starRingEnd ℂ) (gpair α (kvnPoly S β)) := by
    rw [← gpair_kvn_symm, gpair_conj]
  rw [quadP, gpair_expand α β ((t : ℂ) * Complex.I) (kvnPoly S), hC]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hA, hB]
  ring

theorem gpair_real_real {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    (starRingEnd ℂ) (gpair p q) = gpair p q := by
  rw [← gpair_starP, show starP p = p from hp, show starP q = q from hq]

/-- The squared norm of the same family. -/
theorem gpair_real_pair {α β : MvPolynomial (Fin d) ℂ} (hα : RealCoeff α) (hβ : RealCoeff β)
    (t : ℝ) :
    (gpair (α + ((t : ℂ) * Complex.I) • β) (α + ((t : ℂ) * Complex.I) • β)).re
      = (gpair α α).re + t ^ 2 * (gpair β β).re := by
  have hC : gpair β α = (starRingEnd ℂ) (gpair α β) := gpair_conj α β
  have him : (gpair α β).im = 0 := by
    have h := gpair_real_real hα hβ
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hexp := gpair_expand α β ((t : ℂ) * Complex.I)
    (LinearMap.id : Module.End ℂ (MvPolynomial (Fin d) ℂ))
  simp only [LinearMap.id_coe, id_eq] at hexp
  rw [hexp, hC]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, him]
  ring

/-! ## 4. The parity selection rule -/

/-- The total degree of a multi-index. -/
def mdeg (a : Fin d →₀ ℕ) : ℕ := ∑ i, a i

/-- The span of the product Hermite polynomials of a fixed degree parity. -/
def parSpan (d : ℕ) (e : ZMod 2) : Submodule ℂ (MvPolynomial (Fin d) ℂ) :=
  Submodule.span ℂ {p | ∃ a : Fin d →₀ ℕ, ((mdeg a : ℕ) : ZMod 2) = e ∧ p = hermiteMv a}

theorem hermiteMv_mem_parSpan (a : Fin d →₀ ℕ) :
    hermiteMv a ∈ parSpan d ((mdeg a : ℕ) : ZMod 2) :=
  Submodule.subset_span ⟨a, rfl, rfl⟩

theorem mdeg_add_single (a : Fin d →₀ ℕ) (i : Fin d) :
    mdeg (a + Finsupp.single i 1) = mdeg a + 1 := by
  classical
  simp only [mdeg, Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  simp [Finsupp.single_apply]

theorem mdeg_sub_single {a : Fin d →₀ ℕ} {i : Fin d} (h : 1 ≤ a i) :
    mdeg (a - Finsupp.single i 1) + 1 = mdeg a := by
  classical
  have hsub : ∀ j : Fin d, (a - Finsupp.single i 1 : Fin d →₀ ℕ) j
      = a j - (if j = i then 1 else 0) := by
    intro j
    simp [Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]
  have hsplit : mdeg (a - Finsupp.single i 1)
      = ∑ j, (a j - (if j = i then 1 else 0)) := Finset.sum_congr rfl fun j _ => hsub j
  rw [hsplit, mdeg, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => a j) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i, (a j - (if j = i then 1 else 0))
      = ∑ j ∈ Finset.univ.erase i, a j :=
    Finset.sum_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]; omega
  rw [hrest, if_pos rfl]
  omega

theorem zmod_two_shift : ∀ x y : ZMod 2, x + 1 = y → x = y + 1 := by decide

theorem zmod_two_add_two : ∀ x : ZMod 2, x + 1 + 1 = x := by decide

theorem X_mul_mem_parSpan {e : ZMod 2} (i : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) : X i * p ∈ parSpan d (e + 1) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [hermiteMv_X_mul]
      have h1 : hermiteMv (a + Finsupp.single i 1) ∈ parSpan d (e + 1) := by
        refine Submodule.subset_span ⟨a + Finsupp.single i 1, ?_, rfl⟩
        rw [mdeg_add_single, ← ha]
        push_cast
        ring
      refine add_mem h1 ?_
      rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
      · simp [h0]
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a - Finsupp.single i 1, ?_, rfl⟩)
        have hd := mdeg_sub_single (a := a) (i := i) hpos
        refine zmod_two_shift _ _ ?_
        rw [← ha, ← hd]
        push_cast
        ring
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem pderiv_mem_parSpan {e : ZMod 2} (i : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) : pderiv i p ∈ parSpan d (e + 1) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [pderiv_hermiteMv]
      rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
      · simp [h0]
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a - Finsupp.single i 1, ?_, rfl⟩)
        have hd := mdeg_sub_single (a := a) (i := i) hpos
        refine zmod_two_shift _ _ ?_
        rw [← ha, ← hd]
        push_cast
        ring
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
      rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, ← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ hx

theorem derOp_mem_parSpan {e : ZMod 2} (i : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) : derOp i p ∈ parSpan d (e + 1) := by
  rw [derOp_apply]
  exact sub_mem (pderiv_mem_parSpan i hp)
    (Submodule.smul_mem _ _ (X_mul_mem_parSpan i hp))

theorem X_X_mul_mem_parSpan {e : ZMod 2} (j k : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) : X j * X k * p ∈ parSpan d e := by
  have h := X_mul_mem_parSpan j (X_mul_mem_parSpan k hp)
  rw [zmod_two_add_two e] at h
  rw [mul_assoc]
  exact h

/-- Multiplication by the (quadratic) advection field preserves the degree parity. -/
theorem advOf_mul_mem_parSpan {e : ZMod 2} (b : Fin d → Fin d → Fin d → ℝ) (i : Fin d)
    {p : MvPolynomial (Fin d) ℂ} (hp : p ∈ parSpan d e) : advOf b i * p ∈ parSpan d e := by
  rw [advOf, Finset.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Finset.sum_mul]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [smul_mul_assoc]
  exact Submodule.smul_mem _ _ (X_X_mul_mem_parSpan j k hp)

/-- **The parity selection rule**: core vectors of different degree parity are orthogonal. -/
theorem gpair_parity {e e' : ZMod 2} (hee : e ≠ e') {p q : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) (hq : q ∈ parSpan d e') : gpair p q = 0 := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      induction hq using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨c, hc, rfl⟩ := hy
          have hne : a ≠ c := by
            intro hac
            exact hee (ha ▸ hac ▸ hc.symm ▸ rfl)
          rw [gpair_hermiteMv, if_neg hne]
      | zero => simp [gpair, gaussInt]
      | add u v _ _ hu hv => rw [gpair_add_right, hu, hv, add_zero]
      | smul c u _ hu => rw [gpair_smul_right, hu, mul_zero]
  | zero => simp [gpair, gaussInt]
  | add u v _ _ hu hv => rw [gpair_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [gpair_smul_left, hu, mul_zero]

/-! ## 5. The matrix element between the one-mode Hermite states `|n⟩` and `|n+2⟩` -/

theorem realCoeff_prod {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin d) ℂ}
    (h : ∀ i ∈ s, RealCoeff (f i)) : RealCoeff (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using realCoeff_one
  | insert v s hv ih =>
      rw [Finset.prod_insert hv]
      exact (h v (Finset.mem_insert_self v s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem realCoeff_hermiteFactor (i : Fin d) (n : ℕ) : RealCoeff (hermiteFactor i n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simpa [hermiteFactor_zero] using (realCoeff_one (d := d))
      | (m + 1) =>
          have h := hermiteFactor_X_mul i m
          have heq : hermiteFactor i (m + 1)
              = X i * hermiteFactor i m - (((m : ℝ)) : ℂ) • hermiteFactor i (m - 1) := by
            rw [h]
            push_cast
            module
          rw [heq]
          exact realCoeff_sub ((realCoeff_X i).mul (ih m (by omega)))
            (RealCoeff.smul (ih (m - 1) (by omega)))

theorem realCoeff_hermiteMv (a : Fin d →₀ ℕ) : RealCoeff (hermiteMv a) :=
  realCoeff_prod fun i _ => realCoeff_hermiteFactor i (a i)

/-! ### The one-mode multi-indices -/

/-- The multi-index with `m` quanta in the mode `i₀` and none elsewhere. -/
def st (i0 : Fin d) (m : ℕ) : Fin d →₀ ℕ := Finsupp.single i0 m

@[simp] theorem st_apply_self (i0 : Fin d) (m : ℕ) : st i0 m i0 = m := by
  simp [st]

theorem st_apply_other {i0 i : Fin d} (h : i ≠ i0) (m : ℕ) : st i0 m i = 0 := by
  simp [st, Ne.symm h]

theorem st_add_single (i0 : Fin d) (m : ℕ) :
    st i0 m + Finsupp.single i0 1 = st i0 (m + 1) := by
  rw [st, st, ← Finsupp.single_add]

theorem st_sub_single (i0 : Fin d) (m : ℕ) :
    st i0 m - Finsupp.single i0 1 = st i0 (m - 1) := by
  classical
  ext j
  by_cases hj : j = i0
  · subst hj; simp [st, Finsupp.tsub_apply]
  · simp [st, Finsupp.tsub_apply, Ne.symm hj]

theorem st_ne_st {i0 : Fin d} {m m' : ℕ} (h : m ≠ m') : st i0 m ≠ st i0 m' := by
  intro hc
  exact h (by simpa using congrArg (fun a : Fin d →₀ ℕ => a i0) hc)

theorem st_ne_add_other {i0 i : Fin d} (h : i ≠ i0) (m m' : ℕ) (c : ℕ) (hc : c ≠ 0) :
    st i0 m ≠ st i0 m' + Finsupp.single i c := by
  intro hcon
  have := congrArg (fun a : Fin d →₀ ℕ => a i) hcon
  simp [st, Ne.symm h] at this
  exact hc this.symm

/-- The squared norm of the one-mode Hermite state `|m⟩`. -/
theorem gpair_st_self (i0 : Fin d) (m : ℕ) :
    gpair (hermiteMv (st i0 m)) (hermiteMv (st i0 m))
      = (((m.factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ d : ℝ) : ℂ) := by
  classical
  rw [gpair_hermiteMv, if_pos rfl]
  congr 2
  rw [show ((m.factorial : ℝ)) = ((((st i0 m) i0).factorial : ℕ) : ℝ) by rw [st_apply_self]]
  exact Finset.prod_eq_single i0 (fun j _ hj => by rw [st_apply_other hj]; simp)
    (fun h => absurd (Finset.mem_univ i0) h)

theorem gpair_neg_right (p q : MvPolynomial (Fin d) ℂ) : gpair p (-q) = - gpair p q := by
  rw [show (-q) = (-1 : ℂ) • q from (neg_one_smul ℂ q).symm, gpair_smul_right]
  ring

theorem mdeg_st (i0 : Fin d) (m : ℕ) : mdeg (st i0 m) = m := by
  classical
  rw [mdeg, Finset.sum_eq_single i0 (fun j _ hj => st_apply_other hj m)
    (fun h => absurd (Finset.mem_univ i0) h), st_apply_self]

theorem gpair_alpha_st (i0 : Fin d) (n m : ℕ) (hm : m ≠ n + 2) :
    gpair (hermiteMv (st i0 (n + 2))) (hermiteMv (st i0 m)) = 0 := by
  rw [gpair_hermiteMv, if_neg (st_ne_st (Ne.symm hm))]

theorem st_ne_of_apply {a : Fin d →₀ ℕ} {i0 i : Fin d} (h : i ≠ i0) {m : ℕ} (hai : a i ≠ 0) :
    st i0 m ≠ a := fun hc => hai (by rw [← hc, st_apply_other h])

theorem X_mul_st (i0 : Fin d) (m : ℕ) :
    X i0 * hermiteMv (st i0 m)
      = hermiteMv (st i0 (m + 1)) + (m : ℂ) • hermiteMv (st i0 (m - 1)) := by
  rw [hermiteMv_X_mul, st_add_single, st_sub_single, st_apply_self]

theorem pderiv_st (i0 : Fin d) (m : ℕ) :
    pderiv i0 (hermiteMv (st i0 m)) = (m : ℂ) • hermiteMv (st i0 (m - 1)) := by
  rw [pderiv_hermiteMv, st_sub_single, st_apply_self]

theorem pderiv_st_other {i0 i : Fin d} (h : i ≠ i0) (m : ℕ) :
    pderiv i (hermiteMv (st i0 m)) = 0 := by
  rw [pderiv_hermiteMv, st_apply_other h]
  simp

theorem X_mul_st_other {i0 i : Fin d} (h : i ≠ i0) (m : ℕ) :
    X i * hermiteMv (st i0 m) = hermiteMv (st i0 m + Finsupp.single i 1) := by
  rw [hermiteMv_X_mul, st_apply_other h]
  simp

/-- **The advection contributes nothing to the matrix element**: its parity is wrong. -/
theorem gpair_adv_vanishes (i0 : Fin d) (n : ℕ) (i : Fin d) :
    gpair (hermiteMv (st i0 (n + 2))) (advOf S.bcoef i * derOp i (hermiteMv (st i0 n))) = 0 := by
  have hshift : ((n + 2 : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2) := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    push_cast
    rw [h2, add_zero]
  have hne : (((n + 2 : ℕ) : ℕ) : ZMod 2) ≠ ((n : ℕ) : ZMod 2) + 1 := by
    rw [hshift]
    have hx : ∀ x : ZMod 2, x ≠ x + 1 := by decide
    exact hx _
  refine gpair_parity hne ?_ ?_
  · have h := hermiteMv_mem_parSpan (st i0 (n + 2))
    rwa [mdeg_st] at h
  · refine advOf_mul_mem_parSpan _ _ (derOp_mem_parSpan i ?_)
    have h := hermiteMv_mem_parSpan (st i0 n)
    rwa [mdeg_st] at h

/-- The viscous term of a mode other than `i₀` contributes nothing either. -/
theorem gpair_visc_other (i0 : Fin d) (n : ℕ) {i : Fin d} (h : i ≠ i0) :
    gpair (hermiteMv (st i0 (n + 2))) (X i * derOp i (hermiteMv (st i0 n))) = 0 := by
  have hd : derOp i (hermiteMv (st i0 n))
      = -(((1 / 2 : ℝ) : ℂ) • hermiteMv (st i0 n + Finsupp.single i 1)) := by
    rw [derOp_apply, pderiv_st_other h, X_mul_st_other h]
    module
  have haii : ((st i0 n + Finsupp.single i 1 + Finsupp.single i 1 : Fin d →₀ ℕ) i) ≠ 0 := by
    simp [st_apply_other h]
  have hX : X i * hermiteMv (st i0 n + Finsupp.single i 1)
      = hermiteMv (st i0 n + Finsupp.single i 1 + Finsupp.single i 1)
        + (1 : ℂ) • hermiteMv (st i0 n) := by
    rw [hermiteMv_X_mul]
    congr 2
    · simp [st_apply_other h]
    · simp
  rw [hd, mul_neg, mul_smul_comm, hX, gpair_neg_right, gpair_smul_right, gpair_add_right,
    gpair_smul_right, gpair_hermiteMv, gpair_hermiteMv,
    if_neg (st_ne_of_apply h haii), if_neg (st_ne_st (by omega))]
  simp

/-- The expansion of the viscous term of the mode `i₀` in the Hermite basis. -/
theorem X_derOp_st_expand (i0 : Fin d) (n : ℕ) :
    X i0 * derOp i0 (hermiteMv (st i0 n))
      = (-(1 / 2 : ℂ)) • hermiteMv (st i0 (n + 2)) + (-(1 / 2 : ℂ)) • hermiteMv (st i0 n)
        + (((n : ℂ) * ((n - 1 : ℕ) : ℂ)) / 2) • hermiteMv (st i0 (n - 1 - 1)) := by
  cases n with
  | zero =>
      simp only [derOp_apply, pderiv_st, mul_sub, mul_add, mul_smul_comm, X_mul_st]
      push_cast
      module
  | succ m =>
      simp only [derOp_apply, pderiv_st, mul_sub, mul_add, mul_smul_comm, X_mul_st,
        Nat.add_sub_cancel]
      push_cast
      module

/-- The viscous term of the mode `i₀`: the only surviving matrix element. -/
theorem gpair_visc_self (i0 : Fin d) (n : ℕ) :
    gpair (hermiteMv (st i0 (n + 2))) (X i0 * derOp i0 (hermiteMv (st i0 n)))
      = (-(1 / 2 : ℂ)) * (((n + 2).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ d : ℝ) := by
  rw [X_derOp_st_expand, gpair_add_right, gpair_add_right, gpair_smul_right, gpair_smul_right,
    gpair_smul_right, gpair_st_self, gpair_alpha_st i0 n n (by omega),
    gpair_alpha_st i0 n (n - 1 - 1) (by omega)]
  push_cast
  ring

/-- **The exact matrix element** `⟪n+2| H_NS |n⟫` in a single mode `i₀`: the advection drops out
by the parity selection rule, and what remains is the viscous (dilation) part, of size
proportional to `(n+2)!`. -/
theorem gpair_hermite_kvn (i0 : Fin d) (n : ℕ) :
    gpair (hermiteMv (st i0 (n + 2))) (kvnPoly S (hermiteMv (st i0 n)))
      = (-Complex.I)
        * (((S.nu * S.lam i0 / 2) * ((n + 2).factorial : ℝ)
            * Real.sqrt (2 * Real.pi) ^ d : ℝ) : ℂ) := by
  classical
  have hterm : ∀ i : Fin d,
      gpair (hermiteMv (st i0 (n + 2))) (drift S i * derOp i (hermiteMv (st i0 n)))
        = if i = i0 then
            ((S.nu * S.lam i0 : ℝ) : ℂ) * (1 / 2)
              * (((n + 2).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ d : ℝ)
          else 0 := by
    intro i
    rw [drift, add_mul, gpair_add_right, gpair_adv_vanishes S i0 n i, add_zero, neg_mul,
      smul_mul_assoc, gpair_neg_right, gpair_smul_right]
    by_cases hi : i = i0
    · subst hi
      rw [if_pos rfl, gpair_visc_self]
      push_cast
      ring
    · rw [if_neg hi, gpair_visc_other i0 n hi]
      simp
  rw [kvnPoly_apply, gpair_smul_right, gpair_add_right, gpair_sum_right, gpair_smul_right,
    gpair_alpha_st i0 n n (by omega), mul_zero, add_zero,
    Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq' Finset.univ i0,
    if_pos (Finset.mem_univ i0)]
  push_cast
  ring

/-! ## 6. The Hamiltonian is not bounded below -/

/-- **The quadratic form of the mainstream Navier–Stokes Hamiltonian is not bounded below** on
the Gauss–polynomial core: for every `c` there is a core vector with
`⟪p, H_NS p⟫ < − c ‖p‖²`. -/
theorem kvn_quadP_not_bounded_below (i0 : Fin d) (hnu : 0 < S.nu) (hlam : 0 < S.lam i0) (c : ℝ) :
    ∃ p : MvPolynomial (Fin d) ℂ, quadP S p < -c * (gpair p p).re := by
  have hnl : 0 < S.nu * S.lam i0 := mul_pos hnu hlam
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * max c 0 < ((n : ℝ) + 1) * (S.nu * S.lam i0) := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((2 * max c 0) / (S.nu * S.lam i0))
    refine ⟨n, ?_⟩
    have h1 : (2 * max c 0) < (n : ℝ) * (S.nu * S.lam i0) := by
      rw [div_lt_iff₀ hnl] at hn
      exact hn
    nlinarith [hnl]
  set K : ℝ := Real.sqrt (2 * Real.pi) ^ d with hKdef
  have hK : 0 < K := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact pow_pos this d
  set B : ℝ := (n.factorial : ℝ) * K with hBdef
  set A : ℝ := ((n + 2).factorial : ℝ) * K with hAdef
  have hBpos : 0 < B := by
    have : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    positivity
  have hAB : A = ((n : ℝ) + 1) * ((n : ℝ) + 2) * B := by
    rw [hAdef, hBdef]
    have hf : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * (((n : ℝ) + 1) * (n.factorial : ℝ)) := by
      rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hf]
    ring
  have hApos : 0 < A := by
    rw [hAB]
    positivity
  refine ⟨hermiteMv (st i0 (n + 2))
    + (((-((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) • hermiteMv (st i0 n), ?_⟩
  rw [quadP_real_pair S (realCoeff_hermiteMv _) (realCoeff_hermiteMv _),
    gpair_real_pair (realCoeff_hermiteMv _) (realCoeff_hermiteMv _),
    gpair_hermite_kvn, gpair_st_self, gpair_st_self]
  have him : ((-Complex.I)
      * (((S.nu * S.lam i0 / 2) * ((n + 2).factorial : ℝ) * K : ℝ) : ℂ)).im
      = -((S.nu * S.lam i0 / 2) * A) := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hAdef]
    ring
  rw [him]
  simp only [Complex.ofReal_re]
  have hcA : c * (A + ((n : ℝ) + 1) ^ 2 * B) ≤ 2 * max c 0 * A := by
    have h1 : ((n : ℝ) + 1) ^ 2 * B ≤ A := by
      rw [hAB]
      nlinarith [hBpos, Nat.cast_nonneg (α := ℝ) n]
    have h3 : (0 : ℝ) ≤ max c 0 := le_max_right _ _
    have hY : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 * B := by positivity
    rcases le_or_gt c 0 with hc | hc
    · have hle : c * (A + ((n : ℝ) + 1) ^ 2 * B) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
      nlinarith [hApos, h3]
    · rw [max_eq_left hc.le]
      nlinarith [h1, hc]
  nlinarith [hn, hApos, hcA]

/-! ## 7. The same statements on the Gauss–polynomial core of `L²(ℝᵈ)` -/

/-- **The Navier–Stokes Hamiltonian on the Gauss–polynomial core of `L²(ℝᵈ)`.** -/
def nsKoopmanOp : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype.comp ((coreRepPoly d).op (kvnPoly S))

/-- **The Navier–Stokes Hamiltonian is symmetric on the core.** -/
theorem nsKoopmanOp_symmetricOn : SymmetricOn (polyGaussCore (d := d)) (nsKoopmanOp S) :=
  (coreRepPoly d).symmetricOn_op (kvnPoly_polySym S)

theorem coe_core_eq (x : polyGaussCore (d := d)) :
    ((x : L2d d)) = pgLp ((coreRepPoly d).equiv.symm x) := (coreRepPoly d).coe_symm x

theorem quadForm_nsKoopmanOp (x : polyGaussCore (d := d)) :
    quadForm (nsKoopmanOp S) x = quadP S ((coreRepPoly d).equiv.symm x) := by
  have h1 : (nsKoopmanOp S) x = pgLp (kvnPoly S ((coreRepPoly d).equiv.symm x)) :=
    (coreRepPoly d).coe_op (kvnPoly S) x
  rw [quadForm, h1, coe_core_eq, inner_pgLp_pgLp]
  rfl

theorem norm_core_sq (x : polyGaussCore (d := d)) :
    ‖(x : L2d d)‖ ^ 2
      = (gpair ((coreRepPoly d).equiv.symm x) ((coreRepPoly d).equiv.symm x)).re := by
  rw [coe_core_eq, norm_pgLp_sq_eq]

/-- **The mainstream Navier–Stokes Hamiltonian is not bounded below on the core.**  This is the
reason it cannot play the role of the *positive* comparison operator `N` of the Faris–Lavine
criterion. -/
theorem nsKoopmanOp_not_bounded_below (i0 : Fin d) (hnu : 0 < S.nu) (hlam : 0 < S.lam i0)
    (c : ℝ) :
    ∃ x : polyGaussCore (d := d), quadForm (nsKoopmanOp S) x < -c * ‖(x : L2d d)‖ ^ 2 := by
  obtain ⟨p, hp⟩ := kvn_quadP_not_bounded_below S i0 hnu hlam c
  refine ⟨(coreRepPoly d).equiv p, ?_⟩
  rw [quadForm_nsKoopmanOp, norm_core_sq, LinearEquiv.symm_apply_apply]
  exact hp

/-- **The mainstream Navier–Stokes Hamiltonian is not a positive operator.** -/
theorem nsKoopmanOp_not_positive (i0 : Fin d) (hnu : 0 < S.nu) (hlam : 0 < S.lam i0) :
    ¬ ∀ x : polyGaussCore (d := d), 0 ≤ quadForm (nsKoopmanOp S) x := by
  intro hpos
  obtain ⟨x, hx⟩ := nsKoopmanOp_not_bounded_below S i0 hnu hlam 0
  have := hpos x
  simp only [neg_zero, zero_mul] at hx
  linarith

end

end BookProof.NsKoopman
