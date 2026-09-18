import BookProof.ChapterNsKoopman.Part1

/-!
# The Faris–Lavine comparison operator for the mainstream Navier–Stokes Hamiltonian

`BookProof.ChapterNsKoopman.Part1` shows that the Hamiltonian `H_NS` of the mainstream
Navier–Stokes system is unbounded below, so that the comparison operator `N` of the
Faris–Lavine criterion cannot be `H_NS` itself.  This part supplies a comparison operator that
does work and verifies, for the exact nonlinear Hamiltonian, the inequality the criterion
actually consumes.

Faris–Lavine (Theorem 1, as proved in `BookProof.ChapterFarisLavineCore`) asks for a positive
symmetric `N` on the domain of `H`, with `N + 1` onto and

```
|⟪x, i[H, N] x⟫| ≤ c ⟪x, N x⟫ .
```

*No positivity of `H` is required*, which is exactly why the criterion is the right instrument
for an indefinite `H_NS`.

The comparison operator is the **Leray energy**

```
N_E = multiplication by  E(u) = 1 + ‖u‖² = 1 + Σ_i u_i² ,
```

and the commutator is computed exactly:

* `kvn_comm_energy` — `i[H_NS, N_E] = multiplication by F·∇E = 2 Σ_i u_i F_i`;
* `fluxPoly_eq` — and by **Leray's energy identity** the advection and the pressure gradient
  drop out of `F·∇E` completely, leaving the viscous dissipation
  `F·∇E = −2ν Σ_i λ_i u_i² ≤ 0`;
* `commForm_kvn_energy_bound` — hence `|⟪x, i[H_NS, N_E] x⟫| ≤ 2νΛ ⟪x, N_E x⟫` with
  `Λ = max_i λ_i`: **the Faris–Lavine commutator inequality holds for the exact nonlinear
  Navier–Stokes Hamiltonian**, with a constant fixed by the viscosity and the largest Stokes
  eigenvalue of the truncation, and it holds *because* of the energy structure of the true
  nonlinearity — a Hamiltonian in which the advection were replaced by anything that does work
  on the velocity would fail it;
* `nsKoopman_esa_of_energy_comparison` — the resulting Faris–Lavine conclusion.  Its remaining
  hypothesis is the surjectivity of `N_E + 1` from the common domain, the one input of the
  criterion that the Gauss–polynomial core does not supply; it is carried as an explicit named
  hypothesis, never as an axiom.
* `nsTriad` — a non-vacuity witness: the Navier–Stokes Fourier **triad**
  `u̇₁ = −νλ₁u₁ + a u₂u₃`, `u̇₂ = −νλ₂u₂ + b u₃u₁`, `u̇₃ = −νλ₃u₃ + c u₁u₂` with `a + b + c = 0`
  is an `NsSystem`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsKoopman

open MvPolynomial
open BookProof.HermiteCore BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.GaussCoreQuadBounds

noncomputable section

variable {d : ℕ}

/-! ## 1. Gaussian integrals of a real multiplication operator -/

/-- The pointwise value of the integrand of `⟪p, g p⟫` for a real multiplication operator. -/
theorem eval_star_mul (g p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p * (g * p))).re
      = (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g).re
        * Complex.normSq (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  rw [map_mul, map_mul, eval_starP]
  set z := MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p
  set w := MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g
  have h : (starRingEnd ℂ) z * (w * z) = w * ((Complex.normSq z : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [h]
  simp [Complex.mul_re]

/-- Monotonicity of the expectation of a multiplication operator in its symbol. -/
theorem gpair_mul_mono {g s : MvPolynomial (Fin d) ℂ}
    (h : ∀ x : Vd d, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g).re
      ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) s).re) (p : MvPolynomial (Fin d) ℂ) :
    (gpair p (g * p)).re ≤ (gpair p (s * p)).re := by
  refine gaussInt_re_mono fun x => ?_
  rw [eval_star_mul, eval_star_mul]
  exact mul_le_mul_of_nonneg_right (h x) (Complex.normSq_nonneg _)

/-! ## 2. The Leray energy as a comparison operator -/

/-- The **Leray energy** `E(u) = 1 + ‖u‖²`, the comparison observable. -/
def energyPoly (d : ℕ) : MvPolynomial (Fin d) ℂ := 1 + ∑ i, X i * X i

theorem energyPoly_realCoeff : RealCoeff (energyPoly d) :=
  realCoeff_one.add (RealCoeff.sum fun i _ => (realCoeff_X i).mul (realCoeff_X i))

/-- **The comparison operator `N_E`**: multiplication by the Leray energy. -/
def energyOp (d : ℕ) : Module.End ℂ (MvPolynomial (Fin d) ℂ) := mulOp (energyPoly d)

theorem energyOp_polySym : PolySym (energyOp d) := mulOp_polySym energyPoly_realCoeff

/-- The value of the Leray energy at a real configuration. -/
theorem eval_energyPoly (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (energyPoly d)
      = ((1 + ∑ i, (x i) ^ 2 : ℝ) : ℂ) := by
  rw [energyPoly, map_add, map_one, map_sum, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPolynomial.eval_X]
  push_cast
  ring

theorem pderiv_energyPoly (i : Fin d) :
    pderiv i (energyPoly d) = (2 : ℂ) • X i := by
  classical
  have h1 : pderiv i (1 : MvPolynomial (Fin d) ℂ) = 0 := by simp
  rw [energyPoly, map_add, h1, zero_add, map_sum]
  rw [Finset.sum_eq_single i (fun j _ hj => by
    rw [pderiv_mul, pderiv_X_of_ne hj]
    simp) (fun h => absurd (Finset.mem_univ i) h)]
  rw [pderiv_mul, pderiv_X_self, one_mul, mul_one]
  module

variable (S : NsSystem d)

/-- The **energy flux** `F·∇E = 2 Σ_i u_i F_i` of the Navier–Stokes drift. -/
def fluxPoly : MvPolynomial (Fin d) ℂ :=
  ∑ i, ((-2 * S.nu * S.lam i : ℝ) : ℂ) • (X i * X i)

/-- **Leray's identity in the Hamiltonian**: in the energy flux of the drift the advection and
the pressure gradient cancel exactly, and only the viscous dissipation survives. -/
theorem fluxPoly_eq : ∑ i, drift S i * (pderiv i (energyPoly d)) = fluxPoly S := by
  have hterm : ∀ i : Fin d, drift S i * (pderiv i (energyPoly d))
      = ((-2 * S.nu * S.lam i : ℝ) : ℂ) • (X i * X i) + (2 : ℂ) • (X i * advOf S.bcoef i) := by
    intro i
    rw [pderiv_energyPoly, drift, add_mul, mul_smul_comm, mul_smul_comm, neg_mul, smul_mul_assoc]
    simp only [mul_comm (advOf S.bcoef i) (X i)]
    push_cast
    module
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.smul_sum,
    S.leray, smul_zero, add_zero, fluxPoly]

theorem eval_fluxPoly (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (fluxPoly S)
      = ((-2 * S.nu * ∑ i, S.lam i * (x i) ^ 2 : ℝ) : ℂ) := by
  rw [fluxPoly, map_sum,
    show ((-2 * S.nu * ∑ i, S.lam i * (x i) ^ 2 : ℝ) : ℂ)
        = ∑ i, (((-2 * S.nu * S.lam i * (x i) ^ 2 : ℝ)) : ℂ) by
      rw [← Complex.ofReal_sum]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, map_mul, MvPolynomial.eval_X]
  push_cast
  ring

/-! ## 3. The commutator of the Hamiltonian with the comparison operator -/

/-- **The commutator identity** `[H_NS, N_E] = −i · (F·∇E)`, i.e. `i[H_NS, N_E]` is
multiplication by the energy flux. -/
theorem kvn_comm_energy (p : MvPolynomial (Fin d) ℂ) :
    kvnPoly S (energyPoly d * p) - energyPoly d * kvnPoly S p
      = (-Complex.I) • (fluxPoly S * p) := by
  have hder : ∀ i : Fin d, derOp i (energyPoly d * p)
      = pderiv i (energyPoly d) * p + energyPoly d * derOp i p := by
    intro i
    rw [derOp_apply, derOp_apply, pderiv_mul]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  rw [kvnPoly_apply, kvnPoly_apply]
  have hsum : (∑ i, drift S i * derOp i (energyPoly d * p))
      = fluxPoly S * p + energyPoly d * ∑ i, drift S i * derOp i p := by
    have : ∀ i : Fin d, drift S i * derOp i (energyPoly d * p)
        = (drift S i * pderiv i (energyPoly d)) * p
          + energyPoly d * (drift S i * derOp i p) := by
      intro i
      rw [hder i]
      ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, ← Finset.sum_mul,
      fluxPoly_eq, ← Finset.mul_sum]
  rw [hsum]
  simp only [mul_add, mul_smul_comm]
  module

/-! ## 4. The Faris–Lavine commutator inequality -/

/-- The comparison operator on the Gauss–polynomial core of `L²(ℝᵈ)`. -/
def nsEnergyOp : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype.comp ((coreRepPoly d).op (energyOp d))

theorem nsEnergyOp_symmetricOn : SymmetricOn (polyGaussCore (d := d)) (nsEnergyOp (d := d)) :=
  (coreRepPoly d).symmetricOn_op energyOp_polySym

theorem nsEnergyOp_apply (x : polyGaussCore (d := d)) :
    nsEnergyOp (d := d) x = pgLp (energyPoly d * (coreRepPoly d).equiv.symm x) :=
  (coreRepPoly d).coe_op (energyOp d) x

theorem quadForm_nsEnergyOp (x : polyGaussCore (d := d)) :
    quadForm (nsEnergyOp (d := d)) x
      = (gpair ((coreRepPoly d).equiv.symm x)
          (energyPoly d * (coreRepPoly d).equiv.symm x)).re := by
  rw [quadForm, nsEnergyOp_apply, coe_core_eq, inner_pgLp_pgLp]
  rfl

/-- **`N_E ≥ 1`**: the comparison operator dominates the norm, as Faris–Lavine requires. -/
theorem nsEnergyOp_quadForm_ge (x : polyGaussCore (d := d)) :
    ‖(x : L2d d)‖ ^ 2 ≤ quadForm (nsEnergyOp (d := d)) x := by
  set p := (coreRepPoly d).equiv.symm x
  have h1 : ‖(x : L2d d)‖ ^ 2 = (gpair p ((1 : MvPolynomial (Fin d) ℂ) * p)).re := by
    rw [norm_core_sq, one_mul]
  rw [h1, quadForm_nsEnergyOp]
  refine gpair_mul_mono (fun y => ?_) p
  rw [eval_energyPoly]
  simp only [map_one, Complex.one_re, Complex.ofReal_re]
  have : (0 : ℝ) ≤ ∑ i, (y i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem nsEnergyOp_quadForm_nonneg (x : polyGaussCore (d := d)) :
    0 ≤ quadForm (nsEnergyOp (d := d)) x :=
  le_trans (by positivity) (nsEnergyOp_quadForm_ge x)

/-- The commutator form of the Hamiltonian against the comparison operator is the expectation of
the energy flux. -/
theorem commForm_kvn_energy (x : polyGaussCore (d := d)) :
    commForm (nsKoopmanOp S) (nsEnergyOp (d := d)) x
      = (gpair ((coreRepPoly d).equiv.symm x)
          (fluxPoly S * (coreRepPoly d).equiv.symm x)).re := by
  set p := (coreRepPoly d).equiv.symm x with hp
  have hH : (nsKoopmanOp S) x = pgLp (kvnPoly S p) := (coreRepPoly d).coe_op (kvnPoly S) x
  have hN : nsEnergyOp (d := d) x = pgLp (energyPoly d * p) := nsEnergyOp_apply x
  have h1 : (inner ℂ ((nsKoopmanOp S) x) (nsEnergyOp (d := d) x) : ℂ)
      = gpair p (kvnPoly S (energyPoly d * p)) := by
    rw [hH, hN, ← gpair_eq_inner, gpair_kvn_symm]
  have h2 : (inner ℂ (nsEnergyOp (d := d) x) ((nsKoopmanOp S) x) : ℂ)
      = gpair p (energyPoly d * kvnPoly S p) := by
    rw [hH, hN, ← gpair_eq_inner]
    exact energyOp_polySym p (kvnPoly S p)
  rw [commForm, h1, h2, ← gpair_sub_right, kvn_comm_energy, gpair_smul_right]
  simp [Complex.mul_re, Complex.mul_im]

/-- **The Faris–Lavine commutator inequality for the exact nonlinear Navier–Stokes
Hamiltonian**: `|⟪x, i[H_NS, N_E] x⟫| ≤ 2νΛ ⟪x, N_E x⟫`, where `Λ` bounds the Stokes
eigenvalues.  It holds because the advection and the pressure gradient do no work — Leray's
identity — so that the whole commutator is the (sign-definite) viscous dissipation. -/
theorem commForm_kvn_energy_bound {L : ℝ} (hL : ∀ i, S.lam i ≤ L) (hL0 : 0 ≤ L)
    (x : polyGaussCore (d := d)) :
    |commForm (nsKoopmanOp S) (nsEnergyOp (d := d)) x|
      ≤ (2 * S.nu * L) * quadForm (nsEnergyOp (d := d)) x := by
  set p := (coreRepPoly d).equiv.symm x with hp
  have hnu := S.nu_nonneg
  have hlam := S.lam_nonneg
  -- the expectation of a real multiple of the energy
  have hscal : ∀ t : ℝ, (gpair p ((((t : ℝ) : ℂ) • energyPoly d) * p)).re
      = t * (gpair p (energyPoly d * p)).re := by
    intro t
    rw [smul_mul_assoc, gpair_smul_right]
    simp
  -- the pointwise bounds on the energy flux
  have hpt : ∀ y : Vd d,
      (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (fluxPoly S)).re
          ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
              ((((2 * S.nu * L : ℝ) : ℂ) • energyPoly d))).re
        ∧ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
              ((((-(2 * S.nu * L) : ℝ) : ℂ) • energyPoly d))).re
          ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (fluxPoly S)).re := by
    intro y
    have hflux : (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (fluxPoly S)).re
        = -2 * S.nu * ∑ i, S.lam i * (y i) ^ 2 := by
      rw [eval_fluxPoly, Complex.ofReal_re]
    have hE : ∀ t : ℝ, (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
        ((((t : ℝ) : ℂ) • energyPoly d))).re = t * (1 + ∑ i, (y i) ^ 2) := by
      intro t
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, eval_energyPoly,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    have hs0 : 0 ≤ ∑ i, S.lam i * (y i) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (sq_nonneg _)
    have hsq : (0 : ℝ) ≤ ∑ i, (y i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsL : ∑ i, S.lam i * (y i) ^ 2 ≤ L * (1 + ∑ i, (y i) ^ 2) := by
      have h1 : ∑ i, S.lam i * (y i) ^ 2 ≤ ∑ i, L * (y i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hL i) (sq_nonneg _)
      have h2 : ∑ i, L * (y i) ^ 2 = L * ∑ i, (y i) ^ 2 := by rw [Finset.mul_sum]
      nlinarith [hL0, hsq]
    refine ⟨?_, ?_⟩
    · rw [hflux, hE]
      nlinarith [hnu, hL0, hs0, hsq]
    · rw [hflux, hE]
      nlinarith [hnu, hL0, hsL, hsq]
  have hQ : 0 ≤ quadForm (nsEnergyOp (d := d)) x := nsEnergyOp_quadForm_nonneg x
  rw [commForm_kvn_energy, quadForm_nsEnergyOp, abs_le]
  constructor
  · have := gpair_mul_mono (fun y => (hpt y).2) p
    rw [hscal] at this
    rw [quadForm_nsEnergyOp] at hQ
    linarith
  · have := gpair_mul_mono (fun y => (hpt y).1) p
    rw [hscal] at this
    linarith

/-- **Faris–Lavine for the mainstream Navier–Stokes Hamiltonian.**  With the Leray energy as
comparison operator, all the inequalities of the criterion are proved above; the one remaining
input is the surjectivity of `N_E + 1` on the common domain, which is carried here as an
explicit hypothesis. -/
theorem nsKoopman_esa_of_energy_comparison {L : ℝ} (hL : ∀ i, S.lam i ≤ L) (hL0 : 0 ≤ L)
    (hsurj : ∀ f : L2d d, ∃ x : polyGaussCore (d := d),
      nsEnergyOp (d := d) x + (x : L2d d) = f) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (nsKoopmanOp S) :=
  essentiallySelfAdjointOn_of_farisLavine (nsKoopmanOp S) (nsEnergyOp (d := d)) (2 * S.nu * L)
    (nsKoopmanOp_symmetricOn S) nsEnergyOp_symmetricOn
    (mul_nonneg (by linarith [S.nu_nonneg]) hL0) nsEnergyOp_quadForm_nonneg hsurj
    (commForm_kvn_energy_bound S hL hL0)

/-! ## 5. A non-vacuity witness: the Navier–Stokes Fourier triad -/

/-- The structure constants of the Navier–Stokes **triad**
`u̇₁ = −νλ₁u₁ + a u₂u₃`, `u̇₂ = −νλ₂u₂ + b u₃u₁`, `u̇₃ = −νλ₃u₃ + c u₁u₂`. -/
def triadCoef (a b c : ℝ) : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k =>
  if i = 0 ∧ j = 1 ∧ k = 2 then a
  else if i = 1 ∧ j = 2 ∧ k = 0 then b
  else if i = 2 ∧ j = 0 ∧ k = 1 then c
  else 0

theorem triadCoef_zero (a b c : ℝ) (j k : Fin 3) :
    triadCoef a b c 0 j k = if j = 1 ∧ k = 2 then a else 0 := by
  fin_cases j <;> fin_cases k <;> simp [triadCoef, Fin.ext_iff]

theorem triadCoef_one (a b c : ℝ) (j k : Fin 3) :
    triadCoef a b c 1 j k = if j = 2 ∧ k = 0 then b else 0 := by
  fin_cases j <;> fin_cases k <;> simp [triadCoef, Fin.ext_iff]

theorem triadCoef_two (a b c : ℝ) (j k : Fin 3) :
    triadCoef a b c 2 j k = if j = 0 ∧ k = 1 then c else 0 := by
  fin_cases j <;> fin_cases k <;> simp [triadCoef, Fin.ext_iff]

theorem advOf_triad_zero (a b c : ℝ) :
    advOf (triadCoef a b c) 0 = ((a : ℝ) : ℂ) • (X 1 * X 2) := by
  simp only [advOf, Fin.sum_univ_three, triadCoef_zero]
  norm_num [Fin.ext_iff]

theorem advOf_triad_one (a b c : ℝ) :
    advOf (triadCoef a b c) 1 = ((b : ℝ) : ℂ) • (X 2 * X 0) := by
  simp only [advOf, Fin.sum_univ_three, triadCoef_one]
  norm_num [Fin.ext_iff]

theorem advOf_triad_two (a b c : ℝ) :
    advOf (triadCoef a b c) 2 = ((c : ℝ) : ℂ) • (X 0 * X 1) := by
  simp only [advOf, Fin.sum_univ_three, triadCoef_two]
  norm_num [Fin.ext_iff]

/-- **The Navier–Stokes triad is a mainstream Navier–Stokes system**: the resonant three-mode
interaction of the Fourier-space Euler/Navier–Stokes nonlinearity, energy-conserving
(`a + b + c = 0`) and volume-preserving. -/
def nsTriad (nu : ℝ) (hnu : 0 ≤ nu) (lam : Fin 3 → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (a b c : ℝ) (habc : a + b + c = 0) : NsSystem 3 where
  nu := nu
  lam := lam
  bcoef := triadCoef a b c
  nu_nonneg := hnu
  lam_nonneg := hlam
  leray := by
    have hC : (C ((a : ℝ) : ℂ) + C ((b : ℝ) : ℂ) + C ((c : ℝ) : ℂ)
        : MvPolynomial (Fin 3) ℂ) = 0 := by
      rw [← map_add, ← map_add,
        show (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) + ((c : ℝ) : ℂ)) = (((a + b + c : ℝ)) : ℂ) by
          push_cast; ring, habc]
      simp
    simp only [Fin.sum_univ_three, advOf_triad_zero, advOf_triad_one, advOf_triad_two,
      MvPolynomial.smul_eq_C_mul]
    linear_combination (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) ℂ) * hC
  liouville := by
    simp [Fin.sum_univ_three, advOf_triad_zero, advOf_triad_one, advOf_triad_two,
      MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_X, Fin.ext_iff]

end

end BookProof.NsKoopman
