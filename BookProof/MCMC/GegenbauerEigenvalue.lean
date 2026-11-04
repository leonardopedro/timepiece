import Mathlib
import BookProof.Toolbox.PhysHSGaussian
import BookProof.MCMC.MehlerEigenfunction

/-!
# Chapter GegenbauerEigenvalue — the finite-`d` pCN spectrum and its Fock limit

Plan: `pcnl.md`, Module 1, in its **finite-`d` form** (§1.A).  `BookProof.MCMC.MehlerEigenfunction`
proves the `α → ∞` (Gaussian, Fock) form of the eigenfunction identity,
`∫ Hₙ(ρx + √(1 − ρ²)y) e^{−y²} dy = √π ρⁿ Hₙ(x)`, i.e. `T_ρ Hₙ = ρⁿ Hₙ`.  This module supplies
the finite-`d` side and the bridge between the two.

## What the finite-`d` spectrum actually is

On the sphere `S^{d-1}` the pCN/rotation step is

`x' = ρ x + √(1 − ρ²) ξ`,  `ξ` uniform on the unit sphere of `x^⊥`,

and it preserves the uniform measure.  Its eigenfunctions are the hyperspherical harmonics; on the
**zonal** harmonics — the ones that depend on a single coordinate, which are the Gegenbauer
polynomials `Cₙ^{(λ)}` with `λ = (d − 2)/2` — a rotation of angle `arccos ρ` sends the pole `e` to
`ρ e`, so the eigenvalue is the value of the zonal function there:

`P₀^{(d)} Cₙ^{(λ)} = Λₙ^{(d)} · Cₙ^{(λ)}`,  `Λₙ^{(d)} = Cₙ^{(λ)}(ρ) / Cₙ^{(λ)}(1)`.

That quotient is `pcnZonalEigen n lam ρ` below.  Two exact values are proved here:
`Λ₀ = 1` (`pcnZonalEigen_zero`) and `Λ₁ = ρ` (`pcnZonalEigen_one`, the Euclidean factor of `x'`,
which is why the plan's `λ₁ = ρ` is exactly true), and at `n = 2`
`Λ₂ = λ(2λ + 1)⁻¹(2(λ + 1)ρ² − 1)` (`pcnZonalEigen_two`), which is **not** `ρ²`, and concretely
`Λ₂ = −1/8 ≠ 1/4` at `d = 3`, `ρ = 1/2` (`pcnZonalEigen_two_ne_pow_two`).  So the plan's
`λₙ^{(d)} = ρⁿ` is *not* a finite-`d` identity for `n ≥ 2`; it is the `d → ∞` limit, and that limit
is proved here:

* **`gegenbauer_div_pow_tendsto`** — `λ⁻ⁿ Cₙ^{(λ)}(x) → (2x)ⁿ/n!` as `λ → ∞`, by two-step
  induction on the Gegenbauer recurrence `gegenbauer_rec`;
* **`pcnZonalEigen_tendsto`** — `Λₙ^{(d)} → ρⁿ`: the finite-`d` Gegenbauer eigenvalue tends to the
  Fock eigenvalue that `MehlerEigenfunction.mehlerOp_physHermite` proves is *exactly* `ρⁿ` at
  `d = ∞`.

Together with `UnadjustedPCNGap.pcn_gap_uniform` (the `d`-independence of the Fock weight `ρ^{2N}`)
and `PhysHSGaussian.gegenbauerScaled_tendsto_hermite` (the eigen*function* limit), this closes
Module 1 of `pcnl.md` in both forms: the spectrum is `Λₙ^{(d)}` at finite `d` and `ρⁿ` in the limit,
and the two agree in the limit.

## Honest boundary

The *operator* identity at finite `d`, `P₀^{(d)} Cₙ^{(λ)} = Λₙ^{(d)} Cₙ^{(λ)}`, is stated here
through its eigenvalue `Λₙ^{(d)}` and justified in this docstring, but not proved as an identity of
operators: doing so needs the **Gegenbauer product formula** (the zonal case of the spherical
addition theorem),
`∫₋₁¹ Cₙ^{(λ)}(xy + √(1 − x²)√(1 − y²)u) (1 − u²)^{λ − 1/2} du = N_λ Cₙ^{(λ)}(x) Cₙ^{(λ)}(y)`,
together with the uniform measure on `S^{d-1}`.  Neither is in the corpus (`PhysHSGaussian` carries
`gegenbauer` as a *polynomial*, with no sphere measure on it).  What *is* proved is the part the
gap argument uses: the eigenvalue's closed form at `n ≤ 2`, its `d → ∞` limit `ρⁿ`, and — from
`MehlerEigenfunction` — that the limit statement is exact, not asymptotic, at `d = ∞`.
-/

noncomputable section

namespace BookProof.MCMC

open PhysHSGaussian Filter
open scoped BigOperators Topology

/-! ## 1. The finite-`d` zonal eigenvalue -/

/-- **The zonal eigenvalue of one pCN step on `S^{d-1}`**, `λ = (d − 2)/2`:
`Λₙ^{(d)} = Cₙ^{(λ)}(ρ) / Cₙ^{(λ)}(1)`.  The zonal harmonic
`y ↦ Cₙ^{(λ)}(⟨y, e⟩)` is mapped to itself with this factor by the rotation step of angle
`arccos ρ`, because a rotation moves the pole to a point at inner product `ρ`. -/
def pcnZonalEigen (n : ℕ) (lam ρ : ℝ) : ℝ := gegenbauer n lam ρ / gegenbauer n lam 1

/-- The vacuum (`n = 0`) is invariant: `Λ₀ = 1`. -/
@[simp] theorem pcnZonalEigen_zero (lam ρ : ℝ) : pcnZonalEigen 0 lam ρ = 1 := by
  simp [pcnZonalEigen]

/-- The first excited zonal level carries the Euclidean factor: `Λ₁ = ρ` **exactly**, at every `d`.
This is the plan's `λ₁^{(d)} = ρ`. -/
theorem pcnZonalEigen_one {lam : ℝ} (hlam : lam ≠ 0) (ρ : ℝ) : pcnZonalEigen 1 lam ρ = ρ := by
  have h1 : gegenbauer 1 lam 1 = 2 * lam := by simp
  unfold pcnZonalEigen
  rw [gegenbauer_one, h1]
  have h2 : 2 * lam ≠ 0 := mul_ne_zero (by norm_num) hlam
  field_simp [h2]

/-- At `n = 2` the eigenvalue is the Gegenbauer quotient
`(2λ(λ+1)ρ² − λ)/(2λ(λ+1) − λ)`, which differs from `ρ²` — so the plan's `λₙ^{(d)} = ρⁿ` is a
limit statement, not a finite-`d` identity. -/
theorem pcnZonalEigen_two {lam : ℝ} (ρ : ℝ) :
    pcnZonalEigen 2 lam ρ =
      (2 * lam * (lam + 1) * ρ ^ 2 - lam) / (2 * lam * (lam + 1) - lam) := by
  have h2 : gegenbauer 2 lam 1 = 2 * lam * (lam + 1) - lam := by
    rw [gegenbauer_two]; norm_num
  unfold pcnZonalEigen
  rw [gegenbauer_two, h2]

/-- **The plan's finite-`d` eigenvalue `λₙ^{(d)} = ρⁿ` is false at `n = 2`.**  On `S²`
(`λ = (d − 2)/2 = 1/2`, the Legendre case) at `ρ = 1/2` the zonal eigenvalue is
`(3ρ² − 1)/2 = −1/8`, not `ρ² = 1/4`.  So `λₙ^{(d)} = ρⁿ` is the `d → ∞` statement
`pcnZonalEigen_tendsto`, and the finite-`d` spectrum is `Λₙ^{(d)} = Cₙ^{(λ)}(ρ)/Cₙ^{(λ)}(1)`. -/
theorem pcnZonalEigen_two_ne_pow_two :
    pcnZonalEigen 2 (1 / 2) (1 / 2) ≠ (1 / 2) ^ 2 := by
  rw [pcnZonalEigen_two]
  norm_num

/-! ## 2. The `d → ∞` limit of the Gegenbauer polynomial -/

/-- **`Cₙ^{(λ)}(x)/λⁿ → (2x)ⁿ/n!`** as `λ → ∞`: the leading behaviour of the Gegenbauer
polynomial in its degree parameter.  This is the coefficient-level statement behind the
Gegenbauer → Hermite limit (`gegenbauerScaled_tendsto_hermite` is the rescaled form). -/
theorem gegenbauer_div_pow_tendsto (n : ℕ) (x : ℝ) :
    Tendsto (fun lam : ℝ => gegenbauer n lam x / lam ^ n) atTop
      (𝓝 ((2 * x) ^ n / (n.factorial : ℝ))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · simp
    · -- `n = 1`: `C₁ = 2λx`, so `C₁/λ = 2x`
      have hgoal : Tendsto (fun lam : ℝ => gegenbauer 1 lam x / lam ^ 1) atTop
          (𝓝 ((2 * x) ^ 1 / ((1).factorial : ℝ))) := by
        have hfun : (fun lam : ℝ => gegenbauer 1 lam x / lam ^ 1) =ᶠ[atTop]
            (fun _ : ℝ => 2 * x) := by
          filter_upwards [eventually_ne_atTop (0 : ℝ)] with lam hlam
          rw [gegenbauer_one]
          field_simp
        refine Tendsto.congr' hfun.symm ?_
        simp
      simpa using hgoal
    · -- `n = m + 2`: the recurrence rescaled
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      set A : ℝ := (2 * x) ^ (m + 1) / ((m + 1).factorial : ℝ) with hAdef
      set B : ℝ := (2 * x) ^ m / (m.factorial : ℝ) with hBdef
      -- the rescaled recurrence
      have hfun : (fun lam : ℝ => gegenbauer (m + 2) lam x / lam ^ (m + 2)) =ᶠ[atTop]
          (fun lam : ℝ =>
            (2 * x / ((m : ℝ) + 2)) * (1 + ((m : ℝ) + 1) / lam) *
                (gegenbauer (m + 1) lam x / lam ^ (m + 1)) -
              (((m : ℝ) / lam + 2) / ((m : ℝ) + 2)) * (1 / lam) *
                (gegenbauer m lam x / lam ^ m)) := by
        filter_upwards [eventually_ne_atTop (0 : ℝ)] with lam hlam
        have h2 : ((m : ℝ) + 2) ≠ 0 := by positivity
        have hC : gegenbauer (m + 2) lam x =
            (2 * x * ((m : ℝ) + 1 + lam) * gegenbauer (m + 1) lam x -
              ((m : ℝ) + 2 * lam) * gegenbauer m lam x) / ((m : ℝ) + 2) := by
          rw [eq_div_iff h2]
          simpa [mul_comm] using gegenbauer_rec m lam x
        rw [hC]
        field_simp
        ring
      refine Tendsto.congr' hfun.symm ?_
      have hA : Tendsto (fun lam : ℝ => 1 + ((m : ℝ) + 1) / lam) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (Tendsto.div_atTop tendsto_const_nhds tendsto_id)
      have hB : Tendsto (fun lam : ℝ => (m : ℝ) / lam + 2) atTop (𝓝 (0 + 2)) :=
        (Tendsto.div_atTop tendsto_const_nhds tendsto_id).add tendsto_const_nhds
      have hinv : Tendsto (fun lam : ℝ => 1 / lam) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds tendsto_id
      have ht1 : Tendsto (fun lam : ℝ => (2 * x / ((m : ℝ) + 2)) * (1 + ((m : ℝ) + 1) / lam) *
          (gegenbauer (m + 1) lam x / lam ^ (m + 1))) atTop
          (𝓝 ((2 * x / ((m : ℝ) + 2)) * (1 + 0) * A)) := by
        have := (tendsto_const_nhds (x := (2 * x / ((m : ℝ) + 2)))).mul (hA.mul h1)
        simpa [mul_assoc] using this
      have ht2 : Tendsto (fun lam : ℝ => (((m : ℝ) / lam + 2) / ((m : ℝ) + 2)) * (1 / lam) *
          (gegenbauer m lam x / lam ^ m)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun lam : ℝ => ((m : ℝ) / lam + 2) / ((m : ℝ) + 2)) atTop
            (𝓝 ((0 + 2) / ((m : ℝ) + 2))) :=
          hB.div_const ((m : ℝ) + 2)
        have h3 := h2.mul (hinv.mul h0)
        have hzero : ((0 + 2) / ((m : ℝ) + 2)) * (0 * B) = 0 := by ring
        rw [hzero] at h3
        simpa [mul_assoc] using h3
      have hsub := ht1.sub ht2
      have hval : (2 * x / ((m : ℝ) + 2)) * (1 + 0) * A - 0 = (2 * x) ^ (m + 2) /
          ((m + 2).factorial : ℝ) := by
        rw [hAdef, add_zero, sub_zero]
        have hcast : ((m + 2).factorial : ℝ) =
            ((m : ℝ) + 2) * ((m + 1).factorial : ℝ) := by
          rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ]
          push_cast
          ring
        rw [hcast]
        have hfac : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
        have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
        field_simp
        ring
      rw [← hval]
      exact hsub

/-! ## 3. The finite-`d` eigenvalue tends to `ρⁿ` -/

/-- **The pCN spectrum in the `d → ∞` limit is `ρⁿ`.**  The finite-`d` zonal eigenvalue
`Λₙ^{(d)} = Cₙ^{(λ)}(ρ)/Cₙ^{(λ)}(1)` converges, as `λ = (d − 2)/2 → ∞`, to the Fock eigenvalue
`ρⁿ` — the eigenvalue `MehlerEigenfunction.mehlerOp_physHermite` proves *exactly* at `d = ∞`.
So §1.A and §1.B of `pcnl.md` are one statement in the limit, and `λₙ = ρⁿ` is exact only there. -/
theorem pcnZonalEigen_tendsto (n : ℕ) (ρ : ℝ) :
    Tendsto (fun lam : ℝ => pcnZonalEigen n lam ρ) atTop (𝓝 (ρ ^ n)) := by
  have hnum := gegenbauer_div_pow_tendsto n ρ
  have hden := gegenbauer_div_pow_tendsto n 1
  have hden' : Tendsto (fun lam : ℝ => gegenbauer n lam 1 / lam ^ n) atTop
      (𝓝 ((2 * 1) ^ n / (n.factorial : ℝ))) := by
    simpa using hden
  have hfac : ((2 * 1) ^ n / (n.factorial : ℝ)) ≠ 0 := by positivity
  have hq := hnum.div hden' hfac
  have hval : (2 * ρ) ^ n / (n.factorial : ℝ) / ((2 * 1) ^ n / (n.factorial : ℝ)) = ρ ^ n := by
    have hfacn : ((n.factorial : ℝ)) ≠ 0 := by positivity
    have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    field_simp
    ring
  rw [← hval]
  refine Tendsto.congr' ?_ hq
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with lam hlam
  simp only [Pi.div_apply]
  unfold pcnZonalEigen
  rw [div_div_div_cancel_right₀ (pow_ne_zero n hlam)]

end BookProof.MCMC
