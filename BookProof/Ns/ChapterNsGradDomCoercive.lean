/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import BookProof.Ns.ChapterNsLagrangianComparisonEsa

/-!
# Gradient domination for the Navier–Stokes Lagrangian potential

§54/§55 of `SM_ESA_COMPLETION_PLAN` settled the QYM case: gradient domination fails for
`weylPotPoly Φ = ∑_j Φ_j² + 1` (no coercive quadratic) and holds again once the quadratic is added
(`weylCoercive`).  The corresponding question for Navier–Stokes was left as "the proof template, no
NS potential of that shape in the corpus".  That was too pessimistic: the Lagrangian model *does*
carry a potential, and this module answers the question for it.

The model (`BookProof/Ns/ChapterNsLagrangianDetFarisLavine`) has

  `lagEnergy S = 1 + ½ ∑_j v_j² + V_κ(ξ)`,

with `V_κ` the incompressibility penalty of `volPot` — a **non-negative polynomial of degree six**
whose zero set is the set of incompressible configurations
(`det_eq_one_of_volPot_eq_zero`), plus the coercive displacement term `½ ∑_j ξ_j²` carried by
the Lyapunov polynomial `lagLyap = lagEnergy + ½ ∑_j ξ_j²`.

So the potential splits into three blocks, and they behave differently:

* **The velocity block is coercive, and domination for it is exact and free.**  `∂_{v_j} E = v_j`
  (`pderiv_vel_lagEnergy`), hence `∑_j (∂_{v_j} E)² = ∑_j v_j²` (`vel_grad_sum`), and since
  `E ≥ 1 + ½∑ v²` this is at most `2E` (`lagEnergy_vel_gradDom`) — with no constant term at all.
* **The displacement quadratic is coercive too.**  `∂_{ξ_j} ½∑ ξ² = ξ_j` (`pderiv_disp_dispSq`),
  contributing `2 · (½∑ ξ²)` exactly, again with no constant.
* **The volume penalty is the whole question**, and it is *not* settled by non-negativity plus
  degree.  `lagGradDom_of_volDom` proves the reduction: if the penalty obeys its own pointwise
  domination with constants `A, B`, then `lagLyap` obeys it with `a = 2A + 3`, `b = 2B + 3` — the
  proof is the elementary `∑ v² + 4·½∑ξ² + 2A V² ≤ (2A+3) W² + 3` step, so the NS chain becomes the
  SM §49 shape (`GradBound` → `pointwise_dom_of_sq_sum` → `PotSelfBound`) with one input.
  Conversely `not_gradDom_flatSextic` shows that input is not automatic: `(xyz)²` is non-negative of
  degree six and is **not** dominated, by the same `(t, 1/t, 1)` curve that refutes the flat quartic
  in §48.  Sixth-order flatness is not better than fourth-order flatness.

So for NS the coercive blocks really are part of the model — this is stronger than the QYM
`weylCoercive` situation, where the quadratic had to be added by hand — and what the model still
needs is the penalty's own estimate, named `VolDom`, with a proof that "non-negative degree six"
cannot be weakened to give it.

**Correction (§58 of the plan, 2026-11-13).** `VolDom` is not merely unproved for `volPot`: it is
**false**, so `lagGradDom_of_volDom` has an unsatisfiable hypothesis and the §49 chain cannot be run
on `lagEnergy`/`lagLyap` at all.  The refuting family is the unimodular shears.  With `N = e_x ⊗ e_y`
(`N² = 0`, so `det(I + tN) = 1` for every amplitude `t`) and a transversal tilt `εB`,
`B = e_y ⊗ e_x`, one has `det F − 1 = −εt + O(ε²)`, hence `V_κ ≈ (κ/2)ε²t²`, `∂_t V_κ ≈ κε²t`,
`∂_ε V_κ ≈ κεt²` and

  `|∇V_κ|² / V_κ² → 4/ε²`   as `t → ∞`,

which is unbounded as `ε → 0`.  `scripts/eval-vol-dom.py` evaluates the truncated model exactly and
reproduces the `4/ε²` saturation.  The velocity and displacement blocks above are unaffected: they are
coercive in the model and dominated with no constant.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsGradDomCoercive

open MvPolynomial
open BookProof.NsLagrangianDet BookProof.NsLagrangianDetFL
open BookProof.NsLagrangianComparisonEsa

noncomputable section

variable {K : Type*}

/-! ## 1. Evaluation at a real phase-space point -/

/-- Evaluation at a real phase-space point, as a linear functional. -/
abbrev evP (z : PIdx K → ℝ) (p : MvPolynomial (PIdx K) ℂ) : ℂ :=
  MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) p

theorem evP_X (z : PIdx K → ℝ) (i : PIdx K) : evP z (X i) = ((z i : ℝ) : ℂ) := by
  simp only [evP, MvPolynomial.eval_X]

theorem evP_X_re (z : PIdx K → ℝ) (i : PIdx K) : (evP z (X i)).re = z i := by
  rw [evP_X, Complex.ofReal_re]

theorem evP_add (z : PIdx K → ℝ) (p q : MvPolynomial (PIdx K) ℂ) :
    evP z (p + q) = evP z p + evP z q := by
  simp only [evP, map_add]

/-- Pulling an evaluation through a renaming along the displacement coordinates. -/
theorem evP_rename (z : PIdx K → ℝ) (q : MvPolynomial (DIdx K) ℂ) :
    evP z (rename dispVar q) = ev (fun j => z (dispVar j)) q := by
  rw [evP, ev, MvPolynomial.eval_rename]
  rfl

variable [Fintype K] (S : LagNsData K)

/-! ## 2. The gradient of the energy, block by block -/

/-- `∂_{v_j} E = v_j`: the velocity block of the energy is a pure quadratic. -/
theorem pderiv_vel_lagEnergy (j : DIdx K) :
    pderiv ((true, j) : PIdx K) (lagEnergy S) = X (true, j) :=
  pderiv_vel_energy S j

/-- `∂_{ξ_j} E = ∂_{ξ_j} V_κ`: the energy depends on the displacement only through the penalty. -/
theorem pderiv_disp_lagEnergy (j : DIdx K) :
    pderiv ((false, j) : PIdx K) (lagEnergy S) = pderiv (false, j) (potP S) :=
  pderiv_disp_energy S j

/-- `∂_{v_j} W = v_j` for the Lyapunov polynomial `W = E + ½|ξ|²`. -/
theorem pderiv_vel_lagLyap (j : DIdx K) :
    pderiv ((true, j) : PIdx K) (lagLyap S) = X (true, j) := by
  rw [lagLyap, map_add, pderiv_vel_lagEnergy S j, Derivation.map_smul, pderiv_vel_dispSq,
    smul_zero, add_zero]

/-- `∂_{ξ_j} W = ∂_{ξ_j} V_κ + ξ_j`: the identity behind the `2A + 3` constant. -/
theorem pderiv_disp_lagLyap (j : DIdx K) :
    pderiv ((false, j) : PIdx K) (lagLyap S) = pderiv (false, j) (potP S) + X (false, j) := by
  rw [lagLyap, map_add, pderiv_disp_lagEnergy S j, Derivation.map_smul, pderiv_disp_dispSq,
    smul_smul]
  have hc : ((1 / 2 : ℝ) : ℂ) * (2 : ℂ) = 1 := by norm_num
  rw [hc, one_smul]

/-! ## 3. The coercive blocks are dominated for free -/

/-- **The velocity gradient sum is exactly the kinetic energy**: `∑_j (∂_{v_j} E)² = ∑_j v_j²`. -/
theorem vel_grad_sum (z : PIdx K → ℝ) :
    ∑ j : DIdx K, (evP z (pderiv ((true, j) : PIdx K) (lagEnergy S))).re ^ 2
      = ∑ j : DIdx K, z (true, j) ^ 2 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_vel_lagEnergy S j, evP_X_re]

/-- **Domination of the velocity block, with no constant term**: `∑_j (∂_{v_j} E)² ≤ 2 E`.  This is
the NS analogue of `weylCoercive`'s quadratic — except that here the quadratic is part of the model,
not added to it, and `b = 0` rather than `b = 8|M||ι|C + 8`. -/
theorem lagEnergy_vel_gradDom (z : PIdx K → ℝ) :
    ∑ j : DIdx K, (evP z (pderiv ((true, j) : PIdx K) (lagEnergy S))).re ^ 2
      ≤ 2 * (evP z (lagEnergy S)).re := by
  rw [vel_grad_sum S z, eval_lagEnergy_re S z]
  have hV := volPot_eval_nonneg S.kappa_nonneg S.kvec (fun j => z (dispVar j))
  have hsq : 0 ≤ ∑ j : DIdx K, z (true, j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- The displacement quadratic contributes `ξ_j` per coordinate, so its gradient sum is `2 · ½|ξ|²`
exactly — again no constant. -/
theorem disp_grad_sum (z : PIdx K → ℝ) :
    ∑ j : DIdx K,
        (evP z (pderiv ((false, j) : PIdx K) (((1 / 2 : ℝ) : ℂ) • dispSq (K := K)))).re ^ 2
      = ∑ j : DIdx K, z (false, j) ^ 2 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.map_smul, pderiv_disp_dispSq, smul_smul]
  have hc : ((1 / 2 : ℝ) : ℂ) * (2 : ℂ) = 1 := by norm_num
  rw [hc, one_smul, evP_X_re]

/-! ## 4. The reduction to the volume penalty

What the NS potential needs is an estimate on `V_κ` alone.  It is stated in the `.re` form that the
corpus's other NS pointwise lemmas use (`eval_lagEnergy_re`, `abs_eval_lagLyapFlux_le`), since the
phase-space evaluations are real by `dispField_im` but the corpus keeps every pointwise statement in
real parts. -/

/-- **The named input the NS potential must supply**: the volume penalty dominates its own gradient,
`∑_j (∂_{ξ_j} V_κ)² ≤ A V_κ² + B`.  Unlike the SM's `GradBound` this is a single-polynomial
condition, and §5 shows it is not a consequence of `V_κ ≥ 0` and `deg V_κ = 6`. -/
def VolDom (A B : ℝ) : Prop :=
  ∀ y : DIdx K → ℝ,
    ∑ j : DIdx K, (ev y (pderiv j (volPot S.kappa S.kvec))).re ^ 2
      ≤ A * (ev y (volPot S.kappa S.kvec)).re ^ 2 + B

/-- The penalty's `VolDom` in phase-space coordinates. -/
theorem volDom_phase {A B : ℝ} (h : VolDom S A B) (z : PIdx K → ℝ) :
    ∑ j : DIdx K, (evP z (pderiv ((false, j) : PIdx K) (potP S))).re ^ 2
      ≤ A * (evP z (potP S)).re ^ 2 + B := by
  have hz := h (fun j => z (dispVar j))
  have hterm : ∀ j : DIdx K,
      evP z (pderiv ((false, j) : PIdx K) (potP S))
        = ev (fun l => z (dispVar l)) (pderiv j (volPot S.kappa S.kvec)) := by
    intro j
    rw [pderiv_disp_potP S j, evP_rename]
  have hpot : evP z (potP S) = ev (fun l => z (dispVar l)) (volPot S.kappa S.kvec) := by
    rw [potP, evP_rename]
  rw [hpot]
  calc ∑ j : DIdx K, (evP z (pderiv ((false, j) : PIdx K) (potP S))).re ^ 2
      = ∑ j : DIdx K,
          (ev (fun l => z (dispVar l)) (pderiv j (volPot S.kappa S.kvec))).re ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hterm]
    _ ≤ A * (ev (fun l => z (dispVar l)) (volPot S.kappa S.kvec)).re ^ 2 + B := hz

/-- **Gradient domination for the NS Lyapunov potential, reduced to the volume penalty.**  If `V_κ`
obeys `VolDom A B` then `lagLyap` obeys the pointwise domination with `a = 2A + 3` and `b = 2B + 3`.
The constants come from three elementary steps: the velocity block costs `2K`, the displacement
block costs `2∑(∂V)² + 2∑ξ² ≤ 2A V² + 2B + 2∑ξ²`, and `2(½|v|² + ½|ξ|²) ≤ 3W² + 3` absorbs the
quadratic terms because `W ≥ 1` and `W ≥ 1 + ½|v|² + ½|ξ|²`. -/
theorem lagGradDom_of_volDom {A B : ℝ} (hA : 0 ≤ A) (h : VolDom S A B)
    (z : PIdx K → ℝ) :
    ∑ i : PIdx K, (evP z (pderiv i (lagLyap S))).re ^ 2
      ≤ (2 * A + 3) * (evP z (lagLyap S)).re ^ 2 + (2 * B + 3) := by
  classical
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  -- the velocity block
  have hvel : ∑ j : DIdx K, (evP z (pderiv ((true, j) : PIdx K) (lagLyap S))).re ^ 2
      = ∑ j : DIdx K, z (true, j) ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_vel_lagLyap S j, evP_X_re]
  -- the displacement block: `(∂V + ξ)² ≤ 2(∂V)² + 2ξ²`
  have hdisp : ∑ j : DIdx K, (evP z (pderiv ((false, j) : PIdx K) (lagLyap S))).re ^ 2
      ≤ 2 * ∑ j : DIdx K, (evP z (pderiv ((false, j) : PIdx K) (potP S))).re ^ 2
        + 2 * ∑ j : DIdx K, z (false, j) ^ 2 := by
    have hterm : ∀ j : DIdx K,
        (evP z (pderiv ((false, j) : PIdx K) (lagLyap S))).re ^ 2
          ≤ 2 * (evP z (pderiv ((false, j) : PIdx K) (potP S))).re ^ 2 + 2 * z (false, j) ^ 2 := by
      intro j
      rw [pderiv_disp_lagLyap S j, evP_add, Complex.add_re, evP_X_re]
      nlinarith [sq_nonneg ((evP z (pderiv ((false, j) : PIdx K) (potP S))).re - z (false, j))]
    calc ∑ j : DIdx K, (evP z (pderiv ((false, j) : PIdx K) (lagLyap S))).re ^ 2
        ≤ ∑ j : DIdx K, (2 * (evP z (pderiv ((false, j) : PIdx K) (potP S))).re ^ 2
            + 2 * z (false, j) ^ 2) := Finset.sum_le_sum fun j _ => hterm j
      _ = 2 * ∑ j : DIdx K, (evP z (pderiv ((false, j) : PIdx K) (potP S))).re ^ 2
            + 2 * ∑ j : DIdx K, z (false, j) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  set v := ∑ j : DIdx K, z (true, j) ^ 2 with hv
  set d := ∑ j : DIdx K, z (false, j) ^ 2 with hd
  set p := (evP z (potP S)).re with hp
  set W := (evP z (lagLyap S)).re with hWdef
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hd0 : 0 ≤ d := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hpotEval : (evP z (potP S)).re
      = (ev (fun j => z (dispVar j)) (volPot S.kappa S.kvec)).re := by
    rw [potP, evP_rename]
  have hp0 : 0 ≤ p := by
    rw [hp, hpotEval]
    exact volPot_eval_nonneg S.kappa_nonneg S.kvec (fun j => z (dispVar j))
  have hWdecomp : W = 1 + (1 / 2) * v + p + (1 / 2) * d := by
    rw [hWdef, eval_lagLyap_re S z, eval_lagEnergy_re S z, ← hpotEval, ← hp, ← hv, ← hd]
  have hVle : p ≤ W := by
    rw [hWdecomp]; nlinarith
  have hVd := volDom_phase S h z
  rw [hvel]
  have hP : ∑ j : DIdx K, (evP z (pderiv ((false, j) : PIdx K) (potP S))).re ^ 2
      ≤ A * p ^ 2 + B := by
    rw [hp]
    exact hVd
  have hvd : v + 2 * d ≤ 3 * W ^ 2 + 3 := by
    have hs0 : 0 ≤ (1 / 2) * v + (1 / 2) * d := by nlinarith
    have hWs : 1 + ((1 / 2) * v + (1 / 2) * d) ≤ W := by
      rw [hWdecomp]; nlinarith [hp0]
    have hWpos : 0 ≤ W := by linarith
    have hsq : (1 + ((1 / 2) * v + (1 / 2) * d)) ^ 2 ≤ W ^ 2 := by
      have h1 : 0 ≤ W - (1 + ((1 / 2) * v + (1 / 2) * d)) := by linarith
      have h2 : 0 ≤ W + (1 + ((1 / 2) * v + (1 / 2) * d)) := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hkey : 2 * ((1 / 2) * v + (1 / 2) * d)
        ≤ 3 * (1 + ((1 / 2) * v + (1 / 2) * d)) ^ 2 + 3 := by nlinarith [hs0]
    nlinarith [hsq, hkey]
  have hAp : 2 * A * p ^ 2 ≤ 2 * A * W ^ 2 := by
    have h1 : 0 ≤ W - p := by linarith
    have h2 : 0 ≤ W + p := by linarith
    nlinarith [mul_nonneg hA (mul_nonneg h1 h2)]
  linarith [hdisp, hP, hvd, hAp]

/-! ## 5. The penalty's input is not automatic: the flat sextic -/

section Sextic

/-- Evaluation at a real point of `ℝ³`. -/
abbrev ev3 (x : Fin 3 → ℝ) (p : MvPolynomial (Fin 3) ℂ) : ℂ :=
  MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p

/-- `(xyz)²`, the sextic analogue of §48's flat quartic `X₀²X₁²`.  Non-negative, degree six, and
flat on the coordinate hyperplanes. -/
def flatSextic : MvPolynomial (Fin 3) ℂ :=
  (X 0 * X 1 * X 2) * (X 0 * X 1 * X 2)

/-- Evaluation of the flat sextic at a real point. -/
theorem ev3_flatSextic (x : Fin 3 → ℝ) :
    (ev3 x flatSextic).re = (x 0 * x 1 * x 2) ^ 2 := by
  simp [ev3, flatSextic]
  ring

theorem ev3_pderiv_zero (x : Fin 3 → ℝ) :
    (ev3 x (pderiv 0 flatSextic)).re = 2 * x 0 * x 1 ^ 2 * x 2 ^ 2 := by
  simp [ev3, flatSextic, pderiv_X]
  ring

theorem ev3_pderiv_one (x : Fin 3 → ℝ) :
    (ev3 x (pderiv 1 flatSextic)).re = 2 * x 0 ^ 2 * x 1 * x 2 ^ 2 := by
  simp [ev3, flatSextic, pderiv_X]
  ring

theorem ev3_pderiv_two (x : Fin 3 → ℝ) :
    (ev3 x (pderiv 2 flatSextic)).re = 2 * x 0 ^ 2 * x 1 ^ 2 * x 2 := by
  simp [ev3, flatSextic, pderiv_X]
  ring

/-- **The flat sextic is non-negative and of degree six.** -/
theorem ev3_flatSextic_nonneg (x : Fin 3 → ℝ) : 0 ≤ (ev3 x flatSextic).re := by
  rw [ev3_flatSextic]
  positivity

/-- **The flat sextic is NOT gradient-dominated.**  Along `(t, 1/t, 1)` the potential is the
constant `1` while the gradient grows like `4t²`, so no `a b` can dominate it.  This is the exact
sixth-degree analogue of `not_gradDom_flat_quartic`, and it is why `VolDom` is an input and not a
consequence of `V_κ ≥ 0` and `deg V_κ = 6`. -/
theorem not_gradDom_flatSextic :
    ¬ ∃ a b : ℝ, ∀ x : Fin 3 → ℝ,
      ∑ j : Fin 3, (ev3 x (pderiv j flatSextic)).re ^ 2
        ≤ a * (ev3 x flatSextic).re ^ 2 + b := by
  rintro ⟨a, b, h⟩
  set t : ℝ := |a| + |b| + 2 with ht
  have ht2 : 2 ≤ t := by
    have : 0 ≤ |a| + |b| := by positivity
    rw [ht]; linarith
  have ht0 : 0 < t := by linarith
  set x : Fin 3 → ℝ := fun i => if i = 0 then t else if i = 1 then 1 / t else 1 with hx
  have hx0 : x 0 = t := by simp [hx]
  have hx1 : x 1 = 1 / t := by simp [hx]
  have hx2 : x 2 = 1 := by simp [hx]
  have hpt := h x
  rw [Fin.sum_univ_three, ev3_pderiv_zero, ev3_pderiv_one, ev3_pderiv_two, ev3_flatSextic,
    hx0, hx1, hx2] at hpt
  have htinv : t * (1 / t) = 1 := by field_simp
  have hpot : (t * (1 / t) * 1) ^ 2 = 1 := by rw [htinv]; norm_num
  rw [hpot] at hpt
  have e0 : (2 * t * (1 / t) ^ 2 * 1 ^ 2) ^ 2 = 4 / t ^ 2 := by field_simp; ring
  have e1 : (2 * t ^ 2 * (1 / t) * 1 ^ 2) ^ 2 = 4 * t ^ 2 := by field_simp; ring
  have e2 : (2 * t ^ 2 * (1 / t) ^ 2 * 1) ^ 2 = 4 := by field_simp; ring
  rw [e0, e1, e2] at hpt
  have hab : a + b ≤ t := by
    have ha : a ≤ |a| := le_abs_self a
    have hb : b ≤ |b| := le_abs_self b
    rw [ht]; linarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 2) (by linarith : (0 : ℝ) ≤ t)]

end Sextic

end

end BookProof.NsGradDomCoercive
