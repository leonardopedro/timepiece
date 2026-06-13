import Mathlib
import PnpProof.Foundations

/-!
# Part 3b: The uniform sphere measure and the Gaussian limit (G0–G7)

The Gegenbauer → Hermite limit, the weight → Gaussian limit, the
normalization-constant limit, and the uniform-sphere ↔ Gaussian
identification.  This module is independent of the main chain.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace PnpProof

/-! ### G0. Physicists' Hermite polynomials -/

/-- Physicists' Hermite polynomials as real functions, by recurrence
    (lopez99 eq. (1.1)): `H_0 = 1`, `H_1 = 2x`,
    `H_{n+2} = 2x·H_{n+1} − 2(n+1)·H_n`. -/
def physHermite : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | (n+2), x => 2 * x * physHermite (n+1) x - 2 * (n+1) * physHermite n x

@[simp] theorem physHermite_zero (x : ℝ) : physHermite 0 x = 1 := rfl
@[simp] theorem physHermite_one (x : ℝ) : physHermite 1 x = 2 * x := rfl

theorem physHermite_succ_succ (n : ℕ) (x : ℝ) :
    physHermite (n+2) x = 2 * x * physHermite (n+1) x - 2 * (n+1) * physHermite n x := rfl

/-! ### G1. Gegenbauer polynomials -/

/-- Gegenbauer (ultraspherical) polynomials `C_n^λ`, by the standard three-term
    recurrence, as real functions of `(λ, x)`. -/
def gegenbauer : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, lam, x => 2 * lam * x
  | (n+2), lam, x =>
      (2 * x * (n + 1 + lam) * gegenbauer (n+1) lam x
        - (n + 2 * lam) * gegenbauer n lam x) / (n + 2)

@[simp] theorem gegenbauer_zero (lam x : ℝ) : gegenbauer 0 lam x = 1 := rfl
@[simp] theorem gegenbauer_one (lam x : ℝ) : gegenbauer 1 lam x = 2 * lam * x := rfl

theorem gegenbauer_two (lam x : ℝ) :
    gegenbauer 2 lam x = 2 * lam * (lam + 1) * x^2 - lam := by
  grind +locals

/-
The standard `n·C_n = …` recurrence, clearing the division.
-/
theorem gegenbauer_rec (n : ℕ) (lam x : ℝ) :
    ((n : ℝ) + 2) * gegenbauer (n+2) lam x
      = 2 * x * (n + 1 + lam) * gegenbauer (n+1) lam x
        - (n + 2 * lam) * gegenbauer n lam x := by
  exact Eq.symm ( by rw [ show gegenbauer ( n + 2 ) lam x = ( 2 * x * ( n + 1 + lam ) * gegenbauer ( n + 1 ) lam x - ( n + 2 * lam ) * gegenbauer n lam x ) / ( n + 2 ) by rfl ] ; rw [ mul_div_cancel₀ _ ( by positivity ) ] )

/-! ### G2. The lopez99 limit: rescaled Gegenbauer → Hermite -/

/-- The rescaled Gegenbauer function of the chapter. -/
def gegenbauerScaled (n : ℕ) (lam x : ℝ) : ℝ :=
  lam ^ (-(n : ℝ)/2) * gegenbauer n lam (x / Real.sqrt lam)

theorem gegenbauerScaled_tendsto_hermite (n : ℕ) (x : ℝ) :
    Filter.Tendsto (fun lam => gegenbauerScaled n lam x)
      Filter.atTop (𝓝 (physHermite n x / n.factorial)) := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | n ) <;> norm_num [ physHermite_succ_succ ] at *;
  · unfold gegenbauerScaled; aesop;
  · unfold gegenbauerScaled;
    unfold gegenbauer; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg ] ; ring_nf; norm_num; (
    refine' Filter.Tendsto.congr' _ tendsto_const_nhds ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with lam hl ; norm_num [ ← Real.rpow_neg hl.le, ← Real.rpow_add hl ] ; ring_nf ;
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul hl.le ] ; norm_num [ hl.ne' ];
    rw [ Real.rpow_neg_one, inv_mul_cancel₀ hl.ne', one_mul ]);
  · have h_recurrence : ∀ lam > 0, ((n : ℝ) + 2) * gegenbauerScaled (n + 2) lam x = 2 * x * (1 + (n + 1) / lam) * gegenbauerScaled (n + 1) lam x - (2 + n / lam) * gegenbauerScaled n lam x := by
      intro lam hl
      simp [gegenbauerScaled];
      convert congr_arg ( fun y => lam ^ ( ( -2 + -n : ℝ ) / 2 ) * y ) ( gegenbauer_rec n lam ( x / Real.sqrt lam ) ) using 1 <;> ring;
      norm_num [ Real.sqrt_eq_rpow, Real.rpow_add hl, Real.rpow_neg hl.le ] ; ring;
      grind;
    have h_limit : Filter.Tendsto (fun lam => (2 * x * (1 + (n + 1) / lam) * gegenbauerScaled (n + 1) lam x - (2 + n / lam) * gegenbauerScaled n lam x) / (n + 2)) Filter.atTop (nhds ((2 * x * physHermite (n + 1) x - 2 * (n + 1) * physHermite n x) / (Nat.factorial (n + 2)))) := by
      convert Filter.Tendsto.div_const ( Filter.Tendsto.sub ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ) ( ih _ _ ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( ih _ _ ) ) ) _ using 2 <;> norm_num [ Nat.factorial_succ ] ; ring;
      -- Combine and simplify the fractions
      field_simp
      ring;
    exact h_limit.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with lam hl using by rw [ ← h_recurrence lam hl, mul_div_cancel_left₀ _ ( by positivity ) ] )

/-! ### G5. The uniform measure on the `k`-sphere via Gaussians -/

/-- Standard Gaussian on `EuclideanSpace ℝ (Fin k)`. -/
def gaussianE (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (Measure.pi fun _ : Fin k => ProbabilityTheory.gaussianReal 0 1).map
    (EuclideanSpace.measurableEquiv (Fin k)).symm

/-- Radial projection onto the sphere of radius `√k` (junk value at 0). -/
def sphereProj (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  if x = 0 then x else (Real.sqrt k / ‖x‖) • x

/-- The uniform measure on the `√k`-sphere. -/
def sphereUniform (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (gaussianE k).map (sphereProj k)

instance gaussianE_isProbability (k : ℕ) : IsProbabilityMeasure (gaussianE k) := by
  constructor ; norm_num [ gaussianE ];
  rw [ Measure.map_apply ] <;> norm_num;
  exact MeasurableEquiv.measurable _

theorem sphereProj_measurable (k : ℕ) : Measurable (sphereProj k) := by
  refine' Measurable.piecewise _ _ _;
  · exact MeasurableSingletonClass.measurableSet_singleton _;
  · exact measurable_id;
  · fun_prop

instance sphereUniform_isProbability (k : ℕ) :
    IsProbabilityMeasure (sphereUniform k) := by
  constructor;
  unfold sphereUniform;
  rw [ Measure.map_apply ] <;> norm_num [ sphereProj_measurable ]

theorem sphereUniform_sphere (k : ℕ) (hk : 0 < k) :
    sphereUniform k {x | ‖x‖ = Real.sqrt k} = 1 := by
  -- First show that the normalize map sends almost all vectors to the sphere of radius `√k`.
  have h_norm_map : ∀ᵐ x ∂gaussianE k, ‖sphereProj k x‖ = Real.sqrt k := by
    -- The set of vectors with norm zero has measure zero under the Gaussian measure.
    have h_zero_measure : (gaussianE k) {x : EuclideanSpace ℝ (Fin k) | x = 0} = 0 := by
      simp [gaussianE];
      rw [ Measure.map_apply ] <;> norm_num [ EuclideanSpace.measurableEquiv ];
      · rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] ; norm_num;
        rw [ MeasureTheory.ae_iff ] ; norm_num;
        exact ⟨ by rw [ ProbabilityTheory.gaussianReal ] ; norm_num, hk.ne' ⟩;
      · fun_prop;
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_zero_measure ] with x hx;
    unfold sphereProj; simp +decide [ hx, norm_smul, Real.norm_eq_abs ] ;
  -- Apply the fact that the measure of the preimage under a measurable function is equal to the measure of the set.
  have h_preimage : (gaussianE k).map (sphereProj k) {x | ‖x‖ = Real.sqrt k} = (gaussianE k) {x | ‖sphereProj k x‖ = Real.sqrt k} := by
    rw [ Measure.map_apply ] <;> norm_num [ sphereProj_measurable ];
    exact measurableSet_eq_fun ( measurable_norm ) measurable_const |> MeasurableSet.mem;
  convert h_preimage using 1;
  rw [ MeasureTheory.measure_congr, MeasureTheory.IsProbabilityMeasure.measure_univ ] ; aesop

/-! ### G3. The weight limit -/

theorem weight_tendsto_gaussian (x : ℝ) :
    Filter.Tendsto (fun lam : ℝ => (1 - x^2/lam) ^ (lam - 1/2))
      Filter.atTop (𝓝 (Real.exp (-x^2))) := by
  -- We'll use the fact that $(1 - \frac{x^2}{\lambda})^{\lambda}$ converges to $e^{-x^2}$ as $\lambda \to \infty$.
  have h_exp : Filter.Tendsto (fun lam => (1 - x^2 / lam) ^ lam) Filter.atTop (nhds (Real.exp (-x^2))) := by
    -- We'll use the fact that $(1 + \frac{y}{n})^n$ converges to $e^y$ as $n \to \infty$.
    have h_exp : Filter.Tendsto (fun n => (1 + (-x^2) / n) ^ n) Filter.atTop (nhds (Real.exp (-x^2))) := by
      exact Real.tendsto_one_add_div_rpow_exp (-x^2);
    simpa only [ neg_div, sub_eq_add_neg ] using h_exp;
  -- Let's simplify the exponent: $(1 - x^2 / lam)^{lam - 1/2} = (1 - x^2 / lam)^lam * (1 - x^2 / lam)^{-1/2}$.
  suffices h_simp : Filter.Tendsto (fun lam => ((1 - x^2 / lam) ^ lam) * ((1 - x^2 / lam) ^ (-1 / 2 : ℝ))) Filter.atTop (nhds (Real.exp (-x^2))) by
    refine h_simp.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop ( x ^ 2 ) ] with lam hl using by rw [ ← Real.rpow_add ( by exact sub_pos.mpr <| by rw [ div_lt_iff₀ <| by nlinarith ] ; nlinarith ) ] ; ring;
  convert h_exp.mul ( Filter.Tendsto.rpow ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) tendsto_const_nhds _ ) using 2 <;> norm_num

/-! ### G5 (continued). Rotation invariance of the uniform sphere measure -/

/-
The radial projection commutes with any linear isometry.
-/
theorem sphereProj_equivariant (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) :
    sphereProj k (L x) = L (sphereProj k x) := by
  by_cases hx : x = 0 <;> simp +decide [ hx, sphereProj ]

/-
The standard Gaussian on Euclidean space is invariant under linear isometries.
-/
theorem gaussianE_rotation_invariant (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (gaussianE k).map L = gaussianE k := by
  apply MeasureTheory.Measure.ext_of_charFun;
  -- By definition of $gaussianE$, we know that its characteristic function is given by $\exp(-\|t\|^2 / 2)$.
  have h_char_gaussian : ∀ t : EuclideanSpace ℝ (Fin k), charFun (gaussianE k) t = Complex.exp (-‖t‖^2 / 2) := by
    intro t
    unfold gaussianE;
    rw [ charFun ];
    rw [ MeasureTheory.integral_map ];
    · -- The integral of the exponential of the inner product is the product of the integrals of the exponentials of the components.
      have h_prod : ∫ x : Fin k → ℝ, Complex.exp (Complex.I * ∑ i, x i * t i) ∂Measure.pi (fun _ => ProbabilityTheory.gaussianReal 0 1) = ∏ i, ∫ x : ℝ, Complex.exp (Complex.I * x * t i) ∂ProbabilityTheory.gaussianReal 0 1 := by
        have h_prod : ∀ (f : Fin k → ℝ → ℂ), (∫ x : Fin k → ℝ, ∏ i, f i (x i) ∂Measure.pi (fun _ => ProbabilityTheory.gaussianReal 0 1)) = ∏ i, ∫ x : ℝ, f i x ∂ProbabilityTheory.gaussianReal 0 1 := by
          intro f;
          rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ];
        convert h_prod ( fun i x => Complex.exp ( Complex.I * x * t i ) ) using 3 ; norm_num [ Complex.exp_sum, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      -- The integral of the exponential of the inner product is the product of the integrals of the exponentials of the components, which is the characteristic function of the Gaussian measure.
      have h_char : ∀ i : Fin k, ∫ x : ℝ, Complex.exp (Complex.I * x * t i) ∂ProbabilityTheory.gaussianReal 0 1 = Complex.exp (-t i ^ 2 / 2) := by
        intro i;
        have := @ProbabilityTheory.charFun_gaussianReal 0 1 ( t i );
        convert this using 1 <;> norm_num [ charFun ] ; ring;
        · ac_rfl;
        · ring;
      convert h_prod using 1;
      · norm_num [ mul_comm, inner ];
        simp +decide [ mul_comm, EuclideanSpace.measurableEquiv ];
      · simp_all +decide [ EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
        norm_cast ; norm_num [ ← Finset.sum_div _ _ _, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
        rw [ ← Real.exp_sum ] ; norm_num [ neg_div, Finset.sum_div _ _ _ ];
    · exact Measurable.aemeasurable ( by exact MeasurableEquiv.measurable _ );
    · fun_prop;
  ext t; simp +decide [ charFun, h_char_gaussian ] ; ring;
  rw [ MeasureTheory.integral_map ];
  · -- Since $L$ is a linear isometry, we have $\langle L(x), t \rangle = \langle x, L^{-1}(t) \rangle$.
    have h_inner : ∀ x : EuclideanSpace ℝ (Fin k), inner ℝ (L x) t = inner ℝ x (L.symm t) := by
      intro x; exact (by
      rw [ ← L.inner_map_map x ( L.symm t ), L.apply_symm_apply ]);
    have := h_char_gaussian ( L.symm t ) ; simp_all +decide [ charFun ] ;
  · exact L.continuous.aemeasurable;
  · fun_prop (disch := norm_num)

theorem sphereUniform_rotation_invariant (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (sphereUniform k).map L = sphereUniform k := by
  convert Measure.map_map ( L.continuous.measurable ) ( sphereProj_measurable k ) using 1;
  convert Measure.map_map ( sphereProj_measurable k ) L.continuous.measurable using 1;
  rw [ gaussianE_rotation_invariant k L ];
  · rfl;
  · exact congr_arg ( fun f => Measure.map f ( gaussianE k ) ) ( funext fun x => by simp +decide [ sphereProj_equivariant ] )

/-! ### G4 (second half). The Hermite normalization integral -/

/-
Derivative recurrence for the physicists' Hermite polynomials:
    `H_{n+1}'(x) = 2(n+1)·H_n(x)`.
-/
theorem physHermite_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (physHermite (n+1)) (2 * (n+1) * physHermite n x) x := by
  induction' n using Nat.strong_induction_on with n ih generalizing x; rcases n with ( _ | _ | n ) <;> simp_all +decide [ physHermite_succ_succ ] ; ring!; (
  convert HasDerivAt.const_mul 2 ( hasDerivAt_id x ) using 1 ; norm_num [ physHermite ]);
  · convert HasDerivAt.sub ( HasDerivAt.mul ( HasDerivAt.const_mul 2 ( hasDerivAt_id x ) ) ( ih x ) ) ( HasDerivAt.const_mul 2 ( hasDerivAt_const x 1 ) ) using 1 ; ring!;
    · ext; norm_num [ physHermite ] ; ring;
      norm_num;
    · norm_num [ physHermite ] ; ring;
  · have h_recurrence : ∀ x, physHermite (n + 3) x = 2 * x * physHermite (n + 2) x - 2 * (n + 2) * physHermite (n + 1) x := by
      exact fun x => by exact_mod_cast physHermite_succ_succ ( n + 1 ) x;
    rw [ show physHermite ( n + 3 ) = _ from funext h_recurrence ] ; convert HasDerivAt.sub ( HasDerivAt.mul ( HasDerivAt.const_mul 2 ( hasDerivAt_id x ) ) ( ih _ le_rfl _ ) ) ( HasDerivAt.const_mul _ ( ih _ ( by linarith ) _ ) ) using 1 ; ring;
    rw [ show 2 + n = n + 2 by ring ] ; rw [ show 1 + n = n + 1 by ring ] ; rw [ physHermite_succ_succ ] ; norm_num ; ring;

/-
The diagonal Hermite–Gaussian integral: `∫ H_n(x)² e^{-x²} dx = √π · 2ⁿ · n!`.
-/
theorem hermite_sq_integral (n : ℕ) :
    ∫ x : ℝ, (physHermite n x)^2 * Real.exp (-x^2)
      = Real.sqrt Real.pi * 2^n * n.factorial := by
  -- For the inductive step, we use the recurrence relation for the Hermite polynomials.
  have h_recurrence : ∀ n : ℕ, ∫ x : ℝ, (physHermite (n + 1) x)^2 * Real.exp (-x^2) = 2 * (n + 1) * ∫ x : ℝ, (physHermite n x)^2 * Real.exp (-x^2) := by
    intro n
    have h_parts : ∀ a b : ℝ, ∫ x in a..b, (physHermite (n + 1) x)^2 * Real.exp (-x^2) = (physHermite (n + 1) b * (-physHermite n b * Real.exp (-b^2))) - (physHermite (n + 1) a * (-physHermite n a * Real.exp (-a^2))) + 2 * (n + 1) * ∫ x in a..b, (physHermite n x)^2 * Real.exp (-x^2) := by
      intro a b
      have h_parts : ∫ x in a..b, (physHermite (n + 1) x)^2 * Real.exp (-x^2) = (physHermite (n + 1) b * (-physHermite n b * Real.exp (-b^2))) - (physHermite (n + 1) a * (-physHermite n a * Real.exp (-a^2))) - ∫ x in a..b, (-physHermite n x * Real.exp (-x^2)) * (2 * (n + 1) * physHermite n x) := by
        rw [ eq_sub_iff_add_eq, ← intervalIntegral.integral_add ];
        · rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
          · intro x hx; convert HasDerivAt.mul ( physHermite_hasDerivAt n x ) ( HasDerivAt.mul ( HasDerivAt.neg ( hasDerivAt_deriv_iff.mpr ?_ ) ) ( HasDerivAt.exp ( HasDerivAt.neg ( hasDerivAt_pow 2 x ) ) ) ) using 1 <;> norm_num ; ring;
            · rw [ show deriv ( physHermite n ) x = 2 * n * physHermite ( n - 1 ) x from _ ] ; rcases n with ( _ | n ) <;> norm_num [ physHermite_succ_succ ] ; ring;
              · rw [ show 1 + ( n + 1 ) = n + 2 by ring ] ; rw [ physHermite_succ_succ ] ; ring;
              · induction' n with n ih generalizing x <;> simp_all +decide [ physHermite_succ_succ ];
                · exact HasDerivAt.deriv ( hasDerivAt_const _ _ );
                · exact HasDerivAt.deriv ( physHermite_hasDerivAt n x );
            · -- By definition of $physHermite$, we know that it is a polynomial, hence differentiable everywhere.
              have h_poly : ∀ n : ℕ, ∃ p : Polynomial ℝ, ∀ x : ℝ, physHermite n x = p.eval x := by
                intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ physHermite_succ_succ ] ; ring!; (
                exact ⟨ 1, fun x => by norm_num ⟩);
                · exact ⟨ Polynomial.monomial 1 2, fun x => by norm_num ⟩;
                · obtain ⟨ p, hp ⟩ := ih ( n + 1 ) ( by linarith ) ; obtain ⟨ q, hq ⟩ := ih n ( by linarith ) ; exact ⟨ 2 * Polynomial.X * p - 2 * ( Polynomial.C ( n + 1 : ℝ ) ) * q, fun x => by simp +decide [ hp, hq ] ⟩ ;
              obtain ⟨ p, hp ⟩ := h_poly n; exact by rw [ show physHermite n = _ from funext hp ] ; exact p.differentiableAt;
          · apply_rules [ Continuous.intervalIntegrable ];
            -- The Hermite polynomials are continuous, and the exponential function is continuous, so their product is continuous.
            have h_cont : ∀ n : ℕ, Continuous (fun x : ℝ => physHermite n x) := by
              intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ physHermite_succ_succ ] ; ring!; (
              exact continuous_const);
              · continuity;
              · exact Continuous.sub ( Continuous.mul ( continuous_const.mul continuous_id' ) ( ih _ le_rfl ) ) ( Continuous.mul ( continuous_const ) ( ih _ ( Nat.le_succ _ ) ) );
            exact Continuous.add ( Continuous.mul ( Continuous.pow ( h_cont _ ) _ ) ( Real.continuous_exp.comp ( Continuous.neg ( continuous_pow 2 ) ) ) ) ( Continuous.mul ( Continuous.mul ( Continuous.neg ( h_cont _ ) ) ( Real.continuous_exp.comp ( Continuous.neg ( continuous_pow 2 ) ) ) ) ( Continuous.mul ( continuous_const ) ( h_cont _ ) ) );
        · apply_rules [ Continuous.intervalIntegrable ];
          apply_rules [ Continuous.mul, Continuous.pow, Continuous.neg, continuous_id, continuous_const, Real.continuous_exp ];
          · induction' n + 1 using Nat.strong_induction_on with n ih;
            rcases n with ( _ | _ | n ) <;> [ exact continuous_const; exact continuous_const.mul continuous_id; exact Continuous.sub ( Continuous.mul ( continuous_const.mul continuous_id ) ( ih _ <| by linarith ) ) ( Continuous.mul ( continuous_const.mul continuous_const ) ( ih _ <| by linarith ) ) ];
          · induction' n + 1 using Nat.strong_induction_on with n ih;
            rcases n with ( _ | _ | n ) <;> [ exact continuous_const; exact continuous_const.mul continuous_id; exact Continuous.sub ( Continuous.mul ( continuous_const.mul continuous_id ) ( ih _ <| by linarith ) ) ( Continuous.mul ( continuous_const.mul continuous_const ) ( ih _ <| by linarith ) ) ];
          · continuity;
        · apply_rules [ Continuous.intervalIntegrable ];
          apply_rules [ Continuous.mul, Continuous.neg, Continuous.add, continuous_id, continuous_const, Real.continuous_exp ];
          · induction' n using Nat.strong_induction_on with n ih;
            rcases n with ( _ | _ | n ) <;> simp_all +decide [ physHermite ];
            · exact continuous_const;
            · continuity;
            · exact Continuous.sub ( Continuous.mul ( continuous_const.mul continuous_id' ) ( ih _ le_rfl ) ) ( Continuous.mul ( continuous_const ) ( ih _ ( Nat.le_succ _ ) ) );
          · continuity;
          · induction' n using Nat.strong_induction_on with n ih;
            rcases n with ( _ | _ | n ) <;> simp_all +decide [ physHermite ];
            · exact continuous_const;
            · continuity;
            · exact Continuous.sub ( Continuous.mul ( continuous_const.mul continuous_id' ) ( ih _ le_rfl ) ) ( Continuous.mul ( continuous_const ) ( ih _ ( Nat.le_succ _ ) ) );
      convert h_parts using 1 ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ] ; ring;
    -- Let's take the limit of the integration by parts formula as $a \to -\infty$ and $b \to \infty$.
    have h_limit : Filter.Tendsto (fun b => ∫ x in (-b)..b, (physHermite (n + 1) x)^2 * Real.exp (-x^2)) Filter.atTop (nhds (∫ x : ℝ, (physHermite (n + 1) x)^2 * Real.exp (-x^2))) ∧ Filter.Tendsto (fun b => ∫ x in (-b)..b, (physHermite n x)^2 * Real.exp (-x^2)) Filter.atTop (nhds (∫ x : ℝ, (physHermite n x)^2 * Real.exp (-x^2))) := by
      constructor <;> apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral ];
      any_goals exact Filter.tendsto_id;
      · -- The product of a polynomial and a Gaussian function is integrable.
        have h_integrable : ∀ p : Polynomial ℝ, MeasureTheory.Integrable (fun x => p.eval x * Real.exp (-x^2)) MeasureTheory.volume := by
          intro p
          have h_integrable : ∀ k : ℕ, MeasureTheory.Integrable (fun x => x^k * Real.exp (-x^2)) MeasureTheory.volume := by
            intro k;
            have := @integrable_rpow_mul_exp_neg_mul_sq;
            simpa using @this 1 zero_lt_one k ( by linarith );
          simp_all +decide [ Polynomial.eval_eq_sum_range ];
          simp +decide only [Finset.sum_mul _ _ _, mul_assoc];
          exact MeasureTheory.integrable_finset_sum _ fun i hi => MeasureTheory.Integrable.const_mul ( h_integrable i ) _;
        -- By definition of Hermite polynomials, we know that they are polynomials.
        have h_hermite_poly : ∀ n : ℕ, ∃ p : Polynomial ℝ, ∀ x : ℝ, physHermite n x = p.eval x := by
          intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ physHermite_succ_succ ] ;
          · exact ⟨ 1, fun x => by norm_num ⟩;
          · exact ⟨ Polynomial.monomial 1 2, fun x => by norm_num ⟩;
          · obtain ⟨ p, hp ⟩ := ih ( n + 1 ) ( by linarith ) ; obtain ⟨ q, hq ⟩ := ih n ( by linarith ) ; exact ⟨ 2 * Polynomial.X * p - 2 * ( Polynomial.C ( n + 1 : ℝ ) ) * q, fun x => by simp +decide [ hp, hq ] ⟩ ;
        obtain ⟨ p, hp ⟩ := h_hermite_poly ( n + 1 ) ; simp_all +decide [ sq, mul_assoc ] ;
        convert h_integrable ( p * p ) using 1 ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      · exact Filter.tendsto_neg_atTop_atBot;
      · -- The function $x \mapsto (physHermite n x)^2 * \exp(-x^2)$ is integrable because it is a polynomial times a Gaussian.
        have h_integrable : ∀ p : Polynomial ℝ, MeasureTheory.Integrable (fun x => p.eval x * Real.exp (-x^2)) MeasureTheory.volume := by
          intro p
          have h_integrable : ∀ k : ℕ, MeasureTheory.Integrable (fun x => x^k * Real.exp (-x^2)) MeasureTheory.volume := by
            intro k;
            have := @integrable_rpow_mul_exp_neg_mul_sq;
            simpa using @this 1 zero_lt_one k ( by linarith );
          simp_all +decide [ Polynomial.eval_eq_sum_range ];
          simp +decide only [Finset.sum_mul _ _ _, mul_assoc];
          exact MeasureTheory.integrable_finset_sum _ fun i hi => MeasureTheory.Integrable.const_mul ( h_integrable i ) _;
        -- By definition of $physHermite$, we know that $physHermite n$ is a polynomial.
        have h_poly : ∀ n : ℕ, ∃ p : Polynomial ℝ, ∀ x : ℝ, physHermite n x = p.eval x := by
          intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ physHermite_succ_succ ] ;
          · exact ⟨ 1, fun x => by norm_num ⟩;
          · exact ⟨ Polynomial.monomial 1 2, fun x => by norm_num ⟩;
          · obtain ⟨ p, hp ⟩ := ih ( n + 1 ) ( by linarith ) ; obtain ⟨ q, hq ⟩ := ih n ( by linarith ) ; exact ⟨ 2 * Polynomial.X * p - 2 * ( Polynomial.C ( n + 1 : ℝ ) ) * q, fun x => by simp +decide [ hp, hq ] ⟩ ;
        obtain ⟨ p, hp ⟩ := h_poly n; specialize h_integrable ( p ^ 2 ) ; simp_all +decide [ sq, mul_assoc ] ;
      · exact Filter.tendsto_neg_atTop_atBot;
    -- Let's take the limit of the boundary terms as $b \to \infty$.
    have h_boundary : Filter.Tendsto (fun b => physHermite (n + 1) b * (-physHermite n b * Real.exp (-b^2))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun b => physHermite (n + 1) (-b) * (-physHermite n (-b) * Real.exp (-(-b)^2))) Filter.atTop (nhds 0) := by
      have h_boundary : ∀ p : Polynomial ℝ, Filter.Tendsto (fun x => p.eval x * Real.exp (-x^2)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => p.eval (-x) * Real.exp (-x^2)) Filter.atTop (nhds 0) := by
        intro p
        have h_poly_exp : Filter.Tendsto (fun x => p.eval x * Real.exp (-x^2)) Filter.atTop (nhds 0) := by
          have h_poly_exp : ∀ k : ℕ, Filter.Tendsto (fun x => x^k * Real.exp (-x^2)) Filter.atTop (nhds 0) := by
            intro k;
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
            refine' squeeze_zero_norm' _ this;
            filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; nlinarith;
          simp_all +decide [ Polynomial.eval_eq_sum_range ];
          simpa [ Finset.sum_mul _ _ _, mul_assoc ] using tendsto_finset_sum _ fun i hi => Filter.Tendsto.const_mul ( p.coeff i ) ( h_poly_exp i )
        have h_poly_exp_neg : Filter.Tendsto (fun x => p.eval (-x) * Real.exp (-x^2)) Filter.atTop (nhds 0) := by
          have h_poly_exp_neg : ∀ q : Polynomial ℝ, Filter.Tendsto (fun x => q.eval x * Real.exp (-x^2)) Filter.atTop (nhds 0) := by
            intro q
            have h_poly_exp_neg : ∀ k : ℕ, Filter.Tendsto (fun x => x^k * Real.exp (-x^2)) Filter.atTop (nhds 0) := by
              intro k;
              have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
              refine' squeeze_zero_norm' _ this;
              filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; nlinarith;
            simp_all +decide [ Polynomial.eval_eq_sum_range ];
            simpa [ Finset.sum_mul _ _ _, mul_assoc ] using tendsto_finset_sum _ fun i hi => Filter.Tendsto.const_mul ( q.coeff i ) ( h_poly_exp_neg i );
          convert h_poly_exp_neg ( p.comp ( -Polynomial.X ) ) using 2 ; norm_num
        exact ⟨h_poly_exp, h_poly_exp_neg⟩;
      have h_poly : ∀ n : ℕ, ∃ p : Polynomial ℝ, ∀ x : ℝ, physHermite n x = p.eval x := by
        intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ physHermite_succ_succ ] ;
        · exact ⟨ 1, fun x => by norm_num ⟩;
        · exact ⟨ Polynomial.monomial 1 2, fun x => by norm_num ⟩;
        · obtain ⟨ p, hp ⟩ := ih ( n + 1 ) ( by linarith ) ; obtain ⟨ q, hq ⟩ := ih n ( by linarith ) ; exact ⟨ 2 * Polynomial.X * p - 2 * ( Polynomial.C ( n + 1 : ℝ ) ) * q, fun x => by simp +decide [ hp, hq ] ⟩ ;
      obtain ⟨ p, hp ⟩ := h_poly ( n + 1 ) ; obtain ⟨ q, hq ⟩ := h_poly n; simp_all +decide [ ← mul_assoc, ← sq ] ;
      have := h_boundary ( p * q ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      exact ⟨ by simpa using this.1.neg, by simpa using this.2.neg ⟩;
    linarith [ tendsto_nhds_unique h_limit.1 ( by simpa only [ h_parts ] using Filter.Tendsto.add ( Filter.Tendsto.sub h_boundary.1 h_boundary.2 ) ( tendsto_const_nhds.mul h_limit.2 ) ) ];
  induction' n with n ih;
  · simpa [ physHermite_zero ] using integral_gaussian ( 1 : ℝ );
  · rw [ h_recurrence, ih ] ; push_cast [ Nat.factorial_succ, pow_succ' ] ; ring

theorem hermite_normalization (n : ℕ) :
    ∫ x : ℝ, (physHermite n x / n.factorial)^2 * Real.exp (-x^2)
      = Real.sqrt Real.pi * 2^n / n.factorial := by
  convert congr_arg ( fun x : ℝ => x / ( n.factorial : ℝ ) ^ 2 ) ( hermite_sq_integral n ) using 1 <;> ring;
  · rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ; ring;
  · simp +decide [ sq, mul_assoc, Nat.factorial_ne_zero ]

/-! ### G4 (first half). The normalization-constant limit via dominated convergence

The statement below is the chapter's normalization limit *after* the change of
variables `x_old = x/√λ` has been carried out (the substitution is baked into the
interval `[-√λ, √λ]` and the `gegenbauerScaled`/weight integrand), as permitted by
the plan. -/

/-
The rescaled three-term recurrence for `gegenbauerScaled` (for `λ > 0`).
-/
theorem gegenbauerScaled_rec (n : ℕ) (lam x : ℝ) (hl : 0 < lam) :
    ((n : ℝ) + 2) * gegenbauerScaled (n+2) lam x
      = 2 * x * (1 + (n + 1) / lam) * gegenbauerScaled (n+1) lam x
        - (2 + n / lam) * gegenbauerScaled n lam x := by
  unfold gegenbauerScaled;
  convert congr_arg ( fun y => lam ^ ( ( -2 + -n : ℝ ) / 2 ) * y ) ( gegenbauer_rec n lam ( x / Real.sqrt lam ) ) using 1 <;> ring;
  · push_cast; ring;
  · norm_num [ Real.sqrt_eq_rpow, Real.rpow_add hl, Real.rpow_neg hl.le ] ; ring;
    rw [ Real.rpow_add hl, Real.rpow_mul hl.le ] ; norm_num [ hl.ne' ] ; ring

/-
A uniform-in-`λ` polynomial bound on the rescaled Gegenbauer functions.
-/
theorem gegenbauerScaled_bound (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ lam : ℝ, 1 ≤ lam → ∀ x : ℝ,
      |gegenbauerScaled n lam x| ≤ B * (1 + |x|)^n := by
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | n );
  · unfold gegenbauerScaled; aesop;
  · refine' ⟨ 2, by norm_num, fun lam hl x => _ ⟩ ; norm_num [ gegenbauerScaled ];
    rw [ Real.rpow_neg ( by positivity ), abs_of_nonneg ( by positivity : 0 ≤ lam ) ];
    rw [ ← Real.sqrt_eq_rpow, abs_of_nonneg ( by positivity ), abs_div, abs_of_nonneg ( Real.sqrt_nonneg _ ) ];
    field_simp;
    rw [ Real.sq_sqrt ] <;> nlinarith [ abs_nonneg x ];
  · obtain ⟨ B₁, hB₁, hB₁' ⟩ := ih ( n + 1 ) ( by linarith ) ; ( obtain ⟨ B₂, hB₂, hB₂' ⟩ := ih n ( by linarith ) ; use 2 * ( B₁ + B₂ ) ; norm_num ; );
    refine' ⟨ by positivity, fun lam hl x => _ ⟩
    have h_recurrence : (n + 2) * |gegenbauerScaled (n + 2) lam x| ≤ 2 * |x| * (1 + (n + 1) / lam) * |gegenbauerScaled (n + 1) lam x| + (2 + n / lam) * |gegenbauerScaled n lam x| := by
      have h_recurrence : (n + 2) * gegenbauerScaled (n + 2) lam x = 2 * x * (1 + (n + 1) / lam) * gegenbauerScaled (n + 1) lam x - (2 + n / lam) * gegenbauerScaled n lam x := by
        exact gegenbauerScaled_rec n lam x ( by positivity )
      generalize_proofs at *; (
      have h_abs : |(n + 2) * gegenbauerScaled (n + 2) lam x| ≤ |2 * x * (1 + (n + 1) / lam) * gegenbauerScaled (n + 1) lam x| + |(2 + n / lam) * gegenbauerScaled n lam x| := by
        exact h_recurrence ▸ abs_sub _ _
      generalize_proofs at *; (
      convert h_abs using 1 <;> norm_num [ abs_mul, abs_of_nonneg, add_nonneg, div_nonneg, hl ] ; ring;
      rw [ abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 1 + n * lam⁻¹ + lam⁻¹ ), abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 + n * lam⁻¹ ) ] ; ring;))
    generalize_proofs at *; (
    -- Apply the induction hypothesis to bound the terms involving `gegenbauerScaled`.
    have h_bound : (n + 2) * |gegenbauerScaled (n + 2) lam x| ≤ 2 * |x| * (1 + (n + 1)) * B₁ * (1 + |x|) ^ (n + 1) + (2 + n) * B₂ * (1 + |x|) ^ n := by
      refine le_trans h_recurrence ?_;
      refine' add_le_add _ _;
      · refine' le_trans ( mul_le_mul_of_nonneg_left ( hB₁' lam hl x ) ( by positivity ) ) _;
        norm_num [ mul_assoc ];
        exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_right ( by rw [ add_div', div_le_iff₀ ] <;> nlinarith ) ( by positivity ) ) ( by positivity );
      · exact le_trans ( mul_le_mul_of_nonneg_left ( hB₂' lam hl x ) ( by positivity ) ) ( by nlinarith [ show ( n : ℝ ) / lam ≤ n by rw [ div_le_iff₀ ] <;> nlinarith, show ( 0 : ℝ ) ≤ B₂ * ( 1 + |x| ) ^ n by positivity ] )
    generalize_proofs at *; (
    ring_nf at h_bound ⊢;
    nlinarith [ show 0 ≤ |x| * B₁ * ( 1 + |x| ) ^ n by positivity, show 0 ≤ |x| * B₂ * ( 1 + |x| ) ^ n by positivity, show 0 ≤ |x| ^ 2 * B₁ * ( 1 + |x| ) ^ n by positivity, show 0 ≤ |x| ^ 2 * B₂ * ( 1 + |x| ) ^ n by positivity, show 0 ≤ B₁ * ( 1 + |x| ) ^ n by positivity, show 0 ≤ B₂ * ( 1 + |x| ) ^ n by positivity ]))

theorem normalization_tendsto (n : ℕ) :
    Filter.Tendsto
      (fun lam => ∫ x in (-Real.sqrt lam)..(Real.sqrt lam),
          (gegenbauerScaled n lam x)^2 * (1 - x^2/lam) ^ (lam - 1/2))
      Filter.atTop
      (𝓝 (∫ x : ℝ, (physHermite n x / n.factorial)^2 * Real.exp (-x^2))) := by
  -- Apply the Dominated Convergence Theorem.
  have h_dominated : Filter.Tendsto (fun lam => ∫ x : ℝ, (if |x| ≤ Real.sqrt lam then (gegenbauerScaled n lam x)^2 * (1 - x^2 / lam)^(lam - 1/2) else 0)) Filter.atTop (nhds (∫ x : ℝ, (physHermite n x / n.factorial)^2 * Real.exp (-x^2))) := by
    refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
    use fun x => ( gegenbauerScaled_bound n |> Classical.choose ) ^ 2 * ( 1 + |x| ) ^ ( 2 * n ) * Real.exp ( -x ^ 2 / 2 );
    · refine' Filter.eventually_atTop.mpr ⟨ 1, fun lam hl => _ ⟩ ; refine' Measurable.aestronglyMeasurable _ ; refine' Measurable.ite _ _ _ <;> norm_num;
      · exact measurableSet_Iic.mem.comp measurable_norm;
      · refine' Measurable.mul _ _;
        · refine' Measurable.pow_const _ _;
          refine' Measurable.mul _ _;
          · exact measurable_const;
          · refine' Measurable.comp ( show Measurable ( gegenbauer n lam ) from _ ) ( measurable_id'.div_const _ );
            induction' n using Nat.strong_induction_on with n ih;
            rcases n with ( _ | _ | n ) <;> simp_all +decide [ gegenbauer ];
            · exact measurable_const.mul measurable_id';
            · exact Measurable.mul ( Measurable.sub ( Measurable.mul ( measurable_const.mul measurable_id' ) measurable_const |> Measurable.mul <| ih _ <| by linarith ) <| Measurable.mul measurable_const <| ih _ <| by linarith ) measurable_const;
        · exact Measurable.pow_const ( by exact Measurable.sub measurable_const ( by exact Measurable.div_const ( measurable_id.pow_const 2 ) _ ) ) _;
    · refine' Filter.eventually_atTop.mpr ⟨ 1, fun lam hl => Filter.Eventually.of_forall fun x => _ ⟩ ; split_ifs <;> norm_num;
      · refine' le_trans ( mul_le_mul_of_nonneg_right ( show ( gegenbauerScaled n lam x ) ^ 2 ≤ ( Classical.choose ( gegenbauerScaled_bound n ) ) ^ 2 * ( 1 + |x| ) ^ ( 2 * n ) by
                                                          have := Classical.choose_spec ( gegenbauerScaled_bound n ) |>.2 lam hl x;
                                                          convert pow_le_pow_left₀ ( abs_nonneg _ ) this 2 using 1 <;> norm_num [ mul_pow, pow_mul' ] ) ( abs_nonneg _ ) ) _;
        gcongr;
        rw [ abs_of_nonneg ( Real.rpow_nonneg ( sub_nonneg.2 <| div_le_one_of_le₀ ( by nlinarith [ abs_le.mp ‹_›, Real.mul_self_sqrt ( show 0 ≤ lam by positivity ) ] ) <| by positivity ) _ ) ];
        refine' le_trans ( Real.rpow_le_rpow ( sub_nonneg.2 <| div_le_one_of_le₀ ( by nlinarith [ abs_le.mp ‹_›, Real.mul_self_sqrt ( show 0 ≤ lam by positivity ) ] ) <| by positivity ) ( show 1 - x ^ 2 / lam ≤ Real.exp ( -x ^ 2 / lam ) from _ ) <| by linarith ) _;
        · exact le_trans ( by ring_nf; norm_num ) ( Real.add_one_le_exp _ );
        · rw [ ← Real.exp_mul ] ; ring_nf ; norm_num;
          nlinarith [ inv_mul_cancel_left₀ ( by positivity : lam ≠ 0 ) ( x ^ 2 ), abs_le.mp ‹_›, Real.mul_self_sqrt ( show 0 ≤ lam by positivity ) ];
      · exact mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( pow_nonneg ( by positivity ) _ ) ) ( Real.exp_nonneg _ );
    · have h_integrable : MeasureTheory.Integrable (fun x : ℝ => (1 + |x|)^(2 * n) * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
        have h_poly_exp : ∀ k : ℕ, MeasureTheory.Integrable (fun x : ℝ => |x|^k * Real.exp (-x^2 / 2)) MeasureTheory.volume := by
          intro k; have := @integrable_rpow_mul_exp_neg_mul_sq; simp_all +decide [ div_eq_inv_mul ] ;
          specialize @this ( 1 / 2 ) ( by norm_num ) ( k : ℝ ) ( by linarith );
          convert this.norm using 2 ; norm_num [ abs_mul, abs_of_nonneg, Real.exp_nonneg ];
        simp_all +decide [ add_comm ( 1 : ℝ ), add_pow, mul_assoc, mul_comm, mul_left_comm ];
        simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        exact MeasureTheory.integrable_finset_sum _ fun i hi => by simpa only [ mul_assoc, mul_left_comm, mul_comm ] using h_poly_exp i |> fun h => h.const_mul ( Nat.choose ( n * 2 ) i : ℝ ) ;
      simpa only [ mul_assoc ] using h_integrable.const_mul _;
    · refine' Filter.Eventually.of_forall fun x => _;
      -- We'll use the fact that if the denominator grows faster than the numerator, the limit will be zero.
      have h_lim : Filter.Tendsto (fun lam => (gegenbauerScaled n lam x)^2 * (1 - x^2 / lam)^(lam - 1/2)) Filter.atTop (nhds ((physHermite n x / n.factorial)^2 * Real.exp (-x^2))) := by
        refine' Filter.Tendsto.mul _ _;
        · exact Filter.Tendsto.pow ( gegenbauerScaled_tendsto_hermite n x ) _;
        · convert weight_tendsto_gaussian x using 1;
      refine' h_lim.congr' _;
      filter_upwards [ Filter.eventually_gt_atTop ( x ^ 2 ) ] with lam hl using by rw [ if_pos ( Real.abs_le_sqrt <| by nlinarith ) ] ;
  refine' h_dominated.congr' _ |> fun h => h.trans _;
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with lam hl;
    rw [ intervalIntegral.integral_of_le ( by linarith [ Real.sqrt_nonneg lam ] ), ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    rw [ ← MeasureTheory.integral_congr_ae ];
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton ( -Real.sqrt lam ) ) ] with x hx;
    grind;
  · grind

/-! ### G6–G7. Poincaré–Borel: sphere marginals → Gaussian

Everything is realized on the single probability space `γ = gammaMeasure`, the
infinite product of standard Gaussians on `ℕ → ℝ`. -/

/-- The infinite product of standard Gaussians (the law of an i.i.d. Gaussian
    sequence). -/
def gammaMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)

instance gammaMeasure_isProbability : IsProbabilityMeasure gammaMeasure := by
  unfold gammaMeasure; infer_instance

/-- Empirical squared norm of the first `k` coordinates. -/
def normSq (k : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range k, (ω i)^2

/-
a.s. concentration (the strong law): the normalized empirical squared norm
    of the first `k` coordinates converges to `1`.
-/
theorem gaussian_concentration_sphere :
    ∀ᵐ ω ∂gammaMeasure,
      Filter.Tendsto (fun k => normSq k ω / k) Filter.atTop (𝓝 1) := by
  convert ProbabilityTheory.strong_law_ae _ _ _ _ using 1;
  case convert_4 => exact ℝ;
  case convert_10 => exact fun i ω => ( ω i ) ^ 2;
  all_goals try infer_instance;
  · have h_integral : ∫ x : ℕ → ℝ, x 0 ^ 2 ∂gammaMeasure = 1 := by
      have h_gauss : ∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
        have := @ProbabilityTheory.variance_id_gaussianReal 0 1;
        rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ] at this <;> norm_num at *;
        · exact this;
        · exact Filter.Eventually.of_forall fun x => sq_nonneg x;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      have h_gauss : ∫ x : ℕ → ℝ, x 0 ^ 2 ∂gammaMeasure = ∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) := by
        have h_map : MeasureTheory.Measure.map (fun x : ℕ → ℝ => x 0) gammaMeasure = ProbabilityTheory.gaussianReal 0 1 := by
          convert MeasureTheory.Measure.infinitePi_map_eval _ _ using 1;
          exact fun _ => by infer_instance;
        rw [ ← h_map, MeasureTheory.integral_map ];
        · exact measurable_pi_apply 0 |> Measurable.aemeasurable;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      linarith;
    simp_all +decide [ div_eq_inv_mul, normSq ];
  · have h_integrable : MeasureTheory.Integrable (fun x : ℝ => x^2) (ProbabilityTheory.gaussianReal 0 1) := by
      have h_gauss_integrable : ∫ x, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
        have := @ProbabilityTheory.variance_id_gaussianReal 0 1;
        rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ] at this <;> norm_num at *;
        · exact this;
        · exact Filter.Eventually.of_forall fun x => sq_nonneg x;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      exact ( by contrapose! h_gauss_integrable; rw [ MeasureTheory.integral_undef h_gauss_integrable ] ; norm_num );
    have h_integrable : MeasureTheory.Integrable (fun ω : ℕ → ℝ => ω 0 ^ 2) (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)) := by
      have h_map : (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)).map (fun ω : ℕ → ℝ => ω 0) = ProbabilityTheory.gaussianReal 0 1 := by
        convert MeasureTheory.Measure.infinitePi_map_eval _ _ using 1;
        exact fun _ => inferInstance
      rw [ ← h_map ] at h_integrable;
      rwa [ MeasureTheory.integrable_map_measure ] at h_integrable;
      · exact h_integrable.1;
      · exact measurable_pi_apply 0 |> Measurable.aemeasurable;
    exact h_integrable;
  · have h_indep : ProbabilityTheory.iIndepFun (fun i : ℕ => fun ω : ℕ → ℝ => ω i) gammaMeasure := by
      convert ProbabilityTheory.iIndepFun_infinitePi ( fun i => measurable_id ) using 1;
      infer_instance;
    exact fun i j hij => h_indep.indepFun hij |> fun h => h.comp ( measurable_id.pow_const 2 ) ( measurable_id.pow_const 2 );
  · intro i
    have h_ident : ProbabilityTheory.IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω : ℕ → ℝ => ω 0) gammaMeasure gammaMeasure := by
      constructor;
      · exact measurable_pi_apply i |> Measurable.aemeasurable;
      · exact measurable_pi_apply 0 |> Measurable.aemeasurable;
      · have h_map : ∀ i : ℕ, Measure.map (fun ω : ℕ → ℝ => ω i) gammaMeasure = ProbabilityTheory.gaussianReal 0 1 := by
          intro i
          generalize_proofs at *; (
          convert MeasureTheory.Measure.infinitePi_map_eval ( fun _ => ProbabilityTheory.gaussianReal 0 1 ) i using 1);
        rw [ h_map i, h_map 0 ]
    generalize_proofs at *; (
    exact h_ident.comp ( measurable_id.pow_const 2 ))

/-
a.s. Poincaré–Borel: the `√k`-sphere normalization of the first `k` Gaussian
    coordinates converges coordinatewise to the coordinates themselves.
-/
theorem poincare_borel_ae :
    ∀ᵐ ω ∂gammaMeasure, ∀ i : ℕ,
      Filter.Tendsto
        (fun k : ℕ => (Real.sqrt k / Real.sqrt (normSq k ω)) * ω i)
        Filter.atTop (𝓝 (ω i)) := by
  have h_ae_all : ∀ᵐ ω ∂gammaMeasure, ∀ i : ℕ, Filter.Tendsto (fun k : ℕ => Real.sqrt k / Real.sqrt (normSq k ω)) Filter.atTop (nhds 1) := by
    have h_ae_all : ∀ᵐ ω ∂gammaMeasure, Filter.Tendsto (fun k : ℕ => Real.sqrt (normSq k ω / k)) Filter.atTop (nhds 1) := by
      have := @gaussian_concentration_sphere;
      exact this.mono fun ω hω => by simpa using Filter.Tendsto.sqrt hω;
    filter_upwards [ h_ae_all ] with ω hω using by simpa using hω.inv₀;
  filter_upwards [ h_ae_all ] with ω hω using fun i => by simpa using hω i |> Filter.Tendsto.mul_const ( ω i ) ;

end PnpProof