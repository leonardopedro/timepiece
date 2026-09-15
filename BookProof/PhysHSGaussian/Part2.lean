import Mathlib
import BookProof.PhysMeasureBasis
import BookProof.PhysHSGaussian.Part1

/-!
# Part 3b: The uniform sphere measure and the Gaussian limit (G0–G7)

The Gegenbauer → Hermite limit, the weight → Gaussian limit, the
normalization-constant limit, and the uniform-sphere ↔ Gaussian
identification.  This module is independent of the main chain.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace PhysHSGaussian

open PhysMeasureBasis
/-! ### G4 (second half). The Hermite normalization integral -/

/-
Derivative recurrence for the physicists' Hermite polynomials:
    `H_{n+1}'(x) = 2(n+1)·H_n(x)`.
-/
/-- The two-term recurrence in the uniform (`n − 1` truncated-subtraction) form,
valid also at `n = 0`. -/
theorem physHermite_rec (m : ℕ) (x : ℝ) :
    physHermite (m+1) x = 2 * x * physHermite m x - 2 * m * physHermite (m-1) x := by
  cases m with
  | zero => simp
  | succ j => simpa using physHermite_succ_succ j x

/-- The derivative recurrence in uniform form: `H_n'(x) = 2n·H_{n-1}(x)`. -/
theorem physHermite_hasDerivAt_aux (n : ℕ) (x : ℝ) :
    HasDerivAt (physHermite n) (2 * n * physHermite (n-1) x) x := by
  induction n using Nat.strong_induction_on generalizing x with | _ n ih => ?_
  match n, ih with
  | 0, _ => simpa using hasDerivAt_const x (1 : ℝ)
  | 1, _ =>
      have hf : physHermite 1 = fun y : ℝ => 2 * y := funext physHermite_one
      rw [hf]
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  | (m+2), ih =>
      have h1 : HasDerivAt (physHermite (m+1)) (2 * (m+1) * physHermite m x) x := by
        simpa using ih (m+1) (by omega) x
      have h0 : HasDerivAt (physHermite m) (2 * m * physHermite (m-1) x) x :=
        ih m (by omega) x
      have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      have hsub := (hlin.mul h1).sub (h0.const_mul (2 * ((m : ℝ) + 1)))
      have hf : physHermite (m+2)
          = fun y : ℝ => 2 * y * physHermite (m+1) y - 2 * ((m : ℝ)+1) * physHermite m y :=
        funext fun y => physHermite_succ_succ m y
      rw [hf]
      refine hsub.congr_deriv ?_
      have hrec := physHermite_rec m x
      push_cast
      nlinarith [hrec]

theorem physHermite_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (physHermite (n+1)) (2 * (n+1) * physHermite n x) x := by
  simpa using physHermite_hasDerivAt_aux (n+1) x

/-- Every physicists' Hermite function is the evaluation of a polynomial. -/
theorem physHermite_exists_poly (n : ℕ) :
    ∃ p : Polynomial ℝ, ∀ x : ℝ, physHermite n x = p.eval x := by
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  match n, ih with
  | 0, _ => exact ⟨1, fun x => by simp⟩
  | 1, _ => exact ⟨Polynomial.monomial 1 2, fun x => by simp⟩
  | (m+2), ih =>
      obtain ⟨p, hp⟩ := ih (m+1) (by omega)
      obtain ⟨q, hq⟩ := ih m (by omega)
      exact ⟨2 * Polynomial.X * p - 2 * Polynomial.C ((m : ℝ) + 1) * q, fun x => by
        simp [physHermite_succ_succ, hp, hq]⟩

theorem physHermite_continuous (n : ℕ) : Continuous (physHermite n) := by
  obtain ⟨p, hp⟩ := physHermite_exists_poly n
  rw [show physHermite n = _ from funext hp]
  exact p.continuous_aeval

theorem physHermite_differentiableAt (n : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (physHermite n) x := by
  obtain ⟨p, hp⟩ := physHermite_exists_poly n
  rw [show physHermite n = _ from funext hp]
  exact p.differentiableAt

/-
The diagonal Hermite–Gaussian integral: `∫ H_n(x)² e^{-x²} dx = √π · 2ⁿ · n!`.
-/
theorem hermite_sq_integral (n : ℕ) :
    ∫ x : ℝ, (physHermite n x)^2 * Real.exp (-x^2)
      = Real.sqrt Real.pi * 2^n * n.factorial := by
  -- For the inductive step, we use the recurrence relation for the Hermite polynomials.
  have h_recurrence : ∀ n : ℕ, ∫ x : ℝ, (physHermite (n + 1) x)^2 * Real.exp (-x^2) = 2 * (n + 1) *
    ∫ x : ℝ, (physHermite n x)^2 * Real.exp (-x^2) := by
    intro n
    have h_parts : ∀ a b : ℝ, ∫ x in a..b, (physHermite (n + 1) x)^2 * Real.exp (-x^2) =
      (physHermite (n + 1) b * (-physHermite n b * Real.exp (-b^2))) - (physHermite (n + 1) a *
      (-physHermite n a * Real.exp (-a^2))) + 2 * (n + 1) * ∫ x in a..b, (physHermite n x)^2 *
      Real.exp (-x^2) := by
      intro a b
      have h_parts : ∫ x in a..b, (physHermite (n + 1) x)^2 * Real.exp (-x^2) = (physHermite (n + 1)
        b * (-physHermite n b * Real.exp (-b^2))) - (physHermite (n + 1) a * (-physHermite n a *
        Real.exp (-a^2))) - ∫ x in a..b, (-physHermite n x * Real.exp (-x^2)) * (2 * (n + 1) *
        physHermite n x) := by
        rw [ eq_sub_iff_add_eq, ← intervalIntegral.integral_add ];
        · rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
          · intro x hx
            convert HasDerivAt.mul ( physHermite_hasDerivAt n x ) ( HasDerivAt.mul
              ( HasDerivAt.neg ( physHermite_hasDerivAt_aux n x ) )
              ( HasDerivAt.exp ( HasDerivAt.neg ( hasDerivAt_pow 2 x ) ) ) ) using 1
            have hrec := physHermite_rec n x
            simp only [ Pi.mul_apply, Pi.neg_apply ]
            norm_num
            linear_combination ( physHermite ( n + 1 ) x * Real.exp ( -x ^ 2 ) ) * hrec
          · apply_rules [ Continuous.intervalIntegrable ];
            -- The Hermite polynomials are continuous, and the exponential function is continuous,
            -- so their product is continuous.
            have h_cont : ∀ n : ℕ, Continuous (fun x : ℝ => physHermite n x) :=
              physHermite_continuous
            exact Continuous.add ( Continuous.mul ( Continuous.pow ( h_cont _ ) _ ) (
              Real.continuous_exp.comp ( Continuous.neg ( continuous_pow 2 ) ) ) ) ( Continuous.mul
              ( Continuous.mul ( Continuous.neg ( h_cont _ ) ) ( Real.continuous_exp.comp (
              Continuous.neg ( continuous_pow 2 ) ) ) ) ( Continuous.mul ( continuous_const ) (
              h_cont _ ) ) );
        · apply_rules [ Continuous.intervalIntegrable ];
          apply_rules [ Continuous.mul, Continuous.pow, Continuous.neg, continuous_id,
            continuous_const, Real.continuous_exp ];
          · induction n + 1 using Nat.strong_induction_on with | _ n ih => ?_
            rcases n with ( _ | _ | n ) <;> [ exact continuous_const; exact continuous_const.mul
                continuous_id; exact Continuous.sub ( Continuous.mul ( continuous_const.mul
                continuous_id ) ( ih _ <| by linarith ) ) ( Continuous.mul ( continuous_const.mul
                continuous_const ) ( ih _ <| by linarith ) ) ];
          · induction n + 1 using Nat.strong_induction_on with | _ n ih => ?_
            rcases n with ( _ | _ | n ) <;> [ exact continuous_const; exact continuous_const.mul
                continuous_id; exact Continuous.sub ( Continuous.mul ( continuous_const.mul
                continuous_id ) ( ih _ <| by linarith ) ) ( Continuous.mul ( continuous_const.mul
                continuous_const ) ( ih _ <| by linarith ) ) ];
          · continuity;
        · apply_rules [ Continuous.intervalIntegrable ];
          apply_rules [ Continuous.mul, Continuous.neg, Continuous.add, continuous_id,
            continuous_const, Real.continuous_exp ];
          · induction n using Nat.strong_induction_on with | _ n ih => ?_
            rcases n with ( _ | _ | n ) <;> simp_all? +decide [ physHermite ];
            · exact continuous_const;
            · continuity;
            · exact Continuous.sub ( Continuous.mul ( continuous_const.mul continuous_id' ) ( ih _
              le_rfl ) ) ( Continuous.mul ( continuous_const ) ( ih _ ( Nat.le_succ _ ) ) );
          · continuity;
          · induction n using Nat.strong_induction_on with | _ n ih => ?_
            rcases n with ( _ | _ | n ) <;> simp_all? +decide [ physHermite ];
            · exact continuous_const;
            · continuity;
            · exact Continuous.sub ( Continuous.mul ( continuous_const.mul continuous_id' ) ( ih _
              le_rfl ) ) ( Continuous.mul ( continuous_const ) ( ih _ ( Nat.le_succ _ ) ) );
      convert h_parts using 1
      norm_num [ mul_assoc, mul_comm, mul_left_comm, ← intervalIntegral.integral_const_mul ]
      ring
    -- Let's take the limit of the integration by parts formula as $a \to -\infty$ and $b \to
    -- \infty$.
    have h_limit : Filter.Tendsto (fun b => ∫ x in (-b)..b, (physHermite (n + 1) x)^2 * Real.exp
      (-x^2)) Filter.atTop (nhds (∫ x : ℝ, (physHermite (n + 1) x)^2 * Real.exp (-x^2))) ∧
      Filter.Tendsto (fun b => ∫ x in (-b)..b, (physHermite n x)^2 * Real.exp (-x^2)) Filter.atTop
      (nhds (∫ x : ℝ, (physHermite n x)^2 * Real.exp (-x^2))) := by
      constructor <;> apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral ];
      any_goals exact Filter.tendsto_id;
      · -- The product of a polynomial and a Gaussian function is integrable.
        have h_integrable : ∀ p : Polynomial ℝ, MeasureTheory.Integrable (fun x => p.eval x *
          Real.exp (-x^2)) MeasureTheory.volume := by
          intro p
          have h_integrable : ∀ k : ℕ, MeasureTheory.Integrable (fun x => x^k * Real.exp (-x^2))
            MeasureTheory.volume := by
            intro k;
            have := @integrable_rpow_mul_exp_neg_mul_sq;
            simpa using @this 1 zero_lt_one k ( by linarith );
          simp_all? +decide [ Polynomial.eval_eq_sum_range ];
          simp +decide only [Finset.sum_mul _ _ _, mul_assoc];
          exact MeasureTheory.integrable_finset_sum _ fun i hi => MeasureTheory.Integrable.const_mul
            ( h_integrable i ) _;
        -- By definition of Hermite polynomials, we know that they are polynomials.
        have h_hermite_poly : ∀ n : ℕ, ∃ p : Polynomial ℝ, ∀ x : ℝ, physHermite n x = p.eval x := by
          intro n
          induction n using Nat.strong_induction_on with | _ n ih => ?_
          rcases n with ( _ | _ | n ) <;> simp_all? +decide [ physHermite_succ_succ ]
          · exact ⟨ 1, fun x => by norm_num ⟩;
          · exact ⟨ Polynomial.monomial 1 2, fun x => by norm_num ⟩;
          · obtain ⟨ p, hp ⟩ := ih ( n + 1 ) ( by linarith )
            obtain ⟨ q, hq ⟩ := ih n ( by linarith )
            exact ⟨ 2 * Polynomial.X * p - 2 * ( Polynomial.C ( n + 1 : ℝ ) ) * q, fun x =>
                by simp +decide [ hp, hq ] ⟩
        obtain ⟨ p, hp ⟩ := h_hermite_poly ( n + 1 ) ; simp_all? +decide [ sq, mul_assoc ] ;
        convert h_integrable ( p * p ) using 1 ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      · exact Filter.tendsto_neg_atTop_atBot;
      · -- The function $x \mapsto (physHermite n x)^2 * \exp(-x^2)$ is integrable because
        -- it is a polynomial times a Gaussian.
        have h_integrable : ∀ p : Polynomial ℝ, MeasureTheory.Integrable (fun x => p.eval x *
          Real.exp (-x^2)) MeasureTheory.volume := by
          intro p
          have h_integrable : ∀ k : ℕ, MeasureTheory.Integrable (fun x => x^k * Real.exp (-x^2))
            MeasureTheory.volume := by
            intro k;
            have := @integrable_rpow_mul_exp_neg_mul_sq;
            simpa using @this 1 zero_lt_one k ( by linarith );
          simp_all? +decide [ Polynomial.eval_eq_sum_range ];
          simp +decide only [Finset.sum_mul _ _ _, mul_assoc];
          exact MeasureTheory.integrable_finset_sum _ fun i hi => MeasureTheory.Integrable.const_mul
            ( h_integrable i ) _;
        -- By definition of $physHermite$, we know that $physHermite n$ is a polynomial.
        have h_poly : ∀ n : ℕ, ∃ p : Polynomial ℝ, ∀ x : ℝ, physHermite n x = p.eval x := by
          intro n
          induction n using Nat.strong_induction_on with | _ n ih => ?_
          rcases n with ( _ | _ | n ) <;> simp_all? +decide [ physHermite_succ_succ ]
          · exact ⟨ 1, fun x => by norm_num ⟩;
          · exact ⟨ Polynomial.monomial 1 2, fun x => by norm_num ⟩;
          · obtain ⟨ p, hp ⟩ := ih ( n + 1 ) ( by linarith )
            obtain ⟨ q, hq ⟩ := ih n ( by linarith )
            exact ⟨ 2 * Polynomial.X * p - 2 * ( Polynomial.C ( n + 1 : ℝ ) ) * q, fun x =>
                by simp +decide [ hp, hq ] ⟩
        obtain ⟨ p, hp ⟩ := h_poly n
        specialize h_integrable ( p ^ 2 )
        simp_all +decide [ sq, mul_assoc ]
      · exact Filter.tendsto_neg_atTop_atBot;
    -- Let's take the limit of the boundary terms as $b \to \infty$.
    have h_boundary : Filter.Tendsto (fun b => physHermite (n + 1) b * (-physHermite n b * Real.exp
      (-b^2))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun b => physHermite (n + 1) (-b) *
      (-physHermite n (-b) * Real.exp (-(-b)^2))) Filter.atTop (nhds 0) := by
      have h_boundary : ∀ p : Polynomial ℝ, Filter.Tendsto (fun x => p.eval x * Real.exp (-x^2))
        Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => p.eval (-x) * Real.exp (-x^2)) Filter.atTop
        (nhds 0) := by
        intro p
        have h_poly_exp : Filter.Tendsto (fun x => p.eval x * Real.exp (-x^2)) Filter.atTop (nhds 0)
          := by
          have h_poly_exp : ∀ k : ℕ, Filter.Tendsto (fun x => x^k * Real.exp (-x^2)) Filter.atTop
            (nhds 0) := by
            intro k;
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
            refine squeeze_zero_norm' ?_ this;
            filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx using by
              rw [ Real.norm_of_nonneg ( by positivity ) ]
              gcongr
              nlinarith
          simp_all +decide [ Polynomial.eval_eq_sum_range ];
          simpa [ Finset.sum_mul _ _ _, mul_assoc ] using tendsto_finset_sum _ fun i hi =>
            Filter.Tendsto.const_mul ( p.coeff i ) ( h_poly_exp i )
        have h_poly_exp_neg : Filter.Tendsto (fun x => p.eval (-x) * Real.exp (-x^2)) Filter.atTop
          (nhds 0) := by
          have h_poly_exp_neg : ∀ q : Polynomial ℝ, Filter.Tendsto (fun x => q.eval x * Real.exp
            (-x^2)) Filter.atTop (nhds 0) := by
            intro q
            have h_poly_exp_neg : ∀ k : ℕ, Filter.Tendsto (fun x => x^k * Real.exp (-x^2))
              Filter.atTop (nhds 0) := by
              intro k;
              have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
              refine squeeze_zero_norm' ?_ this;
              filter_upwards [ Filter.eventually_ge_atTop 1 ] with x hx using by
                rw [ Real.norm_of_nonneg ( by positivity ) ]
                gcongr
                nlinarith
            simp_all +decide [ Polynomial.eval_eq_sum_range ];
            simpa [ Finset.sum_mul _ _ _, mul_assoc ] using tendsto_finset_sum _ fun i hi =>
              Filter.Tendsto.const_mul ( q.coeff i ) ( h_poly_exp_neg i );
          convert h_poly_exp_neg ( p.comp ( -Polynomial.X ) ) using 2 ; norm_num
        exact ⟨h_poly_exp, h_poly_exp_neg⟩;
      have h_poly : ∀ n : ℕ, ∃ p : Polynomial ℝ, ∀ x : ℝ, physHermite n x = p.eval x := by
        intro n
        induction n using Nat.strong_induction_on with | _ n ih => ?_
        rcases n with ( _ | _ | n ) <;> simp_all? +decide [ physHermite_succ_succ ]
        · exact ⟨ 1, fun x => by norm_num ⟩;
        · exact ⟨ Polynomial.monomial 1 2, fun x => by norm_num ⟩;
        · obtain ⟨ p, hp ⟩ := ih ( n + 1 ) ( by linarith )
          obtain ⟨ q, hq ⟩ := ih n ( by linarith )
          exact ⟨ 2 * Polynomial.X * p - 2 * ( Polynomial.C ( n + 1 : ℝ ) ) * q, fun x =>
              by simp +decide [ hp, hq ] ⟩
      obtain ⟨ p, hp ⟩ := h_poly ( n + 1 )
      obtain ⟨ q, hq ⟩ := h_poly n
      simp_all? +decide [ ← mul_assoc ]
      have := h_boundary ( p * q )
      simp_all +decide only [ mul_assoc, mul_comm, Polynomial.eval_mul ]
      exact ⟨ by simpa using this.1.neg, by simpa using this.2.neg ⟩;
    linarith [ tendsto_nhds_unique h_limit.1 ( by simpa only [ h_parts ] using Filter.Tendsto.add (
        Filter.Tendsto.sub h_boundary.1 h_boundary.2 ) ( tendsto_const_nhds.mul h_limit.2 ) ) ];
  induction n with
  | zero => ?_
  | succ n ih => ?_
  · simpa [ physHermite_zero ] using integral_gaussian ( 1 : ℝ );
  · rw [ h_recurrence, ih ] ; push_cast [ Nat.factorial_succ, pow_succ' ] ; ring

theorem hermite_normalization (n : ℕ) :
    ∫ x : ℝ, (physHermite n x / n.factorial)^2 * Real.exp (-x^2)
      = Real.sqrt Real.pi * 2^n / n.factorial := by
  convert congr_arg ( fun x : ℝ => x / ( n.factorial : ℝ ) ^ 2 ) ( hermite_sq_integral n ) using 1
    <;> ring;
  · rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ; ring;
  · simp +decide [ sq, mul_assoc, Nat.factorial_ne_zero ]

end PhysHSGaussian
