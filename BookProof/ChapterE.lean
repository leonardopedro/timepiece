import Mathlib

/-!
# Chapter E — Wave-function collapse versus Euler's formula

Formalization of the theorem-rich Chapter E of `book.tex`
(see `FORMALIZATION_ROADMAP.md` §E): the wave-function as a "multi-dimensional
Euler formula" parametrizing any probability distribution, with collapse =
"taking the real part."
-/

open scoped Matrix BigOperators
open Filter
open scoped Topology

namespace BookProof.ChapterE

/-! ## E.1 — The 2-state probability clock -/

/-- The 2-state wave function `Ψ t = (cos t, sin t)`. -/
noncomputable def Ψ (t : ℝ) : Fin 2 → ℝ := ![Real.cos t, Real.sin t]

/-- The rotation generator `J = [[0,-1],[1,0]]`. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-
**E.1a (surjectivity of the Born map).** Every probability `p ∈ [0,1]` is
realized as `cos² t` for some angle `t`.
-/
theorem cos_sq_surjective {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ t : ℝ, Real.cos t ^ 2 = p := by
  refine ⟨ Real.arccos ( Real.sqrt p ), ?_ ⟩
  rw [ Real.cos_arccos ] <;> nlinarith [ Real.mul_self_sqrt hp0 ]

/-
**E.1b (Euler rotation).** The matrix exponential of `t • J` is the rotation
matrix `[[cos t, -sin t],[sin t, cos t]]`.
-/
theorem exp_J (t : ℝ) :
    NormedSpace.exp (t • J) = !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t] := by
  -- By definition of matrix exponential, we know that
  have h_exp : NormedSpace.exp (t • J) = ∑' n, (t ^ n / Nat.factorial n) • (J ^ n) := by
    simp only [div_eq_inv_mul];
    convert NormedSpace.exp_eq_tsum using 3;
    constructor;
    · exact fun _ 𝕂 {_} _ _ _ _ _ _ ↦ NormedSpace.exp_eq_tsum 𝕂;
    intro h; rw [ h ℝ ] ; simp [ mul_comm, smul_pow ] ;
    simp [ mul_comm, smul_smul ];
  -- We'll use the fact that $J^2 = -I$ to simplify the series.
  have h_simp : ∀ n : ℕ, J ^ (2 * n) = (-1 : ℝ) ^ n • 1 ∧ J ^ (2 * n + 1) = (-1 : ℝ) ^ n • J := by
    intro n; induction n <;> simp_all [ Nat.mul_succ, pow_succ, pow_mul ] ;
    simp_all [ show J * J = -1 from by ext i j; fin_cases i <;> fin_cases j <;> norm_num [ J ] ];
  -- Let's split the sum into two parts: one for even $n$ and one for odd $n$.
  have h_split : ∑' n, (t ^ n / Nat.factorial n) • (J ^ n) =
      (∑' n, (t ^ (2 * n) / Nat.factorial (2 * n)) • (J ^ (2 * n))) +
        (∑' n, (t ^ (2 * n + 1) / Nat.factorial (2 * n + 1)) • (J ^ (2 * n + 1))) := by
    rw [ ← tsum_even_add_odd ];
    · simp_all only [] ;
      have := Real.hasSum_cos t;
      convert this.summable.smul_const ( 1 : Matrix ( Fin 2 ) ( Fin 2 ) ℝ ) using 2 ; ring;
      rw [ smul_smul, mul_comm ];
    · simp_all only [← smul_assoc, smul_eq_mul];
      refine Summable.smul_const ?_ _
      refine Summable.of_norm ?_
      simp
      have base := Real.summable_pow_div_factorial (|t| : ℝ)
      refine Summable.comp_injective base ?_
      intro m n h
      simpa using h
  simp_all only [← smul_assoc, smul_eq_mul];
  -- Recognize that the sums are the Taylor series for $\cos t$ and $\sin t$.
  have h_cos_sin :
      (∑' n, (t ^ (2 * n) / Nat.factorial (2 * n)) * (-1) ^ n) = Real.cos t ∧
        (∑' n, (t ^ (2 * n + 1) / Nat.factorial (2 * n + 1)) * (-1) ^ n) = Real.sin t := by
    constructor
    · rw [ Real.cos_eq_tsum ]
      exact tsum_congr fun n => by ring
    · rw [ Real.sin_eq_tsum ]
      exact tsum_congr fun n => by ring
  rw [ Summable.tsum_smul_const, Summable.tsum_smul_const ] ;
  focus (norm_num [ h_cos_sin ]);
  · ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ J ];
  · refine Summable.of_norm ?_
    simp
    have base := Real.summable_pow_div_factorial (|t| : ℝ)
    refine Summable.comp_injective base ?_
    intro m n h
    simpa using h
  · refine Summable.of_norm ?_
    simp
    have base := Real.summable_pow_div_factorial (|t| : ℝ)
    refine Summable.comp_injective base ?_
    intro m n h
    simpa using h

/-
**E.1b (rotation acts on the clock).** The rotation by `t` sends the initial
state `(1,0)` to `Ψ t`.
-/
theorem exp_J_mulVec (t : ℝ) : (NormedSpace.exp (t • J)) *ᵥ ![1, 0] = Ψ t := by
  convert congr_arg ( fun m : Matrix ( Fin 2 ) ( Fin 2 ) ℝ => m *ᵥ ![1, 0] ) ( exp_J t ) using 1;
  ext i; fin_cases i <;> norm_num [ Ψ ] ;

/-
**E.1c (collapse = diagonal / real part).** The collapsed (diagonal) density
matrix of `Ψ t` is `½·I + ½cos(2t)·diag(1,-1)`.
-/
theorem collapse_density (t : ℝ) :
    (!![Real.cos t ^ 2, 0; 0, Real.sin t ^ 2] : Matrix (Fin 2) (Fin 2) ℝ)
      = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        + (1 / 2 * Real.cos (2 * t)) • !![1, 0; 0, -1] := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Real.sin_sq, Real.cos_sq ] <;> ring

/-! ## E.2 — Probability-preserving linear maps -/

/-
**E.2b (uniform → vertex forces singularity).** A column-stochastic `2×2`
matrix that maps the uniform distribution `(½,½)` to the vertex `(1,0)` is
singular (`det = 0`); hence it is not an invertible symmetry.
-/
theorem stochastic_uniform_to_vertex_singular
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hnonneg : ∀ i j, 0 ≤ M i j)
    (hcol : ∀ j, ∑ i, M i j = 1)
    (huniform : M *ᵥ ![1 / 2, 1 / 2] = ![1, 0]) :
    M.det = 0 := by
  simp_all [ funext_iff, Fin.forall_fin_two, Matrix.det_fin_two ];
  norm_num [ Matrix.mulVec ] at huniform ; nlinarith!

/-! ## E.3 — A unitary that uniformizes every basis state -/

/-
**E.3 (Hadamard, `n = 2`).** The normalized Hadamard matrix is unitary and
maps every basis state to the uniform Born distribution `|·|² = 1/2`.
-/
theorem hadamard_uniformizes :
    let H : Matrix (Fin 2) (Fin 2) ℂ :=
      (1 / Real.sqrt 2 : ℂ) • !![1, 1; 1, -1]
    Hᴴ * H = 1 ∧ ∀ i j, ‖H i j‖ ^ 2 = 1 / 2 := by
  norm_num [ Fin.forall_fin_two, ← Matrix.ext_iff ];
  norm_num [ Matrix.mul_apply, Complex.ext_iff ];
  ring_nf; norm_num;

/-
**E.3 (general `n`).** For every `n ≥ 1` there is a unitary `n × n` matrix
that maps every computational basis state to the uniform Born distribution
`|·|² = 1/n` (the DFT / "black hole" uniformizer).
-/
theorem exists_uniformizer (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ ∀ i j, ‖U i j‖ ^ 2 = 1 / n := by
  have hn0 : n ≠ 0 := by omega
  let U : Matrix (Fin n) (Fin n) ℂ := fun i j =>
      Complex.exp (2 * Real.pi * Complex.I * i.val * j.val / n) / Real.sqrt n
  have hUent : ∀ a b : Fin n, U a b =
      Complex.exp (2 * Real.pi * Complex.I * a.val * b.val / n) / Real.sqrt n := fun _ _ => rfl
  refine ⟨U, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hUent]
    have hn0c : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hterm : ∀ x : Fin n,
        star (Complex.exp (2 * Real.pi * Complex.I * x.val * i.val / n) / Real.sqrt n) *
          (Complex.exp (2 * Real.pi * Complex.I * x.val * j.val / n) / Real.sqrt n)
        = (n : ℂ)⁻¹ *
            Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n) := by
      intro x
      rw [star_div₀, Complex.star_def, ← Complex.exp_conj, Complex.conj_ofReal]
      have hsa : star (2 * Real.pi * Complex.I * x.val * i.val / n)
          = -(2 * Real.pi * Complex.I * x.val * i.val / n) := by
        simp [star_mul, star_div₀, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [Complex.star_def] at hsa
      rw [hsa, div_mul_div_comm, ← Complex.exp_add]
      have hs2 : ((Real.sqrt n : ℝ) : ℂ) * Real.sqrt n = (n : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity : 0 ≤ (n : ℝ))]
        rfl
      rw [hs2]
      rw [show -((2 * Real.pi * Complex.I * x.val * i.val) / n)
              + (2 * Real.pi * Complex.I * x.val * j.val / n)
            = 2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n by ring]
      rw [div_eq_mul_inv, mul_comm]
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
    by_cases hij : i = j
    · rw [if_pos hij]
      have h0 : ∑ x : Fin n,
          Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n) = (n : ℂ) := by
        have hterm0 : ∀ x : Fin n,
            Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n) = 1 := by
          intro x
          rw [show (j.val - i.val : ℂ) = 0 from by rw [hij]; ring, mul_zero, zero_div,
            Complex.exp_zero]
        rw [Finset.sum_congr rfl (fun x _ => hterm0 x), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, Nat.smul_one_eq_cast]
      rw [h0, mul_comm, mul_inv_cancel₀ hn0c]
    · rw [if_neg hij]
      have hne : Complex.exp (2 * Real.pi * Complex.I * (j.val - i.val) / n) ≠ 1 := by
        intro h
        obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
        rw [← mul_div_assoc'] at hk
        rw [show ((k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
              = (2 * Real.pi * Complex.I) * ((k : ℤ) : ℂ) from by ring] at hk
        have h2 : (j.val - i.val : ℂ) / (n : ℂ) = ((k : ℤ) : ℂ) :=
          mul_left_cancel₀ Complex.two_pi_I_ne_zero hk
        have h4 : (j.val - i.val : ℂ) = ((k : ℤ) : ℂ) * (n : ℂ) := by
          rw [← div_eq_iff hn0c]
          exact h2
        have hr : ((k * (n : ℤ)) : ℂ) = ((k : ℤ) : ℂ) * (n : ℂ) := by norm_cast
        have hl : (((j.val : ℤ) - (i.val : ℤ)) : ℂ) = (j.val - i.val : ℂ) := by norm_cast
        have h5 : (((j.val : ℤ) - (i.val : ℤ)) : ℂ) = ((k * (n : ℤ)) : ℂ) := by
          rw [hl, h4, hr]
        have h4' : ((j.val : ℤ) - (i.val : ℤ)) = k * (n : ℤ) := by exact_mod_cast h5
        have hi : i.val < n := Fin.is_lt i
        have hj : j.val < n := Fin.is_lt j
        have hij' : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
        by_cases hk0 : k = 0
        · rw [hk0, zero_mul] at h4'
          omega
        · have hz : (0 : ℤ) < |k| := abs_pos.mpr hk0
          have hz1 : (1 : ℤ) ≤ |k| := by omega
          have hn0z : (0 : ℤ) < n := by omega
          have hle1 : (n : ℤ) ≤ |k| * n := by nlinarith [hz1, hn0z]
          have h8 : |k| * n = |(j.val : ℤ) - (i.val : ℤ)| := by
            rw [h4', abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ n)]
          have hb : |(j.val : ℤ) - (i.val : ℤ)| ≤ (n : ℤ) - 1 := by
            apply abs_le.mpr
            constructor <;> omega
          have hcon : (n : ℤ) ≤ (n : ℤ) - 1 :=
            le_trans hle1 (le_trans (le_of_eq h8) hb)
          omega
      have hpow : Complex.exp (2 * Real.pi * Complex.I * (j.val - i.val) / n) ^ n = 1 := by
        rw [← Complex.exp_nat_mul, mul_div_assoc', mul_div_cancel_left₀ _ hn0c]
        refine Complex.exp_eq_one_iff.mpr ⟨(j.val : ℤ) - i.val, ?_⟩
        rw [show (j.val - i.val : ℂ) = (((j.val : ℤ) - i.val : ℤ) : ℂ) from by norm_cast]
        ring
      have hsum : ∑ x : Fin n,
          Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n) = 0 := by
        have hterm_pow : ∀ x : Fin n,
            Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n)
              = Complex.exp (2 * Real.pi * Complex.I * (j.val - i.val) / n) ^ x.val := by
          intro x
          rw [← Complex.exp_nat_mul]
          ring_nf
        rw [Finset.sum_congr rfl (fun x _ => hterm_pow x), ← Finset.sum_range,
          geom_sum_eq hne, hpow, sub_self, zero_div]
      rw [hsum, mul_zero]
  · intro i j
    rw [hUent]
    norm_num [Complex.norm_exp]

/-! ## E.4 — Hyperspherical Born recursion onto the simplex -/

/-- The stick-breaking / hyperspherical Born map:
`Θ(θ)ₙ = (∏_{k<n} sin²θ_k)·cos²θ_n`. -/
noncomputable def stickBreaking {N : ℕ} (θ : Fin N → ℝ) (n : Fin N) : ℝ :=
    (∏ k ∈ Finset.Iio n, Real.sin (θ k) ^ 2) * Real.cos (θ n) ^ 2

/-
**E.4 (surjectivity onto the simplex).** Every probability distribution `P`
on `Fin N` is realized by the hyperspherical Born recursion of a real unit
vector, i.e. the stick-breaking map is surjective onto the probability simplex.
-/
theorem stickBreaking_surjective {N : ℕ} (P : Fin N → ℝ)
    (hP0 : ∀ n, 0 ≤ P n) (hPsum : ∑ n, P n = 1) :
    ∃ θ : Fin N → ℝ, ∀ n, stickBreaking θ n = P n := by
  induction N with
  | zero => ?_
  | succ N ih => ?_
  · aesop;
  · -- Define the tail T_n for n in Fin (N+1)
    let T : Fin (N + 1) → ℝ := fun n => ∑ k ∈ Finset.Ici n, P k;
    -- Prove that $T_n$ is nonincreasing, $T_0 = 1$, each $T_n \geq 0$, and $T_n = P_n + T_{n+1}$
    -- for the successor within range.
    have hT_noninc : ∀ n m : Fin (N + 1), n ≤ m → T m ≤ T n := by
      exact fun n m hnm =>
        Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Ici_subset_Ici.mpr hnm ) fun _ _ _ => hP0 _
    have hT0 : T 0 = 1 := by
      convert hPsum using 1;
      exact Finset.sum_subset ( Finset.subset_univ _ ) fun x hx₁ hx₂ => by aesop;
    have hT_pos : ∀ n : Fin (N + 1), 0 ≤ T n := by
      exact fun n => Finset.sum_nonneg fun _ _ => hP0 _
    have hT_succ : ∀ n : Fin N, T (Fin.succ n) = T (Fin.castSucc n) - P (Fin.castSucc n) := by
      intro n; simp only [T] ; ring;
      rw [ eq_sub_iff_add_eq',
        ← Finset.sum_erase_add _ _
          ( show n.castSucc ∈ Finset.Ici n.castSucc from Finset.mem_Ici.mpr le_rfl ),
        add_comm ];
      rcongr k ; aesop;
    -- Choose angles: for each `n`, if `T n > 0` pick `θ n` with `Real.cos (θ n) ^ 2 = P n / T n`
    -- (possible by `cos_sq_surjective`, since `0 ≤ P n / T n ≤ 1` as `0 ≤ P n ≤ T n`); if `T n = 0`
    -- pick `θ n` with `Real.cos (θ n)^2 = 0` i.e. `θ n = π/2` so `Real.sin (θ n)^2 = 1`...
    obtain ⟨θ, hθ⟩ : ∃ θ : Fin (N + 1) → ℝ,
        ∀ n : Fin (N + 1), Real.cos (θ n) ^ 2 = if T n > 0 then P n / T n else 0 := by
      use fun n => Real.arccos ( Real.sqrt ( if T n > 0 then P n / T n else 0 ) );
      intro n; split_ifs <;> simp_all only [gt_iff_lt, ↓reduceIte, Real.sqrt_div, not_lt, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]  ;
      · rw [ Real.cos_arccos ];
        · rw [ div_pow, Real.sq_sqrt ( hP0 n ), Real.sq_sqrt ( hT_pos n ) ];
        · exact le_trans ( by norm_num )
            ( div_nonneg ( Real.sqrt_nonneg _ ) ( Real.sqrt_nonneg _ ) );
        · exact div_le_one_of_le₀
            ( Real.sqrt_le_sqrt <| Finset.single_le_sum ( fun a _ => hP0 a ) <|
              Finset.mem_Ici.mpr <| le_refl n ) <| Real.sqrt_nonneg _;
      · rw [ if_neg ( by linarith [ hT_pos n ] ) ] ; norm_num [ Real.cos_arccos ];
    -- Prove that $\prod_{k < n} \sin^2(\theta_k) = T_n$.
    have h_prod_sin_sq : ∀ n : Fin (N + 1), (∏ k ∈ Finset.Iio n, Real.sin (θ k) ^ 2) = T n := by
      intro n
      induction n using Fin.induction with
      | zero => ?_
      | succ n ih => ?_
      · aesop;
      · rw [ show ( Finset.Iio ( Fin.succ n ) : Finset ( Fin ( N + 1 ) ) ) =
            Finset.Iio ( Fin.castSucc n ) ∪ { Fin.castSucc n } from ?_,
          Finset.prod_union ] <;> norm_num [ ih, hT_succ ];
        · rw [ Real.sin_sq, hθ ];
          grind;
        · ext; simp only [Finset.mem_Iio, Finset.mem_Iic];
          exact ⟨ fun h => Nat.le_of_lt_succ h, fun h => Nat.lt_succ_of_le h ⟩;
    use θ; intro n; simp only [stickBreaking, h_prod_sin_sq, hθ, gt_iff_lt, mul_ite, mul_zero] ;
    split_ifs <;> simp_all only [gt_iff_lt, ne_eq, ne_of_gt, not_false_eq_true, mul_div_cancel₀,
        not_lt];
    exact Eq.symm ( le_antisymm
      ( le_trans ( Finset.single_le_sum ( fun a _ => hP0 a ) ( by aesop ) ) ‹T n ≤ 0› )
      ( hP0 n ) )

end BookProof.ChapterE
