import BookProof.Ultrafinitism.ChapterMehlerFeasibility
import BookProof.Ultrafinitism.ChapterGramPolyDecision

/-!
# Chapter UltrafinitistSirk — Ultrafinitist Hashimoto/SIRK with Horizon-`M` Convergence

This module converts the Hashimoto shift-invert and Shift-Invert Rational Krylov (SIRK)
algorithm (`BookProof/Sirk/ChapterHashimotoShiftInvert.lean`,
`BookProof/Textbook/ChapterH4.lean`, `BookProof/Sirk/ChapterSirkEndToEnd.lean`,
`BookProof/Sirk/ChapterSirkTruncation.lean`, `BookProof/Sirk/ChapterSirkRestart.lean`)
into the strictly finite, rational **Ultrafinitist Solovay–Mehler–Kopperman (`U-SMK`)**
framework of `BookProof/Ultrafinitism/`.

Everything over `ℚ` is completely computable (zero `noncomputable` on rational operators
and approximations, zero `Real.exp`, zero `Real.sqrt`, zero `sorry`, zero `native_decide`,
zero custom axioms, and **zero unproved Crouzeix hypotheses**).

## Main results

* `uHashimoto_shift_bound`, `uShiftInvert_opBound`, `uShiftInvert_perturbation_bound`,
  `hashimoto_shift_transfer_identity` — exact rational Hashimoto shift-invert bounds over `ℚ`
  and the shift-transfer identity `(H + (γ - τ) I)⁻¹ = (I - τ X)⁻¹ X`.
* `uKrylov_pow_transfer`, `uKrylov_poly_transfer`, `uKrylov_block_compat` — unconditional
  exact Krylov compression `B = Vᵀ X V` and polynomial transfer on the Krylov subspace.
* `neumannPoly`, `neumann_remainder_identity`, `inv_one_sub_opBound`, `uSirk_error_bound`,
  `uSirk_error_bound_leaky` — computable rational U-SIRK approximant and unconditional
  geometric error bound `‖(I - τ X)⁻¹ v - V (I - τ B)⁻¹ Vᵀ v‖ ≤ 2 qᵐ / (1 - q) ‖v‖`
  (plus rank-truncated / leaky-seed variant).
* `uSirk_converges_at_horizon`, `uSirk_converges_to_M_tol_log_steps`,
  `uSirk_exact_at_full_horizon`, `uSirk_horizon_total_tolerance`,
  `uSirk_order_mehler_feasible` — explicit **horizon-`M`-controlled convergence**:
  for `q = 1 - β` error is `≤ 2 / (β (1 + M β))`; for `q ≤ 1 / 2` tolerance `1 / M` is
  reached in `m = ⌊log₂ M⌋ + 3 ≤ M` steps while remaining feasible under `mehlerFeasEffect`;
  at full horizon `m = M + 1` error vanishes identically; and horizon-`M` Hamiltonian
  perturbations `O(1/M)` add linearly.
* `uSirk_isometry_decideGram`, `uSirk_ritz_residual_bound`,
  `krawtchouk_uSirk_converges_to_M_tol` — `decideGram` verification of Krylov bases,
  rational Ritz residual certificate, and concrete Krawtchouk number-Hamiltonian witness.
* `opBound_transpose`, `uSirk_fullSpace_block_bound`, `uSirkBudget_antitone_m`,
  `uSirkBudget_log_le`, `uSirkBudget_log_antitone_M`, `uSirk_finite_M_certifies_U4_gap`,
  `uSirk_finite_M_certifies_U3_gap`, `uSirk_schur_head_tail_positive`,
  `uSirk_U4_schur_head_tail_margin`, `uSirk_dyadic_order_eq`,
  `uSirk_dyadic_error_sum_bound`, `uSirk_c6_telescoping_bound` — `U2`/`U3`/`U4` block,
  non-growth, finite-`M` stopping, pure-`ℚ` Schur head-plus-tail coercivity, and dyadic `C6`
  Cauchy-increment (`≤ C / 6`) theorems.
-/

namespace BookProof.Ultrafinitism.ChapterUltrafinitistSirk

open scoped BigOperators Matrix
open BookProof.Ultrafinitism.ChapterGramPolyDecision
open BookProof.Ultrafinitism.ChapterMehlerFeasibility

/-! ## 1. Exact rational Euclidean geometry and operator bounds over `ℚ` -/

/-- Rational Euclidean inner product on `Fin N → ℚ`. -/
def vecDot {N : ℕ} (u v : Fin N → ℚ) : ℚ :=
  ∑ i : Fin N, u i * v i

/-- Rational squared Euclidean norm on `Fin N → ℚ`. -/
def vecSqNorm {N : ℕ} (v : Fin N → ℚ) : ℚ :=
  ∑ i : Fin N, v i ^ 2

theorem vecSqNorm_nonneg {N : ℕ} (v : Fin N → ℚ) : 0 ≤ vecSqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem vecDot_self {N : ℕ} (v : Fin N → ℚ) : vecDot v v = vecSqNorm v := by
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem vecDot_symm {N : ℕ} (u v : Fin N → ℚ) : vecDot u v = vecDot v u := by
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem vecDot_add_left {N : ℕ} (u v w : Fin N → ℚ) :
    vecDot (u + v) w = vecDot u w + vecDot v w := by
  simp [vecDot, add_mul, Finset.sum_add_distrib]

theorem vecDot_add_right {N : ℕ} (u v w : Fin N → ℚ) :
    vecDot u (v + w) = vecDot u v + vecDot u w := by
  simp [vecDot, mul_add, Finset.sum_add_distrib]

theorem vecDot_sub_right {N : ℕ} (u v w : Fin N → ℚ) :
    vecDot u (v - w) = vecDot u v - vecDot u w := by
  simp [vecDot, mul_sub, Finset.sum_sub_distrib]

theorem vecDot_smul_left {N : ℕ} (c : ℚ) (u v : Fin N → ℚ) :
    vecDot (c • u) v = c * vecDot u v := by
  simp [vecDot, Finset.mul_sum, mul_assoc]

theorem vecDot_smul_right {N : ℕ} (c : ℚ) (u v : Fin N → ℚ) :
    vecDot u (c • v) = c * vecDot u v := by
  simp only [vecDot, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem vecSqNorm_smul {N : ℕ} (c : ℚ) (v : Fin N → ℚ) :
    vecSqNorm (c • v) = c ^ 2 * vecSqNorm v := by
  simp [vecSqNorm, Finset.mul_sum, mul_pow]

theorem vecSqNorm_neg {N : ℕ} (v : Fin N → ℚ) : vecSqNorm (-v) = vecSqNorm v := by
  simp [vecSqNorm]

theorem vecSqNorm_add_eq {N : ℕ} (u v : Fin N → ℚ) :
    vecSqNorm (u + v) = vecSqNorm u + 2 * vecDot u v + vecSqNorm v := by
  unfold vecSqNorm vecDot
  have h : (∑ i : Fin N, (u + v) i ^ 2) =
      ∑ i : Fin N, (u i ^ 2 + 2 * (u i * v i) + v i ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  rw [h, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem vecSqNorm_sub_eq {N : ℕ} (u v : Fin N → ℚ) :
    vecSqNorm (u - v) = vecSqNorm u - 2 * vecDot u v + vecSqNorm v := by
  unfold vecSqNorm vecDot
  have h : (∑ i : Fin N, (u - v) i ^ 2) =
      ∑ i : Fin N, (u i ^ 2 - 2 * (u i * v i) + v i ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    ring
  rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem vecSqNorm_sub_comm {N : ℕ} (u v : Fin N → ℚ) :
    vecSqNorm (u - v) = vecSqNorm (v - u) := by
  rw [← vecSqNorm_neg (u - v), neg_sub]

theorem ratQuad_eq_vecDot {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℚ) :
    ratQuad A v = vecDot v (A.mulVec v) := by
  unfold ratQuad vecDot
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem vecDot_mulVec_transpose {N K : ℕ} (A : Matrix (Fin N) (Fin K) ℚ)
    (u : Fin K → ℚ) (v : Fin N → ℚ) :
    vecDot v (A.mulVec u) = vecDot (Aᵀ.mulVec v) u := by
  unfold vecDot
  change v ⬝ᵥ A.mulVec u = Aᵀ.mulVec v ⬝ᵥ u
  have h1 : Aᵀ.mulVec v = v ᵥ* A := by
    simpa [Matrix.transpose_transpose] using (Matrix.vecMul_transpose Aᵀ v).symm
  rw [Matrix.dotProduct_mulVec, h1, dotProduct_comm]

/-- Rational Cauchy–Schwarz inequality on `Fin N → ℚ`. -/
theorem vecDot_sq_le {N : ℕ} (u v : Fin N → ℚ) :
    vecDot u v ^ 2 ≤ vecSqNorm u * vecSqNorm v := by
  simpa [vecDot, vecSqNorm] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N)) u v

/-- Rational triangle inequality in squared-norm form (no `Real.sqrt`). -/
theorem vecSqNorm_add_le {N : ℕ} {u v : Fin N → ℚ} {a b : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : vecSqNorm u ≤ a ^ 2) (hv : vecSqNorm v ≤ b ^ 2) :
    vecSqNorm (u + v) ≤ (a + b) ^ 2 := by
  have hcs := vecDot_sq_le u v
  have hmul : vecSqNorm u * vecSqNorm v ≤ a ^ 2 * b ^ 2 :=
    mul_le_mul hu hv (vecSqNorm_nonneg v) (sq_nonneg a)
  have hdot : vecDot u v ≤ a * b := by nlinarith [mul_nonneg ha hb]
  rw [vecSqNorm_add_eq]
  nlinarith

theorem vecSqNorm_sub_le {N : ℕ} {u v : Fin N → ℚ} {a b : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : vecSqNorm u ≤ a ^ 2) (hv : vecSqNorm v ≤ b ^ 2) :
    vecSqNorm (u - v) ≤ (a + b) ^ 2 := by
  have hvn : vecSqNorm (-v) ≤ b ^ 2 := by simpa [vecSqNorm_neg] using hv
  simpa [sub_eq_add_neg] using vecSqNorm_add_le ha hb hu hvn

/-- Scaled rational triangle inequality in squared-norm form (`s = vecSqNorm v`). -/
theorem vecSqNorm_add_mul_le {N : ℕ} {u v : Fin N → ℚ} {c₁ c₂ s : ℚ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hs : 0 ≤ s)
    (hu : vecSqNorm u ≤ c₁ ^ 2 * s) (hv : vecSqNorm v ≤ c₂ ^ 2 * s) :
    vecSqNorm (u + v) ≤ (c₁ + c₂) ^ 2 * s := by
  have hcs := vecDot_sq_le u v
  have hprod : vecSqNorm u * vecSqNorm v ≤ (c₁ ^ 2 * s) * (c₂ ^ 2 * s) :=
    mul_le_mul hu hv (vecSqNorm_nonneg v) (mul_nonneg (sq_nonneg c₁) hs)
  have hnn : 0 ≤ c₁ * c₂ * s := mul_nonneg (mul_nonneg hc₁ hc₂) hs
  have hdot : vecDot u v ≤ c₁ * c₂ * s := by nlinarith
  rw [vecSqNorm_add_eq]
  nlinarith

/-- Rational operator-norm bound `‖A v‖² ≤ c² ‖v‖²` with `0 ≤ c` (`OpBound A c`). -/
def OpBound {N K : ℕ} (A : Matrix (Fin N) (Fin K) ℚ) (c : ℚ) : Prop :=
  0 ≤ c ∧ ∀ v : Fin K → ℚ, vecSqNorm (A.mulVec v) ≤ c ^ 2 * vecSqNorm v

theorem opBound_zero {N K : ℕ} : OpBound (0 : Matrix (Fin N) (Fin K) ℚ) 0 := by
  refine ⟨le_rfl, fun v => by simp [vecSqNorm]⟩

theorem opBound_one {N : ℕ} : OpBound (1 : Matrix (Fin N) (Fin N) ℚ) 1 := by
  refine ⟨zero_le_one, fun v => by simp⟩

theorem opBound_mono {N K : ℕ} {A : Matrix (Fin N) (Fin K) ℚ} {c₁ c₂ : ℚ}
    (h : OpBound A c₁) (hle : c₁ ≤ c₂) : OpBound A c₂ := by
  refine ⟨h.1.trans hle, fun v => ?_⟩
  have hsq : c₁ ^ 2 ≤ c₂ ^ 2 := by nlinarith [h.1, hle]
  exact (h.2 v).trans (mul_le_mul_of_nonneg_right hsq (vecSqNorm_nonneg v))

theorem opBound_smul {N K : ℕ} {A : Matrix (Fin N) (Fin K) ℚ} {c : ℚ}
    (h : OpBound A c) {τ : ℚ} (hτ : 0 ≤ τ) :
    OpBound (τ • A) (τ * c) := by
  refine ⟨mul_nonneg hτ h.1, fun v => ?_⟩
  have hmul : (τ • A).mulVec v = τ • A.mulVec v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hmul, vecSqNorm_smul]
  have h1 := mul_le_mul_of_nonneg_left (h.2 v) (sq_nonneg τ)
  nlinarith

theorem opBound_mul {N K L : ℕ} {A : Matrix (Fin N) (Fin K) ℚ} {B : Matrix (Fin K) (Fin L) ℚ}
    {cA cB : ℚ} (hA : OpBound A cA) (hB : OpBound B cB) :
    OpBound (A * B) (cA * cB) := by
  refine ⟨mul_nonneg hA.1 hB.1, fun v => ?_⟩
  rw [← Matrix.mulVec_mulVec]
  have h1 := hA.2 (B.mulVec v)
  have h2 := mul_le_mul_of_nonneg_left (hB.2 v) (sq_nonneg cA)
  nlinarith

theorem opBound_pow {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ} {c : ℚ}
    (hA : OpBound A c) (m : ℕ) : OpBound (A ^ m) (c ^ m) := by
  induction m with
  | zero => simpa using opBound_one
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact opBound_mul ih hA

theorem opBound_add {N K : ℕ} {A B : Matrix (Fin N) (Fin K) ℚ} {cA cB : ℚ}
    (hA : OpBound A cA) (hB : OpBound B cB) :
    OpBound (A + B) (cA + cB) := by
  refine ⟨add_nonneg hA.1 hB.1, fun v => ?_⟩
  rw [Matrix.add_mulVec]
  exact vecSqNorm_add_mul_le hA.1 hB.1 (vecSqNorm_nonneg v) (hA.2 v) (hB.2 v)

theorem opBound_sub {N K : ℕ} {A B : Matrix (Fin N) (Fin K) ℚ} {cA cB : ℚ}
    (hA : OpBound A cA) (hB : OpBound B cB) :
    OpBound (A - B) (cA + cB) := by
  have hneg : OpBound (-B) cB := by
    refine ⟨hB.1, fun v => ?_⟩
    have hmul : (-B).mulVec v = -(B.mulVec v) := by
      ext i
      simp [Matrix.mulVec, dotProduct]
    rw [hmul, vecSqNorm_neg]
    exact hB.2 v
  simpa [sub_eq_add_neg] using opBound_add hA hneg

/-- An isometric rational matrix `Vᵀ * V = 1` preserves squared norms. -/
theorem isometry_preserves_sqNorm {N m : ℕ} {V : Matrix (Fin N) (Fin m) ℚ}
    (hV : Vᵀ * V = 1) (y : Fin m → ℚ) :
    vecSqNorm (V.mulVec y) = vecSqNorm y := by
  rw [← vecDot_self, vecDot_mulVec_transpose, Matrix.mulVec_mulVec, hV,
    Matrix.one_mulVec, vecDot_self]

theorem isometry_opBound {N m : ℕ} {V : Matrix (Fin N) (Fin m) ℚ} (hV : Vᵀ * V = 1) :
    OpBound V 1 := by
  refine ⟨zero_le_one, fun y => ?_⟩
  rw [isometry_preserves_sqNorm hV y, one_pow, one_mul]

/-- Orthogonal Pythagoras split `‖v‖² = ‖Vᵀ v‖² + ‖v - V Vᵀ v‖²` for `Vᵀ V = 1`. -/
theorem isometry_pythagoras {N m : ℕ} {V : Matrix (Fin N) (Fin m) ℚ}
    (hV : Vᵀ * V = 1) (v : Fin N → ℚ) :
    vecSqNorm v = vecSqNorm (Vᵀ.mulVec v) + vecSqNorm (v - (V * Vᵀ).mulVec v) := by
  let p := (V * Vᵀ).mulVec v
  have hp_norm : vecSqNorm p = vecSqNorm (Vᵀ.mulVec v) := by
    change vecSqNorm ((V * Vᵀ).mulVec v) = _
    rw [← Matrix.mulVec_mulVec, isometry_preserves_sqNorm hV]
  have hdot : vecDot v p = vecSqNorm (Vᵀ.mulVec v) := by
    change vecDot v ((V * Vᵀ).mulVec v) = _
    rw [← Matrix.mulVec_mulVec, vecDot_mulVec_transpose, vecDot_self]
  change vecSqNorm v = vecSqNorm (Vᵀ.mulVec v) + vecSqNorm (v - p)
  rw [vecSqNorm_sub_eq v p, hp_norm, hdot]
  ring

theorem isometry_adjoint_contraction {N m : ℕ} {V : Matrix (Fin N) (Fin m) ℚ}
    (hV : Vᵀ * V = 1) (v : Fin N → ℚ) :
    vecSqNorm (Vᵀ.mulVec v) ≤ vecSqNorm v := by
  have hpy := isometry_pythagoras hV v
  have hnn := vecSqNorm_nonneg (v - (V * Vᵀ).mulVec v)
  linarith

theorem isometry_adjoint_opBound {N m : ℕ} {V : Matrix (Fin N) (Fin m) ℚ} (hV : Vᵀ * V = 1) :
    OpBound Vᵀ 1 := by
  refine ⟨zero_le_one, fun v => ?_⟩
  simpa using isometry_adjoint_contraction hV v

theorem opBound_compress {N m : ℕ} {V : Matrix (Fin N) (Fin m) ℚ}
    {X : Matrix (Fin N) (Fin N) ℚ} {r : ℚ}
    (hV : Vᵀ * V = 1) (hX : OpBound X r) :
    OpBound (Vᵀ * X * V) r := by
  have h1 := opBound_mul (opBound_mul (isometry_adjoint_opBound hV) hX) (isometry_opBound hV)
  simpa [mul_assoc, one_mul, mul_one] using h1

/-! ## 2. Ultrafinitist Hashimoto shift-invert bound & second resolvent identity -/

/-- A rational matrix `H` is bounded below by `e : ℚ` when `e ‖v‖² ≤ ⟨v, H v⟩`. -/
def IsLowerBounded {N : ℕ} (H : Matrix (Fin N) (Fin N) ℚ) (e : ℚ) : Prop :=
  ∀ v : Fin N → ℚ, e * vecSqNorm v ≤ ratQuad H v

/-- `R` is the exact rational shift-invert `(H + γ I)⁻¹` of `H` at shift `γ`. -/
def IsRatShiftInvert {N : ℕ} (H : Matrix (Fin N) (Fin N) ℚ) (γ : ℚ)
    (R : Matrix (Fin N) (Fin N) ℚ) : Prop :=
  (H + γ • 1) * R = 1 ∧ R * (H + γ • 1) = 1

/-- **Ultrafinitist Hashimoto shift bound:** if `⟨v, H v⟩ ≥ e ‖v‖²` and `e + γ ≥ 0`, then
`‖(H + γ I) v‖² ≥ (e + γ)² ‖v‖²` over `ℚ`. -/
theorem uHashimoto_shift_bound {N : ℕ} {H : Matrix (Fin N) (Fin N) ℚ} {e γ : ℚ}
    (hbot : IsLowerBounded H e) (hpos : 0 ≤ e + γ) (v : Fin N → ℚ) :
    (e + γ) ^ 2 * vecSqNorm v ≤ vecSqNorm ((H + γ • 1).mulVec v) := by
  have h1 : (e + γ) * vecSqNorm v ≤ vecDot v ((H + γ • 1).mulVec v) := by
    have hadd : (H + γ • 1).mulVec v = H.mulVec v + γ • v := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hadd, vecDot_add_right, vecDot_smul_right, vecDot_self, ← ratQuad_eq_vecDot]
    linarith [hbot v]
  have hcs := vecDot_sq_le v ((H + γ • 1).mulVec v)
  have hnn : 0 ≤ vecSqNorm v := vecSqNorm_nonneg v
  rcases eq_or_lt_of_le hnn with hv0 | hvpos
  · rw [← hv0, mul_zero]
    exact vecSqNorm_nonneg _
  · have h2 : ((e + γ) * vecSqNorm v) ^ 2 ≤ vecDot v ((H + γ • 1).mulVec v) ^ 2 := by
      have h0 : 0 ≤ (e + γ) * vecSqNorm v := mul_nonneg hpos hnn
      nlinarith
    have h3 : (e + γ) ^ 2 * vecSqNorm v * vecSqNorm v ≤
        vecSqNorm v * vecSqNorm ((H + γ • 1).mulVec v) := by nlinarith
    nlinarith

theorem uShiftInvert_symm {N : ℕ} {H R : Matrix (Fin N) (Fin N) ℚ} {γ : ℚ}
    (hH : Hᵀ = H) (hR : IsRatShiftInvert H γ R) : Rᵀ = R := by
  have hsym : (H + γ • (1 : Matrix (Fin N) (Fin N) ℚ))ᵀ = H + γ • 1 := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hH]
  calc Rᵀ
      = Rᵀ * ((H + γ • 1) * R) := by rw [hR.1, Matrix.mul_one]
    _ = (Rᵀ * (H + γ • 1)ᵀ) * R := by rw [hsym, Matrix.mul_assoc]
    _ = ((H + γ • 1) * R)ᵀ * R := by rw [← Matrix.transpose_mul]
    _ = (1 : Matrix (Fin N) (Fin N) ℚ)ᵀ * R := by rw [hR.1]
    _ = R := by rw [Matrix.transpose_one, Matrix.one_mul]

/-- **Ultrafinitist shift-invert operator bound:** `‖(H + γ I)⁻¹‖ ≤ 1 / (e + γ)` over `ℚ`. -/
theorem uShiftInvert_opBound {N : ℕ} {H R : Matrix (Fin N) (Fin N) ℚ} {e γ : ℚ}
    (hbot : IsLowerBounded H e) (hpos : 0 < e + γ) (hR : IsRatShiftInvert H γ R) :
    OpBound R (1 / (e + γ)) := by
  refine ⟨div_nonneg zero_le_one hpos.le, fun v => ?_⟩
  have hsh := uHashimoto_shift_bound hbot hpos.le (R.mulVec v)
  rw [Matrix.mulVec_mulVec, hR.1, Matrix.one_mulVec] at hsh
  have hsq : 0 < (e + γ) ^ 2 := sq_pos_of_pos hpos
  calc vecSqNorm (R.mulVec v)
      = ((e + γ) ^ 2 * vecSqNorm (R.mulVec v)) / (e + γ) ^ 2 := by
        field_simp [hsq.ne']
    _ ≤ vecSqNorm v / (e + γ) ^ 2 := div_le_div_of_nonneg_right hsh hsq.le
    _ = (1 / (e + γ)) ^ 2 * vecSqNorm v := by
        field_simp [hpos.ne']

theorem uShiftInvert_pos {N : ℕ} {H R : Matrix (Fin N) (Fin N) ℚ} {e γ : ℚ}
    (_hH : Hᵀ = H) (hbot : IsLowerBounded H e) (hpos : 0 ≤ e + γ)
    (hR : IsRatShiftInvert H γ R) : IsRatPSD R := by
  intro v
  rw [ratQuad_eq_vecDot]
  have hv : v = (H + γ • 1).mulVec (R.mulVec v) := by
    rw [Matrix.mulVec_mulVec, hR.1, Matrix.one_mulVec]
  calc vecDot v (R.mulVec v)
      = vecDot ((H + γ • 1).mulVec (R.mulVec v)) (R.mulVec v) := by
        conv_lhs => left; rw [hv]
    _ = vecDot (R.mulVec v) ((H + γ • 1).mulVec (R.mulVec v)) := vecDot_symm _ _
    _ = ratQuad H (R.mulVec v) + γ * vecSqNorm (R.mulVec v) := by
        have hadd : (H + γ • 1).mulVec (R.mulVec v) =
            H.mulVec (R.mulVec v) + γ • (R.mulVec v) := by
          rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [hadd, vecDot_add_right, vecDot_smul_right, vecDot_self, ← ratQuad_eq_vecDot]
    _ ≥ (e + γ) * vecSqNorm (R.mulVec v) := by
        linarith [hbot (R.mulVec v)]
    _ ≥ 0 := mul_nonneg hpos (vecSqNorm_nonneg _)

theorem uShiftInvert_unique {N : ℕ} {H R₁ R₂ : Matrix (Fin N) (Fin N) ℚ} {γ : ℚ}
    (h₁ : IsRatShiftInvert H γ R₁) (h₂ : IsRatShiftInvert H γ R₂) : R₁ = R₂ := by
  calc R₁ = R₁ * ((H + γ • 1) * R₂) := by rw [h₂.1, Matrix.mul_one]
    _ = (R₁ * (H + γ • 1)) * R₂ := by rw [Matrix.mul_assoc]
    _ = R₂ := by rw [h₁.2, Matrix.one_mul]

/-- Exact rational second resolvent identity: `R₁ - R₂ = R₁ * (H₂ - H₁) * R₂`. -/
theorem uShiftInvert_second_resolvent {N : ℕ} {H₁ H₂ R₁ R₂ : Matrix (Fin N) (Fin N) ℚ}
    {γ : ℚ} (h₁ : IsRatShiftInvert H₁ γ R₁) (h₂ : IsRatShiftInvert H₂ γ R₂) :
    R₁ - R₂ = R₁ * (H₂ - H₁) * R₂ := by
  have hsub : (H₂ + γ • (1 : Matrix (Fin N) (Fin N) ℚ)) - (H₁ + γ • 1) = H₂ - H₁ := by
    ext i j; simp
  calc R₁ - R₂
      = R₁ * ((H₂ + γ • 1) * R₂) - (R₁ * (H₁ + γ • 1)) * R₂ := by
        rw [h₂.1, h₁.2, Matrix.mul_one, Matrix.one_mul]
    _ = R₁ * ((H₂ + γ • 1) - (H₁ + γ • 1)) * R₂ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = R₁ * (H₂ - H₁) * R₂ := by rw [hsub]

/-- Operator-norm perturbation of the shift-invert resolvent:
`‖(H₁ + γ)⁻¹ - (H₂ + γ)⁻¹‖ ≤ ‖H₁ - H₂‖ / (e + γ)²`. -/
theorem uShiftInvert_perturbation_bound {N : ℕ} {H₁ H₂ R₁ R₂ : Matrix (Fin N) (Fin N) ℚ}
    {e γ δ : ℚ} (hb₁ : IsLowerBounded H₁ e) (hb₂ : IsLowerBounded H₂ e)
    (hpos : 0 < e + γ) (h₁ : IsRatShiftInvert H₁ γ R₁) (h₂ : IsRatShiftInvert H₂ γ R₂)
    (hδ : OpBound (H₁ - H₂) δ) :
    OpBound (R₁ - R₂) (δ / (e + γ) ^ 2) := by
  have hR1 := uShiftInvert_opBound hb₁ hpos h₁
  have hR2 := uShiftInvert_opBound hb₂ hpos h₂
  have hdiff : OpBound (H₂ - H₁) δ := by
    have heq : H₂ - H₁ = -(H₁ - H₂) := (neg_sub H₁ H₂).symm
    rw [heq]
    refine ⟨hδ.1, fun v => ?_⟩
    rw [Matrix.neg_mulVec, vecSqNorm_neg]
    exact hδ.2 v
  have hmul := opBound_mul (opBound_mul hR1 hdiff) hR2
  rw [← uShiftInvert_second_resolvent h₁ h₂] at hmul
  have hrate : 1 / (e + γ) * δ * (1 / (e + γ)) = δ / (e + γ) ^ 2 := by
    field_simp [hpos.ne']
  rwa [hrate] at hmul

/-- **Hashimoto Shift-Transfer Identity:** if `X = (H + γ I)⁻¹` and `Ψ = (I - τ X)⁻¹`,
then `Ψ * X = (H + (γ - τ) I)⁻¹` identically over `ℚ`. -/
theorem hashimoto_shift_transfer_identity {N : ℕ} {H X Ψ : Matrix (Fin N) (Fin N) ℚ}
    {γ τ : ℚ} (hX : IsRatShiftInvert H γ X)
    (hΨ1 : (1 - τ • X) * Ψ = 1) (hΨ2 : Ψ * (1 - τ • X) = 1) :
    IsRatShiftInvert H (γ - τ) (Ψ * X) := by
  have hsplit : H + (γ - τ) • (1 : Matrix (Fin N) (Fin N) ℚ) =
      (H + γ • 1) - τ • 1 := by
    ext i j
    simp [sub_eq_add_neg, add_assoc]
    ring
  have hfacL : (H + (γ - τ) • (1 : Matrix (Fin N) (Fin N) ℚ)) * X = 1 - τ • X := by
    rw [hsplit, Matrix.sub_mul, hX.1, Matrix.smul_mul, Matrix.one_mul]
  have hfacR : X * (H + (γ - τ) • (1 : Matrix (Fin N) (Fin N) ℚ)) = 1 - τ • X := by
    rw [hsplit, Matrix.mul_sub, hX.2, Matrix.mul_smul, Matrix.mul_one]
  have hcomm : Ψ * X = X * Ψ := by
    calc Ψ * X = Ψ * (X * ((1 - τ • X) * Ψ)) := by rw [hΨ1, Matrix.mul_one]
      _ = Ψ * ((X * (1 - τ • X)) * Ψ) := by rw [Matrix.mul_assoc]
      _ = Ψ * (((1 - τ • X) * X) * Ψ) := by
          have hXcomm : X * (1 - τ • X) = (1 - τ • X) * X := by
            rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
              Matrix.mul_smul, Matrix.smul_mul]
          rw [hXcomm]
      _ = (Ψ * (1 - τ • X)) * (X * Ψ) := by simp only [Matrix.mul_assoc]
      _ = X * Ψ := by rw [hΨ2, Matrix.one_mul]
  constructor
  · calc (H + (γ - τ) • 1) * (Ψ * X)
        = (H + (γ - τ) • 1) * (X * Ψ) := by rw [hcomm]
      _ = ((H + (γ - τ) • 1) * X) * Ψ := by rw [Matrix.mul_assoc]
      _ = (1 - τ • X) * Ψ := by rw [hfacL]
      _ = 1 := hΨ1
  · calc (Ψ * X) * (H + (γ - τ) • 1)
        = Ψ * (X * (H + (γ - τ) • 1)) := by rw [Matrix.mul_assoc]
      _ = Ψ * (1 - τ • X) := by rw [hfacR]
      _ = 1 := hΨ2

/-! ## 3. Exact finite-order Krylov compression and polynomial transfer -/

/-- Exact rational SIRK compression `B = Vᵀ X V`. -/
def uCompress {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ) (X : Matrix (Fin N) (Fin N) ℚ) :
    Matrix (Fin m) (Fin m) ℚ :=
  Vᵀ * X * V

/-- Rational SIRK subspace reconstruction `V B Vᵀ`. -/
def uSirkApprox {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ) (psiB : Matrix (Fin m) (Fin m) ℚ) :
    Matrix (Fin N) (Fin N) ℚ :=
  V * psiB * Vᵀ

/-- Exact order-`k` Krylov subspace membership for seed `v` and operator `X`. -/
def InKrylovRange {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ) (X : Matrix (Fin N) (Fin N) ℚ)
    (k : ℕ) (v : Fin N → ℚ) : Prop :=
  ∀ j < k, (V * Vᵀ).mulVec ((X ^ j).mulVec v) = (X ^ j).mulVec v

/-- **Unconditional finite-order power transfer:** if `Vᵀ V = 1` and `Xʲ v ∈ range V` for
all `j < k`, then `Xʲ v = V (Vᵀ X V)ʲ (Vᵀ v)` for all `j < k`. -/
theorem uKrylov_pow_transfer {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ)
    (X : Matrix (Fin N) (Fin N) ℚ) (k : ℕ) (v : Fin N → ℚ)
    (_hV : Vᵀ * V = 1) (hK : InKrylovRange V X k v) :
    ∀ j < k, (X ^ j).mulVec v = V.mulVec (((uCompress V X) ^ j).mulVec (Vᵀ.mulVec v)) := by
  intro j hj
  induction j with
  | zero =>
    simpa [uCompress] using (hK 0 hj).symm
  | succ j ih =>
    have hj_lt : j < k := Nat.lt_of_succ_lt hj
    have ihj := ih hj_lt
    have hproj : (V * Vᵀ).mulVec ((X ^ (j + 1)).mulVec v) = (X ^ (j + 1)).mulVec v :=
      hK (j + 1) hj
    have hstep1 : (X ^ (j + 1)).mulVec v = X.mulVec ((X ^ j).mulVec v) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec]
    have hstep2 : (uCompress V X ^ (j + 1)).mulVec (Vᵀ.mulVec v) =
        (uCompress V X).mulVec ((uCompress V X ^ j).mulVec (Vᵀ.mulVec v)) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [← hproj, hstep1, ihj, hstep2]
    simp only [uCompress, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc]

/-- **Unconditional polynomial Krylov transfer:** for any coefficients `c : ℕ → ℚ` and
Krylov order `k`, `(∑_{j<k} c_j Xʲ) v = V (∑_{j<k} c_j Bʲ) Vᵀ v`. -/
theorem uKrylov_poly_transfer {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ)
    (X : Matrix (Fin N) (Fin N) ℚ) (k : ℕ) (v : Fin N → ℚ) (c : ℕ → ℚ)
    (hV : Vᵀ * V = 1) (hK : InKrylovRange V X k v) :
    (∑ j ∈ Finset.range k, c j • X ^ j).mulVec v =
      (uSirkApprox V (∑ j ∈ Finset.range k, c j • (uCompress V X) ^ j)).mulVec v := by
  have hsmul_mulVec : ∀ {n : ℕ} (a : ℚ) (A : Matrix (Fin n) (Fin n) ℚ) (w : Fin n → ℚ),
      (a • A).mulVec w = a • A.mulVec w := by
    intro n a A w
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hsum_mulVec : ∀ {n : ℕ} (s : Finset ℕ) (f : ℕ → Matrix (Fin n) (Fin n) ℚ)
      (w : Fin n → ℚ),
      (∑ j ∈ s, f j).mulVec w = ∑ j ∈ s, (f j).mulVec w := by
    intro n s f w
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Matrix.add_mulVec, ih, Finset.sum_insert ha]
  rw [hsum_mulVec]
  unfold uSirkApprox
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsum_mulVec, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj_lt : j < k := Finset.mem_range.mp hj
  rw [hsmul_mulVec, hsmul_mulVec, Matrix.mulVec_smul, uKrylov_pow_transfer V X k v hV hK j hj_lt]

/-- Block compatibility for nested Krylov embeddings (`ChapterH8`). -/
theorem uKrylov_block_compat {N n m : ℕ} (V₁ : Matrix (Fin N) (Fin n) ℚ)
    (V₂ : Matrix (Fin N) (Fin m) ℚ) (J : Matrix (Fin m) (Fin n) ℚ)
    (X : Matrix (Fin N) (Fin N) ℚ) (hJ : V₁ = V₂ * J) :
    uCompress V₁ X = Jᵀ * uCompress V₂ X * J := by
  subst hJ
  unfold uCompress
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-! ## 4. Computable U-SIRK (`neumannPoly`) and unconditional geometric convergence -/

/-- Exact computable finite-degree Neumann–SIRK polynomial `∑_{j<m} (τ X)ʲ`. -/
def neumannPoly {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (τ : ℚ) (m : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  ∑ j ∈ Finset.range m, (τ • X) ^ j

theorem one_sub_mul_neumannPoly {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (τ : ℚ) (m : ℕ) :
    (1 - τ • X) * neumannPoly X τ m = 1 - (τ • X) ^ m := by
  induction m with
  | zero => simp [neumannPoly]
  | succ m ih =>
    unfold neumannPoly at ih ⊢
    rw [Finset.sum_range_succ, Matrix.mul_add, ih, pow_succ', Matrix.sub_mul, Matrix.one_mul]
    abel

/-- Exact algebraic remainder identity `(I - τ X)⁻¹ - ∑_{j<m} (τ X)ʲ = (I - τ X)⁻¹ (τ X)ᵐ`. -/
theorem neumann_remainder_identity {n : ℕ} {X Ψ : Matrix (Fin n) (Fin n) ℚ}
    {τ : ℚ} (hΨ : Ψ * (1 - τ • X) = 1) (m : ℕ) :
    Ψ - neumannPoly X τ m = Ψ * (τ • X) ^ m := by
  calc Ψ - neumannPoly X τ m
      = Ψ * 1 - (Ψ * (1 - τ • X)) * neumannPoly X τ m := by
        rw [hΨ, Matrix.mul_one, Matrix.one_mul]
    _ = Ψ * 1 - Ψ * ((1 - τ • X) * neumannPoly X τ m) := by
        rw [Matrix.mul_assoc]
    _ = Ψ * (1 - (1 - τ • X) * neumannPoly X τ m) := by
        rw [← Matrix.mul_sub]
    _ = Ψ * (τ • X) ^ m := by
        rw [one_sub_mul_neumannPoly]
        have h : (1 : Matrix (Fin n) (Fin n) ℚ) - (1 - (τ • X) ^ m) = (τ • X) ^ m := by abel
        rw [h]

/-- Pure-`ℚ` Neumann resolvent bound: if `OpBound X r`, `0 ≤ τ`, `τ * r < 1`, and
`(1 - τ X) Ψ = 1`, then `OpBound Ψ (1 / (1 - τ * r))`. -/
theorem inv_one_sub_opBound {n : ℕ} {X Ψ : Matrix (Fin n) (Fin n) ℚ} {r τ : ℚ}
    (hX : OpBound X r) (hτ : 0 ≤ τ) (hq : τ * r < 1) (hΨ : (1 - τ • X) * Ψ = 1) :
    OpBound Ψ (1 / (1 - τ * r)) := by
  have h1q : 0 < 1 - τ * r := sub_pos.mpr hq
  refine ⟨div_nonneg zero_le_one h1q.le, fun w => ?_⟩
  let q : ℚ := τ * r
  have hq0 : 0 ≤ q := mul_nonneg hτ hX.1
  let u := Ψ.mulVec w
  let y := (τ • X).mulVec u
  have hwu : w = u - y := by
    have hw : w = (1 - τ • X).mulVec u := by
      change w = (1 - τ • X).mulVec (Ψ.mulVec w)
      rw [Matrix.mulVec_mulVec, hΨ, Matrix.one_mulVec]
    have hsub : (1 - τ • X).mulVec u = u - y := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact hw.trans hsub
  have hy_bound : vecSqNorm y ≤ q ^ 2 * vecSqNorm u := (opBound_smul hX hτ).2 u
  have hcs := vecDot_sq_le u y
  have ha : 0 ≤ vecSqNorm u := vecSqNorm_nonneg u
  have hb : 0 ≤ vecSqNorm y := vecSqNorm_nonneg y
  have h2q : 0 ≤ 2 * q - q ^ 2 := by nlinarith
  have h2mq : 0 ≤ (2 - q) ^ 2 * vecSqNorm u - vecSqNorm y := by
    have hq2 : q ^ 2 ≤ (2 - q) ^ 2 := by nlinarith
    have hle : q ^ 2 * vecSqNorm u ≤ (2 - q) ^ 2 * vecSqNorm u :=
      mul_le_mul_of_nonneg_right hq2 ha
    linarith
  have hpoly : ((2 * q - q ^ 2) * vecSqNorm u + vecSqNorm y) ^ 2 -
      4 * vecSqNorm u * vecSqNorm y =
      (q ^ 2 * vecSqNorm u - vecSqNorm y) *
        ((2 - q) ^ 2 * vecSqNorm u - vecSqNorm y) := by ring
  have hprod : 0 ≤ (q ^ 2 * vecSqNorm u - vecSqNorm y) *
      ((2 - q) ^ 2 * vecSqNorm u - vecSqNorm y) :=
    mul_nonneg (sub_nonneg.mpr hy_bound) h2mq
  have hsq_dot : (2 * vecDot u y) ^ 2 ≤
      ((2 * q - q ^ 2) * vecSqNorm u + vecSqNorm y) ^ 2 := by
    linarith
  have hdot_le : 2 * vecDot u y ≤ (2 * q - q ^ 2) * vecSqNorm u + vecSqNorm y := by
    have hsum_nn : 0 ≤ (2 * q - q ^ 2) * vecSqNorm u + vecSqNorm y :=
      add_nonneg (mul_nonneg h2q ha) hb
    nlinarith
  have hlow : (1 - q) ^ 2 * vecSqNorm u ≤ vecSqNorm w := by
    rw [hwu, vecSqNorm_sub_eq u y]
    nlinarith
  have h1q_sq : 0 < (1 - q) ^ 2 := sq_pos_of_pos h1q
  calc vecSqNorm (Ψ.mulVec w)
      = ((1 - q) ^ 2 * vecSqNorm u) / (1 - q) ^ 2 :=
        (mul_div_cancel_left₀ (vecSqNorm u) h1q_sq.ne').symm
    _ ≤ vecSqNorm w / (1 - q) ^ 2 := div_le_div_of_nonneg_right hlow h1q_sq.le
    _ = (1 / (1 - τ * r)) ^ 2 * vecSqNorm w := by
        dsimp [q]
        field_simp [h1q.ne']

/-- Operator-norm bound on the computable U-SIRK remainder:
`‖(I - τ X)⁻¹ - ∑_{j<m} (τ X)ʲ‖ ≤ (τ r)ᵐ / (1 - τ r)`. -/
theorem neumann_remainder_opBound {n : ℕ} {X Ψ : Matrix (Fin n) (Fin n) ℚ} {r τ : ℚ}
    (hX : OpBound X r) (hτ : 0 ≤ τ) (hq : τ * r < 1)
    (hΨ1 : (1 - τ • X) * Ψ = 1) (hΨ2 : Ψ * (1 - τ • X) = 1) (m : ℕ) :
    OpBound (Ψ - neumannPoly X τ m) ((τ * r) ^ m / (1 - τ * r)) := by
  have hinv := inv_one_sub_opBound hX hτ hq hΨ1
  have hpow := opBound_pow (opBound_smul hX hτ) m
  have hmul := opBound_mul hinv hpow
  rw [← neumann_remainder_identity hΨ2 m] at hmul
  have hrate : 1 / (1 - τ * r) * (τ * r) ^ m = (τ * r) ^ m / (1 - τ * r) := by ring
  rwa [hrate] at hmul

private theorem uSirk_poly_transfer_neumann {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ)
    (X : Matrix (Fin N) (Fin N) ℚ) (τ : ℚ) (k : ℕ) (v : Fin N → ℚ)
    (hV : Vᵀ * V = 1) (hK : InKrylovRange V X k v) :
    (neumannPoly X τ k).mulVec v =
      (uSirkApprox V (neumannPoly (uCompress V X) τ k)).mulVec v := by
  have hrew : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ),
      neumannPoly A τ k = ∑ j ∈ Finset.range k, τ ^ j • A ^ j := by
    intro n A
    unfold neumannPoly
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_pow]
  rw [hrew X, hrew (uCompress V X)]
  exact uKrylov_poly_transfer V X k v (fun j => τ ^ j) hV hK

/-- **Unconditional U-SIRK Convergence Theorem (Crouzeix-free):**
for any rational isometry `Vᵀ V = 1` containing the Krylov subspace `K_k(X, v)`,
`‖(I - τ X)⁻¹ v - V (I - τ B)⁻¹ Vᵀ v‖ ≤ (2 (τ r)ᵏ / (1 - τ r)) ‖v‖`. -/
theorem uSirk_error_bound {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ)
    (X ΨX : Matrix (Fin N) (Fin N) ℚ) (ΨB : Matrix (Fin m) (Fin m) ℚ)
    {r τ : ℚ} (k : ℕ) (v : Fin N → ℚ)
    (hV : Vᵀ * V = 1) (hX : OpBound X r) (hτ : 0 ≤ τ) (hq : τ * r < 1)
    (hΨX1 : (1 - τ • X) * ΨX = 1) (hΨX2 : ΨX * (1 - τ • X) = 1)
    (hΨB1 : (1 - τ • uCompress V X) * ΨB = 1) (hΨB2 : ΨB * (1 - τ • uCompress V X) = 1)
    (hK : InKrylovRange V X k v) :
    vecSqNorm (ΨX.mulVec v - (uSirkApprox V ΨB).mulVec v) ≤
      (2 * (τ * r) ^ k / (1 - τ * r)) ^ 2 * vecSqNorm v := by
  let B := uCompress V X
  let pX := neumannPoly X τ k
  let pB := neumannPoly B τ k
  have htransfer : pX.mulVec v = (uSirkApprox V pB).mulVec v :=
    uSirk_poly_transfer_neumann V X τ k v hV hK
  have hsplit : ΨX.mulVec v - (uSirkApprox V ΨB).mulVec v =
      (ΨX - pX).mulVec v + V.mulVec ((pB - ΨB).mulVec (Vᵀ.mulVec v)) := by
    have hVapprox : (uSirkApprox V ΨB).mulVec v = V.mulVec (ΨB.mulVec (Vᵀ.mulVec v)) := by
      unfold uSirkApprox
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hpBapprox : (uSirkApprox V pB).mulVec v = V.mulVec (pB.mulVec (Vᵀ.mulVec v)) := by
      unfold uSirkApprox
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.sub_mulVec, hVapprox, Matrix.sub_mulVec, htransfer, hpBapprox, Matrix.mulVec_sub]
    abel
  have hremX := neumann_remainder_opBound hX hτ hq hΨX1 hΨX2 k
  have hremB := neumann_remainder_opBound (opBound_compress hV hX) hτ hq hΨB1 hΨB2 k
  let e : ℚ := (τ * r) ^ k / (1 - τ * r)
  have he : 0 ≤ e := hremX.1
  have h1 : vecSqNorm ((ΨX - pX).mulVec v) ≤ e ^ 2 * vecSqNorm v := hremX.2 v
  have h2 : vecSqNorm (V.mulVec ((pB - ΨB).mulVec (Vᵀ.mulVec v))) ≤ e ^ 2 * vecSqNorm v := by
    rw [isometry_preserves_sqNorm hV]
    have hneg : (pB - ΨB).mulVec (Vᵀ.mulVec v) = -((ΨB - pB).mulVec (Vᵀ.mulVec v)) := by
      have heq : pB - ΨB = -(ΨB - pB) := (neg_sub ΨB pB).symm
      rw [heq, Matrix.neg_mulVec]
    rw [hneg, vecSqNorm_neg]
    have hB := hremB.2 (Vᵀ.mulVec v)
    have hVt := isometry_adjoint_contraction hV v
    have hle : e ^ 2 * vecSqNorm (Vᵀ.mulVec v) ≤ e ^ 2 * vecSqNorm v :=
      mul_le_mul_of_nonneg_left hVt (sq_nonneg e)
    exact hB.trans hle
  rw [hsplit]
  have hcomb := vecSqNorm_add_mul_le he he (vecSqNorm_nonneg v) h1 h2
  have hrate : e + e = 2 * (τ * r) ^ k / (1 - τ * r) := by
    dsimp [e]; ring
  rwa [hrate] at hcomb

/-- **Rank-truncated / leaky-seed U-SIRK convergence (`ChapterSirkTruncation`):**
if the Krylov invariance holds on the projected seed `P v = V Vᵀ v` rather than `v`,
then the discarded tail `δ ≥ ‖v - V Vᵀ v‖` enters additively as `(1 - τ r)⁻¹ δ`. -/
theorem uSirk_error_bound_leaky {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ)
    (X ΨX : Matrix (Fin N) (Fin N) ℚ) (ΨB : Matrix (Fin m) (Fin m) ℚ)
    {r τ a δ : ℚ} (k : ℕ) (v : Fin N → ℚ)
    (hV : Vᵀ * V = 1) (hX : OpBound X r) (hτ : 0 ≤ τ) (hq : τ * r < 1)
    (hΨX1 : (1 - τ • X) * ΨX = 1) (hΨX2 : ΨX * (1 - τ • X) = 1)
    (hΨB1 : (1 - τ • uCompress V X) * ΨB = 1) (hΨB2 : ΨB * (1 - τ • uCompress V X) = 1)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hv : vecSqNorm v ≤ a ^ 2)
    (hleak : vecSqNorm (v - (V * Vᵀ).mulVec v) ≤ δ ^ 2)
    (hK : InKrylovRange V X k ((V * Vᵀ).mulVec v)) :
    vecSqNorm (ΨX.mulVec v - (uSirkApprox V ΨB).mulVec v) ≤
      (2 * (τ * r) ^ k / (1 - τ * r) * a + 1 / (1 - τ * r) * δ) ^ 2 := by
  let p := (V * Vᵀ).mulVec v
  have hp_approx : (uSirkApprox V ΨB).mulVec p = (uSirkApprox V ΨB).mulVec v := by
    unfold uSirkApprox
    change (V * ΨB * Vᵀ).mulVec ((V * Vᵀ).mulVec v) = (V * ΨB * Vᵀ).mulVec v
    rw [Matrix.mulVec_mulVec]
    have hmat : (V * ΨB * Vᵀ) * (V * Vᵀ) = V * ΨB * Vᵀ := by
      calc (V * ΨB * Vᵀ) * (V * Vᵀ)
          = V * (ΨB * ((Vᵀ * V) * Vᵀ)) := by simp only [Matrix.mul_assoc]
        _ = V * (ΨB * ((1 : Matrix (Fin m) (Fin m) ℚ) * Vᵀ)) := by rw [hV]
        _ = V * ΨB * Vᵀ := by rw [Matrix.one_mul]; simp only [Matrix.mul_assoc]
    rw [hmat]
  have hsplit : ΨX.mulVec v - (uSirkApprox V ΨB).mulVec v =
      (ΨX.mulVec p - (uSirkApprox V ΨB).mulVec p) + ΨX.mulVec (v - p) := by
    rw [hp_approx, Matrix.mulVec_sub]
    abel
  have hp_norm : vecSqNorm p ≤ a ^ 2 := by
    have hp_eq : vecSqNorm p = vecSqNorm (Vᵀ.mulVec v) := by
      dsimp [p]
      rw [← Matrix.mulVec_mulVec, isometry_preserves_sqNorm hV]
    have hle : vecSqNorm p ≤ vecSqNorm v := by
      rw [hp_eq]
      exact isometry_adjoint_contraction hV v
    exact hle.trans hv
  have hkern := uSirk_error_bound V X ΨX ΨB k p hV hX hτ hq hΨX1 hΨX2 hΨB1 hΨB2 hK
  have hc0 : 0 ≤ 2 * (τ * r) ^ k / (1 - τ * r) := by
    have hq0 : 0 ≤ τ * r := mul_nonneg hτ hX.1
    have h1q : 0 < 1 - τ * r := sub_pos.mpr hq
    exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hq0 k)) h1q.le
  have h1 : vecSqNorm (ΨX.mulVec p - (uSirkApprox V ΨB).mulVec p) ≤
      (2 * (τ * r) ^ k / (1 - τ * r) * a) ^ 2 := by
    have hm : (2 * (τ * r) ^ k / (1 - τ * r)) ^ 2 * vecSqNorm p ≤
        (2 * (τ * r) ^ k / (1 - τ * r)) ^ 2 * a ^ 2 :=
      mul_le_mul_of_nonneg_left hp_norm (sq_nonneg _)
    have hsq : (2 * (τ * r) ^ k / (1 - τ * r)) ^ 2 * a ^ 2 =
        (2 * (τ * r) ^ k / (1 - τ * r) * a) ^ 2 := by ring
    exact hkern.trans (hsq ▸ hm)
  have hinv := inv_one_sub_opBound hX hτ hq hΨX1
  have hc1 : 0 ≤ 1 / (1 - τ * r) := hinv.1
  have h2 : vecSqNorm (ΨX.mulVec (v - p)) ≤ (1 / (1 - τ * r) * δ) ^ 2 := by
    have hm := hinv.2 (v - p)
    have hle : (1 / (1 - τ * r)) ^ 2 * vecSqNorm (v - p) ≤
        (1 / (1 - τ * r)) ^ 2 * δ ^ 2 :=
      mul_le_mul_of_nonneg_left hleak (sq_nonneg _)
    have hsq : (1 / (1 - τ * r)) ^ 2 * δ ^ 2 = (1 / (1 - τ * r) * δ) ^ 2 := by ring
    exact hm.trans (hsq ▸ hle)
  rw [hsplit]
  exact vecSqNorm_add_le (mul_nonneg hc0 ha) (mul_nonneg hc1 hδ) h1 h2

/-! ## 5. Horizon-`M`-controlled convergence theorems -/

private theorem rat_bernoulli_ineq {β : ℚ} (h0 : 0 ≤ β) (n : ℕ) :
    1 + (n : ℚ) * β ≤ (1 + β) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ 1 + β := by linarith
    have hmul : (1 + (n : ℚ) * β) * (1 + β) ≤ (1 + β) ^ n * (1 + β) :=
      mul_le_mul_of_nonneg_right ih h1
    have hsq : 0 ≤ (n : ℚ) * β ^ 2 := by positivity
    rw [pow_succ]
    push_cast
    linarith

/-- Pure-`ℚ` quantitative decay `(1 - β)ⁿ ≤ 1 / (1 + n β)` for `0 ≤ β < 1`. -/
theorem rat_one_sub_pow_le_inv {β : ℚ} (h0 : 0 ≤ β) (h1 : β < 1) (n : ℕ) :
    (1 - β) ^ n ≤ 1 / (1 + (n : ℚ) * β) := by
  have hpos : 0 < 1 + (n : ℚ) * β := by positivity
  rw [le_div_iff₀ hpos]
  have hprod : (1 - β) * (1 + β) ≤ 1 := by nlinarith
  have hpow : ((1 - β) * (1 + β)) ^ n ≤ 1 :=
    pow_le_one₀ (mul_nonneg (sub_nonneg.mpr h1.le) (by linarith)) hprod
  rw [mul_pow] at hpow
  have hbern := rat_bernoulli_ineq h0 n
  have hmul : (1 - β) ^ n * (1 + (n : ℚ) * β) ≤ (1 - β) ^ n * (1 + β) ^ n :=
    mul_le_mul_of_nonneg_left hbern (pow_nonneg (sub_nonneg.mpr h1.le) n)
  exact hmul.trans hpow

private theorem real_one_sub_mul_le_pow {β : ℝ} (_h0 : 0 ≤ β) (h1 : β ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * β ≤ (1 - β) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1b : 0 ≤ 1 - β := sub_nonneg.mpr h1
    have hmul : (1 - (n : ℝ) * β) * (1 - β) ≤ (1 - β) ^ n * (1 - β) :=
      mul_le_mul_of_nonneg_right ih h1b
    have hsq : 0 ≤ (n : ℝ) * β ^ 2 := by positivity
    rw [pow_succ]
    push_cast
    linarith

private theorem add_three_le_pow_two (k : ℕ) (hk : 3 ≤ k) : k + 3 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hklt | hkge
    · have hk2 : k = 2 := by omega
      subst hk2
      norm_num
    · have ihk := ih hkge
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      omega

/-- Logarithmic Krylov order `m = ⌊log₂ M⌋ + 3` satisfies `4 M ≤ 2ᵐ` and `m ≤ M` for `8 ≤ M`. -/
theorem log_krylov_order_bound (M : ℕ) (hM : 8 ≤ M) :
    4 * M ≤ 2 ^ (Nat.log 2 M + 3) ∧ Nat.log 2 M + 3 ≤ M := by
  constructor
  · have hlt : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
    have hpow : 4 * 2 ^ (Nat.log 2 M + 1) = 2 ^ (Nat.log 2 M + 3) := by
      have : Nat.log 2 M + 3 = (Nat.log 2 M + 1) + 2 := by omega
      rw [this, pow_add]
      ring
    omega
  · have hlog8 : 3 ≤ Nat.log 2 M := by
      have h3 : Nat.log 2 8 = 3 := by norm_num
      have hmono := Nat.log_mono_right (b := 2) hM
      omega
    have hpow_le : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 (by omega)
    exact (add_three_le_pow_two (Nat.log 2 M) hlog8).trans hpow_le

/-- **Horizon-`M` convergence at order `m = M`:** when `τ r = 1 - β` (`0 < β < 1`),
at horizon order `M` the U-SIRK error obeys
`‖(I - τ X)⁻¹ v - V (I - τ B)⁻¹ Vᵀ v‖ ≤ (2 / (β (1 + M β))) ‖v‖`. -/
theorem uSirk_converges_at_horizon {N m : ℕ} (M : ℕ)
    (V : Matrix (Fin N) (Fin m) ℚ)
    (X ΨX : Matrix (Fin N) (Fin N) ℚ) (ΨB : Matrix (Fin m) (Fin m) ℚ)
    {r τ β : ℚ} (v : Fin N → ℚ)
    (hV : Vᵀ * V = 1) (hX : OpBound X r) (hτ : 0 ≤ τ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hq_eq : τ * r ≤ 1 - β)
    (hΨX1 : (1 - τ • X) * ΨX = 1) (hΨX2 : ΨX * (1 - τ • X) = 1)
    (hΨB1 : (1 - τ • uCompress V X) * ΨB = 1) (hΨB2 : ΨB * (1 - τ • uCompress V X) = 1)
    (hK : InKrylovRange V X M v) :
    vecSqNorm (ΨX.mulVec v - (uSirkApprox V ΨB).mulVec v) ≤
      (2 / (β * (1 + (M : ℚ) * β))) ^ 2 * vecSqNorm v := by
  have hq : τ * r < 1 := by linarith
  have hbase := uSirk_error_bound V X ΨX ΨB M v hV hX hτ hq hΨX1 hΨX2 hΨB1 hΨB2 hK
  have hq0 : 0 ≤ τ * r := mul_nonneg hτ hX.1
  have hpow : (τ * r) ^ M ≤ (1 - β) ^ M := pow_le_pow_left₀ hq0 hq_eq M
  have hbern := rat_one_sub_pow_le_inv hβ0.le hβ1 M
  have hden : β ≤ 1 - τ * r := by linarith
  have hratio : 2 * (τ * r) ^ M / (1 - τ * r) ≤ 2 / (β * (1 + (M : ℚ) * β)) := by
    have hnum : 2 * (τ * r) ^ M ≤ 2 * (1 / (1 + (M : ℚ) * β)) := by linarith
    have h1q : 0 < 1 - τ * r := by linarith
    calc 2 * (τ * r) ^ M / (1 - τ * r)
        ≤ (2 * (1 / (1 + (M : ℚ) * β))) / (1 - τ * r) :=
          div_le_div_of_nonneg_right hnum h1q.le
      _ ≤ (2 * (1 / (1 + (M : ℚ) * β))) / β := by
          apply div_le_div_of_nonneg_left _ hβ0 hden
          positivity
      _ = 2 / (β * (1 + (M : ℚ) * β)) := by
          field_simp [hβ0.ne']
  have hratio0 : 0 ≤ 2 * (τ * r) ^ M / (1 - τ * r) := by
    have h1q : 0 < 1 - τ * r := by linarith
    exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hq0 M)) h1q.le
  have hsq : (2 * (τ * r) ^ M / (1 - τ * r)) ^ 2 ≤ (2 / (β * (1 + (M : ℚ) * β))) ^ 2 := by
    nlinarith
  have hm : (2 * (τ * r) ^ M / (1 - τ * r)) ^ 2 * vecSqNorm v ≤
      (2 / (β * (1 + (M : ℚ) * β))) ^ 2 * vecSqNorm v :=
    mul_le_mul_of_nonneg_right hsq (vecSqNorm_nonneg v)
  exact hbase.trans hm

/-- **Horizon-`M` tolerance theorem (`1 / M`):** when `τ r ≤ 1 / 2` and `4 M ≤ 2ᵐ`,
U-SIRK achieves exact error tolerance `1 / M` (`‖err‖² ≤ (1 / M)² ‖v‖²`). -/
theorem uSirk_converges_to_M_tol {N dim : ℕ} (M m : ℕ) (hM : 0 < M)
    (V : Matrix (Fin N) (Fin dim) ℚ)
    (X ΨX : Matrix (Fin N) (Fin N) ℚ) (ΨB : Matrix (Fin dim) (Fin dim) ℚ)
    {r τ : ℚ} (v : Fin N → ℚ)
    (hV : Vᵀ * V = 1) (hX : OpBound X r) (hτ : 0 ≤ τ)
    (hq_half : τ * r ≤ 1 / 2) (hm : 4 * M ≤ 2 ^ m)
    (hΨX1 : (1 - τ • X) * ΨX = 1) (hΨX2 : ΨX * (1 - τ • X) = 1)
    (hΨB1 : (1 - τ • uCompress V X) * ΨB = 1) (hΨB2 : ΨB * (1 - τ • uCompress V X) = 1)
    (hK : InKrylovRange V X m v) :
    vecSqNorm (ΨX.mulVec v - (uSirkApprox V ΨB).mulVec v) ≤
      (1 / (M : ℚ)) ^ 2 * vecSqNorm v := by
  have hq : τ * r < 1 := by linarith
  have hbase := uSirk_error_bound V X ΨX ΨB m v hV hX hτ hq hΨX1 hΨX2 hΨB1 hΨB2 hK
  have hq0 : 0 ≤ τ * r := mul_nonneg hτ hX.1
  have hpow : (τ * r) ^ m ≤ (1 / 2 : ℚ) ^ m := pow_le_pow_left₀ hq0 hq_half m
  have hmQ : (4 : ℚ) * (M : ℚ) ≤ (2 : ℚ) ^ m := by exact_mod_cast hm
  have hMpos : (0 : ℚ) < (M : ℚ) := Nat.cast_pos.mpr hM
  have hpow_inv : (1 / 2 : ℚ) ^ m ≤ 1 / (4 * (M : ℚ)) := by
    rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
    exact hmQ
  have hden : (1 / 2 : ℚ) ≤ 1 - τ * r := by linarith
  have hrate : 2 * (τ * r) ^ m / (1 - τ * r) ≤ 1 / (M : ℚ) := by
    have hnum : 2 * (τ * r) ^ m ≤ 2 * (1 / (4 * (M : ℚ))) := by linarith
    have h1q : 0 < 1 - τ * r := by linarith
    calc 2 * (τ * r) ^ m / (1 - τ * r)
        ≤ (2 * (1 / (4 * (M : ℚ)))) / (1 - τ * r) :=
          div_le_div_of_nonneg_right hnum h1q.le
      _ ≤ (2 * (1 / (4 * (M : ℚ)))) / (1 / 2 : ℚ) := by
          apply div_le_div_of_nonneg_left _ (by norm_num) hden
          positivity
      _ = 1 / (M : ℚ) := by
          field_simp [hMpos.ne']
          norm_num
  have hrate0 : 0 ≤ 2 * (τ * r) ^ m / (1 - τ * r) := by
    have h1q : 0 < 1 - τ * r := by linarith
    exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hq0 m)) h1q.le
  have hsq : (2 * (τ * r) ^ m / (1 - τ * r)) ^ 2 ≤ (1 / (M : ℚ)) ^ 2 := by nlinarith
  have hmul : (2 * (τ * r) ^ m / (1 - τ * r)) ^ 2 * vecSqNorm v ≤
      (1 / (M : ℚ)) ^ 2 * vecSqNorm v :=
    mul_le_mul_of_nonneg_right hsq (vecSqNorm_nonneg v)
  exact hbase.trans hmul

/-- **Logarithmic-step convergence to `1 / M` tolerance:** for any horizon `8 ≤ M` and
`τ r ≤ 1 / 2`, only `m = ⌊log₂ M⌋ + 3 ≤ M` Krylov steps suffice to certify error `≤ 1 / M`. -/
theorem uSirk_converges_to_M_tol_log_steps {N dim : ℕ} (M : ℕ) (hM : 8 ≤ M)
    (V : Matrix (Fin N) (Fin dim) ℚ)
    (X ΨX : Matrix (Fin N) (Fin N) ℚ) (ΨB : Matrix (Fin dim) (Fin dim) ℚ)
    {r τ : ℚ} (v : Fin N → ℚ)
    (hV : Vᵀ * V = 1) (hX : OpBound X r) (hτ : 0 ≤ τ) (hq_half : τ * r ≤ 1 / 2)
    (hΨX1 : (1 - τ • X) * ΨX = 1) (hΨX2 : ΨX * (1 - τ • X) = 1)
    (hΨB1 : (1 - τ • uCompress V X) * ΨB = 1) (hΨB2 : ΨB * (1 - τ • uCompress V X) = 1)
    (hK : InKrylovRange V X (Nat.log 2 M + 3) v) :
    Nat.log 2 M + 3 ≤ M ∧
      vecSqNorm (ΨX.mulVec v - (uSirkApprox V ΨB).mulVec v) ≤
        (1 / (M : ℚ)) ^ 2 * vecSqNorm v := by
  have hlog := log_krylov_order_bound M hM
  refine ⟨hlog.2, uSirk_converges_to_M_tol M (Nat.log 2 M + 3) (by omega) V X ΨX ΨB v
    hV hX hτ hq_half hlog.1 hΨX1 hΨX2 hΨB1 hΨB2 hK⟩

/-- **Exact termination at full horizon `M + 1`:** when the orthonormal Krylov basis fills
the entire `(M + 1)`-dimensional Krawtchouk space (`Vᵀ V = 1` and `V Vᵀ = 1`), U-SIRK
reproduces `(I - τ X)⁻¹` with **zero error**. -/
theorem uSirk_exact_at_full_horizon {M : ℕ} (V : Matrix (Fin (M + 1)) (Fin (M + 1)) ℚ)
    (X ΨX ΨB : Matrix (Fin (M + 1)) (Fin (M + 1)) ℚ) (τ : ℚ) (v : Fin (M + 1) → ℚ)
    (_hV : Vᵀ * V = 1) (hVV : V * Vᵀ = 1)
    (hΨX2 : ΨX * (1 - τ • X) = 1) (hΨB1 : (1 - τ • uCompress V X) * ΨB = 1) :
    (uSirkApprox V ΨB).mulVec v = ΨX.mulVec v := by
  have hconj : V * (1 - τ • uCompress V X) = (1 - τ • X) * V := by
    unfold uCompress
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    have hVXV : V * (Vᵀ * X * V) = X * V := by
      calc V * (Vᵀ * X * V) = (V * Vᵀ) * (X * V) := by simp only [Matrix.mul_assoc]
        _ = 1 * (X * V) := by rw [hVV]
        _ = X * V := Matrix.one_mul _
    rw [hVXV]
  have hinvL : (1 - τ • X) * uSirkApprox V ΨB = 1 := by
    unfold uSirkApprox
    calc (1 - τ • X) * (V * ΨB * Vᵀ)
        = ((1 - τ • X) * V) * ΨB * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = (V * (1 - τ • uCompress V X)) * ΨB * Vᵀ := by rw [← hconj]
      _ = V * ((1 - τ • uCompress V X) * ΨB) * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = V * 1 * Vᵀ := by rw [hΨB1]
      _ = 1 := by rw [Matrix.mul_one, hVV]
  have heq : ΨX = uSirkApprox V ΨB := by
    calc ΨX = ΨX * ((1 - τ • X) * uSirkApprox V ΨB) := by rw [hinvL, Matrix.mul_one]
      _ = (ΨX * (1 - τ • X)) * uSirkApprox V ΨB := by rw [Matrix.mul_assoc]
      _ = uSirkApprox V ΨB := by rw [hΨX2, Matrix.one_mul]
  rw [heq]

/-- **U-SIRK restart accumulation (`ChapterSirkRestart`):** if `OpBound U 1`, `OpBound S 1`,
and `OpBound (U - S) ε`, then over `n` restart cycles `OpBound (Uⁿ - Sⁿ) (n ε)`. -/
theorem uSirk_restart_accumulation {N : ℕ} (U S : Matrix (Fin N) (Fin N) ℚ) (ε : ℚ)
    (hU : OpBound U 1) (hS : OpBound S 1) (hstep : OpBound (U - S) ε) (n : ℕ) :
    OpBound (U ^ n - S ^ n) ((n : ℚ) * ε) := by
  induction n with
  | zero =>
    simpa using opBound_zero
  | succ n ih =>
    have hsplit : U ^ (n + 1) - S ^ (n + 1) = U * (U ^ n - S ^ n) + (U - S) * S ^ n := by
      rw [pow_succ', pow_succ']
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel
    have h1 : OpBound (U * (U ^ n - S ^ n)) (1 * ((n : ℚ) * ε)) := opBound_mul hU ih
    have hSn : OpBound (S ^ n) (1 ^ n) := opBound_pow hS n
    have h2 : OpBound ((U - S) * S ^ n) (ε * 1 ^ n) := opBound_mul hstep hSn
    have hcomb := opBound_add h1 h2
    rw [← hsplit] at hcomb
    have hrate : 1 * ((n : ℚ) * ε) + ε * 1 ^ n = ((n + 1 : ℕ) : ℚ) * ε := by
      push_cast; ring
    rwa [hrate] at hcomb

/-- **Combined Horizon-`M` Total Tolerance Theorem:** combines the horizon-`M` Hamiltonian
defect (`OpBound (Href - HM) (Cccr / M)`, mirroring `ChapterDeformedCCR.deformed_ccr_defect_bound`),
the second resolvent perturbation `uShiftInvert_perturbation_bound`, propagator perturbation,
and the Krylov truncation error at order `m`:
`‖Ψ_ref v - V Ψ_B Vᵀ v‖ ≤ τ C_ccr / ((1 - q)² (e + γ)² M) ‖v‖ + 2 qᵐ / (1 - q) ‖v‖`. -/
theorem uSirk_horizon_total_tolerance {N dim : ℕ} (M m : ℕ) (hM : 0 < M)
    (V : Matrix (Fin N) (Fin dim) ℚ)
    (Href HM Rref RM Ψref ΨM : Matrix (Fin N) (Fin N) ℚ)
    (ΨB : Matrix (Fin dim) (Fin dim) ℚ)
    {e γ τ r Cccr : ℚ} (v : Fin N → ℚ)
    (hb_ref : IsLowerBounded Href e) (hb_M : IsLowerBounded HM e) (hpos : 0 < e + γ)
    (hR_ref : IsRatShiftInvert Href γ Rref) (hR_M : IsRatShiftInvert HM γ RM)
    (_hCccr : 0 ≤ Cccr) (hH_diff : OpBound (Href - HM) (Cccr / (M : ℚ)))
    (hRM_bound : OpBound RM r) (hτ : 0 ≤ τ) (hq : τ * r < 1)
    (hΨref1 : (1 - τ • Rref) * Ψref = 1) (hΨref2 : Ψref * (1 - τ • Rref) = 1)
    (hΨM1 : (1 - τ • RM) * ΨM = 1) (hΨM2 : ΨM * (1 - τ • RM) = 1)
    (hRref_bound : OpBound Rref r)
    (hV : Vᵀ * V = 1)
    (hΨB1 : (1 - τ • uCompress V RM) * ΨB = 1) (hΨB2 : ΨB * (1 - τ • uCompress V RM) = 1)
    (hK : InKrylovRange V RM m v) :
    vecSqNorm (Ψref.mulVec v - (uSirkApprox V ΨB).mulVec v) ≤
      (τ * Cccr / ((1 - τ * r) ^ 2 * (e + γ) ^ 2 * (M : ℚ)) +
        2 * (τ * r) ^ m / (1 - τ * r)) ^ 2 * vecSqNorm v := by
  have hR_diff : OpBound (Rref - RM) ((Cccr / (M : ℚ)) / (e + γ) ^ 2) :=
    uShiftInvert_perturbation_bound hb_ref hb_M hpos hR_ref hR_M hH_diff
  have hΨ_diff_eq : Ψref - ΨM = Ψref * (τ • (Rref - RM)) * ΨM := by
    have hsub : (1 - τ • RM) - (1 - τ • Rref) = τ • (Rref - RM) := by
      ext i j; simp; ring
    calc Ψref - ΨM
        = Ψref * ((1 - τ • RM) * ΨM) - (Ψref * (1 - τ • Rref)) * ΨM := by
          rw [hΨM1, hΨref2, Matrix.mul_one, Matrix.one_mul]
      _ = Ψref * ((1 - τ • RM) - (1 - τ • Rref)) * ΨM := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = Ψref * (τ • (Rref - RM)) * ΨM := by rw [hsub]
  have hΨref_b := inv_one_sub_opBound hRref_bound hτ hq hΨref1
  have hΨM_b := inv_one_sub_opBound hRM_bound hτ hq hΨM1
  have hΨ_diff_b : OpBound (Ψref - ΨM)
      (τ * Cccr / ((1 - τ * r) ^ 2 * (e + γ) ^ 2 * (M : ℚ))) := by
    have hmul := opBound_mul (opBound_mul hΨref_b (opBound_smul hR_diff hτ)) hΨM_b
    rw [← hΨ_diff_eq] at hmul
    have hMne : (M : ℚ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
    have h1q : 1 - τ * r ≠ 0 := (sub_pos.mpr hq).ne'
    have hegn : e + γ ≠ 0 := hpos.ne'
    have hrate : 1 / (1 - τ * r) * (τ * (Cccr / (M : ℚ) / (e + γ) ^ 2)) * (1 / (1 - τ * r)) =
        τ * Cccr / ((1 - τ * r) ^ 2 * (e + γ) ^ 2 * (M : ℚ)) := by
      field_simp [hMne, h1q, hegn]
    rwa [hrate] at hmul
  have h1 := hΨ_diff_b.2 v
  have h2 := uSirk_error_bound V RM ΨM ΨB m v hV hRM_bound hτ hq hΨM1 hΨM2 hΨB1 hΨB2 hK
  have hsplit : Ψref.mulVec v - (uSirkApprox V ΨB).mulVec v =
      (Ψref - ΨM).mulVec v + (ΨM.mulVec v - (uSirkApprox V ΨB).mulVec v) := by
    rw [Matrix.sub_mulVec]
    abel
  have hc0 : 0 ≤ τ * Cccr / ((1 - τ * r) ^ 2 * (e + γ) ^ 2 * (M : ℚ)) := hΨ_diff_b.1
  have hc1 : 0 ≤ 2 * (τ * r) ^ m / (1 - τ * r) := by
    have hq0 : 0 ≤ τ * r := mul_nonneg hτ hRM_bound.1
    have h1q : 0 < 1 - τ * r := sub_pos.mpr hq
    exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hq0 m)) h1q.le
  rw [hsplit]
  exact vecSqNorm_add_mul_le hc0 hc1 (vecSqNorm_nonneg v) h1 h2

/-- **Mehler feasibility of the logarithmic U-SIRK convergence order (`ChapterMehlerFeasibility`):**
for `8 ≤ M`, the Krylov order `m = ⌊log₂ M⌋ + 3` achieving `1 / M` accuracy remains strictly
feasible under `mehlerFeasEffect M (1 - 1 / M)`, with truth value `≥ 1 - m / M > 0`. -/
theorem uSirk_order_mehler_feasible (M : ℕ) (hM : 8 ≤ M) :
    let m : ℕ := Nat.log 2 M + 3
    let ρ : ℝ := 1 - 1 / (M : ℝ)
    ∃ (hm : m < M + 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1),
      1 - (m : ℝ) / (M : ℝ) ≤
        (mehlerFeasEffect M ρ h0 h1).truthVal (Pi.single ⟨m, hm⟩ 1) := by
  intro m ρ
  have hm_le : m ≤ M := (log_krylov_order_bound M hM).2
  have hm_lt : m < M + 1 := Nat.lt_succ_of_le hm_le
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hβ0 : 0 ≤ 1 / (M : ℝ) := by positivity
  have hβ1 : 1 / (M : ℝ) ≤ 1 := div_le_one_of_le₀ hM1 hMpos.le
  have h0 : 0 ≤ ρ := sub_nonneg.mpr hβ1
  have h1 : ρ ≤ 1 := by dsimp [ρ]; linarith
  refine ⟨hm_lt, h0, h1, ?_⟩
  rw [mehlerFeas_grade]
  have hbern := real_one_sub_mul_le_pow hβ0 hβ1 m
  have heq : 1 - (m : ℝ) / (M : ℝ) = 1 - (m : ℝ) * (1 / (M : ℝ)) := by ring
  simpa [ρ, heq] using hbern

/-! ## 6. Rational Ritz residual certificate, `decideGram`, and Krawtchouk witness -/

/-- **Bridge to `decideGram`:** any isometric rational Krylov basis `V : Matrix (Fin N) (Fin m) ℚ`
of capacity `m ≤ R` yields `decideGram (Vᵀ * V) R = true`. -/
theorem uSirk_isometry_decideGram {N m R : ℕ} (V : Matrix (Fin N) (Fin m) ℚ)
    (hV : Vᵀ * V = 1) (hm : m ≤ R) :
    HasBoundedGramFactor (Vᵀ * V) R ∧ decideGram (Vᵀ * V) R = true := by
  have hfac : HasBoundedGramFactor (Vᵀ * V) R := by
    refine ⟨m, hm, fun _ => 1, 1, fun _ => zero_lt_one, ?_⟩
    intro i j
    rw [hV]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply]
    · simp [Matrix.one_apply, hij, Ne.symm hij]
  exact ⟨hfac, decideGram_complete hfac⟩

/-- Exact Rayleigh quotient of a lifted reduced eigenvector `u = V y`. -/
theorem uSirk_ritz_rayleigh {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ)
    (X : Matrix (Fin N) (Fin N) ℚ) (y : Fin m → ℚ) (μ : ℚ)
    (heig : (uCompress V X).mulVec y = μ • y) (hy : vecSqNorm y = 1) :
    vecDot (V.mulVec y) (X.mulVec (V.mulVec y)) = μ := by
  rw [vecDot_symm, vecDot_mulVec_transpose V y (X.mulVec (V.mulVec y)), vecDot_symm,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  change vecDot y ((uCompress V X).mulVec y) = μ
  rw [heig, vecDot_smul_right, vecDot_self, hy, mul_one]

/-- **Rational Ritz residual certificate:** for any reduced eigenpair `(μ, y)` of
`B = Vᵀ X V` with `‖y‖² = 1`, the residual `‖X(V y) - μ (V y)‖²` equals
`‖(X - V B Vᵀ)(V y)‖²` (hence is at most `ε²` whenever `OpBound (X - V B Vᵀ) ε`). -/
theorem uSirk_ritz_residual_bound {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ)
    (X : Matrix (Fin N) (Fin N) ℚ) (y : Fin m → ℚ) (μ ε : ℚ)
    (hV : Vᵀ * V = 1) (heig : (uCompress V X).mulVec y = μ • y)
    (hy : vecSqNorm y = 1) (hbound : OpBound (X - uSirkApprox V (uCompress V X)) ε) :
    let u := V.mulVec y
    vecSqNorm (X.mulVec u - μ • u) =
        vecSqNorm ((X - uSirkApprox V (uCompress V X)).mulVec u) ∧
      vecSqNorm (X.mulVec u - μ • u) ≤ ε ^ 2 := by
  intro u
  have happ : (uSirkApprox V (uCompress V X)).mulVec u = μ • u := by
    dsimp [u, uSirkApprox]
    rw [Matrix.mulVec_mulVec]
    have hmul : (V * uCompress V X * Vᵀ) * V = V * uCompress V X := by
      calc (V * uCompress V X * Vᵀ) * V
          = V * uCompress V X * (Vᵀ * V) := by simp only [Matrix.mul_assoc]
        _ = V * uCompress V X := by rw [hV, Matrix.mul_one]
    rw [hmul, ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul]
  have hres : X.mulVec u - μ • u = (X - uSirkApprox V (uCompress V X)).mulVec u := by
    rw [Matrix.sub_mulVec, happ]
  have hu : vecSqNorm u = 1 := by
    dsimp [u]
    rw [isometry_preserves_sqNorm hV y, hy]
  refine ⟨by rw [hres], ?_⟩
  rw [hres]
  simpa [hu] using hbound.2 u

/-- Concrete diagonal number-Hamiltonian `H_M = diag(0, 1, …, M)` on the Krawtchouk
degree space `Fin (M + 1) → ℚ` (`ChapterDeformedCCR.numOp`). -/
def krawtchoukNumMat (M : ℕ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℚ :=
  Matrix.diagonal (fun k : Fin (M + 1) => (k : ℚ))

/-- Exact rational shift-invert `(H_M + γ I)⁻¹` on the Krawtchouk degree space. -/
def krawtchoukShiftInvert (M : ℕ) (γ : ℚ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℚ :=
  Matrix.diagonal (fun k : Fin (M + 1) => 1 / ((k : ℚ) + γ))

/-- Exact shifted transfer propagator `(I - τ (H_M + γ I)⁻¹)⁻¹` on `Fin (M + 1) → ℚ`. -/
def krawtchoukShiftedProp (M : ℕ) (γ τ : ℚ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℚ :=
  Matrix.diagonal (fun k : Fin (M + 1) => ((k : ℚ) + γ) / ((k : ℚ) + γ - τ))

theorem krawtchoukNumMat_symm (M : ℕ) : (krawtchoukNumMat M)ᵀ = krawtchoukNumMat M :=
  Matrix.diagonal_transpose _

theorem krawtchoukNumMat_lowerBounded (M : ℕ) : IsLowerBounded (krawtchoukNumMat M) 0 := by
  intro v
  rw [zero_mul, ratQuad_eq_vecDot]
  unfold vecDot krawtchoukNumMat
  refine Finset.sum_nonneg fun k _ => ?_
  rw [Matrix.mulVec_diagonal]
  have hk : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg _
  have hsq : 0 ≤ v k ^ 2 := sq_nonneg _
  nlinarith

theorem krawtchoukShiftInvert_isRatShiftInvert (M : ℕ) {γ : ℚ} (hγ : 0 < γ) :
    IsRatShiftInvert (krawtchoukNumMat M) γ (krawtchoukShiftInvert M γ) := by
  have hdiag : krawtchoukNumMat M + γ • (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) ℚ) =
      Matrix.diagonal (fun k : Fin (M + 1) => (k : ℚ) + γ) := by
    ext i j
    by_cases hij : i = j <;> simp [krawtchoukNumMat, hij]
  constructor
  · rw [hdiag, krawtchoukShiftInvert, Matrix.diagonal_mul_diagonal]
    have hfun : (fun k : Fin (M + 1) => ((k : ℚ) + γ) * (1 / ((k : ℚ) + γ))) = fun _ => 1 := by
      ext k
      have hk : (k : ℚ) + γ ≠ 0 := by positivity
      field_simp [hk]
    rw [hfun, Matrix.diagonal_one]
  · rw [hdiag, krawtchoukShiftInvert, Matrix.diagonal_mul_diagonal]
    have hfun : (fun k : Fin (M + 1) => (1 / ((k : ℚ) + γ)) * ((k : ℚ) + γ)) = fun _ => 1 := by
      ext k
      have hk : (k : ℚ) + γ ≠ 0 := by positivity
      field_simp [hk]
    rw [hfun, Matrix.diagonal_one]

theorem krawtchoukShiftInvert_opBound (M : ℕ) {γ : ℚ} (hγ : 0 < γ) :
    OpBound (krawtchoukShiftInvert M γ) (1 / γ) := by
  simpa using uShiftInvert_opBound (krawtchoukNumMat_lowerBounded M) (by linarith)
    (krawtchoukShiftInvert_isRatShiftInvert M hγ)

theorem krawtchoukShiftedProp_inv (M : ℕ) {γ τ : ℚ} (hγ : 0 < γ) (hτ : τ < γ) :
    (1 - τ • krawtchoukShiftInvert M γ) * krawtchoukShiftedProp M γ τ = 1 ∧
      krawtchoukShiftedProp M γ τ * (1 - τ • krawtchoukShiftInvert M γ) = 1 := by
  have hdiag : 1 - τ • krawtchoukShiftInvert M γ =
      Matrix.diagonal (fun k : Fin (M + 1) => 1 - τ / ((k : ℚ) + γ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [krawtchoukShiftInvert]
      ring
    · simp [krawtchoukShiftInvert, hij]
  rw [hdiag]
  constructor
  · unfold krawtchoukShiftedProp
    rw [Matrix.diagonal_mul_diagonal]
    have hfun : (fun k : Fin (M + 1) =>
        (1 - τ / ((k : ℚ) + γ)) * (((k : ℚ) + γ) / ((k : ℚ) + γ - τ))) = fun _ => 1 := by
      ext k
      have hk1 : (k : ℚ) + γ ≠ 0 := by positivity
      have hk2 : (k : ℚ) + γ - τ ≠ 0 := by
        have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg _
        linarith
      field_simp [hk1, hk2]
    rw [hfun, Matrix.diagonal_one]
  · unfold krawtchoukShiftedProp
    rw [Matrix.diagonal_mul_diagonal]
    have hfun : (fun k : Fin (M + 1) =>
        (((k : ℚ) + γ) / ((k : ℚ) + γ - τ)) * (1 - τ / ((k : ℚ) + γ))) = fun _ => 1 := by
      ext k
      have hk1 : (k : ℚ) + γ ≠ 0 := by positivity
      have hk2 : (k : ℚ) + γ - τ ≠ 0 := by
        have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg _
        linarith
      field_simp [hk1, hk2]
    rw [hfun, Matrix.diagonal_one]

/-- **Concrete Krawtchouk U-SIRK convergence theorem:** on the finite Krawtchouk
degree space `Fin (M + 1)` (`8 ≤ M`), with `X = (N̂ + 2 I)⁻¹` and `τ = 1`, any isometric
Krylov basis containing `K_m(X, v)` of order `m = ⌊log₂ M⌋ + 3 ≤ M` computes
`(N̂ + I)⁻¹ v = (I - X)⁻¹ X v` within tolerance `1 / M`. -/
theorem krawtchouk_uSirk_converges_to_M_tol (M dim : ℕ) (hM : 8 ≤ M)
    (V : Matrix (Fin (M + 1)) (Fin dim) ℚ)
    (ΨB : Matrix (Fin dim) (Fin dim) ℚ)
    (v : Fin (M + 1) → ℚ)
    (hV : Vᵀ * V = 1)
    (hΨB1 : (1 - (1 : ℚ) • uCompress V (krawtchoukShiftInvert M 2)) * ΨB = 1)
    (hΨB2 : ΨB * (1 - (1 : ℚ) • uCompress V (krawtchoukShiftInvert M 2)) = 1)
    (hK : InKrylovRange V (krawtchoukShiftInvert M 2) (Nat.log 2 M + 3) v) :
    Nat.log 2 M + 3 ≤ M ∧
      vecSqNorm ((krawtchoukShiftedProp M 2 1).mulVec v - (uSirkApprox V ΨB).mulVec v) ≤
        (1 / (M : ℚ)) ^ 2 * vecSqNorm v := by
  have hX := krawtchoukShiftInvert_opBound M (γ := 2) (by norm_num)
  obtain ⟨hΨ1, hΨ2⟩ := krawtchoukShiftedProp_inv M (γ := 2) (τ := 1) (by norm_num) (by norm_num)
  exact uSirk_converges_to_M_tol_log_steps M hM V (krawtchoukShiftInvert M 2)
    (krawtchoukShiftedProp M 2 1) ΨB v hV hX (by norm_num) (by norm_num)
    hΨ1 hΨ2 hΨB1 hΨB2 hK

/-! ### Executable rational U-SIRK & `decideGram` witnesses (axiom-free, no `native_decide`) -/

theorem krawtchouk_uSirk_m2_entry00 :
    neumannPoly (krawtchoukShiftInvert 2 2) 1 3 0 0 = 7 / 4 := by
  simp [neumannPoly, Finset.sum_range_succ, krawtchoukShiftInvert, pow_succ]
  norm_num

theorem krawtchouk_uSirk_m2_prop00 :
    krawtchoukShiftedProp 2 2 1 0 0 = 2 := by
  simp [krawtchoukShiftedProp]
  norm_num

theorem krawtchouk_uSirk_m2_id3_decideGram :
    decideGram ((1 : Matrix (Fin 3) (Fin 3) ℚ)ᵀ * 1) 3 = true := by
  simpa using (uSirk_isometry_decideGram (1 : Matrix (Fin 3) (Fin 3) ℚ)
    (by simp) (le_refl 3)).2

/-! ## 7. Bridge Theorems for `U2`–`U4` (`softmodes.md`) and `C6` (`cftproof.md`) -/

/-- Transposing a matrix preserves its rational operator-norm bound `OpBound A c`. -/
theorem opBound_transpose {N K : ℕ} {A : Matrix (Fin N) (Fin K) ℚ} {c : ℚ}
    (hA : OpBound A c) : OpBound Aᵀ c := by
  refine ⟨hA.1, fun v => ?_⟩
  by_cases hw : vecSqNorm (Aᵀ.mulVec v) = 0
  · rw [hw]
    exact mul_nonneg (sq_nonneg c) (vecSqNorm_nonneg v)
  · have hw_pos : 0 < vecSqNorm (Aᵀ.mulVec v) :=
      lt_of_le_of_ne (vecSqNorm_nonneg _) (Ne.symm hw)
    have hid : vecSqNorm (Aᵀ.mulVec v) = vecDot v (A.mulVec (Aᵀ.mulVec v)) := by
      rw [← vecDot_self, vecDot_mulVec_transpose A (Aᵀ.mulVec v) v]
    have hcs := vecDot_sq_le v (A.mulVec (Aᵀ.mulVec v))
    rw [← hid] at hcs
    have hmul := mul_le_mul_of_nonneg_left (hA.2 (Aᵀ.mulVec v)) (vecSqNorm_nonneg v)
    have hsq : vecSqNorm (Aᵀ.mulVec v) * vecSqNorm (Aᵀ.mulVec v) ≤
        (c ^ 2 * vecSqNorm v) * vecSqNorm (Aᵀ.mulVec v) := by
      nlinarith
    exact le_of_mul_le_mul_right hsq hw_pos

/-- **`U2` full-space block decomposition bound over `ℚ`:** for symmetric `R` (`Rᵀ = R`),
isometric `V` (`Vᵀ V = 1`), projections `P = V Vᵀ` and `Q = 1 - P`,
`‖R - V Bhat Vᵀ‖ ≤ ‖Vᵀ R V - Bhat‖ + 2‖Q R P‖ + ‖Q R Q‖`. -/
theorem uSirk_fullSpace_block_bound {N m : ℕ} (V : Matrix (Fin N) (Fin m) ℚ)
    (R : Matrix (Fin N) (Fin N) ℚ) (Bhat : Matrix (Fin m) (Fin m) ℚ)
    {δB δQP δQQ : ℚ}
    (hV : Vᵀ * V = 1) (hR_symm : Rᵀ = R)
    (hB : OpBound (Vᵀ * R * V - Bhat) δB)
    (hQP : OpBound ((1 - V * Vᵀ) * R * (V * Vᵀ)) δQP)
    (hQQ : OpBound ((1 - V * Vᵀ) * R * (1 - V * Vᵀ)) δQQ) :
    OpBound (R - uSirkApprox V Bhat) (δB + 2 * δQP + δQQ) := by
  let P : Matrix (Fin N) (Fin N) ℚ := V * Vᵀ
  let Q : Matrix (Fin N) (Fin N) ℚ := 1 - P
  have hPQ : P + Q = 1 := by simp [Q]
  have hP_symm : Pᵀ = P := by simp [P, Matrix.transpose_mul]
  have hQ_symm : Qᵀ = Q := by simp [Q, hP_symm]
  have hPRQ : P * R * Q = (Q * R * P)ᵀ := by
    conv_rhs =>
      rw [Matrix.transpose_mul (Q * R) P, Matrix.transpose_mul Q R,
        hP_symm, hR_symm, hQ_symm]
    exact Matrix.mul_assoc P R Q
  have hPQ_op : OpBound (P * R * Q) δQP := by
    rw [hPRQ]
    exact opBound_transpose hQP
  have hPRP_sub : P * R * P - uSirkApprox V Bhat = V * (Vᵀ * R * V - Bhat) * Vᵀ := by
    simp only [P, uSirkApprox, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hPRP_op : OpBound (P * R * P - uSirkApprox V Bhat) δB := by
    rw [hPRP_sub]
    have hmul := opBound_mul (opBound_mul (isometry_opBound hV) hB)
      (isometry_adjoint_opBound hV)
    simpa [one_mul, mul_one] using hmul
  have hdecomp : R - uSirkApprox V Bhat =
      (P * R * P - uSirkApprox V Bhat) + P * R * Q + Q * R * P + Q * R * Q := by
    have hR1 : R = (P + Q) * R * (P + Q) := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]
    have hR2 : R = P * R * P + P * R * Q + Q * R * P + Q * R * Q := by
      calc R = (P + Q) * R * (P + Q) := hR1
        _ = P * R * P + P * R * Q + Q * R * P + Q * R * Q := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
          abel
    conv_lhs => rw [hR2]
    abel
  have hsum : OpBound (R - uSirkApprox V Bhat) (δB + δQP + δQP + δQQ) := by
    rw [hdecomp]
    exact opBound_add (opBound_add (opBound_add hPRP_op hPQ_op) hQP) hQQ
  exact opBound_mono hsum (by linarith)

/-- Pure rational `U2` error budget splitting horizon-`M` defect `Chor / M`, geometric U-SIRK
tail `2 q^m / (1 - q)`, and certified omitted-space + Gauss + rounding floor `tail`. -/
def uSirkBudget (M m : ℕ) (qSirk Chor tail : ℚ) : ℚ :=
  Chor / (M : ℚ) + 2 * qSirk ^ m / (1 - qSirk) + tail

/-- `uSirkBudget` is monotone non-increasing in Krylov order `m`. -/
theorem uSirkBudget_antitone_m (M : ℕ) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂)
    {qSirk Chor tail : ℚ} (hq0 : 0 ≤ qSirk) (hq1 : qSirk < 1) :
    uSirkBudget M m₂ qSirk Chor tail ≤ uSirkBudget M m₁ qSirk Chor tail := by
  unfold uSirkBudget
  have hpow : qSirk ^ m₂ ≤ qSirk ^ m₁ := pow_le_pow_of_le_one hq0 hq1.le hm
  have h1q : 0 < 1 - qSirk := sub_pos.mpr hq1
  have hdiv : 2 * qSirk ^ m₂ / (1 - qSirk) ≤ 2 * qSirk ^ m₁ / (1 - qSirk) := by
    exact div_le_div_of_nonneg_right (by linarith) h1q.le
  linarith

/-- Along `4 M ≤ 2ᵐ` (in particular `m = ⌊log₂ M⌋ + 3` for `8 ≤ M`) and `qSirk ≤ 1 / 2`,
the U-SIRK plus horizon-`M` defect terms collapse to `(1 + Chor) / M`. -/
theorem uSirkBudget_log_le {M m : ℕ} (hM : 0 < M) (hm : 4 * M ≤ 2 ^ m)
    {qSirk Chor tail : ℚ} (hq0 : 0 ≤ qSirk) (hq_half : qSirk ≤ 1 / 2) :
    uSirkBudget M m qSirk Chor tail ≤ (1 + Chor) / (M : ℚ) + tail := by
  unfold uSirkBudget
  have hpow : qSirk ^ m ≤ (1 / 2 : ℚ) ^ m := pow_le_pow_left₀ hq0 hq_half m
  have hmQ : (4 : ℚ) * (M : ℚ) ≤ (2 : ℚ) ^ m := by exact_mod_cast hm
  have hMpos : (0 : ℚ) < (M : ℚ) := Nat.cast_pos.mpr hM
  have hpow_inv : (1 / 2 : ℚ) ^ m ≤ 1 / (4 * (M : ℚ)) := by
    rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
    exact hmQ
  have hden : (1 / 2 : ℚ) ≤ 1 - qSirk := by linarith
  have h1q : 0 < 1 - qSirk := by linarith
  have hrate : 2 * qSirk ^ m / (1 - qSirk) ≤ 1 / (M : ℚ) := by
    calc 2 * qSirk ^ m / (1 - qSirk)
        ≤ (2 * (1 / (4 * (M : ℚ)))) / (1 - qSirk) :=
          div_le_div_of_nonneg_right (by linarith) h1q.le
      _ ≤ (2 * (1 / (4 * (M : ℚ)))) / (1 / 2 : ℚ) := by
          apply div_le_div_of_nonneg_left _ (by norm_num) hden
          positivity
      _ = 1 / (M : ℚ) := by
          field_simp [hMpos.ne']
          norm_num
  have hsum : Chor / (M : ℚ) + 1 / (M : ℚ) = (1 + Chor) / (M : ℚ) := by ring
  linarith

/-- **`U2` non-growth along the diagonal curve `m(M) = ⌊log₂ M⌋ + 3`:** increasing the
horizon `M` monotonically tightens `uSirkBudget` whenever `0 ≤ Chor` and `0 ≤ qSirk < 1`. -/
theorem uSirkBudget_log_antitone_M {M₁ M₂ : ℕ} (hM1 : 0 < M₁) (hM : M₁ ≤ M₂)
    {qSirk Chor tail : ℚ} (hChor : 0 ≤ Chor) (hq0 : 0 ≤ qSirk) (hq1 : qSirk < 1) :
    uSirkBudget M₂ (Nat.log 2 M₂ + 3) qSirk Chor tail ≤
      uSirkBudget M₁ (Nat.log 2 M₁ + 3) qSirk Chor tail := by
  unfold uSirkBudget
  have hM1pos : (0 : ℚ) < (M₁ : ℚ) := Nat.cast_pos.mpr hM1
  have hMle : (M₁ : ℚ) ≤ (M₂ : ℚ) := by exact_mod_cast hM
  have h1 : Chor / (M₂ : ℚ) ≤ Chor / (M₁ : ℚ) :=
    div_le_div_of_nonneg_left hChor hM1pos hMle
  have hlog : Nat.log 2 M₁ + 3 ≤ Nat.log 2 M₂ + 3 :=
    Nat.add_le_add_right (Nat.log_mono_right hM) 3
  have hpow : qSirk ^ (Nat.log 2 M₂ + 3) ≤ qSirk ^ (Nat.log 2 M₁ + 3) :=
    pow_le_pow_of_le_one hq0 hq1.le hlog
  have h1q : 0 < 1 - qSirk := sub_pos.mpr hq1
  have h2 : 2 * qSirk ^ (Nat.log 2 M₂ + 3) / (1 - qSirk) ≤
      2 * qSirk ^ (Nat.log 2 M₁ + 3) / (1 - qSirk) :=
    div_le_div_of_nonneg_right (by linarith) h1q.le
  linarith

/-- **Finite-`M` stopping rule for `U4` (`softmodes.md`):** whenever the residual floor
`tail < Δcert` leaves positive headroom `η_sol = Δcert - tail`, any horizon `M ≥ 8` with
`(1 + Chor) < (Δcert - tail) * M` certifies `uSirkBudget M (⌊log₂ M⌋ + 3) qSirk Chor tail < Δcert`
without sending `m → ∞`. -/
theorem uSirk_finite_M_certifies_U4_gap (M : ℕ) (hM : 8 ≤ M)
    {qSirk Chor tail Δcert : ℚ} (hq0 : 0 ≤ qSirk) (hq_half : qSirk ≤ 1 / 2)
    (hhead : 1 + Chor < (Δcert - tail) * (M : ℚ)) :
    uSirkBudget M (Nat.log 2 M + 3) qSirk Chor tail < Δcert := by
  have hlog := log_krylov_order_bound M hM
  have hb := uSirkBudget_log_le (by omega : 0 < M) hlog.1 (Chor := Chor) (tail := tail)
    hq0 hq_half
  have hMpos : (0 : ℚ) < (M : ℚ) := by exact_mod_cast (by omega : 0 < M)
  have hlt : (1 + Chor) / (M : ℚ) < Δcert - tail := (div_lt_iff₀ hMpos).2 hhead
  linarith

/-- **Finite-`M` stopping rule for `U3` resolvent-to-energy gap:** if two shifted resolvent
levels `r₀ > r₁ > 0` have tail headroom `2 * tail < r₀ - r₁` (`0 ≤ tail`) and `M ≥ 8`
satisfies `2 * (1 + Chor) < (r₀ - r₁ - 2 * tail) * M`, then for
`e = uSirkBudget M (⌊log₂ M⌋ + 3) qSirk Chor tail`, the certified interval separation
`r₁ + e < r₀ - e` and the shift-free inverse gap `0 < 1 / (r₁ + e) - 1 / (r₀ - e)` hold. -/
theorem uSirk_finite_M_certifies_U3_gap (M : ℕ) (hM : 8 ≤ M)
    {qSirk Chor tail r₀ r₁ : ℚ} (hq0 : 0 ≤ qSirk) (hq_half : qSirk ≤ 1 / 2)
    (hr₁ : 0 < r₁) (hChor : 0 ≤ Chor) (htail : 0 ≤ tail)
    (hsep : 2 * (1 + Chor) < (r₀ - r₁ - 2 * tail) * (M : ℚ)) :
    let e := uSirkBudget M (Nat.log 2 M + 3) qSirk Chor tail
    r₁ + e < r₀ - e ∧ 0 < 1 / (r₁ + e) - 1 / (r₀ - e) := by
  intro e
  have hlog := log_krylov_order_bound M hM
  have hb : e ≤ (1 + Chor) / (M : ℚ) + tail :=
    uSirkBudget_log_le (by omega : 0 < M) hlog.1 hq0 hq_half
  have hMpos : (0 : ℚ) < (M : ℚ) := by exact_mod_cast (by omega : 0 < M)
  have he_nonneg : 0 ≤ e := by
    have hqpow : 0 ≤ qSirk ^ (Nat.log 2 M + 3) := pow_nonneg hq0 _
    have h1q : 0 < 1 - qSirk := by linarith
    have hdiv1 : 0 ≤ Chor / (M : ℚ) := div_nonneg hChor hMpos.le
    have hdiv2 : 0 ≤ 2 * qSirk ^ (Nat.log 2 M + 3) / (1 - qSirk) :=
      div_nonneg (mul_nonneg (by norm_num) hqpow) h1q.le
    dsimp [e, uSirkBudget]
    linarith
  have hdiv : 2 * (1 + Chor) / (M : ℚ) < r₀ - r₁ - 2 * tail :=
    (div_lt_iff₀ hMpos).2 hsep
  have he2 : 2 * e ≤ 2 * (1 + Chor) / (M : ℚ) + 2 * tail := by
    have hmul : 2 * ((1 + Chor) / (M : ℚ) + tail) = 2 * (1 + Chor) / (M : ℚ) + 2 * tail := by
      ring
    linarith [hb]
  have hlt : r₁ + e < r₀ - e := by linarith
  have hlo : 0 < r₁ + e := by linarith
  have hhi : 0 < r₀ - e := by linarith
  refine ⟨hlt, ?_⟩
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hlo hlt)

/-- **Pure-`ℚ` `U4` Schur coercivity lemma (scalar form):** if `0 < aHead`, `0 < dTail`, and
`b ^ 2 < aHead * dTail`, then `c = (aHead * dTail - b ^ 2) / (aHead + dTail) > 0` and
`c * (x ^ 2 + y ^ 2) ≤ aHead * x ^ 2 - 2 * b * |x * y| + dTail * y ^ 2` for all `x y : ℚ`. -/
theorem uSirk_schur_head_tail_positive {aHead dTail b : ℚ}
    (ha : 0 < aHead) (hd : 0 < dTail) (hschur : b ^ 2 < aHead * dTail) :
    let c := (aHead * dTail - b ^ 2) / (aHead + dTail)
    0 < c ∧ ∀ x y : ℚ,
      c * (x ^ 2 + y ^ 2) ≤ aHead * x ^ 2 - 2 * b * |x * y| + dTail * y ^ 2 := by
  intro c
  have hden : 0 < aHead + dTail := add_pos ha hd
  have hnum : 0 < aHead * dTail - b ^ 2 := sub_pos.mpr hschur
  refine ⟨div_pos hnum hden, fun x y => ?_⟩
  rw [abs_mul, div_mul_eq_mul_div, div_le_iff₀ hden]
  have hid : (aHead * x ^ 2 - 2 * b * (|x| * |y|) + dTail * y ^ 2) * (aHead + dTail) -
      (aHead * dTail - b ^ 2) * (x ^ 2 + y ^ 2) =
      (aHead * |x| - b * |y|) ^ 2 + (b * |x| - dTail * |y|) ^ 2 := by
    calc (aHead * x ^ 2 - 2 * b * (|x| * |y|) + dTail * y ^ 2) * (aHead + dTail) -
          (aHead * dTail - b ^ 2) * (x ^ 2 + y ^ 2)
        = (aHead * |x| ^ 2 - 2 * b * (|x| * |y|) + dTail * |y| ^ 2) * (aHead + dTail) -
            (aHead * dTail - b ^ 2) * (|x| ^ 2 + |y| ^ 2) := by
          rw [sq_abs x, sq_abs y]
      _ = (aHead * |x| - b * |y|) ^ 2 + (b * |x| - dTail * |y|) ^ 2 := by ring
  nlinarith [sq_nonneg (aHead * |x| - b * |y|), sq_nonneg (b * |x| - dTail * |y|)]

/-- **Vector-form `U4` Schur head-plus-tail coercivity over `ℚ`:** given lower-bounded head
operator `Hhead ≥ aHead`, tail operator `Htail ≥ dTail`, and cross-coupling `OpBound C b`
with `b ^ 2 < aHead * dTail`, the coupled block quadratic form is bounded below by the positive
constant `(aHead * dTail - b ^ 2) / (aHead + dTail)` without `Real.sqrt`. -/
theorem uSirk_U4_schur_head_tail_margin {m k : ℕ}
    (Hhead : Matrix (Fin m) (Fin m) ℚ) (Htail : Matrix (Fin k) (Fin k) ℚ)
    (C : Matrix (Fin m) (Fin k) ℚ)
    {aHead dTail b : ℚ} (ha : 0 < aHead) (hd : 0 < dTail)
    (hschur : b ^ 2 < aHead * dTail)
    (hHead : IsLowerBounded Hhead aHead) (hTail : IsLowerBounded Htail dTail)
    (hC : OpBound C b) (u : Fin m → ℚ) (w : Fin k → ℚ) :
    let c := (aHead * dTail - b ^ 2) / (aHead + dTail)
    0 < c ∧
      c * (vecSqNorm u + vecSqNorm w) ≤
        ratQuad Hhead u + 2 * vecDot u (C.mulVec w) + ratQuad Htail w := by
  intro c
  have hden : 0 < aHead + dTail := add_pos ha hd
  have hnum : 0 < aHead * dTail - b ^ 2 := sub_pos.mpr hschur
  refine ⟨div_pos hnum hden, ?_⟩
  have hquad_u : aHead * vecSqNorm u ≤ ratQuad Hhead u := hHead u
  have hquad_w : dTail * vecSqNorm w ≤ ratQuad Htail w := hTail w
  have hSu : 0 ≤ vecSqNorm u := vecSqNorm_nonneg u
  have hSw : 0 ≤ vecSqNorm w := vecSqNorm_nonneg w
  have hcs : vecDot u (C.mulVec w) ^ 2 ≤ vecSqNorm u * (b ^ 2 * vecSqNorm w) :=
    (vecDot_sq_le u (C.mulVec w)).trans (mul_le_mul_of_nonneg_left (hC.2 w) hSu)
  let P : ℚ := (aHead ^ 2 + b ^ 2) * vecSqNorm u + (dTail ^ 2 + b ^ 2) * vecSqNorm w
  let Q : ℚ := -2 * (aHead + dTail) * vecDot u (C.mulVec w)
  have hP0 : 0 ≤ P := by positivity
  have hQP : Q ^ 2 ≤ P ^ 2 := by
    have hdiff : P ^ 2 - Q ^ 2 =
        ((aHead ^ 2 + b ^ 2) * vecSqNorm u - (dTail ^ 2 + b ^ 2) * vecSqNorm w) ^ 2 +
          4 * (aHead * dTail - b ^ 2) ^ 2 * (vecSqNorm u * vecSqNorm w) +
          4 * (aHead + dTail) ^ 2 * (b ^ 2 * vecSqNorm u * vecSqNorm w -
            vecDot u (C.mulVec w) ^ 2) := by
      dsimp [P, Q]
      ring
    have hrem : 0 ≤ b ^ 2 * vecSqNorm u * vecSqNorm w - vecDot u (C.mulVec w) ^ 2 := by
      linarith
    nlinarith [sq_nonneg ((aHead ^ 2 + b ^ 2) * vecSqNorm u - (dTail ^ 2 + b ^ 2) * vecSqNorm w),
      sq_nonneg (aHead * dTail - b ^ 2), mul_nonneg hSu hSw, sq_nonneg (aHead + dTail)]
  have hlin : 0 ≤ P - Q := by nlinarith
  have hschur_diag : (aHead * dTail - b ^ 2) * (vecSqNorm u + vecSqNorm w) ≤
      (aHead + dTail) * (aHead * vecSqNorm u + 2 * vecDot u (C.mulVec w) +
        dTail * vecSqNorm w) := by
    have hid : (aHead + dTail) * (aHead * vecSqNorm u + 2 * vecDot u (C.mulVec w) +
          dTail * vecSqNorm w) -
        (aHead * dTail - b ^ 2) * (vecSqNorm u + vecSqNorm w) = P - Q := by
      dsimp [P, Q]
      ring
    linarith
  have hcomb : (aHead * dTail - b ^ 2) * (vecSqNorm u + vecSqNorm w) ≤
      (aHead + dTail) * (ratQuad Hhead u + 2 * vecDot u (C.mulVec w) + ratQuad Htail w) := by
    nlinarith [hquad_u, hquad_w, hden]
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith

/-- **Dyadic `C6` horizon-to-Krylov order identity (`M_q = 4^(q+2)`):** for every RG scale
`q : ℕ`, `M_q = 4^(q+2)` clears `8 ≤ M_q` and fixes `m_q = ⌊log₂ M_q⌋ + 3 = 2 q + 7`. -/
theorem uSirk_dyadic_order_eq (q : ℕ) :
    8 ≤ 4 ^ (q + 2) ∧ Nat.log 2 (4 ^ (q + 2)) + 3 = 2 * q + 7 := by
  have h4 : (4 : ℕ) ^ (q + 2) = 2 ^ (2 * q + 4) := by
    calc (4 : ℕ) ^ (q + 2) = (2 ^ 2) ^ (q + 2) := by norm_num
      _ = 2 ^ (2 * (q + 2)) := by rw [← pow_mul]
      _ = 2 ^ (2 * q + 4) := by ring_nf
  constructor
  · rw [h4]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * q + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [h4, Nat.log_pow (by norm_num : 1 < 2)]

/-- Exact finite geometric sum of dyadic horizon reciprocals `∑_{q < n} 4^{-(q+2)}`. -/
theorem uSirk_dyadic_inv_sum_eq (n : ℕ) :
    ∑ q ∈ Finset.range n, ((1 : ℚ) / (4 : ℚ) ^ (q + 2)) =
      (1 - (1 / 4 : ℚ) ^ n) / 12 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hstep : (1 : ℚ) / (4 : ℚ) ^ (n + 2) = (1 / 16 : ℚ) * (1 / 4 : ℚ) ^ n := by
      rw [pow_add, one_div_pow]
      ring
    rw [hstep, pow_succ]
    ring

/-- **Dyadic `C6` remainder sum bound (`≤ C / 6`):** if each scale `q` has solver-plus-CCR
remainder `ε q ≤ C / 4^(q+2)` with `0 ≤ C`, then every partial Cauchy increment sum obeys
`∑_{q < n} (ε (q + 1) + ε q) ≤ C / 6` uniformly in `n`. -/
theorem uSirk_dyadic_error_sum_bound (n : ℕ) {C : ℚ} (hC : 0 ≤ C)
    (ε : ℕ → ℚ) (hε : ∀ q, ε q ≤ C / (4 : ℚ) ^ (q + 2)) :
    ∑ q ∈ Finset.range n, (ε (q + 1) + ε q) ≤ C / 6 := by
  have hstep : ∀ q ∈ Finset.range n,
      ε (q + 1) + ε q ≤ C * ((1 / 4 : ℚ) * ((1 : ℚ) / (4 : ℚ) ^ (q + 2)) +
        (1 : ℚ) / (4 : ℚ) ^ (q + 2)) := by
    intro q _
    have h1 := hε (q + 1)
    have h2 := hε q
    have hpow : C / (4 : ℚ) ^ (q + 1 + 2) =
        C * ((1 / 4 : ℚ) * ((1 : ℚ) / (4 : ℚ) ^ (q + 2))) := by
      have hexp : (4 : ℚ) ^ (q + 1 + 2) = 4 * (4 : ℚ) ^ (q + 2) := by
        rw [show q + 1 + 2 = (q + 2) + 1 by omega, pow_succ']
      rw [hexp]
      ring
    have h2' : C / (4 : ℚ) ^ (q + 2) = C * ((1 : ℚ) / (4 : ℚ) ^ (q + 2)) := by ring
    linarith
  have hsum_le : ∑ q ∈ Finset.range n, (ε (q + 1) + ε q) ≤
      (C * (1 / 4 + 1)) * ∑ q ∈ Finset.range n, ((1 : ℚ) / (4 : ℚ) ^ (q + 2)) := by
    calc ∑ q ∈ Finset.range n, (ε (q + 1) + ε q)
        ≤ ∑ q ∈ Finset.range n,
            C * ((1 / 4 : ℚ) * ((1 : ℚ) / (4 : ℚ) ^ (q + 2)) +
              (1 : ℚ) / (4 : ℚ) ^ (q + 2)) := Finset.sum_le_sum hstep
      _ = (C * (1 / 4 + 1)) * ∑ q ∈ Finset.range n, ((1 : ℚ) / (4 : ℚ) ^ (q + 2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          ring
  rw [uSirk_dyadic_inv_sum_eq] at hsum_le
  have hpow0 : (0 : ℚ) ≤ (1 / 4 : ℚ) ^ n := pow_nonneg (by norm_num) n
  nlinarith

/-- **`C6` multiscale Cauchy-telescoping certificate (`cftproof.md`):** pairing dyadic
U-SIRK budgets at `M_q = 4^(q+2)` and `m_q = 2 q + 7` with any scale-by-scale Cauchy bound
`|S (q + 1) - S q| ≤ |S_hat (q + 1) - S_hat q| + ε (q + 1) + ε q` isolates the remaining
physical RG increment sum cleanly with uniform solver-plus-CCR remainder `≤ (1 + Chor) / 6`. -/
theorem uSirk_c6_telescoping_bound (n : ℕ) (S S_hat ε : ℕ → ℚ)
    {qSirk Chor : ℚ} (hq0 : 0 ≤ qSirk) (hq_half : qSirk ≤ 1 / 2) (hChor : 0 ≤ Chor)
    (hε : ∀ q, ε q ≤ uSirkBudget (4 ^ (q + 2)) (2 * q + 7) qSirk Chor 0)
    (hcauchy : ∀ q, |S (q + 1) - S q| ≤ |S_hat (q + 1) - S_hat q| + ε (q + 1) + ε q) :
    |S n - S 0| ≤ (∑ q ∈ Finset.range n, |S_hat (q + 1) - S_hat q|) + (1 + Chor) / 6 := by
  have htel : |S n - S 0| ≤ ∑ q ∈ Finset.range n, |S (q + 1) - S q| := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have htri : |S (n + 1) - S 0| ≤ |S (n + 1) - S n| + |S n - S 0| := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          abs_add_le (S (n + 1) - S n) (S n - S 0)
      linarith
  have hε_dyadic : ∀ q, ε q ≤ (1 + Chor) / (4 : ℚ) ^ (q + 2) := by
    intro q
    have hord := uSirk_dyadic_order_eq q
    have hlog := log_krylov_order_bound (4 ^ (q + 2)) hord.1
    rw [hord.2] at hlog
    have hMpos : 0 < 4 ^ (q + 2) := by positivity
    have hb := uSirkBudget_log_le hMpos hlog.1 (Chor := Chor) (tail := 0) hq0 hq_half
    push_cast at hb
    linarith [hε q, hb]
  have hsum_cauchy : ∑ q ∈ Finset.range n, |S (q + 1) - S q| ≤
      (∑ q ∈ Finset.range n, |S_hat (q + 1) - S_hat q|) +
        ∑ q ∈ Finset.range n, (ε (q + 1) + ε q) := by
    calc ∑ q ∈ Finset.range n, |S (q + 1) - S q|
        ≤ ∑ q ∈ Finset.range n, (|S_hat (q + 1) - S_hat q| + (ε (q + 1) + ε q)) := by
          apply Finset.sum_le_sum
          intro q _
          linarith [hcauchy q]
      _ = (∑ q ∈ Finset.range n, |S_hat (q + 1) - S_hat q|) +
            ∑ q ∈ Finset.range n, (ε (q + 1) + ε q) := by
          rw [Finset.sum_add_distrib]
  have hsum_err := uSirk_dyadic_error_sum_bound n (by linarith : 0 ≤ 1 + Chor) ε hε_dyadic
  linarith

end BookProof.Ultrafinitism.ChapterUltrafinitistSirk
