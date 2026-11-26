import BookProof.Phi4.ChapterScalarMomRankTwo

/-!
# The rank-two continuous orbit

This module starts `P9`: the rational quadratic-algebra certificate is mapped
into `ℂ` before the exponential orbit is formed.  The reduced Hashimoto
generator is dissipative for the physical Gram form, so the reduced orbit and
its first two derivatives are forward contractive.  The analytic contractivity
and the two-sided return interval are built on that fact.
-/

namespace BookProof.Phi4.MomRankTwo

open Matrix

noncomputable section

/-- The ring map `ℚ[i] → ℂ` sending the rational basis element to `Complex.I`. -/
noncomputable def toComplex : QI →+* ℂ where
  toFun z := (z.re : ℂ) + (z.im : ℂ) * Complex.I
  map_one' := by
    show ((1 : QI).re : ℂ) + ((1 : QI).im : ℂ) * Complex.I = 1
    simp [QuadraticAlgebra.im_one]
  map_zero' := by
    show ((0 : QI).re : ℂ) + ((0 : QI).im : ℂ) * Complex.I = 0
    simp
  map_add' := by
    intro x y
    show (((x + y).re : ℂ) + ((x + y).im : ℂ) * Complex.I) =
      ((x.re : ℂ) + (x.im : ℂ) * Complex.I) +
        ((y.re : ℂ) + (y.im : ℂ) * Complex.I)
    simp
    ring
  map_mul' := by
    intro x y
    show (((x * y).re : ℂ) + ((x * y).im : ℂ) * Complex.I) =
      ((x.re : ℂ) + (x.im : ℂ) * Complex.I) *
        ((y.re : ℂ) + (y.im : ℂ) * Complex.I)
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    ring_nf
    rw [pow_two, Complex.I_mul_I]
    push_cast
    ring

/-- The complexification sends the rational imaginary unit to `I`. -/
@[simp] theorem toComplex_ii : toComplex ((⟨0, 1⟩ : QI)) = Complex.I := by
  show ((0 : ℚ) : ℂ) + ((1 : ℚ) : ℂ) * Complex.I = Complex.I
  simp

theorem toComplex_star (z : QI) : toComplex (star z) = star (toComplex z) := by
  show ((star z).re : ℂ) + ((star z).im : ℂ) * Complex.I =
    star ((z.re : ℂ) + (z.im : ℂ) * Complex.I)
  simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

/-- Entrywise complexification of a rational matrix. -/
noncomputable def toCMat {m n : ℕ} (A : Mat m n) : Matrix (Fin m) (Fin n) ℂ :=
  A.map toComplex

theorem toCMat_mul {m n o : ℕ} (A : Mat m n) (B : Mat n o) :
    toCMat (A * B) = toCMat A * toCMat B := by
  simp [toCMat, Matrix.map_mul]

theorem toCMat_one (n : ℕ) : toCMat (1 : Mat n n) = 1 := by
  ext i j
  simp [toCMat, Matrix.one_apply]

theorem toCMat_conjTranspose {m n : ℕ} (A : Mat m n) :
    toCMat A.conjTranspose = (toCMat A).conjTranspose := by
  ext i j
  simp [toCMat, Matrix.conjTranspose_apply, toComplex_star]

theorem toCMat_trace {n : ℕ} (A : Mat n n) :
    (toCMat A).trace = toComplex A.trace := by
  simp [toCMat, Matrix.trace, map_sum]

theorem toCMat_hermitian {n : ℕ} (A : Mat n n) (h : A.conjTranspose = A) :
    (toCMat A).conjTranspose = toCMat A := by
  rw [← toCMat_conjTranspose, h]

theorem toCMat_add {m n : ℕ} (A B : Mat m n) : toCMat (A + B) = toCMat A + toCMat B := by
  ext i j
  simp [toCMat, map_add]

theorem toCMat_neg {m n : ℕ} (A : Mat m n) : toCMat (-A) = -toCMat A := by
  ext i j
  simp [toCMat, map_neg]

theorem toCMat_smul {m n : ℕ} (c : QI) (A : Mat m n) :
    toCMat (c • A) = toComplex c • toCMat A := by
  ext i j
  simp [toCMat, Matrix.smul_apply, map_mul, smul_eq_mul]

theorem toCMat_nsmul {m n : ℕ} (k : ℕ) (A : Mat m n) :
    toCMat (k • A) = k • toCMat A := by
  ext i j
  simp [toCMat, Matrix.smul_apply, map_natCast, map_mul, smul_eq_mul]

@[simp] theorem toComplex_natCast (n : ℕ) : toComplex (n : QI) = (n : ℂ) := by
  simp [toComplex]

/-! ## Elementary quadratic-form algebra -/

open scoped Matrix.Norms.Operator

/-- The Hermitian pairing `∑ conj v_i * w_i`. -/
noncomputable def dot {n : ℕ} (v w : Fin n → ℂ) : ℂ := star v ⬝ᵥ w

/-- The real quadratic form `v ↦ Re (conj v ⬝ W v)`. -/
noncomputable def normSqC {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (dot v (W *ᵥ v)).re

theorem dot_mulVec_conjTranspose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (v : Fin n → ℂ) (w : Fin m → ℂ) :
    dot v (A.conjTranspose *ᵥ w) = dot (A *ᵥ v) w := by
  simp only [dot, dotProduct_mulVec, vecMul_conjTranspose, star_star]

theorem normSqC_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (W : Matrix (Fin m) (Fin m) ℂ) (v : Fin n → ℂ) :
    normSqC (A.conjTranspose * W * A) v = normSqC W (A *ᵥ v) := by
  have h : (A.conjTranspose * W * A) *ᵥ v = A.conjTranspose *ᵥ (W *ᵥ (A *ᵥ v)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  show (dot v ((A.conjTranspose * W * A) *ᵥ v)).re = (dot (A *ᵥ v) (W *ᵥ (A *ᵥ v))).re
  rw [h, dot_mulVec_conjTranspose]

theorem normSqC_smul {n : ℕ} (c : ℝ) (W : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    normSqC (c • W) v = c * normSqC W v := by
  show (star v ⬝ᵥ ((c • W) *ᵥ v)).re = c * (star v ⬝ᵥ (W *ᵥ v)).re
  rw [Matrix.smul_mulVec]
  have h : (star v ⬝ᵥ (c • (W *ᵥ v))).re = c * (star v ⬝ᵥ (W *ᵥ v)).re := by
    rw [dotProduct_smul]
    exact Complex.smul_re c _
  exact h

theorem normSqC_neg {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    normSqC (-W) v = -normSqC W v := by
  show (star v ⬝ᵥ ((-W) *ᵥ v)).re = -(star v ⬝ᵥ (W *ᵥ v)).re
  rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]

theorem normSqC_nsmul {n : ℕ} (k : ℕ) (W : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    normSqC (k • W) v = k * normSqC W v := by
  show (star v ⬝ᵥ ((k • W) *ᵥ v)).re = k * (star v ⬝ᵥ (W *ᵥ v)).re
  rw [Matrix.smul_mulVec]
  have h : (star v ⬝ᵥ (k • (W *ᵥ v))).re = k * (star v ⬝ᵥ (W *ᵥ v)).re := by
    rw [dotProduct_smul]
    simp [nsmul_eq_mul]
  exact h

theorem normSqC_diagonal_nonneg {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : Fin n → ℂ) :
    0 ≤ normSqC (Matrix.diagonal (fun i => (w i : ℂ))) v := by
  show 0 ≤ (star v ⬝ᵥ (Matrix.diagonal (fun i => (w i : ℂ)) *ᵥ v)).re
  simp only [Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
  apply Finset.sum_nonneg
  intro i _
  have h : (star (v i) * ((w i : ℂ) * v i)).re = w i * ‖v i‖ ^ 2 := by
    have hzz : star (v i) * v i = ((Complex.normSq (v i) : ℝ) : ℂ) := by
      rw [show star (v i) = starRingEnd ℂ (v i) from rfl, ← Complex.normSq_eq_conj_mul_self]
    have hval : star (v i) * ((w i : ℂ) * v i) = ((w i * ‖v i‖ ^ 2 : ℝ) : ℂ) := by
      rw [show star (v i) * ((w i : ℂ) * v i) = (w i : ℂ) * (star (v i) * v i) by ring,
        hzz, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hval, Complex.ofReal_re]
  rw [h]
  exact mul_nonneg (hw i) (sq_nonneg _)

set_option maxHeartbeats 1000000 in
theorem dot_conj_hermitian {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W.conjTranspose = W) (a b : Fin n → ℂ) :
    dot a (W *ᵥ b) = star (dot b (W *ᵥ a)) := by
  show star a ⬝ᵥ (W *ᵥ b) = star (star b ⬝ᵥ (W *ᵥ a))
  calc star a ⬝ᵥ (W *ᵥ b) = (star a ᵥ* W) ⬝ᵥ b := dotProduct_mulVec _ _ _
    _ = (star a ᵥ* W.conjTranspose) ⬝ᵥ b := by rw [hW]
    _ = star (W *ᵥ a) ⬝ᵥ b := by rw [← Matrix.star_mulVec]
    _ = star (star b ⬝ᵥ (W *ᵥ a)) := Matrix.star_dotProduct _ _

theorem dot_add {n : ℕ} (v a b : Fin n → ℂ) : dot v (a + b) = dot v a + dot v b := by
  simp [dot, dotProduct_add]

theorem dot_hasDerivAt {n : ℕ} {v w : ℝ → Fin n → ℂ} {v' w' : Fin n → ℂ} {s : ℝ}
    (hv : HasDerivAt v v' s) (hw : HasDerivAt w w' s) :
    HasDerivAt (fun t => dot (v t) (w t)) (dot v' (w s) + dot (v s) w') s := by
  have hv' : ∀ i, HasDerivAt (fun t => v t i) (v' i) s := fun i => hasDerivAt_pi.mp hv i
  have hw' : ∀ i, HasDerivAt (fun t => w t i) (w' i) s := fun i => hasDerivAt_pi.mp hw i
  have h : HasDerivAt (fun t => ∑ i, star (v t i) * w t i)
      (∑ i, (star (v' i) * w s i + star (v s i) * w' i)) s := by
    apply HasDerivAt.fun_sum
    intro i _
    exact ((hv' i).star).mul (hw' i)
  simpa only [dot, dotProduct, Finset.sum_add_distrib] using h

theorem HasDerivAt.mulVec {m n : ℕ} {u : ℝ → Matrix (Fin m) (Fin n) ℂ}
    {u' : Matrix (Fin m) (Fin n) ℂ} {v : Fin n → ℂ} {s : ℝ} (hu : HasDerivAt u u' s) :
    HasDerivAt (fun t => u t *ᵥ v) (u' *ᵥ v) s := by
  have hu' : ∀ i j, HasDerivAt (fun t => u t i j) (u' i j) s :=
    fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hu i) j
  have h : HasDerivAt (fun t => fun i => ∑ j, u t i j * v j)
      (fun i => ∑ j, u' i j * v j) s := by
    apply hasDerivAt_pi.mpr
    intro i
    apply HasDerivAt.fun_sum
    intro j _
    exact (hu' i j).mul_const (v j)
  simpa [Matrix.mulVec, dotProduct] using h

theorem HasDerivAt.const_mulVec {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℂ)
    {v : ℝ → Fin n → ℂ} {v' : Fin n → ℂ} {s : ℝ} (hv : HasDerivAt v v' s) :
    HasDerivAt (fun t => W *ᵥ v t) (W *ᵥ v') s := by
  have hv' : ∀ j, HasDerivAt (fun t => v t j) (v' j) s := fun j => hasDerivAt_pi.mp hv j
  have h : HasDerivAt (fun t => fun i => ∑ j, W i j * v t j)
      (fun i => ∑ j, W i j * v' j) s := by
    apply hasDerivAt_pi.mpr
    intro i
    apply HasDerivAt.fun_sum
    intro j _
    exact (hv' j).const_mul (W i j)
  simpa [Matrix.mulVec, dotProduct] using h

theorem hasDerivAt_normSqC {n : ℕ} {W : Matrix (Fin n) (Fin n) ℂ}
    (hW : W.conjTranspose = W) {u u' : ℝ → Fin n → ℂ}
    (hu : ∀ s, HasDerivAt u (u' s) s) (s : ℝ) :
    HasDerivAt (fun t => normSqC W (u t))
      (2 * (dot (u s) (W *ᵥ (u' s))).re) s := by
  have h := dot_hasDerivAt (hu s) (HasDerivAt.const_mulVec W (hu s))
  have hre : HasDerivAt (fun t => (dot (u t) (W *ᵥ u t)).re)
      ((dot (u' s) (W *ᵥ u s) + dot (u s) (W *ᵥ u' s)).re) s :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h
  have hz : dot (u' s) (W *ᵥ u s) = star (dot (u s) (W *ᵥ u' s)) :=
    dot_conj_hermitian W hW _ _
  rw [hz] at hre
  have hder : (star (dot (u s) (W *ᵥ u' s)) + dot (u s) (W *ᵥ u' s)).re =
      2 * (dot (u s) (W *ᵥ u' s)).re := by
    have hconj : (star (dot (u s) (W *ᵥ u' s))).re = (dot (u s) (W *ᵥ u' s)).re := by
      simp
    rw [Complex.add_re, hconj]
    ring
  rw [hder] at hre
  exact hre

set_option maxHeartbeats 1000000 in
theorem two_re_dot_eq_normSqC {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W.conjTranspose = W) (G : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    2 * (dot v (W *ᵥ (G *ᵥ v))).re =
      normSqC (G.conjTranspose * W + W * G) v := by
  have hsum : (G.conjTranspose * W + W * G) *ᵥ v =
      G.conjTranspose *ᵥ (W *ᵥ v) + W *ᵥ (G *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h1 : dot v (G.conjTranspose *ᵥ (W *ᵥ v)) = star (dot v (W *ᵥ (G *ᵥ v))) := by
    rw [dot_mulVec_conjTranspose]
    have h := dot_conj_hermitian W hW v (G *ᵥ v)
    rw [h, star_star]
  show 2 * (dot v (W *ᵥ (G *ᵥ v))).re =
      (dot v ((G.conjTranspose * W + W * G) *ᵥ v)).re
  rw [hsum, dot_add, h1, Complex.add_re]
  have hre : (star (dot v (W *ᵥ (G *ᵥ v)))).re = (dot v (W *ᵥ (G *ᵥ v))).re := by
    simp
  rw [hre]
  ring

/-! ## The reduced generator and its orbit -/

/-- The complexified reduced Hashimoto generator. -/
noncomputable def GC : Matrix (Fin 2) (Fin 2) ℂ := toCMat generator

/-- The complexified physical Gram matrix of the two-column basis. -/
noncomputable def W2C : Matrix (Fin 2) (Fin 2) ℂ := toCMat gram

/-- The complexified retained three-mode metric. -/
noncomputable def metricC : Matrix (Fin 3) (Fin 3) ℂ := toCMat metric

/-- The complexified leak. -/
noncomputable def leakC : Matrix (Fin 3) (Fin 2) ℂ := toCMat leak

theorem W2C_hermitian : W2C.conjTranspose = W2C :=
  toCMat_hermitian gram gram_hermitian

/-- The reduced seed `e₀`. -/
def e0 : Fin 2 → ℂ := ![1, 0]

/-- The reduced trajectory `s ↦ exp (s G) e₀`. -/
noncomputable def c (s : ℝ) : Fin 2 → ℂ :=
  (NormedSpace.exp ((s : ℂ) • GC)).mulVec e0

theorem c_zero : c 0 = e0 := by
  simp [c]

theorem expGC_mul (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • GC) * GC = GC * NormedSpace.exp ((s : ℂ) • GC) := by
  have h : Commute GC (NormedSpace.exp ((s : ℂ) • GC)) :=
    (Commute.refl GC).smul_right (s : ℂ) |>.exp_right
  exact h.eq.symm

theorem c_deriv_eq (s : ℝ) :
    (NormedSpace.exp ((s : ℂ) • GC) * GC) *ᵥ e0 = GC *ᵥ c s := by
  show (NormedSpace.exp ((s : ℂ) • GC) * GC) *ᵥ e0 =
    GC *ᵥ ((NormedSpace.exp ((s : ℂ) • GC)).mulVec e0)
  rw [expGC_mul s]
  rw [← Matrix.mulVec_mulVec]

theorem hasDerivAt_c (s : ℝ) : HasDerivAt c (GC *ᵥ c s) s := by
  have h := HasDerivAt.mulVec (m := 2) (n := 2) (u := fun t : ℝ =>
    NormedSpace.exp ((t : ℂ) • GC)) (u' := NormedSpace.exp ((s : ℂ) • GC) * GC)
    (v := e0) (hasDerivAt_exp_smul_const (𝕂 := ℝ) GC s)
  exact h.congr_deriv (c_deriv_eq s)

/-- The first derivative orbit `G c (s)`. -/
noncomputable def c1 (s : ℝ) : Fin 2 → ℂ := GC *ᵥ c s

/-- The second derivative orbit `G² c (s)`. -/
noncomputable def c2 (s : ℝ) : Fin 2 → ℂ := GC *ᵥ c1 s

theorem hasDerivAt_c1 (s : ℝ) : HasDerivAt c1 (GC *ᵥ c1 s) s :=
  HasDerivAt.const_mulVec GC (hasDerivAt_c s)

theorem hasDerivAt_c2 (s : ℝ) : HasDerivAt c2 (GC *ᵥ c2 s) s :=
  HasDerivAt.const_mulVec GC (hasDerivAt_c1 s)

/-! ## Complexified dissipation -/

theorem dissipation_C :
    GC.conjTranspose * W2C + W2C * GC =
      -(10 • (leakC.conjTranspose * metricC * leakC)) := by
  have h := congrArg toCMat dissipation
  simp only [toCMat_add, toCMat_mul, toCMat_conjTranspose, toCMat_neg, toCMat_nsmul,
    GC, W2C, leakC, metricC] at h
  show (toCMat generator).conjTranspose * toCMat gram + toCMat gram * toCMat generator =
    -(10 • ((toCMat leak).conjTranspose * toCMat metric * toCMat leak))
  exact h

theorem dissipation_form (v : Fin 2 → ℂ) :
    normSqC (GC.conjTranspose * W2C + W2C * GC) v =
      -10 * normSqC (leakC.conjTranspose * metricC * leakC) v := by
  rw [dissipation_C, normSqC_neg, normSqC_nsmul]
  ring

theorem metricC_diagonal : metricC =
    Matrix.diagonal (fun i => ((![1, 2, 6] : Fin 3 → ℚ) i : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metricC, metric, toCMat, toComplex, Matrix.diagonal_apply,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.im_one] <;> norm_num

theorem leak_form_nonneg (v : Fin 2 → ℂ) :
    0 ≤ normSqC (leakC.conjTranspose * metricC * leakC) v := by
  rw [normSqC_mulVec, metricC_diagonal]
  exact normSqC_diagonal_nonneg _ (by intro i; fin_cases i <;> norm_num) _

theorem dissipation_nonpos (v : Fin 2 → ℂ) :
    normSqC (GC.conjTranspose * W2C + W2C * GC) v ≤ 0 := by
  rw [dissipation_form]
  nlinarith [leak_form_nonneg v]

/-! ## Forward contractivity -/

set_option maxHeartbeats 1000000 in
/-- Every orbit with velocity `G u` has a non-increasing `W₂` quadratic form. -/
theorem orbit_contractive {u : ℝ → Fin 2 → ℂ}
    (hu : ∀ s, HasDerivAt u (GC *ᵥ u s) s) {s : ℝ} (hs : 0 ≤ s) :
    normSqC W2C (u s) ≤ normSqC W2C (u 0) := by
  have hanti : AntitoneOn (fun t : ℝ => normSqC W2C (u t)) (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t =>
      2 * (dot (u t) (W2C *ᵥ (GC *ᵥ u t))).re) (convex_Ici 0) ?_ ?_ ?_
    · intro t _
      exact (hasDerivAt_normSqC W2C_hermitian hu t).continuousAt.continuousWithinAt
    · intro t _
      have h := hasDerivAt_normSqC W2C_hermitian hu t
      exact h.hasDerivWithinAt
    · intro t _
      rw [show (fun t => 2 * (dot (u t) (W2C *ᵥ (GC *ᵥ u t))).re) t =
          2 * (dot (u t) (W2C *ᵥ (GC *ᵥ u t))).re from rfl,
        two_re_dot_eq_normSqC W2C W2C_hermitian GC (u t)]
      exact dissipation_nonpos (u t)
  exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs

theorem cont_orbit_contractive {s : ℝ} (hs : 0 ≤ s) :
    normSqC W2C (c s) ≤ normSqC W2C (c 0) :=
  orbit_contractive (fun u => hasDerivAt_c u) hs

theorem cont_orbit_contractive1 {s : ℝ} (hs : 0 ≤ s) :
    normSqC W2C (c1 s) ≤ normSqC W2C (c1 0) :=
  orbit_contractive (fun u => hasDerivAt_c1 u) hs

theorem cont_orbit_contractive2 {s : ℝ} (hs : 0 ≤ s) :
    normSqC W2C (c2 s) ≤ normSqC W2C (c2 0) :=
  orbit_contractive (fun u => hasDerivAt_c2 u) hs

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

/-! ## Synthesis norms -/

theorem fullMetric_im_zero (i j : Fin 11) : (fullMetric i j).im = 0 := by
  revert i j
  decide +kernel

theorem toCMat_fullMetric_apply (i j : Fin 11) :
    toCMat fullMetric i j = ((fullMetric i j).re : ℂ) := by
  show toComplex (fullMetric i j) = _
  rw [show toComplex (fullMetric i j) =
      ((fullMetric i j).re : ℂ) + ((fullMetric i j).im : ℂ) * Complex.I from rfl,
    fullMetric_im_zero i j]
  simp

theorem normSqC_fullMetric_apply (a : Fin 11 → ℂ) :
    normSqC (toCMat fullMetric) a =
      (∑ i, ∑ j, star (a i) * ((fullMetric i j).re : ℂ) * a j).re := by
  simp [normSqC, dot, Matrix.mulVec, dotProduct, toCMat_fullMetric_apply, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]

theorem norm_synthesize_sq (a : Fin 11 → ℂ) :
    ‖synthesize a‖ ^ 2 =
      (Real.sqrt (2 * Real.pi)) ^ 4 * normSqC (toCMat fullMetric) a := by
  have h := synthesis_inner a a
  have h2 : ((‖synthesize a‖ ^ 2 : ℝ) : ℂ) =
      (∑ i, ∑ j, star (a i) * ((fullMetric i j).re : ℂ) * a j) *
        ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ 4 := by
    have hs : ((‖synthesize a‖ ^ 2 : ℝ) : ℂ) = ((‖synthesize a‖ : ℂ)) ^ 2 := by
      push_cast
      ring
    rw [hs]
    exact (inner_self_eq_norm_sq_to_K (synthesize a)).symm.trans h
  have hdC : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ 4 =
      (((Real.sqrt (2 * Real.pi)) ^ 4 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]
  rw [hdC] at h2
  have hre := congrArg Complex.re h2
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.ofReal_ofNat] at hre
  rw [← normSqC_fullMetric_apply a, mul_comm] at hre
  exact hre

theorem norm_pgLp_one_sq :
    ‖pgLp (d := 4) 1‖ ^ 2 = (Real.sqrt (2 * Real.pi)) ^ 4 := by
  have h0 := contMode_inner (0 : Fin 11) 0
  have hc : contMode (0 : Fin 11) = 1 := by simp [contMode]
  rw [hc] at h0
  have hf : (fullMetric (0 : Fin 11) 0).re = 1 := by simp [fullMetric]
  rw [hf] at h0
  norm_num at h0
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hsq : ((‖pgLp (d := 4) 1‖ ^ 2 : ℝ) : ℂ) =
      (((Real.sqrt 2 * Real.sqrt Real.pi) ^ 4 : ℝ) : ℂ) := by
    push_cast
    exact h0
  exact Complex.ofReal_injective hsq

/-! ## The reconstructed core orbit -/

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

/-- The eleven-row embedding of the three retained columns. -/
def Vmat : Mat 11 2 := fun i j => if h : (i : ℕ) < 3 then basis ⟨(i : ℕ), h⟩ j else 0

theorem Vmat_gram : Vmat.conjTranspose * fullMetric * Vmat = gram := by
  decide +kernel

/-- The complexified retained embedding. -/
noncomputable def VmatC : Matrix (Fin 11) (Fin 2) ℂ := toCMat Vmat

/-- The complexified basis of the two reduced coordinates. -/
noncomputable def basisC : Matrix (Fin 3) (Fin 2) ℂ := toCMat basis

/-- The complexified eleven-column superoperator, restricted to the three
retained modes. -/
noncomputable def fullColumnsC : Matrix (Fin 11) (Fin 3) ℂ := toCMat fullColumns

theorem normSqC_Vmat (v : Fin 2 → ℂ) :
    normSqC (toCMat fullMetric) (VmatC *ᵥ v) = normSqC W2C v := by
  have h := normSqC_mulVec VmatC (toCMat fullMetric) v
  rw [← h]
  congr 1
  show (toCMat Vmat).conjTranspose * toCMat fullMetric * toCMat Vmat = toCMat gram
  rw [← toCMat_conjTranspose, ← toCMat_mul, ← toCMat_mul, Vmat_gram]

theorem synthesize_mem (a : Fin 11 → ℂ) : synthesize a ∈ polyGaussCore (d := 4) := by
  unfold synthesize
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (pgLp_mem_core _)

/-- The Gaussian-core element of an eleven-mode coefficient vector. -/
noncomputable def synthesizeC (a : Fin 11 → ℂ) : polyGaussCore (d := 4) :=
  ⟨synthesize a, synthesize_mem a⟩

@[simp] theorem synthesizeC_coe (a : Fin 11 → ℂ) :
    (synthesizeC a : L2d 4) = synthesize a := rfl

theorem hasDerivAt_synthesize {a : ℝ → Fin 11 → ℂ} {a' : Fin 11 → ℂ} {s : ℝ}
    (ha : HasDerivAt a a' s) :
    HasDerivAt (fun t => synthesize (a t)) (synthesize a') s := by
  have h : (fun t => synthesize (a t)) = fun t => ∑ i, a t i • pgLp (contMode i) := rfl
  rw [h]
  apply HasDerivAt.fun_sum
  intro i _
  exact (hasDerivAt_pi.mp ha i).smul_const (pgLp (contMode i))

/-- The reconstructed core orbit. -/
noncomputable def y (s : ℝ) : polyGaussCore (d := 4) :=
  synthesizeC (VmatC *ᵥ c s)

/-- The velocity of the reconstructed orbit. -/
noncomputable def v (s : ℝ) : L2d 4 := synthesize (VmatC *ᵥ c1 s)

/-- The acceleration of the reconstructed orbit. -/
noncomputable def acc (s : ℝ) : L2d 4 := synthesize (VmatC *ᵥ c2 s)

theorem y_zero : (y 0 : L2d 4) = pgLp (d := 4) 1 := by
  have hc : c 0 = e0 := c_zero
  have hV : VmatC *ᵥ e0 = Pi.single (0 : Fin 11) 1 := by
    funext i
    simp only [VmatC, toCMat, Vmat, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Pi.single_apply]
    fin_cases i <;>
      simp [Vmat, toComplex, basis, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  show synthesize (VmatC *ᵥ c 0) = pgLp (d := 4) 1
  rw [hc, hV]
  simp [synthesize, contMode]

theorem hasDerivAt_y (s : ℝ) :
    HasDerivAt (fun u => (y u : L2d 4)) (v s) s := by
  have hb : HasDerivAt (fun t => VmatC *ᵥ c t) (VmatC *ᵥ c1 s) s := by
    have h := HasDerivAt.const_mulVec VmatC (hasDerivAt_c s)
    simpa [c1] using h
  exact hasDerivAt_synthesize hb

theorem hasDerivAt_v (s : ℝ) :
    HasDerivAt (fun u => v u) (acc s) s := by
  have hb : HasDerivAt (fun t => VmatC *ᵥ c1 t) (VmatC *ᵥ c2 s) s := by
    have h := HasDerivAt.const_mulVec VmatC (hasDerivAt_c1 s)
    simpa [c2] using h
  exact hasDerivAt_synthesize hb

theorem y_norm_sq (s : ℝ) :
    ‖(y s : L2d 4)‖ ^ 2 = ‖pgLp (d := 4) 1‖ ^ 2 * normSqC W2C (c s) := by
  change ‖synthesize (VmatC *ᵥ c s)‖ ^ 2 = _
  rw [norm_synthesize_sq, normSqC_Vmat, norm_pgLp_one_sq]

theorem normSqC_W2C_e0 : normSqC W2C e0 = 1 := by
  have h : normSqC W2C e0 = normSqC (toCMat fullMetric) (VmatC *ᵥ e0) := by
    rw [normSqC_Vmat]
  rw [h]
  have hV : VmatC *ᵥ e0 = Pi.single (0 : Fin 11) 1 := by
    funext i
    simp only [VmatC, toCMat, Vmat, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Pi.single_apply]
    fin_cases i <;>
      simp [Vmat, toComplex, basis, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
        QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  rw [hV, normSqC_fullMetric_apply]
  simp [fullMetric, Pi.single_apply, Matrix.diagonal_apply]

/-- The complexified full defect `D = i V G − H V` on the eleven modes. -/
noncomputable def defectC : Matrix (Fin 11) (Fin 2) ℂ := toCMat defect

/-- The complexified defect Gram identity. -/
theorem defectC_gram :
    defectCᴴ * toCMat fullMetric * defectC = toCMat defectGram := by
  show (toCMat defect).conjTranspose * toCMat fullMetric * toCMat defect = toCMat defectGram
  rw [← toCMat_conjTranspose, ← toCMat_mul, ← toCMat_mul, full_defect_gram]

/-- The full defect norm of a reduced state equals the defect-Gram form of its
coordinate vector. -/
theorem normSqC_defectC (v : Fin 2 → ℂ) :
    normSqC (toCMat defectGram) v = normSqC (toCMat fullMetric) (defectC *ᵥ v) := by
  conv_lhs => rw [← defectC_gram]
  rw [normSqC_mulVec]

/-- The seed residual rate: the defect of the initial reduced state is bounded by
`(23/10)²` in the physical Gram form. -/
theorem defect_rate_e0 :
    normSqC (toCMat defectGram) e0 ≤ (23 / 10 : ℝ) ^ 2 := by
  have h : normSqC (toCMat defectGram) e0 = (defectGram 0 0).re := by
    rw [normSqC]
    simp [dot, e0, toCMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, toComplex,
      defectGram]
  rw [h]
  have hq : ((defectGram 0 0).re : ℝ) ≤ ((23 / 10 : ℚ) ^ 2 : ℝ) := by
    exact_mod_cast (show (defectGram 0 0).re ≤ (23 / 10 : ℚ) ^ 2 by decide +kernel)
  norm_num at hq
  rw [show ((23 / 10 : ℝ) ^ 2) = 529 / 100 by norm_num]
  exact hq

theorem y_norm_contractive {s : ℝ} (hs : 0 ≤ s) :
    ‖(y s : L2d 4)‖ ≤ ‖pgLp (d := 4) 1‖ := by
  have hle : normSqC W2C (c s) ≤ 1 := by
    have h := cont_orbit_contractive hs
    rwa [c_zero, normSqC_W2C_e0] at h
  have hsq : ‖(y s : L2d 4)‖ ^ 2 ≤ ‖pgLp (d := 4) 1‖ ^ 2 := by
    rw [y_norm_sq]
    calc ‖pgLp (d := 4) 1‖ ^ 2 * normSqC W2C (c s) ≤ ‖pgLp (d := 4) 1‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = ‖pgLp (d := 4) 1‖ ^ 2 := mul_one _
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h

/-! ## The assembly identity for the reconstructed orbit

The three retained inputs to `fullColumns` sit in the first three rows, so the
eleven-mode sum of the inner Hamiltonian action collapses to a three-term sum,
and the result is exactly the synthesis of the eleven-mode coefficient vector
`fullColumns · basis · c`. -/

/-- The retained index embedding, matching the rank-two certificate window. -/
def retainedIdx (i : Fin 3) : Fin 11 := i.castLE (by decide)

/-- The retained rows of `Vmat` are the rows of `basis`. -/
theorem Vmat_retained (j : Fin 3) : Vmat (retainedIdx j) = basis j := by
  funext l
  simp only [Vmat, retainedIdx, Fin.val_castLE, dif_pos j.2]

/-- On the retained rows the complexified embedding acts as the complexified
basis. -/
theorem VmatC_mulVec_retained (a : Fin 2 → ℂ) (j : Fin 3) :
    (VmatC *ᵥ a) (retainedIdx j) = (basisC *ᵥ a) j := by
  have hrow := Vmat_retained j
  simp only [VmatC, basisC, toCMat, Matrix.map_apply, Matrix.mulVec, dotProduct]
  rw [hrow]

/-- Past the third row the complexified embedding vanishes. -/
theorem VmatC_mulVec_of_three_le (a : Fin 2 → ℂ) (i : Fin 11) (h : 3 ≤ (i : ℕ)) :
    (VmatC *ᵥ a) i = 0 := by
  have hz : ∀ j : Fin 2, Vmat i j = 0 := by
    intro j
    have hlt : ¬ ((i : ℕ) < 3) := by omega
    simp only [Vmat, dif_neg hlt]
  simp [VmatC, toCMat, Matrix.map_apply, Matrix.mulVec, dotProduct, hz]

/-- The Gaussian-core element is the sum of its mode components. -/
theorem synthesizeC_eq_sum (a : Fin 11 → ℂ) :
    synthesizeC a = ∑ i, a i • ⟨pgLp (contMode i), pgLp_mem_core (contMode i)⟩ := by
  apply Subtype.ext
  simp [synthesizeC, synthesize]

private theorem filter_univ_eq_image :
    (Finset.univ.filter (fun i : Fin 11 => (i : ℕ) < 3))
      = Finset.univ.image retainedIdx := by
  decide +kernel

/-- A sum over `Fin 11` whose terms vanish past the retained window collapses to
a sum over `Fin 3`. -/
theorem sum_fin_eleven_eq_sum_three {M : Type*} [AddCommMonoid M]
    (f : Fin 11 → M) (hf : ∀ i : Fin 11, ¬ ((i : ℕ) < 3) → f i = 0) :
    ∑ i : Fin 11, f i = ∑ j : Fin 3, f (retainedIdx j) := by
  have hsupp : (∑ i ∈ (Finset.univ.filter (fun i : Fin 11 => (i : ℕ) < 3)), f i)
      = ∑ i : Fin 11, f i := by
    refine Finset.sum_subset (s₂ := Finset.univ) (f := f) (Finset.filter_subset _ _) ?_
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hf x hx
  rw [← hsupp, filter_univ_eq_image]
  rw [Finset.sum_image]
  intro x _ y _ hxy
  simpa [retainedIdx] using hxy

/-- `toComplex` of a rational quadratic number with vanishing imaginary part is
its real part. -/
theorem toComplex_of_im_zero (z : QI) (h : z.im = 0) :
    toComplex z = (z.re : ℂ) := by
  show (z.re : ℂ) + (z.im : ℂ) * Complex.I = (z.re : ℂ)
  rw [h]
  simp

/-- The action table `fullColumns` is real. -/
theorem fullColumns_im_zero (k : Fin 11) (j : Fin 3) : (fullColumns k j).im = 0 := by
  revert k j
  decide +kernel

/-- The complexified action table entry is its real part. -/
theorem fullColumnsC_apply (k : Fin 11) (j : Fin 3) :
    fullColumnsC k j = ((fullColumns k j).re : ℂ) := by
  show toComplex (fullColumns k j) = _
  exact toComplex_of_im_zero _ (fullColumns_im_zero k j)

/-- `pgLp` turns a complex combination of the eleven modes into the
corresponding combination of the mode vectors. -/
theorem pgLp_sum_smul (c : Fin 11 → ℂ) :
    pgLp (∑ k : Fin 11, C (c k) * contMode k) = ∑ k, c k • pgLp (contMode k) := by
  rw [← HermiteProductCore.pgMap_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [← smul_eq_C_mul, map_smul, HermiteProductCore.pgMap_apply]

-- The eleven-mode collapse and the eleven-row table are expensive to unify
-- definitionally, so the default recursion and heartbeat budgets do not suffice.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- The inner Hamiltonian action on the eleven-mode synthesis is the synthesis of
the action table applied to the retained coordinates. -/
theorem innerHam_synthesizeC (a : Fin 2 → ℂ) :
    unitMomCont.innerHam (synthesizeC (VmatC *ᵥ a)) =
      synthesize (fullColumnsC *ᵥ (basisC *ᵥ a)) := by
  set d : Fin 3 → ℂ := basisC *ᵥ a with hd
  have h1 : unitMomCont.innerHam (synthesizeC (VmatC *ᵥ a)) =
      ∑ i : Fin 11, (VmatC *ᵥ a) i •
        unitMomCont.innerHam ⟨pgLp (contMode i), pgLp_mem_core (contMode i)⟩ := by
    rw [synthesizeC_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hHj : ∀ j : Fin 3,
      unitMomCont.innerHam ⟨pgLp (contMode (retainedIdx j)),
        pgLp_mem_core (contMode (retainedIdx j))⟩
        = ∑ k : Fin 11, ((fullColumns k j).re : ℂ) • pgLp (contMode k) :=
    fun j => (cont_fullColumns_action j).trans (pgLp_sum_smul _)
  have h2 : (∑ i : Fin 11, (VmatC *ᵥ a) i •
        unitMomCont.innerHam ⟨pgLp (contMode i), pgLp_mem_core (contMode i)⟩) =
      ∑ j : Fin 3, d j • ∑ k : Fin 11,
        ((fullColumns k j).re : ℂ) • pgLp (contMode k) := by
    rw [sum_fin_eleven_eq_sum_three
      (fun i => (VmatC *ᵥ a) i •
        unitMomCont.innerHam ⟨pgLp (contMode i), pgLp_mem_core (contMode i)⟩)
      (fun i hi => by
        dsimp only
        rw [VmatC_mulVec_of_three_le a i (by omega)]
        exact zero_smul ℂ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hHj j]
    have hdj : (VmatC *ᵥ a) (retainedIdx j) = d j := by
      rw [hd, VmatC_mulVec_retained]
    rw [hdj]
  have hstep := h1.trans h2
  have hR : synthesize (fullColumnsC *ᵥ d) =
      ∑ k : Fin 11, (∑ j : Fin 3, ((fullColumns k j).re : ℂ) * d j) •
        pgLp (contMode k) := by
    have hdef : synthesize (fullColumnsC *ᵥ d) =
        ∑ k : Fin 11, (fullColumnsC *ᵥ d) k • pgLp (contMode k) := rfl
    rw [hdef]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [fullColumnsC_apply]
  rw [hstep, hR]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- The inner Hamiltonian action on the reconstructed orbit, in the defect form
used by the residual estimate. -/
theorem innerHam_y (s : ℝ) :
    unitMomCont.innerHam (y s) = synthesize (fullColumnsC *ᵥ (basisC *ᵥ c s)) :=
  innerHam_synthesizeC (c s)

/-! ## The full residual of the reconstructed orbit -/

/-- Synthesis of a coefficient vector is additive. -/
theorem synthesize_add (a b : Fin 11 → ℂ) :
    synthesize (a + b) = synthesize a + synthesize b := by
  simp [synthesize, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Synthesis of a coefficient vector is subtractive. -/
theorem synthesize_sub (a b : Fin 11 → ℂ) :
    synthesize (a - b) = synthesize a - synthesize b := by
  simp [synthesize, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- Synthesis of a coefficient vector is complex homogeneous. -/
theorem synthesize_smul (z : ℂ) (a : Fin 11 → ℂ) :
    synthesize (z • a) = z • synthesize a := by
  simp [synthesize, Pi.smul_apply, smul_smul, Finset.smul_sum]

/-- The full defect is `i·V·G − F·B` on the eleven modes. -/
theorem defect_split :
    defect = ((⟨0, 1⟩ : QI)) • (Vmat * generator) - fullColumns * basis := by
  decide +kernel

/-- The complexified defect is `I·V·G − F·B` on the eleven modes. -/
theorem defectC_split :
    defectC = Complex.I • (VmatC * GC) - fullColumnsC * basisC := by
  have hsplit : defect =
      ((⟨0, 1⟩ : QI)) • (Vmat * generator) - fullColumns * basis := defect_split
  rw [defectC, hsplit, sub_eq_add_neg]
  simp only [toCMat_add, toCMat_neg, toCMat_smul, toCMat_mul, GC, VmatC, fullColumnsC, basisC,
    toComplex_ii]
  abel

/-- The exact residual identity: the Stone-generator residual of the
reconstructed orbit is the defect applied to the reduced state. -/
theorem innerHam_residual (s : ℝ) :
    Complex.I • unitMomCont.innerHam (y s) + v s =
      -(Complex.I • synthesize (defectC *ᵥ c s)) := by
  have hw : VmatC *ᵥ c1 s = (VmatC * GC) *ᵥ c s := by
    rw [c1, Matrix.mulVec_mulVec]
  rw [innerHam_y s, show v s = synthesize (VmatC *ᵥ c1 s) from rfl, hw, defectC_split,
    Matrix.sub_mulVec, Matrix.smul_mulVec, synthesize_sub, synthesize_smul, smul_sub]
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, neg_sub, Matrix.mulVec_mulVec, sub_neg_eq_add,
    add_comm]


/-! ## The `2×2` quadratic-form certificate

The defect and transverse Gram forms are compared with the physical Gram form
through an explicit positive-semidefinite `2×2` matrix over `ℚ[i]`, so every
numeric input is a kernel-checked rational computation. -/

theorem normSqC_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    normSqC (A - B) v = normSqC A v - normSqC B v := by
  show (star v ⬝ᵥ ((A - B) *ᵥ v)).re =
    (star v ⬝ᵥ (A *ᵥ v)).re - (star v ⬝ᵥ (B *ᵥ v)).re
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

/-- The quadratic form of a Hermitian `2×2` matrix in components. -/
theorem normSqC_fin_two {M : Matrix (Fin 2) (Fin 2) ℂ} (h : Mᴴ = M) (v : Fin 2 → ℂ) :
    normSqC M v = (M 0 0).re * Complex.normSq (v 0) + (M 1 1).re * Complex.normSq (v 1)
      + 2 * (star (v 0) * M 0 1 * v 1).re := by
  have h10 : M 1 0 = star (M 0 1) := by
    have hh : star (M 0 1) = M 1 0 := by
      have hc := congrFun (congrFun h 1) 0
      simpa [Matrix.conjTranspose_apply] using hc
    exact hh.symm
  have hst : star (star (v 0) * M 0 1 * v 1) = star (v 1) * star (M 0 1) * v 0 := by
    rw [StarMul.star_mul, StarMul.star_mul, star_star]
    ring
  have hzc : (star (v 0) * M 0 1 * v 1 + star (v 1) * star (M 0 1) * v 0).re
      = 2 * (star (v 0) * M 0 1 * v 1).re := by
    rw [← hst, Complex.star_def, Complex.add_conj]
    simp
  have hn0 : star (v 0) * v 0 = ((Complex.normSq (v 0) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
  have hn1 : star (v 1) * v 1 = ((Complex.normSq (v 1) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
  have hsplit : star (v 0) * (M 0 0 * v 0 + M 0 1 * v 1)
        + star (v 1) * (star (M 0 1) * v 0 + M 1 1 * v 1)
      = M 0 0 * (star (v 0) * v 0) + M 1 1 * (star (v 1) * v 1)
        + (star (v 0) * M 0 1 * v 1 + star (v 1) * star (M 0 1) * v 0) := by
    ring
  have hexp : star v ⬝ᵥ (M *ᵥ v) =
      M 0 0 * ((Complex.normSq (v 0) : ℝ) : ℂ) + M 1 1 * ((Complex.normSq (v 1) : ℝ) : ℂ) +
        (star (v 0) * M 0 1 * v 1 + star (v 1) * star (M 0 1) * v 0) := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10, Pi.star_apply]
    rw [hsplit, hn0, hn1]
  have hfin : normSqC M v = (star v ⬝ᵥ (M *ᵥ v)).re := rfl
  have hM0 : (M 0 0 * ((Complex.normSq (v 0) : ℝ) : ℂ)).re
      = (M 0 0).re * Complex.normSq (v 0) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hM1 : (M 1 1 * ((Complex.normSq (v 1) : ℝ) : ℂ)).re
      = (M 1 1).re * Complex.normSq (v 1) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hfin, hexp, Complex.add_re, Complex.add_re, hM0, hM1, hzc]

/-- A Hermitian `2×2` matrix with nonnegative diagonal and nonnegative determinant
has a nonnegative quadratic form. -/
theorem normSqC_fin_two_nonneg {M : Matrix (Fin 2) (Fin 2) ℂ} (h : Mᴴ = M)
    (h00 : 0 ≤ (M 0 0).re) (h11 : 0 ≤ (M 1 1).re)
    (hdet : Complex.normSq (M 0 1) ≤ (M 0 0).re * (M 1 1).re) (v : Fin 2 → ℂ) :
    0 ≤ normSqC M v := by
  rw [normSqC_fin_two h v]
  have habs : |(star (v 0) * M 0 1 * v 1).re| ≤ ‖v 0‖ * ‖M 0 1‖ * ‖v 1‖ := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_star]
  have hb : ‖M 0 1‖ ^ 2 ≤ (M 0 0).re * (M 1 1).re := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hdet
  have hx : ‖v 0‖ ^ 2 = Complex.normSq (v 0) := (Complex.normSq_eq_norm_sq _).symm
  have hy : ‖v 1‖ ^ 2 = Complex.normSq (v 1) := (Complex.normSq_eq_norm_sq _).symm
  have hnn : (0:ℝ) ≤ ‖v 0‖ * ‖M 0 1‖ * ‖v 1‖ := by positivity
  have step1 : ‖M 0 1‖ ^ 2 * ‖v 1‖ ^ 2 ≤ ((M 0 0).re * (M 1 1).re) * ‖v 1‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hb (by positivity)
  have step2 : ‖v 0‖ ^ 2 * (‖M 0 1‖ ^ 2 * ‖v 1‖ ^ 2)
      ≤ ‖v 0‖ ^ 2 * (((M 0 0).re * (M 1 1).re) * ‖v 1‖ ^ 2) :=
    mul_le_mul_of_nonneg_left step1 (by positivity)
  have ht2 : (‖v 0‖ * ‖M 0 1‖ * ‖v 1‖) ^ 2
      ≤ ((M 0 0).re * Complex.normSq (v 0)) * ((M 1 1).re * Complex.normSq (v 1)) := by
    calc (‖v 0‖ * ‖M 0 1‖ * ‖v 1‖) ^ 2
        = ‖v 0‖ ^ 2 * (‖M 0 1‖ ^ 2 * ‖v 1‖ ^ 2) := by ring
      _ ≤ ‖v 0‖ ^ 2 * (((M 0 0).re * (M 1 1).re) * ‖v 1‖ ^ 2) := step2
      _ = ((M 0 0).re * Complex.normSq (v 0)) * ((M 1 1).re * Complex.normSq (v 1)) := by
          rw [hx, hy]
          ring
  have ham : 2 * (‖v 0‖ * ‖M 0 1‖ * ‖v 1‖)
      ≤ (M 0 0).re * Complex.normSq (v 0) + (M 1 1).re * Complex.normSq (v 1) := by
    nlinarith [ht2, hnn, mul_nonneg h00 (Complex.normSq_nonneg (v 0)),
      mul_nonneg h11 (Complex.normSq_nonneg (v 1)),
      sq_nonneg ((M 0 0).re * Complex.normSq (v 0) - (M 1 1).re * Complex.normSq (v 1))]
  linarith [(abs_le.mp habs).1]


theorem toComplex_mk (a b : ℚ) :
    toComplex ((⟨a, b⟩ : QI)) = ((a : ℂ)) + ((b : ℂ)) * Complex.I := rfl

theorem toCMat_apply_re {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    (toCMat A i j).re = (A i j).re := by
  simp [toCMat, toComplex, Complex.add_re, Complex.mul_re]

theorem toCMat_apply_im {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    (toCMat A i j).im = (A i j).im := by
  simp [toCMat, toComplex, Complex.add_im, Complex.mul_im]

def defectBound : QI := ⟨((177 : ℚ) / 10) ^ 2, 0⟩

theorem toComplex_defectBound : toComplex defectBound = (((177 : ℝ) / 10) ^ 2 : ℂ) := by
  simp [defectBound, toComplex]

def defectPSD : Mat 2 2 := defectBound • gram - defectGram

theorem defectGram_hermitian : defectGramᴴ = defectGram := by decide +kernel

theorem defectPSD_hermitian : defectPSDᴴ = defectPSD := by
  rw [defectPSD, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, defectGram_hermitian,
    gram_hermitian, show star defectBound = defectBound from by simp [defectBound]]

theorem defectPSD_00 : 0 ≤ (defectPSD 0 0).re := by decide +kernel
theorem defectPSD_11 : 0 ≤ (defectPSD 1 1).re := by decide +kernel
theorem defectPSD_det :
    (defectPSD 0 1).re ^ 2 + (defectPSD 0 1).im ^ 2
      ≤ (defectPSD 0 0).re * (defectPSD 1 1).re := by decide +kernel

theorem toCMat_defectPSD : toCMat defectPSD
    = ((((177 : ℝ) / 10) ^ 2 : ℂ)) • W2C - toCMat defectGram := by
  rw [defectPSD, sub_eq_add_neg, toCMat_add, toCMat_neg, toCMat_smul, toComplex_defectBound,
    sub_eq_add_neg]
  rfl

theorem normSq_toCMat_apply {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    Complex.normSq (toCMat A i j) = (A i j).re ^ 2 + (A i j).im ^ 2 := by
  rw [Complex.normSq_apply, toCMat_apply_re, toCMat_apply_im]
  ring

theorem toCMat_defectPSD_real :
    toCMat defectPSD = (((177 : ℝ) / 10) ^ 2) • W2C - toCMat defectGram := by
  rw [toCMat_defectPSD, sub_eq_add_neg, sub_eq_add_neg]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Algebra.smul_def]
  norm_num

/-- The defect Gram form is dominated by the physical Gram form. -/
theorem normSqC_defectGram_le (v : Fin 2 → ℂ) :
    normSqC (toCMat defectGram) v ≤ (177 / 10 : ℝ) ^ 2 * normSqC W2C v := by
  have hHer : (toCMat defectPSD)ᴴ = toCMat defectPSD :=
    toCMat_hermitian defectPSD defectPSD_hermitian
  have h00 : 0 ≤ (toCMat defectPSD 0 0).re := by
    rw [toCMat_apply_re]
    exact_mod_cast defectPSD_00
  have h11 : 0 ≤ (toCMat defectPSD 1 1).re := by
    rw [toCMat_apply_re]
    exact_mod_cast defectPSD_11
  have hdet : Complex.normSq (toCMat defectPSD 0 1)
      ≤ (toCMat defectPSD 0 0).re * (toCMat defectPSD 1 1).re := by
    rw [normSq_toCMat_apply, toCMat_apply_re, toCMat_apply_re]
    exact_mod_cast defectPSD_det
  have hnn := normSqC_fin_two_nonneg hHer h00 h11 hdet v
  rw [toCMat_defectPSD_real, normSqC_sub, normSqC_smul] at hnn
  linarith


/-! ## The reduced orbit rates

The speed and acceleration Gram forms of the reduced generator, together with
their exact values on the seed `e₀`.  Every numeric bound is a kernel-checked
rational computation. -/

/-- The speed Gram of the reduced generator. -/
def speedMat : Mat 2 2 := generator.conjTranspose * gram * generator

/-- The acceleration Gram of the reduced generator. -/
def accMat : Mat 2 2 :=
  (generator.conjTranspose * generator.conjTranspose) * gram * (generator * generator)

theorem toCMat_speedMat : toCMat speedMat = GCᴴ * W2C * GC := by
  show toCMat (generator.conjTranspose * gram * generator)
    = (toCMat generator)ᴴ * toCMat gram * toCMat generator
  rw [← toCMat_conjTranspose, ← toCMat_mul, ← toCMat_mul]

theorem toCMat_accMat : toCMat accMat = (GC * GC)ᴴ * W2C * (GC * GC) := by
  show toCMat ((generator.conjTranspose * generator.conjTranspose) * gram
      * (generator * generator))
    = (toCMat generator * toCMat generator)ᴴ * toCMat gram
      * (toCMat generator * toCMat generator)
  rw [Matrix.conjTranspose_mul, ← toCMat_conjTranspose,
    ← toCMat_mul, ← toCMat_mul, ← toCMat_mul, ← toCMat_mul]

/-- The Gram form of the reduced velocity. -/
theorem normSqC_speedMat (v : Fin 2 → ℂ) :
    normSqC W2C (GC *ᵥ v) = normSqC (toCMat speedMat) v := by
  rw [← normSqC_mulVec GC W2C v, toCMat_speedMat]

/-- The Gram form of the reduced acceleration. -/
theorem normSqC_accMat (v : Fin 2 → ℂ) :
    normSqC W2C (GC *ᵥ (GC *ᵥ v)) = normSqC (toCMat accMat) v := by
  rw [Matrix.mulVec_mulVec, ← normSqC_mulVec (GC * GC) W2C v, toCMat_accMat]

/-- The Gram form of the seed is the top-left entry. -/
theorem normSqC_e0_eq (M : Matrix (Fin 2) (Fin 2) ℂ) : normSqC M e0 = (M 0 0).re := by
  simp [normSqC, dot, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

theorem c1_zero : c1 0 = GC *ᵥ e0 := by
  rw [c1, c_zero]

theorem c2_zero : c2 0 = GC *ᵥ (GC *ᵥ e0) := by
  rw [c2, c1_zero]

theorem speedMat_rate : ((speedMat 0 0).re : ℝ) ≤ (401 / 100 : ℝ) ^ 2 := by
  have h : (speedMat 0 0).re ≤ ((401 : ℚ) / 100) ^ 2 := by decide +kernel
  have h2 : (((speedMat 0 0).re : ℚ) : ℝ) ≤ ((((401 : ℚ) / 100) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast h
  have h3 : ((((401 : ℚ) / 100) ^ 2 : ℚ) : ℝ) = (401 / 100 : ℝ) ^ 2 := by
    push_cast
    ring
  linarith [h2, h3]

theorem accMat_rate : ((accMat 0 0).re : ℝ) ≤ (542 / 10 : ℝ) ^ 2 := by
  have h : (accMat 0 0).re ≤ ((542 : ℚ) / 10) ^ 2 := by decide +kernel
  have h2 : (((accMat 0 0).re : ℚ) : ℝ) ≤ ((((542 : ℚ) / 10) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast h
  have h3 : ((((542 : ℚ) / 10) ^ 2 : ℚ) : ℝ) = (542 / 10 : ℝ) ^ 2 := by
    push_cast
    ring
  linarith [h2, h3]

/-- The seed speed is below `(401/100)²`. -/
theorem speed_rate : normSqC W2C (c1 0) ≤ (401 / 100 : ℝ) ^ 2 := by
  rw [c1_zero, normSqC_speedMat, normSqC_e0_eq, toCMat_apply_re]
  exact speedMat_rate

/-- The seed acceleration is below `(542/10)²`. -/
theorem accel_rate : normSqC W2C (c2 0) ≤ (542 / 10 : ℝ) ^ 2 := by
  rw [c2_zero, normSqC_accMat, normSqC_e0_eq, toCMat_apply_re]
  exact accMat_rate


/-! ## The affine residual envelope -/

/-- The defect residual of the seed. -/
theorem norm_synthesize_defectC_e0 :
    ‖synthesize (defectC *ᵥ e0)‖ ≤ (23 / 10) * ‖pgLp (d := 4) 1‖ := by
  have hsq : ‖synthesize (defectC *ᵥ e0)‖ ^ 2
      ≤ ((23 / 10) * ‖pgLp (d := 4) 1‖) ^ 2 := by
    rw [norm_synthesize_sq, ← norm_pgLp_one_sq, ← normSqC_defectC]
    calc ‖pgLp (d := 4) 1‖ ^ 2 * normSqC (toCMat defectGram) e0
        ≤ ‖pgLp (d := 4) 1‖ ^ 2 * (23 / 10) ^ 2 :=
          mul_le_mul_of_nonneg_left defect_rate_e0 (sq_nonneg _)
      _ = ((23 / 10) * ‖pgLp (d := 4) 1‖) ^ 2 := by ring
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h

/-- The defect residual of any state whose `W₂` form is below `(401/100)²`. -/
theorem norm_synthesize_defectC_le (v : Fin 2 → ℂ)
    (hv : normSqC W2C v ≤ (401 / 100 : ℝ) ^ 2) :
    ‖synthesize (defectC *ᵥ v)‖ ≤ (177 / 10) * (401 / 100) * ‖pgLp (d := 4) 1‖ := by
  have hsq : ‖synthesize (defectC *ᵥ v)‖ ^ 2
      ≤ ((177 / 10) * (401 / 100) * ‖pgLp (d := 4) 1‖) ^ 2 := by
    rw [norm_synthesize_sq, ← norm_pgLp_one_sq, ← normSqC_defectC]
    calc ‖pgLp (d := 4) 1‖ ^ 2 * normSqC (toCMat defectGram) v
        ≤ ‖pgLp (d := 4) 1‖ ^ 2 * ((177 / 10) ^ 2 * normSqC W2C v) :=
          mul_le_mul_of_nonneg_left (normSqC_defectGram_le v) (sq_nonneg _)
      _ ≤ ‖pgLp (d := 4) 1‖ ^ 2 * ((177 / 10) ^ 2 * (401 / 100 : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hv (sq_nonneg _)
      _ = ((177 / 10) * (401 / 100) * ‖pgLp (d := 4) 1‖) ^ 2 := by ring
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h

/-- The affine envelope of the Stone-generator residual of the reconstructed orbit. -/
theorem residual_bound {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.I • unitMomCont.innerHam (y s) + v s‖
      ≤ (23 / 10 + (177 / 10) * (401 / 100) * s) * ‖pgLp (d := 4) 1‖ := by
  rw [innerHam_residual, norm_neg, norm_smul, Complex.norm_I, one_mul]
  have hder : ∀ u : ℝ, HasDerivAt (fun t => synthesize (defectC *ᵥ c t))
      (synthesize (defectC *ᵥ c1 u)) u := fun u =>
    hasDerivAt_synthesize (HasDerivAt.const_mulVec defectC (hasDerivAt_c u))
  have hcont : ContinuousOn (fun t => synthesize (defectC *ᵥ c t)) (Set.Icc 0 s) :=
    fun u _ => (hder u).continuousAt.continuousWithinAt
  have hBder : ∀ u : ℝ, HasDerivAt
      (fun t : ℝ => (23 / 10 + (177 / 10) * (401 / 100) * t) * ‖pgLp (d := 4) 1‖)
      ((177 / 10) * (401 / 100) * ‖pgLp (d := 4) 1‖) u := by
    intro u
    have h1 : HasDerivAt (fun t : ℝ => 23 / 10 + ((177 / 10) * (401 / 100)) * t)
        ((177 / 10) * (401 / 100)) u := by
      simpa using ((hasDerivAt_id u).const_mul ((177 / 10) * (401 / 100))).const_add (23 / 10)
    exact h1.mul_const _
  have h0 : ‖synthesize (defectC *ᵥ c 0)‖
      ≤ (23 / 10 + (177 / 10) * (401 / 100) * 0) * ‖pgLp (d := 4) 1‖ := by
    rw [c_zero]
    simpa using norm_synthesize_defectC_e0
  have hbd : ∀ u ∈ Set.Ico (0 : ℝ) s,
      ‖synthesize (defectC *ᵥ c1 u)‖ ≤ (177 / 10) * (401 / 100) * ‖pgLp (d := 4) 1‖ := by
    intro u hu
    exact norm_synthesize_defectC_le _ (le_trans (cont_orbit_contractive1 hu.1) speed_rate)
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (fun u _ => (hder u).hasDerivWithinAt) h0 hBder hbd (Set.right_mem_Icc.mpr hs)

open BookProof.ChapterStoneResolvent BookProof.EsaClosure in
/-- State error of the reconstructed orbit against the exact Stone flow at `t = 1/100`. -/
theorem state_error_bound {T : UnboundedSelfAdjoint (L2d 4)}
    (hext : IsSelfAdjointExtension unitMomCont.innerHam T.op) :
    ‖(y (1 / 100) : L2d 4) - T.stoneU (1 / 100) (y 0)‖
      ≤ (530977 / 20000000) * ‖pgLp (d := 4) 1‖ := by
  have h := Model.orbit_error unitMomCont hext y v hasDerivAt_y
    ((23 / 10) * ‖pgLp (d := 4) 1‖) ((177 / 10) * (401 / 100) * ‖pgLp (d := 4) 1‖)
    (1 / 100) (by norm_num) (by
      intro u hu
      have hr := residual_bound hu.1
      refine hr.trans_eq ?_
      ring)
  refine h.trans_eq ?_
  ring


/-! ## The transverse Gram certificate -/

/-- The diagonal mode projector that removes the seed mode `0`. -/
def seedProj : Mat 11 11 :=
  fun i j => if (i : ℕ) = 0 then (0 : QI) else if i = j then 1 else 0

/-- The transverse Gram form on the reduced coordinates. -/
def transvMat : Mat 2 2 :=
  (seedProj * Vmat).conjTranspose * fullMetric * (seedProj * Vmat)

/-- The transverse speed Gram of the reduced generator. -/
def transvSpeedMat : Mat 2 2 := generator.conjTranspose * transvMat * generator

theorem toCMat_transvMat : toCMat transvMat
    = (toCMat (seedProj * Vmat))ᴴ * toCMat fullMetric * toCMat (seedProj * Vmat) := by
  show toCMat ((seedProj * Vmat).conjTranspose * fullMetric * (seedProj * Vmat)) = _
  rw [toCMat_mul, toCMat_mul, toCMat_conjTranspose]

/-- The transverse form of a reduced state is the `fullMetric` form of the
projected eleven-mode coefficients. -/
theorem normSqC_transvMat (v : Fin 2 → ℂ) :
    normSqC (toCMat transvMat) v
      = normSqC (toCMat fullMetric) (toCMat (seedProj * Vmat) *ᵥ v) := by
  rw [toCMat_transvMat, normSqC_mulVec]

theorem transvMat_hermitian : transvMatᴴ = transvMat := by decide +kernel

/-- The transverse form is dominated by the physical Gram form. -/
def transvPSD : Mat 2 2 := gram - transvMat

theorem transvPSD_hermitian : transvPSDᴴ = transvPSD := by
  rw [transvPSD, Matrix.conjTranspose_sub, gram_hermitian, transvMat_hermitian]

theorem transvPSD_00 : 0 ≤ (transvPSD 0 0).re := by decide +kernel
theorem transvPSD_11 : 0 ≤ (transvPSD 1 1).re := by decide +kernel
theorem transvPSD_det :
    (transvPSD 0 1).re ^ 2 + (transvPSD 0 1).im ^ 2
      ≤ (transvPSD 0 0).re * (transvPSD 1 1).re := by decide +kernel

theorem toCMat_transvPSD : toCMat transvPSD = W2C - toCMat transvMat := by
  rw [transvPSD, sub_eq_add_neg, toCMat_add, toCMat_neg, sub_eq_add_neg]
  rfl

/-- The transverse Gram form is bounded by the physical Gram form. -/
theorem normSqC_transvMat_le (v : Fin 2 → ℂ) :
    normSqC (toCMat transvMat) v ≤ normSqC W2C v := by
  have hHer : (toCMat transvPSD)ᴴ = toCMat transvPSD :=
    toCMat_hermitian transvPSD transvPSD_hermitian
  have h00 : 0 ≤ (toCMat transvPSD 0 0).re := by
    rw [toCMat_apply_re]
    exact_mod_cast transvPSD_00
  have h11 : 0 ≤ (toCMat transvPSD 1 1).re := by
    rw [toCMat_apply_re]
    exact_mod_cast transvPSD_11
  have hdet : Complex.normSq (toCMat transvPSD 0 1)
      ≤ (toCMat transvPSD 0 0).re * (toCMat transvPSD 1 1).re := by
    rw [normSq_toCMat_apply, toCMat_apply_re, toCMat_apply_re]
    exact_mod_cast transvPSD_det
  have hnn := normSqC_fin_two_nonneg hHer h00 h11 hdet v
  rw [toCMat_transvPSD, normSqC_sub] at hnn
  linarith

/-- The transverse speed form of a reduced state. -/
theorem normSqC_transvSpeedMat (v : Fin 2 → ℂ) :
    normSqC (toCMat transvSpeedMat) v = normSqC (toCMat transvMat) (GC *ᵥ v) := by
  rw [transvSpeedMat, toCMat_mul, toCMat_mul, toCMat_conjTranspose, normSqC_mulVec]
  rfl

/-- The transverse speed Gram is dominated by the physical Gram form. -/
theorem normSqC_transvSpeed_le (v : Fin 2 → ℂ) :
    normSqC (toCMat transvSpeedMat) v ≤ normSqC W2C (GC *ᵥ v) := by
  rw [normSqC_transvSpeedMat]
  exact normSqC_transvMat_le _

/-- The transverse seed speed is at least `(343/100)²`. -/
theorem transvSpeedMat_rate : ((343 : ℚ) / 100) ^ 2 ≤ (transvSpeedMat 0 0).re := by
  decide +kernel


/-! ## The transverse orbit and its Taylor lower bound -/

/-- The transverse synthesis: the seed mode is removed from the eleven modes. -/
noncomputable def zvec (v : Fin 2 → ℂ) : L2d 4 :=
  synthesize (toCMat (seedProj * Vmat) *ᵥ v)

/-- The transverse component of the reconstructed orbit. -/
noncomputable def z (s : ℝ) : L2d 4 := zvec (c s)

theorem zvec_norm_sq (v : Fin 2 → ℂ) :
    ‖zvec v‖ ^ 2 = ‖pgLp (d := 4) 1‖ ^ 2 * normSqC (toCMat transvMat) v := by
  rw [zvec, norm_synthesize_sq, norm_pgLp_one_sq, normSqC_transvMat]

theorem z_norm_sq (s : ℝ) :
    ‖z s‖ ^ 2 = ‖pgLp (d := 4) 1‖ ^ 2 * normSqC (toCMat transvMat) (c s) :=
  zvec_norm_sq (c s)

theorem hasDerivAt_z (s : ℝ) : HasDerivAt z (zvec (c1 s)) s :=
  hasDerivAt_synthesize
    (HasDerivAt.const_mulVec (toCMat (seedProj * Vmat)) (hasDerivAt_c s))

theorem hasDerivAt_zvec_c1 (s : ℝ) :
    HasDerivAt (fun u => zvec (c1 u)) (zvec (c2 s)) s :=
  hasDerivAt_synthesize
    (HasDerivAt.const_mulVec (toCMat (seedProj * Vmat)) (hasDerivAt_c1 s))

theorem seedProj_Vmat_zero (i : Fin 11) : (seedProj * Vmat) i 0 = 0 := by
  revert i
  decide +kernel

theorem toCMat_seedProjVmat_e0 : toCMat (seedProj * Vmat) *ᵥ e0 = 0 := by
  funext i
  show (∑ j : Fin 2, toCMat (seedProj * Vmat) i j * e0 j) = 0
  rw [Fin.sum_univ_two]
  simp only [e0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero,
    add_zero, toCMat, Matrix.map_apply, seedProj_Vmat_zero i, map_zero]

theorem z_zero : z 0 = 0 := by
  show synthesize (toCMat (seedProj * Vmat) *ᵥ c 0) = 0
  rw [c_zero, toCMat_seedProjVmat_e0]
  simp [synthesize]

theorem transv_speed_rate :
    ((343 : ℝ) / 100) ^ 2 ≤ ((transvSpeedMat 0 0).re : ℝ) := by
  have h : ((343 : ℚ) / 100) ^ 2 ≤ (transvSpeedMat 0 0).re := transvSpeedMat_rate
  have h2 : ((((343 : ℚ) / 100) ^ 2 : ℚ) : ℝ) ≤ (((transvSpeedMat 0 0).re : ℚ) : ℝ) := by
    exact_mod_cast h
  have h3 : ((((343 : ℚ) / 100) ^ 2 : ℚ) : ℝ) = (343 / 100 : ℝ) ^ 2 := by
    push_cast
    ring
  linarith [h2, h3]

/-- The transverse seed speed is at least `(343/100)‖pgLp 1‖`. -/
theorem z_deriv_lower :
    (343 / 100 : ℝ) * ‖pgLp (d := 4) 1‖ ≤ ‖zvec (c1 0)‖ := by
  have hval : normSqC (toCMat transvMat) (c1 0) = ((transvSpeedMat 0 0).re : ℝ) := by
    rw [c1_zero, ← normSqC_transvSpeedMat, normSqC_e0_eq, toCMat_apply_re]
  have hsq : ((343 / 100 : ℝ) * ‖pgLp (d := 4) 1‖) ^ 2 ≤ ‖zvec (c1 0)‖ ^ 2 := by
    rw [zvec_norm_sq, hval]
    calc ((343 / 100 : ℝ) * ‖pgLp (d := 4) 1‖) ^ 2
        = (343 / 100 : ℝ) ^ 2 * ‖pgLp (d := 4) 1‖ ^ 2 := by ring
      _ ≤ ((transvSpeedMat 0 0).re : ℝ) * ‖pgLp (d := 4) 1‖ ^ 2 :=
          mul_le_mul_of_nonneg_right transv_speed_rate (sq_nonneg _)
      _ = ‖pgLp (d := 4) 1‖ ^ 2 * ((transvSpeedMat 0 0).re : ℝ) := by ring
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (by positivity), abs_of_nonneg (norm_nonneg _)] at h

/-- The transverse acceleration is bounded by `(542/10)‖pgLp 1‖`. -/
theorem z_deriv2_bound {s : ℝ} (hs : 0 ≤ s) :
    ‖zvec (c2 s)‖ ≤ (542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖ := by
  have hsq : ‖zvec (c2 s)‖ ^ 2 ≤ ((542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖) ^ 2 := by
    rw [zvec_norm_sq]
    calc ‖pgLp (d := 4) 1‖ ^ 2 * normSqC (toCMat transvMat) (c2 s)
        ≤ ‖pgLp (d := 4) 1‖ ^ 2 * normSqC W2C (c2 s) :=
          mul_le_mul_of_nonneg_left (normSqC_transvMat_le _) (sq_nonneg _)
      _ ≤ ‖pgLp (d := 4) 1‖ ^ 2 * (542 / 10 : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact le_trans (cont_orbit_contractive2 hs) accel_rate
      _ = ((542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖) ^ 2 := by ring
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h

/-- The transverse velocity stays within `(542/10)‖pgLp 1‖ · s` of its seed value. -/
theorem z_velocity_lipschitz {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc 0 t) :
    ‖zvec (c1 s) - zvec (c1 0)‖ ≤ ((542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖) * s := by
  have hcont : ContinuousOn (fun u => zvec (c1 u) - zvec (c1 0)) (Set.Icc 0 t) :=
    fun u _ => ((hasDerivAt_zvec_c1 u).sub_const _).continuousAt.continuousWithinAt
  have hB : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => ((542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖) * v)
      ((542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖) u := by
    intro u
    simpa using (hasDerivAt_id u).const_mul ((542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖)
  have h0 : ‖(fun u => zvec (c1 u) - zvec (c1 0)) 0‖
      ≤ ((542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖) * 0 := by
    simp
  have hbd : ∀ u ∈ Set.Ico (0 : ℝ) t,
      ‖zvec (c2 u)‖ ≤ (542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖ := by
    intro u hu
    exact z_deriv2_bound hu.1
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (fun u _ => ((hasDerivAt_zvec_c1 u).sub_const _).hasDerivWithinAt) h0 hB hbd hs

/-- Taylor lower bound for the transverse displacement at `t = 1/100`. -/
theorem z_transverse_lower :
    (3159 / 100000 : ℝ) * ‖pgLp (d := 4) 1‖ ≤ ‖z (1 / 100)‖ := by
  have ht : (0:ℝ) ≤ 1 / 100 := by norm_num
  set M : ℝ := (542 / 10 : ℝ) * ‖pgLp (d := 4) 1‖ with hM
  -- second-order remainder bound
  have hcont : ContinuousOn (fun u => z u - z 0 - u • zvec (c1 0)) (Set.Icc 0 (1/100)) :=
    fun u _ => (((hasDerivAt_z u).sub_const _).sub
      ((hasDerivAt_id u).smul_const _)).continuousAt.continuousWithinAt
  have hder : ∀ u : ℝ, HasDerivAt (fun v : ℝ => z v - z 0 - v • zvec (c1 0))
      (zvec (c1 u) - zvec (c1 0)) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => z v - z 0) (zvec (c1 u)) u :=
      (hasDerivAt_z u).sub_const _
    have h2 : HasDerivAt (fun v : ℝ => v • zvec (c1 0)) (zvec (c1 0)) u := by
      simpa using (hasDerivAt_id u).smul_const (zvec (c1 0))
    have := h1.sub h2
    simpa using this
  have hB : ∀ u : ℝ, HasDerivAt (fun v : ℝ => M * v ^ 2 / 2) (M * u) u := by
    intro u
    have h := (((hasDerivAt_id u).pow 2).const_mul M).div_const 2
    have h' : HasDerivAt (fun v : ℝ => M * v ^ 2 / 2) (M * (2 * u) / 2) u := by
      simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using h
    convert h' using 1
    ring
  have h0 : ‖(fun u => z u - z 0 - u • zvec (c1 0)) 0‖ ≤ M * 0 ^ 2 / 2 := by
    simp [z_zero]
  have hbd : ∀ u ∈ Set.Ico (0 : ℝ) (1/100),
      ‖zvec (c1 u) - zvec (c1 0)‖ ≤ M * u := by
    intro u hu
    exact z_velocity_lipschitz ht (Set.mem_Icc.mpr ⟨hu.1, le_of_lt hu.2⟩)
  have hrem := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (fun u _ => (hder u).hasDerivWithinAt) h0 hB hbd (Set.right_mem_Icc.mpr ht)
  -- lower bound from the triangle inequality
  have hrem' : ‖z (1/100) - (1/100 : ℝ) • zvec (c1 0)‖ ≤ M * (1/100) ^ 2 / 2 := by
    simpa [z_zero] using hrem
  have htri : (1/100 : ℝ) * ‖zvec (c1 0)‖ - M * (1/100) ^ 2 / 2 ≤ ‖z (1/100)‖ := by
    have h := norm_sub_le (z (1/100)) (z (1/100) - (1/100 : ℝ) • zvec (c1 0))
    have he : z (1/100) - (z (1/100) - (1/100 : ℝ) • zvec (c1 0))
        = (1/100 : ℝ) • zvec (c1 0) := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/100)] at h
    linarith
  have hstep : (343 / 100 : ℝ) * ‖pgLp (d := 4) 1‖ ≤ ‖zvec (c1 0)‖ := z_deriv_lower
  have hexp : (1/100 : ℝ) * ((343 / 100 : ℝ) * ‖pgLp (d := 4) 1‖)
      - M * (1/100) ^ 2 / 2 = (3159 / 100000 : ℝ) * ‖pgLp (d := 4) 1‖ := by
    rw [hM]
    ring
  nlinarith [htri, hstep, hexp,
    mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 1/100)]


/-! ## Orthogonal decomposition with respect to the Gaussian seed -/

/-- The Gaussian seed is nonzero. -/
theorem norm_pgLp_one_pos : 0 < ‖pgLp (d := 4) 1‖ := by
  have h : ‖pgLp (d := 4) 1‖ ^ 2 = (Real.sqrt (2 * Real.pi)) ^ 4 := norm_pgLp_one_sq
  have hpos : (0 : ℝ) < (Real.sqrt (2 * Real.pi)) ^ 4 := by positivity
  nlinarith [norm_nonneg (pgLp (d := 4) 1 : L2d 4)]

/-- The rank-one projection onto the Gaussian seed. -/
noncomputable def projE (w : L2d 4) : L2d 4 :=
  (inner ℂ (pgLp (d := 4) 1) w / ((‖pgLp (d := 4) 1‖ : ℂ) ^ 2)) • pgLp (d := 4) 1

/-- The part of a state orthogonal to the Gaussian seed. -/
noncomputable def orthE (w : L2d 4) : L2d 4 := w - projE w

theorem inner_pgLp_self :
    inner ℂ (pgLp (d := 4) 1) (pgLp (d := 4) 1) = (‖pgLp (d := 4) 1‖ : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K _

theorem norm_pgLp_one_sq_coe :
    ((‖pgLp (d := 4) 1‖ : ℂ)) ^ 2 = ((Real.sqrt (2 * Real.pi)) ^ 4 : ℂ) := by
  rw [← Complex.ofReal_pow, norm_pgLp_one_sq, Complex.ofReal_pow]

theorem inner_pgLp_projE (w : L2d 4) :
    inner ℂ (pgLp (d := 4) 1) (projE w) = inner ℂ (pgLp (d := 4) 1) w := by
  rw [projE, inner_smul_right, inner_pgLp_self]
  have hpos := norm_pgLp_one_pos
  have hz : (‖pgLp (d := 4) 1‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  have hne : (‖pgLp (d := 4) 1‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  field_simp

theorem inner_pgLp_orthE (w : L2d 4) :
    inner ℂ (pgLp (d := 4) 1) (orthE w) = 0 := by
  rw [orthE, inner_sub_right, inner_pgLp_projE, sub_self]

theorem inner_projE_orthE (w : L2d 4) : inner ℂ (projE w) (orthE w) = 0 := by
  rw [projE, inner_smul_left, inner_pgLp_orthE, mul_zero]

/-- Pythagorean decomposition along the Gaussian seed. -/
theorem pyth (w : L2d 4) : ‖orthE w‖ ^ 2 + ‖projE w‖ ^ 2 = ‖w‖ ^ 2 := by
  have hsplit : projE w + orthE w = w := by
    show projE w + (w - projE w) = w
    abel
  have h := norm_add_sq (𝕜 := ℂ) (projE w) (orthE w)
  rw [inner_projE_orthE] at h
  simp only [map_zero, mul_zero, add_zero] at h
  rw [hsplit] at h
  linarith

theorem projE_norm_sq (w : L2d 4) :
    ‖projE w‖ ^ 2 = ‖inner ℂ (pgLp (d := 4) 1) w‖ ^ 2 / ‖pgLp (d := 4) 1‖ ^ 2 := by
  rw [projE, norm_smul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos norm_pgLp_one_pos]
  have hne : ‖pgLp (d := 4) 1‖ ^ 2 ≠ 0 := by
    have h := norm_pgLp_one_pos
    positivity
  field_simp

/-- The squared seed overlap in terms of the orthogonal defect. -/
theorem inner_pgLp_norm_sq (w : L2d 4) :
    ‖inner ℂ (pgLp (d := 4) 1) w‖ ^ 2
      = ‖pgLp (d := 4) 1‖ ^ 2 * (‖w‖ ^ 2 - ‖orthE w‖ ^ 2) := by
  have hp := pyth w
  have hc := projE_norm_sq w
  have hne : ‖pgLp (d := 4) 1‖ ≠ 0 := ne_of_gt norm_pgLp_one_pos
  have key : ‖projE w‖ ^ 2 = ‖w‖ ^ 2 - ‖orthE w‖ ^ 2 := by linarith
  have h1 : ‖inner ℂ (pgLp (d := 4) 1) w‖ ^ 2
      = ‖projE w‖ ^ 2 * ‖pgLp (d := 4) 1‖ ^ 2 := by
    rw [hc]
    field_simp
  rw [h1, key]
  ring

theorem orthE_add (a b : L2d 4) : orthE (a + b) = orthE a + orthE b := by
  rw [orthE, orthE, orthE, projE, projE, projE, inner_add_right, add_div, add_smul,
    add_sub_add_comm]

theorem orthE_norm_le (w : L2d 4) : ‖orthE w‖ ≤ ‖w‖ := by
  have hp := pyth w
  have h2 : ‖orthE w‖ ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [hp, sq_nonneg ‖projE w‖]
  have h := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h

/-! ## The transverse identity and the two-sided return interval -/

/-- The seed mode coefficient vector. -/
def seedVec : Fin 11 → ℂ := Pi.single (0 : Fin 11) 1

theorem synthesize_seedVec : synthesize seedVec = pgLp (d := 4) 1 := by
  simp [synthesize, seedVec, contMode]

/-- The seed overlap of an eleven-mode synthesis. -/
theorem inner_pgLp_synthesize (w : Fin 11 → ℂ) :
    inner ℂ (pgLp (d := 4) 1) (synthesize w) =
      w 0 * ((Real.sqrt (2 * Real.pi)) ^ 4 : ℂ) := by
  have h := synthesis_inner seedVec w
  rw [synthesize_seedVec] at h
  have hrow : ∀ j : Fin 11, ((fullMetric (0 : Fin 11) j).re : ℂ) =
      if j = 0 then 1 else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp [fullMetric]
    · have hz : (fullMetric (0 : Fin 11) j).re = 0 := by
        revert j
        decide +kernel
      rw [hz]
      simp [hj]
  have hsum : (∑ i, ∑ j, (starRingEnd ℂ) (seedVec i) *
      ((fullMetric i j).re : ℂ) * w j) = w 0 := by
    have h0 : seedVec (0 : Fin 11) = 1 := by simp [seedVec]
    rw [Finset.sum_eq_single (0 : Fin 11)]
    · rw [Finset.sum_eq_single (0 : Fin 11)]
      · rw [h0, map_one, one_mul, hrow 0]
        simp
      · intro j _ hj
        rw [hrow j]
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      have hz : seedVec i = 0 := by
        rw [seedVec, Pi.single_eq_of_ne hi]
      simp [hz]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum] at h
  exact h

theorem seedProj_Vmat_row_zero (j : Fin 2) : (seedProj * Vmat) (0 : Fin 11) j = 0 := by
  revert j
  decide +kernel

theorem seedProj_Vmat_of_ne (i : Fin 11) (j : Fin 2) (hi : i ≠ 0) :
    (seedProj * Vmat) i j = Vmat i j := by
  revert j i
  decide +kernel

/-- The projected coefficient vector is the full one with the seed mode removed. -/
theorem seedProj_Vmat_mulVec (x : Fin 2 → ℂ) :
    toCMat (seedProj * Vmat) *ᵥ x = VmatC *ᵥ x - ((VmatC *ᵥ x) 0) • seedVec := by
  funext i
  by_cases hi : i = 0
  · subst hi
    have hz : ∀ j, toCMat (seedProj * Vmat) (0 : Fin 11) j = 0 := by
      intro j
      show toComplex ((seedProj * Vmat) (0 : Fin 11) j) = 0
      rw [seedProj_Vmat_row_zero j, map_zero]
    simp [Matrix.mulVec, dotProduct, hz, VmatC, Pi.sub_apply, Pi.smul_apply, seedVec]
  · have hrow : ∀ j, toCMat (seedProj * Vmat) i j = toCMat Vmat i j := by
      intro j
      show toComplex ((seedProj * Vmat) i j) = toComplex (Vmat i j)
      rw [seedProj_Vmat_of_ne i j hi]
    have hs : seedVec i = 0 := by
      rw [seedVec, Pi.single_eq_of_ne hi]
    simp [Matrix.mulVec, dotProduct, hrow, VmatC, Pi.sub_apply, Pi.smul_apply, hs]

/-- The orthogonal part of the reconstructed orbit is its transverse component. -/
theorem orthE_y (s : ℝ) : orthE (y s) = z s := by
  have hy : (y s : L2d 4) = synthesize (VmatC *ᵥ c s) := synthesizeC_coe _
  have hne : ((Real.sqrt (2 * Real.pi)) ^ 4 : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < (Real.sqrt (2 * Real.pi)) ^ 4 := by positivity
    exact_mod_cast ne_of_gt h
  rw [hy, orthE, projE, inner_pgLp_synthesize, norm_pgLp_one_sq_coe,
    mul_div_cancel_right₀ _ hne, z, zvec, seedProj_Vmat_mulVec, synthesize_sub,
    synthesize_smul, synthesize_seedVec]

open BookProof.ChapterStoneResolvent BookProof.EsaClosure in
/-- The transverse component of the exact flow is bounded below at `t = 1/100`. -/
theorem orthE_flow_lower {T : UnboundedSelfAdjoint (L2d 4)}
    (hext : IsSelfAdjointExtension unitMomCont.innerHam T.op) :
    (1 / 200 : ℝ) * ‖pgLp (d := 4) 1‖ ≤
      ‖orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1))‖ := by
  have herr := state_error_bound hext
  rw [y_zero] at herr
  have hz := z_transverse_lower
  have hsplit : orthE (y (1 / 100)) +
      orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1) - y (1 / 100)) =
      orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1)) := by
    rw [← orthE_add]
    congr 1
    abel
  have htri : ‖z (1 / 100)‖ ≤ ‖orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1))‖ +
      ‖orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1) - y (1 / 100))‖ := by
    have h := norm_sub_le (orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1)))
      (orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1) - y (1 / 100)))
    have heq : orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1)) -
        orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1) - y (1 / 100)) =
        orthE (y (1 / 100)) := by
      rw [← hsplit]
      abel
    rw [heq, orthE_y] at h
    exact h
  have hcon := orthE_norm_le (T.stoneU (1 / 100) (pgLp (d := 4) 1) - y (1 / 100))
  have herr' : ‖T.stoneU (1 / 100) (pgLp (d := 4) 1) - y (1 / 100)‖
      ≤ (530977 / 20000000) * ‖pgLp (d := 4) 1‖ := by
    rw [norm_sub_rev]
    exact herr
  have h1 : ‖orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1))‖ ≥
      ‖z (1 / 100)‖ - (530977 / 20000000) * ‖pgLp (d := 4) 1‖ :=
    calc ‖orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1))‖
        ≥ ‖z (1 / 100)‖ - ‖orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1) -
            y (1 / 100))‖ := by linarith
      _ ≥ ‖z (1 / 100)‖ - (530977 / 20000000) * ‖pgLp (d := 4) 1‖ := by
          linarith
  have h2 : (100823 / 20000000 : ℝ) * ‖pgLp (d := 4) 1‖
      ≤ ‖orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1))‖ := by
    have he : (3159 / 100000 : ℝ) * ‖pgLp (d := 4) 1‖
        - (530977 / 20000000) * ‖pgLp (d := 4) 1‖
        = (100823 / 20000000 : ℝ) * ‖pgLp (d := 4) 1‖ := by ring
    linarith
  have hnum : (1 / 200 : ℝ) ≤ 100823 / 20000000 := by norm_num
  calc (1 / 200 : ℝ) * ‖pgLp (d := 4) 1‖
      ≤ (100823 / 20000000 : ℝ) * ‖pgLp (d := 4) 1‖ :=
        mul_le_mul_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ ‖orthE (T.stoneU (1 / 100) (pgLp (d := 4) 1))‖ := h2

open BookProof.ChapterStoneResolvent BookProof.EsaClosure in
/-- Two-sided return interval for the continuous-momentum Gaussian seed at `t = 1/100`. -/
theorem unitMomCont_return_interval {T : UnboundedSelfAdjoint (L2d 4)}
    (hext : IsSelfAdjointExtension unitMomCont.innerHam T.op) :
    (319447 / 320000 : ℝ) * ‖pgLp (d := 4) 1‖ ^ 4 ≤
      ‖inner ℂ (pgLp (d := 4) 1) (T.stoneU (1 / 100) (pgLp 1))‖ ^ 2 ∧
    ‖inner ℂ (pgLp (d := 4) 1) (T.stoneU (1 / 100) (pgLp 1))‖ ^ 2 ≤
      (39999 / 40000 : ℝ) * ‖pgLp (d := 4) 1‖ ^ 4 := by
  constructor
  · have h := unitMomCont_return_probability hext (1 / 100)
    have he : (1 - (553 / 32 : ℝ) * (1 / 100) ^ 2) = 319447 / 320000 := by norm_num
    rw [he] at h
    exact h
  · set e : L2d 4 := pgLp (d := 4) 1 with he
    set w : L2d 4 := T.stoneU (1 / 100) e with hw
    have hlow := orthE_flow_lower hext
    rw [← he] at hlow
    have hw_norm : ‖w‖ = ‖e‖ := T.norm_stoneU_apply (1 / 100) e
    have hinner := inner_pgLp_norm_sq w
    rw [← he, hw_norm] at hinner
    have hlow2 : (1 / 40000 : ℝ) * ‖e‖ ^ 2 ≤ ‖orthE w‖ ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (1 / 200) * ‖e‖) hlow 2
      have hexp : ((1 / 200 : ℝ) * ‖e‖) ^ 2 = (1 / 40000 : ℝ) * ‖e‖ ^ 2 := by ring
      linarith [hsq, hexp]
    have hprod : (1 / 40000 : ℝ) * ‖e‖ ^ 4 ≤ ‖e‖ ^ 2 * ‖orthE w‖ ^ 2 := by
      have hsq := mul_le_mul_of_nonneg_left hlow2 (sq_nonneg ‖e‖)
      calc (1 / 40000 : ℝ) * ‖e‖ ^ 4 = ‖e‖ ^ 2 * ((1 / 40000 : ℝ) * ‖e‖ ^ 2) := by ring
        _ ≤ ‖e‖ ^ 2 * ‖orthE w‖ ^ 2 := hsq
    nlinarith [hinner, hprod]

end

end BookProof.Phi4.MomRankTwo
