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

end

end BookProof.Phi4.MomRankTwo
