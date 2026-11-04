import Mathlib
import BookProof.Toolbox.ChapterKvnKatoEsa
import BookProof.ChapterKoopmanLyapunovFarisLavine
import BookProof.Toolbox.ChapterHermiteGraphApprox

/-!
# Essential self-adjointness of `N = H_G² + E` on the Gauss–polynomial core

For a polynomial vector field `G` with real coefficients and a real polynomial `E ≥ 1`, the
comparison operator `N = H_G² + E` of `BookProof.ChapterKoopmanLyapunovFarisLavine`
(`lyapunovComparison G E`) is **essentially self-adjoint on the Gauss–polynomial core**,
provided `G` admits a proper Lyapunov function: a smooth `L ≥ ‖x‖` with `|G·∇L| ≤ c L`.

The proof transfers a deficiency vector of `N` on the Gauss–polynomial core to a weak solution
of `(−X² + E − z̄) u = 0` against compactly supported smooth test functions (by the Hermite
graph approximation of `BookProof.ChapterHermiteGraphApprox`, which applies verbatim to any
polynomial differential operator), and then invokes the Kato argument
`BookProof.KvnKato.eq_zero_of_lyapunov`.
-/

namespace BookProof.KvnKato

open MeasureTheory Filter Topology MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis BookProof.QgOneParticleCc
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.YangMillsHermite
open BookProof.DegEnergy BookProof.DegKatoEsa BookProof.DegSchrodinger BookProof.HermiteLadder
open BookProof.HermiteGraphApprox BookProof.KoopmanLyapunov BookProof.FarisLavine
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Polynomial vector fields as `KvnData` -/

/-- Evaluation of a polynomial at a point of `ℝᵈ`. -/
def pev (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : ℂ :=
  MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p

theorem contDiff_pev (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pev p) := contDiff_polyEval p

theorem pev_real {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (x : Vd d) :
    (starRingEnd ℂ) (pev p x) = pev p x := by
  have hcp : cpoly p = p := hp
  rw [pev, conj_polyEval, hcp]

/-- The coordinate derivative of a polynomial is its partial derivative. -/
theorem dcoord_pev (p : MvPolynomial (Fin d) ℂ) (j : Fin d) (x : Vd d) :
    dcoord j (pev p) x = pev (pderiv j p) x := by
  have h0 := hasDerivAt_polyEval_coordLine p x j (x j)
  have hshift : HasDerivAt (fun t : ℝ => x j + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x j)
  have h0' : HasDerivAt
      (fun s : ℝ => MvPolynomial.eval (fun i => (((coordLine x j s) i : ℝ) : ℂ)) p)
      (pev (pderiv j p) x) (x j + 0) := by
    simpa [coordLine_self_eq, pev] using h0
  have hcomp := HasDerivAt.scomp (0 : ℝ) h0' hshift
  simp only [Function.comp_def, one_smul] at hcomp
  have hfun :
      (fun t : ℝ => MvPolynomial.eval (fun i => (((coordLine x j (x j + t)) i : ℝ) : ℂ)) p)
      = fun t : ℝ => pev p (x + t • kinDir d j) := by
    funext t
    rw [coordLine_add_smul, pev]
  rw [hfun] at hcomp
  have hld : HasLineDerivAt ℝ (pev p) (pev (pderiv j p) x) x (kinDir d j) := by
    simpa [HasLineDerivAt] using hcomp
  have hdiff : DifferentiableAt ℝ (pev p) x :=
    differentiableAt_of_contDiffTop (contDiff_pev p) x
  have hfd : fderiv ℝ (pev p) x (kinDir d j) = pev (pderiv j p) x := by
    rw [← hdiff.lineDeriv_eq_fderiv]
    exact hld.lineDeriv
  simpa [dcoord] using hfd

theorem pev_add (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) : pev (p + q) x = pev p x + pev q x := by
  simp [pev]

theorem pev_mul (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) : pev (p * q) x = pev p x * pev q x := by
  simp [pev]

theorem pev_sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pev (∑ i ∈ s, p i) x = ∑ i ∈ s, pev (p i) x := by
  simp [pev]

/-- The divergence term `½ div G` of a polynomial vector field. -/
def polyDiv (G : Fin d → MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ := ∑ i, pderiv i (G i)

theorem realCoeff_pderiv {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (j : Fin d) :
    RealCoeff (pderiv j p) := by
  have hcp : cpoly p = p := hp
  change cpoly (pderiv j p) = pderiv j p
  rw [cpoly_pderiv, hcp]

theorem realCoeff_polyDiv {G : Fin d → MvPolynomial (Fin d) ℂ} (hG : ∀ i, RealCoeff (G i)) :
    RealCoeff (polyDiv G) := by
  change cpoly (∑ i, pderiv i (G i)) = ∑ i, pderiv i (G i)
  simp only [cpoly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact realCoeff_pderiv (hG i) i

/-- **A real polynomial vector field as `KvnData`.** -/
def polyKvn (G : Fin d → MvPolynomial (Fin d) ℂ) (hG : ∀ i, RealCoeff (G i)) : KvnData d where
  G i := pev (G i)
  c x := (1 / 2 : ℂ) * pev (polyDiv G) x
  G_smooth i := contDiff_pev (G i)
  c_smooth := contDiff_const.mul (contDiff_pev _)
  G_real i x := pev_real (hG i) x
  c_real x := by
    rw [map_mul, pev_real (realCoeff_polyDiv hG) x, map_div₀, map_one, map_ofNat]
  div_eq x := by
    simp only [dcoord_pev, polyDiv, pev_sum]
    ring

/-! ## 2. The comparison operator on functions -/

/-- The polynomial realization of `N = H_G² + E`. -/
def nPoly (G : Fin d → MvPolynomial (Fin d) ℂ) (E : MvPolynomial (Fin d) ℂ) :
    Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  kvnGen G ∘ₗ kvnGen G + mulOp E

theorem lyapunovComparison_eq_pgLp (G : Fin d → MvPolynomial (Fin d) ℂ)
    (E : MvPolynomial (Fin d) ℂ) (x : polyGaussCore (d := d)) :
    lyapunovComparison G E x = pgLp (nPoly G E ((coreRepPoly d).equiv.symm x)) := by
  set p := (coreRepPoly d).equiv.symm x with hp
  have h1 : (kvnGenOp G) (kvnGenCore G x) = pgLp (kvnGen G (kvnGen G p)) := by
    have := (coreRepPoly d).coe_op (kvnGen G) (kvnGenCore G x)
    rw [show (coreRepPoly d).equiv.symm (kvnGenCore G x) = kvnGen G p from
      (coreRepPoly d).equiv.symm_apply_apply _] at this
    exact this
  have h2 : mulCoreOp E x = pgLp (E * p) := (coreRepPoly d).coe_op (mulOp E) x
  have h3 : lyapunovComparison G E x = (kvnGenOp G) (kvnGenCore G x) + mulCoreOp E x := rfl
  rw [h3, h1, h2, ← pgLp_add']
  rfl

theorem pgFun_mul_pev (q p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (q * p) x = pev q x * pgFun p x := by
  simp [pgFun, pev, mul_assoc]

theorem pgFun_sum' {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (∑ i ∈ s, p i) x = ∑ i ∈ s, pgFun (p i) x := by
  simp [pgFun, Finset.sum_mul]

theorem derOp_eq_coreD (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : derOp j p = coreD j p := by
  rw [derOp_apply, coreD, smul_eq_C_mul]
  congr 2
  norm_num

/-- **The generator on functions**: `X (p e^{−|x|²/4}) = (i H_G p) e^{−|x|²/4}`. -/
theorem Xf_pgFun (G : Fin d → MvPolynomial (Fin d) ℂ) (hG : ∀ i, RealCoeff (G i))
    (p : MvPolynomial (Fin d) ℂ) :
    Xf (polyKvn G hG) (pgFun p) = pgFun (Complex.I • kvnGen G p) := by
  funext x
  rw [kvnGen_apply, smul_smul, show Complex.I * -Complex.I = 1 by
    rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul, pgFun_add_apply, pgFun_smul_apply,
    pgFun_mul_pev, pgFun_sum', Xf]
  simp only [dcoord_pgFun, pgFun_mul_pev, derOp_eq_coreD, polyKvn, polyDiv]
  push_cast
  ring

/-- **`N` on functions** is the operator `A = −X² + E`. -/
theorem pgFun_nPoly (G : Fin d → MvPolynomial (Fin d) ℂ) (hG : ∀ i, RealCoeff (G i))
    (E p : MvPolynomial (Fin d) ℂ) :
    pgFun (nPoly G E p) = Af (polyKvn G hG) (pev E) (pgFun p) := by
  funext x
  have h2 : Xf (polyKvn G hG) (Xf (polyKvn G hG) (pgFun p))
      = pgFun (Complex.I • kvnGen G (Complex.I • kvnGen G p)) := by
    rw [Xf_pgFun, Xf_pgFun]
  rw [Af, h2, nPoly, LinearMap.add_apply, LinearMap.comp_apply, mulOp_apply, pgFun_add_apply,
    pgFun_mul_pev, map_smul, smul_smul, pgFun_smul_apply, Complex.I_mul_I]
  ring

/-- **Integration by parts for `A`**: `∫ conj(A f) ψ = ∫ conj f · A ψ` for `ψ` compactly
supported. -/
theorem integral_conj_Af (S : KvnData d) {E : Vd d → ℂ}
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) (hEr : ∀ y, (starRingEnd ℂ) (E y) = E y)
    {f ψ : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ y, (starRingEnd ℂ) (Af S E f y) * ψ y = ∫ y, (starRingEnd ℂ) (f y) * Af S E ψ y := by
  set g : Vd d → ℂ := fun y => (starRingEnd ℂ) (f y) with hg
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.contDiff.comp hf
  have hXg := contDiff_Xf S hgs
  have hXXg := contDiff_Xf S hXg
  have hXψ := contDiff_Xf S hψ
  have hXXψ := contDiff_Xf S hXψ
  have e1 : ∀ y, (starRingEnd ℂ) (Af S E f y) * ψ y
      = E y * g y * ψ y - Xf S (Xf S g) y * ψ y := by
    intro y
    rw [Af_conj S hEr hf y, Af]
    ring
  have e2 : ∀ y, (starRingEnd ℂ) (f y) * Af S E ψ y
      = E y * g y * ψ y - g y * Xf S (Xf S ψ) y := by
    intro y
    simp only [Af, hg]
    ring
  have i1 : Integrable (fun y => E y * g y * ψ y) (volume : Measure (Vd d)) :=
    ((hE.continuous.mul hgs.continuous).mul hψ.continuous).integrable_of_hasCompactSupport
      hψc.mul_left
  have i2 : Integrable (fun y => Xf S (Xf S g) y * ψ y) (volume : Measure (Vd d)) :=
    (hXXg.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have i3 : Integrable (fun y => g y * Xf S (Xf S ψ) y) (volume : Measure (Vd d)) :=
    (hgs.continuous.mul hXXψ.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_Xf S (hasCompactSupport_Xf S hψc)).mul_left
  have k1 := integral_mul_Xf' S hXg hψ hψc
  have k2 := integral_mul_Xf' S hgs hXψ (hasCompactSupport_Xf S hψc)
  rw [integral_congr_ae (Filter.Eventually.of_forall e1),
    integral_congr_ae (Filter.Eventually.of_forall e2), integral_sub i1 i2, integral_sub i1 i3]
  congr 1
  linear_combination k1 - k2

/-! ## 3. Ladder order -/

theorem kvnGen_eq_lin (G : Fin d → MvPolynomial (Fin d) ℂ) :
    kvnGen G = (-Complex.I) • ((∑ i, mulL (G i) ∘ₗ coreDL i)
      + ((1 / 2 : ℝ) : ℂ) • mulL (polyDiv G)) := by
  refine LinearMap.ext fun p => ?_
  rw [kvnGen_apply]
  simp [LinearMap.sum_apply, coreDL_apply, derOp_eq_coreD, polyDiv]

theorem exists_ladderOrd_kvnGen (G : Fin d → MvPolynomial (Fin d) ℂ) :
    ∃ n, LadderOrd (kvnGen G) n := by
  choose n hn using fun i => exists_ladderOrd_mulL (G i)
  obtain ⟨n₀, h₀⟩ := exists_ladderOrd_mulL (polyDiv G)
  refine ⟨(∑ i, n i) + 1 + n₀, ?_⟩
  rw [kvnGen_eq_lin]
  refine LadderOrd.smul (LadderOrd.add ?_ ?_) _
  · refine LadderOrd.sum _ fun i _ => ((hn i).comp (ladderOrd_coreDL i)).mono ?_
    have := Finset.single_le_sum (f := n) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  · exact (h₀.mono (by omega)).smul _

theorem exists_ladderOrd_nPoly (G : Fin d → MvPolynomial (Fin d) ℂ) (E : MvPolynomial (Fin d) ℂ) :
    ∃ n, LadderOrd (nPoly G E) n := by
  obtain ⟨n, hn⟩ := exists_ladderOrd_kvnGen G
  obtain ⟨m, hm⟩ := exists_ladderOrd_mulL E
  refine ⟨n + n + m, ?_⟩
  exact ((hn.comp hn).mono (by omega)).add (hm.mono (by omega))

/-! ## 4. Hermite approximation in the graph norm of `N` -/

theorem lyapunovComparison_bound (G : Fin d → MvPolynomial (Fin d) ℂ) (E : MvPolynomial (Fin d) ℂ)
    {n : ℕ} (hT : LadderOrd (nPoly G E) n) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ y : polyGaussCore (d := d),
      ENNReal.ofReal (‖lyapunovComparison G E y‖ ^ 2) ≤ C * hn n (y : L2d d) := by
  obtain ⟨C, hC, h⟩ := hT.norm_sq_le
  refine ⟨C, hC, fun y => ?_⟩
  rw [lyapunovComparison_eq_pgLp, (coreRepPoly d).coe_symm y]
  exact h _

theorem cauchySeq_lyap_truncCore (G : Fin d → MvPolynomial (Fin d) ℂ) (E : MvPolynomial (Fin d) ℂ)
    {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g)
    {v : L2d d} (hv : (v : Vd d → ℂ) =ᵐ[volume] g) :
    CauchySeq (fun F => lyapunovComparison G E (truncCore v F)) := by
  obtain ⟨n, hT⟩ := exists_ladderOrd_nPoly G E
  obtain ⟨C, hC, hbound⟩ := lyapunovComparison_bound G E hT
  have hfin : ∑' b, wt n b * ‖coef b v‖ₑ ^ 2 ≠ ⊤ := hn_ne_top_of_cc hg hgc hv n
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero hfin
  have h2 : Tendsto (fun F : Finset (Fin d →₀ ℕ) =>
      C * ∑' b : {b // b ∉ F}, wt n (b : Fin d →₀ ℕ) * ‖coef (b : Fin d →₀ ℕ) v‖ₑ ^ 2)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul htail (Or.inr hC)
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.1 (h2.eventually (gt_mem_nhds hpos))
  refine ⟨F₀, fun F hF F' hF' => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  have h3 := hbound (truncCore v F - truncCore v F')
  have h4 : hn n ((truncCore v F - truncCore v F' : polyGaussCore (d := d)) : L2d d)
      ≤ ∑' b : {b // b ∉ F₀}, wt n (b : Fin d →₀ ℕ) * ‖coef (b : Fin d →₀ ℕ) v‖ₑ ^ 2 :=
    hn_htrunc_sub_le v n hF hF'
  have h5 := lt_of_le_of_lt (h3.trans (mul_le_mul_right h4 C)) (hF₀ F₀ le_rfl)
  have h6 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 h5
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).1 h6

/-- **Mixed symmetry** between the Gauss–polynomial core and compactly supported functions. -/
theorem inner_lyap_cc (G : Fin d → MvPolynomial (Fin d) ℂ) (hG : ∀ i, RealCoeff (G i))
    {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E)
    {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g)
    {v w : L2d d} (hv : (v : Vd d → ℂ) =ᵐ[volume] g)
    (hw : (w : Vd d → ℂ) =ᵐ[volume] Af (polyKvn G hG) (pev E) g) (y : polyGaussCore (d := d)) :
    (inner ℂ (lyapunovComparison G E y) v : ℂ) = inner ℂ (y : L2d d) w := by
  rw [lyapunovComparison_eq_pgLp, (coreRepPoly d).coe_symm y, inner_pgLp_ae hv, inner_pgLp_ae hw,
    pgFun_nPoly G hG]
  exact integral_conj_Af _ (contDiff_pev E) (pev_real hE) (contDiff_pgFun _) hg hgc

theorem tendsto_lyap_truncCore (G : Fin d → MvPolynomial (Fin d) ℂ) (hG : ∀ i, RealCoeff (G i))
    {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E)
    {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g)
    {v w : L2d d} (hv : (v : Vd d → ℂ) =ᵐ[volume] g)
    (hw : (w : Vd d → ℂ) =ᵐ[volume] Af (polyKvn G hG) (pev E) g) :
    Tendsto (fun F => lyapunovComparison G E (truncCore v F)) atTop (𝓝 w) := by
  obtain ⟨g₀, hg₀⟩ := cauchySeq_tendsto_of_complete (cauchySeq_lyap_truncCore G E hg hgc hv)
  have hid : g₀ = w := by
    refine sub_eq_zero.1 (eq_zero_of_orth_dense polyGaussCore_dense fun y hy => ?_)
    have hlim1 : Tendsto (fun F => (inner ℂ y (lyapunovComparison G E (truncCore v F)) : ℂ))
        atTop (𝓝 (inner ℂ y g₀)) := tendsto_const_nhds.inner hg₀
    have hlim2 : Tendsto (fun F => (inner ℂ y (lyapunovComparison G E (truncCore v F)) : ℂ))
        atTop (𝓝 (inner ℂ (lyapunovComparison G E ⟨y, hy⟩) v)) := by
      have heq : (fun F => (inner ℂ y (lyapunovComparison G E (truncCore v F)) : ℂ))
          = fun F => (inner ℂ (lyapunovComparison G E ⟨y, hy⟩) (htrunc v F) : ℂ) := by
        funext F
        exact (lyapunovComparison_symmetricOn hG hE ⟨y, hy⟩ (truncCore v F)).symm
      rw [heq]
      exact tendsto_const_nhds.inner (tendsto_htrunc _)
    have hval := tendsto_nhds_unique hlim1 hlim2
    rw [inner_sub_right, hval, inner_lyap_cc G hG hE hg hgc hv hw ⟨y, hy⟩]
    exact sub_self _
  rwa [hid] at hg₀

/-! ## 5. Deficiency vectors -/

theorem contDiff_Af (S : KvnData d) {E φ : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Af S E φ) :=
  (contDiff_Xf S (contDiff_Xf S hφ)).neg.add (hE.mul hφ)

theorem hasCompactSupport_Af (S : KvnData d) (E : Vd d → ℂ) {φ : Vd d → ℂ}
    (hφc : HasCompactSupport φ) : HasCompactSupport (Af S E φ) :=
  (hasCompactSupport_Xf S (hasCompactSupport_Xf S hφc)).neg.add hφc.mul_left

theorem Df_cx_poly (G : Fin d → MvPolynomial (Fin d) ℂ) (hG : ∀ i, RealCoeff (G i))
    {L : Vd d → ℝ} (hL : Differentiable ℝ L) (x : Vd d) :
    ‖Df (polyKvn G hG) (cx L) x‖
      = |∑ i, (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (G i)).re
          * fderiv ℝ L x (kinDir d i)| := by
  have h : Df (polyKvn G hG) (cx L) x
      = ((∑ i, (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (G i)).re
          * fderiv ℝ L x (kinDir d i) : ℝ) : ℂ) := by
    simp only [Df, dcoord_cx hL]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hr := pev_real (hG i) x
    exact (Complex.conj_eq_iff_re.1 hr).symm
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- **Deficiency vectors of `N` vanish** at every purely imaginary `z`. -/
theorem lyapunovComparison_deficiency (G : Fin d → MvPolynomial (Fin d) ℂ)
    (hG : ∀ i, RealCoeff (G i)) {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E)
    (hE1 : ∀ y : Vd d, 1 ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re)
    {L : Vd d → ℝ} (hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L) (hLn : ∀ x, ‖x‖ ≤ L x) {c₀ : ℝ}
    (hLf : ∀ x : Vd d, |∑ i, (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (G i)).re
      * fderiv ℝ L x (kinDir d i)| ≤ c₀ * L x)
    {z : ℂ} (hz : z.re = 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (lyapunovComparison G E) z := by
  intro u hu
  set S := polyKvn G hG with hS
  have hweak : ∀ φ : Vd d → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ y, (starRingEnd ℂ) (Af S (pev E) φ y) * (u : Vd d → ℂ) y
        = z * ∫ y, (starRingEnd ℂ) (φ y) * (u : Vd d → ℂ) y := by
    intro φ hφ hφc
    have hm1 := memLp_of_cc' hφ.continuous hφc
    have hm2 := memLp_of_cc' (contDiff_Af S (contDiff_pev E) hφ).continuous
      (hasCompactSupport_Af S (pev E) hφc)
    have ht := tendsto_lyap_truncCore G hG hE hφ hφc hm1.coeFn_toLp hm2.coeFn_toLp
    have h1 : Tendsto (fun F => (inner ℂ (lyapunovComparison G E (truncCore (hm1.toLp φ) F))
        u : ℂ)) atTop (𝓝 (inner ℂ (hm2.toLp _) u)) := ht.inner tendsto_const_nhds
    have h2 : Tendsto (fun F => (inner ℂ (lyapunovComparison G E (truncCore (hm1.toLp φ) F))
        u : ℂ)) atTop (𝓝 (z * inner ℂ (hm1.toLp φ) u)) := by
      have heq : (fun F => (inner ℂ (lyapunovComparison G E (truncCore (hm1.toLp φ) F))
          u : ℂ)) = fun F => z * (inner ℂ (htrunc (hm1.toLp φ) F) u : ℂ) :=
        funext fun F => hu _
      rw [heq]
      exact ((tendsto_htrunc _).inner tendsto_const_nhds).const_mul z
    have h3 := tendsto_nhds_unique h1 h2
    have i1 : (inner ℂ (hm2.toLp _) u : ℂ)
        = ∫ y, (starRingEnd ℂ) (Af S (pev E) φ y) * (u : Vd d → ℂ) y := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hm2.coeFn_toLp] with x hx
      rw [hx, RCLike.inner_apply, mul_comm]
    have i2 : (inner ℂ (hm1.toLp φ) u : ℂ) = ∫ y, (starRingEnd ℂ) (φ y) * (u : Vd d → ℂ) y := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hm1.coeFn_toLp] with x hx
      rw [hx, RCLike.inner_apply, mul_comm]
    rw [← i1, ← i2, h3]
  have hLf' : ∀ x, ‖Df S (cx L) x‖ ≤ c₀ * L x := fun x => by
    rw [hS, Df_cx_poly G hG (hL.differentiable (by simp)) x]
    exact hLf x
  have hzero := eq_zero_of_lyapunov S (contDiff_pev E) (pev_real hE) hE1 (Lp.memLp u)
    (Lp.stronglyMeasurable u) hz hweak hL hLn hLf'
  exact Lp.ext (hzero.trans (Lp.coeFn_zero _ _ _).symm)

/-- **Essential self-adjointness of the Koopman comparison operator** `N = H_G² + E` on the
Gauss–polynomial core, for a real polynomial vector field `G` admitting a proper Lyapunov
function `L` (smooth, `L(x) ≥ ‖x‖`, `|G·∇L| ≤ c₀ L`) and a real polynomial `E ≥ 1`. -/
theorem lyapunovComparison_esa (G : Fin d → MvPolynomial (Fin d) ℂ)
    (hG : ∀ i, RealCoeff (G i)) {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E)
    (hE1 : ∀ y : Vd d, 1 ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re)
    {L : Vd d → ℝ} (hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L) (hLn : ∀ x, ‖x‖ ≤ L x) {c₀ : ℝ}
    (hLf : ∀ x : Vd d, |∑ i, (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (G i)).re
      * fderiv ℝ L x (kinDir d i)| ≤ c₀ * L x) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (lyapunovComparison G E) :=
  ⟨lyapunovComparison_deficiency G hG hE hE1 hL hLn hLf (by simp),
    lyapunovComparison_deficiency G hG hE hE1 hL hLn hLf (by simp)⟩

/-- **The Koopman generator itself**: combining `lyapunovComparison_esa` with the Faris–Lavine
criterion `kvnGen_esa_of_lyapunov`, the Koopman generator `H_G` is essentially self-adjoint on
the Gauss–polynomial core as soon as, besides the Lyapunov function `L`, there is a real
polynomial `E ≥ 1` with `|G·∇E| ≤ c E`. -/
theorem kvnGenOp_esa (G : Fin d → MvPolynomial (Fin d) ℂ)
    (hG : ∀ i, RealCoeff (G i)) {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E)
    (hE1 : ∀ y : Vd d, 1 ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re) {c : ℝ}
    (hc : 0 ≤ c)
    (hflux : ∀ y : Vd d, |(MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
      (∑ i, G i * pderiv i E)).re| ≤ c * (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re)
    {L : Vd d → ℝ} (hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L) (hLn : ∀ x, ‖x‖ ≤ L x) {c₀ : ℝ}
    (hLf : ∀ x : Vd d, |∑ i, (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (G i)).re
      * fderiv ℝ L x (kinDir d i)| ≤ c₀ * L x) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (kvnGenOp G) :=
  kvnGen_esa_of_lyapunov hG hE hc (fun y => zero_le_one.trans (hE1 y)) hflux
    (lyapunovComparison_esa G hG hE hE1 hL hLn hLf)

/-! ## 6. Polynomial Lyapunov functions -/

theorem pev_im_eq_zero {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (x : Vd d) :
    (pev p x).im = 0 :=
  Complex.conj_eq_iff_im.1 (pev_real hp x)

theorem contDiff_pev_re (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Vd d => (pev p x).re) :=
  Complex.reCLM.contDiff.comp (contDiff_pev p)

theorem fderiv_pev_re (p : MvPolynomial (Fin d) ℂ) (x : Vd d) (i : Fin d) :
    fderiv ℝ (fun x : Vd d => (pev p x).re) x (kinDir d i) = (pev (pderiv i p) x).re := by
  have hd : DifferentiableAt ℝ (pev p) x :=
    differentiableAt_of_contDiffTop (contDiff_pev p) x
  have h : HasFDerivAt (fun x : Vd d => (pev p x).re)
      (Complex.reCLM.comp (fderiv ℝ (pev p) x)) x :=
    Complex.reCLM.hasFDerivAt.comp x hd.hasFDerivAt
  rw [h.fderiv, ← dcoord_pev]
  rfl

/-- **ESA of `N = H_G² + E` from a polynomial Lyapunov function**: the hypotheses of
`lyapunovComparison_esa` with `L` a real polynomial `P`, `‖x‖ ≤ P(x)`, `|G·∇P| ≤ c₀ P`. -/
theorem lyapunovComparison_esa_poly (G : Fin d → MvPolynomial (Fin d) ℂ)
    (hG : ∀ i, RealCoeff (G i)) {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E)
    (hE1 : ∀ y : Vd d, 1 ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re)
    {P : MvPolynomial (Fin d) ℂ}
    (hPn : ∀ y : Vd d, ‖y‖ ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) P).re) {c₀ : ℝ}
    (hPf : ∀ y : Vd d, |(MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
      (∑ i, G i * pderiv i P)).re| ≤ c₀ * (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) P).re) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (lyapunovComparison G E) := by
  refine lyapunovComparison_esa G hG hE hE1 (L := fun x => (pev P x).re) (contDiff_pev_re P)
    hPn (c₀ := c₀) fun x => ?_
  have h : ∑ i, (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (G i)).re
      * fderiv ℝ (fun x : Vd d => (pev P x).re) x (kinDir d i)
      = (pev (∑ i, G i * pderiv i P) x).re := by
    rw [pev_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_pev_re, pev_mul, Complex.mul_re, pev_im_eq_zero (hG i) x, zero_mul, sub_zero]
    rfl
  rw [h]
  exact hPf x

end

end BookProof.KvnKato
