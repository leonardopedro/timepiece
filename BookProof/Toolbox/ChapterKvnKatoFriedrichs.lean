import Mathlib
import BookProof.Toolbox.ChapterKvnKatoKernel

/-!
# Friedrichs' lemma for the commutator kernels

For a square-integrable `u`, the commutators `kint u k₁`, `kint u k₂` and `kint u (ek E ρ)`
of the mollifier `ρ_s` with `X` (and with `E`) tend to zero in `L²` of every ball as `s → ∞`.

The proof is the classical one: the kernels are uniformly bounded on `L²` (the Schur test and
the explicit size estimates), and on compactly supported smooth functions the commutators
tend to zero *uniformly*, by the operator identities
`kint g k₁ = X(J g) − J(X g)` and `kint g k₂ = X(kint g k₁) − kint (X g) k₁`
together with the uniform convergence of `J = kint · κ₀` and of its derivatives.
-/

namespace BookProof.KvnKato

open MeasureTheory Filter Topology
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegEnergy
open BookProof.ConvolutionCalc BookProof.DegKatoEsa
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Uniform convergence to zero on a set -/

/-- `F n → 0` uniformly on `K`. -/
def UnifTo (F : ℕ → Vd d → ℂ) (K : Set (Vd d)) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ K, ‖F n x‖ ≤ ε

namespace UnifTo

variable {F G : ℕ → Vd d → ℂ} {K : Set (Vd d)}

theorem add (hF : UnifTo F K) (hG : UnifTo G K) : UnifTo (fun n x => F n x + G n x) K := by
  intro ε hε
  filter_upwards [hF (ε / 2) (by positivity), hG (ε / 2) (by positivity)] with n h1 h2 x hx
  calc ‖F n x + G n x‖ ≤ ‖F n x‖ + ‖G n x‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h1 x hx) (h2 x hx)
    _ = ε := by ring

theorem neg (hF : UnifTo F K) : UnifTo (fun n x => -F n x) K := by
  intro ε hε
  filter_upwards [hF ε hε] with n h x hx
  rw [norm_neg]; exact h x hx

theorem sub (hF : UnifTo F K) (hG : UnifTo G K) : UnifTo (fun n x => F n x - G n x) K := by
  have h := hF.add hG.neg
  intro ε hε
  filter_upwards [h ε hε] with n h x hx
  have e : F n x - G n x = F n x + -G n x := sub_eq_add_neg _ _
  rw [e]; exact h x hx

theorem mono (hG : UnifTo G K) (h : ∀ n, ∀ x ∈ K, ‖F n x‖ ≤ ‖G n x‖) : UnifTo F K := by
  intro ε hε
  filter_upwards [hG ε hε] with n h' x hx
  exact (h n x hx).trans (h' x hx)

theorem congr (hG : UnifTo G K) (h : ∀ n, ∀ x ∈ K, F n x = G n x) : UnifTo F K :=
  hG.mono fun n x hx => by rw [h n x hx]

theorem subset (hF : UnifTo F K) {K' : Set (Vd d)} (h : K' ⊆ K) : UnifTo F K' := by
  intro ε hε
  filter_upwards [hF ε hε] with n h' x hx
  exact h' x (h hx)

theorem mul_left (hF : UnifTo F K) {b : Vd d → ℂ} {B : ℝ} (hb : ∀ x ∈ K, ‖b x‖ ≤ B) :
    UnifTo (fun n x => b x * F n x) K := by
  intro ε hε
  have hB1 : 0 < |B| + 1 := by positivity
  filter_upwards [hF (ε / (|B| + 1)) (by positivity)] with n h x hx
  rw [norm_mul]
  calc ‖b x‖ * ‖F n x‖ ≤ (|B| + 1) * (ε / (|B| + 1)) :=
        mul_le_mul ((hb x hx).trans (by linarith [le_abs_self B])) (h x hx) (norm_nonneg _)
          hB1.le
    _ = ε := by field_simp

theorem zero : UnifTo (fun _ _ => (0 : ℂ)) K := by
  intro ε hε
  exact Filter.Eventually.of_forall fun n x _ => by simp [hε.le]

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℕ → Vd d → ℂ}
    (hF : ∀ i ∈ s, UnifTo (F i) K) : UnifTo (fun n x => ∑ i ∈ s, F i n x) K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (K := K))
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    refine (h1.add h2).congr fun n x _ => ?_
    rw [Finset.sum_insert ha]

end UnifTo

/-! ## 2. Mollification of compactly supported functions -/

/-- The mollification operator at step `n`. -/
def Jn (n : ℕ) (g : Vd d → ℂ) : Vd d → ℂ := kint g (kz (rhoS (sN n)))

theorem goodKernel_kzN (n : ℕ) : GoodKernel (kz (rhoS (d := d) (sN n))) :=
  goodKernel_kz (contDiff_rhoS _) fun _ hz => rhoS_eq_zero (one_le_sN n) hz

theorem contDiff_Jn (n : ℕ) {g : Vd d → ℂ} (hg : LocallyIntegrable g (volume : Measure (Vd d))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Jn n g) :=
  contDiff_kint (goodKernel_kzN n) hg

/-- **Mollification converges uniformly** for a continuous compactly supported function. -/
theorem unifTo_Jn {h : Vd d → ℂ} (hc : Continuous h) (hcs : HasCompactSupport h) :
    UnifTo (fun n x => Jn n h x - h x) Set.univ := by
  intro ε hε
  have huc : UniformContinuous h := hcs.uniformContinuous_of_continuous hc
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  have hr : Tendsto (fun n : ℕ => 1 / (2 * sN n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 2)) atTop atTop :=
      h.const_mul_atTop (by norm_num)
    refine h2.inv_tendsto_atTop.congr fun n => ?_
    simp only [Pi.inv_apply, sN, one_div]
  filter_upwards [hr.eventually (gt_mem_nhds hδ)] with n hn x _
  have hloc : LocallyIntegrable h (volume : Measure (Vd d)) := hc.locallyIntegrable
  have hs := sN_pos n
  rw [Jn, rhoS, ← integral_smul_sub_eq_kint (contDiff_rhoR _).continuous
    ((hasCompactSupport_rho0.comp_smul hs.ne').mul_left) (integral_rhoR hs) hloc x]
  have hint : Integrable (fun y => rhoR (d := d) (sN n) y * ε) (volume : Measure (Vd d)) :=
    ((contDiff_rhoR _).continuous.integrable_of_hasCompactSupport
      ((hasCompactSupport_rho0.comp_smul hs.ne').mul_left)).mul_const ε
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · rw [norm_smul, Real.norm_of_nonneg (rhoR_nonneg hs.le y)]
    by_cases hy : rhoR (sN n) y = 0
    · simp [hy]
    · refine mul_le_mul_of_nonneg_left ?_ (rhoR_nonneg hs.le y)
      have hy' := rhoR_supp hs hy
      have := hδh (a := x - y) (b := x) (by rw [dist_eq_norm]; simp; linarith)
      rw [dist_eq_norm] at this
      exact this.le
  · rw [integral_mul_const, integral_rhoR hs, one_mul]

/-- **Mollification commutes with derivatives** on compactly supported smooth functions. -/
theorem dcoord_Jn (n : ℕ) {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) (j : Fin d) (x : Vd d) :
    dcoord j (Jn n g) x = Jn n (dcoord j g) x := by
  have hk := goodKernel_kzN (d := d) n
  have hρ := contDiff_rhoS (d := d) (sN n)
  have hρd : Differentiable ℝ (rhoS (d := d) (sN n)) := hρ.differentiable (by simp)
  rw [Jn, dcoord_kint hk hg.continuous.locallyIntegrable]
  have e1 : ∀ y, dxk j (kz (rhoS (sN n))) x y
      = -dcoord j (fun y => rhoS (d := d) (sN n) (x - y)) y := by
    intro y
    simp only [dxk, kz, dc_comp_sub, dc_reflect x y (hρd (x - y)), neg_neg]
  simp only [kint, e1, mul_neg, integral_neg]
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => rhoS (d := d) (sN n) (x - y)) :=
    hρ.comp (contDiff_const.sub contDiff_id)
  rw [integral_dcoord_mul hg hgc hψ j, neg_neg]
  rfl

/-! ## 3. `X` and `X²` of uniformly small functions -/

variable (S : KvnData d)

theorem Xf_sub {f g : Vd d → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Vd d) :
    Xf S (fun y => f y - g y) x = Xf S f x - Xf S g x := by
  simp only [Xf, dc_sub (hf x) (hg x)]
  rw [← sub_eq_zero]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem dcoord_Xf {F : Vd d → ℂ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (i : Fin d)
    (x : Vd d) :
    dcoord i (Xf S F) x = ∑ j, (dcoord i (S.G j) x * dcoord j F x
        + S.G j x * dcoord i (dcoord j F) x) + dcoord i S.c x * F x + S.c x * dcoord i F x := by
  have hF1 : ∀ j, Differentiable ℝ (dcoord j F) := fun j =>
    (contDiff_dcoord hF j).differentiable (by simp)
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hG : ∀ j, Differentiable ℝ (S.G j) := S.G_diff
  have hc : Differentiable ℝ S.c := S.c_diff
  have hd0 : DifferentiableAt ℝ (fun x => ∑ j, S.G j x * dcoord j F x) x := by fun_prop
  have hd1 : DifferentiableAt ℝ (fun x => S.c x * F x) x := by fun_prop
  have hXf : Xf S F = fun x => ∑ j, S.G j x * dcoord j F x + S.c x * F x := rfl
  rw [hXf, dc_add hd0 hd1, dc_sum _ fun j _ => by fun_prop]
  simp (disch := fun_prop) only [dc_mul]
  ring

/-- `X` of uniformly small functions (with uniformly small first derivatives) is uniformly
small on every ball. -/
theorem unifTo_Xf {F : ℕ → Vd d → ℂ} (h0 : UnifTo F Set.univ)
    (h1 : ∀ j, UnifTo (fun n => dcoord j (F n)) Set.univ) (R : ℝ) :
    UnifTo (fun n => Xf S (F n)) (Metric.closedBall 0 R) := by
  obtain ⟨B, -, hB⟩ := exists_bound_family (Option.elim · S.c S.G)
    (fun a => by cases a <;> simp [S.c_smooth.continuous, (S.G_smooth _).continuous]) R
  have hG : ∀ i, ∀ x ∈ Metric.closedBall (0 : Vd d) R, ‖S.G i x‖ ≤ B := fun i => hB (some i)
  have hc : ∀ x ∈ Metric.closedBall (0 : Vd d) R, ‖S.c x‖ ≤ B := hB none
  exact (UnifTo.sum Finset.univ fun i _ => ((h1 i).subset (Set.subset_univ _)).mul_left
    (hG i)).add ((h0.subset (Set.subset_univ _)).mul_left hc)

/-- `X²` of uniformly small functions (with uniformly small first and second derivatives) is
uniformly small on every ball. -/
theorem unifTo_XXf {F : ℕ → Vd d → ℂ} (hF : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F n))
    (h0 : UnifTo F Set.univ) (h1 : ∀ j, UnifTo (fun n => dcoord j (F n)) Set.univ)
    (h2 : ∀ i j, UnifTo (fun n => dcoord i (dcoord j (F n))) Set.univ) (R : ℝ) :
    UnifTo (fun n => Xf S (Xf S (F n))) (Metric.closedBall 0 R) := by
  obtain ⟨B, -, hB⟩ := exists_bound_family
    (Sum.elim (Option.elim · S.c S.G) (fun ij : Option (Fin d) × Fin d =>
      Option.elim ij.1 (dcoord ij.2 S.c) (fun j => dcoord ij.2 (S.G j))))
    (fun a => by
      rcases a with (_ | i) | ⟨_ | j, i⟩ <;>
        simp [S.c_smooth.continuous, (S.G_smooth _).continuous,
          (contDiff_dcoord S.c_smooth _).continuous,
          (contDiff_dcoord (S.G_smooth _) _).continuous]) R
  have hG : ∀ i, ∀ x ∈ Metric.closedBall (0 : Vd d) R, ‖S.G i x‖ ≤ B :=
    fun i => hB (Sum.inl (some i))
  have hc : ∀ x ∈ Metric.closedBall (0 : Vd d) R, ‖S.c x‖ ≤ B := hB (Sum.inl none)
  have hdG : ∀ i j, ∀ x ∈ Metric.closedBall (0 : Vd d) R, ‖dcoord i (S.G j) x‖ ≤ B :=
    fun i j => hB (Sum.inr (some j, i))
  have hdc : ∀ i, ∀ x ∈ Metric.closedBall (0 : Vd d) R, ‖dcoord i S.c x‖ ≤ B :=
    fun i => hB (Sum.inr (none, i))
  set K := Metric.closedBall (0 : Vd d) R
  have h0' := h0.subset (Set.subset_univ K)
  have h1' : ∀ j, UnifTo (fun n => dcoord j (F n)) K := fun j => (h1 j).subset (Set.subset_univ K)
  have h2' : ∀ i j, UnifTo (fun n => dcoord i (dcoord j (F n))) K := fun i j =>
    (h2 i j).subset (Set.subset_univ K)
  have hX := unifTo_Xf S h0 h1 R
  have hdX : ∀ i, UnifTo (fun n => dcoord i (Xf S (F n))) K := by
    intro i
    refine (((UnifTo.sum Finset.univ fun j _ => ((h1' j).mul_left (hdG i j)).add
      ((h2' i j).mul_left (hG j))).add (h0'.mul_left (hdc i))).add
      ((h1' i).mul_left hc)).congr fun n x _ => ?_
    exact dcoord_Xf S (hF n) i x
  exact (UnifTo.sum Finset.univ fun i _ => (hdX i).mul_left (hG i)).add (hX.mul_left hc)

/-! ## 4. The commutators on compactly supported smooth functions -/

theorem kint_Xyk {κ : Vd d → Vd d → ℂ} (hκ : GoodKernel κ) {g : Vd d → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) (x : Vd d) :
    kint g (Xyk S κ) x = -kint (Xf S g) κ x :=
  integral_mul_Xf S hg hgc (hκ.contDiff_right x)

/-- `kint g k₁ = X (J g) − J (X g)`. -/
theorem kint_k1_cc {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρs : ∀ z, 1 / 2 < ‖z‖ → ρ z = 0) {g : Vd d → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) (x : Vd d) :
    kint g (k1 S ρ) x = Xf S (kint g (kz ρ)) x - kint (Xf S g) (kz ρ) x := by
  have h0 := goodKernel_kz hρ hρs
  have hloc : LocallyIntegrable g (volume : Measure (Vd d)) := hg.continuous.locallyIntegrable
  rw [k1, kint_add (h0.Xxk S) (h0.Xyk S) hloc, ← Xf_kint S h0 hloc, kint_Xyk S h0 hg hgc]
  ring

/-- `kint g k₂ = X (kint g k₁) − kint (X g) k₁`. -/
theorem kint_k2_cc {ρ : Vd d → ℂ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρs : ∀ z, 1 / 2 < ‖z‖ → ρ z = 0) {g : Vd d → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) (x : Vd d) :
    kint g (k2 S ρ) x = Xf S (kint g (k1 S ρ)) x - kint (Xf S g) (k1 S ρ) x := by
  have h1 := goodKernel_k1 S hρ hρs
  have hloc : LocallyIntegrable g (volume : Measure (Vd d)) := hg.continuous.locallyIntegrable
  rw [k2, kint_add (h1.Xxk S) (h1.Xyk S) hloc, ← Xf_kint S h1 hloc, kint_Xyk S h1 hg hgc]
  ring

theorem dcoord_Jn_sub (n : ℕ) {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) (j : Fin d) :
    dcoord j (fun x => Jn n g x - g x) = fun x => Jn n (dcoord j g) x - dcoord j g x := by
  funext x
  rw [dc_sub ((contDiff_Jn n hg.continuous.locallyIntegrable).differentiable (by simp) x)
    (hg.differentiable (by simp) x), dcoord_Jn n hg hgc]

/-- The mollification error of a compactly supported smooth function, with its first two
derivatives, tends to zero uniformly. -/
theorem unifTo_Jn_C2 {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    UnifTo (fun n x => Jn n g x - g x) Set.univ ∧
    (∀ j, UnifTo (fun n => dcoord j (fun x => Jn n g x - g x)) Set.univ) ∧
    (∀ i j, UnifTo (fun n => dcoord i (dcoord j (fun x => Jn n g x - g x))) Set.univ) := by
  have hg1 : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dcoord j g) := fun j => contDiff_dcoord hg j
  have hgc1 : ∀ j, HasCompactSupport (dcoord j g) := fun j => hasCompactSupport_dcoord hgc j
  refine ⟨unifTo_Jn hg.continuous hgc, fun j => ?_, fun i j => ?_⟩
  · simp only [dcoord_Jn_sub _ hg hgc]
    exact unifTo_Jn (hg1 j).continuous (hgc1 j)
  · simp only [dcoord_Jn_sub _ hg hgc, dcoord_Jn_sub _ (hg1 j) (hgc1 j)]
    exact unifTo_Jn (contDiff_dcoord (hg1 j) i).continuous (hasCompactSupport_dcoord (hgc1 j) i)

theorem contDiff_Jn_sub (n : ℕ) {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Jn n g x - g x) :=
  (contDiff_Jn n hg.continuous.locallyIntegrable).sub hg

/-- **The first commutator tends to zero uniformly on balls** for compactly supported smooth
functions. -/
theorem unifTo_K1 {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) (R : ℝ) :
    UnifTo (fun n => kint g (k1 S (rhoS (sN n)))) (Metric.closedBall 0 R) := by
  obtain ⟨h0, h1, -⟩ := unifTo_Jn_C2 hg hgc
  have hXg := unifTo_Jn (contDiff_Xf S hg).continuous (hasCompactSupport_Xf S hgc)
  refine ((unifTo_Xf S h0 h1 R).sub (hXg.subset (Set.subset_univ _))).congr fun n x _ => ?_
  rw [kint_k1_cc S (contDiff_rhoS _) (fun _ hz => rhoS_eq_zero (one_le_sN n) hz) hg hgc,
    Xf_sub S ((contDiff_Jn n hg.continuous.locallyIntegrable).differentiable (by simp))
      (hg.differentiable (by simp))]
  simp only [Jn]
  ring

/-- **The second commutator tends to zero uniformly on balls** for compactly supported smooth
functions. -/
theorem unifTo_K2 {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) (R : ℝ) :
    UnifTo (fun n => kint g (k2 S (rhoS (sN n)))) (Metric.closedBall 0 R) := by
  obtain ⟨h0, h1, h2⟩ := unifTo_Jn_C2 hg hgc
  have hXg := contDiff_Xf S hg
  have hXgc := hasCompactSupport_Xf S hgc
  obtain ⟨h0', h1', -⟩ := unifTo_Jn_C2 hXg hXgc
  have hA := unifTo_XXf S (fun n => contDiff_Jn_sub n hg) h0 h1 h2 R
  have hB := unifTo_Xf S h0' h1' R
  have hC := unifTo_K1 S hXg hXgc R
  refine ((hA.sub hB).sub hC).congr fun n x _ => ?_
  have hρ := contDiff_rhoS (d := d) (sN n)
  have hρs : ∀ z : Vd d, 1 / 2 < ‖z‖ → rhoS (sN n) z = 0 :=
    fun _ hz => rhoS_eq_zero (one_le_sN n) hz
  have hJ : ∀ {h : Vd d → ℂ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      Differentiable ℝ (Jn n h) := fun hh =>
    (contDiff_Jn n hh.continuous.locallyIntegrable).differentiable (by simp)
  have hdiff : ∀ {h : Vd d → ℂ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      Differentiable ℝ h := fun hh => hh.differentiable (by simp)
  have hXJ : ∀ {h : Vd d → ℂ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      Differentiable ℝ (Xf S (Jn n h)) := fun hh =>
    (contDiff_Xf S (contDiff_Jn n hh.continuous.locallyIntegrable)).differentiable (by simp)
  have eK1 : kint g (k1 S (rhoS (sN n))) = fun x => Xf S (Jn n g) x - Jn n (Xf S g) x := by
    funext x; exact kint_k1_cc S hρ hρs hg hgc x
  have eD : Xf S (fun x => Jn n g x - g x) = fun x => Xf S (Jn n g) x - Xf S g x := by
    funext x; exact Xf_sub S (hJ hg) (hdiff hg) x
  rw [kint_k2_cc S hρ hρs hg hgc, eK1, Xf_sub S (hXJ hg) (hJ hXg), eD,
    Xf_sub S (hXJ hg) (hdiff hXg), Xf_sub S (hJ hXg) (hdiff hXg)]
  ring

/-! ## 5. `L²` bounds on balls -/

/-- The Schur test for a kernel localised in `x` to a ball and dominated by a constant on a
small ball in `x − y`. -/
theorem schur_ball {k : Vd d → Vd d → ℂ} {R a r : ℝ} (ha : 0 ≤ a)
    (hk : ∀ x ∈ Metric.closedBall (0 : Vd d) R, ∀ y,
      ‖k x y‖ ≤ (Metric.closedBall (0 : Vd d) r).indicator (fun _ => a) (x - y))
    {f : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d))) :
    eLpNorm ((Metric.closedBall (0 : Vd d) R).indicator (kint f k)) 2 volume
      ≤ ENNReal.ofReal a * volume (Metric.closedBall (0 : Vd d) r) * eLpNorm f 2 volume := by
  set K := Metric.closedBall (0 : Vd d) R
  set W : Vd d → ℝ := (Metric.closedBall (0 : Vd d) r).indicator (fun _ => a) with hW
  have hWm : Measurable W := measurable_const.indicator measurableSet_closedBall
  have hWA : ∫⁻ w, ENNReal.ofReal (W w) ≤ ENNReal.ofReal a * volume (Metric.closedBall (0 : Vd d) r) := by
    have e : (fun w => ENNReal.ofReal (W w))
        = (Metric.closedBall (0 : Vd d) r).indicator (fun _ => ENNReal.ofReal a) := by
      funext w
      by_cases hw : w ∈ Metric.closedBall (0 : Vd d) r
      · simp [hW, Set.indicator_of_mem hw]
      · simp [hW, Set.indicator_of_notMem hw]
    rw [e, lintegral_indicator_const measurableSet_closedBall]
  have hAt : ENNReal.ofReal a * volume (Metric.closedBall (0 : Vd d) r) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have h := schur_L2 (k := fun x y => K.indicator (fun x => k x y) x) hWm hAt hWA
    (fun x y => by
      by_cases hx : x ∈ K
      · simp only [Set.indicator_of_mem hx]; exact hk x hx y
      · simp only [Set.indicator_of_notMem hx, norm_zero, hW]
        by_cases hxy : x - y ∈ Metric.closedBall (0 : Vd d) r
        · simp [Set.indicator_of_mem hxy, ha]
        · simp [Set.indicator_of_notMem hxy]) hf
  convert h using 2
  funext x
  by_cases hx : x ∈ K
  · simp [Set.indicator_of_mem hx, kint]
  · simp [Set.indicator_of_notMem hx]

theorem exists_small {B : ℝ≥0∞} (hB : B ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ B * ENNReal.ofReal η ≤ ε := by
  by_cases hB0 : B = 0
  · exact ⟨1, one_pos, by simp [hB0]⟩
  have hpos : (0 : ℝ≥0∞) < ε / B := ENNReal.div_pos hε.ne' hB
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hpos
  refine ⟨r, ?_, ?_⟩
  · by_contra h
    simp [ENNReal.ofReal_eq_zero.2 (not_lt.1 h)] at hr1
  · calc B * ENNReal.ofReal r ≤ B * (ε / B) := by gcongr
      _ = ε := ENNReal.mul_div_cancel hB0 hB

theorem eLpNorm_indicator_le_of_bound {F : Vd d → ℂ} {K : Set (Vd d)} {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ x ∈ K, ‖F x‖ ≤ η) :
    eLpNorm (K.indicator F) 2 volume ≤ volume K ^ (1 / (2:ℝ)) * ENNReal.ofReal η := by
  have h1 : eLpNorm (K.indicator F) 2 volume
      ≤ eLpNorm (K.indicator (fun _ => ((η : ℝ) : ℂ))) 2 volume := by
    refine eLpNorm_mono fun x => ?_
    by_cases hx : x ∈ K
    · simp only [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_of_nonneg hη]
      exact h x hx
    · simp [Set.indicator_of_notMem hx]
  refine h1.trans ((eLpNorm_indicator_const_le _ _).trans (le_of_eq ?_))
  rw [mul_comm]
  congr 1
  rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg hη]

/-- **An abstract Friedrichs lemma.**  If a sequence of kernels is uniformly bounded on `L²`
(localised to a ball) and tends to zero uniformly on the ball when applied to compactly
supported smooth functions, then it tends to zero in `L²` of the ball when applied to any
square-integrable function. -/
theorem tendsto_delta {κ : ℕ → Vd d → Vd d → ℂ} (hκ : ∀ n, GoodKernel (κ n)) {R : ℝ}
    {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hschur : ∀ n, ∀ f : Vd d → ℂ, MemLp f 2 (volume : Measure (Vd d)) →
      eLpNorm ((Metric.closedBall (0 : Vd d) R).indicator (kint f (κ n))) 2 volume
        ≤ A * eLpNorm f 2 volume)
    (hcc : ∀ g : Vd d → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
      UnifTo (fun n => kint g (κ n)) (Metric.closedBall 0 R))
    {u : Vd d → ℂ} (hu : MemLp u 2 (volume : Measure (Vd d))) :
    Tendsto (fun n => eLpNorm ((Metric.closedBall (0 : Vd d) R).indicator (kint u (κ n))) 2
      volume) atTop (𝓝 0) := by
  set K := Metric.closedBall (0 : Vd d) R
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨η, hη, hAη⟩ := exists_small hA hε2
  have hVt : volume K ^ (1 / (2:ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne
  obtain ⟨η', hη', hVη⟩ := exists_small hVt hε2
  obtain ⟨g, hgc, hgs, hug⟩ := hu.exist_eLpNorm_sub_le (p := 2) (by norm_num) (by norm_num) hη
  have hg2 : MemLp g 2 (volume : Measure (Vd d)) := hgs.continuous.memLp_of_hasCompactSupport hgc
  filter_upwards [hcc g hgs hgc η' hη'] with n hn
  have hloc_u : LocallyIntegrable u (volume : Measure (Vd d)) := hu.locallyIntegrable one_le_two
  have hloc_g : LocallyIntegrable g (volume : Measure (Vd d)) := hgs.continuous.locallyIntegrable
  have hsplit : K.indicator (kint u (κ n))
      = K.indicator (kint (u - g) (κ n)) + K.indicator (kint g (κ n)) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [Pi.add_apply, Set.indicator_of_mem hx, kint, Pi.sub_apply, sub_mul]
      rw [integral_sub ((hκ n).integrable hloc_u x) ((hκ n).integrable hloc_g x)]
      ring
    · simp [Set.indicator_of_notMem hx]
  have hm1 : AEStronglyMeasurable (K.indicator (kint (u - g) (κ n))) volume :=
    ((contDiff_kint (hκ n) (hloc_u.sub hloc_g)).continuous.aestronglyMeasurable).indicator
      measurableSet_closedBall
  have hm2 : AEStronglyMeasurable (K.indicator (kint g (κ n))) volume :=
    ((contDiff_kint (hκ n) hloc_g).continuous.aestronglyMeasurable).indicator
      measurableSet_closedBall
  rw [hsplit]
  refine (eLpNorm_add_le hm1 hm2 (by norm_num)).trans ?_
  have h1 : eLpNorm (K.indicator (kint (u - g) (κ n))) 2 volume ≤ ε / 2 :=
    (hschur n _ (hu.sub hg2)).trans ((by gcongr : A * eLpNorm (u - g) 2 volume ≤ A * ENNReal.ofReal η).trans hAη)
  have h2 : eLpNorm (K.indicator (kint g (κ n))) 2 volume ≤ ε / 2 :=
    (eLpNorm_indicator_le_of_bound hη'.le hn).trans hVη
  calc _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

/-! ## 6. The commutators tend to zero in `L²` of every ball -/

theorem vol_scale {C : ℝ} (hC : 0 ≤ C) {s : ℝ} (hs : 1 ≤ s) :
    ENNReal.ofReal (C * s ^ d) * volume (Metric.closedBall (0 : Vd d) (1 / (2 * s)))
      ≤ ENNReal.ofReal C * volume (Metric.ball (0 : Vd d) 1) := by
  have hs0 : 0 < s := by linarith
  rw [Measure.addHaar_closedBall _ _ (by positivity), finrank_Vd, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  gcongr
  have e : C * s ^ d * (1 / (2 * s)) ^ d = C * (1 / 2) ^ d := by
    rw [div_pow, div_pow, mul_pow]; field_simp
  rw [e]
  exact mul_le_of_le_one_right hC (pow_le_one₀ (by norm_num) (by norm_num))

theorem vol_scale' {C : ℝ} (hC : 0 ≤ C) {s : ℝ} (hs : 1 ≤ s) :
    ENNReal.ofReal (C * s ^ d / s) * volume (Metric.closedBall (0 : Vd d) (1 / (2 * s)))
      ≤ ENNReal.ofReal (C / s) * volume (Metric.ball (0 : Vd d) 1) := by
  have hs0 : 0 < s := by linarith
  have e : C * s ^ d / s = (C / s) * s ^ d := by ring
  rw [e]
  exact vol_scale (div_nonneg hC hs0.le) hs

include S in
/-- **The potential commutator tends to zero** in `L²` of every ball. -/
theorem tendsto_delta_ek {E : Vd d → ℂ} (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E)
    {u : Vd d → ℂ} (hu : MemLp u 2 (volume : Measure (Vd d))) (R : ℝ) :
    Tendsto (fun n => eLpNorm ((Metric.closedBall (0 : Vd d) R).indicator
      (kint u (ek E (rhoS (sN n))))) 2 volume) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_kernel_bounds S hE R
  have hle : ∀ n, eLpNorm ((Metric.closedBall (0 : Vd d) R).indicator
      (kint u (ek E (rhoS (sN n))))) 2 volume
      ≤ ENNReal.ofReal (C / sN n) * volume (Metric.ball (0 : Vd d) 1) * eLpNorm u 2 volume := by
    intro n
    refine (schur_ball (by have := sN_pos n; positivity)
      (fun x hx y => (hb (sN n) (one_le_sN n) x hx y).2.2) hu).trans ?_
    exact mul_le_mul' (vol_scale' (d := d) hC (one_le_sN n)) le_rfl
  have hlim : Tendsto (fun n => ENNReal.ofReal (C / sN n) * volume (Metric.ball (0 : Vd d) 1)
      * eLpNorm u 2 volume) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => C / sN n) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      exact h.const_div_atTop C
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    have h3 := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul_const h2
      (Or.inr (measure_ball_lt_top (μ := (volume : Measure (Vd d))) (x := 0) (r := 1)).ne))
      (Or.inr hu.eLpNorm_ne_top)
    simpa using h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le _) hle

variable {S}

/-- **Friedrichs' lemma for `k₁`.** -/
theorem tendsto_delta_k1 {u : Vd d → ℂ} (hu : MemLp u 2 (volume : Measure (Vd d))) (R : ℝ) :
    Tendsto (fun n => eLpNorm ((Metric.closedBall (0 : Vd d) R).indicator
      (kint u (k1 S (rhoS (sN n))))) 2 volume) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_kernel_bounds S (E := fun _ => (0 : ℂ)) contDiff_const R
  have hρs : ∀ n, ∀ z : Vd d, 1 / 2 < ‖z‖ → rhoS (sN n) z = 0 :=
    fun n _ hz => rhoS_eq_zero (one_le_sN n) hz
  refine tendsto_delta (fun n => goodKernel_k1 S (contDiff_rhoS _) (hρs n))
    (A := ENNReal.ofReal C * volume (Metric.ball (0 : Vd d) 1))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne) (fun n f hf => ?_)
    (fun g hg hgc => unifTo_K1 S hg hgc R) hu
  refine (schur_ball (by have := sN_pos n; positivity)
    (fun x hx y => (hb (sN n) (one_le_sN n) x hx y).1) hf).trans ?_
  exact mul_le_mul' (vol_scale (d := d) hC (one_le_sN n)) le_rfl

/-- **Friedrichs' lemma for `k₂`.** -/
theorem tendsto_delta_k2 {u : Vd d → ℂ} (hu : MemLp u 2 (volume : Measure (Vd d))) (R : ℝ) :
    Tendsto (fun n => eLpNorm ((Metric.closedBall (0 : Vd d) R).indicator
      (kint u (k2 S (rhoS (sN n))))) 2 volume) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_kernel_bounds S (E := fun _ => (0 : ℂ)) contDiff_const R
  have hρs : ∀ n, ∀ z : Vd d, 1 / 2 < ‖z‖ → rhoS (sN n) z = 0 :=
    fun n _ hz => rhoS_eq_zero (one_le_sN n) hz
  refine tendsto_delta (fun n => goodKernel_k2 S (contDiff_rhoS _) (hρs n))
    (A := ENNReal.ofReal C * volume (Metric.ball (0 : Vd d) 1))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne) (fun n f hf => ?_)
    (fun g hg hgc => unifTo_K2 S hg hgc R) hu
  refine (schur_ball (by have := sN_pos n; positivity)
    (fun x hx y => (hb (sN n) (one_le_sN n) x hx y).2.1) hf).trans ?_
  exact mul_le_mul' (vol_scale (d := d) hC (one_le_sN n)) le_rfl

end

end BookProof.KvnKato
