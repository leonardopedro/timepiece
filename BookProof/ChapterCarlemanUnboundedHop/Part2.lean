import Mathlib
import BookProof.ChapterNavierStokesDeficiency
import BookProof.ChapterStoneBridge
import BookProof.ChapterCarlemanUnboundedHop.Part1

/-!
# A flux (Carleman) criterion for lattice operators with **unbounded hops**

Placeholder header; filled in once the mathematics is in place.
-/

namespace BookProof.CarlemanUnboundedHop

open Finset

noncomputable section
/-! ## 4. The kernel operator on `ℓ²(ℕ)` -/

section Operator

open BookProof BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine

/-- A Hermitian kernel whose columns are square-summable: enough for the associated
matrix to act on the finitely supported states. -/
structure IsL2Kernel (a : ℕ → ℕ → ℂ) : Prop where
  herm : IsHermitianKernel a
  col : ∀ k, Memℓp (fun n => a n k) 2

/-- The action of the kernel on a coefficient sequence. -/
def kernelFun (a : ℕ → ℕ → ℂ) (f : ℕ → ℂ) : ℕ → ℂ := fun n => ∑' k : ℕ, a n k * f k

theorem kernelFun_eq_sum (a : ℕ → ℕ → ℂ) {f : ℕ → ℂ} {M : ℕ} (hf : ∀ n, M ≤ n → f n = 0)
    (n : ℕ) : kernelFun a f n = ∑ k ∈ range M, a n k * f k := by
  refine tsum_eq_sum ?_
  intro k hk
  rw [hf k (by simpa using hk)]
  ring

theorem memℓp_finsetSum (s : Finset ℕ) (g : ℕ → ℕ → ℂ) (h : ∀ k ∈ s, Memℓp (g k) 2) :
    Memℓp (fun n => ∑ k ∈ s, g k n) 2 := by
  classical
  induction s using Finset.induction with
  | empty => simpa using zero_memℓp (E := fun _ : ℕ => ℂ) (p := 2)
  | insert j s hj ih =>
    have h1 : Memℓp (g j) 2 := h j (Finset.mem_insert_self _ _)
    have h2 : Memℓp (fun n => ∑ k ∈ s, g k n) 2 :=
      ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    have heq : (fun n => ∑ k ∈ insert j s, g k n) = g j + (fun n => ∑ k ∈ s, g k n) := by
      funext n
      simp [Finset.sum_insert hj]
    rw [heq]
    exact h1.add h2

theorem memℓp_kernelFun {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) {f : ℕ → ℂ} {M : ℕ}
    (hf : ∀ n, M ≤ n → f n = 0) : Memℓp (kernelFun a f) 2 := by
  have heq : kernelFun a f = fun n => ∑ k ∈ range M, f k * a n k := by
    funext n
    rw [kernelFun_eq_sum a hf n]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [heq]
  exact memℓp_finsetSum (range M) (fun k n => f k * a n k)
    fun k _ => (hk.col k).const_smul (f k)

/-- The operator defined by an `ℓ²`-column Hermitian kernel, on the finitely supported
states of `ℓ²(ℕ)`. -/
def kernelOp {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) : lpFiniteModes ℕ →ₗ[ℂ] L2N where
  toFun f := ⟨kernelFun a ((f : L2N) : ℕ → ℂ),
    memℓp_kernelFun hk (Classical.choose_spec (exists_tail_zero f.2))⟩
  map_add' f g := by
    obtain ⟨Mf, hMf⟩ := exists_tail_zero f.2
    obtain ⟨Mg, hMg⟩ := exists_tail_zero g.2
    have hf : ∀ n, max Mf Mg ≤ n → ((f : L2N) : ℕ → ℂ) n = 0 :=
      fun n hn => hMf n (le_trans (le_max_left _ _) hn)
    have hg : ∀ n, max Mf Mg ≤ n → ((g : L2N) : ℕ → ℂ) n = 0 :=
      fun n hn => hMg n (le_trans (le_max_right _ _) hn)
    have hfg : ∀ n, max Mf Mg ≤ n → (((f + g : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) n = 0 := by
      intro n hn
      simp [hf n hn, hg n hn]
    ext n
    change kernelFun a (((f + g : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) n = _
    rw [kernelFun_eq_sum a hfg n]
    change _ = kernelFun a ((f : L2N) : ℕ → ℂ) n + kernelFun a ((g : L2N) : ℕ → ℂ) n
    rw [kernelFun_eq_sum a hf n, kernelFun_eq_sum a hg n, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (((f + g : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) k
        = ((f : L2N) : ℕ → ℂ) k + ((g : L2N) : ℕ → ℂ) k := by simp
    rw [this]; ring
  map_smul' c f := by
    obtain ⟨Mf, hMf⟩ := exists_tail_zero f.2
    have hcf : ∀ n, Mf ≤ n → (((c • f : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) n = 0 := by
      intro n hn
      simp [hMf n hn]
    ext n
    change kernelFun a (((c • f : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) n = _
    rw [kernelFun_eq_sum a hcf n]
    change _ = c * kernelFun a ((f : L2N) : ℕ → ℂ) n
    rw [kernelFun_eq_sum a hMf n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (((c • f : lpFiniteModes ℕ) : L2N) : ℕ → ℂ) k = c * ((f : L2N) : ℕ → ℂ) k := by simp
    rw [this]; ring

@[simp] theorem kernelOp_coe {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) (f : lpFiniteModes ℕ) :
    ((kernelOp hk f : L2N) : ℕ → ℂ) = kernelFun a ((f : L2N) : ℕ → ℂ) := rfl

/-- The kernel operator is symmetric on the finitely supported states. -/
theorem kernelOp_symmetric {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) :
    SymmetricOn (lpFiniteModes ℕ) (kernelOp hk) := by
  intro x y
  obtain ⟨Mx, hMx⟩ := exists_tail_zero x.2
  obtain ⟨My, hMy⟩ := exists_tail_zero y.2
  have hL : (inner ℂ (kernelOp hk x : L2N) (y : L2N) : ℂ)
      = ∑ n ∈ range My, ∑ k ∈ range Mx,
          ((y : L2N) : ℕ → ℂ) n * ((starRingEnd ℂ) (a n k)
            * (starRingEnd ℂ) (((x : L2N) : ℕ → ℂ) k)) := by
    rw [← inner_conj_symm, inner_eq_sum_range (f := (y : L2N)) hMy, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, Complex.conj_conj]
    change ((y : L2N) : ℕ → ℂ) n * (starRingEnd ℂ) (kernelFun a ((x : L2N) : ℕ → ℂ) n) = _
    rw [kernelFun_eq_sum a hMx n, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
  have hR : (inner ℂ (x : L2N) (kernelOp hk y : L2N) : ℂ)
      = ∑ k ∈ range Mx, ∑ n ∈ range My,
          (starRingEnd ℂ) (((x : L2N) : ℕ → ℂ) k) * (a k n * ((y : L2N) : ℕ → ℂ) n) := by
    rw [inner_eq_sum_range (f := (x : L2N)) hMx]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (starRingEnd ℂ) (((x : L2N) : ℕ → ℂ) k) * kernelFun a ((y : L2N) : ℕ → ℂ) k = _
    rw [kernelFun_eq_sum a hMy k, Finset.mul_sum]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n _ => ?_
  rw [hk.herm n k]
  ring

/-- Square-summability of the moduli of an `ℓ²(ℕ)` state. -/
theorem summable_normSq_lp (f : L2N) : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ 2 := by
  have hsum := (lp.memℓp f).summable (p := 2) (by norm_num)
  refine hsum.congr fun n => ?_
  rw [show ENNReal.toReal 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The rows of an `ℓ²`-column Hermitian kernel are square-summable too. -/
theorem row_summable {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) (k : ℕ) :
    Summable fun n : ℕ => ‖a k n‖ ^ 2 := by
  have hcol : Summable fun n : ℕ => ‖a n k‖ ^ 2 := by
    have hsum := (hk.col k).summable (p := 2) (by norm_num)
    refine hsum.congr fun n => ?_
    rw [show ENNReal.toReal 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine hcol.congr fun n => ?_
  rw [hk.herm n k, RCLike.norm_conj]

/-- **A deficiency vector satisfies the recursion.**  Testing the deficiency identity
against the canonical basis vector `e_k` gives the `k`-th line of `a w = z w`. -/
theorem ladderRec_of_deficiency {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) {z : ℂ} {w : L2N}
    (hw : ∀ v : lpFiniteModes ℕ, (inner ℂ (kernelOp hk v) (w : L2N) : ℂ)
        = z * inner ℂ (v : L2N) (w : L2N)) :
    LadderRecInf a ((w : ℕ → ℂ)) z := by
  classical
  have hw2 := summable_normSq_lp w
  have hrow : ∀ k : ℕ, Summable fun n : ℕ => a k n * (w : ℕ → ℂ) n := by
    intro k
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (((row_summable hk k).add hw2).mul_left (1 / 2))
    rw [norm_mul]
    nlinarith [sq_nonneg (‖a k n‖ - ‖(w : ℕ → ℂ) n‖), norm_nonneg (a k n),
      norm_nonneg ((w : ℕ → ℂ) n)]
  refine ⟨hrow, fun k => ?_⟩
  -- test against `e_k`
  set v : lpFiniteModes ℕ := ⟨lp.single 2 k (1 : ℂ), lpSingle_mem_lpFiniteModes k 1⟩ with hv
  have hvcoe : ∀ j, ((v : L2N) : ℕ → ℂ) j = if j = k then (1 : ℂ) else 0 := by
    intro j; simp [hv, lp.single_apply, Pi.single_apply]
  have hTv : ∀ n, ((kernelOp hk v : L2N) : ℕ → ℂ) n = a n k := by
    intro n
    rw [kernelOp_coe, kernelFun]
    rw [tsum_eq_single k (by
      intro b hb
      rw [hvcoe b, if_neg hb]
      ring)]
    rw [hvcoe k, if_pos rfl]
    ring
  have hrhs : (inner ℂ (v : L2N) (w : L2N) : ℂ) = (w : ℕ → ℂ) k := by
    rw [lp.inner_eq_tsum]
    rw [tsum_eq_single k (by
      intro b hb
      simp [RCLike.inner_apply, hvcoe b, if_neg hb])]
    simp [RCLike.inner_apply, hvcoe k]
  have hlhs : (inner ℂ (kernelOp hk v : L2N) (w : L2N) : ℂ)
      = ∑' n : ℕ, a k n * (w : ℕ → ℂ) n := by
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun n => ?_
    rw [RCLike.inner_apply, hTv n, hk.herm n k]
    ring
  have := hw v
  rw [hlhs, hrhs] at this
  exact this

/-- **Essential self-adjointness under the unbounded-hop Carleman condition.**  The
deficiency spaces of the kernel operator are trivial at every non-real point. -/
theorem kernelOp_deficiencyTrivialAt {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (lpFiniteModes ℕ) (kernelOp hk) z := by
  intro w hw
  have hrec := ladderRec_of_deficiency hk hw
  have hzero := ladder_eq_zero_of_carleman hz hk.herm hrec (summable_normSq_lp w)
    hθ0 hΘ hΘsum hApos hAmono hbd hcar
  exact lp.ext (funext hzero)

/-- **The headline of the unbounded-hop criterion.**  A Hermitian matrix on `ℓ²(ℕ)` whose
off-diagonal entries decay in the hop length with a finite first moment, with amplitudes
satisfying Carleman's growth condition, is essentially self-adjoint on the finitely
supported states — whatever its diagonal, and however long its hops. -/
theorem kernelOp_essentiallySelfAdjoint {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ) (kernelOp hk) :=
  ⟨kernelOp_deficiencyTrivialAt hk hθ0 hΘ hΘsum hApos hAmono hbd hcar (by simp),
    kernelOp_deficiencyTrivialAt hk hθ0 hΘ hΘsum hApos hAmono hbd hcar (by simp)⟩

/-- **The unitary flow.**  Stone's theorem applied to the closure of the kernel
operator. -/
theorem kernelOp_stone_flow {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) :
    ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint L2N) (U : ℝ → (L2N →L[ℂ] L2N)),
      EsaClosure.IsSelfAdjointExtension (kernelOp hk) T.op ∧ StoneBridge.IsStoneFlow T U :=
  StoneBridge.exists_stone_flow_of_esa _ lpFiniteModes_dense (kernelOp_symmetric hk)
    (kernelOp_essentiallySelfAdjoint hk hθ0 hΘ hΘsum hApos hAmono hbd hcar)

end Operator

/-! ## 5. An instance with genuinely unbounded hops -/

section Instance

open BookProof BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine

/-- A Hermitian matrix on `ℓ²(ℕ)` with **infinite hop range**: the entry at distance `r`
from the diagonal is `(1 + min n k) ρ^r`, and the diagonal is an arbitrary real sequence
`b` — no growth restriction on it whatsoever. -/
def geoHop (b : ℕ → ℝ) (rho : ℝ) : ℕ → ℕ → ℂ := fun n k =>
  if n = k then ((b n : ℝ) : ℂ)
  else (((1 + ((min n k : ℕ) : ℝ)) * rho ^ (max n k - min n k) : ℝ) : ℂ)

theorem geoHop_herm (b : ℕ → ℝ) (rho : ℝ) : IsHermitianKernel (geoHop b rho) := by
  intro n k
  by_cases h : n = k
  · subst h; simp [geoHop]
  · rw [geoHop, geoHop, if_neg (Ne.symm h), if_neg h, min_comm k n, max_comm k n,
      Complex.conj_ofReal]

theorem geoHop_norm_off {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) {n k : ℕ} (h : n ≠ k) :
    ‖geoHop b rho n k‖ = (1 + ((min n k : ℕ) : ℝ)) * rho ^ (max n k - min n k) := by
  rw [geoHop, if_neg h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Off the diagonal, the hop amplitude splits as `A n · θ (k − n)` with `A n = 1 + n`
and the geometric profile `θ r = ρ^r`. -/
theorem geoHop_bound {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) (n k : ℕ) (hnk : n < k) :
    ‖geoHop b rho n k‖ ≤ (1 + (n : ℝ)) * rho ^ (k - n) := by
  have hmin : min n k = n := min_eq_left hnk.le
  have hmax : max n k = k := max_eq_right hnk.le
  rw [geoHop_norm_off hrho (Nat.ne_of_lt hnk), hmin, hmax]

theorem geoHop_col {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) (k : ℕ) :
    Memℓp (fun n => geoHop b rho n k) 2 := by
  refine memLpTwo_of_summable_normSq ?_
  refine (summable_nat_add_iff (k + 1)).mp ?_
  have heq : ∀ m : ℕ, ‖geoHop b rho (m + (k + 1)) k‖ ^ 2
      = (1 + (k : ℝ)) ^ 2 * ((rho ^ 2) ^ (m + 1)) := by
    intro m
    have hne : m + (k + 1) ≠ k := by omega
    have hmin : min (m + (k + 1)) k = k := by omega
    have hmax : max (m + (k + 1)) k = m + (k + 1) := by omega
    have hsub : m + (k + 1) - k = m + 1 := by omega
    rw [geoHop_norm_off hrho hne, hmin, hmax, hsub, mul_pow, ← pow_mul, ← pow_mul]
    ring_nf
  have hgeo : Summable (fun m : ℕ => (1 + (k : ℝ)) ^ 2 * ((rho ^ 2) ^ (m + 1))) := by
    have hlt : rho ^ 2 < 1 := by nlinarith
    have hsum : Summable (fun m : ℕ => (rho ^ 2) ^ m) :=
      (hasSum_geometric_of_lt_one (by positivity) hlt).summable
    have := (hsum.mul_left (rho ^ 2)).mul_left ((1 + (k : ℝ)) ^ 2)
    refine this.congr fun m => ?_
    rw [pow_succ]
    ring
  exact hgeo.congr fun m => (heq m).symm

/-- The geometric hop profile has a finite first moment: its tails are summable. -/
theorem geo_hasSum_tail {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) (j : ℕ) :
    HasSum (fun i : ℕ => rho ^ (i + j + 1)) (rho ^ (j + 1) * (1 - rho)⁻¹) := by
  have h := (hasSum_geometric_of_lt_one hrho hrho1).mul_left (rho ^ (j + 1))
  have heq : (fun i : ℕ => rho ^ (j + 1) * rho ^ i) = fun i : ℕ => rho ^ (i + j + 1) := by
    funext i
    rw [← pow_add]
    congr 1
    omega
  exact heq ▸ h

theorem geo_summable_tail {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    Summable (fun j : ℕ => rho ^ (j + 1) * (1 - rho)⁻¹) := by
  have hsum : Summable (fun j : ℕ => rho ^ j) :=
    (hasSum_geometric_of_lt_one hrho hrho1).summable
  have := ((hsum.mul_left rho).mul_right (1 - rho)⁻¹)
  refine this.congr fun j => ?_
  rw [pow_succ]
  ring

theorem not_summable_inv_one_add_nat : ¬ Summable (fun n : ℕ => (1 + (n : ℝ))⁻¹) := by
  intro h
  refine Real.not_summable_natCast_inv ?_
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1))⁻¹) := by simpa [add_comm] using h
  exact (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ))⁻¹) 1).mp (by simpa using h1)

/-- The kernel data of `geoHop`. -/
theorem geoHop_isL2Kernel (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    IsL2Kernel (geoHop b rho) :=
  ⟨geoHop_herm b rho, fun k => geoHop_col hrho hrho1 k⟩

/-- **An unbounded-hop instance.**  For an *arbitrary* real diagonal `b` and geometric
hops of infinite range with linearly growing amplitudes, the matrix operator is
essentially self-adjoint on the finitely supported states of `ℓ²(ℕ)`.  The finite-hop
Carleman criteria of `ChapterHermiteCarlemanEsa`, `ChapterCarlemanTwoStep` and
`ChapterCarlemanGeneralHop` do not cover this operator: every row has infinitely many
nonzero entries. -/
theorem geoHop_essentiallySelfAdjoint (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho)
    (hrho1 : rho < 1) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ) (kernelOp (geoHop_isL2Kernel b hrho hrho1)) :=
  kernelOp_essentiallySelfAdjoint (A := fun n => 1 + (n : ℝ)) (θ := fun r => rho ^ r)
    (Θ := fun j => rho ^ (j + 1) * (1 - rho)⁻¹) _
    (fun r => by positivity) (geo_hasSum_tail hrho hrho1) (geo_summable_tail hrho hrho1)
    (fun n => by positivity) (fun m n hmn => by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
      linarith)
    (fun n k hnk => geoHop_bound hrho n k hnk) not_summable_inv_one_add_nat

/-- The corresponding unitary flow. -/
theorem geoHop_stone_flow (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint L2N) (U : ℝ → (L2N →L[ℂ] L2N)),
      EsaClosure.IsSelfAdjointExtension (kernelOp (geoHop_isL2Kernel b hrho hrho1)) T.op ∧
        StoneBridge.IsStoneFlow T U :=
  StoneBridge.exists_stone_flow_of_esa _ lpFiniteModes_dense
    (kernelOp_symmetric (geoHop_isL2Kernel b hrho hrho1))
    (geoHop_essentiallySelfAdjoint b hrho hrho1)

end Instance

end

end BookProof.CarlemanUnboundedHop
