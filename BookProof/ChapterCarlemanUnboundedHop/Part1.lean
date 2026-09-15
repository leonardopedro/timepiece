import Mathlib
import BookProof.ChapterNavierStokesDeficiency
import BookProof.ChapterStoneBridge

/-!
# A flux (Carleman) criterion for lattice operators with **unbounded hops**

Placeholder header; filled in once the mathematics is in place.
-/

namespace BookProof.CarlemanUnboundedHop

open Finset

noncomputable section

/-! ## 1. The kernel, the recursion and the flux across a cut -/

/-- A Hermitian matrix kernel on the lattice `ℕ`. -/
def IsHermitianKernel (a : ℕ → ℕ → ℂ) : Prop :=
  ∀ n k, a k n = (starRingEnd ℂ) (a n k)

/-- The deficiency recursion `∑ₖ a n k u k = z uₙ` for a kernel with (absolutely)
convergent rows. -/
structure LadderRecInf (a : ℕ → ℕ → ℂ) (u : ℕ → ℂ) (z : ℂ) : Prop where
  row : ∀ n, Summable fun k => a n k * u k
  eqn : ∀ n, ∑' k, a n k * u k = z * u n

/-- The **flux** of `u` through the cut separating `{0, …, N}` from `{N+1, …}`. -/
def flux (a : ℕ → ℕ → ℂ) (u : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range (N + 1),
    (starRingEnd ℂ) (u n) * ∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))

/-- The interior contributions cancel: the finite Hermitian quadratic form is real. -/
theorem inner_block_im_eq_zero (a : ℕ → ℕ → ℂ) (u : ℕ → ℂ) (hherm : IsHermitianKernel a)
    (N : ℕ) :
    (∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) *
        ∑ k ∈ range (N + 1), a n k * u k).im = 0 := by
  set Q : ℂ := ∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) * ∑ k ∈ range (N + 1), a n k * u k
    with hQ
  have hexp : Q = ∑ n ∈ range (N + 1), ∑ k ∈ range (N + 1),
      (starRingEnd ℂ) (u n) * (a n k * u k) := by
    rw [hQ]; simp [Finset.mul_sum]
  have hconj : (starRingEnd ℂ) Q = Q := by
    rw [hexp]
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hherm, Complex.conj_conj]
    ring
  have := Complex.conj_eq_iff_im.mp hconj
  simpa [hQ] using this

/-- **The flux identity.**  For a Hermitian kernel and a solution of the recursion at
`z`, the imaginary part of the flux through the cut at `N` equals `Im z` times the mass
retained on `{0, …, N}`. -/
theorem flux_identity {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hherm : IsHermitianKernel a)
    (hrec : LadderRecInf a u z) (N : ℕ) :
    z.im * ∑ n ∈ range (N + 1), ‖u n‖ ^ 2 = (flux a u N).im := by
  have hsplit : ∀ n, z * u n
      = (∑ k ∈ range (N + 1), a n k * u k)
        + ∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1)) := by
    intro n
    rw [← hrec.eqn n, ← (hrec.row n).sum_add_tsum_nat_add (N + 1)]
  have hL : ∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) * (z * u n)
      = z * ((∑ n ∈ range (N + 1), ‖u n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h1 : (starRingEnd ℂ) (u n) * u n = ((‖u n‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      simp [Complex.normSq_eq_norm_sq]
    push_cast at h1
    rw [show (starRingEnd ℂ) (u n) * (z * u n) = z * ((starRingEnd ℂ) (u n) * u n) by ring, h1]
  have hL2 : ∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) * (z * u n)
      = (∑ n ∈ range (N + 1), (starRingEnd ℂ) (u n) * ∑ k ∈ range (N + 1), a n k * u k)
        + flux a u N := by
    rw [flux, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hsplit n, mul_add]
  have him := congrArg Complex.im (hL.symm.trans hL2)
  rw [Complex.add_im, inner_block_im_eq_zero a u hherm N, zero_add] at him
  rw [← him, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- If the flux through arbitrarily late cuts is arbitrarily small, a solution of the
recursion at a non-real point vanishes. -/
theorem eq_zero_of_flux_small {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} (hz : z.im ≠ 0)
    (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z)
    (hsmall : ∀ ε > 0, ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ‖flux a u N‖ < ε) :
    ∀ n, u n = 0 := by
  have key : ∀ M : ℕ, ∑ n ∈ range (M + 1), ‖u n‖ ^ 2 ≤ 0 := by
    intro M
    by_contra hpos
    push_neg at hpos
    set S := ∑ n ∈ range (M + 1), ‖u n‖ ^ 2 with hS
    obtain ⟨N, hMN, hflux⟩ := hsmall (|z.im| * S) (by positivity) M
    have hmono : S ≤ ∑ n ∈ range (N + 1), ‖u n‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hid := flux_identity hherm hrec N
    have h1 : |z.im| * S ≤ |z.im * ∑ n ∈ range (N + 1), ‖u n‖ ^ 2| := by
      rw [abs_mul]
      have hnn : 0 ≤ ∑ n ∈ range (N + 1), ‖u n‖ ^ 2 :=
        Finset.sum_nonneg fun n _ => by positivity
      rw [abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left hmono (abs_nonneg _)
    have h2 : |z.im * ∑ n ∈ range (N + 1), ‖u n‖ ^ 2| ≤ ‖flux a u N‖ := by
      rw [hid]
      exact Complex.abs_im_le_norm _
    linarith
  intro n
  have h := key n
  have hnn : 0 ≤ ∑ m ∈ range (n + 1), ‖u m‖ ^ 2 := Finset.sum_nonneg fun m _ => by positivity
  have hzero : ∑ m ∈ range (n + 1), ‖u m‖ ^ 2 = 0 := le_antisymm h hnn
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => by positivity)).mp hzero n
    (Finset.self_mem_range_succ n)
  simpa using this

/-! ## 2. The flux bound for a kernel with decaying hops -/

section Bound

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

/-- The boundary mass carried by the cut at `N`: the `ℓ²`-mass on either side of the
cut, weighted by the tail `Θ` of the hop profile. -/
def cutMass (u : ℕ → ℂ) (Θ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), Θ (N - n) * ‖u n‖ ^ 2 + ∑' i : ℕ, Θ i * ‖u (i + (N + 1))‖ ^ 2

/-- Each hop weight is at most the tail it belongs to. -/
theorem theta_le_Theta (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j i : ℕ) : θ (i + j + 1) ≤ Θ j :=
  le_hasSum (hΘ j) i fun _ _ => hθ0 _

theorem Theta_nonneg (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j : ℕ) : 0 ≤ Θ j :=
  le_trans (hθ0 _) (theta_le_Theta hθ0 hΘ j 0)

/-- The tails of a nonnegative hop profile decrease. -/
theorem Theta_succ_le (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j : ℕ) : Θ (j + 1) ≤ Θ j := by
  have h := (hΘ j).summable.tsum_eq_zero_add
  rw [(hΘ j).tsum_eq] at h
  have h2 : ∑' b : ℕ, θ (b + 1 + j + 1) = Θ (j + 1) := by
    rw [← (hΘ (j + 1)).tsum_eq]
    exact tsum_congr fun b => by congr 1; omega
  rw [h2] at h
  have := hθ0 (0 + j + 1)
  linarith

theorem Theta_antitone (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) : Antitone Θ := by
  refine antitone_nat_of_succ_le fun j => Theta_succ_le hθ0 hΘ j

set_option maxHeartbeats 1000000 in
-- The proof re-associates a double sum over the cut and interleaves several `tsum`
-- comparison steps; the default heartbeat budget is not enough for the `Summable`
-- side conditions discharged along the way.
/-- **The flux bound.**  If the hop from `n` to `k > n` has modulus at most
`A n · θ (k − n)` with `A` nondecreasing and `θ` a hop profile with tails `Θ`, then the
flux through the cut at `N` is at most `A N` times the boundary mass there. -/
theorem two_norm_flux_le (hu : Summable fun n => ‖u n‖ ^ 2)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hA0 : ∀ n, 0 ≤ A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n)) (N : ℕ) :
    2 * ‖flux a u N‖ ≤ A N * cutMass u Θ N := by
  have hushift : Summable (fun i : ℕ => ‖u (i + (N + 1))‖ ^ 2) :=
    (summable_nat_add_iff (N + 1)).mpr hu
  -- the summability of the tail series, row by row
  have hsθu : ∀ j : ℕ, Summable (fun i : ℕ => θ (i + j + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
    intro j
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hθ0 _) (by positivity)) (fun i => ?_)
      (hushift.mul_left (Θ j))
    exact mul_le_mul_of_nonneg_right (theta_le_Theta hθ0 hΘ j i) (by positivity)
  have habs : ∀ n ∈ range (N + 1),
      Summable (fun i : ℕ => ‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hmaj : Summable (fun i : ℕ =>
        A N * (θ (i + (N - n) + 1) + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) / 2) := by
      have := (((hΘ (N - n)).summable).add (hsθu (N - n))).mul_left (A N)
      simpa [mul_div_assoc, mul_add] using this.div_const 2
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hmaj
    have hlt : n < i + (N + 1) := by omega
    have hidx : i + (N + 1) - n = i + (N - n) + 1 := by omega
    have hb := hbd n (i + (N + 1)) hlt
    rw [hidx] at hb
    have hAn : A n ≤ A N := hAmono (by omega)
    have hθn : 0 ≤ θ (i + (N - n) + 1) := hθ0 _
    have hun : 0 ≤ ‖u (i + (N + 1))‖ := norm_nonneg _
    have hAN : 0 ≤ A N := hA0 N
    have hb2 : ‖a n (i + (N + 1))‖ ≤ A N * θ (i + (N - n) + 1) :=
      hb.trans (mul_le_mul_of_nonneg_right hAn hθn)
    nlinarith [mul_nonneg (mul_nonneg hAN hθn) (sq_nonneg (‖u (i + (N + 1))‖ - 1)),
      mul_le_mul_of_nonneg_right hb2 hun]
  -- the row estimate
  have key : ∀ n ∈ range (N + 1),
      2 * (‖u n‖ * ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖)
        ≤ A N * (Θ (N - n) * ‖u n‖ ^ 2
            + ∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
    intro n hn
    have hn' : n ≤ N := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hn
    have habsn := habs n hn
    have hnorm : ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖
        ≤ ∑' i : ℕ, ‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖ := by
      have := norm_tsum_le_tsum_norm (f := fun i : ℕ => a n (i + (N + 1)) * u (i + (N + 1)))
        (by simpa [norm_mul] using habsn)
      simpa [norm_mul] using this
    have hstep1 : 2 * (‖u n‖ * ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖)
        ≤ 2 * (‖u n‖ * ∑' i : ℕ, ‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖) := by
      have := mul_le_mul_of_nonneg_left hnorm (norm_nonneg (u n))
      linarith
    have hmul : 2 * (‖u n‖ * ∑' i : ℕ, ‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖)
        = ∑' i : ℕ, 2 * (‖u n‖ * (‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖)) := by
      rw [← habsn.tsum_mul_left, ← (habsn.mul_left ‖u n‖).tsum_mul_left]
    have hterm : ∀ i : ℕ, 2 * (‖u n‖ * (‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖))
        ≤ A N * (θ (i + (N - n) + 1) * ‖u n‖ ^ 2
            + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
      intro i
      have hlt : n < i + (N + 1) := by omega
      have hidx : i + (N + 1) - n = i + (N - n) + 1 := by omega
      have hb := hbd n (i + (N + 1)) hlt
      rw [hidx] at hb
      have hAn : A n ≤ A N := hAmono hn'
      have hθn : 0 ≤ θ (i + (N - n) + 1) := hθ0 _
      have hun : 0 ≤ ‖u (i + (N + 1))‖ := norm_nonneg _
      have hun0 : 0 ≤ ‖u n‖ := norm_nonneg _
      have hAN : 0 ≤ A N := hA0 N
      have hb2 : ‖a n (i + (N + 1))‖ ≤ A N * θ (i + (N - n) + 1) :=
        hb.trans (mul_le_mul_of_nonneg_right hAn hθn)
      nlinarith [mul_nonneg (mul_nonneg hAN hθn) (sq_nonneg (‖u n‖ - ‖u (i + (N + 1))‖)),
        mul_le_mul_of_nonneg_right hb2 (mul_nonneg hun0 hun)]
    have hrhs_sum : Summable (fun i : ℕ => A N * (θ (i + (N - n) + 1) * ‖u n‖ ^ 2
        + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2)) :=
      ((((hΘ (N - n)).summable).mul_right (‖u n‖ ^ 2)).add (hsθu (N - n))).mul_left (A N)
    have hstep2 : ∑' i : ℕ, 2 * (‖u n‖ * (‖a n (i + (N + 1))‖ * ‖u (i + (N + 1))‖))
        ≤ ∑' i : ℕ, A N * (θ (i + (N - n) + 1) * ‖u n‖ ^ 2
            + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) :=
      Summable.tsum_mono ((habsn.mul_left ‖u n‖).mul_left 2) hrhs_sum hterm
    have hstep3 : ∑' i : ℕ, A N * (θ (i + (N - n) + 1) * ‖u n‖ ^ 2
            + θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2)
        = A N * (Θ (N - n) * ‖u n‖ ^ 2
            + ∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
      rw [tsum_mul_left, Summable.tsum_add
        (((hΘ (N - n)).summable).mul_right (‖u n‖ ^ 2)) (hsθu (N - n)),
        tsum_mul_right, (hΘ (N - n)).tsum_eq]
    linarith [hstep1, hmul ▸ hstep1, hstep2, hstep3]
  -- assemble
  have hflux1 : ‖flux a u N‖
      ≤ ∑ n ∈ range (N + 1), ‖u n‖ * ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
    rw [norm_mul, RCLike.norm_conj]
  have hflux2 : 2 * ‖flux a u N‖
      ≤ ∑ n ∈ range (N + 1), A N * (Θ (N - n) * ‖u n‖ ^ 2
          + ∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2) := by
    have h2 : 2 * ‖flux a u N‖
        ≤ ∑ n ∈ range (N + 1),
            2 * (‖u n‖ * ‖∑' i : ℕ, a n (i + (N + 1)) * u (i + (N + 1))‖) := by
      rw [← Finset.mul_sum]
      linarith
    exact h2.trans (Finset.sum_le_sum key)
  -- the incoming layer, after interchanging the finite sum with the series
  have hRsum : Summable (fun i : ℕ => Θ i * ‖u (i + (N + 1))‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (Theta_nonneg hθ0 hΘ i) (by positivity))
      (fun i => mul_le_mul_of_nonneg_right (Theta_antitone hθ0 hΘ (Nat.zero_le i))
        (by positivity)) (hushift.mul_left (Θ 0))
  have hinter : ∑ n ∈ range (N + 1),
        (∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2)
      ≤ ∑' i : ℕ, Θ i * ‖u (i + (N + 1))‖ ^ 2 := by
    rw [← Summable.tsum_finsetSum (fun n _ => hsθu (N - n))]
    refine Summable.tsum_mono (summable_sum (fun n _ => hsθu (N - n))) hRsum (fun i => ?_)
    · rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hrefl : ∑ n ∈ range (N + 1), θ (i + (N - n) + 1)
          = ∑ m ∈ range (N + 1), θ (i + m + 1) := by
        simpa using Finset.sum_range_reflect (fun m => θ (i + m + 1)) (N + 1)
      rw [hrefl]
      have hcomm : ∀ m : ℕ, θ (i + m + 1) = θ (m + i + 1) := by
        intro m; rw [Nat.add_comm i m]
      simp_rw [hcomm]
      exact Summable.sum_le_tsum (range (N + 1)) (fun _ _ => hθ0 _) ((hΘ i).summable) |>.trans
        (le_of_eq ((hΘ i).tsum_eq))
  have hfin : ∑ n ∈ range (N + 1), A N * (Θ (N - n) * ‖u n‖ ^ 2
        + ∑' i : ℕ, θ (i + (N - n) + 1) * ‖u (i + (N + 1))‖ ^ 2)
      ≤ A N * cutMass u Θ N := by
    rw [← Finset.mul_sum, cutMass, Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (by linarith [hinter]) (hA0 N)
  linarith

/-! ## 3. Carleman's condition: the flux is small along a subsequence of cuts -/

theorem cutMass_nonneg (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (N : ℕ) : 0 ≤ cutMass u Θ N := by
  refine add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (Theta_nonneg hθ0 hΘ _)
    (by positivity)) ?_
  exact tsum_nonneg fun i => mul_nonneg (Theta_nonneg hθ0 hΘ _) (by positivity)

/-- **The boundary masses are summable.**  Because the hop profile has a finite first
moment (`Θ` summable) and `u` is square-summable, the total boundary mass over all cuts
is finite. -/
theorem summable_cutMass (hu : Summable fun n => ‖u n‖ ^ 2) (hΘ0 : ∀ j, 0 ≤ Θ j)
    (hΘsum : Summable Θ) : Summable (fun N => cutMass u Θ N) := by
  set v : ℕ → ℝ := fun n => ‖u n‖ ^ 2 with hv
  have hv0 : ∀ n, 0 ≤ v n := fun n => by positivity
  -- the outgoing layer is a Cauchy product
  have hpart1 : Summable (fun N => ∑ n ∈ range (N + 1), Θ (N - n) * v n) := by
    have hprod : Summable (fun x : ℕ × ℕ => Θ x.1 * v x.2) :=
      hΘsum.mul_of_nonneg hu hΘ0 hv0
    have hanti := summable_sum_mul_antidiagonal_of_summable_mul hprod
    refine hanti.congr fun N => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_range_reflect (fun k => Θ k * v (N - k)) (N + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    congr 2
    all_goals omega
  -- the incoming layer is an injective reindexing of the product family
  have hpart2 : Summable (fun N => ∑' i : ℕ, Θ i * v (i + (N + 1))) := by
    have hprod : Summable (fun x : ℕ × ℕ => Θ x.1 * v x.2) :=
      hΘsum.mul_of_nonneg hu hΘ0 hv0
    have hinj : Function.Injective (fun p : ℕ × ℕ => (p.2, p.2 + p.1 + 1)) := by
      rintro ⟨N, i⟩ ⟨N', i'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      have : N = N' := by omega
      simp [this]
    have hcomp : Summable (fun p : ℕ × ℕ => Θ p.2 * v (p.2 + p.1 + 1)) := by
      simpa [Function.comp] using hprod.comp_injective hinj
    exact hcomp.prod
  simpa [cutMass, hv] using hpart1.add hpart2

/-- **Carleman's condition.**  If the amplitudes `A` grow slowly enough that
`∑ 1/A n = ∞`, then a summable sequence of boundary masses cannot keep `A N · S N` away
from zero: it is arbitrarily small along arbitrarily late cuts. -/
theorem exists_mul_lt_of_not_summable_inv {A S : ℕ → ℝ} (hA : ∀ n, 0 < A n)
    (hSsum : Summable S) (hcar : ¬ Summable fun n => (A n)⁻¹) :
    ∀ ε > 0, ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ A N * S N < ε := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ε, hε, N₀, hall⟩ := hcon
  refine hcar ?_
  have hkey : ∀ N : ℕ, (A (N + N₀))⁻¹ ≤ S (N + N₀) / ε := by
    intro N
    have h := hall (N + N₀) (by omega)
    have hApos := hA (N + N₀)
    rw [inv_eq_one_div, div_le_div_iff₀ hApos hε]
    nlinarith
  have hmaj : Summable (fun N : ℕ => S (N + N₀) / ε) :=
    (((summable_nat_add_iff N₀).mpr hSsum)).div_const ε
  have h2 : Summable (fun N : ℕ => (A (N + N₀))⁻¹) :=
    Summable.of_nonneg_of_le (fun N => inv_nonneg.mpr (hA _).le) hkey hmaj
  exact (summable_nat_add_iff N₀).mp h2

/-- **The unbounded-hop Carleman criterion.**  Let `a` be a Hermitian kernel on `ℕ` whose
hops obey `‖a n k‖ ≤ A n · θ (k − n)` for `n < k`, with

* `θ ≥ 0` a hop profile of **finite first moment** (its tails `Θ` are summable) — the hop
  range may be infinite, and
* `A > 0` nondecreasing with `∑ 1/A n = ∞` (Carleman).

Then every square-summable solution of the recursion at a non-real `z` vanishes.  The
*diagonal* of `a` is unconstrained. -/
theorem ladder_eq_zero_of_carleman {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} {A θ Θ : ℕ → ℝ}
    (hz : z.im ≠ 0) (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z)
    (hu : Summable fun n => ‖u n‖ ^ 2) (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (hΘsum : Summable Θ)
    (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) :
    ∀ n, u n = 0 := by
  refine eq_zero_of_flux_small hz hherm hrec ?_
  intro ε hε N₀
  obtain ⟨N, hN, hlt⟩ := exists_mul_lt_of_not_summable_inv hApos
    (summable_cutMass hu (Theta_nonneg hθ0 hΘ) hΘsum) hcar
    (2 * ε) (by positivity) N₀
  refine ⟨N, hN, ?_⟩
  have hb := two_norm_flux_le (a := a) hu hθ0 hΘ (fun n => (hApos n).le) hAmono hbd N
  linarith

end Bound

end

end BookProof.CarlemanUnboundedHop
