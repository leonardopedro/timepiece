import BookProof.ChapterFarisLavineCore

/-!
# The Faris–Lavine criterion on a core: `N + 1` with dense range instead of onto

`BookProof.ChapterFarisLavineCore` proves Theorem 1 of Faris–Lavine in the form in which the
comparison operator `N` is given on the whole of its self-adjointness domain, i.e. `N + 1` maps
the common domain **onto** the Hilbert space.  On an algebraic core (polynomials times a
Gaussian, finite-particle vectors, …) that is never the case: a positive operator that is
essentially self-adjoint on a core `D` only has `N + 1` with **dense range** from `D`.

This module proves the criterion in that form, with every hypothesis stated on the core only:

> Let `D` be a dense subspace, `H`, `N : D → F` symmetric, `N ≥ 0`, `(N + 1) D` dense,
> `‖H x‖ ≤ a ‖N x‖ + b ‖x‖` and `|⟪x, i[H, N] x⟫| ≤ c ⟪x, N x⟫` on `D`.
> Then `H` is essentially self-adjoint on `D`.

This is the statement of Faris–Lavine, Corollary 1.1 (`D` is a core for the self-adjoint
closure of `N`, and the two estimates are only required on `D`), proved directly: the test
vector `(N̄ + 1)⁻¹ w` of the paper is replaced by a sequence `g_n ∈ D` with `(N + 1) g_n → w`,
the relative bound keeps `H g_n` bounded, the commutator bound forces
`⟪g_n, (N + 1) g_n⟫ → 0`, and closability of `N + 1` (symmetry plus density of `D`) turns
`g_n → 0`, `(N + 1) g_n → w` into `w = 0`.

* `deficiencyTrivialAt_of_farisLavine_dense` — the estimate: deficiency at `d i` vanishes
  whenever `2|d| > c`;
* **`essentiallySelfAdjointOn_of_farisLavine_dense`** — the criterion;
* `dense_range_add_one_of_esa_of_pos` — for a positive symmetric `N`, essential
  self-adjointness on `D` gives density of `(N + 1) D`, so the density hypothesis above is
  exactly essential self-adjointness of `N`;
* the **square comparison** `N = H² + E` for an `H` that maps `D` into itself:
  `quadForm_square_comparison` (`⟪x, N x⟫ = ‖H x‖² + ⟪x, E x⟫`),
  `symmetricOn_square_comparison`, `norm_le_square_comparison` (`‖H x‖ ≤ ‖N x‖ + ‖x‖`),
  `commForm_square_comparison` (`⟪x, i[H, N] x⟫ = ⟪x, i[H, E] x⟫` exactly), and
  **`essentiallySelfAdjointOn_of_square_comparison`**: if `E ≥ 0` has
  `|⟪x, i[H, E] x⟫| ≤ c ⟪x, E x⟫` and `H² + E` is essentially self-adjoint on `D`, then so is
  `H`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.FarisLavine

open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

/-- For a positive symmetric `N`, `‖N g‖ ≤ ‖N g + g‖` and `‖g‖ ≤ ‖N g + g‖`. -/
theorem norm_le_norm_add_of_pos (N : D →ₗ[ℂ] F)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x) (g : D) :
    ‖N g‖ ^ 2 + ‖(g : F)‖ ^ 2 ≤ ‖N g + (g : F)‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ) (N g) (g : F)
  have hre : RCLike.re (inner ℂ (N g) (g : F) : ℂ) = quadForm N g := by
    have h1 : (inner ℂ (N g) (g : F) : ℂ) = starRingEnd ℂ (inner ℂ (g : F) (N g)) :=
      (inner_conj_symm (𝕜 := ℂ) (N g) (g : F)).symm
    rw [h1]
    simp only [RCLike.re_to_complex, Complex.conj_re]
    rfl
  rw [hre] at h
  have := hNpos g
  linarith

/-- **The Faris–Lavine estimate on a core.** -/
theorem deficiencyTrivialAt_of_farisLavine_dense [CompleteSpace F]
    (H N : D →ₗ[ℂ] F) (a b c d : ℝ)
    (hD : Dense (D : Set F))
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNdense : Dense (Set.range fun x : D => N x + (x : F)))
    (hrel : ∀ x : D, ‖H x‖ ≤ a * ‖N x‖ + b * ‖(x : F)‖)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hd : c < 2 * |d|) :
    DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) := by
  intro w hw
  -- approximate `w` by `(N + 1) g_n`
  have hex : ∀ n : ℕ, ∃ g : D, ‖N g + (g : F) - w‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, ⟨g, rfl⟩, hy⟩ :=
      hNdense.exists_dist_lt w (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    exact ⟨g, by rw [← dist_eq_norm, dist_comm]; exact hy⟩
  choose g hg using hex
  set M : ℝ := ‖w‖ + 1 with hM
  set e : ℕ → F := fun n => w - (N (g n) + (g n : F)) with he
  have he_le : ∀ n, ‖e n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n; rw [he]; simp only; rw [norm_sub_rev]; exact (hg n).le
  have hinv_le : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hNg_le : ∀ n, ‖N (g n) + (g n : F)‖ ≤ M := by
    intro n
    have h1 : N (g n) + (g n : F) = w - e n := by simp [he]
    rw [h1, hM]
    calc ‖w - e n‖ ≤ ‖w‖ + ‖e n‖ := norm_sub_le _ _
      _ ≤ ‖w‖ + 1 := by linarith [he_le n, hinv_le n]
  have hsq : ∀ n, ‖N (g n)‖ ≤ M ∧ ‖(g n : F)‖ ≤ M := by
    intro n
    have h := norm_le_norm_add_of_pos N hNpos (g n)
    have hM0 : 0 ≤ M := by positivity
    have h2 : ‖N (g n) + (g n : F)‖ ^ 2 ≤ M ^ 2 := by
      have := hNg_le n; gcongr
    constructor
    · nlinarith [norm_nonneg (N (g n)), sq_nonneg ‖(g n : F)‖]
    · nlinarith [norm_nonneg (g n : F), sq_nonneg ‖N (g n)‖]
  set A : ℝ := |a| * M + |b| * M with hA
  have hHg : ∀ n, ‖H (g n)‖ ≤ A := by
    intro n
    have h := hrel (g n)
    have h1 : a * ‖N (g n)‖ ≤ |a| * M :=
      le_trans (le_abs_self _) (by rw [abs_mul, abs_norm]; gcongr; exact (hsq n).1)
    have h2 : b * ‖(g n : F)‖ ≤ |b| * M :=
      le_trans (le_abs_self _) (by rw [abs_mul, abs_norm]; gcongr; exact (hsq n).2)
    linarith
  -- the quantity `t_n = ⟪g_n, (N + 1) g_n⟫`
  set t : ℕ → ℝ := fun n => quadForm N (g n) + ‖(g n : F)‖ ^ 2 with ht
  have hdc : 0 < |d| - c / 2 := by linarith
  have ht_le : ∀ n, t n ≤ (A + |d| * M) * (1 / ((n : ℝ) + 1)) / (|d| - c / 2) := by
    intro n
    set gn := g n
    have key := hw gn
    have hw' : w = N gn + (gn : F) + e n := by simp [he, gn]
    rw [hw', inner_add_right, inner_add_right, inner_add_right, inner_add_right] at key
    -- imaginary parts
    have him := congrArg Complex.im key
    have hBim : (inner ℂ (H gn) (gn : F) : ℂ).im = 0 := inner_apply_self_im H hH gn
    have hPim : (inner ℂ (gn : F) (N gn) : ℂ).im = 0 := quadForm_im N hN gn
    have hQim : (inner ℂ (gn : F) (gn : F) : ℂ).im = 0 := by
      simpa using inner_self_im (𝕜 := ℂ) (gn : F)
    have hQre : (inner ℂ (gn : F) (gn : F) : ℂ).re = ‖(gn : F)‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (gn : F)
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re, hBim, hPim, hQim,
      hQre] at him
    -- error terms
    have hE1 : |(inner ℂ (H gn) (e n) : ℂ).im| ≤ A * (1 / ((n : ℝ) + 1)) := by
      calc |(inner ℂ (H gn) (e n) : ℂ).im| ≤ ‖(inner ℂ (H gn) (e n) : ℂ)‖ :=
            Complex.abs_im_le_norm _
        _ ≤ ‖H gn‖ * ‖e n‖ := norm_inner_le_norm _ _
        _ ≤ A * (1 / ((n : ℝ) + 1)) :=
            mul_le_mul (hHg n) (he_le n) (norm_nonneg _) (le_trans (norm_nonneg _) (hHg n))
    have hE2 : |(inner ℂ (gn : F) (e n) : ℂ).re| ≤ M * (1 / ((n : ℝ) + 1)) := by
      calc |(inner ℂ (gn : F) (e n) : ℂ).re| ≤ ‖(inner ℂ (gn : F) (e n) : ℂ)‖ :=
            Complex.abs_re_le_norm _
        _ ≤ ‖(gn : F)‖ * ‖e n‖ := norm_inner_le_norm _ _
        _ ≤ M * (1 / ((n : ℝ) + 1)) :=
            mul_le_mul (hsq n).2 (he_le n) (norm_nonneg _) (by positivity)
    have hcf : |commForm H N gn| = 2 * |(inner ℂ (H gn) (N gn) : ℂ).im| := by
      rw [commForm_eq, abs_mul]; norm_num
    have hc1 := hcomm gn
    rw [hcf] at hc1
    have hq : quadForm N gn = (inner ℂ (gn : F) (N gn) : ℂ).re := rfl
    have htn : t n = (inner ℂ (gn : F) (N gn) : ℂ).re + ‖(gn : F)‖ ^ 2 := rfl
    have hqle : quadForm N gn ≤ t n := by
      rw [htn, ← hq]; nlinarith [sq_nonneg ‖(gn : F)‖]
    have hc0 : 0 ≤ c := hc
    -- `d t = Im⟪H g, N g⟫ + Im⟪H g, e⟫ - d Re⟪g, e⟫`
    have hdt : d * t n = (inner ℂ (H gn) (N gn) : ℂ).im + (inner ℂ (H gn) (e n) : ℂ).im
        - d * (inner ℂ (gn : F) (e n) : ℂ).re := by
      rw [htn]; linarith
    have habs : |d| * t n ≤ c / 2 * t n + (A + |d| * M) * (1 / ((n : ℝ) + 1)) := by
      have htnn : 0 ≤ t n := by have := hNpos gn; positivity
      have h1 : |d * t n| = |d| * t n := by rw [abs_mul, abs_of_nonneg htnn]
      have h2 : |d * t n| ≤ |(inner ℂ (H gn) (N gn) : ℂ).im|
          + |(inner ℂ (H gn) (e n) : ℂ).im| + |d| * |(inner ℂ (gn : F) (e n) : ℂ).re| := by
        rw [hdt, ← abs_mul]
        exact le_trans (abs_sub _ _) (by gcongr; exact abs_add_le _ _)
      have h3 : |(inner ℂ (H gn) (N gn) : ℂ).im| ≤ c / 2 * t n := by
        have : 2 * |(inner ℂ (H gn) (N gn) : ℂ).im| ≤ c * t n :=
          le_trans hc1 (mul_le_mul_of_nonneg_left hqle hc0)
        linarith
      have h4 : |d| * |(inner ℂ (gn : F) (e n) : ℂ).re| ≤ |d| * (M * (1 / ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hE2 (abs_nonneg d)
      nlinarith
    rw [le_div_iff₀ hdc]
    nlinarith
  -- `g_n → 0`
  have hg0 : Tendsto (fun n => (g n : F)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hK : Tendsto (fun n : ℕ => (A + |d| * M) * (1 / ((n : ℝ) + 1)) / (|d| - c / 2))
        atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (A + |d| * M)
      simpa using this.div_const (|d| - c / 2)
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt
        ((A + |d| * M) * (1 / ((n : ℝ) + 1)) / (|d| - c / 2))) atTop (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0).comp hK
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsqrt
    apply Real.le_sqrt_of_sq_le
    have h1 := ht_le n
    have h2 := hNpos (g n)
    have : ‖(g n : F)‖ ^ 2 ≤ t n := by simp only [ht]; linarith
    linarith
  -- `(N + 1) g_n → w`
  have hNw : Tendsto (fun n => N (g n) + (g n : F)) atTop (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hg n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- `w ⊥ D`
  have horth : ∀ v : D, (inner ℂ w (v : F) : ℂ) = 0 := by
    intro v
    have h1 : Tendsto (fun n => (inner ℂ (N (g n) + (g n : F)) (v : F) : ℂ)) atTop
        (𝓝 (inner ℂ w (v : F))) :=
      ((continuous_inner.comp
        (Continuous.prodMk continuous_id continuous_const)).tendsto w).comp hNw
    have h2 : (fun n => (inner ℂ (N (g n) + (g n : F)) (v : F) : ℂ))
        = fun n => (inner ℂ (g n : F) (N v + (v : F)) : ℂ) := by
      funext n
      rw [inner_add_left, inner_add_right, hN (g n) v]
    have h3 : Tendsto (fun n => (inner ℂ (g n : F) (N v + (v : F)) : ℂ)) atTop
        (𝓝 (inner ℂ (0 : F) (N v + (v : F)))) :=
      ((continuous_inner.comp
        (Continuous.prodMk continuous_id continuous_const)).tendsto 0).comp hg0
    rw [inner_zero_left] at h3
    rw [h2] at h1
    exact tendsto_nhds_unique h1 h3
  -- `D` dense, so `w = 0`
  have hclosed : IsClosed {x : F | (inner ℂ w x : ℂ) = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : (D : Set F) ⊆ {x : F | (inner ℂ w x : ℂ) = 0} := fun x hx => horth ⟨x, hx⟩
  have hall : closure (D : Set F) ⊆ {x : F | (inner ℂ w x : ℂ) = 0} :=
    closure_minimal hsub hclosed
  rw [hD.closure_eq] at hall
  have hww : (inner ℂ w w : ℂ) = 0 := hall (Set.mem_univ w)
  exact inner_self_eq_zero.mp hww

/-- **Faris–Lavine on a core** (Corollary 1.1 of the paper, with every hypothesis stated on the
core only).  `D` dense, `H` and `N` symmetric on `D`, `N ≥ 0` with `(N + 1) D` dense (for a
positive symmetric operator this is essential self-adjointness of `N` on `D`), `H` relatively
bounded by `N` and `|⟪x, i[H, N] x⟫| ≤ c ⟪x, N x⟫` on `D`.  Then `H` is essentially
self-adjoint on `D`. -/
theorem essentiallySelfAdjointOn_of_farisLavine_dense [CompleteSpace F]
    (H N : D →ₗ[ℂ] F) (a b c : ℝ)
    (hD : Dense (D : Set F))
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNdense : Dense (Set.range fun x : D => N x + (x : F)))
    (hrel : ∀ x : D, ‖H x‖ ≤ a * ‖N x‖ + b * ‖(x : F)‖)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    EssentiallySelfAdjointOn D H := by
  set d : ℝ := c + 1 with hdd
  have hdpos : 0 < d := by simp [hdd]; linarith
  have hdabs : |d| = d := abs_of_pos hdpos
  have hd0 : d ≠ 0 := ne_of_gt hdpos
  have hdgt : c < 2 * |d| := by rw [hdabs, hdd]; linarith
  have hplus : DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) :=
    deficiencyTrivialAt_of_farisLavine_dense H N a b c d hD hH hN hc hNpos hNdense hrel hcomm hdgt
  have hminus : DeficiencyTrivialAt D H (((-d : ℝ) : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_farisLavine_dense H N a b c (-d) hD hH hN hc hNpos hNdense hrel
      hcomm ?_
    rwa [abs_neg]
  have hconj : starRingEnd ℂ ((d : ℂ) * Complex.I) = ((-d : ℝ) : ℂ) * Complex.I := by
    simp
  have hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) :=
    dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (by rw [hconj]; exact hminus)
  exact ⟨deficiencyTrivialAt_of_dense_range H hH d hd0 Complex.I (by simp) hdense hplus,
    deficiencyTrivialAt_of_dense_range H hH d hd0 (-Complex.I) (by simp) hdense hplus⟩

/-! ## Essential self-adjointness of a positive `N` gives dense range of `N + 1` -/

/-- For a **positive** symmetric operator, essential self-adjointness on `D` implies that
`(N + 1) D` is dense.  (So the density hypothesis of
`essentiallySelfAdjointOn_of_farisLavine_dense` is exactly essential self-adjointness of `N`.) -/
theorem dense_range_add_one_of_esa_of_pos [CompleteSpace F] (N : D →ₗ[ℂ] F)
    (hN : SymmetricOn D N) (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hesa : EssentiallySelfAdjointOn D N) :
    Dense (Set.range fun x : D => N x + (x : F)) := by
  have hI : Dense (Set.range fun x : D => N x - (-Complex.I) • (x : F)) :=
    dense_range_of_deficiencyTrivialAt N (-Complex.I) (by simpa using hesa.1)
  -- `range (N + 1)` is a submodule; show its orthogonal complement is trivial
  set K : Submodule ℂ F := LinearMap.range (N + D.subtype) with hK
  have hset : (K : Set F) = Set.range fun x : D => N x + (x : F) := by
    ext u; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp⟩
  rw [← hset, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_orthogonal] at hw
  have hw' : ∀ v : D, (inner ℂ (N v + (v : F)) w : ℂ) = 0 := fun v =>
    hw _ ⟨v, by simp⟩
  -- approximate `w` by `(N + i) v_n`
  have hex : ∀ n : ℕ, ∃ v : D, ‖N v + Complex.I • (v : F) - w‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, ⟨v, rfl⟩, hy⟩ :=
      hI.exists_dist_lt w (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    refine ⟨v, ?_⟩
    rw [← dist_eq_norm, dist_comm]
    simpa [sub_neg_eq_add] using hy
  choose v hv using hex
  set e : ℕ → F := fun n => w - (N (v n) + Complex.I • (v n : F)) with he
  have he_le : ∀ n, ‖e n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n; simp only [he]; rw [norm_sub_rev]; exact (hv n).le
  have hinv_le : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set M : ℝ := ‖w‖ + 1 with hM
  have hbd : ∀ n, ‖N (v n)‖ ≤ M ∧ ‖(v n : F)‖ ≤ M := by
    intro n
    have hnorm : ‖N (v n) + Complex.I • (v n : F)‖ ^ 2 = ‖N (v n)‖ ^ 2 + ‖(v n : F)‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
      have him : (inner ℂ (N (v n)) (v n : F) : ℂ).im = 0 := inner_apply_self_im N hN (v n)
      simp [him]
    have h1 : N (v n) + Complex.I • (v n : F) = w - e n := by simp [he]
    have h2 : ‖N (v n) + Complex.I • (v n : F)‖ ≤ M := by
      rw [h1]
      calc ‖w - e n‖ ≤ ‖w‖ + ‖e n‖ := norm_sub_le _ _
        _ ≤ M := by rw [hM]; linarith [he_le n, hinv_le n]
    have hM0 : 0 ≤ M := by positivity
    have h3 : ‖N (v n)‖ ^ 2 + ‖(v n : F)‖ ^ 2 ≤ M ^ 2 := by
      rw [← hnorm]; gcongr
    constructor
    · nlinarith [norm_nonneg (N (v n)), sq_nonneg ‖(v n : F)‖]
    · nlinarith [norm_nonneg (v n : F), sq_nonneg ‖N (v n)‖]
  -- the key identity `0 = ⟪(N+1) v, (N+i) v⟫ + ⟪(N+1) v, e⟫`
  have hkey : ∀ n, ‖N (v n)‖ ^ 2 + ‖(v n : F)‖ ^ 2 ≤ 4 * M * (1 / ((n : ℝ) + 1)) := by
    intro n
    set x := v n
    have h0 := hw' x
    have hw2 : w = N x + Complex.I • (x : F) + e n := by simp [he, x]
    rw [hw2, inner_add_right, inner_add_right, inner_smul_right, inner_add_left,
      inner_add_left] at h0
    have hq : (inner ℂ (x : F) (N x) : ℂ).im = 0 := quadForm_im N hN x
    have hq' : (inner ℂ (N x) (x : F) : ℂ).im = 0 := inner_apply_self_im N hN x
    have hNN : (inner ℂ (N x) (N x) : ℂ) = ((‖N x‖ ^ 2 : ℝ) : ℂ) := by
      simp
    have hxx : (inner ℂ (x : F) (x : F) : ℂ) = ((‖(x : F)‖ ^ 2 : ℝ) : ℂ) := by
      simp
    have hqq : (inner ℂ (x : F) (N x) : ℂ).re = (inner ℂ (N x) (x : F) : ℂ).re := by
      rw [← inner_conj_symm (𝕜 := ℂ) (N x) (x : F), Complex.conj_re]
    set r : ℂ := inner ℂ (N x + (x : F)) (e n) with hr
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    rw [hNN, hxx] at hre him
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      hq, hq'] at hre him
    have hpos : 0 ≤ (inner ℂ (N x) (x : F) : ℂ).re := by
      have := hNpos x; simp only [quadForm] at this; linarith
    have hE : ‖r‖ ≤ 2 * M * (1 / ((n : ℝ) + 1)) := by
      calc ‖r‖ ≤ ‖N x + (x : F)‖ * ‖e n‖ := norm_inner_le_norm _ _
        _ ≤ (2 * M) * (1 / ((n : ℝ) + 1)) := by
            apply mul_le_mul _ (he_le n) (norm_nonneg _) (by positivity)
            calc ‖N x + (x : F)‖ ≤ ‖N x‖ + ‖(x : F)‖ := norm_add_le _ _
              _ ≤ 2 * M := by linarith [(hbd n).1, (hbd n).2]
    have h1 := (abs_le.mp (le_trans (Complex.abs_re_le_norm r) hE)).1
    have h2 := (abs_le.mp (le_trans (Complex.abs_im_le_norm r) hE)).1
    nlinarith
  -- hence `(N + i) v_n → 0`, and also `→ w`
  have hlim0 : Tendsto (fun n => N (v n) + Complex.I • (v n : F)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hK : Tendsto (fun n : ℕ => Real.sqrt (4 * M * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 * M))
      simpa using (Real.continuous_sqrt.tendsto 0).comp (by simpa using this)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hK
    apply Real.le_sqrt_of_sq_le
    have hnorm : ‖N (v n) + Complex.I • (v n : F)‖ ^ 2 = ‖N (v n)‖ ^ 2 + ‖(v n : F)‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
      have him : (inner ℂ (N (v n)) (v n : F) : ℂ).im = 0 := inner_apply_self_im N hN (v n)
      simp [him]
    rw [hnorm]; exact hkey n
  have hlimw : Tendsto (fun n => N (v n) + Complex.I • (v n : F)) atTop (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hv n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_nhds_unique hlimw hlim0

/-! ## The square comparison `N = H² + E` -/

/-- The quadratic form of the square comparison: `⟪x, (H² + E) x⟫ = ‖H x‖² + ⟪x, E x⟫`. -/
theorem quadForm_square_comparison (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (x : D) :
    quadForm ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x
      = ‖(D.subtype ∘ₗ H₀) x‖ ^ 2 + quadForm E x := by
  have h1 : (inner ℂ (x : F) ((D.subtype ∘ₗ H₀) (H₀ x)) : ℂ)
      = inner ℂ ((D.subtype ∘ₗ H₀) x) ((D.subtype ∘ₗ H₀) x) := by
    rw [← hH x (H₀ x)]; rfl
  have h2 : (inner ℂ ((D.subtype ∘ₗ H₀) x) ((D.subtype ∘ₗ H₀) x) : ℂ).re
      = ‖(D.subtype ∘ₗ H₀) x‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((D.subtype ∘ₗ H₀) x)
  have h3 : ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x = (D.subtype ∘ₗ H₀) (H₀ x) + E x := rfl
  rw [quadForm, h3, inner_add_right, Complex.add_re, h1, h2]
  rfl

/-- **The exact commutation relation of the square comparison**: `H` commutes with `H²`, so
`⟪x, i[H, H² + E] x⟫ = ⟪x, i[H, E] x⟫`. -/
theorem commForm_square_comparison (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (x : D) :
    commForm (D.subtype ∘ₗ H₀) ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x
      = commForm (D.subtype ∘ₗ H₀) E x := by
  have hsq : (inner ℂ ((D.subtype ∘ₗ H₀) x) ((D.subtype ∘ₗ H₀) (H₀ x)) : ℂ).im = 0 :=
    quadForm_im (D.subtype ∘ₗ H₀) hH (H₀ x)
  have h3 : ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x = (D.subtype ∘ₗ H₀) (H₀ x) + E x := rfl
  rw [commForm_eq, commForm_eq, h3, inner_add_right, Complex.add_im, hsq, zero_add]

/-- The square comparison `H² + E` is symmetric. -/
theorem symmetricOn_square_comparison (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (hE : SymmetricOn D E) :
    SymmetricOn D ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) := by
  intro x y
  have h3 : ∀ z : D, ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) z = (D.subtype ∘ₗ H₀) (H₀ z) + E z :=
    fun z => rfl
  rw [h3, h3, inner_add_left, inner_add_right, hE x y, hH (H₀ x) y, ← hH x (H₀ y)]
  rfl

/-- The relative bound of the square comparison: `‖H x‖ ≤ ‖(H² + E) x‖ + ‖x‖` when `E ≥ 0`. -/
theorem norm_le_square_comparison (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (hEpos : ∀ x : D, 0 ≤ quadForm E x) (x : D) :
    ‖(D.subtype ∘ₗ H₀) x‖ ≤ ‖((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x‖ + ‖(x : F)‖ := by
  set N := (D.subtype ∘ₗ H₀) ∘ₗ H₀ + E
  have h1 : ‖(D.subtype ∘ₗ H₀) x‖ ^ 2 ≤ quadForm N x := by
    rw [quadForm_square_comparison H₀ E hH]; linarith [hEpos x]
  have h2 : quadForm N x ≤ ‖(x : F)‖ * ‖N x‖ := by
    calc quadForm N x ≤ ‖(inner ℂ (x : F) (N x) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖(x : F)‖ * ‖N x‖ := norm_inner_le_norm _ _
  have h3 : ‖(D.subtype ∘ₗ H₀) x‖ ^ 2 ≤ (‖N x‖ + ‖(x : F)‖) ^ 2 := by
    nlinarith [norm_nonneg (N x), norm_nonneg (x : F)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-- **Faris–Lavine with the comparison operator `N = H² + E`.**  Let `H = ι ∘ H₀` be symmetric
on `D` and map `D` into itself (`H₀ : D → D`), and let `E ≥ 0` be symmetric on `D` with
`|⟪x, i[H, E] x⟫| ≤ c ⟪x, E x⟫`.  Put `N = H² + E`.  Then

* `⟪x, N x⟫ = ‖H x‖² + ⟪x, E x⟫ ≥ 0`,
* `‖H x‖ ≤ ‖N x‖ + ‖x‖`,
* `⟪x, i[H, N] x⟫ = ⟪x, i[H, E] x⟫` — the square commutes with `H` exactly,

so the Faris–Lavine hypotheses hold with the same constant `c`, and `H` is essentially
self-adjoint on `D` as soon as `N` is. -/
theorem essentiallySelfAdjointOn_of_square_comparison [CompleteSpace F]
    (hD : Dense (D : Set F)) (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F) (c : ℝ)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (hE : SymmetricOn D E) (hc : 0 ≤ c)
    (hEpos : ∀ x : D, 0 ≤ quadForm E x)
    (hcomm : ∀ x : D, |commForm (D.subtype ∘ₗ H₀) E x| ≤ c * quadForm E x)
    (hNesa : EssentiallySelfAdjointOn D ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E)) :
    EssentiallySelfAdjointOn D (D.subtype ∘ₗ H₀) := by
  set H : D →ₗ[ℂ] F := D.subtype ∘ₗ H₀ with hHdef
  set N : D →ₗ[ℂ] F := H ∘ₗ H₀ + E with hNdef
  have hHx : ∀ x : D, H x = ((H₀ x : D) : F) := fun x => rfl
  have hNx : ∀ x : D, N x = H (H₀ x) + E x := fun x => rfl
  have hqN : ∀ x : D, quadForm N x = ‖H x‖ ^ 2 + quadForm E x :=
    quadForm_square_comparison H₀ E hH
  have hN : SymmetricOn D N := symmetricOn_square_comparison H₀ E hH hE
  have hNpos : ∀ x : D, 0 ≤ quadForm N x := fun x => by
    rw [hqN]; have := hEpos x; positivity
  -- the relative bound
  have hrel : ∀ x : D, ‖H x‖ ≤ 1 * ‖N x‖ + 1 * ‖(x : F)‖ := fun x => by
    simpa using norm_le_square_comparison H₀ E hH hEpos x
  -- the commutator: the square drops out
  have hcommN : ∀ x : D, |commForm H N x| ≤ c * quadForm N x := by
    intro x
    have hcf : commForm H N x = commForm H E x := commForm_square_comparison H₀ E hH x
    rw [hcf]
    have hle : quadForm E x ≤ quadForm N x := by rw [hqN]; nlinarith [sq_nonneg ‖H x‖]
    exact le_trans (hcomm x) (mul_le_mul_of_nonneg_left hle hc)
  exact essentiallySelfAdjointOn_of_farisLavine_dense H N 1 1 c hD hH hN hc hNpos
    (dense_range_add_one_of_esa_of_pos N hN hNpos hNesa) hrel hcommN

end BookProof.FarisLavine
