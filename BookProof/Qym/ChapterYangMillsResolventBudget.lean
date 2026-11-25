import BookProof.Textbook.ChapterH6
import Mathlib.Tactic.NoncommRing

/-! # Uniform resolvent and mass error bookkeeping for softmodes.md U2–U4

The operator norm prices the entire space. The hypotheses below distinguish a
head reconstruction, the two coupling blocks and an optional tail completion.
A spectral identification of the physical edges remains necessary to apply the
reciprocal estimates to Yang–Mills. -/

namespace BookProof.YangMillsResolventBudget

open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- With P the retained projection and Q its complement the residual consists of
four blocks. X and Y denote lifted head and tail approximations, respectively.
The algebra even works without orthogonality or commutation. -/
theorem full_resolvent_error (R P Q X Y : E →L[ℂ] E) (hsum : P + Q = 1) :
    ‖R - (X + Y)‖ ≤ ‖P * R * P - X‖ + ‖P * R * Q‖ +
      ‖Q * R * P‖ + ‖Q * R * Q - Y‖ := by
  have h : R - (X + Y) =
      (P * R * P - X) + P * R * Q + Q * R * P + (Q * R * Q - Y) := by
    calc
      _ = (P + Q) * R * (P + Q) - (X + Y) := by simp [hsum]
      _ = _ := by noncomm_ring
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)

/-- A fixed minimum order controls every admitted rank. T includes the entire tail,
S solves, O the Gram and transfer defect, F assembly/rounding. Any off-block
contribution must appear in one of these operator-norm budgets. -/
theorem uniform_resolvent_envelope {q : ℕ → ℕ} {q₀ : ℕ} {C D a T S O F : ℝ}
    {err : ℕ → ℝ} {admitted : Set ℕ} (hC : 0 ≤ C) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hq : ∀ m ∈ admitted, q₀ ≤ q m)
    (hb : ∀ m ∈ admitted, err m ≤ sirkBound C D a 1 (q m) + T + S + O + F) :
    ∀ m ∈ admitted, err m ≤ sirkBound C D a 1 q₀ + T + S + O + F := by
  intro m hm
  have h := sirk_error_bound_antitone C D a 1 hC hD zero_le_one ha (hq m hm)
  linarith [hb m hm]

/-- Absolute edge test for the complete positive resolvent, valid also for a threshold. -/
theorem resolvent_norm_lt {R approx : E →L[ℂ] E} {ε cap : ℝ}
    (herr : ‖R - approx‖ ≤ ε) (hmargin : ‖approx‖ + ε < cap) : ‖R‖ < cap := by
  calc
    ‖R‖ = ‖(R - approx) + approx‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _
    _ < cap := by linarith

/-- Stability of the upper Rayleigh edge on a common test family. This works for
a spectral threshold without a maximizing vector. Using it on a ground complement
requires identification of that *whole* physical subspace. -/
theorem upper_edge_error {ι : Type*} {f g : ι → ℝ} {μ est ε : ℝ}
    (hf : IsLUB (Set.range f) μ) (hg : IsLUB (Set.range g) est)
    (herr : ∀ i, |f i - g i| ≤ ε) : |μ - est| ≤ ε := by
  have h₁ : μ ≤ est + ε := by
    apply hf.2
    rintro _ ⟨i, rfl⟩
    have h := hg.1 (Set.mem_range_self i)
    linarith [(abs_le.mp (herr i)).2]
  have h₂ : est ≤ μ + ε := by
    apply hg.2
    rintro _ ⟨i, rfl⟩
    have h := hf.1 (Set.mem_range_self i)
    linarith [(abs_le.mp (herr i)).1]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A full operator-norm enclosure controls every normalized Rayleigh test at once. -/
theorem rayleigh_error {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {R A : F →L[ℂ] F} {ε : ℝ}
    (herr : ‖R - A‖ ≤ ε) {x : F} (hx : ‖x‖ = 1) :
    |(inner ℂ x (R x)).re - (inner ℂ x (A x)).re| ≤ ε := by
  rw [← Complex.sub_re, ← inner_sub_right, ← ContinuousLinearMap.sub_apply]
  calc
    _ ≤ _ := Complex.abs_re_le_norm _
    _ ≤ _ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖R - A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((R-A).le_opNorm _) (norm_nonneg _)
    _ ≤ ε := by simpa [hx] using herr

/-- If the calculated edge stays above a uniform denominator margin u, inversion
loses at most this many energy units. κ cancels in the difference. -/
theorem inverse_energy_error {s κ μ est ε u : ℝ} (hs : 0 ≤ s) (he : 0 ≤ ε)
    (hmargin : ε < u) (hu : u ≤ est) (herr : |μ - est| ≤ ε) :
    |s * (1 / μ - κ) - s * (1 / est - κ)| ≤ s * ε / (u * (u - ε)) := by
  have hμ : u - ε ≤ μ := by have := (abs_le.mp herr).1; linarith
  have hu0 : 0 < u := lt_of_le_of_lt he hmargin
  have hp : 0 < μ := lt_of_lt_of_le (sub_pos.mpr hmargin) hμ
  have ht : 0 < est := lt_of_lt_of_le hu0 hu
  have hd : u * (u - ε) ≤ est * μ := mul_le_mul hu hμ (sub_nonneg.mpr hmargin.le) ht.le
  have hid : s * (1 / μ - κ) - s * (1 / est - κ) = s * (est - μ) / (est * μ) := by
    field_simp
    ring
  rw [hid, abs_div, abs_mul, abs_of_nonneg hs, abs_of_pos (mul_pos ht hp), abs_sub_comm est μ]
  exact div_le_div₀ (mul_nonneg hs he) (mul_le_mul_of_nonneg_left herr hs)
    (mul_pos hu0 (sub_pos.mpr hmargin)) hd

/-- Price both edges above a populated ground. With an exact ground its charge is zero. -/
theorem two_edge_error {E₀ E₁ a₀ a₁ e₀ e₁ : ℝ}
    (h₀ : |E₀ - a₀| ≤ e₀) (h₁ : |E₁ - a₁| ≤ e₁) :
    |(E₁ - E₀) - (a₁ - a₀)| ≤ e₁ + e₀ := by
  rw [show (E₁ - E₀) - (a₁ - a₀) = (E₁ - a₁) - (E₀ - a₀) by ring]
  exact (abs_sub _ _).trans (add_le_add h₁ h₀)

/-- A single bound in energy units for every admitted rank, given independently
identified and ordered resolvent edges. The shift cancels when taking the gap. -/
theorem uniform_mass_error {admitted : Set ℕ} {est₀ est₁ : ℕ → ℝ}
    {μ₀ μ₁ s κ u ε : ℝ} (hs : 0 ≤ s) (he : 0 ≤ ε) (hu : ε < u)
    (h₀ : ∀ m ∈ admitted, u ≤ est₀ m ∧ |μ₀ - est₀ m| ≤ ε)
    (h₁ : ∀ m ∈ admitted, u ≤ est₁ m ∧ |μ₁ - est₁ m| ≤ ε) :
    ∀ m ∈ admitted,
      |(s * (1 / μ₁ - κ) - s * (1 / μ₀ - κ)) -
        (s * (1 / est₁ m - κ) - s * (1 / est₀ m - κ))| ≤
        2 * (s * ε / (u * (u - ε))) := by
  intro m hm
  rw [two_mul]
  exact two_edge_error
    (inverse_energy_error hs he hu (h₀ m hm).1 (h₀ m hm).2)
    (inverse_energy_error hs he hu (h₁ m hm).1 (h₁ m hm).2)

/-- A reported mass exceeds its common energy error only after spectral coverage
has supplied the estimate on the *identified* mass M. -/
theorem positive_margin {M estimate error : ℝ}
    (herr : |M - estimate| ≤ error) (htest : error < estimate) : 0 < M := by
  have := (abs_le.mp herr).1
  linarith

end BookProof.YangMillsResolventBudget
