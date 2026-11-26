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
theorem rayleigh_error {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {R A : F →L[ℂ] F} {ε : ℝ}
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

section RayleighEdges

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Upper edge tested on every unit vector in K. It can be a threshold. -/
def UpperEdgeOn (R : F →L[ℂ] F) (K : Submodule ℂ F) (μ : ℝ) : Prop :=
  IsLUB (Set.range fun x : {v : F // v ∈ K ∧ ‖v‖ = 1} => (inner ℂ (x : F) (R x)).re) μ

theorem upperEdgeOn_stability {R A : F →L[ℂ] F} {K : Submodule ℂ F} {μ est ε : ℝ}
    (hR : UpperEdgeOn R K μ) (hA : UpperEdgeOn A K est) (herr : ‖R - A‖ ≤ ε) :
    |μ - est| ≤ ε :=
  upper_edge_error hR hA (fun x => rayleigh_error herr x.property.2)

/-- Pass from a full-space rank-uniform resolvent bound to a rank-uniform mass error
using the full normalized Rayleigh sets of the same operator and its reconstructions.
For an excitation mass, the caller identifies R with the physical shifted inverse and
ground with its entire ground subspace. An approximate ground requires projection control. -/
theorem uniform_mass_error_of_rayleigh_edges {R : F →L[ℂ] F} {A : ℕ → F →L[ℂ] F}
    {ground : Submodule ℂ F} {admitted : Set ℕ} {est₀ est₁ : ℕ → ℝ} {μ₀ μ₁ s κ ε u : ℝ}
    (hs : 0 ≤ s) (he : 0 ≤ ε) (hu : ε < u)
    (h₀ : UpperEdgeOn R ⊤ μ₀) (h₁ : UpperEdgeOn R groundᗮ μ₁)
    (herr : ∀ m ∈ admitted, ‖R - A m‖ ≤ ε)
    (head : ∀ m ∈ admitted, UpperEdgeOn (A m) ⊤ (est₀ m) ∧ u ≤ est₀ m)
    (rest : ∀ m ∈ admitted, UpperEdgeOn (A m) groundᗮ (est₁ m) ∧ u ≤ est₁ m) :
    ∀ m ∈ admitted,
      |(s * (1 / μ₁ - κ) - s * (1 / μ₀ - κ)) -
        (s * (1 / est₁ m - κ) - s * (1 / est₀ m - κ))| ≤
        2 * (s * ε / (u * (u - ε))) :=
  uniform_mass_error hs he hu
    (fun m hm => ⟨(head m hm).2, upperEdgeOn_stability h₀ (head m hm).1 (herr m hm)⟩)
    (fun m hm => ⟨(rest m hm).2, upperEdgeOn_stability h₁ (rest m hm).1 (herr m hm)⟩)

end RayleighEdges

section EnergyProjection

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- With R = T* T, the ideal energy-space Galerkin error is the square of the
entire omitted map. For a positive shifted Hamiltonian T is its inverse square root.
The projection acts on the image of the trial space in the energy norm. -/
theorem energy_projection_error (T : F →L[ℂ] F) (U : Submodule ℂ F)
    [U.HasOrthogonalProjection] :
    ‖star T * T - star T * U.starProjection * T‖ = ‖Uᗮ.starProjection * T‖ ^ 2 := by
  have heq : star T * T - star T * U.starProjection * T =
      star (Uᗮ.starProjection * T) * (Uᗮ.starProjection * T) := by
    rw [star_mul, (isSelfAdjoint_starProjection Uᗮ).star_eq, U.starProjection_orthogonal']
    noncomm_ring
    rw [← mul_assoc U.starProjection U.starProjection T,
      U.isIdempotentElem_starProjection.eq]
    module
  rw [heq, CStarRing.norm_star_mul_self, sq]

/-- For nested trial spaces the maximum ideal resolvent error actually decreases
weakly with rank, even when the omitted operator fails to converge to zero in norm. -/
theorem energy_projection_error_antitone (T : F →L[ℂ] F) {U V : Submodule ℂ F}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) :
    ‖star T * T - star T * V.starProjection * T‖ ≤
      ‖star T * T - star T * U.starProjection * T‖ := by
  have hV := energy_projection_error T V
  have hU := energy_projection_error T U
  rw [hV, hU]
  have hcomp : Vᗮ.starProjection * Uᗮ.starProjection = Vᗮ.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (Submodule.orthogonal_le h)
  have hn : ‖Vᗮ.starProjection * T‖ ≤ ‖Uᗮ.starProjection * T‖ := calc
    _ = ‖Vᗮ.starProjection * (Uᗮ.starProjection * T)‖ := by rw [← mul_assoc, hcomp]
    _ ≤ ‖Vᗮ.starProjection‖ * ‖Uᗮ.starProjection * T‖ := norm_mul_le _ _
    _ ≤ 1 * ‖Uᗮ.starProjection * T‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Submodule.starProjection_norm_le (K := Vᗮ)
    _ = _ := one_mul _
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- An implementation may deviate from the variational solve at each rank. A uniform
bound on that deviation adds once to the initial whole-space error. -/
theorem inexact_energy_projection_envelope (T A : F →L[ℂ] F) {U V : Submodule ℂ F}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) {δ : ℝ}
    (hδ : ‖star T * V.starProjection * T - A‖ ≤ δ) :
    ‖star T * T - A‖ ≤ ‖Uᗮ.starProjection * T‖ ^ 2 + δ := by
  calc
    ‖star T * T - A‖
        = ‖(star T * T - star T * V.starProjection * T) +
            (star T * V.starProjection * T - A)‖ := by noncomm_ring
    _ ≤ ‖star T * T - star T * V.starProjection * T‖ +
        ‖star T * V.starProjection * T - A‖ := norm_add_le _ _
    _ ≤ ‖star T * T - star T * U.starProjection * T‖ + δ :=
      add_le_add (energy_projection_error_antitone T h) hδ
    _ = _ := by rw [energy_projection_error T U]

/-- A two-sided envelope for ordinary orthogonal compression of a *fixed* bounded
resolvent, including a non-self-adjoint complex shift. The initial subspace controls
both omitted maps. The head error is measured against the operator actually returned. -/
theorem nested_compression_envelope (R A : F →L[ℂ] F) {U V : Submodule ℂ F}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) {δ : ℝ}
    (hδ : ‖V.starProjection * R * V.starProjection - A‖ ≤ δ) :
    ‖R - A‖ ≤ ‖Uᗮ.starProjection * R‖ + ‖R * Uᗮ.starProjection‖ + δ := by
  have hleft : Vᗮ.starProjection * Uᗮ.starProjection = Vᗮ.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (Submodule.orthogonal_le h)
  have hright : Uᗮ.starProjection * Vᗮ.starProjection = Vᗮ.starProjection := by
    simpa only [star_mul, (isSelfAdjoint_starProjection Uᗮ).star_eq,
      (isSelfAdjoint_starProjection Vᗮ).star_eq] using congrArg star hleft
  have hL : ‖Vᗮ.starProjection * R‖ ≤ ‖Uᗮ.starProjection * R‖ := calc
    _ = ‖Vᗮ.starProjection * (Uᗮ.starProjection * R)‖ := by rw [← mul_assoc, hleft]
    _ ≤ ‖Vᗮ.starProjection‖ * ‖Uᗮ.starProjection * R‖ := norm_mul_le _ _
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le (K := Vᗮ)) (norm_nonneg (Uᗮ.starProjection * R))
  have hR : ‖V.starProjection * R * Vᗮ.starProjection‖ ≤ ‖R * Uᗮ.starProjection‖ := calc
    _ = ‖V.starProjection * (R * Uᗮ.starProjection) * Vᗮ.starProjection‖ := by
      simp only [mul_assoc, hright]
    _ ≤ ‖V.starProjection * (R * Uᗮ.starProjection)‖ * ‖Vᗮ.starProjection‖ := norm_mul_le _ _
    _ ≤ ‖V.starProjection * (R * Uᗮ.starProjection)‖ := by
      simpa using mul_le_mul_of_nonneg_left (Submodule.starProjection_norm_le (K := Vᗮ))
        (norm_nonneg (V.starProjection * (R * Uᗮ.starProjection)))
    _ ≤ ‖V.starProjection‖ * ‖R * Uᗮ.starProjection‖ := norm_mul_le _ _
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le (K := V)) (norm_nonneg (R * Uᗮ.starProjection))
  have split : R - A = Vᗮ.starProjection * R + V.starProjection * R * Vᗮ.starProjection +
      (V.starProjection * R * V.starProjection - A) := by
    rw [V.starProjection_orthogonal']
    noncomm_ring
  rw [split]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hL hR)) hδ)

end EnergyProjection

end BookProof.YangMillsResolventBudget
