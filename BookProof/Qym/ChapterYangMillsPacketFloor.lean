import BookProof.Phi4.ChapterScalarMomentumGap

/-! # Absolute energy of the unreduced three-profile magnetic packet

The cubic is paired with the X²Y² wall. The leftover Z² stiffness and the
electric terms give an oscillator comparison at every inner Hermite degree.
The coordinates are three amplitudes of smooth spatial profiles.
-/

namespace BookProof.YangMillsPacketFloor

open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.Phi4 MvPolynomial

noncomputable section

abbrev Core := polyGaussCore (d := 3)

/-- Spatial profile coefficients for unit Mehler amplitude variance. -/
structure Coefficients where
  metric : Fin 3 → ℝ
  curl : Fin 3 → ℝ
  cubic : ℝ
  wallXY : ℝ
  wallXZ : ℝ

def pair (j k : Fin 3) (ψ : Core) : L2d 3 :=
  coreX j ((coreRepPoly 3).op (mulOp (X k)) ψ)

/-- A square completion of the magnetic potential at every real field amplitude. -/
theorem complete_magnetic (g K b c X Y Z : ℝ) (hb : b ≠ 0) :
    c * Z^2 / 2 + g*K*X*Y*Z + g^2*b*(X*Y)^2 / 2 =
      (c - K^2 / b) * Z^2 / 2 + (g*b*X*Y + K*Z)^2 / (2*b) := by
  field_simp
  ring

def stiffness (a : Coefficients) (j : Fin 3) : ℝ :=
  a.curl j - if j = 2 then a.cubic^2 / a.wallXY else 0

/-- Form with the mixed magnetic term inside its square. The second quartic
wall is retained. Coupling zero recovers the original quadratic form. -/
def energy (a : Coefficients) (g : ℝ) (ψ : Core) : ℝ :=
  (∑ j, (‖coreP j ψ‖^2 / a.metric j + stiffness a j * ‖coreX j ψ‖^2) / 2) +
    ‖(g * a.wallXY) • pair 0 1 ψ + a.cubic • coreX 2 ψ‖^2 / (2 * a.wallXY) +
    g^2 * a.wallXZ * ‖pair 0 2 ψ‖^2 / 2

/-- Frequency comparison on the entire packet core, for arbitrary coupling. -/
theorem packet_form_floor (a : Coefficients) (g : ℝ) (ν : Fin 3 → ℝ)
    (hm : ∀ j, 0 < a.metric j) (hν : ∀ j, 0 < ν j)
    (hc : ∀ j, a.metric j * ν j ^ 2 ≤ stiffness a j)
    (hb : 0 < a.wallXY) (hw : 0 ≤ a.wallXZ) (ψ : Core) :
    (∑ j, ν j / 2) * ‖(ψ : L2d 3)‖^2 ≤ energy a g ψ := by
  have hj (j : Fin 3) : ν j / 2 * ‖(ψ : L2d 3)‖^2 ≤
      (‖coreP j ψ‖^2 / a.metric j + stiffness a j * ‖coreX j ψ‖^2) / 2 := by
    have h := harmonic_lower_bound j (mul_pos (hm j) (hν j)) ψ
    have hst := mul_le_mul_of_nonneg_right (hc j) (sq_nonneg ‖coreX j ψ‖)
    have hdiv := (le_div_iff₀ (hm j)).2 (show
        (ν j / 2 * ‖(ψ : L2d 3)‖^2) * a.metric j ≤
        (‖coreP j ψ‖^2 + (a.metric j * ν j)^2 * ‖coreX j ψ‖^2) / 2 by linarith only [h])
    calc
      _ ≤ _ := hdiv
      _ = (‖coreP j ψ‖^2 / a.metric j + (a.metric j * ν j^2) * ‖coreX j ψ‖^2) / 2 := by
        field_simp [(hm j).ne']
      _ ≤ _ := by linarith
  unfold energy
  rw [Finset.sum_mul]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  have hxy : 0 ≤ ‖(g * a.wallXY) • pair 0 1 ψ + a.cubic • coreX 2 ψ‖^2 /
      (2 * a.wallXY) := by positivity
  have hxz : 0 ≤ g^2 * a.wallXZ * ‖pair 0 2 ψ‖^2 / 2 := by positivity
  linarith only [hsum, hxy, hxz]

/-- Coefficients read as the exact decimals in qym_magnetic_packet.json. -/
def fixture : Coefficients where
  metric := ![0.17710681565140393, 0.17677669529878676, 0.014067442439954782]
  curl := ![8.091659141541145, 29.02617753310862, 5.175020000724799]
  cubic := 0.0488421330902749521180563611401
  wallXY := 0.03327576139807117
  wallXZ := 0.0012971322602180826

/-- Absolute lower bound with unrestricted Hermite degree on three fixed profiles. -/
theorem fixture_form_floor (g : ℝ) (ψ : Core) : (37 / 2 : ℝ) * ‖(ψ : L2d 3)‖^2 ≤
    energy fixture g ψ := by
  have h := packet_form_floor fixture g ![6, 12, 19]
    (by intro j; fin_cases j <;> norm_num [fixture, Matrix.cons_val])
    (by intro j; fin_cases j <;> norm_num [Matrix.cons_val])
    (by
      intro j
      fin_cases j
      · change (0.17710681565140393 : ℝ) * 6^2 ≤ 8.091659141541145 -
            (if (0 : Fin 3) = 2 then _ else 0)
        rw [if_neg (by decide)]
        norm_num
      · change (0.17677669529878676 : ℝ) * 12^2 ≤ 29.02617753310862 -
            (if (1 : Fin 3) = 2 then _ else 0)
        rw [if_neg (by decide)]
        norm_num
      · change (0.014067442439954782 : ℝ) * 19^2 ≤
            5.175020000724799 - 0.0488421330902749521180563611401^2 / 0.03327576139807117
        norm_num)
    (by norm_num [fixture]) (by norm_num [fixture]) ψ
  have hs : (∑ j : Fin 3, (![6, 12, 19] j : ℝ) / 2) = 37 / 2 := by
    rw [Fin.sum_univ_three]
    change (6 : ℝ) / 2 + 12 / 2 + 19 / 2 = 37 / 2
    norm_num
  simpa only [hs] using h

/-- Pullback of the *whole* spatial profile f to x ↦ f(x/L). The curl has
one spatial derivative, the cubic one derivative, and the walls have none. -/
def widen (a : Coefficients) (L : ℝ) : Coefficients where
  metric j := L^3 * a.metric j
  curl j := L * a.curl j
  cubic := L^2 * a.cubic
  wallXY := L^3 * a.wallXY
  wallXZ := L^3 * a.wallXZ

/-- For three independent centered amplitudes of variance s² the cubic has
zero mean, the two walls have moment s⁴, and each momentum variance is 1/(4s²).
This is the energy of a normalized squeezed Gaussian in the Mehler chart. -/
def gaussianEnergy (a : Coefficients) (g s : ℝ) : ℝ :=
  (∑ j, (1 / (4 * s^2 * a.metric j) + a.curl j * s^2) / 2) +
    g^2 * (a.wallXY + a.wallXZ) * s^4 / 2

/-- Spatial dilation combined with squeezing the amplitude standard deviation by
1/L prices both the kinetic and interaction energies of the trial state. -/
theorem widened_gaussian_energy (a : Coefficients) (g L : ℝ) (hL : 0 < L) :
    gaussianEnergy (widen a L) g (1 / L) = gaussianEnergy a g 1 / L := by
  simp only [gaussianEnergy, widen, one_pow, mul_one, add_div, Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hm : a.metric j = 0
    · simp [hm]
      field_simp [hL.ne']
    · field_simp [hm, hL.ne']
  · field_simp [hL.ne']

/-- No positive constant bounds these trial energies below for every spatial width
at the same bare coupling, even though each fixed profile admits a positive floor. -/
theorem widened_gaussian_below (a : Coefficients) (g : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, 1 ≤ L ∧ gaussianEnergy (widen a L) g (1 / L) < c := by
  let L := 1 + |gaussianEnergy a g 1| / c
  have hL : 1 ≤ L := le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hc.le)
  refine ⟨L, hL, ?_⟩
  rw [widened_gaussian_energy _ _ _ (by linarith), div_lt_iff₀ (by linarith : 0 < L)]
  dsimp [L]
  rw [mul_add, mul_one, show c * (|gaussianEnergy a g 1| / c) = |gaussianEnergy a g 1| by
    field_simp]
  linarith [le_abs_self (gaussianEnergy a g 1)]

/-- Unit-vector energies in a packet trial space, allowing all Hermite degrees. -/
def energies (a : Coefficients) (g : ℝ) (S : Set Core) : Set ℝ :=
  energy a g '' {ψ | ψ ∈ S ∧ ‖(ψ : L2d 3)‖ = 1}

/-- A common seeded Ritz error for the absolute packet edge. The trial set can
change with rank. Only its unit seed and the seed energy ceiling enter the estimate. -/
theorem seeded_ritz_error (a : Coefficients) {S : Set Core} {E Eritz : ℝ}
    (hfloor : ∀ ψ : Core, 37 / 2 * ‖(ψ : L2d 3)‖^2 ≤ energy a 2 ψ)
    (hE : IsGLB (energies a 2 Set.univ) E) (hritz : IsGLB (energies a 2 S) Eritz)
    {seed : Core} (hs : seed ∈ S) (hn : ‖(seed : L2d 3)‖ = 1) (hseed : energy a 2 seed < 32) :
    37 / 2 ≤ E ∧ |Eritz - E| < 27 / 2 ∧ 27 / 2 < E := by
  have hl : 37 / 2 ≤ E := hE.2 (by
    rintro _ ⟨ψ, ⟨_, hnorm⟩, rfl⟩
    simpa only [hnorm, one_pow, mul_one] using hfloor ψ)
  have le_ritz : E ≤ Eritz := hritz.2 (by
    rintro _ ⟨ψ, ⟨_, hnorm⟩, rfl⟩
    exact hE.1 ⟨ψ, ⟨Set.mem_univ _, hnorm⟩, rfl⟩)
  have hu : Eritz ≤ energy a 2 seed := hritz.1 ⟨seed, ⟨hs, hn⟩, rfl⟩
  rw [abs_of_nonneg (sub_nonneg.mpr le_ritz)]
  exact ⟨hl, by linarith, by linarith⟩

end
end BookProof.YangMillsPacketFloor
