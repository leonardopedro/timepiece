import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic

/-! # Mixed SU(2) magnetic packet in the continuous Weyl-gauge form

Use the positive magnetic square and the Fourier convention exp(-2π i k·x).
The three amplitudes multiply the profiles f₁, f₂, x₁ f₃ described in softmodes.md.
The integrals below are the separated longitudinal Fourier integrals after the curl
Wronskian cancels. The two transverse Gaussian integrals supply the factor 1/3.
The Mehler amplitude measure is the product of three standard normals.
These packet identities precede the residual Gauss reduction.
-/

namespace BookProof.YangMillsMagneticPacket

open MeasureTheory Complex
open scoped Real

/-- Signed, cubic part of the positive half square in the chosen colour block. -/
theorem magnetic_square (dv dw u v w X Y Z g : ℝ) :
    ((Y * dv - g * X * Z * u * w)^2 + (Z * dw + g * X * Y * u * v)^2) / 2 =
      ((Y * dv)^2 + (Z * dw)^2) / 2 + g * X * Y * Z * u * (v * dw - w * dv) +
        ((g * X * Z * u * w)^2 + (g * X * Y * u * v)^2) / 2 := by ring

/-- Along x₁, the third profile is x₁ times a Gaussian with the same logarithmic
derivative as the second. The differentiated test legs have opposite colour signs. -/
theorem curl_wronskian (x d u v w : ℝ) :
    u * (v * (w + x * d * w) - (x * w) * (d * v)) = u * v * w := by ring

noncomputable def longitudinal (n : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (I * (2 * Real.pi * n : ℝ) * x) *
    Complex.exp (-(3 * Real.pi : ℝ) * (x : ℂ)^2)

/-- The actual Fourier integral of the product envelope, including the 2π derivative units. -/
theorem longitudinal_eq (n : ℝ) :
    longitudinal n = ((1 / 3 : ℝ).sqrt : ℂ) * Real.exp (-Real.pi * n^2 / 3) := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : 0 < ((3 * Real.pi : ℝ) : ℂ).re := by simp; positivity
  unfold longitudinal
  push_cast
  rw [fourierIntegral_gaussian (b := (3 : ℂ) * Real.pi) (by simpa using hb)]
  have hbase : (Real.pi : ℂ) / (3 * Real.pi) = ((1 / 3 : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hroot := Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 1 / 3) (1 / 2)
  rw [← Real.sqrt_eq_rpow] at hroot
  push_cast at hroot
  rw [hbase]
  push_cast
  rw [← hroot]
  congr 2
  field_simp
  ring

noncomputable def weight (n : ℝ) : ℝ :=
  Real.sqrt (1 / 3) / 3 * Real.exp (-Real.pi * n^2 / 3)

/-- Eight signed triples from the three cosines; opposite triples have the same weight. -/
noncomputable def entry : ℝ := (weight 0 + weight 2 + weight 4 + weight 6) / 4

theorem polarized_overlap (n : ℝ) : longitudinal n / 3 = (weight n : ℂ) := by
  rw [longitudinal_eq]
  unfold weight
  push_cast
  ring

theorem weight_neg (n : ℝ) : weight (-n) = weight n := by simp [weight]

/-- The two transverse integrals and the four conjugate-paired longitudinal integrals. -/
theorem integrated_entry :
    (longitudinal 0 / 3 + longitudinal 2 / 3 +
     longitudinal 4 / 3 + longitudinal 6 / 3) / 4 = (entry : ℂ) := by
  simp only [polarized_overlap]
  unfold entry
  push_cast
  ring

/-- Completing the square in the convolution integrates out its relative momentum.
The transferred packet is centred at a+b (cycles per unit length). -/
theorem pair_kernel_square (q k a b : ℝ) :
    (q-a)^2 + (k-q-b)^2 = 2*(q-(k+a-b)/2)^2 + (k-a-b)^2/2 := by ring

/-- Completing the remaining Gaussian overlap produces the weight at c-a-b. -/
theorem overlap_kernel_square (k a b c : ℝ) :
    (k-c)^2 + (k-a-b)^2/2 =
      3*(k-(2*c+a+b)/3)^2/2 + (c-a-b)^2/3 := by ring

/-- Test the polarized convolution separately: reversal changes its value at transfer 3. -/
theorem transfer_sign_control : weight (3-1-2) > weight (3+1-2) := by
  norm_num [weight]
  linarith [Real.pi_pos]

/-- Sum the eight real-packet polarizations after fixing the signs on the
Gaussian centres. q is the convolved first leg; k-q is the second. -/
noncomputable def mixedOverlap (a b c : ℝ) : ℝ :=
  (weight (c-a-b) + weight (c-a+b) + weight (c+a-b) + weight (c+a+b) +
   weight (-c-a-b) + weight (-c-a+b) + weight (-c+a-b) + weight (-c+a+b)) / 8

theorem fourier_channels :
    mixedOverlap 1 2 3 = entry ∧ mixedOverlap 1 3 2 = entry := by
  constructor <;> norm_num [mixedOverlap, entry, weight] <;> ring

/-- The two ordered colour contributions in momentum space. -/
theorem colour_pair_sum : (2 / 3 : ℝ) * entry + entry / 3 = entry := by ring

theorem entry_pos : 0 < entry := by
  unfold entry weight
  positivity

theorem nonabelian_entry_ne_zero {g : ℝ} (hg : g ≠ 0) : g * entry ≠ 0 :=
  mul_ne_zero hg entry_pos.ne'

end BookProof.YangMillsMagneticPacket
