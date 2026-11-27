import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic
import BookProof.ChapterNsAdvectionConvolution

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

/-- Give each spatial profile an adjoint colour vector (the rows of A). The cubic
colour contraction is their scalar triple product in the signed SU(2) basis. -/
noncomputable def colourCubic (g : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  g * entry * A.det

/-- In particular this holds for every constant SO(3) adjoint action on the rows. -/
theorem colourCubic_rotate (g : ℝ) (A R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.det = 1) :
    colourCubic g (A * R) = colourCubic g A := by
  simp [colourCubic, Matrix.det_mul, hR]

/-- On a diagonal colour assignment the nine-coordinate formula recovers the
original three-coordinate packet, including its sign. -/
theorem colourCubic_diagonal (g : ℝ) (v : Fin 3 → ℝ) :
    colourCubic g (Matrix.diagonal v) = g * entry * ∏ i, v i := by
  simp [colourCubic]

/-- Axis restriction of the Schwartz gauge parameter x₃ exp(-π|x|²)T¹.
At zero connection the infinitesimal residual action is dω in these units. -/
theorem residual_gauge_axis :
    HasDerivAt (fun t : ℝ => t * Real.exp (-Real.pi * t^2)) 1 0 := by
  have h : DifferentiableAt ℝ (fun t : ℝ => Real.exp (-Real.pi * t^2)) 0 := by fun_prop
  simpa using (hasDerivAt_id (0 : ℝ)).mul h.hasDerivAt

/-- Every packet in the colour-extended ansatz has A₃=0. Even at zero connection
the third component of the gauge tangent just constructed takes the value one. -/
theorem residual_gauge_leaves_packet {v : ℝ → ℝ} (hthird : ∀ t, v t = 0) :
    v 0 ≠ deriv (fun t : ℝ => t * Real.exp (-Real.pi * t^2)) 0 := by
  rw [hthird, residual_gauge_axis.deriv]
  norm_num

open scoped Matrix

/-- Pointwise first variation of F_ij in a smooth gauge direction. U and V denote
A_i and A_j, V_i and U_j their indicated derivatives, W the parameter and W_i,
W_j its derivatives. Mixed second derivatives of W cancel for a smooth field.
These are evaluations of derivatives on a test field, not independent jet coordinates. -/
theorem curvature_variation (g : ℝ) (U V V_i U_j W W_i W_j : Fin 3 → ℝ) :
    g • ((V_i ⨯₃ W) + (V ⨯₃ W_i) - (U_j ⨯₃ W) - (U ⨯₃ W_j)) +
      g • (((W_i + g • (U ⨯₃ W)) ⨯₃ V) + (U ⨯₃ (W_j + g • (V ⨯₃ W)))) =
      g • ((V_i - U_j + g • (U ⨯₃ V)) ⨯₃ W) := by
  ext i
  fin_cases i <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Contracting the curvature variation with the curvature gives zero for each
magnetic half square, without dropping either the cubic or quartic interaction. -/
theorem magnetic_gauge_variation_zero (g : ℝ) (F W : Fin 3 → ℝ) :
    F ⬝ᵥ (g • (F ⨯₃ W)) = 0 := by simp [dotProduct_smul, dot_self_cross]

/-- On a colour orbit with n perpendicular to the gauge axis e, the two
directions n and n×e are orthonormal. A constant projected rotation leaves an
uncancelled curvature component of size b. -/
theorem projected_orbit_curvature (n e : Fin 3 → ℝ) (hn : n ⬝ᵥ n = 1)
    (he : e ⬝ᵥ e = 1) (hperp : n ⬝ᵥ e = 0) (d b : ℝ) :
    (d • n + b • (n ⨯₃ e)) ⬝ᵥ (d • n + b • (n ⨯₃ e)) = d^2 + b^2 := by
  have hrev : e ⬝ᵥ n = 0 := by rw [dotProduct_comm, hperp]
  have horth : (n ⨯₃ e) ⬝ᵥ n = 0 := by rw [dotProduct_comm, dot_self_cross]
  simp [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, hn, he, hperp,
    hrev, horth, cross_dot_cross, smul_eq_mul, sq]

/-- Exact rotation of a colour vector about the first axis, in the right-cross convention. -/
noncomputable def orbitColour (θ : ℝ) : Fin 3 → ℝ := ![0, Real.cos θ, -Real.sin θ]

theorem orbitColour_derivative (θ : ℝ) :
    HasDerivAt orbitColour (orbitColour θ ⨯₃ ![1, 0, 0]) θ := by
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · simpa [orbitColour, cross_apply, Matrix.cons_val] using hasDerivAt_const θ (0 : ℝ)
  · simpa [orbitColour, cross_apply, Matrix.cons_val] using Real.hasDerivAt_cos θ
  · simpa [orbitColour, cross_apply, Matrix.cons_val] using (Real.hasDerivAt_sin θ).neg

/-- With the actual spatially varying colour rotation, differentiating n
gives the opposite of the longitudinal commutator in each curvature component. -/
theorem local_orbit_curvature (n e : Fin 3 → ℝ) (uᵢ uⱼ wᵢ wⱼ d g τ : ℝ) :
    d • n + (g*τ*(uⱼ*wᵢ-uᵢ*wⱼ)) • (n ⨯₃ e) +
      g • ((uᵢ • n + (τ*wᵢ) • e) ⨯₃ (uⱼ • n + (τ*wⱼ) • e)) = d • n := by
  ext k
  fin_cases k <;> simp [cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Orthogonalizing the gauge-orbit velocity against the two retained transverse
colour rows leaves the longitudinal norm J and the variance of the spatial multiplier.
M is the common profile norm squared, b and a its normalized second and first moments. -/
theorem orbit_metric_square (M J a b g σ dx r : ℝ) :
    M*dx^2 + 2*M*a*g*σ*dx*r + (J + M*b*g^2*r^2)*σ^2 =
      M*(dx + a*g*σ*r)^2 + (J + M*(b-a^2)*g^2*r^2)*σ^2 := by ring

/-- Minimizing over the velocity along one gauge orbit. This is the reduced
metric eigenvalue parallel to the retained colour rotation, times dx². -/
theorem horizontal_metric_minimum (M J a b g r dx σ : ℝ) (hM : 0 < M)
    (hJ : 0 < J) (hb : 0 < b) :
    let D := J + M*b*g^2*r^2
    M*dx^2 + 2*M*a*g*r*dx*σ + D*σ^2 =
      M*dx^2 - (M*a*g*r*dx)^2/D + D*(σ + M*a*g*r*dx/D)^2 := by
  dsimp
  have hd : 0 < J + M*b*g^2*r^2 := by positivity
  field_simp [hd.ne']
  ring

/-- The horizontal metric stays uniformly positive when the multiplier has positive
variance b−a². Orthogonal directions keep their original metric coefficient M. -/
theorem horizontal_metric_bounds (M J a b g r dx : ℝ) (hM : 0 < M)
    (hJ : 0 < J) (hb : 0 < b) :
    let D := J + M*b*g^2*r^2
    M*(1-a^2/b)*dx^2 ≤ M*dx^2 - (M*a*g*r*dx)^2/D ∧
      M*dx^2 - (M*a*g*r*dx)^2/D ≤ M*dx^2 := by
  dsimp
  have hd : 0 < J + M*b*g^2*r^2 := by positivity
  constructor
  · have h : M*dx^2 - (M*a*g*r*dx)^2/(J+M*b*g^2*r^2) - M*(1-a^2/b)*dx^2 =
        M*a^2*J*dx^2/(b*(J+M*b*g^2*r^2)) := by
      field_simp [hb.ne', hd.ne']
      ring
    apply sub_nonneg.mp
    rw [h]
    positivity
  · exact sub_le_self _ (by positivity)

section OneGaugeSlice

variable {α : Type*} [MeasurableSpace α]

/-- The exact colour rotation by gτw about a fixed axis and the shift τ∂w.
The integration label can include the spatial component as well as position. -/
noncomputable def alignedOrbit (w longitudinal : α → ℝ) (g τ : ℝ)
    (A : α → Fin 3 → ℝ) (x : α) : Fin 3 → ℝ :=
  let θ := g * τ * w x
  ![A x 0 + τ * longitudinal x,
    Real.cos θ * A x 1 + Real.sin θ * A x 2,
    -Real.sin θ * A x 1 + Real.cos θ * A x 2]

omit [MeasurableSpace α] in
theorem alignedOrbit_add (w l : α → ℝ) (g s t : ℝ) (A : α → Fin 3 → ℝ) :
    alignedOrbit w l g t (alignedOrbit w l g s A) = alignedOrbit w l g (s+t) A := by
  funext x j
  have h : g*(s+t)*w x = g*s*w x + g*t*w x := by ring
  fin_cases j <;> simp [alignedOrbit, Matrix.cons_val, h, Real.cos_add, Real.sin_add] <;> ring

/-- Read off the gauge direction in the aligned colour. -/
noncomputable def orbitCoordinate (μ : Measure α) (l : α → ℝ) (A : α → Fin 3 → ℝ) : ℝ :=
  (∫ x, l x * A x 0 ∂μ) / ∫ x, l x ^ 2 ∂μ

theorem orbitCoordinate_shift (μ : Measure α) (w l : α → ℝ) (g τ : ℝ) (A : α → Fin 3 → ℝ)
    (hA : Integrable (fun x => l x * A x 0) μ) (hl : Integrable (fun x => l x^2) μ)
    (hJ : (∫ x, l x^2 ∂μ) ≠ 0) :
    orbitCoordinate μ l (alignedOrbit w l g τ A) = orbitCoordinate μ l A + τ := by
  unfold orbitCoordinate
  change (∫ x, l x * (A x 0 + τ * l x) ∂μ) / _ = _
  simp_rw [show ∀ x, l x * (A x 0 + τ * l x) = l x * A x 0 + τ*l x^2 by intro x; ring]
  rw [integral_add hA (hl.const_mul τ), integral_const_mul]
  field_simp

/-- The gauge condition χ=0 picks exactly one representative on this one-parameter
orbit. Its derivative along gauge time is one by the translation formula. -/
theorem unique_aligned_slice (μ : Measure α) (w l : α → ℝ) (g : ℝ) (A : α → Fin 3 → ℝ)
    (hA : Integrable (fun x => l x * A x 0) μ) (hl : Integrable (fun x => l x^2) μ)
    (hJ : (∫ x, l x^2 ∂μ) ≠ 0) :
    ∃! τ : ℝ, orbitCoordinate μ l (alignedOrbit w l g τ A) = 0 := by
  simp_rw [orbitCoordinate_shift μ w l g _ A hA hl hJ]
  exact ⟨-orbitCoordinate μ l A, by ring, fun t ht => by linarith⟩

end OneGaugeSlice

section SchwartzGauge

open SchwartzMap FourierTransform LineDeriv
open BookProof.NsAdvectionConvolution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type*} [Fintype ι]

/-- One component of dω + g[A,ω]. Both colour sums, the signed constants and
the continuous spatial derivative act within the Schwartz class. -/
noncomputable def gaussTangent (A ω : ι → 𝓢(V, ℂ)) (a : ι) (m : V)
    (g : ℝ) (f : ι → ι → ι → ℝ) : 𝓢(V, ℂ) :=
  ∂_{m} (ω a) + ∑ b, ∑ c, ((g * f a b c : ℝ) : ℂ) •
    SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (A b) (ω c)

/-- Exact Fourier kernel on classical test fields. A is one spatial component
of the connection. There is no independent derivative coordinate. -/
theorem gaussTangent_fourier (A ω : ι → 𝓢(V, ℂ)) (a : ι) (m k : V)
    (g : ℝ) (f : ι → ι → ι → ℝ) :
    (𝓕 (gaussTangent A ω a m g f) : 𝓢(V, ℂ)) k =
      (2 * Real.pi * Complex.I * ((inner ℝ k m : ℝ) : ℂ)) * 𝓕 (ω a : V → ℂ) k +
      ∑ b, ∑ c, ((g * f a b c : ℝ) : ℂ) *
        ∫ q, 𝓕 (A b : V → ℂ) q * 𝓕 (ω c : V → ℂ) (k - q) := by
  change ((SchwartzMap.fourierTransformCLM ℂ) (gaussTangent A ω a m g f)) k = _
  simp only [gaussTangent, map_add, map_sum, map_smul, SchwartzMap.add_apply,
    SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul]
  congr 1
  · exact fourier_lineDeriv_apply (ω a) m k
  · apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    change (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (A b) (ω c)) : 𝓢(V, ℂ)) k = _
    rw [SchwartzMap.fourier_coe]
    exact fourier_mul_eq_convolution (A b) (ω c) k

end SchwartzGauge

section GaussianCompression

/-- A single real spatial profile in three continuous coordinates. -/
noncomputable def gaugeProfile (x : Fin 3 → ℝ) : ℝ :=
  ∏ j, Real.exp (-Real.pi * x j ^ 2)

/-- Unnormalized moments for the packet and the multiplier, both with this profile. -/
noncomputable def profileMoment (n : ℕ) : ℝ := ∫ x, gaugeProfile x ^ n

private theorem gaugeProfile_pow (n : ℕ) (x : Fin 3 → ℝ) :
    gaugeProfile x ^ n = ∏ j, Real.exp (-((n : ℝ) * Real.pi) * x j ^ 2) := by
  rw [gaugeProfile, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem gaugeProfile_integrable (n : ℕ) (hn : 0 < n) :
    Integrable (fun x => gaugeProfile x ^ n) := by
  simp only [gaugeProfile_pow]
  exact Integrable.fintype_prod (f := fun (_ : Fin 3) (z : ℝ) =>
    Real.exp (-((n : ℝ) * Real.pi) * z ^ 2)) (fun _ => integrable_exp_neg_mul_sq (by positivity))

theorem profileMoment_eq (n : ℕ) (hn : 0 < n) :
    profileMoment n = Real.sqrt (1 / (n : ℝ)) ^ 3 := by
  simp only [profileMoment, gaugeProfile_pow]
  rw [integral_fintype_prod_volume_eq_pow (ι := Fin 3)
    (fun z : ℝ => Real.exp (-((n : ℝ) * Real.pi) * z ^ 2)), integral_gaussian]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [show Real.pi / ((n : ℝ) * Real.pi) = 1 / (n : ℝ) by
    field_simp [Real.pi_ne_zero]]
  simp

/-- The normalized compression coefficients for multiplication by w and w². -/
noncomputable def compressedMoment (n : ℕ) : ℝ := profileMoment (2 + n) / profileMoment 2

theorem compressedMoment_sq (n : ℕ) :
    compressedMoment n ^ 2 = (2 / (2 + (n : ℝ))) ^ 3 := by
  unfold compressedMoment
  rw [profileMoment_eq _ (by omega), profileMoment_eq _ (by decide)]
  push_cast
  rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 3 2, pow_mul, pow_mul,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  ring_nf

/-- Best scalar approximation to w² by c w. The first term is the squared
residual per unit input norm, the second is the excess for choosing c. -/
theorem gaussian_projection_error (c : ℝ) :
    (∫ x, (gaugeProfile x ^ 2 - c * gaugeProfile x) ^ 2) / profileMoment 2 =
      compressedMoment 2 - compressedMoment 1 ^ 2 + (c - compressedMoment 1) ^ 2 := by
  have h2 := gaugeProfile_integrable 2 (by decide)
  have h3 := gaugeProfile_integrable 3 (by decide)
  have h4 := gaugeProfile_integrable 4 (by decide)
  have hp : profileMoment 2 ≠ 0 := by rw [profileMoment_eq 2 (by decide)]; positivity
  simp_rw [show ∀ w : ℝ, (w ^ 2 - c * w) ^ 2 = w ^ 4 - 2*c * w ^ 3 + c^2 * w^2
    by intro w; ring]
  have hs : Integrable (fun x => gaugeProfile x ^ 4 - (2*c) * gaugeProfile x ^ 3) :=
    h4.sub (h3.const_mul (2*c))
  rw [integral_add hs (h2.const_mul (c^2)), integral_sub h4 (h3.const_mul (2*c)),
    integral_const_mul, integral_const_mul]
  change (profileMoment 4 - 2*c * profileMoment 3 + c^2 * profileMoment 2) /
    profileMoment 2 = _
  unfold compressedMoment
  norm_num
  field_simp [hp]
  ring

/-- Compressing w twice loses a positive squared norm outside the one-profile span.
The same two moments multiply the colour commutator for local parameters wT¹, wT². -/
theorem gaussian_compression_defect :
    compressedMoment 2 - compressedMoment 1 ^ 2 = Real.sqrt (1 / 8) - 8 / 27 ∧
    0 < compressedMoment 2 - compressedMoment 1 ^ 2 := by
  have ha := compressedMoment_sq 1
  have hb := compressedMoment_sq 2
  norm_num at ha hb
  have hp : 0 ≤ compressedMoment 2 := by
    unfold compressedMoment
    rw [profileMoment_eq _ (by decide), profileMoment_eq _ (by decide)]
    positivity
  have hroot := Real.sqrt_sq hp
  rw [hb] at hroot
  rw [← hroot, ha]
  constructor
  · rfl
  · nlinarith [Real.sq_sqrt (show 0 ≤ (1 / 8 : ℝ) by norm_num),
      Real.sqrt_nonneg (1 / 8), sq_nonneg (Real.sqrt (1 / 8) - 8 / 27)]

/-- On the input colour e₂ the ordered commutator of the right rotations about
e₁ and e₂ detects the difference between projecting w² and projecting w twice.
Each application carries one power of the gauge coupling. -/
theorem two_colour_projection_defect (g : ℝ) :
    let x : Fin 3 → ℝ := ![0, 1, 0]
    let e : Fin 3 → ℝ := ![1, 0, 0]
    let rotation := fun (c : ℝ) (axis z : Fin 3 → ℝ) => (g * c) • (z ⨯₃ axis)
    let exactBracket := (g^2 * compressedMoment 2) •
      (((x ⨯₃ x) ⨯₃ e) - ((x ⨯₃ e) ⨯₃ x))
    let a := compressedMoment 1
    (exactBracket - (rotation a e (rotation a x x) - rotation a x (rotation a e x))) 0 =
      -(g^2 * (Real.sqrt (1 / 8) - 8 / 27)) := by
  rw [← gaussian_compression_defect.1]
  simp [cross_apply]
  ring

end GaussianCompression

end BookProof.YangMillsMagneticPacket
