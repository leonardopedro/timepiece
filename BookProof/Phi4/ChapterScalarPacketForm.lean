import BookProof.Phi4.ChapterScalarFourierIntegral

/-!
# The two-amplitude packet form for the scalar λφ⁴ wall

`PHI4_FORMALIZATION_PLAN.md`, “Next proofs for the Lean4 specialist”, item 2, asks for the
finite *packet amplitude* model on a common Mehler core: the spatial Gram matrix, the dual
kinetic metric, the gradient matrix and the wall Gram matrix, together with the matrix element
that changes both occupations by two.

Two real Schwartz packets `χ₀, χ₁` on the continuous momentum space `V` span the two-amplitude
model.  Every object below is an integral over `V`; nothing is discretized, and the packets are
carried as complex Schwartz functions so the Fourier chapter's API applies (the intended packets
are real-valued).

* `packetPair`, `packetGram` — the spatial Gram matrix `Gᵢⱼ = ∫ χᵢ χⱼ`;
* `packetKinetic`, `packetKineticMat` — the kinetic Gram matrix `Kᵢⱼ = ½ Σ_m ∫ ∂_m χᵢ ∂_m χⱼ`
  in an orthonormal frame, and the dual metric `G⁻¹ K` with the identity `G · (G⁻¹K) = K`;
* `packetGradient` — the directional gradient matrices `Dᵢⱼ(m) = ∫ χᵢ ∂_m χⱼ`;
* `packetWall` — the localized double-well Gram matrix
  `Wᵢⱼ = (λ/4) ∫ χᵢ χⱼ (Φ² − v²)²`;
* `packetMixed` — the both-occupations-by-two element `(λ/4) ∫ χ₀² χ₁²`, proved to be the
  ordered product of the two squared packets, with its Gram-normalized form invariant under
  independent rescalings of the packets.

## Boundary

This is the finite *classical* packet form.  No quantum form is built here: there is no Fock
space, no domain, no positivity of `K + W` and no convergence of the packet model to the
continuum.  Those are items 3 and 4 of the plan.
-/

namespace BookProof.Phi4

open MeasureTheory SchwartzMap
open BookProof.NsAdvectionConvolution LineDeriv

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ## The spatial Gram matrix -/

/-- The unconjugated `L²` pairing of two (real) packets. -/
def packetPair (f χ : 𝓢(V, ℂ)) : ℂ := ∫ x, f x * χ x

/-- The pairing of two Schwartz packets is integrable. -/
theorem integrable_packet_mul (f χ : 𝓢(V, ℂ)) : Integrable (fun x => f x * χ x) := by
  have h : (fun x => f x * χ x)
      = fun x => (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f χ) x := by
    ext x
    simp [SchwartzMap.pairing_apply_apply]
  rw [h]
  exact (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f χ).integrable

/-- The packet pairing is symmetric. -/
theorem packetPair_comm (f χ : 𝓢(V, ℂ)) : packetPair f χ = packetPair χ f := by
  rw [packetPair, packetPair]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- The packet pairing scales by the product of the scalar factors. -/
theorem packetPair_smul_smul (c d : ℂ) (f χ : 𝓢(V, ℂ)) :
    packetPair (c • f) (d • χ) = c * d * packetPair f χ := by
  have h : (fun x => (c • f) x * (d • χ) x) = fun x => c * d * (f x * χ x) := by
    ext x
    simp only [SchwartzMap.smul_apply, smul_eq_mul]
    ring
  rw [packetPair, h, integral_const_mul]
  rfl

/-- The two packets as a family indexed by `Fin 2`. -/
def packetFamily (χ₀ χ₁ : 𝓢(V, ℂ)) : Fin 2 → 𝓢(V, ℂ) := ![χ₀, χ₁]

/-- **The spatial Gram matrix** `Gᵢⱼ = ⟪χᵢ, χⱼ⟫` of the two packets. -/
def packetGram (χ₀ χ₁ : 𝓢(V, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => packetPair (packetFamily χ₀ χ₁ i) (packetFamily χ₀ χ₁ j)

@[simp] theorem packetGram_apply (χ₀ χ₁ : 𝓢(V, ℂ)) (i j : Fin 2) :
    packetGram χ₀ χ₁ i j = packetPair (packetFamily χ₀ χ₁ i) (packetFamily χ₀ χ₁ j) := rfl

/-- The Gram matrix is symmetric, because the packet pairing is. -/
theorem packetGram_isSymm (χ₀ χ₁ : 𝓢(V, ℂ)) : (packetGram χ₀ χ₁).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [packetGram, packetFamily, packetPair_comm]

/-! ## The kinetic metric and its dual -/

/-- **The kinetic Gram matrix** in an orthonormal frame:
`K(f, χ) = ½ Σ_m ∫ (∂_m f) (∂_m χ)`. -/
def packetKinetic {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (f χ : 𝓢(V, ℂ)) : ℂ :=
  (1 / 2 : ℂ) * ∑ m : ι,
    ∫ x, (∂_{b m} f : 𝓢(V, ℂ)) x * (∂_{b m} χ : 𝓢(V, ℂ)) x

/-- The kinetic metric is symmetric. -/
theorem packetKinetic_comm {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (f χ : 𝓢(V, ℂ)) : packetKinetic b f χ = packetKinetic b χ f := by
  simp only [packetKinetic]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- The kinetic Gram matrix of the two packets. -/
def packetKineticMat {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (χ₀ χ₁ : 𝓢(V, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => packetKinetic b (packetFamily χ₀ χ₁ i) (packetFamily χ₀ χ₁ j)

/-- The kinetic matrix is symmetric. -/
theorem packetKineticMat_isSymm {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (χ₀ χ₁ : 𝓢(V, ℂ)) : (packetKineticMat b χ₀ χ₁).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, packetKineticMat, Matrix.of_apply]
  exact packetKinetic_comm b _ _

/-- **The dual kinetic metric** `G⁻¹ K`: the kinetic form in the amplitude coordinates dual
to the packet coefficients. -/
def packetDualKinetic {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (χ₀ χ₁ : 𝓢(V, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (packetGram χ₀ χ₁)⁻¹ * packetKineticMat b χ₀ χ₁

/-- **The dual metric is the inverse of the Gram matrix applied to the kinetic matrix**:
whenever the packets are linearly independent (`det G` a unit), `G · (G⁻¹K) = K`.  This is
the statement that the packet masses and the kinetic form are transported together rather
than projected separately. -/
theorem packetGram_mul_packetDualKinetic {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (χ₀ χ₁ : 𝓢(V, ℂ))
    (h : IsUnit (packetGram χ₀ χ₁).det) :
    packetGram χ₀ χ₁ * packetDualKinetic b χ₀ χ₁ = packetKineticMat b χ₀ χ₁ := by
  rw [packetDualKinetic, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.one_mul]

/-! ## The gradient matrix -/

/-- **The gradient matrix in the direction `m`**: `Dᵢⱼ(m) = ∫ χᵢ ∂_m χⱼ`. -/
def packetGradient (m : V) (χ₀ χ₁ : 𝓢(V, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    ∫ x, packetFamily χ₀ χ₁ i x * (∂_{m} (packetFamily χ₀ χ₁ j) : 𝓢(V, ℂ)) x

/-! ## The wall Gram matrix -/

/-- **The localized double-well Gram matrix** of the two packets against a profile `Φ`:
`Wᵢⱼ = (λ/4) ∫ χᵢ χⱼ (Φ² − v²)²`.  This is the quadratic form of the localized wall
`localizedWall`, with the full quartic weight kept in one piece. -/
def packetWall (lam v : ℝ) (Φ χ₀ χ₁ : 𝓢(V, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => ((lam : ℂ) / 4) *
    ∫ x, packetFamily χ₀ χ₁ i x * packetFamily χ₀ χ₁ j x *
      ((Φ x) ^ 2 - ((v : ℂ)) ^ 2) ^ 2

/-- The wall matrix is symmetric. -/
theorem packetWall_isSymm (lam v : ℝ) (Φ χ₀ χ₁ : 𝓢(V, ℂ)) :
    (packetWall lam v Φ χ₀ χ₁).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, packetWall, Matrix.of_apply]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-! ## The mixed matrix element changing both occupations by two -/

/-- **The both-occupations-by-two matrix element** `(λ/4) ∫ χ₀² χ₁²`.  This is the
coefficient that multiplies `a²b²` in the wall energy of a two-amplitude packet
`a χ₀ + b χ₁`; it changes each packet's occupation by two. -/
def packetMixed (lam : ℝ) (χ₀ χ₁ : 𝓢(V, ℂ)) : ℂ :=
  ((lam : ℂ) / 4) * ∫ x, (χ₀ x) ^ 2 * (χ₁ x) ^ 2

/-- The mixed element is symmetric in the two packets. -/
theorem packetMixed_comm (lam : ℝ) (χ₀ χ₁ : 𝓢(V, ℂ)) :
    packetMixed lam χ₀ χ₁ = packetMixed lam χ₁ χ₀ := by
  rw [packetMixed, packetMixed]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- **The mixed element is the full ordered product before projection**: the product of the
two squared packets is the square of their product, so the coefficient keeps both factors
`χ₀²` and `χ₁²` rather than a projected or normal-ordered contraction. -/
theorem packetMixed_eq_ordered_product (lam : ℝ) (χ₀ χ₁ : 𝓢(V, ℂ)) :
    packetMixed lam χ₀ χ₁ = ((lam : ℂ) / 4) * ∫ x, (χ₀ x * χ₁ x) ^ 2 := by
  rw [packetMixed]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- The mixed element scales by the square of the product of the packet scalings. -/
theorem packetMixed_smul (lam : ℝ) (c d : ℂ) (χ₀ χ₁ : 𝓢(V, ℂ)) :
    packetMixed lam (c • χ₀) (d • χ₁) = (c * d) ^ 2 * packetMixed lam χ₀ χ₁ := by
  have h : (fun x => ((c • χ₀) x) ^ 2 * ((d • χ₁) x) ^ 2)
      = fun x => (c * d) ^ 2 * ((χ₀ x) ^ 2 * (χ₁ x) ^ 2) := by
    ext x
    simp only [SchwartzMap.smul_apply, smul_eq_mul]
    ring
  rw [packetMixed, packetMixed, h, integral_const_mul]
  ring

/-- **The Gram-normalized mixed element**: the matrix element divided by both packet masses. -/
def packetNormalizedMixed (lam : ℝ) (χ₀ χ₁ : 𝓢(V, ℂ)) : ℂ :=
  packetMixed lam χ₀ χ₁ / (packetPair χ₀ χ₀ * packetPair χ₁ χ₁)

/-- **The normalized mixed element is invariant under independent rescalings of the packets.**
This is the Gram normalization the plan asks to retain: the coefficient belongs to the
normalized packets, not to the raw profile functions. -/
theorem packetNormalizedMixed_smul (lam : ℝ) (c d : ℂ) (χ₀ χ₁ : 𝓢(V, ℂ))
    (hc : c ≠ 0) (hd : d ≠ 0)
    (h₀ : packetPair χ₀ χ₀ ≠ 0) (h₁ : packetPair χ₁ χ₁ ≠ 0) :
    packetNormalizedMixed lam (c • χ₀) (d • χ₁) = packetNormalizedMixed lam χ₀ χ₁ := by
  rw [packetNormalizedMixed, packetNormalizedMixed, packetMixed_smul,
    packetPair_smul_smul, packetPair_smul_smul]
  have hc' : c * c ≠ 0 := mul_ne_zero hc hc
  have hd' : d * d ≠ 0 := mul_ne_zero hd hd
  field_simp

end

end BookProof.Phi4
