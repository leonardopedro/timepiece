import BookProof.OSReconstruction.HalfSpaceHilbert

/-!
# The half-space transfer step as a one-sided, discrete-time semigroup

`HalfSpaceHilbert` states its support-preservation hypothesis for a `TimeTranslation`,
i.e. an `ℝ`-parameter *group* `τ ↦ T τ` of linear maps on `Observable`.  No such object exists
in this corpus, and `HalfSpaceLatticeTranslation` shows why the lattice cannot supply one: the
lattice gives a `ℤ`-action (the cyclic cell rotation of a block), and `ℝ → ℤ/16` has no
nontrivial homomorphism.  On top of that, `PreservesPositiveTime` quantifies over *all* real
`τ`, while a transfer step only ever runs forward.

This module weakens the API to what a lattice transfer matrix actually provides: a **one-sided,
`ℕ`-indexed semigroup**

  `T 0 = 1`,   `T (m + n) = T m ∘ T n`,

together with the one-sided forms of the two hypotheses — `PreservesPositiveTimeNat` (a forward
step keeps `𝔄₊` inside itself) and `HsHinvNat` (the OS form does not grow along forward
steps) — and the whole downstream chain up to the descended contraction `P(n)` on `𝔄₊/𝔑₊`.

## Why this is a weakening and not a different theory

`ofTimeTranslation` embeds any `TimeTranslation` into the new structure, and the bridges
`preservesPositiveTimeNat_of_ofTimeTranslation`, `hsEvolNat_ofTimeTranslation` and
`hsHinvNat_of_hsHinv` show that every `ℝ`-time statement is the corresponding `ℕ`-time
statement of its image.  So the new API is a generalization: the old hypotheses still imply the
new ones.

## Contents

* `DiscreteTimeTranslation` — the structure, with `discreteTimeTranslation_zero` and
  `discreteTimeTranslation_semigroup`;
* `ofTimeTranslation` — the embedding of the old API;
* `PreservesPositiveTimeNat`, `hsEvolNat`, `hsEvolNat_coe`, `hsEvolNat_zero`, `hsEvolNat_add`;
* `HsHinvNat`, `hsRadical_invariantNat` (forward steps preserve the null space `𝔑₊`);
* `hsQuotMapNat`, `hsQuotMapNat_mk`, `hsQuotMapNat_contractive`, `hsQuotMapNat_zero`,
  `hsQuotMapNat_add` — the descended one-sided transfer semigroup and its contraction property;
* the three bridges back to the `ℝ`-time API.

## Boundary

The three hypotheses that `HalfSpaceHilbert` leaves open (`PreservesPositiveTime`, `HsHinv`,
`HsSymmetric`) are hypotheses here too; this module changes the *shape* of the API, not the proof
obligations.  What the weaker shape buys is inhabitability: the concrete half-preserving lattice
step of `HalfSpaceLatticeShiftSemigroup` is an instance of `DiscreteTimeTranslation` and does
satisfy `PreservesPositiveTimeNat`, which no `TimeTranslation` can (see
`not_preservesPositiveTime_of_shift`).  The strong-continuity and completion material of
`HalfSpaceHilbert` has no discrete-time analogue and is not restated.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open RealInnerProductSpace

noncomputable section

/-! ## The one-sided discrete-time structure -/

/-- **A one-sided, discrete-time translation**: an `ℕ`-indexed semigroup of linear maps of the
observable algebra, with `T 0 = 1` and `T (m + n) = T m ∘ T n`.  This is the `ℕ`-time analogue
of `TimeTranslation`, and the shape a lattice transfer matrix has. -/
structure DiscreteTimeTranslation where
  /-- The one-parameter family, at nonnegative integral times. -/
  toFun : ℕ → (Observable →ₗ[ℝ] Observable)
  /-- Time `0` is the identity. -/
  map_zero : toFun 0 = LinearMap.id
  /-- The semigroup law `T (m + n) = T m ∘ T n`. -/
  map_add : ∀ m n : ℕ, toFun (m + n) = (toFun m).comp (toFun n)

instance : CoeFun DiscreteTimeTranslation (fun _ => ℕ → Observable →ₗ[ℝ] Observable) :=
  ⟨DiscreteTimeTranslation.toFun⟩

/-- **The one-sided semigroup law**: `T (m + n) = T m ∘ T n`. -/
theorem discreteTimeTranslation_semigroup (T : DiscreteTimeTranslation) (m n : ℕ)
    (F : Observable) : T (m + n) F = T m (T n F) := by
  rw [show T (m + n) = (T m).comp (T n) from T.map_add m n]
  rfl

/-- `T 0` is the identity. -/
theorem discreteTimeTranslation_zero (T : DiscreteTimeTranslation) (F : Observable) :
    T 0 F = F := by
  rw [show T 0 = LinearMap.id from T.map_zero]
  rfl

/-- **Every `ℝ`-time translation is a one-sided discrete-time one**, by restriction to `ℕ`. -/
def ofTimeTranslation (T : TimeTranslation) : DiscreteTimeTranslation where
  toFun n := T (n : ℝ)
  map_zero := by
    show T ((0 : ℕ) : ℝ) = LinearMap.id
    rw [Nat.cast_zero]
    exact T.map_zero
  map_add m n := by
    show T ((m + n : ℕ) : ℝ) = (T (m : ℝ)).comp (T (n : ℝ))
    rw [Nat.cast_add]
    exact T.map_add _ _

/-! ## Support preservation and the evolution on `𝔄₊` -/

/-- **A forward step preserves positive-time support**: `T n` maps the positive-time algebra into
itself, for every `n : ℕ`.  This is the one-sided form of `PreservesPositiveTime`. -/
def PreservesPositiveTimeNat (T : DiscreteTimeTranslation) : Prop :=
  ∀ (n : ℕ) (F : PositiveTimeAlgebra), T n (F : Observable) ∈ PositiveTimeAlgebra

/-- **The one-sided evolution on `𝔄₊`**: `T n` restricted to the positive-time algebra. -/
def hsEvolNat {T : DiscreteTimeTranslation} (hT : PreservesPositiveTimeNat T) (n : ℕ) :
    PositiveTimeAlgebra →ₗ[ℝ] PositiveTimeAlgebra where
  toFun F := ⟨T n (F : Observable), hT n F⟩
  map_add' F G := by
    refine Subtype.ext ?_
    simp
  map_smul' c F := by
    refine Subtype.ext ?_
    simp

@[simp]
theorem hsEvolNat_coe {T : DiscreteTimeTranslation} (hT : PreservesPositiveTimeNat T) (n : ℕ)
    (F : PositiveTimeAlgebra) : (hsEvolNat hT n F : Observable) = T n (F : Observable) := rfl

/-- The restricted evolution is the identity at time `0`. -/
theorem hsEvolNat_zero {T : DiscreteTimeTranslation} (hT : PreservesPositiveTimeNat T)
    (F : PositiveTimeAlgebra) : hsEvolNat hT 0 F = F :=
  Subtype.ext (discreteTimeTranslation_zero T (F : Observable))

/-- **The restricted one-sided evolution is a semigroup**: `T(m + n) = T(m) T(n)` on `𝔄₊`. -/
theorem hsEvolNat_add {T : DiscreteTimeTranslation} (hT : PreservesPositiveTimeNat T) (m n : ℕ)
    (F : PositiveTimeAlgebra) : hsEvolNat hT (m + n) F = hsEvolNat hT m (hsEvolNat hT n F) :=
  Subtype.ext (discreteTimeTranslation_semigroup T m n (F : Observable))

/-! ## Contractivity and the null space -/

/-- **Contractivity of the OS form along forward steps**: the one-sided OS hypothesis, stated on
`𝔄₊`.  This is the `ℕ`-time form of `HsHinv`. -/
def HsHinvNat (Λ : HalfSpaceState) (T : DiscreteTimeTranslation)
    (hT : PreservesPositiveTimeNat T) : Prop :=
  ∀ (n : ℕ) (F : PositiveTimeAlgebra),
    hsBilin Λ (hsEvolNat hT n F) (hsEvolNat hT n F) ≤ hsBilin Λ F F

/-- **Forward steps preserve the null space `𝔑₊`.**  `0 ≤ ⟨T n F, T n F⟩ ≤ ⟨F,F⟩ = 0` for
`F` null, so `T n F` is null by Cauchy–Schwarz. -/
theorem hsRadical_invariantNat (Λ : HalfSpaceState) (T : DiscreteTimeTranslation)
    {hT : PreservesPositiveTimeNat T} (hinv : HsHinvNat Λ T hT) {F : PositiveTimeAlgebra}
    (hF : F ∈ HsRadical Λ) (n : ℕ) : hsEvolNat hT n F ∈ HsRadical Λ := by
  have h0 : hsBilin Λ F F = 0 := hF F
  refine mem_hsRadical_of_self_eq_zero Λ ?_
  have hle := hinv n F
  rw [h0] at hle
  exact le_antisymm hle (hsBilin_self_nonneg Λ _)

/-! ## The descended one-sided transfer semigroup -/

/-- **The evolution descended to `𝔄₊/𝔑₊`** at a nonnegative integral time. -/
def hsQuotMapNat (Λ : HalfSpaceState) (T : DiscreteTimeTranslation)
    (hT : PreservesPositiveTimeNat T) (hinv : HsHinvNat Λ T hT) (n : ℕ) :
    HsSpace Λ →ₗ[ℝ] HsSpace Λ :=
  (HsRadical Λ).mapQ (HsRadical Λ) (hsEvolNat hT n)
    (fun _ hx => hsRadical_invariantNat Λ T hinv hx n)

@[simp]
theorem hsQuotMapNat_mk (Λ : HalfSpaceState) (T : DiscreteTimeTranslation)
    (hT : PreservesPositiveTimeNat T) (hinv : HsHinvNat Λ T hT) (n : ℕ)
    (F : PositiveTimeAlgebra) :
    hsQuotMapNat Λ T hT hinv n (Submodule.Quotient.mk F)
      = Submodule.Quotient.mk (hsEvolNat hT n F) := rfl

/-- **The descended one-sided evolution is a contraction**: `‖P(n)x‖ ≤ ‖x‖`. -/
theorem hsQuotMapNat_contractive (Λ : HalfSpaceState) (T : DiscreteTimeTranslation)
    (hT : PreservesPositiveTimeNat T) (hinv : HsHinvNat Λ T hT) (n : ℕ) (x : HsSpace Λ) :
    ‖hsQuotMapNat Λ T hT hinv n x‖ ≤ ‖x‖ := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [hsQuotMapNat_mk, hsNorm_mk, hsNorm_mk]
  exact Real.sqrt_le_sqrt (hinv n F)

/-- `P(0) = 1` on `𝔄₊/𝔑₊`. -/
theorem hsQuotMapNat_zero (Λ : HalfSpaceState) (T : DiscreteTimeTranslation)
    (hT : PreservesPositiveTimeNat T) (hinv : HsHinvNat Λ T hT) (x : HsSpace Λ) :
    hsQuotMapNat Λ T hT hinv 0 x = x := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [hsQuotMapNat_mk]
  exact congrArg Submodule.Quotient.mk (hsEvolNat_zero hT F)

/-- `P(m + n) = P(m) P(n)` on `𝔄₊/𝔑₊`. -/
theorem hsQuotMapNat_add (Λ : HalfSpaceState) (T : DiscreteTimeTranslation)
    (hT : PreservesPositiveTimeNat T) (hinv : HsHinvNat Λ T hT) (m n : ℕ) (x : HsSpace Λ) :
    hsQuotMapNat Λ T hT hinv (m + n) x
      = hsQuotMapNat Λ T hT hinv m (hsQuotMapNat Λ T hT hinv n x) := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [hsQuotMapNat_mk, hsQuotMapNat_mk, hsQuotMapNat_mk]
  exact congrArg Submodule.Quotient.mk (hsEvolNat_add hT m n F)

/-! ## The old `ℝ`-time API embeds in the new one -/

/-- The image of an `ℝ`-time translation preserves positive time in the one-sided sense. -/
theorem preservesPositiveTimeNat_of_ofTimeTranslation {T : TimeTranslation}
    (hT : PreservesPositiveTime T) : PreservesPositiveTimeNat (ofTimeTranslation T) :=
  fun n F => hT (n : ℝ) F

/-- The one-sided evolution of the image agrees with the original at integral times. -/
theorem hsEvolNat_ofTimeTranslation {T : TimeTranslation} (hT : PreservesPositiveTime T) (n : ℕ)
    (F : PositiveTimeAlgebra) :
    hsEvolNat (preservesPositiveTimeNat_of_ofTimeTranslation hT) n F = hsEvol hT (n : ℝ) F :=
  Subtype.ext rfl

/-- **The `ℝ`-time contractivity hypothesis implies the one-sided one** for the restricted
translation: nothing is lost in weakening the API. -/
theorem hsHinvNat_of_hsHinv {T : TimeTranslation} (hT : PreservesPositiveTime T)
    {Λ : HalfSpaceState} (hinv : HsHinv Λ hT) :
    HsHinvNat Λ (ofTimeTranslation T) (preservesPositiveTimeNat_of_ofTimeTranslation hT) := by
  intro n F
  rw [hsEvolNat_ofTimeTranslation]
  exact hinv (n : ℝ) (Nat.cast_nonneg n) F

end

end BookProof.OSReconstruction
