import Mathlib
import BookProof.ChapterMackeyQuasiInvariant
import BookProof.ChapterMackeyQuasiInvariantSigma

/-!
# The translation system of imprimitivity on `L²(ℝ³)` — the localization structure

`BookProof.ChapterMackeyQuasiInvariant` proves that, over a continuous base with a
quasi-invariant measure, the induced data is a system of imprimitivity.  This file gives the
concrete instance the book's chapter on the relativistic position operator is about: the
**translation group acting on space**, with Lebesgue measure — which is *invariant*, so the
Radon–Nikodym cocycle is `1` and the induced representation is the ordinary translation
representation `(V a f)(x) = f(x − a)` on `L²(ℝ³)`, while the projection-valued measure is
multiplication by the indicators of the Borel subsets of space: the localization observable.

## Results

* `quasiInvariant_translation` — a left-invariant measure on an additive group is
  quasi-invariant for the translation action, and `dens_translation` computes its cocycle to
  be `1`;
* `translation_inducedSystem` — the system of imprimitivity of an arbitrary left-invariant
  measure on an additive group, with an arbitrary fibre and the trivial cocycle;
* **`position_system_R3`** — the instance on `L²(ℝ³)`: the translation representation and the
  localization projections form a system of imprimitivity based on `ℝ³`, with the covariance
  relation `V a P(E) V(a)⁻¹ = P(E + a)`; `position_pvm_countably_additive_R3` records that
  the localization projections are countably additive.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory Measure

namespace BookProof.ChapterMackeyQuasiInvariant

/-! ## Translations of a left-invariant measure -/

variable {V : Type*} [AddGroup V] [MeasurableSpace V] [MeasurableAdd V]

/-- A left-invariant measure is quasi-invariant for the translation action. -/
theorem quasiInvariant_translation (μ : Measure V) [μ.IsAddLeftInvariant] :
    QuasiInvariant μ (Multiplicative V) where
  measurable := fun g => measurable_const_add (Multiplicative.toAdd g)
  ac := fun g => by
    rw [show (μ.map fun x : V => g • x) = μ from
      Measure.IsAddLeftInvariant.map_add_left_eq_self (Multiplicative.toAdd g)]

omit [MeasurableAdd V] in
/-- …and then the Radon–Nikodym cocycle is `1`: the induced representation is the ordinary
translation representation. -/
theorem dens_translation (μ : Measure V) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (g : Multiplicative V) : dens μ g =ᵐ[μ] fun _ => 1 :=
  dens_eq_one_of_invariant
    (fun g => Measure.IsAddLeftInvariant.map_add_left_eq_self (Multiplicative.toAdd g)) g

/-- **The translation system of imprimitivity.**  For a left-invariant measure on an additive
group, the translation representation on `L²` and multiplication by the indicators of the
measurable sets form a system of imprimitivity based on the group. -/
theorem translation_inducedSystem {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (μ : Measure V) [SigmaFinite μ] [μ.IsAddLeftInvariant] :
    let h := quasiInvariant_translation (V := V) μ
    let hL := unitaryCocycle_one (G := Multiplicative V) (K := K) μ
    (∀ (g : Multiplicative V) (f : Lp K 2 μ), ‖vmap h hL g f‖ = ‖f‖) ∧
    (∀ (g k : Multiplicative V) (f : Lp K 2 μ),
        vmap h hL g (vmap h hL k f) = vmap h hL (g * k) f) ∧
    (∀ (g : Multiplicative V) (E : Set V) (hE : MeasurableSet E) (f : Lp K 2 μ),
        vmap h hL g (proj μ hE (vmap h hL g⁻¹ f))
          = proj μ ((actEquiv h.measurable g).measurableSet_image.mpr hE) f) := by
  intro h hL
  obtain ⟨_, _, hnorm, _, hmul, _, _, _, hcov⟩ :=
    mackey_inducedSystem_continuous (G := Multiplicative V) (K := K)
      (L := fun _ _ => LinearIsometryEquiv.refl ℂ K) h hL
  exact ⟨hnorm, hmul, hcov⟩

/-! ## The position observable on `L²(ℝ³)` -/

/-- **The localization structure of a particle in three-dimensional space.**  The translation
representation on `L²(ℝ³)` and the localization projections (multiplication by the indicator
of a Borel set of space) form a system of imprimitivity based on `ℝ³`: each translation acts
unitarily, translations compose, and conjugating a localization projection by a translation
translates the region. -/
theorem position_system_R3 :
    let μ : Measure (EuclideanSpace ℝ (Fin 3)) := volume
    let h := quasiInvariant_translation (V := EuclideanSpace ℝ (Fin 3)) μ
    let hL := unitaryCocycle_one (G := Multiplicative (EuclideanSpace ℝ (Fin 3))) (K := ℂ) μ
    (∀ (g : Multiplicative (EuclideanSpace ℝ (Fin 3))) (f : Lp ℂ 2 μ),
        ‖vmap h hL g f‖ = ‖f‖) ∧
    (∀ (g k : Multiplicative (EuclideanSpace ℝ (Fin 3))) (f : Lp ℂ 2 μ),
        vmap h hL g (vmap h hL k f) = vmap h hL (g * k) f) ∧
    (∀ (g : Multiplicative (EuclideanSpace ℝ (Fin 3)))
        (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E) (f : Lp ℂ 2 μ),
        vmap h hL g (proj μ hE (vmap h hL g⁻¹ f))
          = proj μ ((actEquiv h.measurable g).measurableSet_image.mpr hE) f) :=
  translation_inducedSystem (K := ℂ) (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-- The localization projections on `L²(ℝ³)` are countably additive. -/
theorem position_pvm_countably_additive_R3
    {E : ℕ → Set (EuclideanSpace ℝ (Fin 3))} (hE : ∀ n, MeasurableSet (E n))
    (hd : Pairwise (Function.onFun Disjoint E))
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    HasSum (fun n => proj volume (hE n) f) (proj volume (MeasurableSet.iUnion hE) f) :=
  proj_hasSum_iUnion volume hE hd f

end BookProof.ChapterMackeyQuasiInvariant
