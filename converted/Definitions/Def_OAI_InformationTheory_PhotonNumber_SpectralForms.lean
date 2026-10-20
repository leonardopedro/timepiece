/-
prove2.me platform library module `Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAI_InformationTheory_PhotonNumber_SpectralForms.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/SpectralForms.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory

namespace BKM

section
open scoped ComplexConjugate
variable {J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def reindexBasis (b : HilbertBasis J ℂ E) (e : K ≃ J) : HilbertBasis K ℂ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have hr : Set.range (b ∘ e) = Set.range b := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨e.symm j, by simp⟩
    rw [hr]
    exact b.dense_span.ge)
@[simp] theorem reindexBasis_apply (b : HilbertBasis J ℂ E) (e : K ≃ J) (i : K) :
    reindexBasis b e i = b (e i) := by simp [reindexBasis]

omit [CompleteSpace E] in
 theorem basis_hasSum_normSq (b : HilbertBasis J ℂ E) (x : E) :
    HasSum (fun j => Complex.normSq (inner ℂ (b j) x)) (‖x‖^2) := by
  simpa only [Complex.normSq_eq_norm_sq] using TraceEnsemble.basis_hasSum_norm_sq b x

def entry (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) : ℂ := inner ℂ (b i) (Z (b j))

 theorem entry_adjoint (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) :
    entry b Z.adjoint i j = conj (entry b Z j i) := by
  rw [entry, ContinuousLinearMap.adjoint_inner_right, entry, inner_conj_symm]

omit [CompleteSpace E] in
 theorem hasSum_column (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (j : J) :
    HasSum (fun i => Complex.normSq (entry b Z i j)) (‖Z (b j)‖^2) := basis_hasSum_normSq b _

omit [CompleteSpace E] in
 theorem weighted_column_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (Z : E →L[ℂ] E) :
    Summable (fun ij : J × J => p ij.2*Complex.normSq (entry b Z ij.1 ij.2)) := by
  have hb (j : J) : ‖Z (b j)‖^2 ≤ ‖Z‖^2 := by
    have h := Z.le_opNorm (b j)
    rw [b.orthonormal.norm_eq_one j, mul_one] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have ht : Summable (fun j => p j*‖Z (b j)‖^2) :=
    (hs.mul_right (‖Z‖^2)).of_nonneg_of_le (fun j => mul_nonneg (hp j) (sq_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left (hb j) (hp j))
  have hh : Summable (fun ji : J × J => p ji.1*Complex.normSq (entry b Z ji.2 ji.1)) := by
    rw [summable_prod_of_nonneg (fun ji => mul_nonneg (hp _) (Complex.normSq_nonneg _))]
    exact ⟨fun j => ((hasSum_column b Z j).mul_left (p j)).summable,
      by simpa only [tsum_mul_left, (hasSum_column b Z _).tsum_eq] using ht⟩
  exact (Equiv.prodComm J J).summable_iff.mpr hh

 theorem weighted_row_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (Z : E →L[ℂ] E) :
    Summable (fun ij : J × J => p ij.1*Complex.normSq (entry b Z ij.1 ij.2)) := by
  have hh := (Equiv.prodComm J J).summable_iff.mpr (weighted_column_summable b p hp hs Z.adjoint)
  simpa only [Function.comp_def, Equiv.prodComm_apply, Prod.swap, entry_adjoint, Complex.normSq_conj] using hh

 theorem logMean_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (Z : E →L[ℂ] E) :
    Summable (fun ij : J × J => DiagonalForms.System.logMean (p ij.1) (p ij.2)*
      Complex.normSq (entry b Z ij.1 ij.2)) := by
  have hh := ((weighted_row_summable b p (fun j => (hp j).le) hs Z).add
    (weighted_column_summable b p (fun j => (hp j).le) hs Z)).div_const 2
  apply hh.of_nonneg_of_le
  · intro ij
    exact mul_nonneg (DiagonalForms.System.logMean_pos (hp _) (hp _)).le (Complex.normSq_nonneg _)
  · intro ij
    convert mul_le_mul_of_nonneg_right (DiagonalForms.System.logMean_le_arithmetic (hp ij.1) (hp ij.2))
        (Complex.normSq_nonneg (entry b Z ij.1 ij.2)) using 1
    ring

end

open scoped BigOperators
variable {J : Type*}

end BKM

namespace SpectralTests
open scoped BigOperators ComplexConjugate
variable {A I P : Type*}

def space (g : A → I → ℂ) : Submodule ℂ (I → ℂ) := Submodule.span ℂ (Set.range g)

theorem frequency_finite (g : A → I → ℂ) (v : I → P) (q : A → P)
    (hg : ∀ a i, g a i ≠ 0 → v i = q a) (z : I → ℂ) (hz : z ∈ space g) :
    ∃ s : Finset P, ∀ i, z i ≠ 0 → v i ∈ s := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨{q a}, fun i hi => by simpa only [Finset.mem_singleton] using hg a i hi⟩
  | zero => exact ⟨∅, fun i hi => (hi rfl).elim⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun i hi => ?_⟩
    by_cases hxi : x i = 0
    · have hyi : y i ≠ 0 := by simpa only [Pi.add_apply, hxi, zero_add] using hi
      exact Finset.mem_union.mpr (Or.inr (ht i hyi))
    · exact Finset.mem_union.mpr (Or.inl (hs i hxi))
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, fun i hi => hs i ?_⟩
    intro hxi
    apply hi
    simp [hxi]

def multiplier (v : I → P) (w : P → ℂ) : (I → ℂ) →ₗ[ℂ] (I → ℂ) where
  toFun z i := w (v i)*z i
  map_add' x y := by ext i; simp only [Pi.add_apply, mul_add]
  map_smul' c x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem multiplier_generator (g : A → I → ℂ) (v : I → P) (q : A → P)
    (hg : ∀ a i, g a i ≠ 0 → v i = q a) (w : P → ℂ) (a : A) :
    multiplier v w (g a) = w (q a) • g a := by
  ext i
  change w (v i)*g a i=w (q a)*g a i
  by_cases hi : g a i = 0
  · simp [hi]
  · rw [hg a i hi]

theorem multiplier_mem (g : A → I → ℂ) (v : I → P) (q : A → P)
    (hg : ∀ a i, g a i ≠ 0 → v i = q a) (z : I → ℂ) (hz : z ∈ space g) (w : P → ℂ) :
    multiplier v w z ∈ space g := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [multiplier_generator g v q hg]
    exact (space g).smul_mem _ (Submodule.subset_span ⟨a,rfl⟩)
  | zero => simpa only [map_zero] using (space g).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (space g).add_mem hx hy
  | smul c x _ hx => simpa only [map_smul] using (space g).smul_mem c hx

end SpectralTests

namespace CenteredTests
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def entryMap (b : HilbertBasis J ℂ E) (w : J × J → ℝ) :
    (E →L[ℂ] E) →ₗ[ℂ] (J × J → ℂ) where
  toFun Z ij := (Real.sqrt (w ij) : ℂ)*BKM.entry b Z ij.1 ij.2
  map_add' X Y := by ext ij; simp [BKM.entry, mul_add]
  map_smul' c X := by ext ij; simp [BKM.entry, mul_left_comm]

@[simp] theorem entryMap_apply (b : HilbertBasis J ℂ E) (w : J × J → ℝ)
    (Z : E →L[ℂ] E) (ij : J × J) :
    entryMap b w Z ij = (Real.sqrt (w ij) : ℂ)*BKM.entry b Z ij.1 ij.2 := rfl

theorem entryMap_injective (b : HilbertBasis J ℂ E) (w : J × J → ℝ) (hw : ∀ ij, 0 < w ij) :
    Function.Injective (entryMap b w) := by
  intro X Y h
  have hb (j : J) : X (b j)=Y (b j) := by
    apply b.repr.injective
    ext i
    simp only [b.repr_apply_apply]
    have hh := congrFun h (i,j)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (hw (i,j)))) hh
  ext x
  have hX := (b.hasSum_repr x).mapL X
  have hY := (b.hasSum_repr x).mapL Y
  apply hX.unique
  convert hY using 1
  ext j
  simp only [map_smul, hb]

def generator (b : HilbertBasis J ℂ E) (p : J → ℝ) (ij : J × J) : E →L[ℂ] E := by
  classical
  exact InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2) -
    (if ij.1=ij.2 then (p ij.1:ℂ) else 0) • ContinuousLinearMap.id ℂ E

theorem generator_entry [DecidableEq J] (b : HilbertBasis J ℂ E) (p : J → ℝ) (ij kl : J × J) :
    BKM.entry b (generator b p ij) kl.1 kl.2 =
      (if kl.1=ij.1 ∧ kl.2=ij.2 then (1:ℂ) else 0)-
      (if ij.1=ij.2 then (p ij.1:ℂ) else 0)*(if kl.1=kl.2 then 1 else 0) := by
  classical
  simp only [generator, BKM.entry, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply,
    inner_sub_right, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  split_ifs <;> simp_all

theorem generator_frequency (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ)
    {P : Type*} (v : J × J → P) (q : P) (hv : ∀ j, v (j,j)=q)
    (ij kl : J × J) (hz : entryMap b w (generator b p ij) kl ≠ 0) : v kl=v ij := by
  classical
  have hg : BKM.entry b (generator b p ij) kl.1 kl.2 ≠ 0 := by
    intro hh; apply hz; simp [hh]
  rw [generator_entry] at hg
  by_cases hij : ij.1=ij.2
  · have hkl : kl.1=kl.2 := by
      by_contra hk
      have hp : ¬ (kl.1=ij.1 ∧ kl.2=ij.2) := fun hf => hk (hf.1.trans (hij.trans hf.2.symm))
      simp [hp,hk] at hg
    calc v kl=v (kl.2,kl.2) := by congr 1; exact Prod.ext hkl rfl
         _=q := hv _
         _=v (ij.2,ij.2) := (hv _).symm
         _=v ij := by congr 1; exact Prod.ext hij.symm rfl
  · have hkl : kl.1=ij.1 ∧ kl.2=ij.2 := by
      by_contra hk
      simp [hij,hk] at hg
    exact congrArg v (Prod.ext hkl.1 hkl.2)

def operatorSpace (b : HilbertBasis J ℂ E) (p : J → ℝ) : Submodule ℂ (E →L[ℂ] E) :=
  Submodule.span ℂ (Set.range (generator b p))

def coordinates (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ) :
    Submodule ℂ (J × J → ℂ) := (operatorSpace b p).map (entryMap b w)

theorem coordinates_eq_span (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ) :
    coordinates b p w = SpectralTests.space (fun ij => entryMap b w (generator b p ij)) := by
  rw [coordinates, operatorSpace, Submodule.map_span, ← Set.range_comp]
  rfl

variable [CompleteSpace E]

theorem coordinates_mass (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : Summable p) (h : ℝ) (hh : 0 ≤ h) (z : coordinates b p (fun ij => h*DiagonalForms.System.logMean (p ij.1) (p ij.2))) :
    Summable (fun ij => Complex.normSq (z.val ij)) := by
  obtain ⟨Z, _hZ, he⟩ := z.property
  rw [← he]
  have hsum := (BKM.logMean_summable b p hp hs Z).mul_left h
  convert hsum using 1
  ext ij
  simp only [entryMap_apply, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (mul_nonneg hh (DiagonalForms.System.logMean_pos (hp _) (hp _)).le)]
  ring

end CenteredTests

namespace ThermalMetric

section
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem observable_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t) (Z : E →L[ℂ] E) :
    Summable (fun a : J × J => metricCoefficient t (p a.1) (p a.2) *
      ‖BKM.entry b Z a.1 a.2‖^2) := by
  have hc := BKM.weighted_column_summable b p (fun j => (hp j).le) hs Z
  have hr := BKM.weighted_row_summable b p (fun j => (hp j).le) hs Z
  simp only [Complex.normSq_eq_norm_sq] at hc hr
  apply Summable.of_nonneg_of_le
    (fun a => mul_nonneg (metricCoefficient_pos ht (hp _) (hp _)).le (sq_nonneg _)) _
    (((hr.mul_left t).add (hc.mul_left (t+1))).mul_left (h t/2))
  intro a
  have hh := DiagonalForms.System.logMean_le_arithmetic (mul_pos ht (hp a.1))
    (mul_pos (by positivity : 0<t+1) (hp a.2))
  have hm : metricCoefficient t (p a.1) (p a.2) =
      h t*DiagonalForms.System.logMean (t*p a.1) ((t+1)*p a.2) := by
    rw [metricCoefficient, mul_assoc, tilted_logMean ht (hp _) (hp _)]
  rw [hm]
  have hh' := mul_le_mul_of_nonneg_left hh (h_pos ht).le
  nlinarith [mul_le_mul_of_nonneg_right hh' (sq_nonneg ‖BKM.entry b Z a.1 a.2‖)]

def observableMap (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t) :
    (E →L[ℂ] E) →ₗ[ℂ] lp (fun _ : J × J => ℂ) 2 where
  toFun Z := weightedVector (fun a => metricCoefficient t (p a.1) (p a.2))
    (fun a => BKM.entry b Z a.1 a.2) (observable_summable b p hp hs t ht Z)
    (fun a => (metricCoefficient_pos ht (hp _) (hp _)).le)
  map_add' Z U := by ext a; simp [BKM.entry, mul_add]
  map_smul' c Z := by ext a; simp [BKM.entry, mul_left_comm]

@[simp] theorem observableMap_apply (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t)
    (Z : E →L[ℂ] E) (a : J × J) :
    observableMap b p hp hs t ht Z a =
      (Real.sqrt (metricCoefficient t (p a.1) (p a.2)) : ℂ) * BKM.entry b Z a.1 a.2 := rfl

@[simp] theorem observableMap_id (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t) :
    observableMap b p hp hs t ht (ContinuousLinearMap.id ℂ E) = identityVector t ht p hp hs := by
  classical
  ext a
  simp [BKM.entry, identityVector, identityEntry,
    orthonormal_iff_ite.mp b.orthonormal]

end

section
open scoped ComplexConjugate
variable {J : Type*}

def centerProjection (e : lp (fun _ : J => ℂ) 2) :
    lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2 :=
  ContinuousLinearMap.id ℂ _ - (innerSL ℂ e).smulRight e

@[simp] theorem centerProjection_apply (e x : lp (fun _ : J => ℂ) 2) :
    centerProjection e x=x-inner ℂ e x • e := rfl

variable [DecidableEq J]

@[simp] theorem identityVector_apply (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (ij : J × J) :
    identityVector r hr p hp hs ij =
      if ij.1=ij.2 then (Real.sqrt (p ij.1):ℂ) else 0 := by
  classical
  simp only [identityVector, weightedVector_apply, identityEntry]
  split_ifs with he
  · rw [he, metricCoefficient_self hr (hp _)]; simp
  · simp

def matrixGenerator (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (ij : J × J) : lp (fun _ : J × J => ℂ) 2 := by
  classical
  exact (Real.sqrt (metricCoefficient r (p ij.1) (p ij.2)):ℂ) • lp.single 2 ij 1 -
    (if ij.1=ij.2 then (p ij.1:ℂ) else 0) • identityVector r hr p hp hs

end

open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

@[simp] theorem observableMap_generator [DecidableEq J] (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t) (ij : J × J) :
    observableMap b p hp hs t ht (CenteredTests.generator b p ij) =
      matrixGenerator t ht p hp hs ij := by
  classical
  ext kl
  simp only [observableMap_apply, CenteredTests.generator_entry, matrixGenerator,
    lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.single_apply, Pi.single_apply, identityVector_apply]
  by_cases he : kl=ij
  · subst kl
    by_cases hd : ij.1=ij.2
    · simp only [hd, metricCoefficient_self ht (hp _), ite_true, and_self,
        mul_one]
      ring
    · simp [hd]
  · have he' : ¬ (kl.1=ij.1 ∧ kl.2=ij.2) := fun hh => he (Prod.ext hh.1 hh.2)
    simp only [ite_eq_right he, ite_eq_right he', mul_zero, zero_sub]
    by_cases hd : kl.1=kl.2
    · simp only [hd, metricCoefficient_self ht (hp _), ite_true]
      ring
    · simp [hd]

end ThermalMetric

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace CenteredTests
open scoped BigOperators
variable {J T E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def includeRange (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ) :
    coordinates b p w →ₗ[ℂ] LinearMap.range (entryMap b w) where
  toFun z := ⟨z.val, by obtain ⟨Z, _hZ, he⟩ := z.property; exact ⟨Z,he⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def realize (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ) (hw : ∀ ij, 0 < w ij) :
    coordinates b p w →ₗ[ℂ] (E →L[ℂ] E) :=
  (LinearEquiv.ofInjective (entryMap b w) (entryMap_injective b w hw)).symm.toLinearMap.comp
    (includeRange b p w)

def system (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : Summable p)
    (h : ℝ) (hh : 0 < h) (v : J × J → P) (q : P) (hv : ∀ j, v (j,j)=q)
    (targetParam : T → P) (L : (E →L[ℂ] E) →ₗ[ℂ] (T → ℂ)) : DiagonalForms.System P (J × J) T where
  sourceParam := v
  targetParam := targetParam
  tests := coordinates b p (fun ij => h*DiagonalForms.System.logMean (p ij.1) (p ij.2))
  map := L.comp (realize b p _ (fun ij => mul_pos hh (DiagonalForms.System.logMean_pos (hp _) (hp _))))
  mass_summable z := coordinates_mass b p hp hs h hh.le z
  finite_values z := by
    apply SpectralTests.frequency_finite (fun ij => entryMap b _ (generator b p ij)) v v
      (generator_frequency b p _ v q hv) z.val
    rw [← coordinates_eq_span]
    exact z.property
  multiplier_mem z w := by
    apply (SetLike.ext_iff.mp (coordinates_eq_span b p _) _).mpr
    exact SpectralTests.multiplier_mem (fun ij => entryMap b _ (generator b p ij)) v v
      (generator_frequency b p _ v q hv) z.val (by rw [← coordinates_eq_span]; exact z.property) w

end CenteredTests

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

end ThermalMetric

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

structure Space (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  I : Type
  basis : HilbertBasis I ℂ E
  p : I → ℝ
  pos : ∀ i, 0 < p i
  sum : HasSum p 1
  r : ℝ
  rpos : 0 < r

namespace Space
variable (S : Space E)
def param (ij : S.I × S.I) : ℝ × ℝ := (S.r, frequency S.r (S.p ij.1) (S.p ij.2))
def base (ij : S.I × S.I) : ℝ := h S.r*logMean (S.p ij.1) (S.p ij.2)
def coords : (E →L[ℂ] E) →ₗ[ℂ] (S.I × S.I → ℂ) := CenteredTests.entryMap S.basis S.base

def quad (w : ℝ × ℝ → ℝ) (Z : E →L[ℂ] E) : ℝ :=
  ∑' ij, w (S.param ij)*Complex.normSq (S.coords Z ij)

def plus (q : ℝ × ℝ) : ℝ := (1/h q.1)*f (h q.1*q.2/2)*Real.exp (h q.1*q.2/2)
def minus (q : ℝ × ℝ) : ℝ := (1/h q.1)*f (h q.1*q.2/2)*Real.exp (-(h q.1*q.2/2))

end Space

abbrev Param := {r : ℝ // 0 < r} × ℝ
def raw (q : Param) : ℝ × ℝ := (q.1.val,q.2)
def Space.pparam (S : Space E) (ij : S.I × S.I) : Param := (⟨S.r,S.rpos⟩,(S.param ij).2)
def Space.pquad (S : Space E) (X : Param → ℝ) (Z : E →L[ℂ] E) : ℝ :=
  ∑' ij, X (S.pparam ij)*Complex.normSq (S.coords Z ij)

def targetMap (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) :
    (E →L[ℂ] E) →ₗ[ℂ] ((Σ i, (S i).I × (S i).I) → ℂ) where
  toFun Z a := (Real.sqrt (w a.1):ℂ)*(S a.1).coords (L a.1 Z) a.2
  map_add' X Y := by ext a; simp [mul_add]
  map_smul' c X := by ext a; simp [mul_left_comm]

def diagram (S₀ : Space E) (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) :
    DiagonalForms.System Param (S₀.I × S₀.I) (Σ i, (S i).I × (S i).I) :=
  CenteredTests.system S₀.basis S₀.p S₀.pos S₀.sum.summable (h S₀.r) (h_pos S₀.rpos)
    S₀.pparam (⟨S₀.r,S₀.rpos⟩,0)
    (fun j => by simp [Space.pparam, Space.param, frequency])
    (fun a => (S a.1).pparam a.2) (targetMap S w L)

def plusWeight (q : Param) : ℝ := Space.plus (raw q)
def minusWeight (q : Param) : ℝ := Space.minus (raw q)
def thermalWeight (q : Param) : ℝ := weight q.1.val q.2

end ThermalSpectral

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

theorem weight_bounds {r : ℝ} (hr : 0<r) (v : ℝ) :
    r ≤ weight r v ∧ weight r v ≤ r+1 := by
  have hh := weight_frequency_bounds hr (Real.exp_pos (h r*v)) (zero_lt_one : (0:ℝ)<1)
  have he : frequency r (Real.exp (h r*v)) 1=v := by
    simp only [frequency, Real.log_exp, Real.log_one, sub_zero]
    field_simp [(h_pos hr).ne']
  rwa [he] at hh

def lowerWeight (r : ℝ) : ℝ := sInf (Set.range (weight r))

theorem lowerWeight_bounds {r : ℝ} (hr : 0<r) :
    r ≤ lowerWeight r ∧ ∀ v, lowerWeight r ≤ weight r v := by
  have hb : BddBelow (Set.range (weight r)) := ⟨r,by rintro _ ⟨v,rfl⟩; exact (weight_bounds hr v).1⟩
  constructor
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨v,rfl⟩; exact (weight_bounds hr v).1)
  · intro v; exact csInf_le hb (Set.mem_range_self v)

theorem lowerWeight_pos {r : ℝ} (hr : 0<r) : 0<lowerWeight r :=
  lt_of_lt_of_le hr (lowerWeight_bounds hr).1

def mixtureConstant (r : ℝ) : ℝ := (Real.sqrt (h r*lowerWeight r))⁻¹

theorem mixtureConstant_pos {r : ℝ} (hr : 0<r) : 0 < mixtureConstant r :=
  inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (h_pos hr) (lowerWeight_pos hr)))

end ThermalMetric

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

def observable : (E →L[ℂ] E) →ₗ[ℂ] lp (fun _ : S.I × S.I => ℂ) 2 :=
  observableMap S.basis S.p S.pos S.sum.summable S.r S.rpos

end ThermalSpectral.Space

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation BeamLadder ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace ThermalSpectral.Space
open EntropyPhotonNumber Annihilation WeightedGenerator ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} (S : Space (Fock n))

end ThermalSpectral.Space

end

end OAI
