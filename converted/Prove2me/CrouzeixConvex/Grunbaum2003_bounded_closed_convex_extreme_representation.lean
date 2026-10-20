/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 37421203-d462-49d1-ba51-f669e79b3029
* original name       : `Grunbaum2003.bounded_closed_convex_extreme_representation`
* title               : Bounded closed convex sets are the convex hull of their extreme points
* statement author    : junyihjy
* solution author     : ryanshin (submission 1f33b733-e350-42a8-8a86-a32c7a5c51ce,
                        accepted 2026-09-30T14:51:57.241643+00:00)
* source              : Branko Grünbaum, Convex Polytopes, second edition (2003), Â§2.5, Theorem 6 (2.5.6), printed p.25 / source.pdf p.43; characteristic cone and line-free sets: printed p.24 / PDF42; extreme points: Â§2.4, printed p.17 / PDF35.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/crouzeix-convex/Grunbaum2003.bounded_closed_convex_extreme_representation.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/Grunbaum2003_bounded_closed_convex_extreme_representation.diff`.
-/
import Mathlib

namespace GrunbaumProof
open scoped Pointwise BigOperators
private theorem cm_small_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Set (E)) (x : E) (hx : x ∈ convexHull ℝ S) :
    ∃ T : Finset (E), T.card ≤ (Module.finrank ℝ E) + 1 ∧ ↑T ⊆ S ∧ x ∈ convexHull ℝ ↑T := by
  let T := Caratheodory.minCardFinsetOfMemConvexHull hx
  refine ⟨T,?_,Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  have h := (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx).card_le_finrank_succ
  have hb := (vectorSpan ℝ (Set.range ((↑) : T → (E)))).finrank_le
  have hd : Module.finrank ℝ (E) = (Module.finrank ℝ E) := by simp
  rw [hd] at hb
  simpa only [Fintype.card_coe] using le_trans h (Nat.add_le_add_right hb 1)

open scoped BigOperators

private theorem hull_representation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : Set (E)) :
    convexHull ℝ s = ⋃ n ∈ Finset.range ((Module.finrank ℝ E)+2),
      (fun p : (Fin n → ℝ) × (Fin n → (E)) => ∑ i, p.1 i • p.2 i) ''
        ((stdSimplex ℝ (Fin n)) ×ˢ (Set.univ.pi (fun _ : Fin n => s))) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨T,hcard,hT,hxT⟩ := cm_small_subset s x hx
    obtain ⟨w,hwn,hws,hwx⟩ := Finset.mem_convexHull'.mp hxT
    let n := Fintype.card T
    let e : Fin n ≃ T := (Fintype.equivFin T).symm
    let p : (Fin n → ℝ) × (Fin n → (E)) := (fun i => w (e i), fun i => (e i).val)
    have hsum : (∑ i : Fin n, w (e i))=1 := by
      rw [e.sum_comp (fun y : T => w y)]
      simpa only [Finset.univ_eq_attach,Finset.sum_attach] using hws
    have hvec : (∑ i : Fin n, w (e i) • (e i).val)=x := by
      rw [e.sum_comp (fun y : T => w y • y.val)]
      change (∑ y ∈ T.attach, (fun z => w z • z) y.val)=x
      rw [Finset.sum_attach (f := fun z => w z • z)]
      exact hwx
    apply Set.mem_iUnion.mpr
    refine ⟨n,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
    · simp only [Finset.mem_range,n,Fintype.card_coe]
      omega
    · refine ⟨p,⟨⟨?_,hsum⟩,?_⟩,hvec⟩
      · intro i
        exact hwn _ (e i).property
      · intro i hi
        exact hT (e i).property
  · intro hx
    obtain ⟨n,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hn,p,⟨hw,hv⟩,rfl⟩ := Set.mem_iUnion.mp hx
    exact mem_convexHull_of_exists_fintype p.1 p.2 hw.1 hw.2 (fun i => hv i (Set.mem_univ i)) rfl

theorem compact_hull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (s : Set (E)) (h : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  rw [hull_representation]
  apply Finset.isCompact_biUnion
  intro n hn
  apply ((isCompact_stdSimplex (Fin n)).prod (isCompact_univ_pi (fun _ => h))).image
  exact continuous_finset_sum _ (fun i hi => (continuous_apply i |>.comp continuous_fst).smul (continuous_apply i |>.comp continuous_snd))


end GrunbaumProof

namespace GrunbaumProof
noncomputable section
 theorem upper_hull_extreme {E:Type*} [AddCommGroup E] [Module ℝ E]
    (K:Set E) (f:E → ℝ) (hf:StrictConvexOn ℝ K f) :
    ∀ p ∈ convexHull ℝ ((fun x=>(x,f x)) '' K),
      (∀ v:ℝ,(p.1,v) ∈ convexHull ℝ ((fun x=>(x,f x)) '' K) → v ≤ p.2) →
      p.1 ∈ convexHull ℝ (K.extremePoints ℝ) := by
  let H:=convexHull ℝ ((fun x=>(x,f x)) '' K)
  have hcv:Convex ℝ H:=convex_convexHull _ _
  let S:Set (E × ℝ):={p | p ∈ H ∧ ((∀ v:ℝ,(p.1,v) ∈ H → v ≤ p.2) → p.1 ∈ convexHull ℝ (K.extremePoints ℝ))}
  have hbase:(fun x=>(x,f x)) '' K ⊆ S := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨subset_convexHull ℝ _ ⟨x,hx,rfl⟩,?_⟩
    intro hmax
    apply subset_convexHull ℝ _
    refine ⟨hx,?_⟩
    rintro y hy z hz ⟨a,b,ha,hb,hab,heq⟩
    by_cases he: y=z
    · subst z
      simpa [←add_smul,hab] using heq
    · have hh: (x,a*f y+b*f z) ∈ H := by
        convert hcv (subset_convexHull ℝ _ ⟨y,hy,rfl⟩) (subset_convexHull ℝ _ ⟨z,hz,rfl⟩) ha.le hb.le hab using 1
        ext <;> simp [heq]
      have hlo:=hf.2 hy hz he ha hb hab
      rw [heq] at hlo
      have hhi:=hmax (a*f y+b*f z) hh
      exact (not_lt_of_ge hhi hlo).elim
  have hS:Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    refine ⟨hcv hx.1 hy.1 ha hb hab,?_⟩
    intro hmax
    by_cases ha0:a=0
    · have hb1:b=1:=by linarith
      simpa [ha0,hb1] using hy.2 (by simpa [ha0,hb1] using hmax)
    by_cases hb0:b=0
    · have ha1:a=1:=by linarith
      simpa [hb0,ha1] using hx.2 (by simpa [hb0,ha1] using hmax)
    have ha':0 < a:=lt_of_le_of_ne ha (Ne.symm ha0)
    have hb':0 < b:=lt_of_le_of_ne hb (Ne.symm hb0)
    have hxmax:∀ v:ℝ,(x.1,v) ∈ H → v ≤ x.2 := by
      intro v hv
      have hh:( (a • x+b • y).1,a*v+b*y.2) ∈ H := by
        convert hcv hv hy.1 ha hb hab using 1 <;> ext <;> simp
      have ht:=hmax (a*v+b*y.2) hh
      change a*v+b*y.2 ≤ a*x.2+b*y.2 at ht
      nlinarith
    have hymax:∀ v:ℝ,(y.1,v) ∈ H → v ≤ y.2 := by
      intro v hv
      have hh:((a • x+b • y).1,a*x.2+b*v) ∈ H := by
        convert hcv hx.1 hv ha hb hab using 1 <;> ext <;> simp
      have ht:=hmax (a*x.2+b*v) hh
      change a*x.2+b*v ≤ a*x.2+b*y.2 at ht
      nlinarith
    exact (convex_convexHull ℝ (K.extremePoints ℝ)) (hx.2 hxmax) (hy.2 hymax) ha hb hab
  intro p hp hmax
  exact ((convexHull_min hbase hS) hp).2 hmax
 theorem compact_representation {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K:Set E) (hK:IsCompact K) (f:E → ℝ) (hf:Continuous f) (hs:StrictConvexOn ℝ K f) :
    K=convexHull ℝ (K.extremePoints ℝ) := by
  apply Set.Subset.antisymm ?_ (convexHull_min (extremePoints_subset) hs.1)
  intro x hx
  let H:=convexHull ℝ ((fun y=>(y,f y)) '' K)
  have hH:IsCompact H:=compact_hull _ (hK.image (continuous_id.prodMk hf))
  have hc:IsCompact (H ∩ {p:E × ℝ | p.1=x}):=hH.inter_right (isClosed_eq continuous_fst continuous_const)
  have hn:(H ∩ {p:E × ℝ | p.1=x}).Nonempty:=⟨(x,f x),subset_convexHull ℝ _ ⟨x,hx,rfl⟩,rfl⟩
  obtain ⟨p,hp,hmax⟩:=hc.exists_isMaxOn hn continuous_snd.continuousOn
  have hh:=upper_hull_extreme K f hs p hp.1 (fun v hv=>hmax ⟨hv,hp.2⟩)
  have hpx:p.1=x:=hp.2
  simpa only [hpx] using hh

 theorem sum_squares_strict {d:ℕ} : StrictConvexOn ℝ (Set.univ:Set (Fin d → ℝ)) (fun x=>∑ i,x i^2) := by
  classical
  have hs:StrictConvexOn ℝ (Set.univ:Set ℝ) (fun x:ℝ=>x^2):=Even.strictConvexOn_pow (by decide : Even (2:ℕ)) (by norm_num)
  refine ⟨convex_univ,?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hi:∃ i,x i ≠ y i:=by by_contra hh;push_neg at hh;exact hxy (funext hh)
  obtain ⟨i,hi⟩:=hi
  have hh: (∑ j:Fin d,(a*x j+b*y j)^2) < ∑ j:Fin d,(a*(x j)^2+b*(y j)^2) := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact hs.convexOn.2 (Set.mem_univ _) (Set.mem_univ _) ha.le hb.le hab
    · exact ⟨i,Finset.mem_univ _,hs.2 (Set.mem_univ _) (Set.mem_univ _) hi ha hb hab⟩
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,←Finset.mul_sum] using hh

 theorem bounded_representation {d:ℕ} (K:Set (Fin d → ℝ)) (hb:Bornology.IsBounded K)
    (hc:IsClosed K) (hv:Convex ℝ K) : K=convexHull ℝ (K.extremePoints ℝ) := by
  apply compact_representation K (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc,hb⟩) (fun x=>∑ i,x i^2) (by fun_prop)
  exact ⟨hv,fun _ _ _ _ hxy _ _ ha hb hab=>sum_squares_strict.2 (Set.mem_univ _) (Set.mem_univ _) hxy ha hb hab⟩
end
end GrunbaumProof
theorem _root_.Prove2me.Solution.Grunbaum2003_bounded_closed_convex_extreme_representation {d:ℕ} (K:Set (Fin d → ℝ)) (hne:K.Nonempty) (hb:Bornology.IsBounded K)
    (hclosed:IsClosed K) (hconvex:Convex ℝ K) : K=convexHull ℝ (K.extremePoints ℝ) := by
  exact GrunbaumProof.bounded_representation K hb hclosed hconvex

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open scoped Pointwise

namespace Grunbaum2003

theorem bounded_closed_convex_extreme_representation {d : ℕ}
    (K : Set (Fin d → ℝ)) (hne : K.Nonempty) (hb : Bornology.IsBounded K)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    K = convexHull ℝ (K.extremePoints ℝ) :=
  _root_.Prove2me.Solution.Grunbaum2003_bounded_closed_convex_extreme_representation K hne hb hclosed hconvex

end Grunbaum2003

end Prove2meStatement
