import BookProof.OSReconstruction.HalfSpaceDiscreteSemigroup
import BookProof.OSReconstruction.HalfSpaceFreeState
import BookProof.OSReconstruction.HalfSpaceLatticeTranslation

/-!
# A concrete half-preserving lattice step, and contractivity on the Gibbs state

`HalfSpaceLatticeTranslation` builds the translation the lattice supplies — the cyclic cell
rotation — and proves that it *cannot* satisfy `PreservesPositiveTime`, because the last positive
cell is rotated onto the first negative one.  That is a genuine obstruction, but it is specific to
the *cyclic* shift: on a block with `halfCells` positive and `halfCells` negative cells, a step that
rotates each half internally never leaves the half it started in.

This module builds that step, shows it is an instance of the one-sided discrete API of
`HalfSpaceDiscreteSemigroup`, and proves the contractivity hypothesis `HsHinvNat` for it on the
finite-volume Gibbs state — not as a hypothesis but as an **equality**, because the state is
rotation invariant.

## Contents

* `cellHalfRotate` — the cell step: `finRotate halfCells` on each half separately, with
  `halfCellFun_cellHalfRotate` recording that it is `Sum.map (finRotate _) (finRotate _)` on the
  cell split;
* `siteHalfRotate` — the same on sites, `μ` fixed, with `coordOf_siteHalfRotate`;
* `isPosCell_cellHalfRotate`, `isPosTime_siteHalfRotate_iff`,
  `isPosTime_siteHalfRotate_pow_iff` — **the step keeps the positive half inside itself**, also
  for every iterate;
* `obsHalfRotate`, `obsHalfRotateₗ`, `obsHalfRotate_add`, `halfRotateTranslation` — the step as
  a `DiscreteTimeTranslation`;
* `preservesPositiveTimeNat_halfRotateTranslation` — **`PreservesPositiveTimeNat` holds**,
  which is exactly what the cyclic shift cannot deliver;
* `cellHalfRotate_flipCell`, `siteHalfRotate_reflectCoord` — the step commutes with the reflection
  (it rotates both halves by the same amount), so it commutes with `θ`;
* `thetaObs_obsHalfRotate` — `θ (T n F) = T n (θ F)`;
* `IsHalfRotateInvariant`, `gibbsFun_obsHalfRotate` — the Gibbs functional is invariant under the
  step for a rotation-invariant grid;
* `hsHinvNat_gibbsHalfSpaceState` — **`HsHinvNat` for the concrete step on the finite-volume Gibbs
  state**, with equality: `⟨T n F, T n F⟩ = ⟨F, F⟩`.

## Boundary

`IsHalfRotateInvariant V` is a hypothesis on the *grid* `V.support`, not on the physics: it says the
declared finite grid of half-configurations is closed under the rotation.  It is satisfied by every
grid of the form `Finset.univ.image (fun k => k • v)`, but no such grid is constructed here.  The
step is a rotation inside the positive half, i.e. a spatial relabelling within the half — it is a
genuine `DiscreteTimeTranslation` and it does preserve positive time, but it is *not* the physical
transfer matrix; what it establishes is that the one-sided API is inhabited, and that `HsHinvNat` is
a theorem (for invariant grids) rather than an unprovable hypothesis.
-/

namespace BookProof.OSReconstruction

open BookProof.BalabanRG BookProof.ReflectionPositivity
open RealInnerProductSpace

noncomputable section

/-! ## The half-preserving cell rotation -/

/-- **The half-preserving cell step**: rotate each time half internally by one cell.  Written
through the cell split `halfCellEquiv`, so bijectivity is inherited. -/
def cellHalfRotate : Equiv.Perm (Fin cellsPerBlock) :=
  (halfCellEquiv.trans (Equiv.sumCongr (finRotate halfCells) (finRotate halfCells))).trans
    halfCellEquiv.symm

/-- On the cell split the step is `Sum.map (finRotate _) (finRotate _)` — in particular it never
swaps the two halves. -/
theorem halfCellFun_cellHalfRotate (c : Fin cellsPerBlock) :
    halfCellFun (cellHalfRotate c) =
      Sum.map (finRotate halfCells) (finRotate halfCells) (halfCellFun c) :=
  halfCellEquiv.right_inv _

/-- The step keeps a cell in its own half. -/
theorem isPosCell_cellHalfRotate (c : Fin cellsPerBlock) :
    (cellHalfRotate c).val < halfCells ↔ c.val < halfCells := by
  fin_cases c <;> decide

/-! ## The step on sites -/

/-- **The half-preserving step on sites**: rotate the cell inside its half, keep `μ`. -/
def siteHalfRotate : Equiv.Perm (Fin latticeDim) :=
  (coordEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin nComponents)) cellHalfRotate)).trans coordEquiv

theorem coordOf_siteHalfRotate (i : Fin latticeDim) :
    coordOf (siteHalfRotate i) = ((coordOf i).1, cellHalfRotate (coordOf i).2) := by
  simp [siteHalfRotate, coordOf, Prod.map]

/-- **The step preserves positive time**: a positive-time site stays positive-time. -/
theorem isPosTime_siteHalfRotate_iff (i : Fin latticeDim) :
    isPosTime (siteHalfRotate i) ↔ isPosTime i := by
  rw [isPosTime, coordOf_siteHalfRotate, isPosTime]
  exact isPosCell_cellHalfRotate _

/-- The same for every iterate of the step. -/
theorem isPosTime_siteHalfRotate_pow_iff (n : ℕ) (i : Fin latticeDim) :
    isPosTime ((siteHalfRotate ^ n) i) ↔ isPosTime i := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, isPosTime_siteHalfRotate_iff]

/-! ## The step on observables -/

/-- **The step on observables**: `(T n F)(z) = F(z ∘ σⁿ)`. -/
def obsHalfRotate (n : ℕ) (F : Observable) : Observable :=
  fun z => F fun i => z ((siteHalfRotate ^ n) i)

/-- The same as a linear map. -/
def obsHalfRotateₗ (n : ℕ) : Observable →ₗ[ℝ] Observable where
  toFun F := obsHalfRotate n F
  map_add' F G := by
    funext z
    simp [obsHalfRotate, Pi.add_apply]
  map_smul' c F := by
    funext z
    simp [obsHalfRotate, Pi.smul_apply]

@[simp]
theorem obsHalfRotateₗ_apply (n : ℕ) (F : Observable) :
    obsHalfRotateₗ n F = obsHalfRotate n F :=
  rfl

/-- **The one-sided semigroup law** on observables. -/
theorem obsHalfRotate_add (m n : ℕ) (F : Observable) :
    obsHalfRotate (m + n) F = obsHalfRotate m (obsHalfRotate n F) := by
  funext z
  simp [obsHalfRotate, pow_add, Equiv.Perm.mul_apply]

/-- **The concrete step as a one-sided discrete-time translation.** -/
def halfRotateTranslation : DiscreteTimeTranslation where
  toFun n := obsHalfRotateₗ n
  map_zero := by
    ext F z
    simp [obsHalfRotateₗ, obsHalfRotate]
  map_add m n := by
    ext F z
    exact congrFun (obsHalfRotate_add m n F) z

/-- **`PreservesPositiveTimeNat` holds for the concrete step.**  The image of a positive-time
observable depends only on `z ∘ σⁿ`, and `σⁿ` keeps the positive half inside itself. -/
theorem preservesPositiveTimeNat_halfRotateTranslation :
    PreservesPositiveTimeNat halfRotateTranslation := by
  intro n F
  change dependsOn (obsHalfRotate n (F : Observable)) posTimeCoords
  intro x y hxy
  refine F.2 (fun i => x ((siteHalfRotate ^ n) i)) (fun i => y ((siteHalfRotate ^ n) i)) ?_
  intro i hi
  exact hxy _ (mem_posTimeCoords.2
    ((isPosTime_siteHalfRotate_pow_iff n i).2 (mem_posTimeCoords.1 hi)))

/-! ## Compatibility with the reflection -/

/-- The half swap commutes with `Sum.map` when the map is the same on both summands. -/
theorem sum_map_swap {α β : Type} (f : α → α) (g : β → β) (s : α ⊕ β) :
    Sum.map g f s.swap = (Sum.map f g s).swap := by
  cases s <;> rfl

/-- The cell step commutes with the half swap: both halves are rotated by the same amount. -/
theorem halfCellFun_cellHalfRotate_flipCell (c : Fin cellsPerBlock) :
    halfCellFun (cellHalfRotate (flipCell c)) = (halfCellFun (cellHalfRotate c)).swap := by
  rw [halfCellFun_cellHalfRotate, halfCellFun_flipCell, sum_map_swap,
    ← halfCellFun_cellHalfRotate]

/-- **The cell step commutes with the reflection of a cell.** -/
theorem cellHalfRotate_flipCell (c : Fin cellsPerBlock) :
    cellHalfRotate (flipCell c) = flipCell (cellHalfRotate c) := by
  apply halfCellEquiv.injective
  change halfCellFun (cellHalfRotate (flipCell c)) = halfCellFun (flipCell (cellHalfRotate c))
  rw [halfCellFun_cellHalfRotate_flipCell, halfCellFun_flipCell]

/-- The reflection of components, as a `coordOf` computation. -/
theorem coordOf_reflectCoord (i : Fin latticeDim) :
    coordOf (reflectCoord i) = ((coordOf i).1, flipCell (coordOf i).2) := by
  unfold reflectCoord
  exact coordOf_coordIdx _

/-- **The site step commutes with the reflection of a site.** -/
theorem siteHalfRotate_reflectCoord (i : Fin latticeDim) :
    siteHalfRotate (reflectCoord i) = reflectCoord (siteHalfRotate i) := by
  apply coordEquiv.symm.injective
  change coordOf (siteHalfRotate (reflectCoord i))
    = coordOf (reflectCoord (siteHalfRotate i))
  rw [coordOf_siteHalfRotate, coordOf_reflectCoord, coordOf_reflectCoord, coordOf_siteHalfRotate,
    cellHalfRotate_flipCell]

/-- The step also commutes with the reflection after any number of iterations. -/
theorem siteHalfRotate_pow_reflectCoord (n : ℕ) (i : Fin latticeDim) :
    (siteHalfRotate ^ n) (reflectCoord i) = reflectCoord ((siteHalfRotate ^ n) i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, siteHalfRotate_reflectCoord, ih, Equiv.Perm.mul_apply]

/-- **`θ` commutes with the step**: the step rotates both halves equally, so reflecting before or
after the step gives the same observable. -/
theorem thetaObs_obsHalfRotate (n : ℕ) (F : Observable) :
    thetaObs (obsHalfRotate n F) = obsHalfRotate n (thetaObs F) := by
  funext z
  simp only [thetaObs_apply, obsHalfRotate]
  congr 1
  funext i
  exact congrArg z (siteHalfRotate_pow_reflectCoord n i).symm

/-! ## Invariance of the Gibbs functional -/

/-- The step on one half-configuration: rotate the cells of the half. -/
def halfIdxRotate : Equiv.Perm HalfIdx :=
  Equiv.prodCongr (Equiv.refl (Fin nComponents)) (finRotate halfCells)

/-- `Sum.map` is functorial. -/
theorem sum_map_comp {α : Type} (f g f' g' : α → α) (s : α ⊕ α) :
    Sum.map f g (Sum.map f' g' s) = Sum.map (f ∘ f') (g ∘ g') s := by
  cases s <;> rfl

/-- The site step in the component coordinates. -/
theorem coordEquiv_symm_siteHalfRotate (i : Fin latticeDim) :
    coordEquiv.symm (siteHalfRotate i)
      = ((coordEquiv.symm i).1, cellHalfRotate (coordEquiv.symm i).2) := by
  simp [siteHalfRotate, Prod.map]

/-- The component split commutes with the step: both halves are rotated the same way. -/
theorem coordSumEquiv_siteHalfRotate (i : Fin latticeDim) :
    coordSumEquiv (siteHalfRotate i)
      = Sum.map halfIdxRotate halfIdxRotate (coordSumEquiv i) := by
  rw [coordSumEquiv_apply, coordEquiv_symm_siteHalfRotate, coordSumEquiv_apply,
    halfCellFun_cellHalfRotate]
  cases h : halfCellFun (coordEquiv.symm i).2 <;> rfl

/-- The same for every iterate of the step. -/
theorem coordSumEquiv_siteHalfRotate_pow (n : ℕ) (i : Fin latticeDim) :
    coordSumEquiv ((siteHalfRotate ^ n) i)
      = Sum.map (halfIdxRotate ^ n) (halfIdxRotate ^ n) (coordSumEquiv i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    have hfun : (⇑(halfIdxRotate ^ n) ∘ ⇑halfIdxRotate)
        = ⇑(halfIdxRotate ^ n * halfIdxRotate) := by
      funext p
      simp [Equiv.Perm.mul_apply]
    rw [pow_succ, Equiv.Perm.mul_apply, ih, coordSumEquiv_siteHalfRotate, sum_map_comp,
      hfun, pow_succ]

/-- **The configuration split commutes with the step**, half by half. -/
theorem configEquiv_comp_siteHalfRotate_pow (n : ℕ) (z : Config) :
    configEquiv (fun i => z ((siteHalfRotate ^ n) i))
      = (fun p => (configEquiv z).1 ((halfIdxRotate ^ n) p),
          fun p => (configEquiv z).2 ((halfIdxRotate ^ n) p)) := by
  refine Prod.ext ?_ ?_
  · funext p
    refine congrArg z (coordSumEquiv.injective ?_)
    rw [Equiv.apply_symm_apply, coordSumEquiv_siteHalfRotate_pow, Equiv.apply_symm_apply]
    rfl
  · funext p
    refine congrArg z (coordSumEquiv.injective ?_)
    rw [Equiv.apply_symm_apply, coordSumEquiv_siteHalfRotate_pow, Equiv.apply_symm_apply]
    rfl

/-- The inverse direction, in terms of half-configurations. -/
theorem configEquiv_symm_comp_siteHalfRotate_pow (n : ℕ) (x y : HalfIdx → ℝ) :
    (fun i => configEquiv.symm (x, y) ((siteHalfRotate ^ n) i))
      = configEquiv.symm (fun i => x ((halfIdxRotate ^ n) i),
          fun i => y ((halfIdxRotate ^ n) i)) := by
  have h := congrArg configEquiv.symm
    (configEquiv_comp_siteHalfRotate_pow n (configEquiv.symm (x, y)))
  simpa using h

/-- The mass action of a half is invariant under a relabelling of its cells. -/
theorem halfAction_comp_perm (e : Equiv.Perm HalfIdx) (x : HalfIdx → ℝ) :
    halfAction (fun i => x (e i)) = halfAction x := by
  simp only [halfAction]
  exact Equiv.sum_comp e (fun i => (x i) ^ 2)

/-- **The Gibbs weights are invariant under a relabelling of the cells.** -/
theorem gibbsWeight_comp_perm (V : GibbsVolume) (e : Equiv.Perm HalfIdx)
    (x : HalfIdx → ℝ) : gibbsWeight V (fun i => x (e i)) = gibbsWeight V x := by
  simp only [gibbsWeight, halfAction_comp_perm e x]

/-- **The grid is closed under the cell relabelling.**  A hypothesis on the declared finite grid
of half-configurations, not on the physics: every grid invariant under a permutation of `HalfIdx`
satisfies it. -/
def IsHalfRotateInvariant (V : GibbsVolume) : Prop :=
  ∀ n : ℕ,
    V.support.image (fun x : HalfIdx → ℝ => fun i => x ((halfIdxRotate ^ n) i)) = V.support

/-- **Reindexing a sum along a self-map that fixes the grid.** -/
theorem sum_comp_of_image_eq {α : Type*} [DecidableEq α] (S : Finset α) (f : α → α)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) (hS : S.image f = S) (g : α → ℝ) :
    ∑ x ∈ S, g (f x) = ∑ x ∈ S, g x := by
  rw [← Finset.sum_image hinj, hS]

/-- **The Gibbs functional is invariant under the half-preserving step**, for a grid closed under
the relabelling: the step only permutes the cells inside each half. -/
theorem gibbsFun_obsHalfRotate (V : GibbsVolume) (hV : IsHalfRotateInvariant V) (n : ℕ)
    (F : Observable) : gibbsFun V (obsHalfRotate n F) = gibbsFun V F := by
  classical
  set e : (HalfIdx → ℝ) → (HalfIdx → ℝ) := fun x i => x ((halfIdxRotate ^ n) i) with he
  have hS : V.support.image e = V.support := hV n
  have hinj : ∀ x ∈ V.support, ∀ y ∈ V.support, e x = e y → x = y := by
    intro x _ y _ h
    funext i
    have h' := congrFun h ((halfIdxRotate ^ n).symm i)
    simpa [he] using h'
  have hw : ∀ x : HalfIdx → ℝ, gibbsWeight V (e x) = gibbsWeight V x := fun x =>
    gibbsWeight_comp_perm V (halfIdxRotate ^ n) x
  have hrewrite : gibbsFun V (obsHalfRotate n F)
      = ∑ x ∈ V.support, gibbsWeight V x *
          (∑ y ∈ V.support, gibbsWeight V y * F (configEquiv.symm (e x, e y))) := by
    simp only [gibbsFun, obsHalfRotate, configEquiv_symm_comp_siteHalfRotate_pow, he,
      Finset.mul_sum, mul_assoc]
  rw [hrewrite]
  calc ∑ x ∈ V.support, gibbsWeight V x *
        (∑ y ∈ V.support, gibbsWeight V y * F (configEquiv.symm (e x, e y)))
      = ∑ x ∈ V.support, (fun u => gibbsWeight V u *
            (∑ y ∈ V.support, gibbsWeight V y *
              F (configEquiv.symm (u, e y)))) (e x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [← hw x]
    _ = ∑ u ∈ V.support, gibbsWeight V u *
          (∑ y ∈ V.support, gibbsWeight V y * F (configEquiv.symm (u, e y))) :=
        sum_comp_of_image_eq V.support e hinj hS
          (fun u => gibbsWeight V u *
            (∑ y ∈ V.support, gibbsWeight V y * F (configEquiv.symm (u, e y))))
    _ = ∑ u ∈ V.support, gibbsWeight V u *
          (∑ v ∈ V.support, gibbsWeight V v * F (configEquiv.symm (u, v))) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        congr 1
        calc ∑ y ∈ V.support, gibbsWeight V y * F (configEquiv.symm (u, e y))
            = ∑ y ∈ V.support, (fun v => gibbsWeight V v *
                F (configEquiv.symm (u, v))) (e y) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              simp only [← hw y]
          _ = ∑ v ∈ V.support, gibbsWeight V v * F (configEquiv.symm (u, v)) :=
              sum_comp_of_image_eq V.support e hinj hS
                (fun v => gibbsWeight V v * F (configEquiv.symm (u, v)))
    _ = gibbsFun V F := by
        rw [gibbsFun]
        simp only [Finset.mul_sum, mul_assoc]

/-- The Gibbs state's OS form, written out. -/
theorem hsBilin_gibbsHalfSpaceState (V : GibbsVolume) (F G : PositiveTimeAlgebra) :
    hsBilin (gibbsHalfSpaceState V) F G
      = gibbsFun V (thetaObs (F : Observable) * (G : Observable)) := rfl

/-- The step is multiplicative on observables. -/
theorem obsHalfRotate_mul (n : ℕ) (A B : Observable) :
    obsHalfRotate n A * obsHalfRotate n B = obsHalfRotate n (A * B) := by
  funext z
  simp only [obsHalfRotate, Pi.mul_apply]

/-- **`HsHinvNat` for the concrete step on the finite-volume Gibbs state** — with *equality*:
the step only relabels cells inside each half, and the Gibbs state is invariant under that, so
`⟨T n F, T n F⟩ = ⟨F, F⟩`. -/
theorem hsHinvNat_gibbsHalfSpaceState (V : GibbsVolume) (hV : IsHalfRotateInvariant V) :
    HsHinvNat (gibbsHalfSpaceState V) halfRotateTranslation
      preservesPositiveTimeNat_halfRotateTranslation := by
  intro n F
  have hT : (hsEvolNat preservesPositiveTimeNat_halfRotateTranslation n F : Observable)
      = obsHalfRotate n (F : Observable) := rfl
  rw [hsBilin_gibbsHalfSpaceState, hsBilin_gibbsHalfSpaceState, hT, thetaObs_obsHalfRotate,
    obsHalfRotate_mul, gibbsFun_obsHalfRotate V hV n]

/-! ## An explicit invariant grid -/

/-- **The grid of constant half-configurations** `0, 1, …, m - 1`.  A cell relabelling fixes every
constant configuration, so this grid satisfies `IsHalfRotateInvariant`, which makes
`hsHinvNat_gibbsHalfSpaceState` unconditional. -/
def constGrid (m : ℕ) (hm : 0 < m) : GibbsVolume where
  support := by
    classical
    exact Finset.univ.image (fun k : Fin m => fun _ : HalfIdx => (k : ℝ))
  support_nonempty := by
    classical
    refine ⟨fun _ => ((⟨0, hm⟩ : Fin m) : ℝ),
      Finset.mem_image.2 ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩⟩

theorem mem_constGrid {m : ℕ} (hm : 0 < m) {x : HalfIdx → ℝ} :
    x ∈ (constGrid m hm).support ↔ ∃ k : Fin m, x = fun _ => (k : ℝ) := by
  classical
  simp only [constGrid, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- **The explicit grid is rotation invariant**: every element is a constant configuration. -/
theorem isHalfRotateInvariant_constGrid (m : ℕ) (hm : 0 < m) :
    IsHalfRotateInvariant (constGrid m hm) := by
  classical
  intro n
  have hfix : ∀ x ∈ (constGrid m hm).support,
      (fun i => x ((halfIdxRotate ^ n) i)) = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := (mem_constGrid hm).1 hx
    funext i
    rfl
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [hfix x hx]
    exact hx
  · intro hy
    exact Finset.mem_image.2 ⟨y, hy, hfix y hy⟩

/-- **`HsHinvNat` with no hypothesis left**: the concrete step on the Gibbs state of the explicit
constant grid satisfies the one-sided contractivity estimate. -/
theorem hsHinvNat_constGrid (m : ℕ) (hm : 0 < m) :
    HsHinvNat (gibbsHalfSpaceState (constGrid m hm)) halfRotateTranslation
      preservesPositiveTimeNat_halfRotateTranslation :=
  hsHinvNat_gibbsHalfSpaceState _ (isHalfRotateInvariant_constGrid m hm)

/-- The descended one-sided transfer on that state is a contraction. -/
theorem constGrid_transfer_contractive (m : ℕ) (hm : 0 < m) (n : ℕ)
    (x : HsSpace (gibbsHalfSpaceState (constGrid m hm))) :
    ‖hsQuotMapNat (gibbsHalfSpaceState (constGrid m hm)) halfRotateTranslation
      preservesPositiveTimeNat_halfRotateTranslation (hsHinvNat_constGrid m hm) n x‖ ≤ ‖x‖ :=
  hsQuotMapNat_contractive _ _ _ (hsHinvNat_constGrid m hm) n x

end

end BookProof.OSReconstruction
