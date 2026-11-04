import Mathlib

/-!
A. Jaffe, E. Witten, *Quantum Yang–Mills theory*, Clay Mathematics Institute Millennium Prize
Problem description (2000), §4 "The Problem" (p. 6) and §6.5 "Yang–Mills theory" (p. 11).

The objects needed to state the Yang–Mills existence and mass gap problem in the form made
precise by Wilson's lattice approximation (Jaffe–Witten §6.5; K. Osterwalder and E. Seiler,
Ann. Phys. 110 (1978); S. Chatterjee, *Yang–Mills for probabilists*, 2019):

* a **compact simple gauge group** `G`, presented with a faithful finite-dimensional unitary
  representation `ρ : G →* U(N)` (every compact Lie group has one, and a compact group with one is
  a Lie group);
* the **Wilson lattice gauge theory** on the finite lattice `{x ∈ ℤ^d : |x_μ| ≤ R}` with free
  boundary conditions: link variables `U(x, μ) ∈ G`, plaquette holonomies, the Wilson action
  `∑_p Re tr ρ(U_p)`, the product Haar probability measure, and the expectation
  `⟨F⟩ = ∫ F e^{β ∑_p Re tr ρ(U_p)} / ∫ e^{β ∑_p Re tr ρ(U_p)}` at inverse coupling `β`;
* **Wilson loops** `tr ρ(U_γ)`, where `γ` is an axis-parallel closed lattice path with dyadic
  vertices ("dyadic loop"), read at lattice spacing `2^{-k}`; their correlation functions in the
  box of physical half-side `L`;
* the symmetries of the lattice (dyadic translations, coordinate permutations and reflections,
  Osterwalder–Schrader time reflection) acting on loops;
* the axioms imposed on a **continuum theory** `W` (a correlation functional on families of
  loops): being the continuum/infinite-volume limit of the lattice theories after a multiplicative
  renormalization of each loop, lattice Euclidean invariance, reflection positivity, and the
  **mass gap** in Euclidean form (exponential clustering in the time direction), together with
  Jaffe–Witten's requirement that the mass `m = sup Δ` be finite.

Conventions.  `Site d = ℤ^d` are lattice sites, direction `0 : Fin d` is Euclidean time.  A
`Loop d` carries its own scale `k₀`: its integer data describe the physical loop with lattice
spacing `2^{-k₀}`; at a finer scale `k ≥ k₀` it is read by scaling the base point by `2^{k-k₀}`
and subdividing every step into `2^{k-k₀}` unit steps (`Loop.atScale`).  For `k < k₀`,
`Loop.atScale` returns the coarse data unchanged (a junk interpretation that never matters for
limits `k → ∞`; fixed-scale statements carry the hypothesis `γ.scale ≤ k`).  Link variables of
edges outside the box are the junk value `1`.
-/

namespace YangMills

noncomputable section

open MeasureTheory Filter Topology TopologicalSpace

/-! ### The gauge group -/

/-- `G` is a compact simple gauge group in the sense of Jaffe–Witten: connected, non-abelian, and
with no closed normal subgroups other than finite ones and `G` itself.  For a compact Lie group
(which `G` is, as soon as it has a faithful finite-dimensional continuous representation) this is
equivalent to: `G` is connected and its Lie algebra is simple; it allows a finite centre (e.g.
`SU(N)`, `Spin(N)`, `G₂`, …) and excludes tori, `U(N)`, `SO(4)`, and all products. -/
structure IsCompactSimpleGaugeGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop where
  connected : ConnectedSpace G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  normal_finite_or_top : ∀ K : Subgroup G, K.Normal → IsClosed (K : Set G) →
    (K : Set G).Finite ∨ K = ⊤

/-! ### The lattice -/

/-- Lattice sites: `ℤ^d`. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- The unit vector `e_μ`. -/
def unit (d : ℕ) (μ : Fin d) : Site d := Pi.single μ 1

/-- The box `{x ∈ ℤ^d : |x_μ| ≤ R for all μ}`. -/
def box (d : ℕ) (R : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R

/-- A directed edge `(x, μ)` of `ℤ^d`, from `x` to `x + e_μ`. -/
abbrev Edge (d : ℕ) := Site d × Fin d

/-- The edges with both endpoints in the box. -/
def boxEdges (d R : ℕ) : Finset (Edge d) :=
  (box d R ×ˢ Finset.univ).filter fun e => e.1 + unit d e.2 ∈ box d R

/-- A plaquette `(x, μ, ν)`: the unit square with corners `x, x+e_μ, x+e_μ+e_ν, x+e_ν`. -/
abbrev Plaquette (d : ℕ) := Site d × Fin d × Fin d

/-- The plaquettes `(x, μ, ν)` with `μ < ν` and all four corners in the box. -/
def boxPlaquettes (d R : ℕ) : Finset (Plaquette d) :=
  (box d R ×ˢ (Finset.univ ×ˢ Finset.univ)).filter fun p =>
    p.2.1 < p.2.2 ∧ p.1 + unit d p.2.1 ∈ box d R ∧ p.1 + unit d p.2.2 ∈ box d R ∧
      p.1 + unit d p.2.1 + unit d p.2.2 ∈ box d R

/-- A lattice gauge field on the box: one group element per edge of the box. -/
abbrev Config (d R : ℕ) (G : Type*) := boxEdges d R → G

section Lattice

variable {d R : ℕ} {G : Type*} [Group G]

/-- The link variable `U(x, μ)` of an edge; edges outside the box carry the junk value `1`. -/
def link (U : Config d R G) (e : Edge d) : G :=
  if h : e ∈ boxEdges d R then U ⟨e, h⟩ else 1

/-- The plaquette holonomy `U_p = U(x,μ) U(x+e_μ,ν) U(x+e_ν,μ)⁻¹ U(x,ν)⁻¹`. -/
def plaquette (U : Config d R G) (p : Plaquette d) : G :=
  link U (p.1, p.2.1) * link U (p.1 + unit d p.2.1, p.2.2) *
    (link U (p.1 + unit d p.2.2, p.2.1))⁻¹ * (link U (p.1, p.2.2))⁻¹

/-- A gauge transformation `g : ℤ^d → G` acts by `U(x,μ) ↦ g(x) U(x,μ) g(x+e_μ)⁻¹`. -/
def gaugeTransform (g : Site d → G) (U : Config d R G) : Config d R G :=
  fun e => g e.1.1 * U e * (g (e.1.1 + unit d e.1.2))⁻¹

variable {N : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ)

/-- The Wilson action `S(U) = ∑_{p ⊆ box} Re tr ρ(U_p)` (the Gibbs density is `e^{β S}`). -/
noncomputable def wilsonAction (U : Config d R G) : ℝ :=
  ∑ p ∈ boxPlaquettes d R, (Matrix.trace (ρ (plaquette U p) : Matrix (Fin N) (Fin N) ℂ)).re

end Lattice

section Measure

variable {d R : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar probability measure of the compact group `G`. -/
noncomputable def haarProb (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] : Measure G :=
  Measure.haarMeasure (⊤ : PositiveCompacts G)

/-- The product Haar probability measure on the gauge fields of the box. -/
noncomputable def configMeasure (d R : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    Measure (Config d R G) :=
  Measure.pi fun _ => haarProb G

variable {N : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ)

/-- The Gibbs weight `e^{β S(U)}` of the Wilson lattice gauge theory at inverse coupling `β`. -/
noncomputable def gibbsWeight (β : ℝ) (U : Config d R G) : ℝ :=
  Real.exp (β * wilsonAction ρ U)

/-- The expectation `⟨F⟩_{R,β} = ∫ F e^{βS} dU / ∫ e^{βS} dU` of an observable `F` in the
Wilson lattice gauge theory on the box of radius `R`, with free boundary conditions. -/
noncomputable def expectation (β : ℝ) (F : Config d R G → ℂ) : ℂ :=
  (∫ U, F U * (gibbsWeight ρ β U : ℂ) ∂configMeasure d R G) /
    ∫ U, (gibbsWeight ρ β U : ℂ) ∂configMeasure d R G

/-- The single-plaquette probability measure `e^{β Re tr ρ(g)} dg / ∫ e^{β Re tr ρ} dg` on `G`
(used in the exact solution of the two-dimensional theory). -/
noncomputable def plaquetteMeasure (β : ℝ) : Measure G :=
  (ENNReal.ofReal (∫ g, Real.exp (β * (Matrix.trace (ρ g : Matrix (Fin N) (Fin N) ℂ)).re)
      ∂haarProb G))⁻¹ •
    (haarProb G).withDensity fun g =>
      ENNReal.ofReal (Real.exp (β * (Matrix.trace (ρ g : Matrix (Fin N) (Fin N) ℂ)).re))

end Measure

/-! ### Paths and loops -/

/-- A unit step `(μ, b)`: `+e_μ` if `b = true`, `-e_μ` if `b = false`. -/
abbrev Step (d : ℕ) := Fin d × Bool

/-- The displacement of a step. -/
def stepVec {d : ℕ} (s : Step d) : Site d := if s.2 then unit d s.1 else -unit d s.1

section Paths

variable {d : ℕ}

/-- The vertices `x = v₀, v₁, …, v_{m-1}` of the path starting at `x` with steps `s₁, …, s_m`
(the final endpoint `v_m` is not listed; for a closed path it is `v₀`). -/
def pathVertices : Site d → List (Step d) → List (Site d)
  | _, [] => []
  | x, s :: rest => x :: pathVertices (x + stepVec s) rest

/-- The undirected edges of a path, each written as `(lower endpoint, direction)`. -/
def pathEdges : Site d → List (Step d) → List (Edge d)
  | _, [] => []
  | x, s :: rest => (if s.2 then (x, s.1) else (x - unit d s.1, s.1)) :: pathEdges (x + stepVec s) rest

variable {R : ℕ} {G : Type*} [Group G]

/-- The holonomy (ordered product of link variables) along the path from `x` with steps `s`;
a step `-e_μ` from `x` contributes `U(x - e_μ, μ)⁻¹`. -/
def pathHol (U : Config d R G) : Site d → List (Step d) → G
  | _, [] => 1
  | x, s :: rest =>
    (if s.2 then link U (x, s.1) else (link U (x - unit d s.1, s.1))⁻¹) *
      pathHol U (x + stepVec s) rest

end Paths

/-- A dyadic loop: an axis-parallel closed lattice path, read at lattice spacing `2^{-scale}`.
Its physical vertices are `2^{-scale} · v` for the vertices `v` of the path. -/
structure Loop (d : ℕ) where
  /-- the scale `k₀`: the loop lives on the lattice `2^{-k₀} ℤ^d` -/
  scale : ℕ
  /-- the starting vertex, in lattice units at scale `k₀` -/
  base : Site d
  /-- the unit steps -/
  steps : List (Step d)
  /-- the path returns to its starting vertex -/
  closed : (steps.map stepVec).sum = 0

namespace Loop

variable {d : ℕ}

theorem sum_map_stepVec_flatMap_replicate (n : ℕ) (l : List (Step d)) :
    ((l.flatMap (List.replicate n)).map stepVec).sum = n • (l.map stepVec).sum := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, List.map_cons, List.sum_cons, ih, smul_add]

/-- The same physical loop read `j` scales finer: base point scaled by `2^j`, each step
subdivided into `2^j` unit steps. -/
def refine (γ : Loop d) (j : ℕ) : Loop d where
  scale := γ.scale + j
  base := (2 ^ j : ℤ) • γ.base
  steps := γ.steps.flatMap (List.replicate (2 ^ j))
  closed := by rw [sum_map_stepVec_flatMap_replicate, γ.closed, smul_zero]

/-- The lattice path (base point, steps) representing `γ` at scale `k`; meaningful for
`k ≥ γ.scale` (for `k < γ.scale` it returns the data of `γ` unchanged). -/
def atScale (γ : Loop d) (k : ℕ) : Site d × List (Step d) :=
  ((γ.refine (k - γ.scale)).base, (γ.refine (k - γ.scale)).steps)

/-- The vertices of `γ` at its own scale (each listed once for a simple loop). -/
def vertices (γ : Loop d) : List (Site d) := pathVertices γ.base γ.steps

/-- The vertices of `γ` read at scale `k`. -/
def verticesAt (γ : Loop d) (k : ℕ) : List (Site d) :=
  pathVertices (γ.atScale k).1 (γ.atScale k).2

/-- The undirected edges of `γ` at its own scale. -/
def edges (γ : Loop d) : List (Edge d) := pathEdges γ.base γ.steps

/-- `γ` is a simple closed curve: non-empty, visits no vertex twice, traverses no edge twice. -/
def IsSimple (γ : Loop d) : Prop := γ.steps ≠ [] ∧ γ.vertices.Nodup ∧ γ.edges.Nodup

/-- Two dyadic loops are disjoint as subsets of `ℝ^d`: read at the finer of their two scales,
they share no vertex. -/
def Disjoint (γ₁ γ₂ : Loop d) : Prop :=
  List.Disjoint (γ₁.verticesAt (max γ₁.scale γ₂.scale)) (γ₂.verticesAt (max γ₁.scale γ₂.scale))

/-- All vertices of `γ` (read at scale `k`) lie in the box of radius `R`. -/
def InBox (γ : Loop d) (k R : ℕ) : Prop := ∀ x ∈ γ.verticesAt k, x ∈ box d R

/-- Translation of `γ` by the dyadic vector `2^{-j} v`. -/
def translate (γ : Loop d) (j : ℕ) (v : Site d) : Loop d where
  scale := max γ.scale j
  base := (γ.refine (max γ.scale j - γ.scale)).base + (2 ^ (max γ.scale j - j) : ℤ) • v
  steps := (γ.refine (max γ.scale j - γ.scale)).steps
  closed := (γ.refine (max γ.scale j - γ.scale)).closed

section Time

variable [NeZero d]

/-- Translation of `γ` forward in Euclidean time (direction `0`) by `n · 2^{-j}`. -/
def timeTranslate (γ : Loop d) (j n : ℕ) : Loop d := γ.translate j ((n : ℤ) • unit d 0)

/-- All vertices of `γ` have time coordinate `≥ 0`. -/
def PositiveTime (γ : Loop d) : Prop := ∀ x ∈ γ.vertices, 0 ≤ x 0

/-- All vertices of `γ` have time coordinate `> 0`. -/
def StrictlyPositiveTime (γ : Loop d) : Prop := ∀ x ∈ γ.vertices, 0 < x 0

/-- Time reflection `(x₀, x⃗) ↦ (-x₀, x⃗)` on sites. -/
def timeFlip (x : Site d) : Site d := fun μ => if μ = 0 then -x μ else x μ

theorem timeFlip_add (x y : Site d) : timeFlip (x + y) = timeFlip x + timeFlip y := by
  funext μ; simp only [timeFlip, Pi.add_apply]; split_ifs <;> ring

theorem timeFlip_zero : timeFlip (0 : Site d) = 0 := by
  funext μ; simp [timeFlip]

/-- Time reflection as an additive map. -/
def timeFlipHom : Site d →+ Site d where
  toFun := timeFlip
  map_zero' := timeFlip_zero
  map_add' := timeFlip_add

/-- The step of the reflected-and-reversed loop: time steps keep their sign, spatial steps flip. -/
def reflectStep (s : Step d) : Step d := if s.1 = 0 then s else (s.1, !s.2)

theorem stepVec_reflectStep (s : Step d) : stepVec (reflectStep s) = -timeFlip (stepVec s) := by
  obtain ⟨μ, b⟩ := s
  funext ν
  simp only [reflectStep, stepVec, timeFlip, unit, Pi.neg_apply]
  by_cases hμ : μ = 0 <;> by_cases hν : ν = 0 <;> cases b <;>
    simp [hμ, hν, Pi.single_apply]

theorem sum_map_stepVec_reflect (l : List (Step d)) :
    (((l.map reflectStep).reverse).map stepVec).sum = -timeFlip (l.map stepVec).sum := by
  induction l with
  | nil => simp [timeFlip_zero]
  | cons s l ih =>
    simp only [List.map_cons, List.reverse_cons, List.map_append, List.sum_append, ih,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, stepVec_reflectStep, timeFlip_add]
    abel

/-- The Osterwalder–Schrader reflection of a loop: reflect the time coordinate and reverse the
orientation, so that `tr ρ(U_{reflect γ}) = conj (tr ρ(U_{θγ}))` for unitary `ρ`. -/
def reflect (γ : Loop d) : Loop d where
  scale := γ.scale
  base := timeFlip γ.base
  steps := (γ.steps.map reflectStep).reverse
  closed := by rw [sum_map_stepVec_reflect, γ.closed, timeFlip_zero, neg_zero]

end Time

section Hyperoctahedral

/-- The signed coordinate permutation `x ↦ (ε_μ · x_{σ⁻¹ μ})_μ` of `ℤ^d`, where `ε_μ = ±1`
according to `ε μ = true / false`. -/
def coordMap (σ : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x : Site d) : Site d :=
  fun μ => (if ε μ then 1 else -1) * x (σ.symm μ)

theorem coordMap_add (σ : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (x y : Site d) :
    coordMap σ ε (x + y) = coordMap σ ε x + coordMap σ ε y := by
  funext μ; simp only [coordMap, Pi.add_apply]; ring

theorem coordMap_zero (σ : Equiv.Perm (Fin d)) (ε : Fin d → Bool) :
    coordMap σ ε (0 : Site d) = 0 := by
  funext μ; simp [coordMap]

/-- The signed coordinate permutation as an additive map. -/
def coordMapHom (σ : Equiv.Perm (Fin d)) (ε : Fin d → Bool) : Site d →+ Site d where
  toFun := coordMap σ ε
  map_zero' := coordMap_zero σ ε
  map_add' := coordMap_add σ ε

/-- The image of a step under a signed coordinate permutation. -/
def mapStep (σ : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (s : Step d) : Step d :=
  (σ s.1, s.2 == ε (σ s.1))

theorem stepVec_mapStep (σ : Equiv.Perm (Fin d)) (ε : Fin d → Bool) (s : Step d) :
    stepVec (mapStep σ ε s) = coordMap σ ε (stepVec s) := by
  obtain ⟨μ, b⟩ := s
  funext ν
  simp only [mapStep, stepVec, coordMap, unit]
  by_cases hν : ν = σ μ
  · subst hν
    simp only [Equiv.symm_apply_apply]
    cases b <;> by_cases hε : ε (σ μ) = true <;> simp [hε]
  · have h1 : σ.symm ν ≠ μ := fun h => hν (by rw [← h, Equiv.apply_symm_apply])
    have h2 : (Pi.single (σ μ) (1 : ℤ) : Site d) ν = 0 := Pi.single_eq_of_ne hν 1
    have h3 : (Pi.single μ (1 : ℤ) : Site d) (σ.symm ν) = 0 := Pi.single_eq_of_ne h1 1
    cases b <;> by_cases hε : ε (σ μ) = true <;> simp [hε, h2, h3]

/-- The image of `γ` under the signed coordinate permutation `(σ, ε)` of the hypercubic group. -/
def mapCoords (γ : Loop d) (σ : Equiv.Perm (Fin d)) (ε : Fin d → Bool) : Loop d where
  scale := γ.scale
  base := coordMap σ ε γ.base
  steps := γ.steps.map (mapStep σ ε)
  closed := by
    rw [List.map_map]
    have h1 : (stepVec ∘ mapStep σ ε) = fun s : Step d => coordMapHom σ ε (stepVec s) := by
      funext s; simp [stepVec_mapStep, coordMapHom]
    rw [h1]
    have h2 : (fun s : Step d => coordMapHom σ ε (stepVec s)) = (coordMapHom σ ε) ∘ stepVec := rfl
    rw [h2, ← List.map_map, ← map_list_sum, γ.closed, map_zero]

end Hyperoctahedral

/-- The rectangular loop with corner `0`, extending `T` lattice units in direction `μ` and `R`
in direction `ν`, at scale `k` (so of physical size `2^{-k} T × 2^{-k} R`). -/
def rect (k T R : ℕ) (μ ν : Fin d) : Loop d where
  scale := k
  base := 0
  steps := List.replicate T (μ, true) ++ List.replicate R (ν, true) ++
    List.replicate T (μ, false) ++ List.replicate R (ν, false)
  closed := by
    simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate, stepVec,
      Bool.false_eq_true, ↓reduceIte, smul_neg]
    abel

end Loop

/-! ### Wilson loops and their correlation functions -/

section Observables

variable {d R N : ℕ} {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ)

/-- The Wilson loop `W_γ(U) = tr ρ(U_γ)`, the trace of the holonomy of `U` around `γ` read at
scale `k`. -/
noncomputable def wilsonLoop (U : Config d R G) (k : ℕ) (γ : Loop d) : ℂ :=
  Matrix.trace (ρ (pathHol U (γ.atScale k).1 (γ.atScale k).2) : Matrix (Fin N) (Fin N) ℂ)

/-- The product `∏_{γ ∈ A} W_γ(U)` over a family of loops. -/
noncomputable def loopProduct (U : Config d R G) (k : ℕ) (A : List (Loop d)) : ℂ :=
  (A.map (wilsonLoop ρ U k)).prod

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G]

/-- The correlation function `⟨∏_{γ ∈ A} tr ρ(U_γ)⟩_{k,L,β}` of a family of dyadic loops in the
Wilson lattice gauge theory at lattice spacing `2^{-k}`, in the box of physical half-side `L`
(lattice radius `L · 2^k`), at inverse coupling `β`. -/
noncomputable def loopCorrelation (k L : ℕ) (β : ℝ) (A : List (Loop d)) : ℂ :=
  expectation (R := L * 2 ^ k) ρ β fun U => loopProduct ρ U k A

end Observables

/-! ### Axioms for the continuum theory -/

section Continuum

variable {d : ℕ}

/-- A family of loops is admissible when each loop is simple and the loops are pairwise
disjoint; the continuum theory is only asked to assign correlation functions to such families. -/
def IsAdmissible (A : List (Loop d)) : Prop :=
  (∀ γ ∈ A, γ.IsSimple) ∧ A.Pairwise Loop.Disjoint

variable {N : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ)

/-- `W` is a continuum limit of the Wilson lattice gauge theories with gauge group `(G, ρ)`:
along the lattice spacings `2^{-k}`, with inverse couplings `β k`, boxes of half-side `L k → ∞`,
and positive multiplicative renormalization constants `Z k γ` for each loop, the renormalized
correlation functions of every admissible family of loops converge to `W`. -/
structure IsContinuumLimit (β : ℕ → ℝ) (L : ℕ → ℕ) (Z : ℕ → Loop d → ℝ)
    (W : List (Loop d) → ℂ) : Prop where
  β_pos : ∀ k, 0 < β k
  Z_pos : ∀ k γ, 0 < Z k γ
  L_tendsto : Tendsto L atTop atTop
  tendsto : ∀ A : List (Loop d), IsAdmissible A →
    Tendsto (fun k => ((A.map (Z k)).prod : ℂ) * loopCorrelation ρ k (L k) (β k) A)
      atTop (𝓝 (W A))

/-- Invariance of `W` under the symmetries of the lattice that survive in the continuum:
all dyadic translations and all signed coordinate permutations. -/
structure IsLatticeInvariant (W : List (Loop d) → ℂ) : Prop where
  translate : ∀ (A : List (Loop d)) (j : ℕ) (v : Site d), IsAdmissible A →
    W (A.map fun γ => γ.translate j v) = W A
  mapCoords : ∀ (A : List (Loop d)) (σ : Equiv.Perm (Fin d)) (ε : Fin d → Bool), IsAdmissible A →
    W (A.map fun γ => γ.mapCoords σ ε) = W A

variable [NeZero d]

/-- Osterwalder–Schrader reflection positivity of `W`: for all coefficients `c_i ∈ ℂ` and
admissible families `A_i` of loops with strictly positive time coordinates,
`∑_{i,j} conj(c_i) c_j W(θA_i ∪ A_j)` is real and `≥ 0`, where `θ` is `Loop.reflect`. -/
def IsReflectionPositive (W : List (Loop d) → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (A : Fin n → List (Loop d)),
    (∀ i, IsAdmissible (A i) ∧ ∀ γ ∈ A i, γ.StrictlyPositiveTime) →
    (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * W ((A i).map Loop.reflect ++ A j)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * W ((A i).map Loop.reflect ++ A j)).re

/-- `W` has a mass gap of size at least `Δ`: connected correlations between any two admissible
families of loops decay at least like `e^{-Δ t}` in their Euclidean time separation `t`,
`|W(A ∪ τ_t B) - W(A) W(B)| ≤ C_{A,B} e^{-Δ t}` for all dyadic `t = n / 2^j ≥ 0` for which
`A ∪ τ_t B` is admissible.  Under Osterwalder–Schrader reconstruction this is equivalent to the
Hamiltonian having no spectrum in `(0, Δ)`. -/
def HasMassGap (W : List (Loop d) → ℂ) (Δ : ℝ) : Prop :=
  ∀ A B : List (Loop d), IsAdmissible A → IsAdmissible B → ∃ C : ℝ, ∀ j n : ℕ,
    IsAdmissible (A ++ B.map fun γ => γ.timeTranslate j n) →
    ‖W (A ++ B.map fun γ => γ.timeTranslate j n) - W A * W B‖ ≤
      C * Real.exp (-Δ * ((n : ℝ) / 2 ^ j))

/-- Jaffe–Witten's requirement that the mass `m = sup {Δ : W has mass gap Δ}` be finite:
equivalently the theory is not trivial (its Hamiltonian is not zero). -/
def HasFiniteMass (W : List (Loop d) → ℂ) : Prop := ¬ ∀ Δ : ℝ, HasMassGap W Δ

end Continuum

end

end YangMills

