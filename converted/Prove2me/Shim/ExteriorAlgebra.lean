import Mathlib

/-!
# Shim: the basis of an exterior algebra induced by a basis of the module

The platform Mathlib provides `Module.Basis.ExteriorAlgebra`, the basis of `ExteriorAlgebra R M`
indexed by `Finset I` induced by a basis `b : Basis I R M` (over a linearly ordered `I`), which
the pinned Mathlib lacks.  It is assembled here from the pinned bases of the exterior powers
(`Module.Basis.exteriorPower`) and the grading `ExteriorAlgebra R M ≃ ⨁ n, ⋀[R]^n M`; the basis
vector of index `s` is the wedge product of the `b i`, `i ∈ s`, in increasing order.
-/

namespace Module.Basis

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]

/-- The basis of `ExteriorAlgebra R M`, indexed by `Finset I`, induced by `b : Basis I R M`. -/
noncomputable def ExteriorAlgebra (b : Basis I R M) : Basis (Finset I) R (ExteriorAlgebra R M) :=
  ((DFinsupp.basis fun n : ℕ => b.exteriorPower n).map
      (DirectSum.decomposeLinearEquiv (fun n : ℕ => ⋀[R]^n M)).symm).reindex
    ((Equiv.sigmaCongrRight fun _ => Equiv.subtypeEquivRight fun _ => Iff.rfl).trans
      (Equiv.sigmaFiberEquiv fun s : Finset I => s.card))

end Module.Basis
