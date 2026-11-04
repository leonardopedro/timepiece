import BookProof.ChapterBookBrstYangMills
import BookProof.ChapterBookBrstGaugeFixing
import BookProof.ChapterBookBrstInstances

/-!
Axiom audit for the implementation of the BRST formalism **as defined in `book.tex`**
(§"Pure SU(3) Yang-Mills theory"): the charge
`Ω = π^μ_a ∂_μψ†_a − π^μ_a f_{abc} A_{μb} ψ†_c − (i/2) f_{abc} ψ†_aψ†_bψ_c`, its canonical
relations, the Gauss-law constraint algebra, nilpotency, the gauge-fixing fermion
`Ψ = i ψ_a A_{0a}` and the gauge algebras it is instantiated with.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- 1. The canonical (anti)commutation relations of the book's section.
#print axioms BookProof.BookBrstYangMills.bookCCR_poly
#print axioms BookProof.BookBrstYangMills.bookCCR
#print axioms BookProof.BookBrstYangMills.bookGhostCar
#print axioms BookProof.BookBrstYangMills.Afield_comm_chi
#print axioms BookProof.BookBrstYangMills.mom_comm_chi

-- 2. The Gauss-law constraint algebra, derived from those relations.
#print axioms BookProof.BookBrstYangMills.gauss_const_identity
#print axioms BookProof.BookBrstYangMills.gauss_field_identity
#print axioms BookProof.BookBrstYangMills.gaussDer_bracket
#print axioms BookProof.BookBrstYangMills.gaussGenPoly_bracket
#print axioms BookProof.BookBrstYangMills.gaussGen_bracket
#print axioms BookProof.BookBrstYangMills.gaussGenPoly_eq
#print axioms BookProof.BookBrstYangMills.bookConstraintAlgebra

-- 3. The book's charge and its nilpotency.
#print axioms BookProof.BookBrstYangMills.I_smul_gaussGen
#print axioms BookProof.BookBrstYangMills.bookOmega_eq_brstCharge
#print axioms BookProof.BookBrstYangMills.bookOmega_nilpotent

-- 4. The gauge-fixing fermion.
#print axioms BookProof.BookBrstGaugeFixing.glin_gf_anticomm
#print axioms BookProof.BookBrstGaugeFixing.Q_gf_anticomm
#print axioms BookProof.BookBrstGaugeFixing.brstCharge_gf_anticomm
#print axioms BookProof.BookBrstGaugeFixing.brst_exact_comm
#print axioms BookProof.BookBrstGaugeFixing.bookGfTerm_eq
#print axioms BookProof.BookBrstGaugeFixing.bookGfTerm_brst_closed

-- 4b. Accounting identity: vanishing at A_0 = 0 (QYM/SM; QG is non-ADM, see module docs).
#print axioms BookProof.BookBrstGaugeFixing.gfFermion_eq_zero
#print axioms BookProof.BookBrstGaugeFixing.bookGfFermion_eq_zero_of_Afield0
#print axioms BookProof.BookBrstGaugeFixing.bookGfTerm_eq_zero_of_Afield0
#print axioms BookProof.BookBrstInstances.su2_bookGfTerm_eq_zero_of_Afield0
#print axioms BookProof.BookBrstInstances.sm_bookGfTerm_eq_zero_of_Afield0

-- 5. The gauge algebras and non-vacuity.
#print axioms BookProof.BookBrstInstances.innerDeriv_leibniz
#print axioms BookProof.BookBrstInstances.su2_bookOmega_nilpotent
#print axioms BookProof.BookBrstInstances.sm_bookOmega_nilpotent
#print axioms BookProof.BookBrstInstances.su2_gaussGenPoly_ne_zero

-- 6. BRST cohomology of the book's charge.
#print axioms BookProof.BookBrstGaugeFixing.exactStates_le_physicalStates
#print axioms BookProof.BookBrstGaugeFixing.bookGfTerm_mem_physicalStates
#print axioms BookProof.BookBrstGaugeFixing.bookGfTerm_mem_exactStates

-- 7. Gauge-invariant observables.
#print axioms BookProof.BookBrstGaugeFixing.brstCharge_comm_of_comm
#print axioms BookProof.BookBrstGaugeFixing.bookOmega_comm_multOp
#print axioms BookProof.BookBrstGaugeFixing.casimir_bookOmega_comm
#print axioms BookProof.BookBrstInstances.su2_casimir_bookOmega_comm
