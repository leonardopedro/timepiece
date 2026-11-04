import BookProof.ChapterMinMaxSpectrum

/-!
# Axiom audit for `BookProof.ChapterMinMaxSpectrum`

Run with `lake build Work.MinMaxSpectrumAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.MinMaxSpectrum.re_inner_mono_of_le
#print axioms BookProof.MinMaxSpectrum.sandwich_inner_eq
#print axioms BookProof.MinMaxSpectrum.const_inner_eq
#print axioms BookProof.MinMaxSpectrum.rayleighVal_le_of_proj_fixed
#print axioms BookProof.MinMaxSpectrum.le_rayleighVal_of_proj_fixed
#print axioms BookProof.MinMaxSpectrum.cutoff_eq_one
#print axioms BookProof.MinMaxSpectrum.cutoff_eq_zero
#print axioms BookProof.MinMaxSpectrum.cfc_cocutoff
#print axioms BookProof.MinMaxSpectrum.cutoff_idem
#print axioms BookProof.MinMaxSpectrum.cocutoff_idem
#print axioms BookProof.MinMaxSpectrum.rayleighVal_le_of_cutoff_fixed
#print axioms BookProof.MinMaxSpectrum.le_rayleighVal_of_cutoff_zero
#print axioms BookProof.MinMaxSpectrum.minmaxLevel_mem_spectrum
#print axioms BookProof.MinMaxSpectrum.minmaxLevel_zero_mem_spectrum
#print axioms BookProof.MinMaxSpectrum.sInf_spectrum_mem_spectrum
#print axioms BookProof.MinMaxSpectrum.galerkin_minmaxLevel_tendsto_spectrum
#print axioms BookProof.MinMaxSpectrum.galerkin_gap_tendsto_spectrum_sub
#print axioms BookProof.MinMaxSpectrum.rayleighVal_le_of_mem_range
#print axioms BookProof.MinMaxSpectrum.exists_cfc_ne_zero
#print axioms BookProof.MinMaxSpectrum.inner_range_eq_zero
#print axioms BookProof.MinMaxSpectrum.finrank_span_pair
#print axioms BookProof.MinMaxSpectrum.rayleighSup_pair_le
#print axioms BookProof.MinMaxSpectrum.notMem_spectrum_of_mem_minmaxGap
#print axioms BookProof.MinMaxSpectrum.spectrum_inter_minmaxGap_eq_empty
#print axioms BookProof.MinMaxSpectrum.mem_spectrum_of_eigen
#print axioms BookProof.MinMaxSpectrum.cfc_commute
#print axioms BookProof.MinMaxSpectrum.exists_eigenvector_of_minmaxGap
