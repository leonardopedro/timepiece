# Summary of changes for run 8c1a652e-a861-4b69-9c74-5c967943edf4
I proved that the Koopman comparison operator \(N_L = H_L^2 + E\) is essentially self-adjoint, with no extra hypotheses. Everything builds, with no `sorry` and no new axioms.

**What is proved** (new file `BookProof/ChapterNsLagrangianComparisonEsa.lean`):
- `lagComparison_esa`: \(N_L = H_L^2 + 1 + \tfrac12|v|^2 + V_\kappa(\xi)\) is essentially self-adjoint on the Gauss–polynomial core of \(L^2(\mathbb R^{\mathrm{PIdx}\,K})\). This holds for every finite set of wave vectors, every \(\nu \ge 0\) and every \(\kappa \ge 0\). Before this, it was the assumption that `lagKoopman_esa_of_comparison_esa` had to take as a hypothesis.
- `lagKoopman_esa`: as a result, the Lagrangian Navier–Stokes Koopman generator \(H_L\) is itself essentially self-adjoint on that core.

**How:** the proof uses the existing criterion `KvnKato.lyapunovComparison_esa_poly` in `BookProof/ChapterKvnKatoPoly.lean`. It requires a polynomial \(P\) with \(\|y\| \le P(y)\) and \(|F\cdot\nabla P| \le c\,P\). The energy \(E\) can't serve as \(P\), because the penalty is zero on the unbounded incompressible set, so \(E\) does not grow in every direction. I used \(P = E + \tfrac12|\xi|^2\) instead:
- \(F\cdot\nabla P = -\nu\sum|k|^2 v^2 + \xi\cdot v\) (`lagLyapFlux_eq`);
- \(|F\cdot\nabla P| \le (2\nu\Lambda + 1)P\) (`abs_eval_lagLyapFlux_le`);
- \(\|y\| \le 1 + \tfrac12\|y\|^2 \le P(y)\) (`norm_le_lagP`).

**Wiring and records:**
- The new chapter is imported from `BookProof.lean`, which also brings the `ChapterKvnKato*` chapters into the main library for the first time.
- Two `#print axioms` lines were added to `BookProof/ChapterRoadmapAudit.lean`. That file builds, and both lines report only `propext, Classical.choice, Quot.sound`.
- I appended new dated entries to `STATUS.md` and `CONSOLIDATED_PLAN.md` (§"2026-10-16") without editing older entries.

**Heartbeat of `qgFlatL2Op_tmul`:** the file already has `set_option maxHeartbeats 8000000` on that theorem, so I didn't change it. `BookProof/ChapterQgFlatContinuumEsa.lean` builds successfully at that setting.

**Limits:** the result has the same scope as `ChapterNsLagrangianDetFarisLavine`: a finite Galerkin truncation, a finite bulk modulus \(\kappa\) (no \(\kappa\to\infty\) limit), and the viscous term taken at \(F = I\). It makes no claim about continuum Navier–Stokes regularity.

All work is committed and pushed.