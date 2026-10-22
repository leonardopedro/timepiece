module

public import BayesianTransformer.Analysis.SphereProj
public import BayesianTransformer.Analysis.ScaleInvariance
public import BayesianTransformer.Transformer.CosineAttention
public import BayesianTransformer.Transformer.GlobalLipschitz
public import BayesianTransformer.Transformer.LipschitzCalculus
public import BayesianTransformer.Transformer.NGPTArchitecture
public import BayesianTransformer.Probability.GradientNoise

/-!
# Dimension-Robust Bayesian Transformers: root export

Imports all verified modules of the formalization:

* `Analysis.SphereProj` — differential and operator-norm bounds of `v ↦ v / ‖v‖` (Milestone 1)
* `Analysis.ScaleInvariance` — Euler's theorem in degree zero, orthogonal drift (Milestone 2)
* `Transformer.CosineAttention` — bounded cosine logits, softmax bounds and Lipschitz (Milestone 3)
* `Transformer.GlobalLipschitz` — universal gradient ceiling, Theorem 1 (Milestone 4)
* `Transformer.LipschitzCalculus` — Lipschitz constants of parameter-dependent maps
* `Transformer.NGPTArchitecture` — the per-example gradient bound derived from a concrete
  normalized-transformer architecture
* `Probability.GradientNoise` — uniformly bounded SG-pCNL noise covariance (Milestone 5)
-/
