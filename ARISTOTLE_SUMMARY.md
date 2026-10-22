# Summary of changes for run d5df5823-3d2d-4b85-95ec-175932ea4f8f
The per-example gradient bound that `NGPTModel` previously had to assume is now proved from the network's architecture. It holds on the region where every weight has norm at least some fixed \(\varepsilon>0\), not for all parameters. A global bound is impossible: the loss doesn't change when a weight is rescaled, so its gradient grows like \(1/\|W\|\) as \(W\to0\).

`lake build BayesianTransformer` succeeds with no warnings. There is no `sorry`, `admit` or `axiom`, and the main theorems use only `propext`, `Classical.choice` and `Quot.sound`.

**The network** (`BayesianTransformer/Transformer/NGPTArchitecture.lean`)
- **Parameters:** each layer has six weight matrices (`W_q, W_k, W_v, W_o, W_up, W_down`), and each vocabulary item has one output vector. Every weight is used only in normalized form \(\hat W=W/\|W\|\).
- **Attention:** logits \(s_{qk}\langle \hat W_q h_i,\hat W_k h_j\rangle\), then softmax, then \(a_i=\hat W_o\sum_j p_{ij}\hat W_v h_j\).
- **Updates:** \(h'=\mathrm{Norm}(h+\alpha_A(a-h))\), then an MLP \(\hat W_{down}\,\sigma(\hat W_{up}h')\) with the same kind of update.
- **Output and loss:** cosine logits \(s_z\langle\hat u_v,h^L_i\rangle\). The loss for one example is the cross entropy averaged over positions.
- **Activation:** any \(\sigma\) with Lipschitz constant 1 and \(\sigma(0)=0\). Coordinatewise ReLU on \(\mathbb R^d\) is proved to qualify (`NGPTConfig.relu`).

**Proved results**
- `ngpt_exampleLoss_lipOn`: there is one constant \(M\) such that every example's loss is \(M\)-Lipschitz in the parameters on that region. \(M\) depends only on the hyperparameters, \(\varepsilon\), the depth and the sequence length.
- `ngpt_exampleLoss_fderiv_bound`: \(\|\nabla_\theta\ell(\theta;x,y)\|\le M\) for every parameter in the region and every example. This is the bound `NGPTModel` assumed.
- `ngpt_empiricalRisk_fderiv_bound`: the same kind of ceiling for the average loss over any dataset (Theorem 1 for this network).

**How the proof works:** normalization \(v\mapsto v/\|v\|\) is \(2/\delta\)-Lipschitz wherever \(\|v\|\ge\delta\). Softmax is 2-Lipschitz (from the earlier work), and cross entropy is 2-Lipschitz in the logits. Each block's Lipschitz constant is tracked through the layers by induction, and the gradient bound follows from the Lipschitz bound. The general tools for this are in the new file `BayesianTransformer/Transformer/LipschitzCalculus.lean`.

**Where this differs from the nGPT paper.** These choices were needed to get a bound that holds uniformly:
- Matrices are normalized by their operator norm, not row by row.
- Queries, keys and sublayer outputs are not re-normalized. Normalizing a vector that can be zero isn't Lipschitz. Their norms are still at most 1 because the weights are normalized.
- \(s_{qk}\), \(s_z\), \(\alpha_A\) and \(\alpha_M\) are fixed hyperparameters, with \(0\le\alpha<1/2\). That condition makes every hidden-state normalization act on a vector of norm at least \(1-2\alpha>0\). If these were trainable and unbounded, no uniform bound could hold.
- Input embeddings are unit vectors supplied with each example, not trained parameters.
- At points where the loss isn't differentiable (for example, ReLU kinks), Lean defines the derivative as 0, so the gradient bound holds there trivially. The Lipschitz bound is the substantive statement.

I also added a pointer in `GlobalLipschitz.lean` and imports in `Main.lean`. The new results are registered in the Properties table and the work is committed and pushed.