The equivalence between the Feynman path integral and the Hamiltonian (canonical) formalism is typically proved using time-slicing (Trotterization) and the insertion of complete sets of position and momentum eigenstates.
This exact derivation appears in standard texts such as Feynman & Hibbs (Quantum Mechanics and Path Integrals), Sakurai (Modern Quantum Mechanics), and Peskin & Schroeder (An Introduction to Quantum Field Theory). Here is the step-by-step proof for a single non-relativistic particle in one dimension, using an infinitesimal damping factor (\(i\epsilon\)) to ensure convergence.

1. Setup and Time-Slicing

In the Hamiltonian formalism, the probability amplitude (propagator) for a particle to travel from position \(q_{a}\) at time \(t_{a}\) to \(q_{b}\) at time \(t_{b}\) is given by the matrix element of the time-evolution operator:
\(K(q_{b},t_{b};q_{a},t_{a})=\langle q_{b}|{}e^{-\frac{i}{\hbar }\^{H}(t_{b}-t_{a})}|{}q_{a}\rangle \)
Assume a standard Hamiltonian separated into kinetic and potential operators:
\(\^{H}=\^{T}(\^{p})+\^{V}(\^{q})=\frac{\^{p}^{2}}{2m}+V(\^{q})\)
Divide the total time interval \(T = t_b - t_a\) into \(N\) small, equal steps of duration \(\epsilon = \frac{T}{N}\), where \(t_j = t_a + j\epsilon\) for \(j = 0, 1, \dots, N\) (with \(q_0 = q_a\) and \(q_N = q_b\)). The evolution operator splits into \(N\) identical factors:
\(e^{-\frac{i}{\hbar }\^{H}T}=\underbrace{e^{-\frac{i}{\hbar }\^{H}\epsilon }e^{-\frac{i}{\hbar }\^{H}\epsilon }\cdots e^{-\frac{i}{\hbar }\^{H}\epsilon }}_{N\text{\ times}}\)

2. Inserting Complete Sets of Position States

Insert the identity operator \(\hat{I} = \int dq_j \, \vert{}q_j\rangle \langle q_j\vert{}\) between every adjacent pair of infinitesimal evolution operators:
\(K(q_{b},t_{b};q_{a},t_{a})=\int \left(\prod _{j=1}^{N-1}dq_{j}\right)\prod _{j=0}^{N-1}\langle q_{j+1}|{}e^{-\frac{i}{\hbar }\^{H}\epsilon }|{}q_{j}\rangle \)
This reduces the problem to evaluating a single infinitesimal time-step amplitude: \(\langle q_{j+1} \vert{} e^{-\frac{i}{\hbar} (\hat{T} + \hat{V}) \epsilon} \vert{} q_j \rangle\).

3. Trotter Approximation and Momentum Insertion

Because \(\^{T}\) and \(\^{V}\) do not commute, \(e^{-\frac{i}{\hbar}(\hat{T}+\hat{V})\epsilon} \neq e^{-\frac{i}{\hbar}\hat{T}\epsilon} e^{-\frac{i}{\hbar}\hat{V}\epsilon}\). However, by the Baker–Campbell–Hausdorff formula (or Lie–Trotter product formula), the error is of order \(\mathcal{O}(\epsilon^2)\):
\(e^{-\frac{i}{\hbar }(\^{T}+\^{V})\epsilon }=e^{-\frac{i}{\hbar }\^{T}\epsilon }e^{-\frac{i}{\hbar }\^{V}\epsilon }+\mathcal{O}(\epsilon ^{2})\)
In the limit \(N \to \infty\) (\(\epsilon \to 0\)), the accumulated \(\mathcal{O}(\epsilon^2)\) errors across \(N\) steps vanish as \(N\epsilon^2 = T\epsilon \to 0\).
Now evaluate the single step by inserting a complete set of momentum eigenstates \(\hat{I} = \int \frac{dp_j}{2\pi\hbar} \, \vert{}p_j\rangle \langle p_j\vert{}\) between the kinetic and potential operators:
\(\begin{aligned}\langle q_{j+1}|{}e^{-\frac{i}{\hbar }\^{T}\epsilon }e^{-\frac{i}{\hbar }\^{V}\epsilon }|{}q_{j}\rangle &=\int \frac{dp_{j}}{2\pi \hbar }\langle q_{j+1}|{}e^{-\frac{i}{\hbar }\frac{\^{p}^{2}}{2m}\epsilon }|{}p_{j}\rangle \langle p_{j}|{}e^{-\frac{i}{\hbar }V(\^{q})\epsilon }|{}q_{j}\rangle \\ &=\int \frac{dp_{j}}{2\pi \hbar }e^{-\frac{i}{\hbar }\frac{p_{j}^{2}}{2m}\epsilon }e^{-\frac{i}{\hbar }V(q_{j})\epsilon }\langle q_{j+1}|{}p_{j}\rangle \langle p_{j}|{}q_{j}\rangle \end{aligned}\)
Using the standard plane-wave inner products \(\langle q \vert{} p \rangle = e^{\frac{i}{\hbar}pq}\) and \(\langle p \vert{} q \rangle = e^{-\frac{i}{\hbar}pq}\), we obtain the phase-space path integral slice:
\(\langle q_{j+1}|{}e^{-\frac{i}{\hbar }\^{H}\epsilon }|{}q_{j}\rangle \approx \int \frac{dp_{j}}{2\pi \hbar }\exp \left[\frac{i\epsilon }{\hbar }\left(p_{j}\frac{q_{j+1}-q_{j}}{\epsilon }-H(p_{j},q_{j})\right)\right]\)

4. Integrating Out Momentum (Gaussian Integral & Damping)

To move from phase space to configuration space (the Lagrangian formulation), perform the Gaussian integral over \(p_{j}\):
\(I_{p}=\int _{-\infty }^{\infty }\frac{dp_{j}}{2\pi \hbar }\exp \left[-\frac{i\epsilon }{2m\hbar }p_{j}^{2}+\frac{i}{\hbar }p_{j}(q_{j+1}-q_{j})\right]\)
Because the exponent is purely imaginary, the integral oscillates endlessly at infinity. To make it converge rigorously, either:
1. Wick rotate to Euclidean time (\(t \to -i\tau\), so \(\epsilon \to -i\epsilon_\tau\)), turning the oscillating exponent into a decaying real Gaussian, or
2. Add an infinitesimal damping factor by replacing \(m \to m(1 + i\delta)\) (or \(\epsilon \to \epsilon - i\delta\)) with \(\delta \to 0^+\).
Applying the standard Gaussian integral formula \(\int_{-\infty}^{\infty} e^{-a p^2 + b p} \, dp = \sqrt{\frac{\pi}{a}} e^{\frac{b^2}{4a}}\) with \(a = \frac{i\epsilon}{2m\hbar}\) and \(b = \frac{i(q_{j+1}-q_j)}{\hbar}\):
\(I_{p}=\frac{1}{2\pi \hbar }\sqrt{\frac{2\pi m\hbar }{i\epsilon }}\exp \left[\frac{im(q_{j+1}-q_{j})^{2}}{2\hbar \epsilon }\right]=\sqrt{\frac{m}{2\pi i\hbar \epsilon }}\exp \left[\frac{i\epsilon }{\hbar }\frac{m}{2}\left(\frac{q_{j+1}-q_{j}}{\epsilon }\right)^{2}\right]\)

5. Taking the Continuum Limit

Substitute \(I_{p}\) back into the product over all \(N\) time slices:
\(K(q_{b},t_{b};q_{a},t_{a})=\lim _{N\rightarrow \infty }\left(\frac{m}{2\pi i\hbar \epsilon }\right)^{\frac{N}{2}}\int \left(\prod _{j=1}^{N-1}dq_{j}\right)\exp \left[\frac{i}{\hbar }\sum _{j=0}^{N-1}\epsilon \left(\frac{m}{2}\left(\frac{q_{j+1}-q_{j}}{\epsilon }\right)^{2}-V(q_{j})\right)\right]\)
In the limit \(N \to \infty\) (\(\epsilon \to 0\)):
• The finite difference \(\frac{q_{j+1}-q_{j}}{\epsilon }\) becomes the velocity \(\dot{q}(t)\).
• The summand becomes the classical Lagrangian \(L(q, \dot{q}) = \frac{1}{2}m\dot{q}^2 - V(q)\).
• The Riemann sum \(\sum_{j=0}^{N-1} \epsilon L_j\) converges to the classical action functional \(S[q(t)] = \int_{t_a}^{t_b} dt \, L(q, \dot{q})\).
• The integration measure \(\lim_{N \to \infty} \left( \frac{m}{2\pi i \hbar \epsilon} \right)^{\frac{N}{2}} \prod_{j=1}^{N-1} dq_j\) is denoted formally as \(\mathcal{D}q(t)\).
This yields the Feynman path integral:
\(\langle q_{b}|{}e^{-\frac{i}{\hbar }\^{H}(t_{b}-t_{a})}|{}q_{a}\rangle =\int _{q(t_{a})=q_{a}}^{q(t_{b})=q_{b}}\mathcal{D}q(t)\,e^{\frac{i}{\hbar }S[q(t)]}\)

Note on Operator Ordering (The Midpoint Rule)

If the Hamiltonian contains cross-terms between position and momentum (such as a particle in a magnetic field, \(\hat{H} = \frac{1}{2m}(\hat{p} - eA(\hat{q}))^2\), or curved space), evaluating \(V\) at \(q_{j}\) introduces an \(\mathcal{O}(\epsilon)\) ambiguity because \(\Delta q \sim \sqrt{\epsilon}\) in path integrals. To preserve equivalence with Weyl-ordered Hamiltonians, the potential or vector potential must be evaluated at the midpoint \(\bar{q}_j = \frac{q_{j+1} + q_j}{2}\).
If you'd like to explore a specific extension of this proof, let me know if you want to see:
The Wick-rotated Euclidean version and its connection to the Feynman–Kac formula and statistical mechanicsThe Quantum Field Theory (QFT) generalization using fields \(\phi(x)\) and conjugate momenta \(\pi(x)\)The reverse derivation (starting from the path integral to derive the Schrödinger equation)


That specific nuance comes from the boundary conditions at infinite time (\(T \to \infty\)) required when deriving vacuum expectation values (Green's functions) in Quantum Field Theory, which is famously highlighted in Weinberg’s The Quantum Theory of Fields (https://www.google.com/search?kgmid=%2Fg%2F11gk9mdllp&q=there+is+in+some+physics+book+a+proof+of+the+equivalence+between+the+feynman+path+integral+%28perhaps+in+its+euclidean+wick-rotated+version%2C+or+just+infinitesimally+damped+%29+and+the+Hamiltonian+formalism+.+Write+that+proof+here+the+quantum+theory+of+fields) (Vol. 1, Chapter 9) as well as Peskin & Schroeder (Chapter 9) and treatments of Spontaneous Symmetry Breaking (SSB). [1] (https://arxiv.org/abs/0810.1412), [2] (https://ocw.mit.edu/courses/8-323-relativistic-quantum-field-theory-i-spring-2023/mit8_323_s23_pset06.pdf)
When you try to prove that the path integral reproduces the canonical vacuum expectation values \(\langle \Omega \vert{} T \{ \hat{\phi}(x_1) \cdots \hat{\phi}(x_n) \} \vert{} \Omega \rangle\), the standard derivation fails if the field has a non-zero vacuum expectation value (\(\langle \Omega \vert{} \hat{\phi} \vert{} \Omega \rangle = v \neq 0\)) unless you shift the field or adjust the boundary conditions.
Here is the exact proof showing why a non-zero VEV breaks the naive equivalence.

1. Projecting onto the Vacuum State

To get vacuum expectation values in the Hamiltonian formalism, we start with field eigenstates \(\vert{}\phi_a\rangle\) and \(\vert{}\phi_b\rangle\) at times \(t = -T\) and \(t = +T\), and apply the damping factor \(H \to H(1 - i\epsilon)\) (or Wick-rotate \(T \to -i\infty\)) to project out all excited states: [1] (https://www.thphys.uni-heidelberg.de/~hebecker/QFTII/notes-now.pdf), [2] (http://www.personal.soton.ac.uk/ab1u06/teaching/qft/qft1/qft_2.pdf)
\(e^{-i\^{H}(1-i\epsilon )T}|{}\phi _{a}\rangle =\sum _{n}e^{-iE_{n}(1-i\epsilon )T}|{}n\rangle \langle n|{}\phi _{a}\rangle \xrightarrow{T\rightarrow \infty }e^{-iE_{0}(1-i\epsilon )T}|{}\Omega \rangle \langle \Omega |{}\phi _{a}\rangle \)
For this projection to survive, the boundary state \(\vert{}\phi_a\rangle\) must have a non-zero overlap with the true vacuum state \(\vert{}\Omega\rangle\): [1] (https://www.thphys.uni-heidelberg.de/~hebecker/QFTII/notes-now.pdf)
\(\langle \Omega |{}\phi _{a}\rangle \ne 0\quad \text{and}\quad \langle \phi _{b}|{}\Omega \rangle \ne 0\)

2. Why a Higgs Potential Breaks the Naive Equivalence

In standard QFT derivations (such as Peskin & Schroeder), one imposes Dirichlet boundary conditions where the field vanishes at temporal infinity: [1] (https://ocw.mit.edu/courses/8-323-relativistic-quantum-field-theory-i-spring-2023/mit8_323_s23_pset06.pdf)
\(\lim _{t\rightarrow \pm \infty }\phi (t,\mathbf{x})=0\implies |{}\phi _{a}\rangle =|{}\phi =0\rangle \)
Now consider a scalar field with a Higgs (Mexican-hat) potential:
\(V(\phi )=-\frac{1}{2}\mu ^{2}\phi ^{2}+\frac{\lambda }{4}\phi ^{4}\quad (\mu ^{2}>0)\)
In the Hamiltonian (canonical) formalism, the true vacuum state \(\vert{}\Omega\rangle\) is localized around the classical minimum \(\phi = v = \pm \sqrt{\mu^2/\lambda} \neq 0\). In the thermodynamic (infinite spatial volume \(V_3 \to \infty\)) limit, the vacuum wavefunctional \(\Psi_\Omega[\phi] = \langle \phi \vert{} \Omega \rangle\) is sharply peaked around \(\phi(\mathbf{x}) = v\):
\(\Psi _{\Omega }[\phi ]\propto \exp \left(-\frac{1}{2}\int d^{3}x\,(\phi (\mathbf{x})-v)\sqrt{-\nabla ^{2}+m_{H}^{2}}(\phi (\mathbf{x})-v)\right)\)
If you evaluate the overlap between the vacuum \(\vert{}\Omega\rangle\) and the standard boundary state \(\vert{}\phi = 0\rangle\):
\(\langle \Omega |{}\phi =0\rangle \propto \exp \left(-\frac{1}{2}v^{2}m_{H}V_{3}\right)\xrightarrow{V_{3}\rightarrow \infty }0\)
Because the overlap \(\langle \Omega \vert{} \phi = 0 \rangle\) vanishes exponentially with the spatial volume \(V_{3}\), the projection onto the true vacuum \(\vert{}\Omega\rangle\) fails completely:
1. Symmetric integration over both vacua: If you integrate over all paths with \(\phi(\pm\infty) = 0\) without breaking the symmetry, the Euclidean path integral sums equally over fluctuations around \(+v\) and \(-v\) (connected by instanton/kink configurations). Consequently, the path integral gives \(\langle \phi \rangle_{\text{PI}} = 0\) instead of the canonical VEV \(\langle \Omega \vert{} \hat{\phi} \vert{} \Omega \rangle = v \neq 0\). [1] (https://davidtong.org/pdfs/teaching/standard-model/standardmodel2.pdf), [2] (https://arxiv.org/abs/0810.1412), [3] (https://arxiv.org/pdf/0810.1412)
2. Breakdown of Perturbation Theory: Expanding the path integral around \(\phi = 0\) places you on top of the unstable local maximum (\(V''(0) = -\mu^2 < 0\)), producing tachyonic propagators \(\frac{i}{p^{2}+\mu ^{2}+i\epsilon }\) whose poles lie on the imaginary axis, invalidating the Wick rotation and the \(i\epsilon\) damping prescription. [1] (https://arxiv.org/pdf/1512.08123)

3. How Equivalence is Restored

To make the path integral equivalent to the Hamiltonian formalism in the presence of a Higgs potential, one must do one of two things:
• Shift the field variable before quantizing: Define \(\phi(x) = v + h(x)\) so that the fluctuating quantum field \(h(x)\) has a null vacuum expectation value (\(\langle \Omega \vert{} \hat{h} \vert{} \Omega \rangle = 0\)) and boundary condition \(\lim_{t \to \pm\infty} h(t, \mathbf{x}) = 0\). [1] (https://arxiv.org/html/1712.04721v4), [2] (https://arxiv.org/pdf/1512.08123)
• Add an external source \(J\): Keep the boundary condition \(\phi(\pm\infty) = v\) (or add a linear symmetry-breaking term \(J\phi\) to the Lagrangian), take the infinite volume limit \(V_3 \to \infty\) first, and only take \(J \to 0^+\) afterward so the boundary state maintains overlap with the selected vacuum \(\vert{}\Omega_v\rangle\).
If you'd like to dig deeper into this specific derivation, let me know if you want to see:
• Weinberg's explicit proof (in QFT Vol. 1, Sec. 9.2) using Gaussian wavepackets for the boundary states
• How instanton/kink tunneling in the Euclidean path integral restores \(\langle \phi \rangle = 0\) in finite volume (quantum mechanics) vs. infinite volume (QFT)
