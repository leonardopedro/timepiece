#!/usr/bin/env python3
"""Measure the VolDom constants of the NS incompressibility penalty.

`VolDom A B` (BookProof/Ns/ChapterNsGradDomCoercive.lean) is the one open input of the
NS gradient-domination chain:

    sum_j (d/dxi_j V_kappa)^2  <=  A * V_kappa^2 + B   for every real configuration,

with V_kappa = (kappa/2) * sum_q |(det F - 1)^(q)|^2, F = I + grad xi, and the q running over
the finitely many momenta that occur in the determinant (volPot / detCoef in
BookProof/Ns/ChapterNsLagrangianDetConvolution.lean).

This script evaluates that inequality numerically on a concrete truncation, with *exact*
gradients (forward-mode dual numbers over the real coordinate ring), and reports the maximum
of

    (sum_j (d_j V)^2) / (V^2 + 1)

over the sampled configurations.  Any `A = B = M` with `M` at least the true supremum makes
VolDom hold; the numbers below are therefore a *sampled lower bound* on the constants a proof
would need, not a proof.  What they do establish is that the required constants are finite and
small on this truncation -- the flat sextic of the same degree has no finite constant at all
(`not_gradDom_flatSextic`), and the shears (`F` unimodular with large displacement) are exactly
the configurations where a naive degree argument would blow up, so they are sampled explicitly.

Run it and the answer is negative: along the shear family `F = I + t N + eps B` with
`N = e_x (x) e_y` (so `det(I + tN) = 1` for all `t`) and `B = e_y (x) e_x`, the ratio saturates at
`4/eps^2` as `t` grows and is therefore unbounded as `eps -> 0`.  So no finite `A`, `B` make
`VolDom` hold for this penalty; the script's final line reports the sampled supremum only because
the family, not random sampling, is what diverges.
"""

import itertools
import random

# ---------------------------------------------------------------- dual numbers

class D:
    """A dual number: value plus gradient with respect to the coordinates."""
    __slots__ = ("v", "g")

    def __init__(self, v, g):
        self.v = v
        self.g = g

    def __add__(self, o):
        o = const(o, len(self.g))
        return D(self.v + o.v, [a + b for a, b in zip(self.g, o.g)])

    __radd__ = __add__

    def __neg__(self):
        return D(-self.v, [-a for a in self.g])

    def __sub__(self, o):
        return self + (-const(o, len(self.g)))

    def __rsub__(self, o):
        return const(o, len(self.g)) + (-self)

    def __mul__(self, o):
        o = const(o, len(self.g))
        return D(self.v * o.v, [a * o.v + self.v * b for a, b in zip(self.g, o.g)])

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = const(o, len(self.g))
        return D(self.v / o.v, [(a * o.v - self.v * b) / (o.v * o.v)
                                for a, b in zip(self.g, o.g)])


def _toC(o, n):
    if isinstance(o, C):
        return o
    return C(const(o, n), const(0.0, n))


def const(c, n):
    if isinstance(c, D):
        return c
    return D(float(c), [0.0] * n)


class C:
    """A complex number with dual-value real and imaginary parts."""
    __slots__ = ("re", "im")

    def __init__(self, re, im):
        self.re, self.im = re, im

    def __add__(self, o):
        o = _toC(o, len(self.re.g))
        return C(self.re + o.re, self.im + o.im)

    def __radd__(self, o):
        return self.__add__(o)

    def __sub__(self, o):
        o = _toC(o, len(self.re.g))
        return C(self.re - o.re, self.im - o.im)

    def __rsub__(self, o):
        return _toC(o, len(self.re.g)).__sub__(self)

    def __neg__(self):
        return C(-self.re, -self.im)

    def __mul__(self, o):
        o = _toC(o, len(self.re.g))
        return C(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def conj(self):
        return C(self.re, -self.im)


# ---------------------------------------------------------------- the model
# K = Fin 2 with kv: k0 -> (1,0,0), k1 -> (0,1,0).  A signed mode is (k, sign).
# Coordinates: (k, axis, part) with part 0 = real, 1 = imaginary, exactly as DIdx.

K = [(1.0, 0.0, 0.0), (0.0, 1.0, 0.0)]
NCOORD = len(K) * 3 * 2
KAPPA = 1.0
SMODES = [(k, sign) for k in range(len(K)) for sign in (True, False)]


def wv(mode):
    k, sign = mode
    s = 1.0 if sign else -1.0
    return tuple(s * c for c in K[k])


def scoef(mode, axis, x):
    """xi-hat_{k,axis} = x_re +- i x_im, as a dual complex number."""
    k, sign = mode
    re = x[(k, axis, 0)]
    im = x[(k, axis, 1)]
    if sign:
        return C(re, im)
    return C(re, -im)


def grad_coef(mode, r, c, x):
    """i * w_c * xi-hat_{mode,r}."""
    w = wv(mode)[c]
    f = scoef(mode, r, x)
    return C(w * f.re, w * f.im)


def row_coef(opt, r, c, x):
    if opt is None:
        return C(const(1.0 if r == c else 0.0, NCOORD), const(0.0, NCOORD))
    return grad_coef(opt, r, c, x)


def owv(opt):
    return (0.0, 0.0, 0.0) if opt is None else wv(opt)


def det3(rows):
    a, b, c = rows
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def det_coef(q, x):
    """Fourier coefficient of det(I + grad xi) at momentum q: the triple convolution."""
    total = C(const(0.0, NCOORD), const(0.0, NCOORD))
    for tau in itertools.product([None] + SMODES, repeat=3):
        w = [sum(owv(t)[i] for t in tau) for i in range(3)]
        if max(abs(w[i] - q[i]) for i in range(3)) > 1e-9:
            continue
        rows = [[row_coef(tau[r], r, c, x) for c in range(3)] for r in range(3)]
        total = total + det3(rows)
    return total


def wave_set():
    out = []
    for tau in itertools.product([None] + SMODES, repeat=3):
        w = tuple(sum(owv(t)[i] for t in tau) for i in range(3))
        if not any(max(abs(w[i] - v[i]) for i in range(3)) < 1e-9 for v in out):
            out.append(w)
    return out


WAVES = wave_set()


def lift(x):
    """Turn a real configuration into dual numbers carrying the coordinate gradient."""
    keys = sorted(x)
    out = {}
    for i, key in enumerate(keys):
        g = [0.0] * NCOORD
        g[i] = 1.0
        out[key] = D(x[key], g)
    return out


def vol_pot(x, mu=0.0):
    """V_kappa = (kappa/2) sum_q |(det F - 1)^(q)|^2, optionally plus the deformation norm.

    With `mu > 0` the potential is regularized by `(mu/2) * sum_{k,j} (1 + |k|^2) |xi-hat_{k,j}|^2`,
    a quadratic that does not vanish on the unimodular set.  The factor `(1 + |k|^2)` is the
    Sobolev-type weight `int (|xi|^2 + |grad xi|^2)` written in Fourier space, so the extra term is
    the deformation norm rather than an arbitrary quadratic.
    """
    y = lift(x)
    acc = const(0.0, NCOORD)
    for q in WAVES:
        p = det_coef(q, y)
        if q == (0.0, 0.0, 0.0):
            p = p - C(const(1.0, NCOORD), const(0.0, NCOORD))
        acc = acc + (p.re * p.re + p.im * p.im)
    V = (KAPPA / 2.0) * acc
    if mu > 0.0:
        for (k, axis, part), xk in y.items():
            weight = 1.0 + sum(c * c for c in K[k])
            V = V + (mu / 2.0) * weight * (xk * xk)
    return V


def make_point(seed):
    rng = random.Random(seed)
    scale = 10.0 ** rng.uniform(-1.5, 1.0)
    return {(k, a, p): scale * rng.gauss(0.0, 1.0)
            for k in range(len(K)) for a in range(3) for p in range(2)}


def shear_point(t, rng):
    """A genuinely unimodular configuration plus noise.

    A shear `F = I + t e_x (x) e_y` has `N^2 = 0`, hence `det F = 1` identically and `V = 0`
    while the displacement grows with `t`.  In Fourier space the shear is the single coefficient
    `xi-hat_{+k1, x} = -i t`, because `i w_y xi-hat = i * 1 * (-i t) = t`.  These are exactly the
    configurations where a degree-only argument would have to blow up, so they are sampled with
    noise on top.
    """
    x = {(k, a, p): 0.0 for k in range(len(K)) for a in range(3) for p in range(2)}
    x[(1, 0, 1)] = -t
    for k in range(len(K)):
        for a in range(3):
            for p in range(2):
                x[(k, a, p)] += rng.gauss(0.0, 0.02 * abs(t) + 0.02)
    return x


def ratio(x, mu=0.0):
    V = vol_pot(x, mu)
    g2 = sum(g * g for g in V.g)
    return g2 / (V.v * V.v + 1.0), V.v, g2


def main():
    print(f"|K| = {len(K)}, coordinates = {NCOORD}, momenta = {len(WAVES)}, kappa = {KAPPA}")
    best = (0.0, None)
    for seed in range(400):
        x = make_point(seed)
        r = ratio(x)
        if r[0] > best[0]:
            best = (r[0], seed)
    print(f"random samples:   max ratio = {best[0]:.6g}  (seed {best[1]})")
    bests = (0.0, None)
    for i, t in enumerate([0.5, 1.0, 2.0, 5.0, 10.0, 50.0, 200.0]):
        rng = random.Random(i)
        for j in range(40):
            x = shear_point(t, rng)
            r = ratio(x)
            if r[0] > bests[0]:
                bests = (r[0], (t, j, r[1], r[2]))
    print(f"shear samples:    max ratio = {bests[0]:.6g}  (t, j, V, |grad V|^2 = {bests[1]})")
    bestl = (0.0, None)
    for seed in range(400):
        rng = random.Random(10000 + seed)
        scale = 10.0 ** rng.uniform(1.0, 2.5)
        x = {(k, a, p): scale * rng.gauss(0.0, 1.0)
             for k in range(len(K)) for a in range(3) for p in range(2)}
        r = ratio(x)
        if r[0] > bestl[0]:
            bestl = (r[0], (seed, r[1], r[2]))
    print(f"large |xi|:       max ratio = {bestl[0]:.6g}  (seed, V, |grad V|^2 = {bestl[1]})")
    print()
    print("the refuting sweep: F = I + t N + eps B, ratio vs 4/eps^2")
    print(f"{'t':>8} {'eps':>8} {'V':>12} {'|grad V|^2':>14} {'ratio':>14} {'4/eps^2':>12}")
    for eps in (1e-2, 1e-3, 1e-4):
        for t in (1e2, 1e4, 1e5):
            x = {(k, a, p): 0.0 for k in range(len(K)) for a in range(3) for p in range(2)}
            x[(1, 0, 1)] = -t     # the shear, xi-hat_{+k1,x} = -i t
            x[(0, 1, 0)] = eps    # transversal tilt
            V = vol_pot(x)
            g2 = sum(g * g for g in V.g)
            print(f"{t:>8.0e} {eps:>8} {V.v:>12.6g} {g2:>14.6g} "
                  f"{g2 / (V.v * V.v + 1.0):>14.6g} {4 / eps ** 2:>12.4g}")
    M = max(best[0], bests[0], bestl[0])
    print()
    print(f"sampled supremum over bounded boxes: M = {M:.6g}")
    print()
    print("does a deformation-norm regularization repair it?")
    print("  V_mu = V_kappa + (mu/2) * sum_{k,j} (1 + |k|^2) |xi-hat_{k,j}|^2")
    print(f"{'mu':>8} {'shear-ratio':>14} {'random':>12} {'shear+noise':>12} {'large |xi|':>12}")
    for mu in (0.0, 1e-3, 1e-2, 0.1, 1.0, 10.0):
        b1 = 0.0
        for eps in (1e-2, 1e-3, 1e-4):
            for t in (1e2, 1e4, 1e5):
                x = {(k, a, p): 0.0 for k in range(len(K)) for a in range(3) for p in range(2)}
                x[(1, 0, 1)] = -t
                x[(0, 1, 0)] = eps
                b1 = max(b1, ratio(x, mu)[0])
        b2 = 0.0
        for seed in range(200):
            b2 = max(b2, ratio(make_point(seed), mu)[0])
        b3 = 0.0
        for i, t in enumerate([0.5, 1.0, 2.0, 5.0, 10.0, 50.0, 200.0]):
            rng = random.Random(i)
            for j in range(20):
                b3 = max(b3, ratio(shear_point(t, rng), mu)[0])
        b4 = 0.0
        for seed in range(200):
            rng = random.Random(10000 + seed)
            scale = 10.0 ** rng.uniform(1.0, 2.5)
            x = {(k, a, p): scale * rng.gauss(0.0, 1.0)
                 for k in range(len(K)) for a in range(3) for p in range(2)}
            b4 = max(b4, ratio(x, mu)[0])
        print(f"{mu:>8} {b1:>14.6g} {b2:>12.6g} {b3:>12.6g} {b4:>12.6g}")
    print()
    print("the diagnostic: shrink the tilt at fixed shear amplitude t = 1e4")
    print("   mu = 0      -> ratio ~ 4/eps^2 grows without bound")
    print("   mu > 0      -> ratio stays flat (a finite constant exists)")
    print(f"{'eps':>10} {'mu=0':>14} {'mu=0.01':>14} {'mu=0.1':>14} {'mu=1':>14}")
    for eps in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
        row = []
        for mu in (0.0, 0.01, 0.1, 1.0):
            x = {(k, a, p): 0.0 for k in range(len(K)) for a in range(3) for p in range(2)}
            x[(1, 0, 1)] = -1e4
            x[(0, 1, 0)] = eps
            row.append(ratio(x, mu)[0])
        print(f"{eps:>10.0e} {row[0]:>14.6g} {row[1]:>14.6g} {row[2]:>14.6g} {row[3]:>14.6g}")
    print()
    print("   NOTE on the mu = 0 column: from eps <= 1e-4 on, V ~ (k/2) eps^2 t^2 is so small that the")
    print("   dual-number gradient loses all its digits to cancellation, and the printed numbers fall")
    print("   back down -- they are artifacts, not data.  The exact law for mu = 0 is the identity")
    print("   ratio = 4/t^2 + 4/eps^2, proved as `shear_grad_sq` in")
    print("   BookProof/Ns/ChapterNsVolDomShear.lean; e.g. t = 1e4, eps = 1e-2 gives 40000.00000004.")
    print("That finite number is NOT the answer: the shear family diverges.  Along")
    print("F = I + t N + eps B (N = e_x (x) e_y, B = e_y (x) e_x) the ratio saturates at 4/eps^2 and")
    print("is unbounded as eps -> 0, so no finite A, B make VolDom hold for this penalty.")
    print("Run the sweep")
    print("    t in {1e2,1e4,1e5} x eps in {1e-2,1e-3,1e-4}")
    print("to see the saturation; this is a measurement on a truncation plus the analytic expansion,")
    print("not a proof of the negation.")


if __name__ == "__main__":
    main()
