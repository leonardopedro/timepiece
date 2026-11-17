#!/usr/bin/env python3
"""Numerical smoke test for the SM no-ghost equivalence (plan 92/93).

`BookProof/Sm/ChapterSmQuartet.lean` proves, for a charge `Q` that is nilpotent and odd for an
involution `U`:

    PhysicalPositivity Q U  <->  closed Q subset of evenSpace U            (section 17)
    PhysicalPositivity Q U  ->   Q x = 0 for every even x                 (section 18)
    PhysicalPositivity Q D.starProjection  for D a complement of range Q  (section 19)

This script checks those statements numerically on a *truncation* of the model's algebra: the
su(2) block of the gauge algebra (three ghost modes, three fundamental matter modes, so 2^6 = 64
states), with the model's own conventions

    Omega = sum_a c_a^dag G_a - (1/2) sum_{a,b,e} f_{abe} c_a^dag c_b^dag b_e,
    G_a   = -i dGamma(T_a),   [T_a, T_b] = i eps_{abc} T_c,   f = eps,

and the fermionic operators built with the Jordan-Wigner signs used by
`BookProof/Sm/ChapterSmCarAlgebra.lean` (`annih`/`creat`, sign (-1)^{#{j in S : j < i}}).

It reports, for the truncation:

  * nilpotency and oddness of Omega (the hypotheses of the theorems);
  * dim ker Omega and dim(odd cap ker Omega) -- the second is the obstruction of section 17, and
    the equivalence predicts that positivity holds exactly when it is zero;
  * an explicit odd closed state and the value of the ghost-parity form on it (negative iff the
    parity metric is not no-ghost);
  * the largest norm ||Omega x|| over even basis states -- nonzero iff section 18's necessary
    condition fails, which refutes positivity for the parity metric;
  * for the projector metric onto D = ker Omega cap (range Omega)^perp: the Gram matrix on
    ker Omega, its factorisation as B^dag B (non-negativity), and the dimension of its radical
    (which must be dim range Omega), i.e. section 19's conclusion;
  * on random small matrices satisfying the hypotheses, both directions of section 17's
    equivalence, so the statement itself is exercised in the passing regime as well.

Pure Python (no third-party packages): small Gaussian elimination over C.

Run: python3 scripts/sm-physical-positivity-smoke.py
"""

import itertools
import random


# ---------------------------------------------------------------------------------------------
# Dense complex matrices as lists of rows
# ---------------------------------------------------------------------------------------------

def zeros(r, c):
    return [[0j] * c for _ in range(r)]


def identity(n):
    return [[1.0 if i == j else 0j for j in range(n)] for i in range(n)]


def dagger(a):
    return [[a[i][j].conjugate() for i in range(len(a))] for j in range(len(a[0]))]


def mat_mul(a, b):
    n, k, m = len(a), len(b), len(b[0])
    out = zeros(n, m)
    for i in range(n):
        row = out[i]
        ai = a[i]
        for t in range(k):
            f = ai[t]
            if f == 0:
                continue
            bt = b[t]
            for j in range(m):
                row[j] += f * bt[j]
    return out


def mat_add(a, b):
    return [[x + y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def mat_scale(c, a):
    return [[c * x for x in row] for row in a]


def mat_sub(a, b):
    return [[x - y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def stack(*ms):
    return [row for m in ms for row in m]


def max_abs(a):
    return max((abs(x) for row in a for x in row), default=0.0)


def rref(a):
    """Row-reduced echelon form with partial pivoting; returns (matrix, pivot columns)."""
    m = [row[:] for row in a]
    rows, cols = len(m), len(m[0])
    pivots = []
    r = 0
    for c in range(cols):
        best, bestv = -1, 1e-12
        for i in range(r, rows):
            v = abs(m[i][c])
            if v > bestv:
                best, bestv = i, v
        if best < 0:
            continue
        m[r], m[best] = m[best], m[r]
        p = m[r][c]
        m[r] = [x / p for x in m[r]]
        for i in range(rows):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        pivots.append(c)
        r += 1
        if r == rows:
            break
    return m, pivots


def rank(a):
    return len(rref(a)[1])


def nullspace(a):
    """Basis of the kernel of `a`, as a list of vectors (columns of the matrix)."""
    m, pivots = rref(a)
    cols = len(a[0])
    free = [c for c in range(cols) if c not in pivots]
    basis = []
    for f in free:
        v = [0j] * cols
        v[f] = 1.0
        for i, p in enumerate(pivots):
            v[p] = -m[i][f]
        basis.append(v)
    return basis


def inner(x, y):
    return sum(xi.conjugate() * yi for xi, yi in zip(x, y))


def norm(x):
    return abs(inner(x, x)) ** 0.5


def gram(basis, eta):
    """Matrix of the form x |-> <x, eta x> on `basis`: G[i][j] = <b_i, eta b_j>."""
    eb = [apply(eta, v) for v in basis]
    return [[inner(basis[i], eb[j]) for j in range(len(basis))] for i in range(len(basis))]


def apply(mat, v):
    return [sum(mat[i][j] * v[j] for j in range(len(v))) for i in range(len(mat))]


def hermitian_eigs(a, sweeps=60):
    """Eigenvalues of a Hermitian matrix by cyclic Jacobi rotations (O(n) per rotation)."""
    n = len(a)
    A = [[complex(a[i][j]) for j in range(n)] for i in range(n)]
    for _ in range(sweeps):
        off = sum(abs(A[i][j]) for i in range(n) for j in range(i + 1, n))
        if off < 1e-12:
            break
        for p in range(n - 1):
            for q in range(p + 1, n):
                apq = A[p][q]
                r = abs(apq)
                if r < 1e-15:
                    continue
                phi = apq / r
                app, aqq = A[p][p].real, A[q][q].real
                tau = (app - aqq) / (2 * r)
                t = (1.0 if tau >= 0 else -1.0) / (abs(tau) + (tau * tau + 1.0) ** 0.5)
                c = 1.0 / (t * t + 1.0) ** 0.5
                s = c * t
                # rows p, q
                for k in range(n):
                    if k == p or k == q:
                        continue
                    akp, akq = A[k][p], A[k][q]
                    A[k][p] = c * akp + s * phi * akq
                    A[k][q] = -s * phi.conjugate() * akp + c * akq
                    A[p][k], A[q][k] = A[k][p].conjugate(), A[k][q].conjugate()
                app2 = c * c * app + s * s * aqq + 2 * c * s * r
                aqq2 = s * s * app + c * c * aqq - 2 * c * s * r
                A[p][p] = complex(app2)
                A[q][q] = complex(aqq2)
                A[p][q] = 0j
                A[q][p] = 0j
    return sorted(A[i][i].real for i in range(n))


def range_contains(mat, x, tol=1e-7):
    """Is `x` in the range of `mat`?  Range = (ker mat^dag)^perp."""
    kd = nullspace(dagger(mat))
    return all(abs(inner(w, x)) < tol for w in kd)


def positivity_holds(omega, eta, ker, tol=1e-7):
    """`PhysicalPositivity omega eta`: the form is non-negative on ker omega and its radical there
    is contained in the gauge orbit `range omega`."""
    if not ker:
        return True, 0.0, 0
    G = gram(ker, eta)
    ev = hermitian_eigs(G)
    nonneg = ev[0] > -tol
    coef = nullspace(G)
    rad = [[sum(c[i] * ker[i][j] for i in range(len(ker))) for j in range(len(ker[0]))]
           for c in coef] if coef else []
    in_gauge = all(range_contains(omega, v) for v in rad)
    return nonneg and in_gauge, ev[0], len(rad)


def orthonormalize(basis):
    """Gram-Schmidt, dropping (numerically) dependent vectors."""
    out = []
    for v in basis:
        w = v[:]
        for u in out:
            proj = inner(u, w)
            w = [wi - proj * ui for wi, ui in zip(w, u)]
        nw = norm(w)
        if nw > 1e-8:
            out.append([x / nw for x in w])
    return out


# ---------------------------------------------------------------------------------------------
# Fermionic Fock space with the model's Jordan-Wigner conventions
# ---------------------------------------------------------------------------------------------

def popcount(mask):
    return bin(mask).count("1")


def jw_sign(i, mask):
    """(-1)^{#{j in mask : j < i}} -- `BookProof.SmCar.jwSign`."""
    lower = mask & ((1 << i) - 1)
    return -1.0 if popcount(lower) % 2 else 1.0


def annihilation(i, n):
    """Matrix of `annih i`: (annih i)|T> = 0 if i in T, else jwSign i T |T + {i}>."""
    d = 2 ** n
    m = zeros(d, d)
    for t in range(d):
        if t >> i & 1:
            continue
        m[t | (1 << i)][t] += jw_sign(i, t)
    return m


def creation(i, n):
    """Matrix of `creat i`: (creat i)|T> = 0 if i not in T, else jwSign i (T erase i)|T - {i}>."""
    d = 2 ** n
    m = zeros(d, d)
    for t in range(d):
        if not (t >> i & 1):
            continue
        m[t ^ (1 << i)][t] += jw_sign(i, t ^ (1 << i))
    return m


def build_operators(n_matter, n_gauge):
    """Omega and the ghost parity on the truncation."""
    n = n_matter + n_gauge
    d = 2 ** n
    ghost_modes = [n_matter + a for a in range(n_gauge)]

    cre = [creation(i, n) for i in range(n)]
    ann = [annihilation(i, n) for i in range(n)]

    # su(2) fundamental: T_a = lambda_a / 2, [T_a, T_b] = i eps_{abc} T_c.
    T = [
        [[0, 0.5, 0], [0.5, 0, 0], [0, 0, 0]],
        [[0, -0.5j, 0], [0.5j, 0, 0], [0, 0, 0]],
        [[0.5, 0, 0], [0, -0.5, 0], [0, 0, 0]],
    ]

    def eps(a, b, c):
        if len({a, b, c}) < 3:
            return 0
        perm = [a, b, c]
        sw = sum(1 for i in range(3) for j in range(i + 1, 3) if perm[i] > perm[j])
        return -1 if sw % 2 else 1

    # G_a = -i sum_{ij} (T_a)_{ij} c_i^dag c_j   (`matterGen = (-I) * fermiBilin`).
    G = []
    for a in range(3):
        g = zeros(d, d)
        for i in range(n_matter):
            for j in range(n_matter):
                if T[a][i][j] != 0:
                    g = mat_add(g, mat_scale(-1j * T[a][i][j], mat_mul(cre[i], ann[j])))
        G.append(g)

    omega = zeros(d, d)
    for a in range(3):
        omega = mat_add(omega, mat_mul(cre[ghost_modes[a]], G[a]))
    for a, b, e in itertools.product(range(3), repeat=3):
        f = eps(a, b, e)
        if f == 0:
            continue
        term = mat_mul(mat_mul(cre[ghost_modes[a]], cre[ghost_modes[b]]), ann[ghost_modes[e]])
        omega = mat_add(omega, mat_scale(-0.5 * f, term))

    ghost_mask = 0
    for g in ghost_modes:
        ghost_mask |= 1 << g
    parity = [[0j] * d for _ in range(d)]
    for t in range(d):
        parity[t][t] = (-1.0) ** popcount(t & ghost_mask)

    return omega, parity, n, d


# ---------------------------------------------------------------------------------------------
# The study
# ---------------------------------------------------------------------------------------------

def study(omega, parity, d, label):
    print(f"--- {label}: dim = {d}")
    print(f"  ||Omega||              = {max_abs(omega):.6f}")
    print(f"  ||Omega^2||            = {max_abs(mat_mul(omega, omega)):.2e}  (nilpotent)")
    print(f"  ||U Omega + Omega U||  = {max_abs(mat_add(mat_mul(parity, omega), mat_mul(omega, parity))):.2e}")
    print(f"  ||U^2 - 1||            = {max_abs(mat_sub(mat_mul(parity, parity), identity(d))):.2e}")

    ker = orthonormalize(nullspace(omega))
    dim_ker = len(ker)
    dim_range = rank(omega)

    odd_proj = mat_scale(0.5, mat_sub(identity(d), parity))   # onto the parity-odd part
    even_proj = mat_scale(0.5, mat_add(identity(d), parity))  # onto the parity-even part
    dim_odd_closed = d - rank(stack(omega, even_proj))
    dim_even_closed = d - rank(stack(omega, odd_proj))

    print(f"  dim ker Omega          = {dim_ker}")
    print(f"  dim range Omega        = {dim_range}")
    print(f"  dim(odd cap ker Omega) = {dim_odd_closed}   <- section 17's obstruction")
    print(f"  dim(even cap ker Omega)= {dim_even_closed}")

    holds, min_ev, rad = positivity_holds(omega, parity, ker)
    print(f"  ghost-parity form on ker Omega: min eigenvalue = {min_ev:.6f}, radical dim = {rad}")
    print(f"  PhysicalPositivity Omega U = {holds}; closed subset even = {dim_odd_closed == 0}"
          f"  -> equivalence {'agrees' if holds == (dim_odd_closed == 0) else 'DISAGREES'}")

    if dim_odd_closed:
        for t in range(d):
            x = [0j] * d
            x[t] = 1.0
            if abs(parity[t][t] + 1.0) > 1e-9:
                continue
            if max(abs(v) for v in apply(omega, x)) < 1e-9:
                print(f"  witness: odd basis state {t:0{int(d.bit_length())}b} is closed; "
                      f"x^dag U x = {inner(x, apply(parity, x)).real:.6f}")
                break

    worst, worst_t = 0.0, None
    for t in range(d):
        x = [0j] * d
        x[t] = 1.0
        if abs(parity[t][t] - 1.0) > 1e-9:
            continue
        nv = norm(apply(omega, x))
        if nv > worst:
            worst, worst_t = nv, t
    print(f"  max ||Omega x|| over even basis states = {worst:.6f} (state {worst_t})")
    print(f"  -> section 18's necessary condition (Omega kills even) = {worst < 1e-9}")

    # section 19: the projector metric onto ker Omega cap (range Omega)^perp
    D = orthonormalize(nullspace(stack(omega, dagger(omega))))
    dim_D = len(D)
    eta = [[sum(D[k][i].conjugate() * D[k][j] for k in range(dim_D)) for j in range(d)] for i in range(d)]
    G = gram(ker, eta)
    B = [apply(eta, v) for v in ker]
    Gb = [[inner(B[i], B[j]) for j in range(len(ker))] for i in range(len(ker))]
    holds_D, min_ev_D, rad_D = positivity_holds(omega, eta, ker)
    print(f"  projector metric: dim D = {dim_D} (dim ker Omega - dim range Omega = {dim_ker - dim_range})")
    print(f"  ||G - B^dag B|| = {max_abs(mat_sub(G, Gb)):.2e}  (the form is a squared norm)")
    print(f"  min eigenvalue on ker Omega = {min_ev_D:.2e}; radical dim = {rad_D} "
          f"vs dim range Omega = {dim_range}")
    print(f"  PhysicalPositivity Omega (projector) = {holds_D}")
    print()


def random_instances(trials=40, d=6):
    rng = random.Random(20261115)
    agree = passing = total = 0
    for _ in range(trials):
        U = [[0j] * d for _ in range(d)]
        signs = [1.0] * (d // 2) + [-1.0] * (d // 2)
        rng.shuffle(signs)
        for i in range(d):
            U[i][i] = signs[i]
        even_proj = mat_scale(0.5, mat_add(identity(d), U))
        odd_proj = mat_scale(0.5, mat_sub(identity(d), U))
        # An odd nilpotent charge.  Both shapes satisfy Q^2 = 0 because the parity projectors are
        # orthogonal: Q = P_odd A P_even (every odd state is then closed, so the closed space is not
        # even) or Q = P_even A P_odd (no odd closed state when A is injective on the odd part).
        A = [[complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(d)] for _ in range(d)]
        Q = (mat_mul(mat_mul(odd_proj, A), even_proj) if rng.random() < 0.5
             else mat_mul(mat_mul(even_proj, A), odd_proj))
        if max_abs(mat_mul(Q, Q)) > 1e-9:
            continue
        if max_abs(mat_add(mat_mul(U, Q), mat_mul(Q, U))) > 1e-9:
            continue
        total += 1
        dim_odd_closed = d - rank(stack(Q, even_proj))
        ker = orthonormalize(nullspace(Q))
        holds, _, rad = positivity_holds(Q, U, ker)
        passing += holds
        agree += holds == (dim_odd_closed == 0)
    return total, agree, passing


def main():
    n_matter, n_gauge = 3, 3
    omega, parity, n, d = build_operators(n_matter, n_gauge)
    study(omega, parity, d,
          f"truncation: {n_matter} matter + {n_gauge} ghost modes")

    total, agree, passing = random_instances()
    print(f"--- section 17 on random instances (dim 6): {agree}/{total} agree with the equivalence,"
          f" {passing}/{total} instances have positivity")


if __name__ == "__main__":
    main()
