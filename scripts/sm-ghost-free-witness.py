#!/usr/bin/env python3
"""The SM BRST charge against its ghost-free sector: dimensions and one witness.

This script is the numerical companion of `BookProof/Sm/ChapterSmQuartet.lean` §20–§21.  It uses
the chapter's own conventions:

  * modes      -- the first `m` are matter, the last twelve are the ghosts of
                  `su(3) + su(2) + u(1)`, in the order gluons (8), weak (3), hypercharge (1);
  * jwSign     -- `(-1)` to the number of occupied modes below the one acted on;
  * charge     -- `Omega = sum_a c^a G_a - sum_{a<b,e} f_abe c^a c^b b_e`, with
                  `G_a = -i dGamma(T_a)` and `f` the Standard-Model structure constants,
                  so that `Omega` is the chapter's `smBrstCharge m T f3` up to the `-1/2`
                  absorbed into the antisymmetrised sum;
  * parity     -- `U = (-1)^{N_ghost}`, i.e. the sign of the ghost number.

It reports

  1. the sector dimensions of the *full* twelve-ghost sector (`m = 0`, `m = 1`): total, kernel,
     range, and the ghost-parity split of each;
  2. whether `ker Omega` contains the whole even sector, which is the numerical form of
     `smPhysicalPositivity_iff_closed_even`;
  3. one ghost-free even state at the six-mode coloured weak doublet (`m = 6`, the representation
     of `ChapterSmGaugeRepresentation`), with `||Omega psi||`, as a decision of "does the charge
     kill its even sector".

Only the ghost-number/matter-number block structure makes this affordable: `Omega` raises the
ghost number by one and preserves the matter number, so every block is at most
`C(12, 6) * C(m, k)` wide, and the ranks are computed block by block by sparse elimination over
floats (no third-party packages; pure Python).
"""

import sys
import time
from itertools import combinations

import cmath

# --------------------------------------------------------------------------------------
# 1. Structure constants of su(3) + su(2) + u(1), from the Gell-Mann and Pauli matrices
# --------------------------------------------------------------------------------------


def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)] for i in range(n)]


def gell_mann():
    """The eight Gell-Mann matrices (Hermitian, trace-orthonormal in the 1/2 normalisation)."""
    lam = []
    lam.append([[0, 1, 0], [1, 0, 0], [0, 0, 0]])
    lam.append([[0, -1j, 0], [1j, 0, 0], [0, 0, 0]])
    lam.append([[1, 0, 0], [0, -1, 0], [0, 0, 0]])
    lam.append([[0, 0, 1], [0, 0, 0], [1, 0, 0]])
    lam.append([[0, 0, -1j], [0, 0, 0], [1j, 0, 0]])
    lam.append([[0, 0, 0], [0, 0, 1], [0, 1, 0]])
    lam.append([[0, 0, 0], [0, 0, -1j], [0, 1j, 0]])
    r3 = 3 ** 0.5
    lam.append([[1 / r3, 0, 0], [0, 1 / r3, 0], [0, 0, -2 / r3]])
    return [[[x / 2 for x in row] for row in A] for A in lam]


def pauli_half():
    s = [[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]]
    return [[[x / 2 for x in row] for row in A] for A in s]


def structure_from_generators(T):
    """`f_abc = -2i tr([T_a, T_b] T_c)` for traceless Hermitian generators."""
    n = len(T[0])
    out = {}
    for a in range(len(T)):
        for b in range(len(T)):
            AB = matmul(T[a], T[b])
            BA = matmul(T[b], T[a])
            C = [[AB[i][j] - BA[i][j] for j in range(n)] for i in range(n)]
            for c in range(len(T)):
                tr = sum(C[i][j] * T[c][j][i] for i in range(n) for j in range(n))
                v = -2j * tr
                if abs(v.imag) > 1e-12:
                    raise SystemExit("structure constant not real")
                if abs(v.real) > 1e-12:
                    out[(a, b, c)] = v.real
    return out


def kron(A, B):
    n, m = len(A), len(B)
    return [[A[i // m][j // m] * B[i % m][j % m] for j in range(n * m)] for i in range(n * m)]


def identity(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def sm_generators(y):
    """The twelve generators on `C^3 (x) C^2`: eight gluons, three weak, one hypercharge."""
    T = []
    for a in range(8):
        T.append(kron(gell_mann()[a], identity(2)))
    for k in range(3):
        T.append(kron(identity(3), pauli_half()[k]))
    T.append([[y if i == j else 0 for j in range(6)] for i in range(6)])
    return T


def sm_structure(T):
    """Structure constants of the direct sum, assembled blockwise from the twelve labels.

    The gluon and weak blocks close on themselves; the hypercharge is central, so its
    structure constants vanish.  This matches `smStruct f3` of `ChapterSmBrstGhost`.
    """
    f = {}
    # The constants are those of the algebra, not of the six-dimensional representation:
    # reading them off the 6 x 6 generators would multiply the gluon block by tr(1_2) = 2 and
    # the weak block by tr(1_3) = 3, which destroys nilpotency of the charge.
    glu = structure_from_generators(gell_mann())
    for (a, b, c), v in glu.items():
        f[(a, b, c)] = v
    weak = structure_from_generators(pauli_half())
    for (a, b, c), v in weak.items():
        f[(8 + a, 8 + b, 8 + c)] = v
    return f


# --------------------------------------------------------------------------------------
# 2. The fermionic Fock space, in the chapter's Jordan-Wigner conventions
# --------------------------------------------------------------------------------------

MODE_OF_GHOST = 8  # placeholder, replaced per model


def occ_bits(mask, n):
    return [i for i in range(n) if mask >> i & 1]


def jw_sign(i, mask):
    return -1.0 if (bin(mask & ((1 << i) - 1)).count("1") % 2) else 1.0


def creat(i, mask):
    if mask >> i & 1:
        return 0, 0.0
    return mask | (1 << i), jw_sign(i, mask)


def annih(i, mask):
    if not (mask >> i & 1):
        return 0, 0.0
    rest = mask & ~(1 << i)
    return rest, jw_sign(i, rest)


def apply_ops(ops, mask, sign=1.0):
    """Apply a word of ('c', i) / ('a', i) given in application order (innermost first)."""
    for kind, i in ops:
        if kind == "c":
            mask, s = creat(i, mask)
        else:
            mask, s = annih(i, mask)
        if s == 0.0:
            return None
        sign *= s
    return (mask, sign)


# --------------------------------------------------------------------------------------
# 3. The charge, as a sparse operator, and its sector dimensions
# --------------------------------------------------------------------------------------


def charge_terms(m, T, f):
    """`[(ops, coefficient)]` for `Omega`, with `ops` in right-to-left application order.

    Gauss part: the operator `G_a = -i dGamma(T_a)` is expanded into its one-particle matrix,
    so a term is `c^a_{m+a}` preceded by `creat i . annih j` on the matter modes.
    Cubic part: `- sum_{a<b,e} f_abe c^a c^b b_e`.
    """
    n = m + 12
    terms = []
    for a in range(12 if m else 0):
        for i in range(m):
            for j in range(m):
                v = T[a][i][j]
                if abs(v) == 0:
                    continue
                # G_a = -i sum_ij T_ij creat i annih j ; then the ghost creation
                terms.append(([("a", j), ("c", i), ("c", m + a)], -1j * v))
    for a in range(12):
        for b in range(12):
            if a >= b:
                continue
            for e in range(12):
                v = f.get((a, b, e), 0.0)
                if v == 0.0:
                    continue
                terms.append(([("a", m + e), ("c", m + b), ("c", m + a)], -v))
    return terms


def act(terms, mask, sign=1.0):
    out = {}
    for ops, coef in terms:
        r = apply_ops(ops, mask, sign)
        if r is None:
            continue
        target, s = r
        out[target] = out.get(target, 0.0) + coef * s
    return {k: v for k, v in out.items() if abs(v) > 1e-12}


def ghost_number(mask, m):
    return bin(mask >> m).count("1")


def matter_number(mask, m):
    return bin(mask & ((1 << m) - 1)).count("1")


def rank_sparse(rows, tol=1e-10):
    """Rank of a sparse matrix given as a list of `{column: value}` rows."""
    piv = {}
    fill = 0
    for r in rows:
        cur = {c: v for c, v in r.items() if abs(v) > tol}
        while cur:
            hit = None
            for c in cur:
                if c in piv:
                    hit = c
                    break
            if hit is None:
                c0 = min(cur)
                f0 = cur[c0]
                piv[c0] = {c: v / f0 for c, v in cur.items()}
                fill += len(piv[c0])
                break
            f0 = cur[hit]
            for c, v in piv[hit].items():
                nv = cur.get(c, 0.0) - f0 * v
                if abs(nv) > tol:
                    cur[c] = nv
                else:
                    cur.pop(c, None)
    return len(piv)


def degree_table(m, T, f, cubic_only=False):
    """Per ghost number: total dimension, rank, kernel dimension, split by parity."""
    n = m + 12
    terms = charge_terms(m, T, f)
    if cubic_only:
        terms = [(ops, c) for ops, c in terms if all(i >= m for _, i in ops)]
    by_key = {}
    for s in range(1 << n):
        by_key.setdefault((matter_number(s, m), ghost_number(s, m)), []).append(s)
    rows = []
    for g in range(13):
        src = [s for k in range(m + 1) for s in by_key.get((k, g), [])]
        if not src:
            continue
        dst = {s: i for i, s in
               enumerate([t for k in range(m + 1) for t in by_key.get((k, g + 1), [])])}
        rows.append((g, src, dst, terms))
    out = []
    for g, src, dst, tms in rows:
        if not dst:
            out.append((g, len(src), 0, len(src), len(src) if g % 2 == 0 else 0,
                len(src) if g % 2 == 1 else 0))
            continue
        mat = []
        for s in src:
            r = act(tms, s)
            mat.append({dst[t]: v for t, v in r.items() if t in dst})
        rk = rank_sparse([r for r in mat if r])
        ker = len(src) - rk
        out.append((g, len(src), rk, ker, ker if g % 2 == 0 else 0,
            ker if g % 2 == 1 else 0))
    return out


def sector_report(m, T, f):
    n = m + 12
    terms = charge_terms(m, T, f)
    states = list(range(1 << n))
    by_key = {}
    for s in states:
        by_key.setdefault((matter_number(s, m), ghost_number(s, m)), []).append(s)

    total_ker = 0
    total_range = 0
    even_ker = 0
    odd_ker = 0
    for (k, g), src in sorted(by_key.items()):
        dstindex = {s: i for i, s in enumerate(by_key.get((k, g + 1), []))}
        if not dstindex:
            total_ker += len(src)
            if g % 2 == 0:
                even_ker += len(src)
            else:
                odd_ker += len(src)
            continue
        rows = []
        for s in src:
            r = act(terms, s)
            rows.append({dstindex[t]: v for t, v in r.items() if t in dstindex})
        rk = rank_sparse([r for r in rows if r])
        total_range += rk
        dim_ker = len(src) - rk
        total_ker += dim_ker
        if g % 2 == 0:
            even_ker += dim_ker
        else:
            odd_ker += dim_ker
    return {
        "dim": len(states),
        "ker": total_ker,
        "range": total_range,
        "even_ker": even_ker,
        "odd_ker": odd_ker,
        "even_total": sum(1 for s in states if ghost_number(s, m) % 2 == 0),
        "odd_total": sum(1 for s in states if ghost_number(s, m) % 2 == 1),
    }


# --------------------------------------------------------------------------------------
# 4. Nilpotency check and the ghost-free witness
# --------------------------------------------------------------------------------------


def check_nilpotent(m, T, f, n_sample=64):
    """`Omega^2 = 0` on a sample of basis states (cheap: the second application is sparse)."""
    terms = charge_terms(m, T, f)
    worst = 0.0
    states = list(range(1 << (m + 12)))
    step = max(1, len(states) // n_sample)
    for s in states[::step]:
        first = act(terms, s)
        acc = {}
        for mid, coef in first.items():
            for t, v in act(terms, mid).items():
                acc[t] = acc.get(t, 0.0) + coef * v
        for v in acc.values():
            worst = max(worst, abs(v))
    return worst


def ghost_free_witness(m, T, f, occupied):
    """`Omega psi` for `psi = occ(occupied)` on the matter modes, with no ghost.

    The identity of §20 says `Omega psi = sum_a c^a G_a psi` and `b_a Omega psi = G_a psi`;
    both are evaluated directly here, together with `||Omega psi||`.
    """
    terms = charge_terms(m, T, f)
    mask = 0
    for i in occupied:
        mask |= 1 << i
    out = act(terms, mask)
    norm_sq = sum(abs(v) ** 2 for v in out.values())

    # The two sides of §20's identity, evaluated independently:
    #   (a) the Gauss sum `sum_a c^a G_a psi`,
    #   (b) the cubic term alone, which §20 says kills a ghost-free state.
    gauss = {}
    per = {}
    for a in range(12):
        piece = {}
        for i in range(m):
            for j in range(m):
                v = T[a][i][j]
                if abs(v) == 0:
                    continue
                r = apply_ops([("a", j), ("c", i)], mask)
                if r is None:
                    continue
                t, s = r
                piece[t] = piece.get(t, 0.0) - 1j * v * s
        per[a] = sum(abs(v) ** 2 for v in piece.values())
        for t, v in piece.items():
            r = apply_ops([("c", m + a)], t)
            if r is None:
                continue
            t2, s2 = r
            gauss[t2] = gauss.get(t2, 0.0) + v * s2
    cubic = {}
    for ops, coef in terms:
        if not all(i >= m for _, i in ops):   # the cubic term touches ghosts only
            continue
        r = apply_ops(ops, mask)
        if r is None:
            continue
        t, s = r
        cubic[t] = cubic.get(t, 0.0) + coef * s
    keys = set(out) | set(gauss)
    diff = max((abs(out.get(k, 0.0) - gauss.get(k, 0.0)) for k in keys), default=0.0)
    cubic_max = max((abs(v) for v in cubic.values()), default=0.0)
    return {
        "mask": mask,
        "norm_sq": norm_sq,
        "norm": norm_sq ** 0.5,
        "per_generator": per,
        "gauss_norm_sq": sum(abs(v) ** 2 for v in gauss.values()),
        "identity_residual": diff,
        "cubic_residual": cubic_max,
        "parity": (-1.0) ** 0,
        "ghost_number": 0,
    }


# --------------------------------------------------------------------------------------
# 5. Run
# --------------------------------------------------------------------------------------


def main():
    y = 1.0
    Tfull = sm_generators(y)
    f = sm_structure(Tfull)

    print("=" * 78)
    print("SM BRST charge, full su(3) x su(2) x u(1) ghost sector")
    print("=" * 78)
    print("structure constants: %d nonzero triples among 12^3" % len(f))

    for m in (0, 1):
        if m == 0:
            T = []
        else:
            # one matter mode carrying hypercharge y and nothing else: this closes with
            # smStruct because no structure constant has a u(1) index
            T = [[[0 + 0j]] for _ in range(11)] + [[[y + 0j]]]
        t0 = time.time()
        nil = check_nilpotent(m, T, f)
        rep = sector_report(m, T, f)
        dt = time.time() - t0
        print()
        print("m = %d matter mode(s), %d states  (%.2fs)" % (m, rep["dim"], dt))
        print("  ||Omega^2|| on a sample of 64 states : %.3e" % nil)
        print("  dim ker Omega                        : %d" % rep["ker"])
        print("  dim range Omega (rank)               : %d" % rep["range"])
        print("  check ker + range = dim              : %d"
              % (rep["ker"] + rep["range"]))
        print("  even (ghost-parity +1) states        : %d" % rep["even_total"])
        print("  dim (even interest ker Omega)        : %d" % rep["even_ker"])
        print("  dim (odd interest ker Omega)         : %d" % rep["odd_ker"])
        print("  even sector inside ker Omega         : %s"
              % ("YES" if rep["even_ker"] == rep["even_total"] else "NO"))
        print("  => ghost-parity positivity           : %s"
              % ("holds" if rep["even_ker"] == rep["even_total"] else "fails"))

        for cubic_only, label in ((False, "Omega"), (True, "the cubic term alone")):
            print()
            print("  per ghost number, %s (m = %d):" % (label, m))
            print("    g   dim      rank    ker   ker(even)  ker(odd)")
            for g, dim, rk, ker, kev, kod in degree_table(m, T, f, cubic_only):
                print("    %2d  %5d   %5d   %5d     %5d      %5d"
                      % (g, dim, rk, ker, kev, kod))


    print()
    print("=" * 78)
    print("Ghost-free witness at the six-mode coloured weak doublet (m = 6)")
    print("=" * 78)
    T = Tfull
    w = ghost_free_witness(6, T, f, [0])
    print("state: matter mode 0 occupied, ghost vacuum (ghost number 0 => even)")
    print("  ||Omega psi||                        : %.6f" % w["norm"])
    print("  ||sum_a c^a G_a psi||^2              : %.6f" % w["norm_sq"])
    print("  sum_a ||G_a psi||^2                  : %.6f" % sum(w["per_generator"].values()))
    print("  nonzero Gauss generators             : %s"
          % [a for a, v in w["per_generator"].items() if v > 1e-12])
    print("  ||cubic term alone||                 : %.3e" % w["cubic_residual"])
    print("  ||Omega psi - sum_a c^a G_a psi||    : %.3e" % w["identity_residual"])
    print("  => the charge kills this even state  : %s"
          % ("YES" if w["norm"] < 1e-9 else "NO"))
    print()
    print("Ghost-free witness at m = 1 (hypercharge y = %.1f)" % y)
    T1 = [[[0 + 0j]] for _ in range(11)] + [[[y + 0j]]]
    w1 = ghost_free_witness(1, T1, f, [0])
    print("  ||Omega psi||                        : %.6f" % w1["norm"])
    print("  nonzero Gauss generators             : %s"
          % [a for a, v in w1["per_generator"].items() if v > 1e-12])


if __name__ == "__main__":
    sys.exit(main())
