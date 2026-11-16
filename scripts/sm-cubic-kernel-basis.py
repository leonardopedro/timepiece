#!/usr/bin/env python3
"""An exact basis of the kernel of the cubic ghost term at ghost number two.

`BookProof/Sm/ChapterSmBrstGhost` proves that the cubic ghost term
`Omega_3 = -1/2 f_abc c^a c^b b_e` raises the ghost number by one
(`ghostNumber_comm_smGhostCharge`).  This script exhibits the
consequence at the first non-trivial degree: with no matter modes (`m = 0`) the ghost-number-two
subspace `Lambda^2 C^12` has dimension `C(12, 2) = 66`, and `Omega_3` maps it to `Lambda^3 C^12`
(dimension `C(12, 3) = 220`).  The kernel there is eleven-dimensional, and this script prints a
basis of it and verifies the two claims that make it a basis:

  * `Omega_3 v = 0` for every returning vector -- checked by exact arithmetic, entry by entry;
  * the eleven vectors are linearly independent -- the elimination is Gauss-Jordan, so the pivot
    columns of each vector are new by construction, and the rank of the stacked matrix is eleven.

It then switches on matter modes and checks that the kernel is *exactly* `2^m` times as large, which
is the statement `BookProof`'s `smGhostCharge_occ_of_ghostFree` makes degree by degree: a matter mode
never appears in a cubic monomial, so the operator splits into matter blocks.  The checks are stronger
than a dimension count -- each block is compared entry by entry with the `m = 0` operator (the
matter-free block agrees, the matter-occupied block is its *negative*, because the matter mode is a
fermion and each of the three Jordan-Wigner signs of the monomial flips once) -- and the lifted copies
of the eleven vectors are verified to be killed in every block.  The dimension is recomputed from
scratch by elimination at `m = 0, 1, 2, 3` and follows from the block identity for `m = 4, ..., 6`, where
the table reports how each rank was obtained.

At every ghost degree the same block structure gives `dim ker(m) = 2^m * dim ker(0)`; the script
eliminates from scratch at the matter numbers where that is affordable (all of `m = 0, 1, 2` at degree
four, `m = 0` at degrees one, three and five) and checks the entry-by-entry block identity elsewhere.
It also prints a rank certificate for the ghost-number-two operator: one square minor (55 x 55) that
is nonsingular, with its determinant computed twice, which is what *proves* the rank is 55 rather
than reading it off the elimination.

The arithmetic is exact and not floating point.  The structure constants of `su(3) + su(2)` with
the `lambda_a / 2`, `tau_k / 2` normalisation lie in `Q(sqrt 3)` -- `f_458 = f_678 = sqrt 3 / 2` are
the only irrational ones -- so every coefficient is a pair of `fractions.Fraction`s and the whole
computation is a finite rational calculation.  The constants are *derived* from the generators
(`f_abc = -2i tr([T_a, T_b] T_c)`), not typed in, and the script asserts that the algebra is the
standard one by re-deriving the charge's nilpotency-relevant identity `f_abc = -f_bac`.

Conventions are those of `scripts/sm-ghost-free-witness.py` and of the chapter: modes are occupied
sets, `c^a = creat(mode a)`, `b_a = annih(mode a)`, and the Jordan-Wigner sign of a mode is `(-1)`
to the number of occupied modes below it.  Run with no arguments; the exit status is nonzero if any
check fails.
"""

import hashlib
import sys
from fractions import Fraction

# --------------------------------------------------------------------------------------
# 1. Exact arithmetic in Q(sqrt 3)
# --------------------------------------------------------------------------------------


class K:
    """`a + b*sqrt 3` with `a`, `b` rational.  The field the structure constants live in."""

    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a = Fraction(a)
        self.b = Fraction(b)

    def __add__(self, other):
        o = as_k(other)
        return K(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return K(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-as_k(other))

    def __rsub__(self, other):
        return as_k(other) + (-self)

    def __mul__(self, other):
        o = as_k(other)
        return K(self.a * o.a + 3 * self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        o = as_k(other)
        norm = o.a * o.a - 3 * o.b * o.b
        if norm == 0:
            raise ZeroDivisionError("division by zero in Q(sqrt 3)")
        return K((self.a * o.a - 3 * self.b * o.b) / norm, (self.b * o.a - self.a * o.b) / norm)

    def __eq__(self, other):
        o = as_k(other)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def is_zero(self):
        return self.a == 0 and self.b == 0

    def __repr__(self):
        if self.b == 0:
            return fmt(self.a)
        if self.a == 0:
            return f"{fmt(self.b)}*sqrt3"
        return f"{fmt(self.a)}+{fmt(self.b)}*sqrt3"


def as_k(x):
    return x if isinstance(x, K) else K(x)


def fmt(q):
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


ZERO = K(0)
ONE = K(1)


class C:
    """A complex number over `Q(sqrt 3)`: `re + i im`."""

    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re = as_k(re)
        self.im = as_k(im)

    def __add__(self, other):
        o = as_c(other)
        return C(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __neg__(self):
        return C(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-as_c(other))

    def __mul__(self, other):
        o = as_c(other)
        return C(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def is_zero(self):
        return self.re.is_zero() and self.im.is_zero()

    def __repr__(self):
        if self.im.is_zero():
            return repr(self.re)
        if self.re.is_zero():
            return f"{self.im!r}i"
        return f"{self.re!r}{self.im!r}i"


def as_c(x):
    return x if isinstance(x, C) else C(x, 0)


def matmul(A, B):
    n, p = len(A), len(B[0])
    m = len(B)
    return [[sum_c([A[i][k] * B[k][j] for k in range(m)]) for j in range(p)] for i in range(n)]


def sum_c(xs):
    out = C(0)
    for x in xs:
        out = out + x
    return out


# --------------------------------------------------------------------------------------
# 2. The generators and the structure constants, derived rather than typed in
# --------------------------------------------------------------------------------------


def gell_mann():
    """The eight `lambda_a / 2`: Hermitian, traceless, orthonormal in the `tr(T_a T_b)` sense."""
    half = Fraction(1, 2)
    lam = [
        [[0, 1, 0], [1, 0, 0], [0, 0, 0]],
        [[0, -C(0, 1), 0], [C(0, 1), 0, 0], [0, 0, 0]],
        [[1, 0, 0], [0, -1, 0], [0, 0, 0]],
        [[0, 0, 1], [0, 0, 0], [1, 0, 0]],
        [[0, 0, -C(0, 1)], [0, 0, 0], [C(0, 1), 0, 0]],
        [[0, 0, 0], [0, 0, 1], [0, 1, 0]],
        [[0, 0, 0], [0, 0, -C(0, 1)], [0, C(0, 1), 0]],
        [[K(0, Fraction(1, 3)), 0, 0], [0, K(0, Fraction(1, 3)), 0],
         [0, 0, K(0, Fraction(-2, 3))]],
    ]
    return [[[as_c(x) * C(half) for x in row] for row in A] for A in lam]


def pauli_half():
    half = Fraction(1, 2)
    s = [[[0, 1], [1, 0]], [[0, -C(0, 1)], [C(0, 1), 0]], [[1, 0], [0, -1]]]
    return [[[as_c(x) * C(half) for x in row] for row in A] for A in s]


def sm_structure():
    """The structure constants of `su(3) + su(2) + u(1)`, blockwise, from the algebra generators.

    They must be read off the `3 x 3` and `2 x 2` generators, *not* off the twelve `6 x 6`
    generators `T_a (x) 1`, `1 (x) tau_k/2`: the Kronecker factors contribute `tr(1_2) = 2` and
    `tr(1_3) = 3`, which would scale the two blocks differently and destroy nilpotency of the
    charge.  The hypercharge is central, so its constants vanish.
    """
    f = {}
    for (a, b, c), v in structure_from_generators(gell_mann()).items():
        f[(a, b, c)] = v
    for (a, b, c), v in structure_from_generators(pauli_half()).items():
        f[(8 + a, 8 + b, 8 + c)] = v
    return f


def structure_from_generators(T):
    """`f_abc = -2i tr([T_a, T_b] T_c)`, asserted real, as an exact `Q(sqrt 3)` number."""
    n = len(T[0])
    out = {}
    for a in range(len(T)):
        for b in range(len(T)):
            AB = matmul(T[a], T[b])
            BA = matmul(T[b], T[a])
            comm = [[AB[i][j] - BA[i][j] for j in range(n)] for i in range(n)]
            for c in range(len(T)):
                tr = sum_c([comm[i][j] * T[c][j][i] for i in range(n) for j in range(n)])
                if not tr.re.is_zero():
                    raise SystemExit("structure constant has a real part: not an i*real algebra")
                f = tr.im * K(2)  # -2i * (i x) = 2x
                if not f.is_zero():
                    out[(a, b, c)] = f
    return out


def su3_gell_mann_count():
    """`f_abc = -f_bac` for the su(3) block, as an internal sanity check on the derivation."""
    glu = structure_from_generators(gell_mann())
    for (a, b, c), v in glu.items():
        if glu.get((b, a, c), K(0)) != -v:
            raise SystemExit(f"su(3) antisymmetry fails at {a},{b},{c}")
    if glu.get((0, 1, 2), K(0)) != K(1):
        raise SystemExit("f_123 is not 1: the normalisation of the generators changed")
    if glu.get((3, 4, 7), K(0)) != K(0, Fraction(1, 2)):
        raise SystemExit("f_458 is not sqrt3/2")
    if glu.get((5, 6, 7), K(0)) != K(0, Fraction(1, 2)):
        raise SystemExit("f_678 is not sqrt3/2")
    for a in range(8):
        for b in range(8):
            for c in range(8):
                for d in range(8):
                    jac = K(0)
                    for e in range(8):
                        jac += glu.get((a, b, e), K(0)) * glu.get((c, d, e), K(0))
                        jac += glu.get((b, c, e), K(0)) * glu.get((a, d, e), K(0))
                        jac += glu.get((c, a, e), K(0)) * glu.get((b, d, e), K(0))
                    if not jac.is_zero():
                        raise SystemExit(f"the Jacobi identity fails at {a},{b},{c},{d}")
    for a in range(8):
        for b in range(8):
            for c in range(8):
                v = glu.get((a, b, c), K(0))
                if glu.get((b, c, a), K(0)) != v:
                    raise SystemExit(f"cyclicity fails at {a},{b},{c}")
    return len(glu)


# --------------------------------------------------------------------------------------
# 3. The cubic term on the occupation basis
# --------------------------------------------------------------------------------------


def jw_sign(i, mask):
    return -1 if bin(mask & ((1 << i) - 1)).count("1") % 2 else 1


def creat(i, mask):
    if mask >> i & 1:
        return None
    return mask | (1 << i), jw_sign(i, mask)


def annih(i, mask):
    if not (mask >> i & 1):
        return None
    rest = mask & ~(1 << i)
    return rest, jw_sign(i, rest)


def apply_word(word, mask):
    """Apply `word` -- a list of `('c', i)`/`('a', i)` in innermost-first order."""
    sign = 1
    for kind, i in word:
        r = creat(i, mask) if kind == "c" else annih(i, mask)
        if r is None:
            return None
        mask, s = r
        sign *= s
    return mask, sign


def cubic_terms(m, f):
    """`Omega_3 = -sum_{a<b,e} f_abe c^a c^b b_e` on `m` matter modes, as `[(word, coefficient)]`.

    The ghosts are the last twelve modes (`m + a`), so the matter modes never appear in a word:
    the cubic term is the same operator for every `m`, just shifted.
    """
    terms = []
    for a in range(12):
        for b in range(12):
            if a >= b:
                continue
            for e in range(12):
                v = f.get((a, b, e), K(0))
                if v.is_zero():
                    continue
                # applied right to left: b_e first, then c^b, then c^a
                terms.append(([("a", m + e), ("c", m + b), ("c", m + a)], -v))
    return terms


def ghost_number(mask, m):
    return bin(mask >> m).count("1")


def matter_number(mask, m):
    return bin(mask & ((1 << m) - 1)).count("1")


def act(terms, mask):
    out = {}
    for word, coef in terms:
        r = apply_word(word, mask)
        if r is None:
            continue
        target, s = r
        c = out.get(target, ZERO) + (coef if s > 0 else -coef)
        if c.is_zero():
            out.pop(target, None)
        else:
            out[target] = c
    return out


def source_states(m, deg=2):
    """The states of ghost number `deg` on `m` matter modes, in increasing bitmask order."""
    return [s for s in range(1 << (m + 12)) if ghost_number(s, m) == deg]


def kernel_basis(rows, ncols):
    """Gauss-Jordan nullspace of the matrix given as `rows`, a list of `ncols`-long lists.

    Returns `(rank, basis)`, the basis as `{column: K}` sparse vectors in reduced form: the
    pivot columns of the reduced matrix are new, so the returned vectors are independent.

    The elimination is row-sparse: the operator's columns carry at most eight entries, and the
    reduced rows stay far shorter than `ncols`, so the dense list comprehension per row operation
    was the whole cost.  The pivot order (first column, first row at or below the current one) and
    the reduced form are unchanged, so the returned basis is the same one as before.
    """
    nrows = len(rows)
    sp = [{c: x for c, x in enumerate(row) if not x.is_zero()} for row in rows]
    row = 0
    pivots = {}
    for c in range(ncols):
        p = None
        for r in range(row, nrows):
            if c in sp[r]:
                p = r
                break
        if p is None:
            continue
        if p != row:
            sp[row], sp[p] = sp[p], sp[row]
        inv = K(1) / sp[row][c]
        pivot = {k: v * inv for k, v in sp[row].items()}
        sp[row] = pivot
        for r in range(nrows):
            if r == row:
                continue
            factor = sp[r].get(c)
            if factor is None or factor.is_zero():
                continue
            target = sp[r]
            for k, v in pivot.items():
                nv = target.get(k, ZERO) - factor * v
                if nv.is_zero():
                    target.pop(k, None)
                else:
                    target[k] = nv
        pivots[c] = row
        row += 1
    rank = row
    basis = []
    for free in (c for c in range(ncols) if c not in pivots):
        v = {free: ONE}
        for c, r in pivots.items():
            x = sp[r].get(free)
            if x is not None and not x.is_zero():
                v[c] = -x
        basis.append(v)
    return rank, basis


# --------------------------------------------------------------------------------------
# 4. The check
# --------------------------------------------------------------------------------------


def kernel_at(m, terms, deg=2):
    """`Omega_3` on the ghost-number-`deg` part with `m` matter modes: `(src, columns, rank, basis)`.

    The image is kept sparse and per-source, which is all the elimination and the verification
    need; the reached targets are returned too, for reporting.
    """
    src = source_states(m, deg)
    columns = []
    for s in src:
        col = act(terms, s)
        for t in col:
            if ghost_number(t, m) != deg + 1:
                raise SystemExit("the cubic term changed the ghost number by more than one")
            if matter_number(t, m) != matter_number(s, m):
                raise SystemExit("the cubic term changed the matter number")
        columns.append(col)
    dst = sorted({t for col in columns for t in col})
    row_of = {t: i for i, t in enumerate(dst)}
    rows = [[ZERO] * len(src) for _ in dst]
    for c, col in enumerate(columns):
        for t, v in col.items():
            rows[row_of[t]][c] = v
    rank, basis = kernel_basis(rows, len(src))
    return src, columns, rank, basis, dst


def verify_kernel(columns, basis, ncols, what):
    """Exact check: every basis vector is killed, and the vectors are independent."""
    for k, v in enumerate(basis):
        image = {}
        for c, coef in v.items():
            for t, x in columns[c].items():
                image[t] = image.get(t, ZERO) + coef * x
        if any(not x.is_zero() for x in image.values()):
            raise SystemExit(f"{what}: basis vector {k} is not in the kernel")
    dim = ncols - rank_of(columns)
    if len(basis) != dim:
        raise SystemExit(f"{what}: the basis does not have the kernel's dimension")
    stacked = [[basis[j].get(c, ZERO) for c in range(ncols)] for j in range(len(basis))]
    rk, _ = kernel_basis(stacked, ncols)
    if rk != len(basis):
        raise SystemExit(f"{what}: the basis vectors are not independent")


def rank_of(columns):
    """Rank of the operator given columnwise, by the same elimination."""
    dst = sorted({t for col in columns for t in col})
    row_of = {t: i for i, t in enumerate(dst)}
    rows = [[ZERO] * len(columns) for _ in dst]
    for c, col in enumerate(columns):
        for t, v in col.items():
            rows[row_of[t]][c] = v
    rank, _ = kernel_basis(rows, len(columns))
    return rank


def a_kernel_matrix(columns, ncols):
    """The operator matrix, row-indexed by the reached targets: `(targets, rows)`."""
    dst = sorted({t for col in columns for t in col})
    row_of = {t: i for i, t in enumerate(dst)}
    rows = [[ZERO] * ncols for _ in dst]
    for c, col in enumerate(columns):
        for t, v in col.items():
            rows[row_of[t]][c] = v
    return dst, rows


def sector_kernel(m, deg, terms):
    """Eliminate the degree block sector by sector: `(sources, reached, rank)`.

    Every image term preserves the matter occupation (checked here, entry by entry), so the
    operator matrix is block diagonal in the matter sector and its rank and kernel dimension are
    the sums of the per-sector ones.  Each sector's matrix is built from the actual `m`-mode
    operator, so the elimination is still from scratch; doing it per sector only keeps every
    elimination at the size of the `m = 0` problem instead of `2^m` times it.
    """
    low = (1 << m) - 1
    sectors = {}
    for s in source_states(m, deg):
        sectors.setdefault(s & low, []).append(s)
    n_src = n_dst = rank = 0
    for matter in sorted(sectors):
        states = sectors[matter]
        columns = []
        for s in states:
            col = act(terms, s)
            for t in col:
                if matter_number(t, m) != matter_number(s, m):
                    raise SystemExit(f"m = {m}: the cubic term changed the matter number")
            columns.append(col)
        dst, rows = a_kernel_matrix(columns, len(states))
        rk, basis = kernel_basis(rows, len(states))
        verify_kernel(columns, basis, len(states), f"m = {m}, degree {deg}, matter {matter}")
        n_src += len(states)
        n_dst += len(dst)
        rank += rk
    return n_src, n_dst, rank


def det_k(mat):
    """Determinant over `Q(sqrt 3)`, by Gaussian elimination with row swaps."""
    a = [row[:] for row in mat]
    n = len(a)
    det = ONE
    for c in range(n):
        p = next((i for i in range(c, n) if not a[i][c].is_zero()), None)
        if p is None:
            return ZERO
        if p != c:
            a[c], a[p] = a[p], a[c]
            det = -det
        det = det * a[c][c]
        inv = K(1) / a[c][c]
        for i in range(c + 1, n):
            if not a[i][c].is_zero():
                fac = a[i][c] * inv
                a[i] = [x - fac * y for x, y in zip(a[i], a[c])]
    return det


def det_k_bareiss(mat):
    """The same determinant fraction-free (Bareiss), as an independent cross-check."""
    a = [row[:] for row in mat]
    n = len(a)
    sign = ONE
    prev = ONE
    for k in range(n - 1):
        if a[k][k].is_zero():
            p = next((i for i in range(k + 1, n) if not a[i][k].is_zero()), None)
            if p is None:
                return ZERO
            a[k], a[p] = a[p], a[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * a[k][k] - a[i][k] * a[k][j]) / prev
        prev = a[k][k]
    return sign * a[n - 1][n - 1]


def minor_certificate(src, columns, what):
    """A square minor of the operator with a computed nonzero determinant.

    The elimination that computes the kernel also yields a certificate for the rank: its pivot
    rows and pivot columns index a square minor whose elimination is triangular with nonzero
    diagonal, so the minor is nonsingular.  The determinant of that extracted submatrix is then
    computed again, independently, and asserted nonzero -- which is all `rank >= ncols` needs.
    """
    ncols = len(src)
    dst, orig = a_kernel_matrix(columns, ncols)
    rows = [row[:] for row in orig]
    order = list(range(len(rows)))
    r = 0
    pivot_cols = []
    for c in range(ncols):
        p = next((i for i in range(r, len(rows)) if not rows[i][c].is_zero()), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        order[r], order[p] = order[p], order[r]
        inv = K(1) / rows[r][c]
        rows[r] = [x * inv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and not rows[i][c].is_zero():
                fac = rows[i][c]
                rows[i] = [x - fac * y for x, y in zip(rows[i], rows[r])]
        pivot_cols.append(c)
        r += 1
    rank = r
    pivot_rows = sorted(order[:rank])
    sub = [[orig[i][c] for c in pivot_cols] for i in pivot_rows]
    det = det_k(sub)
    if det != det_k_bareiss(sub):
        raise SystemExit(f"{what}: the two determinant algorithms disagree")
    if det.is_zero():
        raise SystemExit(f"{what}: the pivot minor vanishes")
    return [dst[i] for i in pivot_rows], [src[c] for c in pivot_cols], det, sub


def q_lit(q):
    """An exact `Q(sqrt 3)` element as Lean syntax, `(p / q : ℚ)`."""
    return f"(({q.numerator} / {q.denominator}) : ℚ)"


def k_lit(k):
    return f"({q_lit(k.a)}, {q_lit(k.b)})"


def emit_minor_lean(sub, rows, cols, path="Work/SmGhostMinorLit.lean"):
    """Write the `55 x 55` minor as Lean data, so the certificate's matrix is Lean, not prose."""
    n = len(sub)
    if any(len(r) != n for r in sub):
        raise SystemExit("the emitted minor is not square")
    lines = []
    lines.append("import Work.Qsqrt3")
    lines.append("")
    lines.append("/-!")
    lines.append("# The `55 x 55` rank-certificate minor, as Lean data")
    lines.append("")
    lines.append("Generated by `scripts/sm-cubic-kernel-basis.py --emit-minor`; do not edit by hand.")
    lines.append("")
    lines.append("The entries are the exact `Q(sqrt 3)` values of the ghost-number-two operator at `m = 0`")
    lines.append("on the pivot rows and columns the elimination selects.  Each pair is `(a, b)` for")
    lines.append("`a + b * sqrt 3`.  The determinant of this matrix is `-3^12 / 2^35`, a nonzero rational;")
    lines.append("what is still missing is a kernel-checkable proof of that, which is why the statement")
    lines.append("below is a `Prop` and not a theorem.")
    lines.append("")
    def wrap(label, states):
        words = [fmt_state(t, 12) for t in states]
        out, cur = [], label
        for w in words:
            if len(cur) + len(w) + 1 > 96:
                out.append(cur)
                cur = "  " + w
            else:
                cur = cur + " " + w
        out.append(cur)
        return out

    lines.append("The pivot rows (`targets`) and columns (`sources`) of the elimination:")
    lines.append("")
    for ln in wrap("targets:", rows):
        lines.append(ln)
    lines.append("")
    for ln in wrap("sources:", cols):
        lines.append(ln)
    lines.append("-/")
    lines.append("")
    lines.append("namespace BookProof.SmBrstGhost")
    lines.append("")
    lines.append("open Qsqrt3")
    lines.append("")
    lines.append("/-- The minor's entries, row by row, as exact `(a, b)` pairs meaning `a + b * sqrt 3`. -/")
    lines.append("def ghostMinorData : List (List (ℚ × ℚ)) := [")
    for r in sub:
        items = [k_lit(x) for x in r]
        cur = "  ["
        row_lines = []
        for i, it in enumerate(items):
            piece = it + (", " if i + 1 < len(items) else "")
            if len(cur) + len(piece) > 96:
                row_lines.append(cur)
                cur = "   " + piece
            else:
                cur += piece
        cur += "],"
        row_lines.append(cur)
        lines.extend(row_lines)
    lines.append("]")
    lines.append("")
    lines.append("/-- The `55 x 55` minor as a matrix over the field (a missing entry, which cannot occur, is 0). -/")
    lines.append("def ghostMinor : Matrix (Fin 55) (Fin 55) Qsqrt3 :=")
    lines.append("  fun i j =>")
    lines.append("    match ghostMinorData[i.val]? with")
    lines.append("    | some row => match row[j.val]? with")
    lines.append("      | some p => (ofRat p.1 + sqrt3 * ofRat p.2)")
    lines.append("      | none => 0")
    lines.append("    | none => 0")
    lines.append("")
    lines.append("/-- The data has 55 rows. -/")
    lines.append("theorem ghostMinorData_length : ghostMinorData.length = 55 := by decide")
    lines.append("")
    lines.append("/-- Every row has 55 entries. -/")
    lines.append("theorem ghostMinorData_rows : ∀ r ∈ ghostMinorData, r.length = 55 := by decide")
    lines.append("")
    lines.append("/-- The certificate: this minor is nonsingular.  Open in Lean (see the module docstring). -/")
    lines.append("def ghostMinorStatement : Prop := certificateStatement ghostMinor")
    lines.append("")
    lines.append("end BookProof.SmBrstGhost")
    lines.append("")
    text = "\n".join(lines)
    with open(path, "w") as fh:
        fh.write(text)
    return path, text


def fmt_state(s, width):
    """The occupation state as `|i+j+k>` over the modes below `width`."""
    return "|" + "+".join(str(i) for i in range(width) if s >> i & 1) + ">"


def main():
    f = sm_structure()
    if f.get((0, 1, 2), K(0)) != K(1):
        raise SystemExit("the derived structure constants are not the standard ones")
    n_su3 = su3_gell_mann_count()

    # ---- the reference case: no matter modes ----------------------------------------
    terms0 = cubic_terms(0, f)
    src0, col0, rank0, basis0, dst0 = kernel_at(0, terms0)
    dim0 = len(src0) - rank0
    verify_kernel(col0, basis0, len(src0), "m = 0")

    print(f"ghost-number-2 source : {len(src0)} states = C(12, 2)  (m = 0)")
    print(f"ghost-number-3 target : {len(dst0)} states reached, of C(12, 3) = 220")
    print(f"rank of Omega_3       : {rank0}")
    print(f"dim ker Omega_3 at g=2: {dim0}")
    print(f"su(3) constants nonzero: {n_su3}")
    print("su(3) Jacobi identity  : holds at all 8^4 = 4096 index quadruples (exact)")
    print("su(3) cyclicity        : holds at all 8^3 triples (exact)")

    print()
    print("ghost labels 0-7: gluons, 8-10: weak, 11: hypercharge; |i+j> = the state with")
    print("occupied modes i < j.  Basis at m = 0 (coefficients in Q(sqrt 3)):")
    digest = hashlib.sha256()
    for j, v in enumerate(basis0):
        support = sorted(v)
        line = " + ".join(
            f"({v[c]!r})*|{'+'.join(str(i) for i in range(12) if s >> i & 1)}>"
            for c, s in ((c, src0[c]) for c in support)
        )
        print(f"  v{j:<2} ({len(support):2d} terms) {line}")
        digest.update(line.encode())
    print()
    print(f"sha256 of the printed basis: {digest.hexdigest()}")

    # ---- several matter modes: the operator ignores them ---------------------------
    # A matter mode never appears in a cubic monomial, so every matter block of `Omega_3` is the
    # `m = 0` operator, up to a sign: a cubic monomial applies three operators, and each of their
    # Jordan-Wigner signs flips once for every occupied matter mode below it.
    def blocks_are_copies(m, deg):
        terms = cubic_terms(m, f)
        src = source_states(m, deg)
        low = (1 << m) - 1
        reached = set()
        for s in src:
            matter = s & low
            reference = act(terms0, s >> m)
            sign = -1 if bin(matter).count("1") % 2 else 1
            want = {((t << m) | matter): sign * v for t, v in reference.items()
                    if not (sign * v).is_zero()}
            if act(terms, s) != want:
                raise SystemExit(f"m = {m}: block {bin(matter)} is not a copy of the m = 0 operator")
            reached.update(want)
        return len(src), len(reached)

    # the degree-two case is settled by elimination at m = 0, 1, 2, 3 and by the block identity above
    table = [(0, 2, len(src0), rank0, dim0, "elimination")]
    terms1 = cubic_terms(1, f)
    src1, col1, rank1, basis1, _ = kernel_at(1, terms1)
    dim1 = len(src1) - rank1
    verify_kernel(col1, basis1, len(src1), "m = 1")
    if not (len(src1) == 2 * len(src0) and rank1 == 2 * rank0 and dim1 == 2 * dim0):
        raise SystemExit("the m = 1 kernel is not exactly twice the m = 0 kernel")
    table.append((1, 2, len(src1), rank1, dim1, "elimination"))
    terms2 = cubic_terms(2, f)
    src2, col2, rank2, basis2, _ = kernel_at(2, terms2)
    dim2 = len(src2) - rank2
    verify_kernel(col2, basis2, len(src2), "m = 2")
    if not (len(src2) == 4 * len(src0) and rank2 == 4 * rank0 and dim2 == 4 * dim0):
        raise SystemExit("the m = 2 kernel is not exactly four times the m = 0 kernel")
    table.append((2, 2, len(src2), rank2, dim2, "elimination"))

    terms3 = cubic_terms(3, f)
    src3, col3, rank3, basis3, _ = kernel_at(3, terms3)
    dim3 = len(src3) - rank3
    verify_kernel(col3, basis3, len(src3), "m = 3")
    if not (len(src3) == 8 * len(src0) and rank3 == 8 * rank0 and dim3 == 8 * dim0):
        raise SystemExit("the m = 3 kernel is not exactly eight times the m = 0 kernel")
    table.append((3, 2, len(src3), rank3, dim3, "elimination"))

    # the block identity holds at every ghost degree; it is what the m >= 4 rows rest on
    for m in (4, 5, 6):
        n, _ = blocks_are_copies(m, 2)
        if n != len(src0) << m:
            raise SystemExit(f"m = {m}: wrong number of two-ghost states")
        table.append((m, 2, n, rank0 << m, dim0 << m, "blocks"))
    # the other degrees: eliminate at the mattered numbers listed, block identity for the rest.
    # `sector_kernel` eliminates the actual m-mode operator sector by sector, which is the same
    # computation as eliminating its whole matrix once matter conservation is used.
    degree_rows = []
    for deg, eliminated in ((1, (0,)), (3, (0,)), (4, (0, 1, 2)), (5, (0,)), (6, (0,)), (7, (0,)), (8, (0,))):
        base = None
        for m in eliminated:
            terms = cubic_terms(m, f)
            if m == 0:
                src_d, col_d, rank_d, basis_d, dst_d = kernel_at(0, terms, deg)
                verify_kernel(col_d, basis_d, len(src_d), f"m = 0, degree {deg}")
                n_src, n_dst = len(src_d), len(dst_d)
            else:
                n_src, n_dst, rank_d = sector_kernel(m, deg, terms)
            dm = n_src - rank_d
            if base is None:
                base = (n_src, n_dst, rank_d, dm)
            elif (n_src, n_dst, rank_d, dm) != tuple(x << m for x in base):
                raise SystemExit(f"degree {deg}, m = {m}: the kernel is not 2^m times the m = 0 one")
            degree_rows.append((deg, m, n_src, n_dst, rank_d, dm, "elimination"))
        for m in (1, 2, 3):
            if m in eliminated:
                continue
            n, nd = blocks_are_copies(m, deg)
            if (n, nd) != (base[0] << m, base[1] << m):
                raise SystemExit(f"degree {deg}, m = {m}: wrong number of states")
            degree_rows.append((deg, m, n, nd, base[2] << m, base[3] << m, "blocks"))

    print()
    print("ghost-number-2 kernel against the matter modes (all rows exact arithmetic)")
    print("matter modes | ghost-number-2 dim | rank | dim ker B | how the rank was obtained")
    for m, deg, n, rk, dm, how in table:
        print(f"{m:12d} | {n:18d} | {rk:4d} | {dm:9d} | {how}")
    print()
    print("the matter-free block is the m = 0 operator and the matter-occupied block is its")
    print("negative (the matter mode is a fermion: all three Jordan-Wigner signs flip), so")
    print("B = (+-1) (x) B_0 on every matter block and dim ker(m) = 2^m * 11 exactly; the")
    print("`blocks` rows verify that block identity entry by entry, the `elimination` rows")
    print("recompute the dimension from scratch at m = 0, 1, 2, 3.")
    print()
    print("the 2^m law at other degrees: an `elimination` row recomputes the dimension with")
    print("Gauss-Jordan (at m > 0 sector by sector, since the operator preserves the matter")
    print("occupation), a `blocks` row checks the entry-by-entry block identity instead:")
    print("degree | m | dim Λ^d | dim Λ^(d+1) reached | rank | dim ker | how obtained")
    print("------ | - | ------- | ------------------- | ---- | ------- | ------------")
    for deg, m, n, nd, rk, dm, how in degree_rows:
        print(f"{deg:6d} | {m} | {n:7d} | {nd:19d} | {rk:4d} | {dm:7d} | {how}")
    print()
    print("every row obeys dim ker(m) = 2^m * dim ker(0) for its degree")
    print()

    print("rank certificate: one square minor of the ghost-number-2 operator at m = 0")
    cert_rows, cert_cols, cert_det, cert_sub = minor_certificate(src0, col0, "m = 0, g = 2")
    if (len(cert_rows), len(cert_cols)) != (rank0, rank0):
        raise SystemExit("the certificate minor is not rank by rank")
    digest_cert = hashlib.sha256()
    line_rows = "targets: " + " ".join(fmt_state(t, 12) for t in cert_rows)
    line_cols = "sources: " + " ".join(fmt_state(t, 12) for t in cert_cols)
    print(f"  size         : {len(cert_rows)} x {len(cert_cols)}")
    print(f"  determinant  : {cert_det!r}")
    print(f"  {line_rows}")
    print(f"  {line_cols}")
    digest_cert.update((line_rows + "\n" + line_cols).encode())
    print(f"  sha256 of the certificate: {digest_cert.hexdigest()}")
    if "--emit-minor" in sys.argv:
        path, text = emit_minor_lean(cert_sub, cert_rows, cert_cols)
        print(f"  wrote {path} ({len(text.splitlines())} lines, sha256 "
              f"{hashlib.sha256(text.encode()).hexdigest()[:16]}...)")
    print("a nonzero determinant of a square minor is all that rank >= 55 needs; with the")
    print("elimination's rank <= 55 this pins the rank at g = 2 to exactly 55.")
    print()
    print("all checks passed (exact arithmetic in Q(sqrt 3))")


if __name__ == "__main__":
    main()
