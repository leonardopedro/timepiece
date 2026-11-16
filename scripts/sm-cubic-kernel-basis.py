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


def cubic_terms(f):
    """`Omega_3 = -sum_{a<b,e} f_abe c^a c^b b_e`, as `[(word, coefficient)]`."""
    n = 12
    terms = []
    for a in range(n):
        for b in range(n):
            if a >= b:
                continue
            for e in range(n):
                v = f.get((a, b, e), K(0))
                if v.is_zero():
                    continue
                # applied right to left: b_e first, then c^b, then c^a
                terms.append(([("a", e), ("c", b), ("c", a)], -v))
    return terms


def ghost_number(mask):
    return bin(mask).count("1")


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


def source_states():
    """The 66 two-ghost states, in increasing bitmask order."""
    return [s for s in range(1 << 12) if ghost_number(s) == 2]


def kernel_basis(rows, ncols):
    """Gauss-Jordan nullspace of the matrix given as `rows`, a list of `ncols`-long lists.

    Returns `(rank, basis)`, the basis as `{column: K}` sparse vectors in reduced form: the
    pivot columns of the reduced matrix are new, so the returned vectors are independent.
    """
    nrows = len(rows)
    pivot_of_row = []
    row = 0
    pivots = {}
    for c in range(ncols):
        p = None
        for r in range(row, nrows):
            if not rows[r][c].is_zero():
                p = r
                break
        if p is None:
            continue
        rows[row], rows[p] = rows[p], rows[row]
        inv = K(1) / rows[row][c]
        rows[row] = [x * inv for x in rows[row]]
        for r in range(nrows):
            if r != row and not rows[r][c].is_zero():
                factor = rows[r][c]
                rows[r] = [x - factor * y for x, y in zip(rows[r], rows[row])]
        pivots[c] = row
        pivot_of_row.append(c)
        row += 1
    rank = row
    basis = []
    for free in (c for c in range(ncols) if c not in pivots):
        v = {free: ONE}
        for c, r in pivots.items():
            if not rows[r][free].is_zero():
                v[c] = -rows[r][free]
        basis.append(v)
    return rank, basis


# --------------------------------------------------------------------------------------
# 4. The check
# --------------------------------------------------------------------------------------


def main():
    f = sm_structure()
    if f.get((0, 1, 2), K(0)) != K(1):
        raise SystemExit("the derived structure constants are not the standard ones")
    n_su3 = su3_gell_mann_count()
    terms = cubic_terms(f)

    src = source_states()
    index = {s: i for i, s in enumerate(src)}
    columns = []
    for s in src:
        col = {}
        for t, v in act(terms, s).items():
            if ghost_number(t) != 3:
                raise SystemExit("the cubic term changed the ghost number by more than one")
            col.setdefault(t, K(0))
            col[t] = v
        columns.append(col)

    # rows are the 220 three-ghost states that actually occur
    dst = sorted({t for col in columns for t in col})
    row_of = {t: i for i, t in enumerate(dst)}
    rows = [[ZERO] * len(src) for _ in dst]
    for c, col in enumerate(columns):
        for t, v in col.items():
            rows[row_of[t]][c] = v

    rank, basis = kernel_basis(rows, len(src))
    dim = len(src) - rank
    print(f"mode count            : m = 0 (no matter modes)")
    print(f"ghost-number-2 source : {len(src)} states = C(12, 2)")
    print(f"ghost-number-3 target : {len(dst)} states reached, of C(12, 3) = 220")
    print(f"rank of Omega_3       : {rank}")
    print(f"dim ker Omega_3 at g=2: {dim}")
    print(f"su(3) constants nonzero: {n_su3}")

    # exact verification of the two defining properties
    for k, v in enumerate(basis):
        image = {}
        for c, coef in v.items():
            for t, x in columns[c].items():
                val = image.get(t, ZERO) + coef * x
                image[t] = val
        if any(not x.is_zero() for x in image.values()):
            raise SystemExit(f"basis vector {k} is not in the kernel")
    if len(basis) != dim:
        raise SystemExit("the basis does not have the kernel's dimension")
    stacked = [[basis[j].get(c, K(0)) for c in range(len(src))] for j in range(len(basis))]
    rk, _ = kernel_basis(stacked, len(src))
    if rk != len(basis):
        raise SystemExit("the basis vectors are not independent")

    print()
    print("ghost labels 0-7: gluons, 8-10: weak, 11: hypercharge; |i+j> = the state with")
    print("occupied modes i < j.  Basis (coefficients in Q(sqrt 3)):")
    digest = hashlib.sha256()
    for j, v in enumerate(basis):
        support = sorted(v)
        line = " + ".join(
            f"({v[c]!r})*|{'+'.join(str(i) for i in range(12) if s >> i & 1)}>"
            for c, s in ((c, src[c]) for c in support)
        )
        print(f"  v{j:<2} ({len(support):2d} terms) {line}")
        digest.update(line.encode())
    print()
    print(f"sha256 of the printed basis: {digest.hexdigest()}")
    print("all checks passed (exact arithmetic in Q(sqrt 3))")


if __name__ == "__main__":
    main()
