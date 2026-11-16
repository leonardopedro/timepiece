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
scratch by elimination at `m = 0, 1` and follows from the block identity for `m = 2, ..., 6`, where
the table reports how each rank was obtained.

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


def source_states(m):
    """The two-ghost states on `m` matter modes, in increasing bitmask order."""
    return [s for s in range(1 << (m + 12)) if ghost_number(s, m) == 2]


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


def kernel_at(m, terms):
    """`Omega_3` on the ghost-number-two part with `m` matter modes: `(src, columns, rank, basis)`.

    The image is kept sparse and per-source, which is all the elimination and the verification
    need; the reached targets are returned too, for reporting.
    """
    src = source_states(m)
    columns = []
    for s in src:
        col = act(terms, s)
        for t in col:
            if ghost_number(t, m) != 3:
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
    def blocks_are_copies(m):
        terms = cubic_terms(m, f)
        src = source_states(m)
        low = (1 << m) - 1
        for s in src:
            matter = s & low
            reference = act(terms0, s >> m)
            sign = -1 if bin(matter).count("1") % 2 else 1
            want = {((t << m) | matter): sign * v for t, v in reference.items()
                    if not (sign * v).is_zero()}
            if act(terms, s) != want:
                raise SystemExit(f"m = {m}: the block {bin(matter)} is not a copy of the m = 0 operator")
        return len(src)

    table = [(0, len(src0), rank0, dim0, "elimination")]
    # the m = 1 case is settled by full elimination as well, as an independent check
    terms1 = cubic_terms(1, f)
    src1, col1, rank1, basis1, _ = kernel_at(1, terms1)
    dim1 = len(src1) - rank1
    verify_kernel(col1, basis1, len(src1), "m = 1")
    if not (len(src1) == 2 * len(src0) and rank1 == 2 * rank0 and dim1 == 2 * dim0):
        raise SystemExit("the m = 1 kernel is not exactly twice the m = 0 kernel")
    table.append((1, len(src1), rank1, dim1, "elimination"))
    for m in range(2, 7):
        n = blocks_are_copies(m)
        if n != len(src0) << m:
            raise SystemExit(f"m = {m}: wrong number of two-ghost states")
        table.append((m, n, rank0 << m, dim0 << m, "blocks"))

    print()
    print("matter modes | ghost-number-2 dim | rank | dim ker B | how the rank was obtained")
    for m, n, rk, dm, how in table:
        print(f"{m:12d} | {n:18d} | {rk:4d} | {dm:9d} | {how}")
    print()
    print("the matter-free block is the m = 0 operator and the matter-occupied block is its")
    print("negative (the matter mode is a fermion: all three Jordan-Wigner signs flip), so")
    print("B = (+-1) (x) B_0 on every matter block and dim ker(m) = 2^m * 11 exactly; the")
    print("`blocks` rows verify that block identity entry by entry, the `elimination` rows")
    print("recompute the dimension from scratch.")
    # ---- every matter block carries its own copy of the eleven vectors -----------------
    at0 = {s: i for i, s in enumerate(src0)}
    for m in (1, 2, 3):
        terms = cubic_terms(m, f)
        src = source_states(m)
        at = {s: i for i, s in enumerate(src)}
        columns = [act(terms, s) for s in src]
        lifted_all = []
        for matter in range(1 << m):
            for v in basis0:
                lifted = {at[(src0[c] << m) | matter]: x for c, x in v.items()}
                image = {}
                for c, coef in lifted.items():
                    for t, x in columns[c].items():
                        image[t] = image.get(t, ZERO) + coef * x
                if any(not x.is_zero() for x in image.values()):
                    raise SystemExit(f"m = {m}: a lifted basis vector is not in the kernel")
                lifted_all.append(lifted)
        used = sorted({c for v in lifted_all for c in v})
        stacked = [[v.get(c, ZERO) for c in used] for v in lifted_all]
        rk, _ = kernel_basis(stacked, len(used))
        if rk != len(lifted_all):
            raise SystemExit(f"m = {m}: the lifted vectors are not independent")
    print()
    print("the eleven vectors lift to every matter block and are still killed there")
    print("(checked at m = 1, 2, 3), and the lifted family is independent, so")
    print("dim ker(m) >= 2^m * 11 for those m -- matching the table above.")
    print()
    print("all checks passed (exact arithmetic in Q(sqrt 3))")


if __name__ == "__main__":
    main()
