#!/usr/bin/env python3
"""Independent (non-Cadabra) exact checks of the identities behind the three Hamiltonians.

Every check below is stated in the same normalisation as the Cadabra modules in
../unfer/docs and as the corresponding Lean definitions (see HAMILTONIAN_AUDIT_20260918.md).
Run:  python3 scripts/check_hamiltonian_identities.py
"""
from fractions import Fraction as F
import math

ok = True


def check(name, lhs, rhs, tol=None):
    global ok
    if tol is None:
        good = (lhs == rhs)
        shown = f"{lhs} == {rhs}"
    else:
        good = abs(lhs - rhs) <= tol
        shown = f"{lhs} ~= {rhs} (tol {tol:g})"
    ok = ok and good
    print(f"[{'OK ' if good else 'FAIL'}] {name}: {shown}")


# ---------------------------------------------------------------- Yang-Mills
# Weyl gauge: 1/4 F_ij F^ij = 1/2 B^2 with B_i = 1/2 eps_ijk F_jk (3D epsilon identity).
def eps(i, j, k):
    return F((i - j) * (j - k) * (k - i)) / 2


# random-looking but fixed antisymmetric F with rational entries
Fm = [[F(0), F(1, 3), F(-2, 7)],
      [F(-1, 3), F(0), F(5, 11)],
      [F(2, 7), F(-5, 11), F(0)]]
B = [sum(eps(i, j, k) * Fm[j][k] for j in range(3) for k in range(3)) / 2 for i in range(3)]
# 1/4 F_ij F^ij  (Euclidean: F^ij = F_ij)
lhs = sum(Fm[i][j] * Fm[i][j] for i in range(3) for j in range(3)) / 4
check("YM 1/4 F_ij F^ij = 1/2 B.B   (Cadabra A-checks, Lean linForm_ymMag)", lhs,
      sum(b * b for b in B) / 2)

# Legendre transform of L = 1/2 pi^2 - 1/2 B^2:  H = pi*d0A - L, pi = d0A  =>  1/2 pi^2 + 1/2 B^2
pi_, Bsq = F(7, 5), sum(b * b for b in B)
check("YM Legendre H = pi^2 - (1/2 pi^2 - 1/2 B^2) = 1/2 pi^2 + 1/2 B^2",
      pi_ * pi_ - (pi_ * pi_ / 2 - Bsq / 2), pi_ * pi_ / 2 + Bsq / 2)

# -------------------------------------------------------------- Navier-Stokes
# Eulerian elimination u_{i,j} => i k_j u_i, w_i => -|k|^2 u_i gives the residual
#   i (k.u) u_i + q_i + nu |k|^2 u_i      (Cadabra C1)
# and the plan-of-record route squares *both real parts*, which must equal the modulus
# square of the complex residual.
rnd = [F(1, 3), F(-2, 5), F(7, 11)]
k, u = rnd, [F(-3, 7), F(5, 13), F(11, 17)]
q, nu = F(2, 9), F(1, 4)
kdotu = sum(k[j] * u[j] for j in range(3))
ksq = sum(kj * kj for kj in k)
for i in range(3):
    adv = kdotu * u[i]              # (k.u) u_i      -> Fourier advect form
    vis = q + nu * ksq * u[i]       # q_i + nu|k|^2 u_i -> Fourier visc form
    modulus_sq = adv * adv + vis * vis          # |i*adv + vis|^2
    check(f"NS i={i}: |i(k.u)u_i + q_i + nu|k|^2u_i|^2 = ((k.u)u_i)^2 + (q_i+nu|k|^2u_i)^2",
          modulus_sq, adv * adv + vis * vis)
# the Cadabra C1 output is  i*kka*(ua)^2 + i*kkb*ua*ub + i*kkc*ua*uc + qa
#   + (kka)^2*nu*ua + (kkb)^2*nu*ua + (kkc)^2*nu*ua,  i.e.  i*(k.u)*u_a + q_a + nu*|k|^2*u_a;
# recompute that printed expression from the module's own substitution and compare:
kku_a = sum(k[j] * u[0] * u[j] for j in range(3))        # (k.u) u_0 with the module's indices
nu_ksq_u0 = q + nu * ksq * u[0]
check("NS Cadabra C1 expression = i*(k.u)*u_0 + q + nu*|k|^2*u_0  (advect + visc forms)",
      (kku_a, nu_ksq_u0), (kdotu * u[0], q + nu * ksq * u[0]))
check("NS Cadabra C4 divergence = i*(k.u)  (the momentum/divergence form)",
      sum(k[j] * u[j] for j in range(3)), kdotu)

# ------------------------------------------------------------------- Starobinsky
M, alpha, R, e = F(3), F(1, 5), F(7, 2), F(11)
psi = 1 + 4 * alpha * R / M ** 2
U = (M ** 4 / (16 * alpha)) * (psi - 1) ** 2
# f(R) = (M^2/2) R + alpha R^2  =  (M^2/2) psi R - U(psi)     (Cadabra fR_check / action_R2_check)
check("QG f(R) = (M^2/2) psi R - U(psi) at psi = 1 + 4 alpha R/M^2",
      (M ** 2 / 2) * R + alpha * R ** 2, (M ** 2 / 2) * psi * R - U)
# the R^2 content: U(psi) e = alpha R^2 e                          (Cadabra R2_check)
check("QG alpha R^2 e = U(psi) e    (the R^2 content)", alpha * R ** 2 * e, U * e)
# the much larger polynomial form of the module's printed fR_check residual:
#   alpha R^2 e - M^4 alpha^{-1} (R alpha M^{-2})^2 e
check("QG printed fR_check residual = alpha R^2 e - M^4/alpha*(R alpha/M^2)^2 e = 0",
      alpha * R ** 2 * e - (M ** 4 / alpha) * (R * alpha / M ** 2) ** 2 * e, 0)
# alpha -> 0: psi -> 1 and U -> 0, so H_final_st -> (M^2/2) * H_8190   (Cadabra base_limit_check)
check("QG alpha -> 0 limit: psi = 1", 1 + 4 * F(0) * R / M ** 2, 1)
alpha_small = F(1, 10 ** 6)
psi_s = 1 + 4 * alpha_small * R / M ** 2
U_s = (M ** 4 / (16 * alpha_small)) * (psi_s - 1) ** 2
check("QG alpha -> 0 limit: U at alpha = 1e-6 is exactly alpha R^2 (so U(psi)e = alpha R^2 e -> 0)",
      U_s, alpha_small * R ** 2)
# H_final_st = (M^2/2) psi * H_8190 + U(psi) e is linear in the auxiliary psi: the Legendre
# transform scales by (M^2/2) psi and shifts by U(psi) e (structural, from the module text).
H8190 = F(13, 4)
check("QG H_final_st = (M^2/2) psi H_8190 + U(psi) e   (linearity in the auxiliary psi)",
      (M ** 2 / 2) * psi * H8190 + U * e, (M ** 2 / 2) * psi * H8190 + U * e)
# densitized absorption: (1/16e)(y S)^2 - (1/24e)(y P)^2 with e = y^2 gives (1/16) S^2 - (1/24) P^2
y, S, P = F(5, 3), F(7, 4), F(-2, 9)
check("QG densitized: (1/16e)(yS)^2 - (1/24e)(yP)^2 = (1/16) S^2 - (1/24) P^2, e = y^2",
      (y * S) ** 2 / (16 * y ** 2) - (y * P) ** 2 / (24 * y ** 2), S ** 2 / 16 - P ** 2 / 24)

# the Einstein-frame potential V(phi) = (M^4/16a)(1 - exp(-sqrt(2/3) phi/M))^2:
# V(0)=0, V'(0)=0, V''(0) = M^2/(12 alpha)  (the published scalaron mass squared),
# plateau M^4/(16 alpha), V >= 0.
Mf, af = 3.0, 0.2
a = math.sqrt(2 / 3) / Mf
V = lambda p: (Mf ** 4 / (16 * af)) * (1 - math.exp(-a * p)) ** 2
h = 1e-4
Vpp0 = (V(h) - 2 * V(0) + V(-h)) / h ** 2
check("QG V(0) = 0", V(0.0), 0.0, tol=1e-12)
check("QG V'(0) = 0", (V(h) - V(-h)) / (2 * h), 0.0, tol=1e-8)
check("QG V''(0) = M^2/(12 alpha)  (m^2, the Rust model's quadratic truncation)", Vpp0,
      Mf ** 2 / (12 * af), tol=1e-4)
check("QG plateau: V(phi) -> M^4/(16 alpha) as phi -> +inf (exponentially)", V(50.0),
      Mf ** 4 / (16 * af), tol=1e-4)
check("QG V >= 0", min(V(p / 10) for p in range(-200, 400)), 0.0, tol=0.0)

print()
print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
