import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""EXACT checks (Gaussian rationals) of the coefficient extractions in S7 (II-b) and S8 (Steps 1-4)."""
import itertools, random
from fractions import Fraction as Fr
from test5_exact import G, I, rgq, had, prod, tau, dot, add, sc, chi, br, V4, v
random.seed(7); bad = []
def chk(name, x):
    if not x.iszero(): bad.append(name)
def T(cols, m): return sum((tau(had(cols[p], cols[q], cols[r])) for p, q, r in itertools.combinations([q for q in range(5) if q != m], 3)), G(0))
def D(cols, m): return br(*[cols[q] for q in range(5) if q != m])
def V4q():
    x = [rgq() for _ in range(3)]; return x + [-(x[0] + x[1] + x[2])]
for trial in range(5):
    # S7 (II-b): arbitrary t-parts A_m in V, arbitrary v, v' in V; column e arbitrary (it is deleted)
    A = [V4q() for _ in range(4)]; x, z = V4q(), V4q()
    def cols(t, mu, mup): return [add(sc(t, A[0]), sc(mu, x)), add(sc(t, A[1]), sc(-mu, x)), add(sc(t, A[2]), sc(mup, z)), add(sc(t, A[3]), sc(-mup, z)), V4q()]
    f = lambda t, mu, mup: T(cols(t, mu, mup), 4)
    chk('IIb mu\'^2', (f(1, 0, 1) + f(1, 0, -1)) / 2 - f(1, 0, 0) + tau(had(z, z, add(A[0], A[1]))))
    chk('IIb mu^2', (f(1, 1, 0) + f(1, -1, 0)) / 2 - f(1, 0, 0) + tau(had(x, x, add(A[2], A[3]))))
    # S8 Step 1: y_m = (x_m + t be_m/2) chi_1 + t u/2 (m in M), y_4 = t(b_4+u)/2, y_5 = t(b_5+u)/2, any u, b_4, b_5 in V
    u, b4, b5 = V4q(), V4q(), V4q(); be = [rgq() for _ in range(3)]; xs = [rgq(), rgq()]; xs.append(-(xs[0] + xs[1]))
    def colsI(t, k): return [add(sc(k * xs[m] + t * be[m] / 2, chi(1)), sc(t / 2, u)) for m in range(3)] + [sc(t / 2, add(b4, u)), sc(t / 2, add(b5, u))]
    cf = lambda m: (T(colsI(1, 1), m) + T(colsI(1, -1), m)) / 2 - T(colsI(1, 0), m)
    e2 = xs[0] * xs[1] + xs[0] * xs[2] + xs[1] * xs[2]
    chk('I.1 T4', cf(3) - e2 * (2 * dot(chi(2), u) + dot(chi(2), b5)) / 2); chk('I.1 T5', cf(4) - e2 * (2 * dot(chi(2), u) + dot(chi(2), b4)) / 2)
    chk('I.1 T1', cf(0) - xs[1] * xs[2] * (2 * dot(chi(2), u) + dot(chi(2), add(b4, b5))) / 2)
    # S8 Step 2 closed form (pi_4 = 0): bracket of deletion 5
    c, t, rho4 = rgq(), rgq(), rgq(); p = [xs[m] + t * be[m] / 2 for m in range(3)]
    cs = [add(sc(p[m], chi(1)), sc(t * c / 2, chi(3))) for m in range(3)] + [sc(t * (rho4 + c) / 2, chi(3)), V4q()]
    chk('I.2', D(cs, 4) - t * t * c * (rho4 + c) * (2 * (p[0] * p[1] + p[0] * p[2] + p[1] * p[2]) - Fr(3, 2) * t * t * c * c))
    # general pi_4: x1x2x3 t coefficient is -12 pi_4 : check full formula
    pi4 = rgq(); cs[3] = add(sc(t * pi4 / 2, chi(1)), sc(t * (rho4 + c) / 2, chi(3)))
    full = -24 * (prod(p) * t * pi4 / 2 + (t * c / 2) ** 3 * t * (rho4 + c) / 2) + 8 * ((p[0] * p[1] + p[0] * p[2] + p[1] * p[2]) * (t * c / 2) * t * (rho4 + c) / 2 + (p[0] + p[1] + p[2]) * (t * pi4 / 2) * (t * c / 2) ** 2)
    chk('I.2gen', D(cs, 4) - full)
    # S8 Step 3: r_m = 0 on M
    cs = [sc(p[m], chi(1)) for m in range(3)] + [add(sc(t * (pi4 + c) / 2, chi(1)), sc(t * rho4 / 2, chi(3))), V4q()]
    chk('I.3', D(cs, 4) + 24 * prod(p) * t * (pi4 + c) / 2)
    # S8 Step 4
    x3 = [rgq() for _ in range(3)]; pi5 = rgq()
    ca = [add(sc(x3[0], chi(1)), sc(t, chi(2))), sc(x3[1], chi(1)), sc(x3[2], chi(1)), sc(t * pi4, chi(1)), sc(t * pi5, chi(1))]
    chk('I.4a', T(ca, 3) - 4 * t * (x3[1] * x3[2] + t * pi5 * (x3[1] + x3[2])))
    cb = [sc(x3[0], chi(1)), sc(x3[1], chi(1)), sc(x3[2], chi(1)), sc(t, add(chi(2), sc(pi4, chi(1)))), sc(t * pi5, chi(1))]
    chk('I.4b', T(cb, 4) - 4 * t * (x3[0] * x3[1] + x3[0] * x3[2] + x3[1] * x3[2]))
    # type IV (2,1,1,1): mu^2 coefficient of G(x) = 4B + 2xA + x^2 C is f(x)
    th1, xx = rgq(), rgq()
    chk('IV f', 4 * (2 * th1) + 2 * xx * 2 * (1 + th1 ** 4 / 4) + xx * xx * 2 * th1 ** 3 - (2 * th1 ** 3 * xx * xx + (4 + th1 ** 4) * xx + 8 * th1))
print('exact checks failing:', sorted(set(bad)) if bad else 'NONE (all differences are exactly 0)')
