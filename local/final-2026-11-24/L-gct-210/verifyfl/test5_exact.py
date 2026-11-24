import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""EXACT checks: identities evaluated at random Gaussian-integer / dyadic points with exact arithmetic
(Python Fractions for real and imaginary parts). Every difference must be exactly 0."""
import itertools, random
from fractions import Fraction as Fr
random.seed(2026)
class G:
    __slots__ = ('a', 'b')
    def __init__(s, a=0, b=0): s.a, s.b = Fr(a), Fr(b)
    def __add__(s, o): o = o if isinstance(o, G) else G(o); return G(s.a + o.a, s.b + o.b)
    __radd__ = __add__
    def __neg__(s): return G(-s.a, -s.b)
    def __sub__(s, o): return s + (-(o if isinstance(o, G) else G(o)))
    def __rsub__(s, o): return (-s) + o
    def __mul__(s, o): o = o if isinstance(o, G) else G(o); return G(s.a * o.a - s.b * o.b, s.a * o.b + s.b * o.a)
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = o if isinstance(o, G) else G(o); n = o.a * o.a + o.b * o.b; return s * G(o.a / n, -o.b / n)
    def __pow__(s, k):
        r = G(1)
        for _ in range(k): r = r * s
        return r
    def iszero(s): return s.a == 0 and s.b == 0
I = G(0, 1)
rg = lambda: G(random.randint(-4, 4), random.randint(-4, 4))
rgq = lambda: G(Fr(random.randint(-6, 6), random.choice([1, 2, 3])), Fr(random.randint(-6, 6), random.choice([1, 2, 5])))
def vec(f): return [f(k) for k in range(4)]
had = lambda *vs: [prod(x) for x in zip(*vs)]
def prod(xs):
    r = G(1)
    for x in xs: r = r * x
    return r
tau = lambda x: sum(x, G(0))
dot = lambda a, b: tau(had(a, b))
add = lambda *vs: [sum(x, G(0)) for x in zip(*vs)]
sc = lambda c, v: [c * x for x in v]
chi = lambda a: [I ** ((a * k) % 4) for k in range(4)]
def br(y1, y2, y3, y4): return -6 * tau(had(y1, y2, y3, y4)) + dot(y1, y2) * dot(y3, y4) + dot(y1, y3) * dot(y2, y4) + dot(y1, y4) * dot(y2, y3)
def perm(A):
    n = len(A); return sum((prod([A[i][p[i]] for i in range(n)]) for p in itertools.permutations(range(n))), G(0))
def V4():
    x = [rg() for _ in range(3)]; return x + [-(x[0] + x[1] + x[2])]
v = lambda t: add(chi(1), sc(t, chi(2)), sc(-(t * t) / 2, chi(3)))
bad = []
def chk(name, x):
    if not x.iszero(): bad.append(name)
for trial in range(6):
    # ID1: Laplace expansion along the last row, 5x5
    A = [[rg() for _ in range(5)] for _ in range(5)]
    chk('ID1', perm(A) - sum((A[4][j] * perm([[A[i][c] for c in range(5) if c != j] for i in range(4)]) for j in range(5)), G(0)))
    # ID2: perm(J_4 + cZ), Z with columns in V, c arbitrary
    z = [V4() for _ in range(4)]; c = rgq()
    M = [[1 + c * z[a][i] for a in range(4)] for i in range(4)]
    f2 = sum((dot(z[a], z[b]) for a, b in itertools.combinations(range(4), 2)), G(0))
    f3 = sum((tau(had(z[a], z[b], z[d])) for a, b, d in itertools.combinations(range(4), 3)), G(0))
    chk('ID2', perm(M) - (24 - 2 * c * c * f2 + 2 * c ** 3 * f3 + c ** 4 * br(*z)))
    # ID3
    x = [rgq() for _ in range(4)]; x.append(-sum(x, G(0))); p2 = sum((t * t for t in x), G(0)); p3 = sum((t ** 3 for t in x), G(0))
    for m in range(5):
        o = [x[a] for a in range(5) if a != m]; e3 = sum((prod(tr) for tr in itertools.combinations(o, 3)), G(0))
        chk('ID3', e3 - (p3 / 3 + x[m] * p2 / 2 - x[m] ** 3))
    # ID6 / ID7
    t, u = rgq(), rgq(); a, b = t + u, t * u
    chk('iso', dot(v(t), v(t))); chk('dot', dot(v(t), v(u)) + 2 * (t - u) ** 2)
    sq = add(sc(-(t ** 3), chi(1)), sc(1 + t ** 4 / 4, chi(2)), sc(2 * t, chi(3)))
    for k in range(4): chk('sq', had(v(t), v(t))[k] - sq[k])
    chk('cube', tau(had(v(t), v(t), v(t))) - 3 * t * (4 + t ** 4))
    E = lambda t, u: 2 * u + t + t * u ** 4 / 4 + t * t * u ** 3 / 2
    chk('mixed', tau(had(v(t), v(u), v(u))) - 4 * E(t, u))
    chk('Esum', E(t, u) + E(u, t) - a / 4 * (12 + a * a * b - b * b)); chk('Ediff', E(t, u) - E(u, t) - (u - t) / 4 * (4 + a * a * b + b * b))
    chk('br22', br(v(t), v(t), v(u), v(u)) - (2 * (a * a + 2 * b) ** 2 - Fr(3, 2) * (b * b - 4) ** 2))
    for k in range(4):
        ik = I ** k; ikinv = I ** ((4 - k) % 4)
        chk('zero', v(t)[k] + (I ** (3 * k % 4)) / 2 * (t * t - 2 * ikinv * t - 2 * ikinv * ikinv))
    chk('br31', br(v(t), v(u), v(u), v(u)) + 6 * tau(had(v(t), v(u), v(u), v(u)))); chk('br4', br(v(t), v(t), v(t), v(t)) + 6 * tau(had(*[v(t)] * 4)))
    # type IV: Psi, G, and raw T_m on N for the (1^5) kernel
    th = [rgq() for _ in range(5)]
    if len({(x.a, x.b) for x in th}) == 5:
        al, be = rgq(), rgq(); om = [prod([th[m] - th[q] for q in range(5) if q != m]) for m in range(5)]
        l = [(al + be * th[m]) / om[m] for m in range(5)]; y = [sc(l[m], v(th[m])) for m in range(5)]
        for k in range(4): chk('IVker', sum((y[m][k] for m in range(5)), G(0)))
        A_ = sum((l[m] ** 2 * (1 + th[m] ** 4 / 4) for m in range(5)), G(0)); B_ = sum((l[m] ** 2 * th[m] for m in range(5)), G(0)); C_ = sum((l[m] ** 2 * th[m] ** 3 for m in range(5)), G(0))
        P3 = sum((tau(had(y[m], y[m], y[m])) for m in range(5)), G(0))
        for m in range(5):
            Tm = sum((tau(had(y[p], y[q], y[r])) for p, q, r in itertools.combinations([q for q in range(5) if q != m], 3)), G(0))
            Gm = 4 * B_ + 2 * th[m] * A_ + th[m] ** 2 * C_
            chk('IV.T', Tm - (P3 / 3 + l[m] * Gm - l[m] ** 3 * 3 * th[m] * (4 + th[m] ** 4)))
    # ID8
    p = [rgq() for _ in range(4)]; r = [rgq() for _ in range(4)]; ys = [add(sc(p[i], chi(1)), sc(r[i], chi(3))) for i in range(4)]
    cl = -24 * (prod(p) + prod(r)) + 8 * sum((p[i] * p[j] * prod([r[k] for k in range(4) if k not in (i, j)]) for i, j in itertools.combinations(range(4), 2)), G(0))
    chk('ID8', br(*ys) - cl)
    # G23 expansions (general isotropic v(t), v(u))
    mu = rgq(); nu = [rgq(), rgq()]; nu.append(-(nu[0] + nu[1])); x, z = v(t), v(u)
    cols = [sc(mu, x), sc(-mu, x)] + [sc(n_, z) for n_ in nu]
    T = lambda m: sum((tau(had(cols[p_], cols[q_], cols[r_])) for p_, q_, r_ in itertools.combinations([q for q in range(5) if q != m], 3)), G(0))
    D = lambda m: br(*[cols[q] for q in range(5) if q != m])
    chk('G23a', T(0) + T(1) - 2 * tau(had(z, z, z)) * prod(nu)); chk('G23b', D(0) - 6 * mu * prod(nu) * tau(had(x, z, z, z)))
    chk('G23c', D(2) + mu * mu * nu[1] * nu[2] * br(x, x, z, z)); chk('G23d', T(2) - mu * mu * nu[0] * tau(had(x, x, z)))
chk('ID5', br(chi(3), chi(3), chi(1), chi(1)) - 8)
for a in range(8):
    for b in range(8): chk('chi', dot(chi(a), chi(b)) - (4 if (a + b) % 4 == 0 else 0))
print('exact checks failing:', sorted(set(bad)) if bad else 'NONE (all differences are exactly 0)')
