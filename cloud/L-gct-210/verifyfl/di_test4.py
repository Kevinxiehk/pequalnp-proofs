import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""numerical check of the closed forms used in DI5.3 (P3), (P4)."""
import numpy as np, itertools
from core import *
rng = np.random.default_rng(9); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
dot = lambda a, b: np.sum(a * b); v = lambda t: chi(1) + t * chi(2) - t * t / 2 * chi(3)
def T(cols): return sum(tau(cols[a] * cols[b] * cols[c]) for a, b, c in itertools.combinations(range(len(cols)), 3))
mx = {}
def rec(n, x, sc=1.0): mx[n] = max(mx.get(n, 0), abs(x) / max(1, abs(sc)))
w = w3
for _ in range(20):
    th = cn(3); l = cn(3); vs = [v(x) for x in th]; z = [l[j] * vs[j] for j in range(3)]; u = -(z[0] + z[1] + z[2]) / 2
    g = lambda j, k: dot(vs[j], vs[k])
    # (P3) first identity: Tbar_1 = -(1/2)[sum_{j!=k} l_j^2 l_k tau(v_j^2 v_k) + l3 l4 l5 tau(v3 v4 v5)]
    A = sum(l[j] ** 2 * l[k] * tau(vs[j] ** 2 * vs[k]) for j in range(3) for k in range(3) if j != k) + np.prod(l) * tau(vs[0] * vs[1] * vs[2])
    rec('P3 Tbar_1', T([u] + z) + A / 2, A)
    Bq = np.prod(l) * sum(l[j] * (3 * tau(vs[j] ** 2 * vs[(j + 1) % 3] * vs[(j + 2) % 3]) - g(j, (j + 1) % 3) * g(j, (j + 2) % 3)) for j in range(3))
    rec('P3 bracket', perm_cols(u, *z) - Bq, Bq)
    # (c2) formulas: lines (v,v,v')
    x, xp = v(th[0]), v(th[1]); l3, l4, b = cn(3); a = l3 + l4; u = -(a * x + b * xp) / 2; z3, z4, z5 = l3 * x, l4 * x, b * xp
    t3, t21, t12, t03 = tau(x ** 3), tau(x * x * xp), tau(x * xp * xp), tau(xp ** 3)
    rec('c2 Tbar_1', T([u, z3, z4, z5]) + (l3 * l4 * (a * t3 - b * t21) + a * b * (a * t21 + b * t12)) / 2, t3)
    rec('c2 Tbar_5', T([u, u, z3, z4]) - (a * (a * a * t3 + 2 * a * b * t21 + b * b * t12) / 4 - l3 * l4 * (a * t3 + b * t21)), t3)
    tu2v = (a * a * t3 + 2 * a * b * t21 + b * b * t12) / 4; tu2vp = (a * a * t21 + 2 * a * b * t12 + b * b * t03) / 4; tuvvp = -(a * t21 + b * t12) / 2
    rec('c2 Tbar_3', T([u, u, z4, z5]) - (l4 * tu2v + b * tu2vp + 2 * l4 * b * tuvvp), t3)
    rec('c2 Tbar_4', T([u, u, z3, z5]) - (l3 * tu2v + b * tu2vp + 2 * l3 * b * tuvvp), t3)
    # (N-b) Tbar_3 with z5 = 0 : columns u,u,z4,0 -> tau(u^2 z4)
    u2 = -(z3 + l4 * xp) / 2
    rec('Nb', T([u2, u2, l4 * xp, 0 * xp]) - tau(u2 * u2 * l4 * xp))
    # (c1) final bracket: [-t chi2, x3 chi1 + t chi2, x4 chi1 + t chi2, x5 chi1 + t chi2] = -24 t^4
    t = cn(1)[0]; xx = cn(3)
    rec('c1 bracket', perm_cols(-t * chi(2), *[xx[j] * chi(1) + t * chi(2) for j in range(3)]) + 24 * t ** 4, t ** 4)
    piu = cn(1)[0]
    rec('c1 Tbar_1', T([t * (piu * chi(1) - chi(2))] + [xx[j] * chi(1) + t * chi(2) for j in range(3)]) - 8 * t * t * piu * xx.sum(), t)
    # (c1) u-deletion bracket for n_0 = c chi_3, beta-sum = 0
    c = cn(1)[0]; be = cn(3); be -= be.mean(); x0 = cn(3); x0 -= x0.mean(); p = x0 + t * be / 2
    cols = [-(t * c / 4) * chi(3)] + [p[j] * chi(1) + t * c / 2 * chi(3) for j in range(3)]
    e2p = p[0] * p[1] + p[0] * p[2] + p[1] * p[2]
    rec('c1 chi3 bracket', perm_cols(*cols) - (-(t * c / 4)) * (-24 * (t * c / 2) ** 3 + 8 * (t * c / 2) * e2p), t ** 4)
    # all-equal-lines Tbar_1 = -(tau(v^3)/2)((l3+l4)(l4+l5)(l5+l3) - l3 l4 l5)
    zz = [l[j] * x for j in range(3)]; uu = -sum(zz) / 2
    rec('c1 cubic', T([uu] + zz) + t3 / 2 * ((l[0] + l[1]) * (l[1] + l[2]) * (l[2] + l[0]) - np.prod(l)), t3)
h = np.array([1, 1, 1, -1.]); z0 = np.array([1, w, w * w, 0])
print('perm[h,h,zeta0,conj zeta0] =', np.round(perm(np.array([h, h, z0, z0.conj()]).T), 10), ' perm[h,h,zeta0,zeta0] =', np.round(perm(np.array([h, h, z0, z0]).T), 10))
print('3 tau(chi1^2 chi3^2) - <chi1,chi3>^2 =', 3 * tau(chi(2) * chi(6)) - dot(chi(1), chi(3)) ** 2, '; zero-row pair: tau(v^2 v\') = %.1e, 3 tau(v^2 v\'^2) - g^2 = %.1e' % (abs(tau(z0 * z0 * z0.conj())), abs(3 * tau(z0 ** 2 * z0.conj() ** 2) - dot(z0, z0.conj()) ** 2)))
for k, e in mx.items(): print(f'  {k:16s} {e:.1e}')
