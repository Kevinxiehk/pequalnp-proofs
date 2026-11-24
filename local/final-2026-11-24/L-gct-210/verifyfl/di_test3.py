import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""(1) symmetrised normal form for m = e_1 - e_2 (identities); (2) new exact (4,1) example of a third kind; (3) Lagrangian lemmas."""
import numpy as np, itertools
from core import *
from di_core import *
rng = np.random.default_rng(5); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
dot = lambda a, b: np.sum(a * b)
def Efun(d):   # E(d)_i = e_2(d without d_i)
    return np.array([sum(d[a] * d[b] for a, b in itertools.combinations([k for k in range(4) if k != i], 2)) for i in range(4)])
def pm(*cols): return perm(np.array(cols).T)
mx = {}
def rec(n, x, sc=1.0): mx[n] = max(mx.get(n, 0), abs(x) / max(1, abs(sc)))
for _ in range(30):
    u = cn(4); u -= u.mean(); d = cn(4); y = [cn(4) for _ in range(3)]; y = [a - a.mean() for a in y]
    Y = np.array([u + d, u - d] + y).T; C = Cvec(Y); one = np.ones(4)
    # (S1) C_1 + C_2 = 2 perm(J + [u,y3,y4,y5]) ; C_2 - C_1 = 2 perm[d, 1+y3, 1+y4, 1+y5]
    rec('S1 sum', C[0] + C[1] - 2 * pm(1 + u, 1 + y[0], 1 + y[1], 1 + y[2]), C[0]); rec('S1 diff', C[1] - C[0] - 2 * pm(d, 1 + y[0], 1 + y[1], 1 + y[2]), C[0])
    # (S2) C_j = perm(J + [u,u,y_k,y_l]) - perm[d,d,1+y_k,1+y_l]
    for j, (k, l) in zip((2, 3, 4), ((1, 2), (0, 2), (0, 1))):
        rec('S2', C[j] - (pm(1 + u, 1 + u, 1 + y[k], 1 + y[l]) - pm(d, d, 1 + y[k], 1 + y[l])), C[j])
        # degree parts of perm[d,d,1+a,1+b]: 4 e2(d) ; 2<a+b,E(d)> ; perm[d,d,a,b]
        a, b = y[k], y[l]; e2 = (d.sum() ** 2 - dot(d, d)) / 2
        rec('S3', pm(d, d, 1 + a, 1 + b) - (4 * e2 + 2 * dot(a + b, Efun(d)) + pm(d, d, a, b)), pm(d, d, a, b))
    rec('E formula', np.abs(Efun(d) - ((d.sum() ** 2 - dot(d, d)) / 2 - d * d.sum() + d * d)).max())
    P = sum(4 * y[0][i] * y[0][j] * d[k] * d[l] for (i, j) in itertools.combinations(range(4), 2) for (k, l) in [tuple(x for x in range(4) if x not in (i, j))])
    rec('perm[d,d,a,a]', pm(d, d, y[0], y[0]) - P, P)
for k, v in mx.items(): print(f'  {k:16s} {v:.1e}')
# (2) third-kind (4,1) example: m = e_0 - e_3, zeta Lagrangian = span(uh, z1), neutral columns ubar on columns 1, 4
w = w3; uh = np.array([1, w, 0, w ** 2]); ub = np.array([1, w ** 2, 0, w]); z1 = np.array([1, 1, -1, 1]) / 2; e = np.eye(5)
B = np.array([np.outer(uh, e[0] - e[3]), np.outer(z1, e[0] - e[3]), np.outer(ub, e[1]), np.outer(ub, e[4])])
ed, Cb, lev, sv = defect(B); print('third-kind example: dim', rank(B), 'e =', ed, 'level err %.1e' % lev, 'defect sv', np.round(sv[:3], 12), 'm =', np.round(Cb[0] / Cb[0][0], 6))
L0, _ = kernel_of(B, lambda Y: Y.sum(0)); print('   ker kappa: dim', len(L0), 'strong-level err %.2e (NOT strongly level => conjecture "kappa != 0 => ker kappa strongly level" is false)' % sl_check(L0))
# 5x5 space L(L') = L' (+) e_5 (x) {1,m}^perp : 7-dim level
Wb = [np.array([1, 0, -2, 0, 1.]) * 0 + v for v in (np.array([1, -2, 0, 1, 0.]), np.array([0, 1, 0, 0, -1.]), np.array([0, 1, -1, 0, 0.]))]
L5 = [np.vstack([b, np.zeros(5)]) for b in B] + [np.vstack([np.zeros((4, 5)), v[None]]) for v in Wb]
print('   5x5 space: dim', rank(np.array(L5)), 'level err %.1e' % level_check(np.array(L5)))
# (3) Lagrangian lemmas: zeta = span(z0, z1'), z0 isotropic in V, tau(z1') = 1, <z0,z1'> = 0, <z1',z1'> = 1
def lagr():
    while True:
        t = cn(1)[0]; z0 = chi(1) + t * chi(2) - t * t / 2 * chi(3)
        # z1 = 1/4 + a z0 + b x + c y with basis of V ; solve <z0,z1>=0, <z1,z1>=1
        Mb = np.array([z0, np.cross(z0[:3], cn(3)).tolist() + [0], cn(4)]); Mb[1] -= Mb[1].mean(); Mb[2] -= Mb[2].mean()
        # pick v in z0^perp cap V not prop to z0 : solve <v,z0> = 0
        A = np.array([np.ones(4), z0]); u_, s_, vh = np.linalg.svd(A); ns = vh[2:].conj().T   # (4,2) null space of [1; z0] (bilinear!)
        ns = np.linalg.svd(np.array([np.ones(4), z0]))[2][2:].conj().T
        # bilinear orthogonality: need vectors v with sum v = 0 and sum v*z0 = 0: null space of rows [1], [z0] under plain (non-conjugate) product
        ns = np.linalg.svd(np.array([np.ones(4), z0]).conj())[2][2:].conj().T
        v = ns @ cn(2)
        if abs(dot(v, v)) < 1e-6: continue
        v = v * np.sqrt(0.75 / dot(v, v)); z1 = 0.25 + v           # <z1,z1> = 1/4 + 3/4 = 1, tau = 1, <z0,z1> = 0
        return z0, z1
mind = 1e9; minchi = 1e9
for _ in range(2000):
    z0, z1 = lagr()
    assert abs(dot(z0, z0)) < 1e-9 and abs(dot(z0, z1)) < 1e-9 and abs(z1.sum() ** 2 - dot(z1, z1)) < 1e-9
    Ez = [z0 * z0, z0 * z1 - z0 / 2, z1 * z1 - z1]
    s = np.linalg.svd(np.array(Ez), compute_uv=False); mind = min(mind, s[1] / s[0])
    for row_perm in itertools.permutations(range(4)):
        c1 = chi(1)[list(row_perm)]; minchi = min(minchi, max(abs(dot(c1, x)) for x in Ez) / max(np.linalg.norm(x) for x in Ez))
print('Lagrangian lemma: min over 2000 random Lagrangians of sv_2/sv_1 of E_zeta: %.3f (dim E_zeta >= 2);  min max|<chi_1-type, E_zeta>|: %.3f (never orthogonal)' % (mind, minchi))
