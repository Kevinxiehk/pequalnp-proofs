import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""EXHAUSTIVE enumeration for the sub-branch (R') of DI5.3 (instead of random LM):
   1. all pairs of distinct isotropic lines v = v(t), v' = v(u) with tau(v^2 v') = 0 and [v,v,v',v'] = 0;
   2. for each pair, all z with tau(z) = 1, Q(z) = 0 and E(z) in C n (n = the vector of V orthogonal to v, v'): w = z - 1/2 solves
      w_i^2 = 1/4 + lam n_i, sum w = -1  (square system, Bezout 16);
   3. for each (pair, z): the <= 2 isotropic lines z_0 in V with <z_0, z> = 0; test E(z,z_0) = z_0 o (z - 1/2) parallel to n."""
import numpy as np, itertools
from core import *
rng = np.random.default_rng(12); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
dot = lambda a, b: np.sum(a * b); v = lambda t: chi(1) + t * chi(2) - t * t / 2 * chi(3)
def newton(F, X, n, it=80):
    for _ in range(it):
        r = F(X); J = np.empty((len(r), n), complex)
        for i in range(n):
            Xp = X.copy(); Xp[i] += 1e-7; J[:, i] = (F(Xp) - r) / 1e-7
        try: X = X - np.linalg.solve(J, r)
        except np.linalg.LinAlgError: return None
        if not np.all(np.isfinite(X)) or np.abs(X).max() > 1e6: return None
    return X if np.abs(F(X)).max() < 1e-10 else None
def all_solutions(F, n, starts, scale=2.0):
    sols = []
    for _ in range(starts):
        X = newton(F, cn(n) * rng.choice([0.5, 1, scale, 4]), n)
        if X is not None and not any(np.abs(X - s).max() < 1e-6 for s in sols): sols.append(X)
    return sols
# step 1
def F1(X):
    t, u = X; a, b = t + u, t * u
    return np.array([2 * t + u + u * t ** 4 / 4 + u * u * t ** 3 / 2, 2 * (a * a + 2 * b) ** 2 - 1.5 * (b * b - 4) ** 2])
pairs = [X for X in all_solutions(F1, 2, 3000) if abs(X[0] - X[1]) > 1e-6]
print('step 1: %d pairs (t,u), t != u, with tau(v^2 v\') = 0 and [v,v,v\',v\'] = 0' % len(pairs))
tot_z = 0; survivors = 0; minang = 1e9
for (t, u) in pairs:
    x, xp = v(t), v(u)
    # n: in V, orthogonal to x, xp
    M = np.array([np.ones(4), x, xp]); n = np.linalg.svd(M)[2][3].conj(); n = n / np.sqrt(dot(n, n))
    assert abs(n.sum()) < 1e-9 and abs(dot(n, x)) < 1e-9 and abs(dot(n, xp)) < 1e-9
    zero_row = [k for k in range(4) if abs(x[k]) < 1e-7 and abs(xp[k]) < 1e-7]
    def F2(X):
        w, lam = X[:4], X[4]; return np.concatenate([w * w - 0.25 - lam * n, [w.sum() + 1]])
    zs = all_solutions(F2, 5, 400)
    nz = 0
    for X in zs:
        w, lam = X[:4], X[4]; z = w + 0.5; nz += 1
        # isotropic z0 in V with <z0, w> = 0 : quadratic in theta, plus chi_3
        c1, c2, c3 = dot(chi(1), w), dot(chi(2), w), dot(chi(3), w)          # <v(th),w> = c1 + th c2 - th^2/2 c3
        cands = [chi(3) + 0j] if abs(c3) < 1e-9 else []
        cands += [v(th) for th in np.roots([-c3 / 2, c2, c1])] if abs(c3) > 1e-12 else ([v(-c1 / c2)] if abs(c2) > 1e-12 else [])
        for z0 in cands:
            if abs(dot(z0, w)) > 1e-7 * (1 + np.linalg.norm(z0)): continue
            E10 = z0 * w; nrm = np.linalg.norm(E10)
            ang = np.linalg.norm(E10 - dot(E10, n) * n) / max(nrm, 1e-30)   # 0 iff parallel to n (n normalised bilinearly)
            if nrm < 1e-7:
                kind = 'E(z,z0) = 0 (M_2 shape; excluded by hand)'
            else:
                minang = min(minang, ang); kind = 'E(z,z0) != 0, deviation from C n: %.3f' % ang
                survivors += ang < 1e-6
    tot_z += nz
    print('  pair t=%s u=%s zero row %s: %d solutions z of step 2' % (np.round(t, 3), np.round(u, 3), zero_row, nz))
print('step 2 total z: %d ; step 3: configurations with E(z,z0) != 0 parallel to n: %d ; smallest deviation %.3f' % (tot_z, survivors, minang))
