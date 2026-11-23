import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""residual configuration (R), c = 0, D_N Lagrangian, tau(z) = 1: necessary conditions e1..e14 in 5 unknowns
   (theta_v, theta_v', theta_0, alpha, B = b_0^2); z_0 = v(theta_0), z = z_1 = 1/4 + sgn*(sqrt3/4)(chi_2 - theta_0 chi_3) + alpha z_0."""
import numpy as np, itertools, time
from core import *
dot = lambda a, b: np.sum(a * b); v = lambda t: chi(1) + t * chi(2) - t * t / 2 * chi(3)
def pm(*cols): return perm(np.array(cols).T)
def eqs(X, sgn, which=None):
    tv, tw, t0, al, B = X; x, xp, z0 = v(tv), v(tw), v(t0)
    z1 = 0.25 + sgn * np.sqrt(3) / 4 * (chi(2) - t0 * chi(3)) + al * z0
    E1 = z1 * z1 - z1; E10 = z0 * (z1 - 0.5)
    e = [tau(x * x * xp), 3 * tau(x * x * xp * xp) - dot(x, xp) ** 2, dot(x, E10), dot(xp, E10), dot(x, E1), dot(xp, E1),
         dot(x, z0 * z0) + 0.75 * tau(x * xp * xp) * B, dot(xp, z0 * z0) - tau(xp ** 3) / 4 * B,
         pm(z1, z1, x, x), pm(z1, z1, x, xp), pm(z0, z1, x, x), pm(z0, z1, x, xp), pm(z0, z0, x, x), pm(z0, z0, x, xp) + 1.5 * B * tau(x * xp ** 3)]
    e = np.array(e)
    return e if which is None else e[which]
def solve(sgn, which, starts, seed, n_unk=5, tmax=60):
    rng = np.random.default_rng(seed); sols = []; best = 1e9; t0 = time.time(); nconv = 0
    for st in range(starts):
        if time.time() - t0 > tmax: break
        X = (rng.normal(size=5) + 1j * rng.normal(size=5)) * rng.choice([0.5, 1.5, 3.0]); lam = 1e-2
        r = eqs(X, sgn, which); f = np.vdot(r, r).real
        for it in range(200):
            J = np.empty((len(r), 5), complex)
            for i in range(5):
                Xp = X.copy(); Xp[i] += 1e-7; J[:, i] = (eqs(Xp, sgn, which) - r) / 1e-7
            g = J.conj().T @ r; H = J.conj().T @ J
            for _ in range(12):
                try: d = np.linalg.solve(H + lam * np.diag(np.diag(H).real + 1e-12), -g)
                except np.linalg.LinAlgError: lam *= 5; continue
                rn = eqs(X + d, sgn, which); fn = np.vdot(rn, rn).real
                if np.isfinite(fn) and fn < f: X, r, f, lam = X + d, rn, fn, max(lam / 5, 1e-12); break
                lam *= 5
            else: break
            if f < 1e-24: break
        res = np.sqrt(f)
        nondeg = abs(X[0] - X[1]) > 1e-4 and abs(X[4]) > 1e-4 and np.abs(X).max() < 1e4
        if res < 1e-9:
            nconv += 1
            if nondeg and not any(np.abs(X - s).max() < 1e-5 for s in sols): sols.append(X)
        elif nondeg: best = min(best, res)
    return sols, nconv, st + 1, best
if __name__ == '__main__':
    full = None
    for sgn in (1, -1):
        s, nc, n, best = solve(sgn, full, 1500, 11 + sgn, tmax=55)
        print('FULL system e1..e14, sign %+d: %d starts, %d converged to ANY zero, %d NONDEGENERATE solutions (v != v\', B != 0); best nondegenerate residual %.2e' % (sgn, n, nc, len(s), best))
        for X in s[:5]: print('    ', np.round(X, 4))
    # calibration: square subsystems must be solvable by the same solver
    for nm, which in (('e1,e2,e3,e4,e7', [0, 1, 2, 3, 6]), ('e1,e2,e5,e6,e8', [0, 1, 4, 5, 7]), ('e1,e3,e4,e9,e13', [0, 2, 3, 8, 12]), ('e1..e6 (6 eqs)', [0, 1, 2, 3, 4, 5])):
        s, nc, n, best = solve(1, which, 150, 5, tmax=20)
        print('calibration subsystem %-18s: %d starts, %d nondegenerate solutions' % (nm, n, len(s)))
