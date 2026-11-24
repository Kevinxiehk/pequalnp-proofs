import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""defect-constrained searches: spaces L' of 4x5 matrices with C(Y) - 24*1 in C m for a FIXED m (sum m = 0).
   ext(F, m): all one-vector extensions of a fixed space F (LM from random starts)."""
import numpy as np, time
from core import *
from di_core import *
def mperp(m):
    """orthonormal rows spanning the complement of m in C^5 w.r.t. the bilinear pairing: w with w.m = 0"""
    u, s, vh = np.linalg.svd(np.array([m], complex)); return vh[1:].conj()       # rows w: sum_j w_j m_j = 0
def res_m(Y, W):
    return ((Cvec(Y) - 24) @ W.T).ravel()
def ambient_m(m):
    """orthonormal basis of 4x5 matrices whose column-sum vector is in C m"""
    E = np.eye(20).reshape(20, 4, 5); cons = np.array([b.sum(0) @ mperp(m).T for b in E])     # (20,4): must vanish
    u, s, vh = np.linalg.svd(cons.T); r = int(np.sum(s > 1e-10)); K = vh[r:].conj().T
    return onb(np.einsum('ik,iab->kab', K, E))
def ext(F, m, starts, seed, tmax=60, tol=1e-9):
    F = np.asarray(F, complex); k0 = len(F); A = ambient_m(m); W = mperp(m)
    C = np.einsum('kab,dab->kd', F, A.conj()); u, s, vh = np.linalg.svd(C); Ac = np.einsum('jd,dab->jab', vh[k0:], A); n = len(Ac)
    rng = np.random.default_rng(seed); sols = []; t0 = time.time(); st = 0
    for st in range(starts):
        if time.time() - t0 > tmax: break
        c = rng.normal(size=(45, k0 + 1)) + 1j * rng.normal(size=(45, k0 + 1)); c /= np.linalg.norm(c, axis=1, keepdims=True)
        a = rng.normal(size=n) + 1j * rng.normal(size=n); a /= np.linalg.norm(a)
        def r(X):
            Y = np.einsum('j,jab->ab', X, Ac); B = np.concatenate([F, Y[None]])
            return np.concatenate([res_m(np.einsum('nk,kab->nab', c, B), W), [3 * (a @ X - 1)]])
        X = rng.normal(size=n) + 1j * rng.normal(size=n); lam = 1e-2; rr = r(X); f = np.vdot(rr, rr).real; h = 1e-7
        for it in range(400):
            J = np.empty((len(rr), n), complex)
            for i in range(n):
                Xp = X.copy(); Xp[i] += h; J[:, i] = (r(Xp) - rr) / h
            g = J.conj().T @ rr; H = J.conj().T @ J
            for _ in range(12):
                d = np.linalg.solve(H + lam * np.diag(np.diag(H).real + 1e-12), -g); rn = r(X + d); fn = np.vdot(rn, rn).real
                if fn < f: X, rr, f, lam = X + d, rn, fn, max(lam / 5, 1e-12); break
                lam *= 5
            else: break
            if f < 1e-26: break
        if np.sqrt(f) < tol:
            Y = np.einsum('j,jab->ab', X, Ac); sols.append(Y / np.linalg.norm(Y))
    return sols, st + 1
def chk_m(B, m, trials=80, seed=4):
    B = np.asarray(B, complex); rng = np.random.default_rng(seed); c = rng.normal(size=(trials, len(B))) + 1j * rng.normal(size=(trials, len(B)))
    return np.abs(res_m(np.einsum('nk,kab->nab', c, B), mperp(m))).max()
if __name__ == '__main__':
    w = w3; e = np.eye(5); m = e[0] - e[1]
    z0 = np.array([1, w, w * w, 0]); zb = z0.conj(); h = np.array([1, 1, 1, -1.])
    # candidate N' of case (N-b, zero row): type II plane on column pairs (2,1),(3,0) plus h (e_0 - e_1)^T   [columns 0,1 non-neutral]
    Nc = np.array([np.outer(z0, e[2] - e[1]), np.outer(zb, e[3] - e[0]), np.outer(h, e[0] - e[1])])
    print('candidate N\' = type II plane (+) h(e_0-e_1)^T: defect-in-Cm residual %.2e ; plane alone %.1e ; h-line alone %.1e' % (chk_m(Nc, m), chk_m(Nc[:2], m), chk_m(Nc[2:], m)))
    for t in (0.5, 1.0, 2.0):
        Nt = Nc.copy(); Nt[2] = np.outer(h, e[0] - e[1]) * t
    # which z make (type II plane) (+) z(e_0-e_1)^T valid? search
    sols, n = ext(Nc[:2], m, 14, 1, tmax=40); print('extensions of the type II plane within defect line C(e_0-e_1): %d/%d' % (len(sols), n))
    for Y in sols[:6]:
        print('   kappa=%.3f  row sums %s  cols: %s' % (abs(Y[:, 0].sum()), np.round(Y.sum(1), 3), ' | '.join(str(np.round(Y[:, j] / (np.abs(Y[:, j]).max() + 1e-30), 2)) for j in range(5))))
