import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""The 'N-problem' of the principal stratum: 2-dim spaces N of 4x5 matrices supported on the columns of P = supp m, with ZERO ROW SUMS,
   column sums in C m, level with defect in C m, kappa not identically 0, and (normal form) <y_j^0,y_j^0> = (3/4) kappa^2 m_j^2 for j in P.
   LM on Gr(2, D), D = 3|P| - 2.  |P| = 3: exists iff m isotropic (Theorem PR3) -> calibration."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import mperp, res_m
def amb(m):
    P = [j for j in range(5) if abs(m[j]) > 1e-9]; E = []
    for i in range(4):
        for j in P:
            b = np.zeros((4, 5), complex); b[i, j] = 1; E.append(b)
    E = np.array(E); W = mperp(m)
    cons = np.array([np.concatenate([b.sum(1), b.sum(0) @ W.T]) for b in E])
    u, s, vh = np.linalg.svd(cons.T); r = int(np.sum(s > 1e-10)); K = vh[r:].conj().T
    return onb(np.einsum('ik,iab->kab', K, E)), P
def nf_res(Y, m, P):
    out = []
    for j in P:
        kap = Y[..., :, j].sum(-1) / m[j]; y0 = Y[..., :, j] - (kap * m[j] / 4)[..., None]
        out.append((y0 * y0).sum(-1) - 0.75 * kap ** 2 * m[j] ** 2)
    return np.array(out).T.ravel()
def search(m, starts, seed, tmax, nf=True, k=2):
    A, P = amb(m); D = len(A); W = mperp(m); hits = []; t0 = time.time(); st = 0
    for st in range(starts):
        if time.time() - t0 > tmax: break
        rng = np.random.default_rng(seed + 31 * st); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
        U, _ = np.linalg.qr(cn(D, D)); c = cn(14, k); c /= np.linalg.norm(c, axis=1, keepdims=True)
        def basis(X): return np.einsum('kd,dab->kab', np.concatenate([np.eye(k), X.reshape(k, D - k)], 1) @ U, A)
        def r(X):
            Y = np.einsum('nk,kab->nab', c, basis(X)); a = res_m(Y, W)
            return np.concatenate([a, nf_res(Y, m, P)]) if nf else a
        X = cn(k * (D - k)) * (0.6 if st % 2 else 1.3); lam = 1e-2; rr = r(X); f = np.vdot(rr, rr).real; n = len(X)
        for it in range(300):
            J = np.empty((len(rr), n), complex)
            for i in range(n):
                Xp = X.copy(); Xp[i] += 1e-7; J[:, i] = (r(Xp) - rr) / 1e-7
            g = J.conj().T @ rr; Hm = J.conj().T @ J
            for _ in range(12):
                d = np.linalg.solve(Hm + lam * np.diag(np.diag(Hm).real + 1e-12), -g); rn = r(X + d); fn = np.vdot(rn, rn).real
                if fn < f: X, rr, f, lam = X + d, rn, fn, max(lam / 5, 1e-12); break
                lam *= 5
            else: break
            if f < 1e-26: break
        if np.sqrt(f) < 1e-9: hits.append(basis(X))
    return hits, st + 1, time.time() - t0
if __name__ == '__main__':
    w = w3; z5 = np.exp(2j * np.pi / 5)
    ms = {'P3 good (1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), 'P3 isotropic (1,w,w^2,0,0)': np.array([1, w, w * w, 0, 0]),
          'P4 good (1,2,-4,1,0)': np.array([1, 2, -4, 1, 0.]), 'P4 good (1,2,3,-6,0)': np.array([1, 2, 3, -6, 0.]), 'P4 isotropic (1,i,-1,-i,0)': np.array([1, 1j, -1, -1j, 0]),
          'P5 good (1,2,3,-1,-5)': np.array([1, 2, 3, -1, -5.]), 'P5 isotropic 5th roots': z5 ** np.arange(5)}
    sel = sys.argv[1].split(','); tmax = float(sys.argv[2]); nf = sys.argv[3] == 'nf'
    for i, (nm, m) in enumerate(ms.items()):
        if str(i) not in sel: continue
        hits, n, t = search(m, 400, 3 + i, tmax, nf)
        kinds = {}
        for B in hits:
            kr = rank(np.array([b.sum(0) for b in B]), 1e-7)
            sr = any(rank(np.concatenate([B, np.outer(np.eye(4)[r_], m)[None]]).reshape(3, -1), 1e-6) == 2 for r_ in range(4))
            sl = sl_check(B, trials=20) < 1e-7
            P = [j for j in range(5) if abs(m[j]) > 1e-9]
            inj = all(rank(np.array([b[:, j] - b[:, j].mean() for b in B]), 1e-6) == 2 for j in P)
            key = 'kappa-rank %d%s%s%s' % (kr, ', contains e_i m^T' if sr else '', ', strongly level' if sl else '', ', ALL COLUMN MAPS INJECTIVE' if inj else '')
            if inj and kr == 1: np.save('r4_n2_inj_%d_%d.npy' % (i, kinds.get(key, 0)), B)
            kinds[key] = kinds.get(key, 0) + 1
        print('%-28s (%s): %d/%d converged (%.0fs): %s' % (nm, 'normal-form constraint' if nf else 'defect only', len(hits), n, t, kinds), flush=True)
