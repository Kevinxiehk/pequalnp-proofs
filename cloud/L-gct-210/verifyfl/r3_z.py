import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""(Z_k): k-dim spaces with ALL COLUMN SUMS ZERO and defect inside C m.  Are they strongly level when m is 'good'
   (not two-column, not isotropic)?  LM on Gr(k,15) (ambient = column-centred matrices), residual = part of C - 24 outside C m."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import mperp, res_m
from lm import ambient
def search(k, m, starts, seed, tmax=60):
    A = ambient('cs'); D = len(A); W = mperp(m); hits = []; t0 = time.time(); st = 0
    for st in range(starts):
        if time.time() - t0 > tmax: break
        rng = np.random.default_rng(seed + 31 * st); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
        U, _ = np.linalg.qr(cn(D, D)); ns = [0, 8, 16, 28, 44][k]; c = cn(ns, k); c /= np.linalg.norm(c, axis=1, keepdims=True)
        def basis(X): return np.einsum('kd,dab->kab', np.concatenate([np.eye(k), X.reshape(k, D - k)], 1) @ U, A)
        def r(X): return res_m(np.einsum('nk,kab->nab', c, basis(X)), W)
        X = cn(k * (D - k)) * (0.6 if st % 2 else 1.3); lam = 1e-2; rr = r(X); f = np.vdot(rr, rr).real; n = len(X)
        for it in range(250):
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
    w = w3
    ms = {'good (1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), 'good (1,1,-2,0,0)': np.array([1, 1, -2, 0, 0.]), 'two-column (1,-1,0,0,0)': np.array([1, -1, 0, 0, 0.]),
          'isotropic (1,w,w^2,0,0)': np.array([1, w, w * w, 0, 0])}
    k = int(sys.argv[1]); tmax = float(sys.argv[2])
    for nm, m in ms.items():
        hits, n, t = search(k, m, 40, 5 + k, tmax)
        sl = [sl_check(B, trials=30) for B in hits]
        print('k=%d m %-26s: %d/%d converged (%.0fs); strongly level: %d, genuinely defect 1 (err > 1e-5): %d' % (k, nm, len(hits), n, t, sum(x < 1e-7 for x in sl), sum(x > 1e-5 for x in sl)), flush=True)
