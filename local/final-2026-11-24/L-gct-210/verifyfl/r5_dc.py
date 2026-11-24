import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""Doubly centred spaces with defect in C m: LM on Gr(k,12).  k = 2 is the calibration (type V / type I' planes exist), k = 3 decides (R4)
   numerically (and type (0,4) needs k = 4)."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import mperp, res_m
from lm import ambient
def search(k, m, starts, seed, tmax):
    A = ambient('dc'); D = len(A); W = mperp(m); hits = []; t0 = time.time(); st = 0
    for st in range(starts):
        if time.time() - t0 > tmax: break
        rng = np.random.default_rng(seed + 31 * st); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
        U, _ = np.linalg.qr(cn(D, D)); c = cn([0, 8, 16, 30, 44][k], k); c /= np.linalg.norm(c, axis=1, keepdims=True)
        def basis(X): return np.einsum('kd,dab->kab', np.concatenate([np.eye(k), X.reshape(k, D - k)], 1) @ U, A)
        def r(X): return res_m(np.einsum('nk,kab->nab', c, basis(X)), W)
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
    w = w3; ms = {'(1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), '(1,1,-2,0,0)': np.array([1, 1, -2, 0, 0.]), '(1,w,w^2,0,0)': np.array([1, w, w * w, 0, 0]),
                  '(1,-1,0,0,0)': np.array([1, -1, 0, 0, 0.])}
    k = int(sys.argv[1]); tmax = float(sys.argv[2]); sel = sys.argv[3].split(',')
    for i, (nm, m) in enumerate(ms.items()):
        if str(i) not in sel: continue
        hits, n, t = search(k, m, 2000, 3 + 7 * k + i, tmax)
        kinds = {}
        for B in hits:
            B = onb(B); sl = sl_check(B, trials=20) < 1e-7; P = [j for j in range(5) if abs(m[j]) > 1e-9]; Nt = [j for j in range(5) if j not in P]
            key = '%s, neutral column ranks %s' % ('strongly level' if sl else 'DEFECT', [rank(B[:, :, j], 1e-6) for j in Nt])
            kinds[key] = kinds.get(key, 0) + 1
        print('DC spaces, m = %s, k = %d: %d/%d converged (%.0fs): %s' % (nm, k, len(hits), n, t, kinds), flush=True)
        if hits: np.save('r5_dc_k%d_%d.npy' % (k, i), np.array(hits))
