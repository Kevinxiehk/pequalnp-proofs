import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""Kind (R3) typed search: 4-dim column-centred spaces with defect in C m whose row sums lie in the degenerate plane u^perp (u isotropic).
   Ambient: zero column sums and <s(Y),u> = 0 (dim 14); LM on Gr(4,14).  Control: two-column m (such spaces exist, u = (1,w^2,w,0))."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import mperp, res_m
from lm import ambient
def search(k, m, u, starts, seed, tmax):
    A0 = ambient('cs'); cons = np.array([np.sum(b.sum(1) * u) for b in A0])          # (15,)
    uu, s, vh = np.linalg.svd(cons[None, :]); A = np.einsum('jd,dab->jab', vh[1:].conj(), A0); D = len(A); W = mperp(m); hits = []; t0 = time.time(); st = 0
    for st in range(starts):
        if time.time() - t0 > tmax: break
        rng = np.random.default_rng(seed + 31 * st); cn = lambda *s_: rng.normal(size=s_) + 1j * rng.normal(size=s_)
        U, _ = np.linalg.qr(cn(D, D)); c = cn(44, k); c /= np.linalg.norm(c, axis=1, keepdims=True)
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
    w = w3; u = np.array([1, w * w, w, 0]); sel = sys.argv[1].split(','); tmax = float(sys.argv[2])
    ms = {'control (1,-1,0,0,0)': np.array([1, -1, 0, 0, 0.]), '(1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), '(1,1,-2,0,0)': np.array([1, 1, -2, 0, 0.]), '(0,0,1,2,-3)': np.array([0, 0, 1, 2, -3.])}
    for i, (nm, m) in enumerate(ms.items()):
        if str(i) not in sel: continue
        hits, n, t = search(4, m, u, 2000, 17 + i, tmax)
        sl = [sl_check(B, trials=20) for B in hits]
        print('(R3)-typed, u = (1,w^2,w,0), m = %s: %d/%d converged (%.0fs); genuine defect %d' % (nm, len(hits), n, t, sum(x > 1e-5 for x in sl)), flush=True)
