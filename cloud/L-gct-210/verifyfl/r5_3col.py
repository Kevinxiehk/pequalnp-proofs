import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""Lemma 3C sanity: column-centred spaces supported on the three columns of P (ambient V^3, dim 9) with defect in C m.
   LM on Gr(k,9), k = 3 (should exist) and k = 4 (Lemma 3C: none)."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import mperp, res_m
def amb3():
    E = []
    for j in range(3):
        for v in np.linalg.svd(np.ones((1, 4)))[2][1:]:
            b = np.zeros((4, 5), complex); b[:, j] = v; E.append(b)
    return np.array(E)
def search(k, m, starts, seed, tmax):
    A = amb3(); D = 9; W = mperp(m); hits = []; t0 = time.time(); st = 0
    for st in range(starts):
        if time.time() - t0 > tmax: break
        rng = np.random.default_rng(seed + 31 * st); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
        U, _ = np.linalg.qr(cn(D, D)); c = cn(30, k); c /= np.linalg.norm(c, axis=1, keepdims=True)
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
w = w3
for nm, m in {'(1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), '(1,w,w^2,0,0)': np.array([1, w, w * w, 0, 0])}.items():
    for k in (3, 4):
        hits, n, t = search(k, m, 500, 7 + k, 22)
        sl = [sl_check(B, trials=20) for B in hits]
        print('3-column spaces, m = %s, k = %d: %d/%d converged (%.0fs); strongly level %d, genuine defect %d' % (nm, k, len(hits), n, t, sum(x < 1e-7 for x in sl), sum(x > 1e-5 for x in sl)), flush=True)
