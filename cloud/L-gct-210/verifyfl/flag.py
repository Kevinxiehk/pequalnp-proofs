import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""classification-free structured search: strongly level L' = N (+) span(Y_1..Y_q) with N a d-dim DC space (chart) and
row sums of the Y_j normalised by a dual-basis condition (so q is exactly the number of Y's).  (q,d) given."""
import numpy as np, time
from core import *
from lm import res, ambient
def flag_search(q, d, starts, seed, useP4=True, tmax=150, verbose=True):
    Adc, Acs = ambient('dc'), ambient('cs'); t0 = time.time(); hits = []
    for st in range(starts):
        if time.time() - t0 > tmax: break
        rng = np.random.default_rng(seed + 977 * st); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
        U, _ = np.linalg.qr(cn(12, 12)); k = q + d; ns = 2 * [0, 3, 12, 31, 65][k] // 3 + 14
        c = cn(ns, k); c /= np.linalg.norm(c, axis=1, keepdims=True)
        duals = cn(q, 4)                                  # a_j : a_i . s(Y_j) = delta_ij
        nz = d * (12 - d)
        def build(X):
            Zc = np.concatenate([np.eye(d), X[:nz].reshape(d, 12 - d)], 1) @ U
            Z = np.einsum('kd,dab->kab', Zc, Adc); Y = np.einsum('jd,dab->jab', X[nz:].reshape(q, 15), Acs)
            return Z, Y
        def r(X):
            Z, Y = build(X); B = np.concatenate([Z, Y])
            nrm = (np.einsum('ik,jk->ij', duals, Y.sum(-1)) - np.eye(q)).ravel()
            return np.concatenate([res(np.einsum('nk,kab->nab', c, B), useP4), 3 * nrm])
        X = cn(nz + 15 * q) * (0.7 if st % 2 else 1.5); lam = 1e-2; rr = r(X); f = np.vdot(rr, rr).real; h = 1e-7; n = len(X)
        for it in range(300):
            J = np.empty((len(rr), n), complex)
            for i in range(n):
                Xp = X.copy(); Xp[i] += h; J[:, i] = (r(Xp) - rr) / h
            g = J.conj().T @ rr; H = J.conj().T @ J
            for _ in range(12):
                dl = np.linalg.solve(H + lam * np.diag(np.diag(H).real + 1e-10), -g); rn = r(X + dl); fn = np.vdot(rn, rn).real
                if fn < f: X, rr, f, lam = X + dl, rn, fn, max(lam / 5, 1e-12); break
                lam *= 5
            else: break
            if f < 1e-26: break
        ok = np.sqrt(f) < 1e-9
        if ok:
            Z, Y = build(X); B = np.concatenate([Z, Y]); hits.append(B)
            S = B.sum(-1); info = 'dim %d, q=%d, fresh %.1e' % (rank(B, 1e-6), rank(S, 1e-6), sl_check(B, trials=60))
        if verbose: print(f'   ({q},{d}) P4={useP4} start {st}: resid {np.sqrt(f):.1e}' + (' ' + info if ok else ''), flush=True)
    print(f'  => ({q},{d}) P4={useP4}: {len(hits)}/{st + 1} converged, {time.time() - t0:.0f}s', flush=True)
    return hits
if __name__ == '__main__':
    q, d, P4, starts, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3] == '1', int(sys.argv[4]), int(sys.argv[5])
    flag_search(q, d, starts, seed, P4, tmax=float(sys.argv[6]) if len(sys.argv) > 6 else 150)
