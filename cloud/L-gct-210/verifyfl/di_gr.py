import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""global LM search on Gr(k, 17) for 4x5 spaces with defect line inside C(e_0 - e_1) (m fixed); also seeded/extension runs."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import mperp, res_m, ambient_m, chk_m, ext
def gr_search(k, m, starts, seed, tmax=150, scale=1.0, verbose=False):
    A = ambient_m(m); D = len(A); W = mperp(m); hits = []; t0 = time.time(); st = 0
    for st in range(starts):
        if time.time() - t0 > tmax: break
        rng = np.random.default_rng(seed + 31 * st); cn = lambda *s: rng.normal(size=s) + 1j * rng.normal(size=s)
        U, _ = np.linalg.qr(cn(D, D)); ns = [0, 6, 14, 26, 40, 60][k]; c = cn(ns, k); c /= np.linalg.norm(c, axis=1, keepdims=True)
        def basis(X): return np.einsum('kd,dab->kab', np.concatenate([np.eye(k), X.reshape(k, D - k)], 1) @ U, A)
        def r(X): return res_m(np.einsum('nk,kab->nab', c, basis(X)), W)
        X = cn(k * (D - k)) * scale; lam = 1e-2; rr = r(X); f = np.vdot(rr, rr).real; h = 1e-7; n = len(X)
        for it in range(250):
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
        if np.sqrt(f) < 1e-9: hits.append(basis(X))
        if verbose: print('   start %d resid %.1e' % (st, np.sqrt(f)), flush=True)
    return hits, st + 1, time.time() - t0
if __name__ == '__main__':
    e = np.eye(5); m = e[0] - e[1]; k = int(sys.argv[1]); starts = int(sys.argv[2]); seed = int(sys.argv[3]); tmax = float(sys.argv[4])
    hits, n, t = gr_search(k, m, starts, seed, tmax)
    print('Gr(%d,17), m = e_0 - e_1: %d/%d converged (%.0fs)' % (k, len(hits), n, t))
    for B in hits:
        ed, Cb, lev, sv = defect(B); S = B.sum(-1); q = rank(S, 1e-7)
        Np, _ = kernel_of(B, lambda Y: Y.sum(1)); zt, _ = kernel_of(B, lambda Y: np.concatenate([Y[:, 2:].ravel(), Y[:, 0] + Y[:, 1]]))
        Lpp, _ = kernel_of(B, lambda Y: Y[:, 0] - Y[:, 1]); kap = rank(B.sum(1), 1e-7)
        print('   e=%d level err %.1e  q=%d dim Nbar=%d dim zeta=%d dim L\'\'=%d kappa rank %d' % (ed, lev, q, len(Np) - len(zt), len(zt), len(Lpp), kap))
    if hits: np.save('di_gr_k%d_s%d.npy' % (k, seed), np.array(hits))
