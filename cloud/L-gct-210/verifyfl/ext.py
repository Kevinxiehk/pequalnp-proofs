import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""one-dimensional extensions of a fixed strongly level space F: all Y with span(F, Y) strongly level (LM, random starts)."""
import numpy as np, time
from core import *
from lm import res, ambient
e = np.eye(5); zeta = np.array([1, w3, w3 ** 2, 0]); zb = zeta.conj()
def ext_search(F, starts, seed, useP4=True, tmax=120, verbose=False, kind='cs'):
    F = np.asarray(F, complex); k0 = len(F); A = ambient(kind)
    # orthonormal basis of the complement of span(F) inside the column-sum-zero space
    C = np.einsum('kab,dab->kd', F, A.conj()); u, s, vh = np.linalg.svd(C); comp = vh[k0:].conj()   # rows: coordinates (15-k0, 15)
    Ac = np.einsum('jd,dab->jab', comp.conj(), A); n = len(Ac)
    rng = np.random.default_rng(seed); sols = []; t0 = time.time()
    for st in range(starts):
        if time.time() - t0 > tmax: break
        c = rng.normal(size=(40, k0 + 1)) + 1j * rng.normal(size=(40, k0 + 1)); c /= np.linalg.norm(c, axis=1, keepdims=True)
        a = rng.normal(size=n) + 1j * rng.normal(size=n); a /= np.linalg.norm(a)
        def r(X):
            Y = np.einsum('j,jab->ab', X, Ac); B = np.concatenate([F, Y[None]])
            return np.concatenate([res(np.einsum('nk,kab->nab', c, B), useP4), [3 * (a @ X - 1)]])
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
        if np.sqrt(f) < 1e-9:
            Y = np.einsum('j,jab->ab', X, Ac); Y /= np.linalg.norm(Y); sols.append(Y)
        if verbose: print('   start', st, 'resid %.1e' % np.sqrt(f), flush=True)
    return sols, st + 1
def describe(sols, F, known=None):
    for Y in sols:
        s = Y.sum(1); ns = np.linalg.norm(s); iso = abs(np.sum(s * s)) / max(ns ** 2, 1e-30)
        fresh = sl_check(np.concatenate([F, Y[None]]), trials=60, seed=5)
        extra = ''
        if known is not None:
            K = np.concatenate([F, known]).reshape(len(F) + len(known), -1); y = Y.ravel()
            coef, *_ = np.linalg.lstsq(K.T, y, rcond=None); extra = ' dist to known ext space %.1e' % np.linalg.norm(K.T @ coef - y)
        print('   |s(Y)| = %.3f, |<s,s>|/|s|^2 = %.4f, s/|s| = %s, fresh %.1e%s' % (ns, iso, np.round(s / max(ns, 1e-30), 3), fresh, extra))
if __name__ == '__main__':
    which = sys.argv[1]
    NII = np.array([np.outer(zeta, e[0] - e[1]), np.outer(zb, e[2] - e[3])])
    NI = np.array([np.outer(chi(1), e[0] - e[1]), np.outer(chi(1), e[1] - e[2])])
    R = np.array([np.outer(chi(1), e[c]) for c in range(3)])
    if which == 'II':
        print('# extensions of the type II plane (known: (1,1,1,-3)^T e_4^T)')
        sols, n = ext_search(NII, 16, 1); print('  %d/%d converged' % (len(sols), n)); describe(sols, NII, np.array([np.outer([1, 1, 1, -3], e[4])]))
    if which == 'I':
        print('# extensions of the type I plane chi_1 (x) Lambda_M (known: chi_1 (x) C^M)')
        sols, n = ext_search(NI, 16, 2); print('  %d/%d converged' % (len(sols), n)); describe(sols, NI, np.array([np.outer(chi(1), e[0])]))
    if which == 'R':
        print('# extensions of R = chi_1 (x) C^M: full system (claim: none)')
        sols, n = ext_search(R, 12, 3); print('  %d/%d converged' % (len(sols), n)); describe(sols, R)
        print('# same, relaxed system without P_4 (calibration: chi_1 e_4^T exists)')
        sols, n = ext_search(R, 6, 4, useP4=False); print('  %d/%d converged' % (len(sols), n))
        for Y in sols: print('   s/|s| =', np.round(Y.sum(1) / np.linalg.norm(Y.sum(1)), 3))
