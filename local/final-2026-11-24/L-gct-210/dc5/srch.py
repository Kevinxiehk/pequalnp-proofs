"""LM search for d-dim subspaces of 5x5 DC matrices on which P_k vanish for k in KS.
usage: python3 -I srch.py d K(e.g. 23 or 234 or 2345) starts seed tlimit"""
import sys, time
sys.path.insert(0, '/home/kevxhk/work/L-gct-086/smallcases')
import numpy as np
from math import comb
from level import Pk, Pk_grad, dc_basis

def residuals(X, Q, A, xs, d, ks, jac=True):
    m = A.shape[0]
    B = np.hstack([np.eye(d), X]) @ Q
    Tb = np.einsum('iq,qab->iab', B, A)
    T = np.einsum('ri,iab->rab', xs, Tb)
    if not jac:
        return Pk(T)[:, ks].reshape(-1)
    P, G = Pk_grad(T)
    C = np.einsum('pq,qab->pab', Q[d:], A)
    GC = np.einsum('rkab,pab->rkp', G[:, ks], C)
    J = np.einsum('ri,rkp->rkip', xs, GC)
    R, K = GC.shape[:2]
    return P[:, ks].reshape(-1), J.reshape(R * K, d * (m - d))

def run(n, d, ks, starts, seed, tlimit, maxit=300):
    rng = np.random.default_rng(seed)
    A = dc_basis(n); m = A.shape[0]
    nsamp = comb(d + max(ks) - 1, max(ks)) + 10
    t0 = time.time(); best = None
    for s in range(starts):
        Z = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m))
        Q, _ = np.linalg.qr(Z); Q = Q.T
        X = 0.5 * (rng.normal(size=(d, m - d)) + 1j * rng.normal(size=(d, m - d)))
        xs = rng.normal(size=(nsamp, d)) + 1j * rng.normal(size=(nsamp, d))
        xs /= np.linalg.norm(xs, axis=1, keepdims=True)
        lam = 1e-3
        r, J = residuals(X, Q, A, xs, d, ks); f = np.linalg.norm(r)
        for it in range(maxit):
            if time.time() - t0 > tlimit: break
            JH = J.conj().T; H = JH @ J; g = JH @ r
            step = np.linalg.solve(H + lam * np.diag(np.diag(H).real + 1e-12), -g)
            Xn = X + step.reshape(X.shape)
            rn = residuals(Xn, Q, A, xs, d, ks, jac=False); fn = np.linalg.norm(rn)
            if fn < f:
                X = Xn; lam = max(lam / 3, 1e-12); r, J = residuals(X, Q, A, xs, d, ks); f = fn
            else:
                lam *= 4
                if lam > 1e8: break
            if f < 1e-12: break
        print(f'start {s}: res {f:.3e} |X| {np.linalg.norm(X):.2e} it {it}', flush=True)
        if best is None or f < best[0]: best = (f, X.copy(), Q.copy())
        if f < 1e-11 or time.time() - t0 > tlimit: break
    f, X, Q = best
    B = np.hstack([np.eye(d), X]) @ Q
    return f, np.einsum('iq,qab->iab', B, A)

if __name__ == '__main__':
    d = int(sys.argv[1]); ks = [int(c) for c in sys.argv[2]]
    starts = int(sys.argv[3]); seed = int(sys.argv[4]); tl = float(sys.argv[5])
    f, Tb = run(5, d, ks, starts, seed, tl)
    print('final', f)
    np.save(f'/home/kevxhk/work/L-gct-210/dc5/sol_d{d}_k{sys.argv[2]}_s{seed}.npy', Tb)
