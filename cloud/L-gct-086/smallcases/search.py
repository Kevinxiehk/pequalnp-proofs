"""Gauss-Newton/LM search for d-dim level spaces inside an ambient space of n x n matrices.
usage: python3 -I search.py n d ambient(full|dc) starts maxit seed
"""
import sys, time
sys.path.insert(0, '/home/claude/work/L-gct-086/smallcases')
import numpy as np
from math import comb
from level import Pk, Pk_grad, dc_basis


def ambient(n, kind):
    if kind == 'full':
        A = np.zeros((n * n, n, n))
        for i in range(n):
            for j in range(n):
                A[i * n + j, i, j] = 1
        return A
    if kind == 'dc':
        return dc_basis(n)
    raise ValueError


def residuals(X, Q, A, xs, n, d, kmin, jac=True):
    m = A.shape[0]
    B = np.hstack([np.eye(d), X]) @ Q  # d x m
    Tb = np.einsum('iq,qab->iab', B, A)  # d n n
    T = np.einsum('ri,iab->rab', xs, Tb)
    if not jac:
        P = Pk(T)
        return P[:, kmin:].reshape(-1)
    P, G = Pk_grad(T)
    C = np.einsum('pq,qab->pab', Q[d:], A)  # (m-d) n n
    # dP_k(r)/dX_{ip} = xs[r,i] * <G[r,k], C_p>
    GC = np.einsum('rkab,pab->rkp', G[:, kmin:], C)  # R K (m-d)
    J = np.einsum('ri,rkp->rkip', xs, GC)
    R, K = GC.shape[:2]
    return P[:, kmin:].reshape(-1), J.reshape(R * K, d * (m - d))


def run(n, d, kind, starts=5, maxit=200, seed=0, verbose=True, tlimit=100):
    rng = np.random.default_rng(seed)
    A = ambient(n, kind)
    m = A.shape[0]
    kmin = 1 if kind == 'full' else 2
    nsamp = comb(d + n - 1, n) + 10
    best = None
    t0 = time.time()
    for s in range(starts):
        Z = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m))
        Q, _ = np.linalg.qr(Z)
        Q = Q.T
        X = 0.3 * (rng.normal(size=(d, m - d)) + 1j * rng.normal(size=(d, m - d)))
        xs = rng.normal(size=(nsamp, d)) + 1j * rng.normal(size=(nsamp, d))
        xs /= np.linalg.norm(xs, axis=1, keepdims=True)
        lam = 1e-3
        r, J = residuals(X, Q, A, xs, n, d, kmin)
        f = np.linalg.norm(r)
        for it in range(maxit):
            if time.time() - t0 > tlimit:
                break
            JH = J.conj().T
            H = JH @ J
            g = JH @ r
            step = np.linalg.solve(H + lam * np.diag(np.diag(H).real + 1e-12), -g)
            Xn = X + step.reshape(X.shape)
            rn = residuals(Xn, Q, A, xs, n, d, kmin, jac=False)
            fn = np.linalg.norm(rn)
            if fn < f:
                X = Xn; lam = max(lam / 3, 1e-12)
                r, J = residuals(X, Q, A, xs, n, d, kmin)
                f = fn
            else:
                lam *= 4
                if lam > 1e8:
                    break
            if f < 1e-13 * (1 + np.linalg.norm(X)) ** n:
                break
        if verbose:
            print(f'start {s}: res {f:.3e} |X| {np.linalg.norm(X):.2e} it {it}', flush=True)
        if best is None or f < best[0]:
            best = (f, X.copy(), Q.copy())
        if f < 1e-11:
            break
        if time.time() - t0 > tlimit:
            break
    f, X, Q = best
    B = np.hstack([np.eye(d), X]) @ Q
    Tb = np.einsum('iq,qab->iab', B, A)
    return f, Tb


def verify(Tb, n, trials=50, seed=99):
    rng = np.random.default_rng(seed)
    d = len(Tb)
    worst = 0
    sc = np.abs(Tb).max()
    for _ in range(trials):
        x = rng.normal(size=d) + 1j * rng.normal(size=d)
        x /= np.linalg.norm(x)
        P = Pk(np.einsum('i,iab->ab', x, Tb / sc))[0]
        worst = max(worst, np.abs(P[1:]).max())
    return worst


if __name__ == '__main__':
    n, d, kind = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    starts = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    maxit = int(sys.argv[5]) if len(sys.argv) > 5 else 200
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    f, Tb = run(n, d, kind, starts, maxit, seed)
    print('final res', f, 'fresh-point check', verify(Tb, n))
    np.save(f'/home/claude/work/L-gct-086/smallcases/sol_n{n}_d{d}_{kind}_s{seed}.npy', Tb)
