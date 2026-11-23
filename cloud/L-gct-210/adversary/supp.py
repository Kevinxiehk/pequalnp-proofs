"""LM search for d-dim level spaces of 5x5 matrices restricted to a support pattern.
usage: python3 -I supp.py NAME d starts seed tlimit"""
import sys, time
sys.path.insert(0, '/home/claude/work/L-gct-086/smallcases')
import numpy as np
from math import comb
from search import residuals
from level import Pk
n = 5
def supp_ambient(S):
    A = np.zeros((len(S), n, n))
    for k, (i, j) in enumerate(S): A[k, i, j] = 1
    return A
def cover(rows, cols):
    return [(i, j) for i in range(n) for j in range(n) if i in rows or j in cols]
SUPPORTS = {
 'r45c45': cover({3,4},{3,4}),
 'r5c345': cover({4},{2,3,4}),
 'r45c5': cover({3,4},{4}),
 'r345c45': cover({2,3,4},{3,4}),
 'r2345c5': cover({1,2,3,4},{4}),
 'noperm': [(i,j) for i in range(n) for j in range(n) if i!=j],
 'noblock22': [(i,j) for i in range(n) for j in range(n) if not (i<2 and j<2)],
 'noblock23': [(i,j) for i in range(n) for j in range(n) if not (i<2 and j<3)],
 'full': [(i,j) for i in range(n) for j in range(n)],
}
def run(A, d, starts, seed, tlimit, maxit=400):
    rng = np.random.default_rng(seed); m = A.shape[0]
    nsamp = comb(d + n - 1, n) + 10; t0 = time.time(); best = (np.inf, None)
    for s in range(starts):
        Z = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m)); Q, _ = np.linalg.qr(Z); Q = Q.T
        X = 0.3 * (rng.normal(size=(d, m - d)) + 1j * rng.normal(size=(d, m - d)))
        xs = rng.normal(size=(nsamp, d)) + 1j * rng.normal(size=(nsamp, d)); xs /= np.linalg.norm(xs, axis=1, keepdims=True)
        lam = 1e-3; r, J = residuals(X, Q, A, xs, n, d, 1); f = np.linalg.norm(r)
        for it in range(maxit):
            if time.time() - t0 > tlimit: break
            H = J.conj().T @ J; g = J.conj().T @ r
            Xn = X + np.linalg.solve(H + lam * np.diag(np.diag(H).real + 1e-12), -g).reshape(X.shape)
            fn = np.linalg.norm(residuals(Xn, Q, A, xs, n, d, 1, jac=False))
            if fn < f:
                X = Xn; lam = max(lam / 3, 1e-12); r, J = residuals(X, Q, A, xs, n, d, 1); f = fn
            else:
                lam *= 4
                if lam > 1e8: break
            if f < 1e-12 * (1 + np.linalg.norm(X)) ** n: break
        print(f' start {s}: res {f:.3e} |X| {np.linalg.norm(X):.2e} it {it}', flush=True)
        if f < best[0]:
            B = np.einsum('iq,qab->iab', np.hstack([np.eye(d), X]) @ Q, A); best = (f, B)
        if time.time() - t0 > tlimit: break
    return best
if __name__ == '__main__':
    name, d, starts, seed, tl = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5])
    A = supp_ambient(SUPPORTS[name])
    f, B = run(A, d, starts, seed, tl)
    print(name, len(SUPPORTS[name]), 'd', d, 'best', f)
    np.save(f'/home/claude/work/L-gct-210/adversary/sol_{name}_{d}_{seed}.npy', B)
