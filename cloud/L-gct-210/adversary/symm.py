"""LM search for g-invariant level spaces L = sum_e W_e, W_e in eigenspace V_e of a symmetry g
of perm(J+t) (g permutes the 25 entries). usage: symm.py GNAME 'd0,d1,...' starts seed tlimit"""
import sys, time
sys.path.insert(0, '/home/claude/work/L-gct-086/smallcases')
import numpy as np
from math import comb
from level import Pk, Pk_grad
n = 5
def perm_entries(f):  # f: (i,j)->(i',j'); returns P with (P t)[f(i,j)] = t[i,j]
    P = np.zeros((25, 25))
    for i in range(n):
        for j in range(n):
            a, b = f(i, j); P[a * n + b, i * n + j] = 1
    return P
s5 = lambda i: (i + 1) % 5
s4 = lambda i: (i + 1) % 4 if i < 4 else 4
c32 = lambda i: [1, 2, 0, 4, 3][i]
G = {
 'g11': lambda i, j: (s5(i), s5(j)),
 'g12': lambda i, j: (s5(i), (j + 2) % 5),
 'g10': lambda i, j: (s5(i), j),
 'gT1': lambda i, j: (s5(j), i),          # transpose twisted, order 10
 'g44': lambda i, j: (s4(i), s4(j)),
 'g4T': lambda i, j: (s4(j), i),           # order 8
 'g66': lambda i, j: (c32(i), c32(j)),
 'g6T': lambda i, j: (c32(j), i),
 'g5T': lambda i, j: (j, s5(i)) if False else (s5(j), s5(s5(i))),
}
def eigenspaces(P):
    N = 1
    M = P.copy()
    while not np.allclose(M, np.eye(25)): M = M @ P; N += 1
    z = np.exp(2j * np.pi / N); out = []
    for e in range(N):
        # projector onto z^e eigenspace
        Pr = sum((z ** (-e * k)) * np.linalg.matrix_power(P, k) for k in range(N)) / N
        u, s, vh = np.linalg.svd(Pr)
        r = int(np.sum(s > 1e-9)); out.append(u[:, :r].T.copy())  # rows: orthonormal basis (columns of Pr range)
    return N, out
def run(V, dims, starts, seed, tlimit, maxit=400):
    rng = np.random.default_rng(seed); blocks = [(e, d) for e, d in enumerate(dims) if d > 0]
    D = sum(dims); nsamp = comb(D + n - 1, n) + 10; t0 = time.time(); best = (np.inf, None)
    for s in range(starts):
        Qs, Xs = [], []
        for e, d in blocks:
            m = V[e].shape[0]; Z = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m)); Q, _ = np.linalg.qr(Z)
            Qs.append(Q.T @ V[e]); Xs.append(0.3 * (rng.normal(size=(d, m - d)) + 1j * rng.normal(size=(d, m - d))))
        xs = rng.normal(size=(nsamp, D)) + 1j * rng.normal(size=(nsamp, D)); xs /= np.linalg.norm(xs, axis=1, keepdims=True)
        def basis(Xs):
            return np.concatenate([(np.hstack([np.eye(d), X]) @ Q) for (e, d), X, Q in zip(blocks, Xs, Qs)]).reshape(D, n, n)
        def res(Xs, jac=True):
            T = np.einsum('ri,iab->rab', xs, basis(Xs))
            if not jac: return Pk(T)[:, 1:].reshape(-1)
            P, Gr = Pk_grad(T); Js = []; off = 0
            for (e, d), Q in zip(blocks, Qs):
                C = Q[d:].reshape(-1, n, n); GC = np.einsum('rkab,pab->rkp', Gr[:, 1:], C)
                Js.append(np.einsum('ri,rkp->rkip', xs[:, off:off + d], GC).reshape(nsamp * 5, -1)); off += d
            return P[:, 1:].reshape(-1), np.hstack(Js)
        def unflat(v):
            out = []; o = 0
            for X in Xs: out.append(v[o:o + X.size].reshape(X.shape)); o += X.size
            return out
        lam = 1e-3; r, J = res(Xs); f = np.linalg.norm(r)
        for it in range(maxit):
            if time.time() - t0 > tlimit: break
            H = J.conj().T @ J; g = J.conj().T @ r
            st = unflat(np.linalg.solve(H + lam * np.diag(np.diag(H).real + 1e-12), -g))
            Xn = [X + S for X, S in zip(Xs, st)]
            fn = np.linalg.norm(res(Xn, False))
            if fn < f: Xs = Xn; lam = max(lam / 3, 1e-12); r, J = res(Xs); f = fn
            else:
                lam *= 4
                if lam > 1e8: break
            if f < 1e-11: break
        print(f'  start {s}: res {f:.3e} it {it}', flush=True)
        if f < best[0]: best = (f, basis(Xs))
        if f < 1e-9 or time.time() - t0 > tlimit: break
    return best
if __name__ == '__main__':
    g = sys.argv[1]; N, V = eigenspaces(perm_entries(G[g]))
    print(g, 'order', N, 'eigdims', [v.shape[0] for v in V])
    if len(sys.argv) > 2:
        dims = [int(x) for x in sys.argv[2].split(',')]
        f, B = run(V, dims, int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]))
        print(g, dims, 'best', f); np.save(f'/home/claude/work/L-gct-210/adversary/sym_{g}_{"".join(map(str,dims))}.npy', B)
