"""LM search for PRODUCT-TYPE level spaces (L_gct_114 setting): t = R + C, row i of R in V_i (dim a_i),
column j of C in S_j (dim b_j), all combinations level.  usage: prodlm.py 'a0,..,a4' 'b0,..,b4' nstarts seed [maxit]"""
import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/repr"); sys.path.insert(1, "/home/kevxhk/work/L-gct-086/smallcases")
import numpy as np, math, time
from level import Pk_grad


def run(a, b, nstarts=3, seed=0, maxit=80, verbose=True):
    rs = np.random.RandomState(seed)
    K = sum(a) + sum(b)
    blocks = [('r', i, a[i]) for i in range(5) if a[i]] + [('c', j, b[j]) for j in range(5) if b[j]]
    nunk = sum(k * (5 - k) for _, _, k in blocks)
    R = int(1.3 * math.comb(K + 4, 5)) + 20
    best = None
    for st in range(nstarts):
        Qs = [np.linalg.qr(rs.randn(5, 5) + 1j * rs.randn(5, 5))[0] for _ in blocks]
        Cc = rs.randn(R, K) + 1j * rs.randn(R, K); Cc /= np.linalg.norm(Cc, axis=1, keepdims=True)
        z = 0.5 * (rs.randn(nunk) + 1j * rs.randn(nunk))

        def vecs(z):
            out = []; off = 0
            for (kind, idx, k), Q in zip(blocks, Qs):
                C = z[off:off + k * (5 - k)].reshape(k, 5 - k); off += k * (5 - k)
                out.append(np.hstack([np.eye(k), C]) @ Q.T)  # k x 5
            return out

        def basis(z):
            rows = []
            for (kind, idx, k), Vv in zip(blocks, vecs(z)):
                for p in range(k):
                    M = np.zeros((5, 5), complex)
                    if kind == 'r': M[idx, :] = Vv[p]
                    else: M[:, idx] = Vv[p]
                    rows.append(M.ravel())
            return np.array(rows)

        def resid_jac(z):
            Bm = basis(z)
            T = (Cc @ Bm).reshape(R, 5, 5)
            P, G = Pk_grad(T)
            f = P[:, 1:6].T.ravel()
            J = np.zeros((5 * R, nunk), complex)
            off = 0; row0 = 0
            for (kind, idx, k), Q in zip(blocks, Qs):
                m = 5 - k
                Gv = G[:, 1:6, idx, :] if kind == 'r' else G[:, 1:6, :, idx]  # R x 5 x 5
                GQ = np.einsum('rkx,xm->krm', Gv, Q[:, k:])  # 5 x R x m
                for p in range(k):
                    J[:, off + p * m: off + (p + 1) * m] = (GQ * Cc[None, :, row0 + p, None]).reshape(5 * R, m)
                off += k * m; row0 += k
            return f, J
        mu = 1e-2
        f, J = resid_jac(z); cost = np.linalg.norm(f)
        for it in range(maxit):
            A = J.conj().T @ J; g = J.conj().T @ f
            while True:
                dz = -np.linalg.solve(A + mu * np.diag(np.diag(A).real + 1e-12), g)
                f2, J2 = resid_jac(z + dz); c2 = np.linalg.norm(f2)
                if c2 < cost:
                    z = z + dz; f, J, cost = f2, J2, c2; mu = max(mu / 3, 1e-12); break
                mu *= 4
                if mu > 1e8: break
            if mu > 1e8 or cost < 1e-12: break
        Bm = basis(z); sv = np.linalg.svd(Bm, compute_uv=False)
        if verbose:
            print('  start', st, 'res %.3e' % cost, 'it', it, 'cond %.1e' % (sv[0] / sv[-1]), 'max|z| %.1e' % np.abs(z).max(), flush=True)
        if best is None or cost < best[0]: best = (cost, Bm)
    return best


if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1].split(',')]; b = [int(x) for x in sys.argv[2].split(',')]
    nst = int(sys.argv[3]); seed = int(sys.argv[4]); maxit = int(sys.argv[5]) if len(sys.argv) > 5 else 80
    t0 = time.time()
    best = run(a, b, nst, seed, maxit)
    print('rows', a, 'cols', b, 'best %.3e' % best[0], 'time %.1f' % (time.time() - t0), flush=True)
    if best[0] < 1e-6:
        np.save('/home/kevxhk/work/L-gct-210/repr/prod_%s_%s_%d.npy' % (sys.argv[1].replace(',', ''), sys.argv[2].replace(',', ''), seed), best[1])
