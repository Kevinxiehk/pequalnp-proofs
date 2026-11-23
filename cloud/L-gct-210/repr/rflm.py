"""LM search in the class RF of 'rank-one families with one fixed factor':
   L = sum_m { x v_m^T : x in X_m }  +  sum_m' { u_m' y^T : y in Y_m' },   v_m, u_m' unknown pattern vectors in C^5,
   X_m, Y_m' unknown subspaces of C^5 of prescribed dims.  (Contains product type, L080, ex1, ex2, K, L9.)
usage: rflm.py 'c4,r3,...' nstarts seed [maxit]   (c4 = column-pattern family with dim X = 4, r3 = row-pattern family)"""
import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/repr"); sys.path.insert(1, "/home/claude/work/L-gct-086/smallcases")
import numpy as np, math, time, os
from level import Pk_grad
KS = [int(c) for c in os.environ.get('KS', '1,2,3,4,5').split(',')]


def run(fams, nstarts=3, seed=0, maxit=70, verbose=True):
    rs = np.random.RandomState(seed)
    K = sum(k for _, k in fams)
    nunk = sum(k * (5 - k) + 4 for _, k in fams)
    R = int(1.3 * math.comb(K + 4, 5)) + 20
    nk = len(KS)
    best = None
    for st in range(nstarts):
        Qs = [np.linalg.qr(rs.randn(5, 5) + 1j * rs.randn(5, 5))[0] for _ in fams]
        Qp = [np.linalg.qr(rs.randn(5, 5) + 1j * rs.randn(5, 5))[0] for _ in fams]
        Cc = rs.randn(R, K) + 1j * rs.randn(R, K); Cc /= np.linalg.norm(Cc, axis=1, keepdims=True)
        z = 0.5 * (rs.randn(nunk) + 1j * rs.randn(nunk))

        def unpack(z):
            out = []; off = 0
            for (kind, k), Q, Qq in zip(fams, Qs, Qp):
                C = z[off:off + k * (5 - k)].reshape(k, 5 - k); off += k * (5 - k)
                w = z[off:off + 4]; off += 4
                X = np.hstack([np.eye(k), C]) @ Q.T  # k x 5
                p = Qq @ np.concatenate([[1.0], w])  # pattern
                out.append((X, p))
            return out

        def basis(z):
            rows = []
            for (kind, k), (X, p) in zip(fams, unpack(z)):
                for q in range(k):
                    M = np.outer(X[q], p) if kind == 'c' else np.outer(p, X[q])
                    rows.append(M.ravel())
            return np.array(rows)

        def resid_jac(z):
            parts = unpack(z)
            Bm = basis(z)
            T = (Cc @ Bm).reshape(R, 5, 5)
            P, G = Pk_grad(T)
            f = P[:, KS].T.ravel()
            Gk = G[:, KS]  # R x nk x 5 x 5
            J = np.zeros((nk * R, nunk), complex)
            off = 0; row0 = 0
            for (kind, k), Q, Qq, (X, p) in zip(fams, Qs, Qp, parts):
                m = 5 - k
                if kind == 'c':   # t += sum_q c_q x_q p^T
                    Gx = np.einsum('rkij,j->rki', Gk, p)      # derivative wrt x direction: R x nk x 5
                    Gp = lambda xv: np.einsum('rkij,ri->rkj', Gk, xv)
                else:             # t += sum_q c_q p x_q^T
                    Gx = np.einsum('rkij,i->rkj', Gk, p)
                    Gp = lambda xv: np.einsum('rkij,rj->rki', Gk, xv)
                GQ = np.einsum('rkx,xm->krm', Gx, Q[:, k:])  # nk x R x m
                for q in range(k):
                    J[:, off + q * m: off + (q + 1) * m] = (GQ * Cc[None, :, row0 + q, None]).reshape(nk * R, m)
                off += k * m
                xv = Cc[:, row0:row0 + k] @ X  # R x 5 : sum_q c_q x_q
                J[:, off:off + 4] = np.einsum('rkx,xm->krm', Gp(xv), Qq[:, 1:]).reshape(nk * R, 4)
                off += 4; row0 += k
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
        Bm = basis(z); Bn = Bm / np.linalg.norm(Bm, axis=1, keepdims=True)
        sv = np.linalg.svd(Bn, compute_uv=False)
        if verbose:
            print('  start', st, 'res %.3e' % cost, 'it', it, 'smin(normalised basis) %.1e' % sv[-1], 'max|z| %.1e' % np.abs(z).max(), flush=True)
        good = cost if sv[-1] > 1e-3 else 1e3 + cost
        if best is None or good < best[0]: best = (good, Bm, cost, sv[-1])
    return best


if __name__ == '__main__':
    fams = [(s[0], int(s[1:])) for s in sys.argv[1].split(',')]
    nst = int(sys.argv[2]); seed = int(sys.argv[3]); maxit = int(sys.argv[4]) if len(sys.argv) > 4 else 70
    t0 = time.time()
    best = run(fams, nst, seed, maxit)
    print('fams', sys.argv[1], 'KS', KS, 'best res %.3e (smin %.1e)' % (best[2], best[3]), 'time %.1f' % (time.time() - t0), flush=True)
    if best[2] < 1e-6:
        np.save('/home/claude/work/L-gct-210/repr/rf_%s_%d.npy' % (sys.argv[1].replace(',', '_'), seed), best[1])
