"""Equivariant LM search for level spaces: L = sum_a L_a, L_a inside joint eigenspace W_a of an abelian subgroup.
usage: python3 -I eqlm.py ROWSUB COLSUB 'kv as python dict' nstarts seed [maxit]"""
import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/repr"); sys.path.insert(1, "/home/claude/work/L-gct-086/smallcases")
import numpy as np, math, time, ast, os
KS = [int(c) for c in os.environ.get('KS', '2,3,4,5').split(',')]
from level import Pk_grad
from abscan import SUB, mat_action, joint_eig
from equiv import permmat


CUSTOM = {'T': [([], [], 1)], 'T2': [([], [], 1), ([(0, 1)], [(0, 1)], 0)], 'T3': [([], [], 1), ([(0, 1, 2)], [(0, 1, 2)], 0)],
          'T22': [([], [], 1), ([(0, 1), (2, 3)], [(0, 1), (2, 3)], 0)], 'T4': [([], [], 1), ([(0, 1, 2, 3)], [(0, 1, 2, 3)], 0)],
          'T5': [([], [], 1), ([(0, 1, 2, 3, 4)], [(0, 1, 2, 3, 4)], 0)],
          'D2': [([(0, 1)], [(0, 1)], 0)], 'D3': [([(0, 1, 2)], [(0, 1, 2)], 0)], 'D3i': [([(0, 1, 2)], [(0, 2, 1)], 0)],
          'D4': [([(0, 1, 2, 3)], [(0, 1, 2, 3)], 0)], 'D5': [([(0, 1, 2, 3, 4)], [(0, 1, 2, 3, 4)], 0)],
          'D52': [([(0, 1, 2, 3, 4)], [(0, 2, 4, 1, 3)], 0)], 'D22': [([(0, 1), (2, 3)], [(0, 1), (2, 3)], 0)]}


def setup(rsub, csub, transp=False):
    I5 = np.eye(5)
    if rsub in CUSTOM:
        gens = [mat_action(permmat(a), permmat(b), bool(t)) for a, b, t in CUSTOM[rsub]]
        orders, sp = joint_eig(gens)
        return sp
    gens = [mat_action(permmat(g), I5) for g in SUB[rsub]] + [mat_action(I5, permmat(g)) for g in SUB[csub]]
    orders, sp = joint_eig(gens)
    return sp


def run(sp, kv, nstarts=4, seed=0, maxit=60, verbose=True):
    rs = np.random.RandomState(seed)
    keys = [a for a in kv if kv[a] > 0]
    K = sum(kv[a] for a in keys)
    Qs = {}
    for a in keys:
        d = sp[a].shape[1]
        Z = rs.randn(d, d) + 1j * rs.randn(d, d)
        U, _ = np.linalg.qr(Z)
        Qs[a] = sp[a] @ U  # 25 x d, orthonormal columns
    shapes = [(a, kv[a], sp[a].shape[1] - kv[a]) for a in keys]
    nunk = sum(k * m for _, k, m in shapes)
    R = int(1.3 * math.comb(K + max(KS) - 1, max(KS))) + 20
    best = None
    for st in range(nstarts):
        Cc = rs.randn(R, K) + 1j * rs.randn(R, K); Cc /= np.linalg.norm(Cc, axis=1, keepdims=True)
        z = 0.5 * (rs.randn(nunk) + 1j * rs.randn(nunk))

        def basis(z):
            rows = []; off = 0
            for a, k, m in shapes:
                C = z[off:off + k * m].reshape(k, m); off += k * m
                Bk = np.hstack([np.eye(k), C]) @ Qs[a].T  # k x 25
                rows.append(Bk)
            return np.vstack(rows)

        def resid_jac(z):
            Bm = basis(z)
            T = (Cc @ Bm).reshape(R, 5, 5)
            P, G = Pk_grad(T)
            f = P[:, KS].T.ravel()
            # jacobian wrt z
            nk = len(KS); J = np.zeros((nk * R, nunk), complex)
            off = 0; row0 = 0
            Gf = G[:, KS].reshape(R, nk, 25)
            for a, k, m in shapes:
                Qm = Qs[a][:, k:]  # 25 x m
                GQ = np.einsum('rkx,xm->krm', Gf, Qm)  # 4 x R x m
                for p in range(k):
                    J[:, off + p * m: off + (p + 1) * m] = (GQ * Cc[None, :, row0 + p, None]).reshape(nk * R, m)
                off += k * m; row0 += k
            return f, J
        mu = 1e-2
        f, J = resid_jac(z); cost = np.linalg.norm(f)
        for it in range(maxit):
            A = J.conj().T @ J
            g = J.conj().T @ f
            while True:
                dz = -np.linalg.solve(A + mu * np.diag(np.diag(A).real + 1e-12), g)
                f2, J2 = resid_jac(z + dz); c2 = np.linalg.norm(f2)
                if c2 < cost:
                    z = z + dz; f, J, cost = f2, J2, c2; mu = max(mu / 3, 1e-12); break
                mu *= 4
                if mu > 1e8: break
            if mu > 1e8 or cost < 1e-12: break
        Bm = basis(z)
        sv = np.linalg.svd(Bm, compute_uv=False)
        if verbose:
            print('start', st, 'res %.3e' % cost, 'iters', it, 'cond %.2e' % (sv[0] / sv[-1]), 'max|z| %.2e' % np.abs(z).max(), flush=True)
        if best is None or cost < best[0]:
            best = (cost, Bm)
    return best


if __name__ == '__main__':
    rsub, csub = sys.argv[1], sys.argv[2]
    kv = ast.literal_eval(sys.argv[3])
    nst = int(sys.argv[4]); seed = int(sys.argv[5]); maxit = int(sys.argv[6]) if len(sys.argv) > 6 else 60
    sp = setup(rsub, csub)
    print({k: v.shape[1] for k, v in sp.items()})
    t0 = time.time()
    best = run(sp, kv, nst, seed, maxit)
    print('best %.3e' % best[0], 'time %.1f' % (time.time() - t0))
    tag = 'K' + ''.join(map(str, KS)) + '_%s_%s_%s_%d' % (rsub, csub, '_'.join('%s-%d' % (''.join(map(str, a)), b) for a, b in kv.items()), seed)
    np.save('/home/claude/work/L-gct-210/repr/eqlm_%s.npy' % tag, best[1])
