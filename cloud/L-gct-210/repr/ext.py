import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/repr"); sys.path.insert(1, "/home/claude/work/L-gct-086/smallcases")
import numpy as np
from level import Pk_grad
def ext_dim(Bm, tol=1e-7, seed=0):
    rs = np.random.RandomState(seed)
    K = Bm.shape[0]
    Cc = rs.randn(400, K) + 1j * rs.randn(400, K)
    T = (Cc @ Bm).reshape(-1, 5, 5)
    P, G = Pk_grad(T)
    lev = np.abs(P[:, 1:]).max() / (1 + np.abs(T).max() ** 5)
    Gm = G[:, 1:6].reshape(-1, 25)
    s = np.linalg.svd(Gm, compute_uv=False)
    rank = int(np.sum(s > tol * s[0]))
    return lev, 25 - rank, s[rank - 1] / s[0], (s[rank] / s[0] if rank < 25 else 0)
if __name__ == '__main__':
    for f in sys.argv[1:]:
        Bm = np.load(f)
        print(f.split('/')[-1], 'dim', Bm.shape[0], 'level err %.1e, first-order extension dim %d (sv gap %.1e | %.1e)' % ext_dim(Bm))
