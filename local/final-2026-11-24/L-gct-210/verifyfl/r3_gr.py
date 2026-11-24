import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""spaces with a FIXED general defect line m: LM on Gr(k,17); report whether hits are split, kappa, strong levelness of ker kappa."""
import numpy as np, time
from core import *
from di_core import *
from di_gr import gr_search
from di_ext import chk_m
def describe(B, m):
    ed, Cb, lev, sv = defect(B); k = len(B)
    split = [i for i in range(4) if rank(np.concatenate([B, np.outer(np.eye(4)[i], m)[None]]).reshape(k + 1, -1), 1e-6) == k]
    L0, _ = kernel_of(B, lambda Y: Y.sum(0)); sl0 = sl_check(L0, trials=40) if len(L0) else 0
    q = rank(B.sum(-1), 1e-6)
    return 'e=%d lev %.0e split rows %s dim ker kappa %d (strong-level err %.0e) q=%d' % (ed, lev, split, len(L0), sl0, q)
if __name__ == '__main__':
    which = sys.argv[1]; k = int(sys.argv[2]); starts = int(sys.argv[3]); tmax = float(sys.argv[4])
    m = {'A': np.array([1, 2, -3, 0, 0.]), 'B': np.array([1, 2, 3, -1, -5.]), 'I': np.array([1, w3, w3 ** 2, 0, 0]), 'C': np.array([1, 1, -2, 0, 0.])}[which]
    hits, n, t = gr_search(k, m, starts, 7 + k, tmax)
    print('m = %s (type %s), Gr(%d,17): %d/%d converged (%.0fs)' % (np.round(m, 2), which, k, len(hits), n, t), flush=True)
    for B in hits[:12]: print('   ', describe(B, m))
    if hits: np.save('r3_gr_%s_k%d.npy' % (which, k), np.array(hits))
