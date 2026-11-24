import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""greedy climb (m fixed) from the saved 'injective' planes N of r4_n2.py: do they lie in (3,1), (4,1), (5,1) spaces?"""
import numpy as np, time, glob
from core import *
from di_core import *
from di_ext import *
idx = int(sys.argv[1]); tmax = float(sys.argv[2]); t0 = time.time()
for f_ in sorted(glob.glob('r4_n2_inj_%d_*.npy' % idx)):
    if time.time() - t0 > tmax: break
    N = np.load(f_); e, Cb, lev, sv = defect(N); m = Cb[0]; m = m / m[np.argmax(np.abs(m))]
    F = list(N)
    while len(F) < 5 and time.time() - t0 < tmax:
        sols, n = ext(np.array(F), m, 8, 17 + len(F), tmax=min(20, max(3, tmax - (time.time() - t0))), tol=1e-7)
        if not sols: break
        F.append(sols[0])
    B = onb(np.array(F)); H, _ = kernel_of(B, lambda Y: Y.sum(0))
    split = [i for i in range(4) if rank(np.concatenate([B, np.outer(np.eye(4)[i], m)[None]]).reshape(len(B) + 1, -1), 1e-6) == len(B)]
    print('%s: m = %s, reached dim %d (residual %.1e), ker kappa dim %d (sl err %.1e, rank s %d), split rows %s' % (
        f_, np.round(m, 3), len(F), chk_m(B, m), len(H), sl_check(H, trials=20) if len(H) else 0, rank(H.sum(-1), 1e-7) if len(H) else 0, split), flush=True)
