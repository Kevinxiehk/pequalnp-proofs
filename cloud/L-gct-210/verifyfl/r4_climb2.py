import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""isotropic m = (1,w,w^2,0,0): greedy climbs (m fixed) starting from the line C chi_1 mbar^T (the Z_* of Theorem PR3, remark (i))."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import *
w = w3; m = np.array([1, w, w * w, 0, 0]); mbar = np.array([1, w * w, w, 0, 0]); Zs = np.outer(chi(1), mbar)
seed = int(sys.argv[1]); tmax = float(sys.argv[2]); t0 = time.time(); run = 0
print('line C chi_1 mbar^T: residual %.1e' % chk_m(Zs[None], m), flush=True)
while time.time() - t0 < tmax:
    F = [Zs / np.linalg.norm(Zs)]; found = []
    while len(F) < 5 and time.time() - t0 < tmax:
        sols, n = ext(np.array(F), m, 6, seed + 1000 * run + len(F), tmax=min(15, max(3, tmax - (time.time() - t0))))
        found.append('%d/%d' % (len(sols), n))
        if not sols: break
        F.append(sols[(seed + run) % len(sols)])
    B = onb(np.array(F)); H, _ = kernel_of(B, lambda Y: Y.sum(0))
    split = [i for i in range(4) if rank(np.concatenate([B, np.outer(np.eye(4)[i], m)[None]]).reshape(len(B) + 1, -1), 1e-6) == len(B)]
    print('run %d: reached dim %d (extensions found per step: %s), residual %.1e, ker kappa dim %d (sl err %.1e, rank s %d), split rows %s' % (
        run, len(F), ' '.join(found), chk_m(B, m), len(H), sl_check(H, trials=20) if len(H) else 0, rank(H.sum(-1), 1e-7) if len(H) else 0, split), flush=True)
    run += 1
