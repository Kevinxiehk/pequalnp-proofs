import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""Kind (R3): greedy climbs (m fixed) from the type II plane  zeta (e_0 - e_1)^T (+) conj(zeta) (e_3 - e_4)^T  (strongly level).
   Control m = (1,-1,0,0,0): must reach a 4-dim column-centred space of type (2,2)."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import *
tmax = float(sys.argv[1]); t0 = time.time(); w = w3; zeta = np.array([1, w, w * w, 0]); zb = np.array([1, w * w, w, 0])
Z1 = np.zeros((4, 5), complex); Z1[:, 0] = zeta; Z1[:, 1] = -zeta; Z2 = np.zeros((4, 5), complex); Z2[:, 3] = zb; Z2[:, 4] = -zb
for mn, m in {'control (1,-1,0,0,0)': np.array([1, -1, 0, 0, 0.]), '(1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), '(1,1,-2,0,0)': np.array([1, 1, -2, 0, 0.])}.items():
    for run in range(3):
        if time.time() - t0 > tmax: break
        F = [Z1 / np.linalg.norm(Z1), Z2 / np.linalg.norm(Z2)]; found = []
        while len(F) < 5 and time.time() - t0 < tmax:
            sols, n = ext(np.array(F), m, 6, 77 + 100 * run + len(F), tmax=8)
            found.append('%d/%d' % (len(sols), n))
            if not sols: break
            sols.sort(key=lambda Y: np.abs(Y.sum(0)).max()); F.append(sols[run % len(sols)])
        B = onb(np.array(F)); H, _ = kernel_of(B, lambda Y: Y.sum(0)); Nn, _ = kernel_of(H, lambda Y: Y.sum(1)) if len(H) else ([], 0)
        print('m %-20s run %d: dim %d (found %s) residual %.1e; ker kappa dim %d, its (q,d) = (%d,%d), sl err %.1e' % (
            mn, run, len(F), ' '.join(found), chk_m(B, m), len(H), rank(H.sum(-1), 1e-6) if len(H) else 0, len(Nn), sl_check(H, trials=20) if len(H) else 0), flush=True)
