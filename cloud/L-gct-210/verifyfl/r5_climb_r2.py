import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""Branch (R2): m = (1,1,-2,0,0), Z_* = v (e_0 - e_1)^T, v isotropic.  Greedy climbs with m fixed (column sums in C m allowed);
   control: m = (1,-1,0,0,0) with the same start (column-centred (4,1) spaces exist there)."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import *
def vth(th): return chi(1) + th * chi(2) - (th * th / 2) * chi(3)
tmax = float(sys.argv[1]); t0 = time.time(); w = w3
zeta = np.array([1, w, w * w, 0]); starts = {'zeta': zeta, 'chi_1': chi(1), 'v(0.7+0.3i)': vth(0.7 + 0.3j)}
for mn, m in {'control (1,-1,0,0,0)': np.array([1, -1, 0, 0, 0.]), '(1,1,-2,0,0)': np.array([1, 1, -2, 0, 0.])}.items():
    for vn, v in starts.items():
        for run in range(2):
            if time.time() - t0 > tmax: break
            Z = np.zeros((4, 5), complex); Z[:, 0] = v; Z[:, 1] = -v; F = [Z / np.linalg.norm(Z)]; found = []
            while len(F) < 5 and time.time() - t0 < tmax:
                sols, n = ext(np.array(F), m, 6, 31 + 100 * run + len(F), tmax=8)
                found.append('%d/%d' % (len(sols), n))
                if not sols: break
                # prefer extensions with zero column sums (kappa = 0)
                sols.sort(key=lambda Y: np.abs(Y.sum(0)).max()); F.append(sols[0])
            B = onb(np.array(F)); H, _ = kernel_of(B, lambda Y: Y.sum(0)); Nn, _ = kernel_of(H, lambda Y: Y.sum(1)) if len(H) else ([], 0)
            print('m %-20s v = %-12s run %d: dim %d (found %s) residual %.1e; ker kappa dim %d, its (q,d) = (%d,%d), sl err %.1e' % (
                mn, vn, run, len(F), ' '.join(found), chk_m(B, m), len(H), rank(H.sum(-1), 1e-6) if len(H) else 0, len(Nn), sl_check(H, trials=20) if len(H) else 0), flush=True)
            np.save('r5_r2_%s_%s_%d.npy' % (mn[:7].replace(' ', ''), vn[:4], run), B)
