import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""Prop I-ALL sanity: climbs (m = (1,2,-3,0,0) fixed) from chi_1 (x) Lam_M for M = {0,1,3}, {0,3,4}, {0,1,2}: must stop at dim <= 3,
   and the 3-dim spaces reached that are column-centred must lie in chi_1 (x) C^M (M != P)."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import *
m = np.array([1, 2, -3, 0, 0.]); t0 = time.time(); tmax = float(sys.argv[1]); c1 = chi(1)
for M in ([0, 1, 3], [0, 3, 4], [0, 1, 2]):
    F0 = []
    for (i, j) in ((M[0], M[1]), (M[1], M[2])):
        Z = np.zeros((4, 5), complex); Z[:, i] = c1; Z[:, j] = -c1; F0.append(Z / np.linalg.norm(Z))
    for run in range(2):
        if time.time() - t0 > tmax: break
        F = list(F0); found = []
        while len(F) < 5 and time.time() - t0 < tmax:
            sols, n = ext(np.array(F), m, 6, 900 + 10 * run + len(F), tmax=8); found.append('%d/%d' % (len(sols), n))
            if not sols: break
            sols.sort(key=lambda Y: np.abs(Y.sum(0)).max()); F.append(sols[run % len(sols)])
        B = onb(np.array(F)); cc = np.abs(B.sum(1)).max() < 1e-8
        target = np.array([np.outer(c1, np.eye(5)[j]) for j in M]).reshape(3, -1)
        inside = rank(np.concatenate([target, B.reshape(len(B), -1)]), 1e-6) == 3
        print('M = %s run %d: dim %d (found %s) residual %.1e; column-centred %s; inside chi_1 (x) C^M: %s' % (M, run, len(F), ' '.join(found), chk_m(B, m), cc, inside), flush=True)
