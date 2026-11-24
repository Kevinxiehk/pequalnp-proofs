import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""more DC planes by LM, classified by (k, g, pattern): the classification says only type I (k=3,g=1) and type II (k=4,g=2)."""
import numpy as np, time, io, contextlib
from core import *
from lm import Prob
def classify(B):
    cols = [B[:, :, m] for m in range(5)]; act = [m for m in range(5) if np.linalg.norm(cols[m]) > 1e-5]
    lines = []; mult = []
    for m in act:
        u, s, vh = np.linalg.svd(cols[m]); v = vh[0]
        if len(s) > 1 and s[1] > 1e-5 * s[0]: return 'NON-RANK-1 COLUMN'
        for i, l in enumerate(lines):
            if abs(abs(np.vdot(v, l)) - 1) < 1e-6: mult[i] += 1; break
        else: lines.append(v); mult.append(1)
    zr = [i for i in range(4) if np.abs(B[:, i, :]).max() < 1e-5]
    return 'k=%d g=%d pattern %s zero rows %s' % (len(act), len(lines), tuple(sorted(mult, reverse=True)), zr)
t0 = time.time(); cnt = {}; n = 0; hit = 0
for st in range(60):
    if time.time() - t0 > 100: break
    P = Prob(2, 'dc', True, seed=5000 + st); nn = 2 * (P.D - 2)
    X0 = (P.rng.normal(size=nn) + 1j * P.rng.normal(size=nn)) * (0.5 if st % 2 else 1.5)
    X, f = P.solve(X0); n += 1
    if f < 1e-11:
        hit += 1; c = classify(P.basis(X)); cnt[c] = cnt.get(c, 0) + 1
print('DC planes: %d/%d starts converged (%.0fs)' % (hit, n, time.time() - t0))
for c, v in sorted(cnt.items()): print('  ', v, 'x', c)
