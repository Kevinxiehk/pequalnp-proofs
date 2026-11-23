import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""isotropic m = (1,w,w^2,0,0): candidate from the principal-stratum analysis: Z_* = v (1/m)^T = v mbar^T with v of chi_1 type,
   together with the split element e_i m^T.  Is span(e_i m^T, v mbar^T) a space with defect line C m?  If yes, climb."""
import numpy as np, itertools, time
from core import *
from di_core import *
from di_ext import ext, chk_m
w = w3; m = np.array([1, w, w * w, 0, 0]); mb = np.array([1, w * w, w, 0, 0])
lines = []
for p in itertools.permutations(range(4)):
    v = chi(1)[list(p)]
    if not any(abs(abs(np.vdot(v, u)) - 4) < 1e-9 for u in lines): lines.append(v)
print('chi_1-type lines:', len(lines))
rng = np.random.default_rng(3); t0 = time.time()
for li, v in enumerate(lines):
    Zs = np.outer(v, mb)
    r1 = chk_m(np.array([Zs]), m)
    for i in range(4):
        F = np.array([np.outer(np.eye(4)[i], m), Zs]); r2 = chk_m(F, m)
        if r2 < 1e-9:
            msg = 'line %d row %d: span(e_i m^T, v mbar^T) has defect in C m (res %.0e); ' % (li, i, r2)
            dims = [2]
            for k in (3, 4, 5):
                if time.time() - t0 > 100: break
                s, n = ext(F, m, 10, int(rng.integers(1e6)), tmax=8)
                if not s: msg += 'dim %d: 0/%d' % (k, n); break
                F = np.concatenate([F, s[0][None]]); msg += 'dim %d: %d/%d; ' % (k, len(s), n)
            print(msg, flush=True)
    if li == 0: print('line 0: C v mbar^T alone: residual %.1e' % r1)
