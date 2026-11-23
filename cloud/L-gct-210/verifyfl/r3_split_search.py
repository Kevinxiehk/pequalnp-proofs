import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""split spaces with a FIXED m: start from Y_1 = e_3 m^T and extend one vector at a time (LM, m fixed); report dimension reached,
   theta = kappa*mu test and strong levelness of ker kappa at each stage."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import ext, chk_m
def climb(m, seed, tries=10, tmax=25, verbose=True):
    F = np.array([np.outer(np.eye(4)[3], m)]); out = []
    for k in range(2, 6):
        sols, n = ext(F, m, tries, seed + 17 * k, tmax=tmax)
        if not sols:
            out.append('dim %d: 0/%d' % (k, n)); break
        rng = np.random.default_rng(seed + k); Ynew = sols[rng.integers(len(sols))]
        F = np.concatenate([F, Ynew[None]])
        L0, _ = kernel_of(onb(F), lambda Y: Y.sum(0)); sl0 = sl_check(L0, trials=40) if len(L0) else 0
        out.append('dim %d: %d/%d (ker kappa dim %d, strong-level err %.0e)' % (k, len(sols), n, len(L0), sl0))
    return F, ' | '.join(out)
if __name__ == '__main__':
    w = w3
    ms = {'non-isotropic (1,2,-3,0,0)': np.array([1, 2, -3, 0, 0.]), 'isotropic (1,w,w^2,0,0)': np.array([1, w, w * w, 0, 0]),
          'isotropic (1,i,-1,-i,0)': np.array([1, 1j, -1, -1j, 0]), 'isotropic 5 entries': None}
    # isotropic with 5 nonzero entries: sum 0, sum of squares 0: (1, a, b, c, d)
    v5 = np.array([1, 2, 0, 0, 0], complex); 
    # solve x+y+z = -3, x^2+y^2+z^2 = -5 with x = 1.5 : y+z = -4.5, y^2+z^2 = -7.25 -> yz = (20.25+7.25)/2 = 13.75
    y = np.roots([1, 4.5, 13.75]); v5[2] = 1.5; v5[3], v5[4] = y[0], y[1]; ms['isotropic 5 entries'] = v5
    for nm, m in ms.items():
        assert abs(m.sum()) < 1e-12
        print('m %s: <m,m> = %s' % (nm, np.round(np.sum(m * m), 10)), flush=True)
        for seed in (1, 2, 3):
            F, msg = climb(m, 100 * seed); print('   run %d: %s' % (seed, msg), flush=True)
