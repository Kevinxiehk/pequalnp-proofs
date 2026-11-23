import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""isotropic m: do split spaces whose ker kappa is NOT strongly level extend?  Start from several such (2,1) spaces, extend with m fixed."""
import numpy as np
from core import *
from di_core import *
from di_ext import ext, chk_m
w = w3; m = np.array([1, w, w * w, 0, 0]); Y1 = np.outer(np.eye(4)[3], m)
sols, n = ext(np.array([Y1]), m, 40, 777, tmax=50)
bad = []
for Y in sols:
    kap = np.sum(Y.sum(0) * m.conj()) / 3; Y0 = Y - kap * Y1
    if np.abs(Cvec(np.array([Y0, 2 * Y0])) - 24).max() > 1e-4: bad.append(Y0)
print('isotropic (2,1) split spaces with ker kappa not strongly level: %d of %d' % (len(bad), len(sols)), flush=True)
for idx, Y0 in enumerate(bad[:6]):
    F = np.array([Y1, Y0]); s3, n3 = ext(F, m, 12, 31 + idx, tmax=20)
    msg = '   example %d: extensions to dim 3: %d/%d' % (idx, len(s3), n3)
    if s3:
        F3 = np.concatenate([F, s3[0][None]]); L0, _ = kernel_of(onb(F3), lambda Y: Y.sum(0))
        s4, n4 = ext(F3, m, 12, 57 + idx, tmax=20); msg += ' (ker kappa strong-level err %.1e); to dim 4: %d/%d' % (sl_check(L0, trials=30), len(s4), n4)
        if s4:
            F4 = np.concatenate([F3, s4[0][None]]); s5, n5 = ext(F4, m, 12, 91 + idx, tmax=20); msg += '; to dim 5: %d/%d' % (len(s5), n5)
    print(msg, flush=True)
