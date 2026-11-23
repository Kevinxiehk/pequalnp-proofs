import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""isotropic m: split (2,1) spaces span(e_3 m^T, Y); is ker kappa strongly level?  (necessity of <m,m> != 0 in Theorem SPLIT)"""
import numpy as np
from core import *
from di_core import *
from di_ext import ext, chk_m
from r3_test1 import Dmat
w = w3; m = np.array([1, w, w * w, 0, 0]); Y1 = np.outer(np.eye(4)[3], m)
sols, n = ext(np.array([Y1]), m, 30, 4242, tmax=60)
print('isotropic m = (1,w,w^2,0,0): %d/%d extensions of C e_3 m^T' % (len(sols), n))
worst = None
for Y in sols:
    B = np.array([Y1, Y]); res = chk_m(B, m, trials=60)
    kap = np.sum(Y.sum(0) * m.conj()) / 3; Y0 = Y - kap * Y1             # element of ker kappa
    C0 = Cvec(np.array([c * Y0 for c in (1, -1, 2, 0.5 + 1j)])) - 24
    sl = np.abs(C0).max(); 
    if worst is None or sl > worst[0]: worst = (sl, res, Y0)
    print('   defect-in-Cm residual %.1e ; |C(cY_0) - 24| on ker kappa: %.2e' % (res, sl))
sl, res, Y0 = worst
if sl > 1e-6:
    np.save('r3_iso_counterexample.npy', np.array([Y1, Y0]))
    D = Dmat(Y0[:3]); Dm = D @ m; mu = np.sum(Dm * m.conj()) / 3; th = np.sum((Cvec(Y0) - 24) * m.conj()) / 3
    print('counterexample saved: Dm - mu m = %.1e, mu = %s, thetahat(Y_0) = %s (kappa(Y_0) = %.1e), <m, row 3 of Y_0> = %.1e' % (np.abs(Dm - mu * m).max(), np.round(mu, 4), np.round(th, 4), abs(Y0.sum(0)).max(), abs(np.sum(m * Y0[3]))))
