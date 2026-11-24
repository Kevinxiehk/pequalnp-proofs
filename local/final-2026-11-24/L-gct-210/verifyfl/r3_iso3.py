import sys; sys.path.insert(0, "/home/kevxhk/work/L-gct-210/verifyfl")
"""isotropic m = (1,w,w^2,0,0): build split (4,1) spaces whose ker kappa is NOT strongly level, save them, look at their structure,
   and try hard to extend them to dimension 5 (m fixed)."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import ext, chk_m
np.set_printoptions(linewidth=220, precision=3, suppress=True)
w = w3; m = np.array([1, w, w * w, 0, 0]); Y1 = np.outer(np.eye(4)[3], m)
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
t0 = time.time(); found = []
sols, n = ext(np.array([Y1]), m, 40, 777 + seed, tmax=40)
bad = []
for Y in sols:
    kap = np.sum(Y.sum(0) * m.conj()) / 3; Y0 = Y - kap * Y1
    if np.abs(Cvec(np.array([Y0, 2 * Y0])) - 24).max() > 1e-4: bad.append(Y0)
for idx, Y0 in enumerate(bad):
    if time.time() - t0 > 100: break
    F = np.array([Y1, Y0]); s3, n3 = ext(F, m, 10, 31 + idx + seed, tmax=12)
    if not s3: continue
    F3 = np.concatenate([F, s3[0][None]]); s4, n4 = ext(F3, m, 10, 57 + idx + seed, tmax=12)
    if not s4: continue
    F4 = onb(np.concatenate([F3, s4[0][None]])); L0, _ = kernel_of(F4, lambda Y: Y.sum(0))
    print('4-dim split isotropic space #%d: defect residual %.1e, ker kappa dim %d strong-level err %.2e' % (len(found), chk_m(F4, m), len(L0), sl_check(L0, trials=30)), flush=True)
    found.append(F4)
if found: np.save('r3_iso4_s%d.npy' % seed, np.array(found))
print('found', len(found), 'time %.0fs' % (time.time() - t0))
