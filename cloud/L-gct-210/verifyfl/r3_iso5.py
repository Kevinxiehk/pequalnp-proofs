import sys; sys.path.insert(0, "/home/claude/work/L-gct-210/verifyfl")
"""isotropic m: broader search for a split (5,1) space: several different (4,1) split spaces (climb from e_3 m^T), many extension starts each."""
import numpy as np, time
from core import *
from di_core import *
from di_ext import ext, chk_m
w = w3; which = sys.argv[1]; seed = int(sys.argv[2])
m = {'I1': np.array([1, w, w * w, 0, 0]), 'I2': np.array([1, 1j, -1, -1j, 0]), 'I3': np.array([1, w, w * w, 0, 0]) + 0.7 * np.array([0, 0, 0, 1, -1]) * 0}[which]
if which == 'I3':   # isotropic with 4 nonzero entries, not a root-of-unity vector: (1, a, b, c, 0), a+b+c = -1, a^2+b^2+c^2 = -1, choose a = 0.5
    a = 0.5; r = np.roots([1, 1.5, (2.25 + 1.25) / 2]); m = np.array([1, a, r[0], r[1], 0])
assert abs(m.sum()) < 1e-12 and abs(np.sum(m * m)) < 1e-12
Y1 = np.outer(np.eye(4)[3], m); t0 = time.time(); n4 = 0; tot5 = 0; tried = 0
rng = np.random.default_rng(seed)
while time.time() - t0 < 140:
    F = np.array([Y1]); ok = True
    for k in (2, 3, 4):
        s, n = ext(F, m, 8, int(rng.integers(1e6)), tmax=10)
        if not s: ok = False; break
        F = np.concatenate([F, s[int(rng.integers(len(s)))][None]])
    if not ok: continue
    n4 += 1; L0, _ = kernel_of(onb(F), lambda Y: Y.sum(0)); sl0 = sl_check(L0, trials=30)
    s5, n5 = ext(F, m, 25, int(rng.integers(1e6)), tmax=25); tot5 += len(s5); tried += n5
    print('  (4,1) space %d: ker kappa strong-level err %.1e; extensions to dim 5: %d/%d' % (n4, sl0, len(s5), n5), flush=True)
    if s5: np.save('r3_iso5_%s_%d.npy' % (which, n4), np.concatenate([F, s5[0][None]]))
print('m type %s: %d spaces of dim 4 built, dim-5 extensions found: %d of %d starts (%.0fs)' % (which, n4, tot5, tried, time.time() - t0))
